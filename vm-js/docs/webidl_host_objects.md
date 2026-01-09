# WebIDL host objects (constructors, prototypes, wrapper caches)

This document describes the intended pattern for exposing **WebIDL interfaces** (constructors +
`prototype` objects) and **DOM wrapper objects** (host-backed JS objects) when embedding `vm-js`.

It is written for:

- **WebIDL binding generators** that need to generate deterministic initialization code for
  interfaces like `Window`, `Document`, `Node`, …
- **Embedders** that need to associate JS objects with host identities (e.g. `NodeId`) while
  preserving wrapper identity and letting the GC collect wrappers when they become unreachable.

## Mental model: `GcObject` handles vs GC roots

`vm-js` uses stable handles like [`GcObject`](crate::GcObject) to refer to heap allocations.

Important: **a `GcObject` is not a root**.

The GC only traces from:

- **Stack roots** (`Scope::push_root`), and
- **Persistent roots** (`Heap::add_root` / `Heap::remove_root`).

If you store a `GcObject` in your own Rust data structures (e.g. a `HashMap`), the GC will **not**
see it and may collect the underlying allocation. This is a feature: it enables weak caches.

`WeakGcObject` is a convenience wrapper around this idea.

## Rooting rules (the non-negotiables)

### When to use `Scope` + `push_root`

Any allocation may trigger a GC cycle (e.g. due to `HeapLimits::gc_threshold`), which can collect
unrooted objects that are only referenced from Rust locals.

Use a `Scope` and `push_root` when:

- You allocate multiple objects and need to keep earlier allocations alive while allocating later
  ones.
- You are building a structure (like a property descriptor array) that will temporarily store
  `Value`s pointing at heap allocations.

Example pattern:

```rust,ignore
let mut scope = heap.scope();

let proto = scope.alloc_object()?;
scope.push_root(proto.into()); // keep `proto` alive across later allocations

// Allocate more things here…
```

### When to use persistent roots (`Heap::add_root`)

If the host needs to keep an object alive beyond a single stack scope (e.g. intrinsics, `Window`,
`Window.prototype`, `Function.prototype`, …), store it in the heap’s persistent root table:

```rust,ignore
let root_id = heap.add_root(Value::Object(window_ctor));
// store `root_id` in your embedding state, and call `heap.remove_root(root_id)` when tearing down
```

### Why wrapper identity caches must store weak handles

Wrapper caches (e.g. `NodeId -> wrapper`) must **not** keep wrappers alive. If the cache stores
roots (e.g. `RootId` or rooted `Value`s), the wrapper becomes permanently reachable and can never be
collected, which is a memory leak for any long-lived DOM.

Instead, store [`WeakGcObject`](crate::WeakGcObject). A `WeakGcObject` can be “upgraded” by checking
whether the underlying allocation is still live:

```rust,ignore
if let Some(obj) = weak.upgrade(&heap) {
  // still live; reuse wrapper
} else {
  // collected; allocate a new wrapper
}
```

## Host data tracing (event listeners, retained callbacks)

When you attach **host data** to a wrapper object (e.g. the `NodeId` the wrapper represents), that
host data may itself contain references back into JS:

- registered event listener callbacks,
- user-provided `MutationObserver` callbacks,
- `Promise` resolve/reject functions retained by the host,
- etc.

GC must treat those JS references as outgoing edges from the wrapper. In practice this means:

1. Host data is stored on the heap *as part of* an object allocation.
2. During marking, `vm-js` traces the object’s JS properties **and** asks the host data to trace any
   GC handles it contains.

Your host payload type must therefore provide a “trace” operation (exact trait name is up to the
API surface; conceptually it is equivalent to calling `trace_value` on each embedded `Value`).

If you forget to trace a callback reference stored in host data, the callback may be collected
while the wrapper is still reachable, leading to use-after-free style “invalid handle” failures
later.

## Interface initialization (constructors + prototypes)

For each WebIDL interface `Interface`, the initialization code typically needs to create and wire:

1. `Interface.prototype` (an ordinary object)
2. `Interface` (a constructor function)
3. Prototype chain relationships
4. Properties (methods/attributes) via [`PropertyDescriptor`](crate::PropertyDescriptor)

### Prototype objects

- Allocate `Interface.prototype`.
- Set `Interface.prototype.[[Prototype]]` to:
  - the parent interface’s prototype (for inheritance), or
  - `Object.prototype` (for root interfaces).
- Define methods/attributes on `Interface.prototype` using property descriptors.

### Constructor functions

- Allocate the constructor function object `Interface`.
- Define the `prototype` property on the constructor as a data descriptor pointing at
  `Interface.prototype`.
- Define the `constructor` property on `Interface.prototype` pointing back at `Interface`.
- Set `Interface.[[Prototype]]` to `Function.prototype`.
- Install `Interface` on the global object (e.g. `Window`) per `[Exposed]` rules.

## Worked example: `Window`, `alert`, and a wrapper cache

The snippet below is **pseudo-code** that demonstrates the full flow:

- create `Window.prototype`
- create `Window` constructor
- define a method `alert()` as a native function on `Window.prototype`
- allocate a wrapper object with `host_data` containing a dummy `NodeId`
- store/retrieve wrappers via `HashMap<NodeId, WeakGcObject>`

```rust,ignore
 use std::collections::HashMap;
 use vm_js::{
  GcObject, Heap, HeapLimits, PropertyDescriptor, PropertyKey, PropertyKind, Scope, Value, Vm,
  VmError, VmHost, VmHostHooks, WeakGcObject,
 };

/// Host identity for a DOM node.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct NodeId(u32);

 /// Embedding state: wrapper identity cache (weak).
 struct HostState {
   node_wrappers: HashMap<NodeId, WeakGcObject>,
 }
 
 // A "native" function entry point.
 // Native handlers receive `host: &mut dyn VmHost`, which an embedding can downcast to access
 // embedder state (DOM, event loop, wrapper caches, etc) without globals.
 fn native_alert(
   _vm: &mut Vm,
   _scope: &mut Scope<'_>,
   host: &mut dyn VmHost,
   _hooks: &mut dyn VmHostHooks,
   _callee: GcObject,
   _this: Value,
   _args: &[Value],
 ) -> Result<Value, VmError> {
   let _host_state = host.as_any().downcast_ref::<HostState>().unwrap();
   // In a real embedder, this would surface to the browser UI / console, schedule tasks, etc.
   Ok(Value::Undefined)
 }

fn init_window_bindings(scope: &mut Scope<'_>) -> Result<(Value, Value), VmError> {
  // 1) Create Window.prototype
  let window_proto = scope.alloc_object()?;
  scope.push_root(window_proto.into()); // keep it alive while we allocate more

  // 2) Create the `alert` native function object
  // (Pseudo: "alloc_native_function" returns a callable object)
  let alert_fn = scope.alloc_native_function(native_alert, /*name=*/"alert", /*length=*/0)?;
  scope.push_root(alert_fn.into());

  // 3) Define `Window.prototype.alert`
  let alert_key = PropertyKey::String(scope.alloc_string("alert")?);
  let desc = PropertyDescriptor {
    enumerable: true,
    configurable: true,
    kind: PropertyKind::Data {
      value: alert_fn.into(),
      writable: true,
    },
  };
  scope.define_own_property(window_proto, alert_key, desc)?;

  // 4) Create Window constructor
  let window_ctor = scope.alloc_native_constructor(/*call=*/None, /*construct=*/Some(|_| {
    // In browsers, `new Window()` is typically not allowed; constructor can throw.
    Err(VmError::Unimplemented("Window constructor"))
  }))?;
  scope.push_root(window_ctor.into());

  // 5) Wire constructor <-> prototype (constructor.prototype, prototype.constructor)
  scope.define_own_property(
    window_ctor,
    PropertyKey::String(scope.alloc_string("prototype")?),
    PropertyDescriptor {
      enumerable: false,
      configurable: false,
      kind: PropertyKind::Data {
        value: window_proto.into(),
        writable: false,
      },
    },
  )?;

  scope.define_own_property(
    window_proto,
    PropertyKey::String(scope.alloc_string("constructor")?),
    PropertyDescriptor {
      enumerable: false,
      configurable: true,
      kind: PropertyKind::Data {
        value: window_ctor.into(),
        writable: true,
      },
    },
  )?;

  Ok((window_ctor.into(), window_proto.into()))
}

fn get_or_create_node_wrapper(
  heap: &mut Heap,
  host: &mut HostState,
  node_id: NodeId,
  node_proto: Value, // e.g. `Node.prototype`
) -> Result<Value, VmError> {
  // 1) Fast path: wrapper cache hit + still-live
  if let Some(weak) = host.node_wrappers.get(&node_id).copied() {
    if let Some(obj) = weak.upgrade(heap) {
      return Ok(obj.into());
    }
  }

  // 2) Allocate a new wrapper with host payload (NodeId)
  let wrapper_obj = {
    let mut scope = heap.scope();
    scope.push_root(node_proto); // keep proto alive during allocation

    // Pseudo: allocate a wrapper whose [[Prototype]] is node_proto and whose host_data is NodeId.
    scope.alloc_host_object(/*proto=*/node_proto, /*host_data=*/node_id)?
  };

  // 3) Store weakly so the wrapper remains collectible
  host.node_wrappers.insert(node_id, WeakGcObject::new(wrapper_obj));

  Ok(wrapper_obj.into())
}

fn main() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(16 * 1024 * 1024, 8 * 1024 * 1024));
  let mut host = HostState {
    node_wrappers: HashMap::new(),
  };

  // Create Window bindings:
  let (window_ctor, window_proto) = {
    let mut scope = heap.scope();
    init_window_bindings(&mut scope)?
  };

  // Create/reuse a Node wrapper:
  let _node_wrapper = get_or_create_node_wrapper(
    &mut heap,
    &mut host,
    NodeId(1),
    /*node_proto=*/window_proto, // placeholder for this example
  )?;

  // The cache does not keep wrappers alive; they disappear after GC if unreferenced.
  heap.collect_garbage();
  Ok(())
}
```
