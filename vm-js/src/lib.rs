//! JavaScript runtime/VM scaffolding for `ecma-rs`.
//!
//! This crate is the foundation for browser-grade JavaScript execution. It provides:
//! - A non-moving mark/sweep GC heap ([`Heap`])
//! - Stable, generation-checked handles ([`GcObject`], [`GcString`], [`GcSymbol`])
//! - Stack rooting via RAII scopes ([`Scope`]) + persistent roots ([`RootId`])
//! - Cooperative interruption primitives ([`Vm`], [`Budget`], [`InterruptToken`])
//! - Source/stack-trace types ([`SourceText`], [`StackFrame`])
//!
//! # Rooting and handle validity
//!
//! Heap-allocated objects (strings, symbols, objects) are referenced using stable handles.
//! A handle contains `{ index, generation }`; the `index` points into the heap slot vector and the
//! `generation` is incremented every time that slot is freed.
//!
//! This means:
//! - Handles are stable across `Vec` reallocations because objects are stored in index-addressed
//!   slots (the object itself never moves to a different index).
//! - A handle becomes invalid once the object is collected; future allocations may reuse the same
//!   slot index with a newer generation.
//! - Public APIs that dereference handles validate `{index,generation}` and return
//!   [`VmError::InvalidHandle`] for stale handles.
//! - During GC, encountering a stale handle in a root set indicates a bug; this crate will
//!   `debug_assert!` and ignore it.
//!
//! The GC traces from two root sets:
//! - **Stack roots**: stored in `Heap::root_stack` and managed by [`Scope`]. When a `Scope` is
//!   dropped, all stack roots created within it are popped.
//! - **Persistent roots**: managed by [`Heap::add_root`] / [`Heap::remove_root`], intended for host
//!   embeddings.
//!
//! # WebIDL / host objects
//!
//! If you are embedding `vm-js` in a browser-style host and need to expose Web APIs (constructors,
//! `prototype` objects, native methods/attributes, wrapper identity caches), see
//! [`docs::webidl_host_objects`](crate::docs::webidl_host_objects).

mod builtins;
mod env;
mod error;
mod exec;
mod execution_context;
mod function;
mod function_properties;
mod handle;
mod heap;
mod interrupt;
mod intrinsics;
mod jobs;
mod module_loading;
mod native;
mod object_ops;
mod ops;
mod promise;
mod promise_jobs;
mod promise_rejection_tracker;
mod property;
mod realm;
mod source;
mod string;
mod symbol;
mod value;
mod vm;

pub(crate) use crate::handle::EnvRootId;
pub(crate) use crate::handle::GcEnv;

pub use crate::error::Termination;
pub use crate::error::TerminationReason;
pub use crate::error::VmError;
pub use crate::exec::Completion;
pub use crate::exec::JsRuntime;
pub use crate::execution_context::ExecutionContext;
pub use crate::execution_context::ModuleId;
pub use crate::execution_context::ScriptId;
pub use crate::execution_context::ScriptOrModule;
pub use crate::function::NativeConstructId;
pub use crate::function::NativeFunctionId;
pub use crate::function_properties::make_constructor;
pub use crate::function_properties::set_function_length;
pub use crate::function_properties::set_function_name;
pub use crate::handle::GcObject;
pub use crate::handle::GcString;
pub use crate::handle::GcSymbol;
pub use crate::handle::HeapId;
pub use crate::handle::RootId;
pub use crate::handle::WeakGcObject;
pub use crate::heap::Heap;
pub use crate::heap::HeapLimits;
pub use crate::heap::MAX_PROTOTYPE_CHAIN;
pub use crate::heap::Scope;
pub use crate::intrinsics::Intrinsics;
pub use crate::intrinsics::WellKnownSymbols;
pub use crate::interrupt::InterruptHandle;
pub use crate::interrupt::InterruptToken;
pub use crate::jobs::Job;
pub use crate::jobs::JobCallback;
pub use crate::jobs::JobKind;
pub use crate::jobs::JobResult;
pub use crate::jobs::PromiseHandle;
pub use crate::jobs::PromiseRejectionOperation;
pub use crate::jobs::RealmId;
pub use crate::jobs::VmHostHooks;
pub use crate::jobs::VmJobContext;
#[deprecated(note = "Use VmHostHooks instead (JobQueue was renamed for spec alignment).")]
pub use crate::jobs::VmHostHooks as JobQueue;
#[deprecated(note = "Use Job instead (MicrotaskJob was renamed for spec alignment).")]
pub use crate::jobs::Job as MicrotaskJob;
pub use crate::module_loading::finish_loading_imported_module;
pub use crate::module_loading::GraphLoadingState;
pub use crate::module_loading::ImportAttribute;
pub use crate::module_loading::ImportCallError;
pub use crate::module_loading::ImportCallTypeError;
pub use crate::module_loading::import_attributes_from_options;
pub use crate::module_loading::ModuleCompletion;
pub use crate::module_loading::ModuleLoadPayload;
pub use crate::module_loading::ModuleRecord;
pub use crate::module_loading::ModuleReferrer;
pub use crate::module_loading::ModuleRequest;
pub use crate::module_loading::PromiseCapability;
pub use crate::module_loading::ScriptOrModuleId;
pub use crate::module_loading::VmModuleHostHooks;
pub use crate::native::alloc_native_function_name;
pub use crate::native::dispatch_native_call;
pub use crate::native::dispatch_native_construct;
pub use crate::native::native_construct_id;
pub use crate::native::native_function_meta;
pub use crate::native::NativeCallFn;
pub use crate::native::NativeConstructFn;
pub use crate::native::NativeFunctionMeta;
pub use crate::promise::create_promise_resolve_thenable_job;
pub use crate::promise::perform_promise_then;
pub use crate::promise::PromiseReactionRecord;
pub use crate::promise::PromiseReactionType;
pub use crate::promise_jobs::new_promise_reaction_job;
pub use crate::promise_jobs::new_promise_resolve_thenable_job;
pub use crate::promise_rejection_tracker::AboutToBeNotifiedBatch;
pub use crate::promise_rejection_tracker::PromiseRejectionHandleAction;
pub use crate::promise_rejection_tracker::PromiseRejectionTracker;
pub use crate::property::PropertyDescriptor;
pub use crate::property::PropertyDescriptorPatch;
pub use crate::property::PropertyKey;
pub use crate::property::PropertyKind;
pub use crate::realm::Realm;
pub use crate::source::format_stack_trace;
pub use crate::source::SourceText;
pub use crate::source::StackFrame;
pub use crate::string::JsString;
pub use crate::symbol::JsSymbol;
pub use crate::value::Value;
pub use crate::vm::Budget;
pub use crate::vm::BudgetGuard;
pub use crate::vm::ExecutionContextGuard;
pub use crate::vm::NativeCall;
pub use crate::vm::NativeConstruct;
pub use crate::vm::Vm;
pub use crate::vm::VmOptions;

/// Long-form guides and embedding documentation.
pub mod docs {
  /// WebIDL binding initialization patterns (constructors, prototypes, host objects).
  #[doc = include_str!("../docs/webidl_host_objects.md")]
  pub mod webidl_host_objects {}
}
