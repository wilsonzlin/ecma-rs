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

mod error;
mod exec;
mod function;
mod function_properties;
mod handle;
mod heap;
mod intrinsics;
mod interrupt;
mod object_ops;
mod jobs;
mod job_queue;
mod native;
mod property;
mod realm;
mod source;
mod string;
mod symbol;
mod value;
mod vm;

pub use crate::error::Termination;
pub use crate::error::TerminationReason;
pub use crate::error::VmError;
pub use crate::exec::Completion;
pub use crate::exec::JsRuntime;
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
pub use crate::heap::Scope;
pub use crate::intrinsics::Intrinsics;
pub use crate::intrinsics::WellKnownSymbols;
pub use crate::interrupt::InterruptHandle;
pub use crate::interrupt::InterruptToken;
pub use crate::jobs::Job;
pub use crate::jobs::JobCallback;
pub use crate::jobs::JobKind;
pub use crate::jobs::JobResult;
pub use crate::jobs::RealmId;
pub use crate::jobs::VmHostHooks;
pub use crate::jobs::VmJobContext;
pub use crate::job_queue::JobQueue;
pub use crate::job_queue::MicrotaskJob;
pub use crate::job_queue::PromiseHandle;
pub use crate::job_queue::PromiseRejectionOperation;
pub use crate::native::alloc_native_function_name;
pub use crate::native::dispatch_native_call;
pub use crate::native::dispatch_native_construct;
pub use crate::native::native_construct_id;
pub use crate::native::native_function_meta;
pub use crate::native::NativeCallFn;
pub use crate::native::NativeConstructFn;
pub use crate::native::NativeFunctionMeta;
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
pub use crate::vm::NativeCall;
pub use crate::vm::NativeConstruct;
pub use crate::vm::Budget;
pub use crate::vm::Vm;
pub use crate::vm::VmOptions;
