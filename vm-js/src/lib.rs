//! JavaScript runtime/VM scaffolding for ecma-rs.
//!
//! This crate intentionally starts small: it provides the cross-cutting safety
//! and diagnostics infrastructure required for executing hostile code:
//!
//! - Cooperative interruption (fuel + deadline + host interrupt token).
//! - A non-catchable termination error channel (timeouts cannot be defeated with
//!   `try/catch`).
//! - Source mapping + stack trace primitives.

mod error;
mod gc;
mod heap;
mod interrupt;
mod scope;
mod source;
mod string;
mod value;
mod vm;

pub use crate::error::Termination;
pub use crate::error::TerminationReason;
pub use crate::error::VmError;
pub use crate::gc::Trace;
pub use crate::gc::Tracer;
pub use crate::heap::GcString;
pub use crate::heap::Heap;
pub use crate::heap::HeapObject;
pub use crate::interrupt::InterruptHandle;
pub use crate::interrupt::InterruptToken;
pub use crate::scope::Scope;
pub use crate::source::format_stack_trace;
pub use crate::source::SourceText;
pub use crate::source::StackFrame;
pub use crate::string::JsString;
pub use crate::value::ObjectId;
pub use crate::value::Value;
pub use crate::vm::Budget;
pub use crate::vm::Vm;
pub use crate::vm::VmOptions;

