mod state;

pub use state::*;

// Re-export internal building blocks that are intentionally exposed to other
// crate modules (e.g. `crate::check` facade in `lib.rs`).
pub(crate) use state::check;
pub(crate) use state::{NamespaceMemberIndex, ProgramTypeResolver};
