mod binder;
mod model;

pub use binder::bind_ts_program;
pub use model::*;

#[cfg(test)]
mod tests;
