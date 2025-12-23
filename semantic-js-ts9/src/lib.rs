#![deny(rust_2018_idioms)]

#[cfg(feature = "ts")]
pub mod ts;

#[cfg(feature = "ts")]
pub use ts::*;
