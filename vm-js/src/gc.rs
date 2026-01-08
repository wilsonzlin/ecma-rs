pub trait Trace {
  fn trace(&self, tracer: &mut Tracer);
}

#[derive(Default)]
pub struct Tracer {
  _priv: (),
}

impl Tracer {
  pub fn new() -> Self {
    Self::default()
  }
}

