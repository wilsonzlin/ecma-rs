use types_ts_interned::{Property, RelateHooks, RelateTypeExpander};

fn same_origin_private_member(a: &Property, b: &Property) -> bool {
  matches!((a.data.origin, b.data.origin), (Some(left), Some(right)) if left == right)
}

/// Build relation hooks that know how to expand type references and compare
/// private/protected members by origin.
pub fn class_hooks<'a>(expander: &'a dyn RelateTypeExpander) -> RelateHooks<'a> {
  RelateHooks {
    expander: Some(expander),
    is_same_origin_private_member: Some(&same_origin_private_member),
  }
}
