use types_ts::Property;
use types_ts::RelateHooks;
use types_ts::TypeExpander;

fn same_origin_private_member(a: &Property, b: &Property) -> bool {
  matches!((a.origin_id, b.origin_id), (Some(left), Some(right)) if left == right)
}

/// Build relation hooks that know how to expand type references and compare
/// private/protected members by origin.
pub fn class_hooks<'a>(expander: &'a dyn TypeExpander) -> RelateHooks<'a> {
  RelateHooks {
    expander: Some(expander),
    is_same_origin_private_member: Some(&same_origin_private_member),
  }
}
