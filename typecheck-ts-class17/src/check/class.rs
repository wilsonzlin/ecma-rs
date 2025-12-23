use crate::check::CheckOptions;
use crate::check::CheckResult;
use crate::check::DefId;
use crate::check::TypeChecker;
use crate::diagnostics::Diagnostic;
use crate::types::Type;

/// Compute the declared type for a definition. For classes this returns the
/// instance type; for interfaces it returns the interface type itself.
pub fn type_of_def(checker: &mut TypeChecker, id: DefId) -> Result<Type, Diagnostic> {
  checker.type_of_def(id)
}

/// Check a definition body and return any diagnostics produced during checking.
pub fn check_body(checker: &mut TypeChecker, id: DefId, options: &CheckOptions) -> CheckResult {
  checker.check_body(id, options)
}
