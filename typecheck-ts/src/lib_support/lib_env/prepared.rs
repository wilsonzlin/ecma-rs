use std::sync::Arc;

use hir_js::{
  lower_file_with_diagnostics as lower_hir_with_diagnostics, FileKind as HirFileKind, LowerResult,
};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use sem_ts::from_hir_js::lower_to_ts_hir;
use semantic_js::ts as sem_ts;

use crate::api::Diagnostic;
use crate::lib_support::LibFile;

#[derive(Clone, Debug)]
pub(crate) struct PreparedLib {
  pub(crate) file: LibFile,
  pub(crate) lowered: Option<Arc<LowerResult>>,
  pub(crate) sem_hir: Option<Arc<sem_ts::HirFile>>,
  pub(crate) diagnostics: Arc<[Diagnostic]>,
}

pub(crate) fn prepare_lib(lib: LibFile) -> PreparedLib {
  let parsed = parse_with_options(
    &lib.text,
    ParseOptions {
      dialect: Dialect::Dts,
      source_type: SourceType::Module,
    },
  )
  .map_err(|err| err.to_diagnostic(lib.id));
  match parsed {
    Ok(ast) => {
      let (lowered, lower_diags) = lower_hir_with_diagnostics(lib.id, HirFileKind::Dts, &ast);
      let sem_hir = lower_to_ts_hir(&ast, &lowered);
      PreparedLib {
        file: lib,
        lowered: Some(Arc::new(lowered)),
        sem_hir: Some(Arc::new(sem_hir)),
        diagnostics: Arc::from(lower_diags),
      }
    }
    Err(err) => PreparedLib {
      file: lib,
      lowered: None,
      sem_hir: None,
      diagnostics: Arc::<[Diagnostic]>::from(vec![err]),
    },
  }
}
