use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use typecheck_ts::db::{queries, Database};
use typecheck_ts::lib_support::{CompilerOptions, FileKind};
use typecheck_ts::{FileId, FileKey, FileOrigin};

#[test]
fn smoke_parallel_database_usage() {
  let mut db = Database::new();
  let roots: Arc<[FileKey]> = vec![FileKey::new("root.ts")].into();
  let options = CompilerOptions::default();
  db.set_roots(roots.clone());
  db.set_compiler_options(options.clone());

  let cancellation = Arc::new(AtomicBool::new(false));
  db.set_cancellation_flag(cancellation.clone());

  db.set_file(
    FileId(0),
    roots[0].clone(),
    FileKind::Ts,
    Arc::<str>::from("export const value = 1;"),
    FileOrigin::Source,
  );
  db.set_module_resolution(FileId(0), Arc::<str>::from("./missing"), None);

  let rev = queries::db_revision(&db);

  std::thread::scope(|scope| {
    let snap = db.snapshot();
    let root_clone = roots.clone();
    let options_clone = options.clone();
    scope.spawn(move || {
      assert_eq!(queries::roots(&snap), root_clone);
      assert_eq!(queries::compiler_options(&snap), options_clone);
      assert_eq!(queries::file_kind(&snap, FileId(0)), FileKind::Ts);
      assert_eq!(
        &*queries::file_text(&snap, FileId(0)),
        "export const value = 1;"
      );
      assert_eq!(
        queries::module_resolve(&snap, FileId(0), Arc::<str>::from("./missing")),
        None
      );
      assert_eq!(queries::db_revision(&snap), rev);
    });

    let snap_cancel = db.snapshot();
    scope.spawn(move || {
      assert!(!queries::cancelled(&snap_cancel).load(Ordering::SeqCst));
    });
  });

  cancellation.store(true, Ordering::SeqCst);
  assert!(queries::cancelled(&db).load(Ordering::SeqCst));
}
