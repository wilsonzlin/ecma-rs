use std::collections::VecDeque;
use std::sync::Arc;
use std::sync::Mutex;

use vm_js::JobKind;
use vm_js::RootedJob;
use vm_js::VmHostHooks;
use vm_js::VmJobContext;
use vm_js::{Heap, HeapLimits};

#[derive(Default)]
struct TestHost {
  queue: VecDeque<RootedJob>,
}

impl VmHostHooks for TestHost {
  fn host_enqueue_promise_job(&mut self, job: RootedJob, _realm: Option<vm_js::RealmId>) {
    self.queue.push_back(job);
  }
}

#[derive(Default)]
struct TestContext;

impl VmJobContext for TestContext {}

fn enqueue_three_jobs(host: &mut dyn VmHostHooks, sink: Arc<Mutex<Vec<u8>>>) {
  for i in 1..=3u8 {
    let sink = sink.clone();
    host.host_enqueue_promise_job(
      RootedJob::new(JobKind::Promise, move |_ctx, _host| {
        sink.lock().unwrap().push(i);
        Ok(())
      }),
      None,
    );
  }
}

#[test]
fn promise_jobs_can_be_run_in_fifo_order() {
  let sink = Arc::new(Mutex::new(Vec::new()));

  // Ensure the host hook API is object-safe and ergonomic by exercising it behind a trait object.
  let mut host = TestHost::default();
  enqueue_three_jobs(&mut host, sink.clone());

  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 512 * 1024));
  let mut ctx = TestContext::default();
  while let Some(mut job) = host.queue.pop_front() {
    let result = job.run(&mut ctx, &mut host);
    job.teardown(&mut heap);
    result.unwrap();
  }

  assert_eq!(&*sink.lock().unwrap(), &[1, 2, 3]);
}
