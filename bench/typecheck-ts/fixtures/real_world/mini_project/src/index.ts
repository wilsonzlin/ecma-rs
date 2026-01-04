import { createClient } from "./api/client";
import { listTodos } from "./api/todos";
import { Store, TodoState, buildTodoState } from "./state/store";

async function fakeFetch(input: string): Promise<string> {
  if (input.endsWith("/todos")) {
    return JSON.stringify([
      { id: "t1", title: "write benchmarks", completed: false, tags: ["perf"] },
      { id: "t2", title: "fix caches", completed: true, tags: ["types"] },
    ]);
  }
  return "[]";
}

export async function demo(): Promise<Store<TodoState>> {
  const client = createClient("https://example.invalid", fakeFetch);
  const res = await listTodos(client);
  const todos = res.ok ? res.value : [];
  const store = new Store(buildTodoState(todos));
  store.subscribe((_state) => {});
  return store;
}

