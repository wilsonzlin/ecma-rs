import { DeepReadonly, Todo } from "../types";
import { groupBy } from "../utils/array";

export type Listener<T> = (state: DeepReadonly<T>) => void;

export class Store<T extends object> {
  private state: T;
  private listeners: Listener<T>[] = [];

  constructor(initial: T) {
    this.state = initial;
  }

  getState(): DeepReadonly<T> {
    return this.state as DeepReadonly<T>;
  }

  setState(next: T): void {
    this.state = next;
    const snapshot = this.getState();
    for (const listener of this.listeners) {
      listener(snapshot);
    }
  }

  subscribe(listener: Listener<T>): () => void {
    this.listeners.push(listener);
    return () => {
      const idx = this.listeners.indexOf(listener);
      if (idx >= 0) {
        this.listeners.splice(idx, 1);
      }
    };
  }
}

export interface TodoState {
  todos: Todo[];
  byId: Record<string, Todo>;
}

export function buildTodoState(todos: Todo[]): TodoState {
  const grouped = groupBy(todos, (t) => t.id);
  const byId: Record<string, Todo> = {};
  for (const id in grouped) {
    byId[id] = grouped[id][0];
  }
  return { todos, byId };
}

