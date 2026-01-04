import { ApiError, Todo, User } from "../types";
import { uniqBy } from "../utils/array";
import { Result, mapResult } from "../utils/result";
import { HttpClient } from "./client";

function decodeUser(json: any): User {
  return {
    id: String(json.id),
    name: String(json.name),
    email: json.email ? String(json.email) : undefined,
  };
}

function decodeTodo(json: any): Todo {
  return {
    id: String(json.id),
    title: String(json.title),
    completed: Boolean(json.completed),
    assignee: json.assignee ? decodeUser(json.assignee) : undefined,
    tags: Array.isArray(json.tags) ? json.tags.map(String) : [],
  };
}

export async function listTodos(client: HttpClient): Promise<Result<Todo[], ApiError>> {
  const res = await client.get("/todos", (json) => {
    const arr = Array.isArray(json) ? json : [];
    return arr.map(decodeTodo);
  });
  return mapResult(res, (todos) => uniqBy(todos, (t) => t.id));
}

