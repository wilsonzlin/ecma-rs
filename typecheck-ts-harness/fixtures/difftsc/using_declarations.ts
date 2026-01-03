type Resource = { tag: "res" };

export function useResource() {
  using resource: Resource = { tag: "res" } as any;
  return resource;
}

export const value = useResource();
             // ^?

// Diagnostic mismatch case: `await using` should require an async context.
export function invalidAwaitUsing() {
  await using resource: Resource = { tag: "res" } as any;
  return resource;
}
