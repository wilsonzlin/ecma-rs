function identity<T>(value: T) {
  return value;
}

export const genericValue = identity({ a: 1, b: "ok" });
               // ^?
