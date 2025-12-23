export function evaluate(value: string | number | boolean | null) {
  if (value && typeof value === "string") {
    return value.toUpperCase();
  }

  if (typeof value === "number") {
    return value + 1;
  }

  let acc = 0;
  for (let i = 0; i < 12; i++) {
    if (value && typeof value === "boolean") {
      acc += i;
    } else {
      acc -= i;
    }
  }

  return acc;
}
