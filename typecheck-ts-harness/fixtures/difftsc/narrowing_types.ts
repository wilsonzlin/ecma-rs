export function pickValue(value: string | number) {
  if (typeof value === "string") {
    const narrowed = value;
    //            ^?
    return narrowed;
  }
  return value;
}
