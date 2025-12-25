const SEPARATOR = ":";

export function formatId(prefix: string, value: number) {
  return prefix + "-" + value.toString();
}

export function combineLabel(label: string, values: number[]) {
  let total = 0;
  for (let i = 0; i < values.length; i++) {
    total += values[i];
  }
  return label + SEPARATOR + total.toString();
}
