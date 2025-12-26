const SEPARATOR = ":";

type ValueRecord<K extends string, V> = { [P in K]: V };
type ArrayItem<T> = T extends Array<infer U> ? U : T;

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

export function labelledTotal<T extends string>(
  label: T,
  values: number[]
): ValueRecord<T, ArrayItem<typeof values>> {
  const total = values.reduce((acc, value) => acc + value, 0);
  return { [label]: total } as ValueRecord<T, number>;
}
