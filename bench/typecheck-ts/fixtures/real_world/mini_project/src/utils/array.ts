export function groupBy<T, K extends string | number>(
  items: readonly T[],
  key: (item: T) => K,
): Record<K, T[]> {
  const out = {} as Record<K, T[]>;
  for (const item of items) {
    const k = key(item);
    (out[k] || (out[k] = [])).push(item);
  }
  return out;
}

export function uniqBy<T, K>(items: readonly T[], key: (item: T) => K): T[] {
  const seen = new Set<K>();
  const out: T[] = [];
  for (const item of items) {
    const k = key(item);
    if (!seen.has(k)) {
      seen.add(k);
      out.push(item);
    }
  }
  return out;
}

export type PickKeys<T, K extends keyof T> = { [P in K]: T[P] };

export function pick<T extends object, K extends keyof T>(obj: T, keys: readonly K[]): PickKeys<T, K> {
  const out = {} as PickKeys<T, K>;
  for (const k of keys) {
    (out as any)[k] = (obj as any)[k];
  }
  return out;
}

