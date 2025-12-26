type KeysMatching<T, V> = { [K in keyof T]-?: T[K] extends V ? K : never }[keyof T];

type DeepPartial<T> = { [K in keyof T]?: T[K] extends object ? DeepPartial<T[K]> : T[K] };

export type Selector<T, K extends keyof T> = { [P in K]: T[P] };

export function mergeDefaults<T extends object>(value: DeepPartial<T>, defaults: T): T {
  const result: any = { ...defaults };
  for (const key in value) {
    const maybe = (value as any)[key];
    if (maybe !== undefined) {
      result[key] = maybe;
    }
  }
  return result as T;
}

export function pickValue<T extends Record<string, unknown>, V>(
  value: T,
  key: KeysMatching<T, V>
): V | undefined {
  const picked = value[key as keyof T];
  if (picked && typeof picked === "object") {
    return picked as V;
  }
  return picked as V | undefined;
}

type Flatten<T> = T extends Array<infer U> ? U : T;

export function firstValue<T>(list: T[]): Flatten<T[]> | undefined {
  return list[0];
}
