export const weights = [1, 2, 3, 4];

export function normalise(values: number[]) {
  let total = 0;
  for (let i = 0; i < values.length; i++) {
    total += values[i];
  }
  if (total === 0) {
    return values.slice();
  }
  const normalized: number[] = [];
  for (let i = 0; i < values.length; i++) {
    normalized.push(values[i] / total);
  }
  return normalized;
}

export function bump(values: number[], delta: number) {
  const next: number[] = [];
  for (let i = 0; i < values.length; i++) {
    next.push(values[i] + delta);
  }
  return next;
}
