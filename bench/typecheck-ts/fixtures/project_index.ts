import { weights, normalise, bump } from "./project_numbers";
import { formatId, combineLabel } from "./project_text";

export function renderScore(userId: number, scores: number[]) {
  const boosted = bump(scores, 1);
  const normalized = normalise(boosted);
  const label = formatId("user", userId);
  return combineLabel(label, normalized);
}

export const defaultScore = renderScore(7, weights);
