import { describe, expect, test } from "vitest";
import {
  NormalizedStep,
  computeChangedBlocks,
  formatId,
  normalizeStep,
  StableDebugStep,
  StableInst,
} from "./schema";

const sampleInst = (t: string): StableInst => ({
  t,
  tgts: [0],
  args: [],
  spreads: [],
  labels: [],
});

const buildStep = (name: string, inst: StableInst): StableDebugStep => ({
  name,
  bblockOrder: [0],
  bblocks: {
    0: [inst],
  },
  cfgChildren: {
    0: [],
  },
});

describe("formatId", () => {
  test("renders numeric IDs", () => {
    expect(formatId({ type: "number", value: "18446744073709551616" })).toBe(
      "18446744073709551616",
    );
  });

  test("renders text IDs", () => {
    expect(formatId({ type: "text", value: "sym-1" })).toBe("sym-1");
  });
});

describe("normalizeStep", () => {
  test("converts map keys to numbers", () => {
    const step = normalizeStep(buildStep("demo", sampleInst("Bin")));
    expect(step.blocks[0].label).toBe(0);
    expect([...step.children.keys()]).toEqual([0]);
  });
});

describe("computeChangedBlocks", () => {
  test("detects differences between steps", () => {
    const steps: NormalizedStep[] = [
      normalizeStep(buildStep("a", sampleInst("Bin"))),
      normalizeStep(buildStep("b", sampleInst("Bin"))),
      normalizeStep(buildStep("c", sampleInst("Phi"))),
    ];
    const changes = computeChangedBlocks(steps);
    expect(changes[0].has(0)).toBe(true);
    expect(changes[1].size).toBe(0);
    expect(changes[2].has(0)).toBe(true);
  });
});
