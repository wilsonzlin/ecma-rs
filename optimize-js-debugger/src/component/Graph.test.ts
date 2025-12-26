import { describe, expect, test } from "vitest";
import { Edge } from "@xyflow/react";
import { BBlockNode, getLayoutedElements } from "./Graph";

describe("getLayoutedElements", () => {
  test("lays out nodes deterministically", () => {
    const nodes: Array<BBlockNode> = [
      {
        id: "1",
        type: "bblock",
        data: { label: 1, insts: [] },
        position: { x: 0, y: 0 },
      },
      {
        id: "2",
        type: "bblock",
        data: { label: 2, insts: [] },
        position: { x: 0, y: 0 },
      },
    ];
    const edges: Array<Edge> = [
      { id: "1-2", source: "1", target: "2" },
      { id: "2-1", source: "2", target: "1" },
    ];

    const layout = getLayoutedElements(nodes, edges, { direction: "TB" });
    expect(layout.nodes).toHaveLength(2);
    expect(layout.nodes[0].position.x).toBeTypeOf("number");
    expect(layout.nodes.map((n) => n.id)).toEqual(["1", "2"]);
  });
});
