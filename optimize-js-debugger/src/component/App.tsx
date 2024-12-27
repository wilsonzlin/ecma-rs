import Dagre from "@dagrejs/dagre";
import { Editor } from "@monaco-editor/react";
import {
  Valid,
  Validator,
  ValuePath,
  VArray,
  VBoolean,
  VFiniteNumber,
  VInteger,
  VMap,
  VMember,
  VOptional,
  VString,
  VStringEnum,
  VStruct,
  VTagged,
  VUnion,
  VUnknown,
} from "@wzlin/valid";
import UnreachableError from "@xtjs/lib/UnreachableError";
import {
  Edge,
  Handle,
  Node,
  Panel,
  Position,
  ReactFlow,
  ReactFlowProvider,
  useEdgesState,
  useNodesInitialized,
  useNodesState,
  useReactFlow,
} from "@xyflow/react";
import "@xyflow/react/dist/style.css";
import { Fragment, useEffect, useMemo, useState } from "react";
import "./App.css";
import { decode, encode } from "@msgpack/msgpack";

class VObjectMapAsMap<K, V> extends Validator<Map<K, V>> {
  constructor(private readonly key: Validator<K>, private readonly value: Validator<V>) {
    super(new Map());
  }

  parse(theValue: ValuePath, raw: unknown): Map<K, V> {
    if (typeof raw != "object" || !raw) {
      throw theValue.isBadAsIt("is not an object");
    }
    return new Map(Object.entries(raw).map(([k, v]) => [this.key.parse(theValue.andThen(k), k), this.value.parse(theValue.andThen(k), v)]));
  }
}

enum InstTyp {
  Bin = "Bin",
  Un = "Un",
  VarAssign = "VarAssign",
  PropAssign = "PropAssign",
  CondGoto = "CondGoto",
  Call = "Call",
  ForeignLoad = "ForeignLoad",
  ForeignStore = "ForeignStore",
  UnknownLoad = "UnknownLoad",
  UnknownStore = "UnknownStore",
  Phi = "Phi",
  // We should never see this, but since we're a debugger, handle these.
  _Goto = "_Goto",
  _Label = "_Label",
  _Dummy = "_Dummy",
}

enum BinOp {
  Add = "Add",
  Div = "Div", // Divide.
  Exp = "Exp", // Exponentiate.
  Geq = "Geq", // Greater than or equals to.
  GetProp = "GetProp",
  Gt = "Gt", // Greater than.
  Leq = "Leq", // Less than or equals to.
  LooseEq = "LooseEq",
  Lt = "Lt", // Less than.
  Mod = "Mod", // Modulo.
  Mul = "Mul", // Multiply.
  NotLooseEq = "NotLooseEq",
  NotStrictEq = "NotStrictEq",
  StrictEq = "StrictEq",
  Sub = "Sub", // Subtract.
}

enum UnOp {
  Neg = "Neg",
  Not = "Not",
  Plus = "Plus",
  Typeof = "Typeof",
  Void = "Void",
}

class VBigInt extends Validator<bigint> {
  constructor() {
    super(0n);
  }

  parse(theValue: ValuePath, raw: unknown): bigint {
    // TODO Parse num_bigint serde format.
    return BigInt(raw as any);
  }
}

const vConst = new VUnion(
  new VMember(["Null", "Undefined"] as const),
  new VStruct({
    BigInt: new VOptional(new VBigInt()),
    Bool: new VOptional(new VBoolean()),
    Num: new VOptional(new VFiniteNumber()),
    Str: new VOptional(new VString()),
  }),
);

type Const = Valid<typeof vConst>;

const vArg = new VStruct({
  Builtin: new VOptional(new VString()),
  Const: new VOptional(vConst),
  Fn: new VOptional(new VInteger()),
  Var: new VOptional(new VInteger()),
});

type Arg = Valid<typeof vArg>;

const vInst = new VStruct({
  t: new VStringEnum(InstTyp),
  tgts: new VArray(new VInteger()),
  args: new VArray(vArg),
  spreads: new VArray(new VInteger()),
  labels: new VArray(new VInteger()),
  bin_op: new VOptional(new VStringEnum(BinOp)),
  un_op: new VOptional(new VStringEnum(UnOp)),
  foreign: new VOptional(new VInteger()),
  unknown: new VOptional(new VString()),
});

type Inst = Valid<typeof vInst>;

const vDebugStep = new VStruct({
  name: new VString(),
  bblockOrder: new VArray(new VInteger()),
  bblocks: new VObjectMapAsMap(new VInteger(), new VArray(vInst)),
  cfgChildren: new VObjectMapAsMap(new VInteger(), new VArray(new VInteger())),
});

type DebugStep = Valid<typeof vDebugStep>;

const vDebug = new VStruct({
  steps: new VArray(vDebugStep),
});

type Debug = Valid<typeof vDebug>;

const vProgramFunction = new VStruct({
  debug: vDebug,
  // We don't care about this field.
  body: new VUnknown(),
});

const vBuiltJs = new VStruct({
  functions: new VArray(vProgramFunction),
  top_level : vProgramFunction,
});

type BuiltJs = Valid<typeof vBuiltJs>;

type BBlockNode = Node<
  {
    label: number;
    insts: Array<Valid<typeof vInst>>;
  },
  "bblock"
>;

const ConstElement = ({ value }: { value: Const }) => {
  if (value === "Null") {
    return <span className="const null">null</span>;
  }
  if (value === "Undefined") {
    return <span className="const undefined">undefined</span>;
  }
  if (value.BigInt !== undefined) {
    return <span className="const bigint">{value.BigInt.toString()}</span>;
  }
  if (value.Bool !== undefined) {
    return <span className="const bool">{value.Bool.toString()}</span>;
  }
  if (value.Num !== undefined) {
    return <span className="const num">{value.Num}</span>;
  }
  if (value.Str !== undefined) {
    return <span className="const str">{value.Str}</span>;
  }
  throw new UnreachableError();
};

const VarElement = ({ id }: { id: number }) => (
  <span className="var">%{id}</span>
);

const ArgElement = ({ arg }: { arg: Arg }) => {
  if (arg.Builtin != undefined) {
    return <span className="builtin">{arg.Builtin}</span>;
  }
  if (arg.Const != undefined) {
    return <ConstElement value={arg.Const} />;
  }
  if (arg.Fn != undefined) {
    return <span className="fn">Fn{arg.Fn}</span>;
  }
  if (arg.Var != undefined) {
    return <VarElement id={arg.Var} />;
  }
  throw new UnreachableError();
};

const InstElement = ({ inst }: { inst: Inst }) => {
  switch (inst.t) {
    case "Bin":
      return (
        <>
          <div>
            <VarElement id={inst.tgts[0]} />
            <span className="eq"> =</span>
          </div>
          <div>
            <ArgElement arg={inst.args[0]} />
            <span> {inst.bin_op} </span>
            <ArgElement arg={inst.args[1]} />
          </div>
        </>
      );
    case "Call":
      return (
        <>
          <div>
            {inst.tgts[0] == undefined ? <span /> : <VarElement id={inst.tgts[0]} />}
            <span className="eq"> =</span>
          </div>
          <div>
            <ArgElement arg={inst.args[0]} />
            <span>(</span>
            <span>this=</span>
            <ArgElement arg={inst.args[1]} />
            {inst.args.slice(2).map((arg, i) => (
              <Fragment key={i}>
                <span>, </span>
                {inst.spreads.includes(i) && <span>&hellip;</span>}
                {arg && <ArgElement arg={arg} />}
              </Fragment>
            ))}
            <span>)</span>
          </div>
        </>
      );
    case "CondGoto":
      return (
        <>
          <div>
            <span>condgoto</span>
          </div>
          <div>
            <span className="label">:{inst.labels[0]}</span>
            <span> if </span>
            <ArgElement arg={inst.args[0]} />
            <span> else </span>
            <span className="label">:{inst.labels[1]}</span>
          </div>
        </>
      );
    case "ForeignLoad":
      return (
        <>
          <div>
            <VarElement id={inst.tgts[0]} />
            <span className="eq"> =</span>
          </div>
          <div>
            <span className="foreign">foreign {inst.foreign}</span>
          </div>
        </>
      );
    case "ForeignStore":
      return (
        <>
          <div>
            <span className="foreign">foreign {inst.foreign}</span>
            <span className="eq"> =</span>
          </div>
          <div>
            <ArgElement arg={inst.args[0]} />
          </div>
        </>
      );
    case "Phi":
      return (
        <>
          <div>
            <VarElement id={inst.tgts[0]} />
            <span className="eq"> =</span>
          </div>
          <div>
            <span>ϕ(</span>
            {inst.labels.map((label, i) => (
              <Fragment key={i}>
                <span>{i === 0 ? "" : ", "}</span>
                <span className="label">:{label}</span>
                <span> ⇒ </span>
                <ArgElement arg={inst.args[i]} />
              </Fragment>
            ))}
            <span>)</span>
          </div>
        </>
      );
    case "PropAssign":
      return (
        <>
          <div>
            <ArgElement arg={inst.args[0]} />
            <span>[</span>
            <ArgElement arg={inst.args[1]} />
            <span>]</span>
            <span className="eq"> =</span>
          </div>
          <div>
            <ArgElement arg={inst.args[2]} />
          </div>
        </>
      );
    case "Un":
      return (
        <>
          <div>
            <VarElement id={inst.tgts[0]} />
            <span className="eq"> =</span>
          </div>
          <div>
            <span>{inst.un_op} </span>
            <ArgElement arg={inst.args[0]} />
          </div>
        </>
      );
    case "UnknownLoad":
      return (
        <>
          <div>
            <VarElement id={inst.tgts[0]} />
            <span className="eq"> =</span>
          </div>
          <div>
            <span className="unknown">unknown {inst.unknown}</span>
          </div>
        </>
      );
    case "UnknownStore":
      return (
        <>
          <div>
            <span className="unknown">unknown {inst.unknown}</span>
            <span className="eq"> =</span>
          </div>
          <div>
            <ArgElement arg={inst.args[0]} />
          </div>
        </>
      );
    case "VarAssign":
      return (
        <>
          <div>
            <VarElement id={inst.tgts[0]} />
            <span className="eq"> =</span>
          </div>
          <div>
            <ArgElement arg={inst.args[0]} />
          </div>
        </>
      );
    case "_Goto":
      return (
        <>
          <div>
            <span className="invalid-inst">goto</span>
          </div>
          <div>
            <span className="label">:{inst.labels[0]}</span>
          </div>
        </>
      );
    case "_Label":
      return (
        <>
          <div>
            <span className="invalid-inst">label</span>
          </div>
          <div>
            <span className="label">:{inst.labels[0]}</span>
          </div>
        </>
      );
    case "_Dummy":
      return (
        <>
          <div>
            <span className="invalid-inst">dummy</span>
          </div>
          <div/>
        </>
      );
    default:
      throw new UnreachableError(inst.t);
  }
};

const BBlockElement = ({
  data: { label, insts },
}: {
  data: BBlockNode["data"];
}) => {
  // Due to the way our layout is calculated, loops will sometimes have edges in a straight line that overlap with each other and obscures the flow, so we use the left as the target instead of the top.
  return (
    <>
      <Handle type="target" position={Position.Left} />
      <div className="bblock">
        <h1>:{label}</h1>
        <ol className="insts">
          {insts.map((s, i) => (
            <li key={i} className="inst">
              <InstElement inst={s} />
            </li>
          ))}
        </ol>
      </div>
      <Handle type="source" position={Position.Bottom} />
    </>
  );
};

const getLayoutedElements = (
  nodes: Array<BBlockNode>,
  edges: Array<Edge>,
  options: { direction: string },
) => {
  const g = new Dagre.graphlib.Graph().setDefaultEdgeLabel(() => ({}));
  g.setGraph({ rankdir: options.direction });

  for (const edge of edges) {
    g.setEdge(edge.source, edge.target);
  }
  for (const node of nodes) {
    g.setNode(node.id, {
      ...node,
      width: node.measured?.width ?? 0,
      height: node.measured?.height ?? 0,
    });
  }

  Dagre.layout(g);

  return {
    nodes: nodes.map((node) => {
      const position = g.node(node.id);
      // We are shifting the Dagre node position (anchor=center center) to the top left
      // so it matches the React Flow node anchor point (top left).
      const x = position.x - (node.measured?.width ?? 0) / 2;
      const y = position.y - (node.measured?.height ?? 0) / 2;
      return { ...node, position: { x, y } };
    }),
    edges,
  };
};

const nodeTypes = {
  bblock: BBlockElement,
};

const Graph = ({
  stepNames,
  step,
}: {
  stepNames: Array<string>;
  step: DebugStep;
}) => {
  const initNodes = useMemo(
    () =>
      // WARNING: Use step.bblocks not step.bblock_order as the latter may hide disconnected components.
      [...step.bblocks].map<BBlockNode>(([label, insts]) => ({
        id: `${label}`,
        type: "bblock",
        data: {
          label,
          insts,
        },
        position: { x: 0, y: 0 },
      })),
    [step],
  );
  const initEdges = useMemo(
    () =>
      [...step.cfgChildren].flatMap(([src, dests]) =>
        dests.map<Edge>((dest) => ({
          id: `${src}-${dest}`,
          source: `${src}`,
          target: `${dest}`,
          animated: true,
        })),
      ),
    [step],
  );

  const { fitView } = useReactFlow();
  const [nodes, setNodes, onNodesChange] = useNodesState(initNodes);
  const [edges, setEdges, onEdgesChange] = useEdgesState(initEdges);
  // https://github.com/xyflow/xyflow/issues/533#issuecomment-1601814350
  const nodesSized = useNodesInitialized();
  const [layoutCalculated, setLayoutCalculated] = useState(false);
  // Force update nodes and edges when source code or step changes.
  // (Otherwise, new nodes and edges are left unused.)
  useEffect(() => {
    setNodes(initNodes);
    setEdges(initEdges);
    setLayoutCalculated(false);
  }, [step]);

  useEffect(() => {
    if (!nodesSized || layoutCalculated) {
      return;
    }
    const layouted = getLayoutedElements(nodes, edges, { direction: "TB" });
    setNodes(layouted.nodes);
    setEdges(layouted.edges);
    setLayoutCalculated(true);
  }, [
    // WARNING: This must *NOT* run when `nodes` or `edges` change, as they will have a size of 0 but nodesSized will be true.
    // This is correct anyway: we only run after sizing, not before (when inputs change) or after (when layout is calculated).
    nodesSized,
  ]);

  useEffect(() => {
    if (nodesSized && layoutCalculated) {
      fitView();
    }
  }, [layoutCalculated]);

  return (
    <ReactFlow
      edges={edges}
      fitView
      nodes={nodes}
      nodesDraggable={false}
      nodeTypes={nodeTypes}
      onEdgesChange={onEdgesChange}
      onNodesChange={onNodesChange}
    >
      <Panel position="top-left">
        <ul className="step-names">
          {stepNames.map((name, i) => (
            <li key={i} className={name == step.name ? "current" : ""}>
              {name}
            </li>
          ))}
        </ul>
      </Panel>
    </ReactFlow>
  );
};


const INIT_SOURCE = `
(() => {
  a?.b?.c;
  let x = 1;
  if (x) {
    g();
    x += Math.round(1.1);
    for (;;) {
      x += 1;
      setTimeout(() => {
        h(x);
      }, 1000);
    }
  }
  f(x);
})();
`.trim();

const BBlocksExplorer = ({
  data,
}: {
  data: Debug;
}) => {
  const [stepIdx, setStepIdx] = useState(0);
  const actualStepIdx = Math.min(stepIdx, data.steps.length - 1);
  const stepNames = useMemo(() => data.steps.map((s) => s.name), [data]);
  const step = data.steps[actualStepIdx];

  useEffect(() => {
    const listener = (e: KeyboardEvent) => {
      if (e.key === "ArrowLeft" || e.key === "ArrowUp") {
        setStepIdx((idx) => Math.max(0, idx - 1));
      } else if (e.key === "ArrowRight" || e.key === "ArrowDown") {
        setStepIdx((idx) => Math.min((data?.steps.length ?? 1) - 1, idx + 1));
      }
    };
    window.addEventListener("keydown", listener);
    return () => window.removeEventListener("keydown", listener);
  }, [data]);

  return (
    <div className="BBlocksExplorer">
      <ReactFlowProvider>
        <Graph step={step} stepNames={stepNames} />
      </ReactFlowProvider>
    </div>
  )
};

export const App = ({}: {}) => {
  const [source, setSource] = useState(INIT_SOURCE);
  const [data, setData] = useState<BuiltJs>();
  const [curFnId, setCurFnId] = useState<number>();
  const [error, setError] = useState<string>();
  useEffect(() => {
    const src = source.trim();
    if (!src) {
      return;
    }
    const ac = new AbortController();
    (async () => {
      const res = await fetch("//localhost:3001/compile", {
        signal: ac.signal,
        method: "POST",
        headers: {
          "Content-Type": "application/msgpack",
        },
        // TODO Module mode.
        body: encode({ source: src, is_global: true }),
      });
      const raw = decode(await res.arrayBuffer());
      setData(vBuiltJs.parseRoot(raw));
    })();
    return () => ac.abort();
  }, [source]);
  const curFn = data?.functions[curFnId!] ?? data?.top_level;

  return (
    <div className="App">
      <main>
        <div className="canvas">
          <div className="function-tabs">
            {[undefined, ...data?.functions.map((_, i) => i) ?? []].map(fnId => (
              <button key={fnId ?? -1} onClick={() => setCurFnId(fnId)}>
                {fnId == undefined ? "Top level" : `Fn${fnId}`}
              </button>
            ))}
          </div>
          {curFn && (
            <BBlocksExplorer data={curFn.debug} />
          )}
        </div>
        <div className="pane">
          <div className="info">
            {error && <p className="error">{error}</p>}
          </div>
          <div className="editor">
            <Editor
              height="50vh"
              width="40vw"
              defaultLanguage="javascript"
              defaultValue={INIT_SOURCE}
              onChange={(e) => setSource(e?.trim() ?? "")}
            />
          </div>
        </div>
      </main>
    </div>
  );
};
