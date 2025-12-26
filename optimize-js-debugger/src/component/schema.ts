import {
  Valid,
  Validator,
  ValuePath,
  VArray,
  VBoolean,
  VFiniteNumber,
  VInteger,
  VMap,
  VOptional,
  VString,
  VStringEnum,
  VStruct,
  VTagged,
  VUnion,
  VUnknown,
} from "@wzlin/valid";

export type StableId =
  | {
      type: "number";
      value: string;
    }
  | { type: "text"; value: string };

export type StableConst =
  | { kind: "null" | "undefined" }
  | { kind: "big_int"; value: string }
  | { kind: "bool"; value: boolean }
  | { kind: "num"; value: number }
  | { kind: "str"; value: string };

export type StableArg =
  | { kind: "builtin"; value: string }
  | { kind: "const"; value: StableConst }
  | { kind: "fn"; value: number }
  | { kind: "var"; value: number };

export type StableInst = {
  t: string;
  tgts: number[];
  args: StableArg[];
  spreads: number[];
  labels: number[];
  binOp?: string;
  unOp?: string;
  foreign?: StableId;
  unknown?: string;
};

export type StableDebugStep = {
  name: string;
  bblockOrder: number[];
  bblocks: Map<number, StableInst[]> | Record<string, StableInst[]>;
  cfgChildren: Map<number, number[]> | Record<string, number[]>;
};

export type StableDebug = {
  steps: StableDebugStep[];
};

export type StableCfg = {
  bblockOrder: number[];
  bblocks: Map<number, StableInst[]>;
  cfgChildren: Map<number, number[]>;
};

export type StableFunction = {
  debug: StableDebug;
  cfg: StableCfg;
};

export type StableProgramSymbol = {
  id: StableId;
  name: string;
  scope: StableId;
  captured: boolean;
};

export type StableFreeSymbols = {
  top_level: StableId[];
  functions: StableId[][];
};

export type StableScope = {
  id: StableId;
  parent?: StableId;
  kind: string;
  symbols?: StableId[];
  children?: StableId[];
  tdz_bindings?: StableId[];
  is_dynamic: boolean;
  has_direct_eval: boolean;
};

export type StableProgramSymbols = {
  symbols: StableProgramSymbol[];
  free_symbols?: StableFreeSymbols;
  names: string[];
  scopes: StableScope[];
};

export type Program = {
  functions: StableFunction[];
  top_level: StableFunction;
  symbols?: StableProgramSymbols;
};

class VObjectMapAsMap<K, V> extends Validator<Map<K, V>> {
  constructor(
    private readonly key: Validator<K>,
    private readonly value: Validator<V>,
  ) {
    super(new Map());
  }

  parse(theValue: ValuePath, raw: unknown): Map<K, V> {
    if (typeof raw != "object" || !raw) {
      throw theValue.isBadAsIt("is not an object");
    }
    return new Map(
      Object.entries(raw).map(([k, v]) => [
        this.key.parse(theValue.andThen(k), k),
        this.value.parse(theValue.andThen(k), v),
      ]),
    );
  }
}

const vId = new VStruct({
  type: new VStringEnum({
    number: "number",
    text: "text",
  }),
  value: new VString(),
});

const vConst = new VTagged("kind", {
  big_int: new VStruct({ value: new VString() }),
  bool: new VStruct({ value: new VBoolean() }),
  num: new VStruct({ value: new VFiniteNumber() }),
  str: new VStruct({ value: new VString() }),
  null: new VStruct({}),
  undefined: new VStruct({}),
});

const vArg = new VTagged("kind", {
  builtin: new VStruct({ value: new VString() }),
  const: new VStruct({ value: vConst }),
  fn: new VStruct({ value: new VInteger() }),
  var: new VStruct({ value: new VInteger() }),
});

const vInst = new VStruct({
  t: new VString(),
  tgts: new VArray(new VInteger()),
  args: new VArray(vArg),
  spreads: new VArray(new VInteger()),
  labels: new VArray(new VInteger()),
  binOp: new VOptional(new VString()),
  unOp: new VOptional(new VString()),
  foreign: new VOptional(vId),
  unknown: new VOptional(new VString()),
});

const vDebugStep = new VStruct({
  name: new VString(),
  bblockOrder: new VArray(new VInteger()),
  bblocks: new VObjectMapAsMap(new VInteger(), new VArray(vInst)),
  cfgChildren: new VObjectMapAsMap(new VInteger(), new VArray(new VInteger())),
});

const vDebug = new VStruct({
  steps: new VArray(vDebugStep),
});

const vCfg = new VStruct({
  bblockOrder: new VArray(new VInteger()),
  bblocks: new VObjectMapAsMap(new VInteger(), new VArray(vInst)),
  cfgChildren: new VObjectMapAsMap(new VInteger(), new VArray(new VInteger())),
});

const vFunction = new VStruct({
  debug: vDebug,
  cfg: vCfg,
});

const vProgramSymbol = new VStruct({
  id: vId,
  name: new VString(),
  scope: vId,
  captured: new VBoolean(),
});

const vFreeSymbols = new VStruct({
  top_level: new VArray(vId),
  functions: new VArray(new VArray(vId)),
});

const vScope = new VStruct({
  id: vId,
  parent: new VOptional(vId),
  kind: new VString(),
  symbols: new VOptional(new VArray(vId)),
  children: new VOptional(new VArray(vId)),
  tdz_bindings: new VOptional(new VArray(vId)),
  is_dynamic: new VBoolean(),
  has_direct_eval: new VBoolean(),
});

const vProgramSymbols = new VStruct({
  symbols: new VArray(vProgramSymbol),
  free_symbols: new VOptional(vFreeSymbols),
  names: new VArray(new VString()),
  scopes: new VArray(vScope),
});

const vProgram = new VStruct({
  functions: new VArray(vFunction),
  top_level: vFunction,
  symbols: new VOptional(vProgramSymbols),
});

export const parseProgram = (raw: unknown): Program => vProgram.parseRoot(raw);

export const formatId = (id: StableId): string => id.value;

export const idMatchesQuery = (id: StableId, query: string): boolean =>
  formatId(id).toLowerCase().includes(query);

export const constToLabel = (value: StableConst): string => {
  switch (value.kind) {
    case "null":
      return "null";
    case "undefined":
      return "undefined";
    case "big_int":
      return `${BigInt(value.value).toString()}n`;
    case "bool":
      return value.value ? "true" : "false";
    case "num":
      return `${value.value}`;
    case "str":
      return JSON.stringify(value.value);
  }
};

export const argToLabel = (arg: StableArg): string => {
  switch (arg.kind) {
    case "builtin":
      return arg.value;
    case "const":
      return constToLabel(arg.value);
    case "fn":
      return `Fn${arg.value}`;
    case "var":
      return `%${arg.value}`;
  }
};

export const buildSymbolNames = (
  symbols?: StableProgramSymbols,
): Map<string, string> | undefined => {
  if (!symbols) {
    return undefined;
  }
  const map = new Map<string, string>();
  for (const symbol of symbols.symbols) {
    map.set(formatId(symbol.id), symbol.name);
  }
  return map;
};

export type NormalizedBlock = {
  label: number;
  insts: StableInst[];
};

export type NormalizedStep = {
  name: string;
  blocks: NormalizedBlock[];
  children: Map<number, number[]>;
};

const normalizeBBlockEntries = (
  blocks: StableDebugStep["bblocks"],
): Array<[number, StableInst[]]> =>
  blocks instanceof Map
    ? [...blocks.entries()]
    : Object.entries(blocks).map(([k, v]) => [Number(k), v]);

const normalizeChildEntries = (
  children: StableDebugStep["cfgChildren"],
): Map<number, number[]> =>
  children instanceof Map
    ? children
    : new Map(
        Object.entries(children).map(([k, v]) => [
          Number(k),
          v.map((n) => Number(n)),
        ]),
      );

export const normalizeStep = (step: StableDebugStep): NormalizedStep => {
  const blocks = normalizeBBlockEntries(step.bblocks)
    .map(([label, insts]) => ({ label, insts }))
    .sort((a, b) => a.label - b.label);
  return {
    name: step.name,
    blocks,
    children: normalizeChildEntries(step.cfgChildren),
  };
};

const instMatchesQuery = (
  inst: StableInst,
  query: string,
  symbolNames?: Map<string, string>,
): boolean => {
  if (inst.t.toLowerCase().includes(query)) {
    return true;
  }
  if (inst.unknown?.toLowerCase().includes(query)) {
    return true;
  }
  if (inst.foreign) {
    const key = formatId(inst.foreign);
    if (key.toLowerCase().includes(query)) {
      return true;
    }
    const name = symbolNames?.get(key);
    if (name && name.toLowerCase().includes(query)) {
      return true;
    }
  }
  const args = [
    ...inst.tgts.map((t) => `%${t}`),
    ...inst.labels.map((l) => `:${l}`),
    ...inst.args.map(argToLabel),
  ];
  return args.some((arg) => arg.toLowerCase().includes(query));
};

export const blockMatchesQuery = (
  block: NormalizedBlock,
  query: string,
  symbolNames?: Map<string, string>,
): boolean => {
  if (!query) {
    return true;
  }
  if (`${block.label}`.includes(query)) {
    return true;
  }
  return block.insts.some((inst) => instMatchesQuery(inst, query, symbolNames));
};

const instSignature = (inst: StableInst): string =>
  JSON.stringify({
    t: inst.t,
    tgts: inst.tgts,
    args: inst.args.map(argToLabel),
    spreads: inst.spreads,
    labels: inst.labels,
    binOp: inst.binOp,
    unOp: inst.unOp,
    foreign: inst.foreign ? formatId(inst.foreign) : undefined,
    unknown: inst.unknown,
  });

export const computeChangedBlocks = (
  steps: NormalizedStep[],
): Array<Set<number>> => {
  const results: Array<Set<number>> = [];
  for (let i = 0; i < steps.length; i++) {
    const current = steps[i];
    const prev = steps[i - 1];
    const changed = new Set<number>();
    if (!prev) {
      current.blocks.forEach((b) => changed.add(b.label));
    } else {
      const prevMap = new Map(prev.blocks.map((b) => [b.label, b.insts]));
      for (const block of current.blocks) {
        const prevInsts = prevMap.get(block.label);
        if (!prevInsts) {
          changed.add(block.label);
          continue;
        }
        const sigA = block.insts.map(instSignature).join("|");
        const sigB = prevInsts.map(instSignature).join("|");
        if (sigA !== sigB) {
          changed.add(block.label);
        }
      }
    }
    results.push(changed);
  }
  return results;
};
