import { Editor } from "@monaco-editor/react";
import { decode, encode } from "@msgpack/msgpack";
import { useEffect, useMemo, useState } from "react";
import { Graph } from "./Graph";
import { SymbolsPanel } from "./SymbolsPanel";
import "./App.css";
import {
  Program,
  NormalizedStep,
  computeChangedBlocks,
  formatId,
  normalizeStep,
  parseProgram,
  buildSymbolNames,
} from "./schema";

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

export const App = () => {
  const [source, setSource] = useState(INIT_SOURCE);
  const [data, setData] = useState<Program>();
  const [curFnId, setCurFnId] = useState<number>();
  const [error, setError] = useState<string>();
  const [isGlobal, setIsGlobal] = useState(true);
  const [filter, setFilter] = useState("");
  const [stepIdx, setStepIdx] = useState(0);
  const [view, setView] = useState<"cfg" | "symbols">("cfg");
  const [showDiff, setShowDiff] = useState(true);

  useEffect(() => {
    const src = source.trim();
    if (!src) {
      return;
    }
    const ac = new AbortController();
    (async () => {
      try {
        const res = await fetch("//localhost:3001/compile", {
          signal: ac.signal,
          method: "POST",
          headers: {
            "Content-Type": "application/msgpack",
          },
          body: encode({ source: src, is_global: isGlobal }),
        });
        const raw = decode(await res.arrayBuffer());
        if (!res.ok) {
          const message = Array.isArray((raw as any)?.diagnostics)
            ? (raw as any).diagnostics.map((d: any) => `${d.code}: ${d.message}`).join("\n")
            : `HTTP ${res.status}`;
          throw new Error(message);
        }
        setData(parseProgram(raw));
        setError(undefined);
        setStepIdx(0);
      } catch (err) {
        if (err instanceof DOMException && err.name === "AbortError") {
          return;
        }
        console.error(err);
        setError(String(err));
        setData(undefined);
        setCurFnId(undefined);
      }
    })();
    return () => ac.abort();
  }, [source, isGlobal]);

  const symbolNames = useMemo(() => buildSymbolNames(data?.symbols), [data]);
  const currentFunction =
    curFnId == undefined ? data?.top_level : data?.functions[curFnId];
  const normalizedSteps: NormalizedStep[] = useMemo(
    () => currentFunction?.debug.steps.map(normalizeStep) ?? [],
    [currentFunction],
  );
  const diffs = useMemo(
    () => computeChangedBlocks(normalizedSteps),
    [normalizedSteps],
  );
  const safeStepIdx =
    normalizedSteps.length === 0
      ? 0
      : Math.min(stepIdx, normalizedSteps.length - 1);
  const currentStep = normalizedSteps[safeStepIdx];

  useEffect(() => {
    const listener = (e: KeyboardEvent) => {
      if (normalizedSteps.length === 0) {
        return;
      }
      if (e.key === "ArrowLeft" || e.key === "ArrowUp") {
        setStepIdx((idx) => Math.max(0, idx - 1));
      } else if (e.key === "ArrowRight" || e.key === "ArrowDown") {
        setStepIdx((idx) =>
          Math.min((normalizedSteps.length ?? 1) - 1, idx + 1),
        );
      }
    };
    window.addEventListener("keydown", listener);
    return () => window.removeEventListener("keydown", listener);
  }, [normalizedSteps.length]);

  return (
    <div className="App">
      <main>
        <div className="canvas">
          <div className="toolbar">
            <div className="function-tabs">
              {[undefined, ...(data?.functions.map((_, i) => i) ?? [])].map(
                (fnId) => (
                  <button
                    key={fnId ?? -1}
                    className={fnId === curFnId ? "active" : ""}
                    onClick={() => {
                      setCurFnId(fnId);
                      setStepIdx(0);
                    }}
                  >
                    {fnId == undefined ? "Top level" : `Fn${fnId}`}
                  </button>
                ),
              )}
            </div>
            <div className="step-controls">
              <label>
                Step:
                <select
                  value={safeStepIdx}
                  onChange={(e) => setStepIdx(Number(e.target.value))}
                >
                  {normalizedSteps.map((step, i) => (
                    <option key={i} value={i}>
                      {i}. {step.name}
                    </option>
                  ))}
                </select>
              </label>
              <label className="toggle">
                <input
                  type="checkbox"
                  checked={showDiff}
                  onChange={(e) => setShowDiff(e.target.checked)}
                />
                Highlight changed blocks
              </label>
              <label className="toggle">
                <input
                  type="radio"
                  name="view"
                  checked={view === "cfg"}
                  onChange={() => setView("cfg")}
                />
                CFG
              </label>
              <label className="toggle">
                <input
                  type="radio"
                  name="view"
                  checked={view === "symbols"}
                  onChange={() => setView("symbols")}
                />
                Symbols
              </label>
              <input
                type="search"
                placeholder="Filter symbol/temp/label"
                value={filter}
                onChange={(e) => setFilter(e.target.value)}
              />
              {currentStep && (
                <span className="step-summary">
                  {currentStep.blocks.length} blocks •{" "}
                  {showDiff && diffs[safeStepIdx]
                    ? `${diffs[safeStepIdx].size} changed`
                    : "diffs off"}
                </span>
              )}
            </div>
          </div>

          {view === "cfg" && currentStep && (
            <Graph
              step={currentStep}
              stepNames={normalizedSteps.map((s) => s.name)}
              symbolNames={symbolNames}
              changed={showDiff ? diffs[safeStepIdx] : undefined}
              filter={filter}
            />
          )}
          {view === "symbols" && (
            <SymbolsPanel symbols={data?.symbols} filter={filter} />
          )}
        </div>
        <div className="pane">
          <div className="info">
            {error && <p className="error">{error}</p>}
            {data?.symbols && (
              <p className="symbol-summary">
                {data.symbols.symbols.length} symbols across{" "}
                {data.symbols.scopes.length} scopes
              </p>
            )}
          </div>
          <div className="editor">
            <div className="controls">
              <label>
                Top-level mode:
                <select
                  value={isGlobal ? "global" : "module"}
                  onChange={(e) => setIsGlobal(e.target.value === "global")}
                >
                  <option value="global">global</option>
                  <option value="module">module</option>
                </select>
              </label>
            </div>
            <Editor
              height="50vh"
              width="40vw"
              defaultLanguage="javascript"
              defaultValue={INIT_SOURCE}
              onChange={(e) => setSource(e?.trim() ?? "")}
            />
            {data && (
              <div className="legend">
                <span>Foreign vars: </span>
                <span>
                  {[...(data.symbols?.symbols ?? [])]
                    .filter((s) => s.captured)
                    .map((s) => formatId(s.id))
                    .join(", ") || "none"}
                </span>
              </div>
            )}
          </div>
        </div>
      </main>
    </div>
  );
};
