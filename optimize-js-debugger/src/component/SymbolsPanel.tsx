import { useMemo } from "react";
import { StableProgramSymbols, StableScope, StableProgramSymbol, formatId } from "./schema";

const buildScopeMap = (symbols: StableProgramSymbols) => {
  const map = new Map<string, StableScope>();
  for (const scope of symbols.scopes) {
    map.set(formatId(scope.id), scope);
  }
  return map;
};

const collectScopeSymbols = (
  scope: StableScope,
  symbols: StableProgramSymbols,
): StableProgramSymbol[] =>
  symbols.symbols.filter((symbol) => formatId(symbol.scope) === formatId(scope.id));

const scopeMatchesQuery = (
  scope: StableScope,
  allSymbols: StableProgramSymbols,
  filter: string,
): boolean => {
  if (!filter) {
    return true;
  }
  const lower = filter.toLowerCase();
  if (formatId(scope.id).toLowerCase().includes(lower)) {
    return true;
  }
  if (scope.kind.toLowerCase().includes(lower)) {
    return true;
  }
  const symbols = collectScopeSymbols(scope, allSymbols);
  return symbols.some(
    (symbol) =>
      symbol.name.toLowerCase().includes(lower) ||
      formatId(symbol.id).toLowerCase().includes(lower),
  );
};

const ScopeTree = ({
  scope,
  symbols,
  scopeMap,
  filter,
}: {
  scope: StableScope;
  symbols: StableProgramSymbols;
  scopeMap: Map<string, StableScope>;
  filter: string;
}) => {
  const children = scope.children?.map((id) => scopeMap.get(formatId(id))!).filter(Boolean) ?? [];
  const visibleChildren = children.filter((child) => scopeMatchesQuery(child, symbols, filter));
  const scopeSymbols = collectScopeSymbols(scope, symbols).filter(
    (symbol) =>
      !filter ||
      symbol.name.toLowerCase().includes(filter.toLowerCase()) ||
      formatId(symbol.id).toLowerCase().includes(filter.toLowerCase()),
  );

  return (
    <li className="scope">
      <header>
        <span className="scope-kind">{scope.kind}</span>
        <span className="scope-id">#{formatId(scope.id)}</span>
        {scope.is_dynamic && <span className="badge">dynamic</span>}
        {scope.has_direct_eval && <span className="badge warn">eval</span>}
      </header>
      <ul className="symbols">
        {scopeSymbols.map((symbol) => (
          <li key={formatId(symbol.id)}>
            <span className="symbol-name">{symbol.name}</span>
            <span className="symbol-id">({formatId(symbol.id)})</span>
            {symbol.captured && <span className="badge">captured</span>}
          </li>
        ))}
      </ul>
      {visibleChildren.length > 0 && (
        <ul className="scopes">
          {visibleChildren.map((child) => (
            <ScopeTree
              key={formatId(child.id)}
              scope={child}
              symbols={symbols}
              scopeMap={scopeMap}
              filter={filter}
            />
          ))}
        </ul>
      )}
    </li>
  );
};

export const SymbolsPanel = ({
  symbols,
  filter,
}: {
  symbols?: StableProgramSymbols;
  filter: string;
}) => {
  const scopeMap = useMemo(
    () => (symbols ? buildScopeMap(symbols) : new Map<string, StableScope>()),
    [symbols],
  );
  const roots = useMemo(() => {
    if (!symbols) {
      return [];
    }
    const hasParent = new Set(
      symbols.scopes
        .map((s) => s.parent)
        .filter(Boolean)
        .map((id) => formatId(id!)),
    );
    return symbols.scopes
      .filter((scope) => !hasParent.has(formatId(scope.id)))
      .filter((scope) => scopeMatchesQuery(scope, symbols, filter));
  }, [symbols, filter]);

  if (!symbols) {
    return (
      <div className="SymbolsPanel">
        <p>No symbol information available.</p>
      </div>
    );
  }

  return (
    <div className="SymbolsPanel">
      <div className="summary">
        <span>{symbols.scopes.length} scopes</span>
        <span>{symbols.symbols.length} symbols</span>
      </div>
      <ul className="scopes">
        {roots.map((scope) => (
          <ScopeTree
            key={formatId(scope.id)}
            scope={scope}
            symbols={symbols}
            scopeMap={scopeMap}
            filter={filter}
          />
        ))}
      </ul>
    </div>
  );
};
