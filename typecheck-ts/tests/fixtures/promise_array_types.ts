type UsesPromise = Promise<string>;
type UsesArray = Array<number>;
type UsesMap = Map<string, number>;
type UsesSymbolConstructor = SymbolConstructor;

const promise: UsesPromise = Promise.resolve("ok");
const list: UsesArray = [];
