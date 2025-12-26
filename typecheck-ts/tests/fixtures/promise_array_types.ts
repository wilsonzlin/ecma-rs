type UsesPromise = Promise<string>;
type UsesArray = Array<number>;

const promise: UsesPromise = Promise.resolve("ok");
const list: UsesArray = [];
