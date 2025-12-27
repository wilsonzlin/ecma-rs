// @strict: true
import { f } from "./m";

f.call({ x: 1 }, 2);
f.call({ x: "no" }, 2);
