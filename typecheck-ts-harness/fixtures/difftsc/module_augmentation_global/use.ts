import { extra, v } from "./m";
import type { Foo } from "./m";

(v as Foo).y.toUpperCase();
extra.toFixed();

const g: GlobalThing = { z: 1 };
g.z.toFixed();

