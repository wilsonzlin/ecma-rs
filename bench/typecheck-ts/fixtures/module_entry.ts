import { value as a } from "./module_a";
import { helper } from "./module_b";

export const combined = helper(a, 4);
