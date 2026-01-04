import { target } from "./lib";

export const result = target.addEventListener("click", (ev) => {
  void ev;
});
