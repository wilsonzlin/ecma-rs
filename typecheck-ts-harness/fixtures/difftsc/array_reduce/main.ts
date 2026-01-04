import { nums } from "./lib";

export const numberResult = nums.reduce((acc, cur) => acc);

const init: string = "";
export const stringResult = nums.reduce((acc, cur) => acc, init);
