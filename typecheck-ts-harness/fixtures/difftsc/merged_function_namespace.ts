function Lib(value: number): number {
  return value * 2;
}

namespace Lib {
  export const version = "merged";
  export function helper(label: string): string {
    return label + version;
  }
}

export const doubled = Lib(2);
export const label = Lib.helper("ok");
export { Lib };
