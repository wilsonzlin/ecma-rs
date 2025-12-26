function formatValue(x: string): string;
function formatValue(x: number): string;
function formatValue(x: string | number) {
  return x.toString();
}

export const overloadedResult = formatValue(123);
                     // ^?
