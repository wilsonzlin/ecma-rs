// @target: ESNext

class AsyncD implements AsyncDisposable {
  value: number = 1;

  [Symbol.asyncDispose](): void {}
}

async function main() {
  await using x = new AsyncD();
           // ^?
}

