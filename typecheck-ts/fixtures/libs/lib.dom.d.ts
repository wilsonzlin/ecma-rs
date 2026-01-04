// Minimal DOM lib for tests
interface Event {
  "type": string;
}

declare const document: {
  title: string;
  addEventListener(eventType: string, listener: (event: Event) => void): void;
};

declare const window: {
  document: typeof document;
};
