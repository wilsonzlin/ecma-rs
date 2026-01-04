export interface Target {
  addEventListener(
    eventType: "click",
    listener: (this: Target, ev: { kind: "click" }) => void,
  ): "click";
  addEventListener(eventType: string, listener: (ev: any) => void): "fallback";
}

export const target: Target;
