import "./m";

declare module "./m" {
  interface Foo {
    y: string;
  }

  export const extra: number;
}

declare global {
  interface GlobalThing {
    z: number;
  }
}

