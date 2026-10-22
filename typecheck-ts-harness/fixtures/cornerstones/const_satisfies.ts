// Cornerstone: const contexts & satisfies
const mode = "on" as const;
const cfg = { mode: "on" as const } satisfies { mode: "on" | "off" };
const bad = { mode: "maybe" } satisfies { mode: "on" | "off" };
