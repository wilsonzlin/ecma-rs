/**
 * Minifies JavaScript code.
 *
 * @param topLevelType - Parse mode for the top level ("global" or "module")
 * @param src - Source JS code as a string or UTF-8 Buffer
 * @returns Minified JS code as a UTF-8 Buffer
 */
export function minify(topLevelType: "global" | "module", src: string | Buffer): Buffer;
