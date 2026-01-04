import { ApiError } from "../types";
import { Result, err, ok } from "../utils/result";

export interface RequestOptions {
  headers?: Record<string, string>;
}

export interface HttpClient {
  "get": <T>(
    path: string,
    decode: (json: unknown) => T,
    opts?: RequestOptions,
  ) => Promise<Result<T, ApiError>>;
}

export function createClient(
  baseUrl: string,
  fetcher: (input: string, opts?: RequestOptions) => Promise<string>,
): HttpClient {
  async function get<T>(
    path: string,
    decode: (json: unknown) => T,
    opts?: RequestOptions,
  ): Promise<Result<T, ApiError>> {
    try {
      const text = await fetcher(baseUrl + path, opts);
      const json = JSON.parse(text) as unknown;
      return ok(decode(json));
    } catch (e) {
      return err({ kind: "network", message: String(e) });
    }
  }

  return { get };
}
