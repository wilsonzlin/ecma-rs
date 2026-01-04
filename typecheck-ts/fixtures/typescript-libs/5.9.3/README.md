# TypeScript standard library declarations (5.9.3)

This directory vendors the upstream TypeScript `lib*.d.ts` files from the
official `typescript@5.9.3` npm package (the contents of `typescript/lib/`).

These files are used by `typecheck-ts` when built with the `bundled-libs`
feature so tests and offline runs can typecheck against the real TypeScript
standard library without relying on a local Node installation.

License information:

- `LICENSE.txt` (TypeScript, Apache 2.0)
- `ThirdPartyNoticeText.txt`

