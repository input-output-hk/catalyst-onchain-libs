# Security and Assurance Analysis

This repo is a Plutarch-focused on-chain library, so "security" here mostly means: making it hard to write the wrong validator, keeping on-chain behavior predictable, and avoiding easy foot-guns around `PData`, ledger types, and resource usage (ex-units / script size).

## What this library does (and does not) try to protect you from

Things it helps with:

- Keeping common checks in one place (so application validators don't re-invent them slightly differently).
- Making ledger assumptions explicit (for example, where we rely on ledger ordering guarantees).
- Offering faster versions of common patterns (to reduce accidental ex-unit blowups from naive recursion).

Things it cannot do for you:

- Prove your validator's business logic is correct.
- Replace threat modeling for your specific dApp.
- Turn unsafe operations into safe ones; it mostly tries to *contain* them and make them easy to spot.

## Module coverage

### `Plutarch.Core.Internal.Builtins`
**What it is**: A concentrated place for raw builtin access (`punsafeBuiltin`).
**Why it matters**: This is one of the main "sharp edge" areas in any Plutarch codebase. The good news is that the sharp edge is not spread everywhere: wrappers like `pindexBS'`, `pwriteBits'`, `pcountSetBits'`, and `pintegerToByteString'` live here, so reviewers know exactly where to look when checking assumptions and invariants.

### `Plutarch.Core.Eval`
**What it is**: Off-chain utilities for compiling/evaluating terms, serialising scripts, and writing artifacts.
**Why it matters**: Consistent compilation configuration is a boring-but-important part of safety. Centralising helpers like `writePlutusScriptNoTrace` / `writePlutusScriptTrace` reduces the chance that two scripts get built with subtly different tracing modes or serialisation steps.

### `Plutarch.Core.Scripts`
**What it is**: Convenience helpers around compilation and script sizing.
**Why it matters**: `tryCompileNoTracing` makes the intended production mode explicit, and `scriptSize` / `serialisedScriptSize` make it easy to keep an eye on ledger limits early (script size failures are an avoidable deployment-time risk).

Note: `tryCompile` throws on compile failure (via `error`). That's fine for a dev tool, but you generally do not want that pattern inside an on-chain path. Keeping it here makes the boundary clear.

### `Plutarch.Core.Trace`
**What it is**: A small tracing layer with a `DEBUG` switch.
**Why it matters**: In production builds (when `DEBUG` is not enabled), `pfail` intentionally reduces to `perror` (no trace message). That is a practical safety feature: you avoid accidentally shipping extra tracing cost and you reduce any chance of leaking structured messages on-chain.

### `Plutarch.Core.Context`
**What it is**: Accessors and small helpers for common `ScriptContext` / `TxInfo` plumbing.
**Why it matters**: A lot of validator bugs are just "read the wrong field" or "handled the datum case wrong". Helpers like `ptxOutDatum`, `ptxOutInlineDatumRaw`, and `ptryInlineDatum` mean you can express intent directly and keep the pattern consistent across validators.

### `Plutarch.Core.Integrity`
**What it is**: Checks around data-encoded ledger types (credentials, purposes, etc.).
**Why it matters**: This module is very explicit about what is safe only under certain conditions. For example, constructor-tag checks like `pisScriptCredential` / `pisPubKeyCredential` are safe when the value really comes from the ledger (because the ledger guarantees the shape), but not necessarily safe as a general-purpose parser for arbitrary `PData`. Having those warnings close to the code is exactly the kind of thing that prevents subtle misuse later.

### `Plutarch.Core.ValidationLogic`
**What it is**: A grab bag of validator building blocks: counting redeemers, filtering inputs, validating a list of conditions, and so on.
**Why it matters**: This is where you want correctness and consistency. For example, `penforceNSpendRedeemers` documents (in code) that it assumes redeemers are sorted by the ledger's `Ord` instance and points at the ledger source. That kind of explicit assumption is good security hygiene: it makes the fast path justifiable and reviewable.

### `Plutarch.Core.Validators`
**What it is**: A few ready-to-use validator patterns (permission checks, one-shot NFT minting, and an always-fail script for testing).
**Why it matters**: These functions encode common patterns in a way that's easy to audit. For instance, `mkNFTMinting` makes the "only one token name, mint exactly 1" rule explicit and uses shared helpers (`pvalidateConditions`, `ptryLookupValue`, `pheadSingleton`) rather than re-implementing them ad hoc.

### `Plutarch.Core.Crypto`
**What it is**: Small crypto helpers (hashing, pubkey-to-hash conversion, script hashing).
**Why it matters**: Centralising crypto operations reduces the chance that different parts of your codebase hash the same thing in slightly different ways. `scriptHashV3` is also explicit about the V3 prefix used during hashing, which avoids "almost the same hash" mistakes.

### `Plutarch.Core.PByteString`
**What it is**: Tiny `ByteString` helpers (prefix checks, take/drop).
**Why it matters**: These are the kinds of utilities that are easy to get subtly wrong (length math, slicing). Keeping them small and reusable helps avoid bugs in token-name conventions and low-level parsing.

### `Plutarch.Core.List`
**What it is**: A set of higher-performance list operations and patterns.
**Why it matters**: On-chain code is vulnerable to resource blowups if you do too much work on long lists. Having fast versions (`pdropFast`, `pbuiltinListLengthFast`, `pelemAtFast`, etc.) helps you keep validator cost predictable, and helpers like `pcheckIndex` make bounds checks explicit.

### `Plutarch.Core.Value`
**What it is**: Helpers for working with `Value` safely and efficiently.
**Why it matters**: Asset accounting bugs are a common source of exploits. This module is deliberately explicit (currency symbols, token names, and counts are handled as separate concepts), and provides "try/only/has" style helpers (`ptryLookupValue`, `phasSingleToken`, `ponlyAsset`, `pstripAdaSafe`, etc.) that encourage defensive checks.

### `Plutarch.Core.Utils`
**What it is**: General-purpose building blocks used across validators.
**Why it matters**: This module is largely about making the safe thing the easy thing: reusable assertions (`passert`, `pcheck`), list/condition combinators (`pand'List`), and common ledger checks (like signature checks) reduce boilerplate and reduce the surface for "I forgot one check" bugs.

### `Plutarch.Core.Time`
**What it is**: Helpers for validity ranges and finite time intervals.
**Why it matters**: Time logic is a classic source of subtle errors. This module keeps the representation explicit (`PPosixFiniteRange`, conversions like `ptoFiniteRange`, checks like `pisFinite`) so validators can state their intent clearly.

### `Plutarch.Core.Unroll`
**What it is**: Re-exports/wrappers for unrolling utilities.
**Why it matters**: Bounded unrolling is a pragmatic way to keep runtime predictable. Predictability is a security property on-chain: it reduces the likelihood of unexpected budget failures or performance cliffs.

### `Plutarch.MerkleTree.Helpers`
**What it is**: Small primitives used by the Merkle tree implementation (hash combining, nibble/path helpers).
**Why it matters**: Merkle code tends to fail in boring ways (wrong ordering, wrong nibble extraction, inconsistent hashing). Having the primitives in one place and consistently using `blake2b_256` via `pcombine` helps keep proof logic deterministic.

### `Plutarch.MerkleTree.Merkling`
**What it is**: Merkle root reconstruction helpers (dense and sparse variants, plus fixed null hashes).
**Why it matters**: Explicit branch ordering and explicit null hashes are good for reviewability. It makes it much easier to answer: "given this proof, do we compute the same root every time?"

### `Plutarch.MerkleTree.PatriciaForestry`
**What it is**: A Merkle Patricia Forestry structure, including proof types and operations.
**Why it matters**: The security story here is mostly: deterministic hashing, typed proof structures, and explicit operations (`pinsert`, `pdelete`, `pupdate`, `phas`, etc.). In other words, it aims to make membership/non-membership reasoning something you can implement without inventing your own bespoke proof format.

## Assurance notes

- The library generally prefers small, composable helpers over big frameworks. That makes it easier to audit what a validator is doing.
- Many helpers are written in a "fail closed" style: if an invariant does not hold, the script errors rather than continuing with a default.
- Unsafe tools still exist (they have to, for performance and for some ledger interactions), but they are mostly isolated in modules where you expect them (`Internal.Builtins`, places using `punsafeCoerce`, etc.).

## Suggested usage practices

- In production, compile with `NoTracing` and treat tracing as a dev-only affordance.
- Prefer the shared helpers (`ValidationLogic`, `Value`, `Context`) over copy/pasting logic into every validator.
- When you handle `PData`, be strict about boundaries: convert once, validate assumptions, and keep the rest of the validator in typed land.

---

If you want to make this more "assurance-y", the next useful step would be a short checklist per module (what to test, what invariants to keep) and a list of the few unsafe entry points reviewers should focus on first.
