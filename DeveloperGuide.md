# Developer Guide: Usage Examples and Trade-offs

This document is a practical guide to the modules in `src/plutarch-onchain-lib/lib`.
It is written for different levels of Plutarch experience and focuses on (1) how to use the library
and (2) when to choose one pattern over another.

## Quick start

Build, test, and benchmark:

```bash
cabal build -j all
cabal run plutarch-onchain-lib-tests
cabal run plutarch-onchain-lib-bench
```

Write a JSON Plutus script (no tracing):

```haskell
import Plutarch.Core.Eval (writePlutusScriptNoTrace)
import Plutarch.Core.Validators (mkPermissionedValidator)

main :: IO ()
main =
  writePlutusScriptNoTrace
    "permissioned"
    "permissioned.plutus"
    mkPermissionedValidator
```

If you want to keep an eye on size early:

```haskell
import Plutarch.Core.Scripts (tryCompileNoTracing, scriptSize)

-- scriptSize (tryCompileNoTracing yourTerm)
```

## The library at a glance

- `Plutarch.Core.Validators`: ready-to-use validators / minting policies (`mkNFTMinting`, `mkPermissionedValidator`).
- `Plutarch.Core.ValidationLogic`: common validation building blocks (`pvalidateConditions`, redeemer/input counters).
- `Plutarch.Core.Value`: safe and efficient `Value` inspection/manipulation.
- `Plutarch.Core.Context`: small, consistent accessors for `ScriptContext`, `TxInfo`, `TxOut`.
- `Plutarch.Core.List`: faster list utilities (often a big ex-unit win).
- `Plutarch.Core.Trace`: debug helpers that erase to no-ops in production builds.
- `Plutarch.Core.Integrity`: helpers for dealing with data-encoded ledger types (and checking shapes).
- `Plutarch.Core.Unroll`: re-exports for bounded/unbounded unrolling (performance tool).
- `Plutarch.MerkleTree.*`: Merkle Patricia Forestry + proof operations for on-chain set/map membership.
- `Plutarch.Core.Crypto`: small crypto helpers (hashes, pubkey conversion, parameter-hash pattern).
- `Plutarch.Core.Eval` / `Plutarch.Core.Scripts`: off-chain helpers for compilation, writing artifacts, and sizing.

## Beginner track: "I want safe, readable validators"

### 1) Validate a list of conditions (fail closed)

Prefer `pvalidateConditions` when you have a handful of independent checks:

```haskell
import Plutarch.Core.ValidationLogic (pvalidateConditions)
import Plutarch.Prelude

-- pvalidateConditions :: [Term s PBool] -> Term s PUnit
-- If any condition is False, the script errors.
```

Why this is nice:

- The validation is "fail closed" by default.
- It keeps validators readable as the number of checks grows.

When you might not want it:

- If you need a custom error path per condition (see trade-offs below).

### 2) A permissioned validator (signature gate)

`mkPermissionedValidator` is a simple template that requires a given `PPubKeyHash` in signatories:

```haskell
import Plutarch.Core.Validators (mkPermissionedValidator)

-- mkPermissionedValidator :: ClosedTerm (PData :--> PAsData PPubKeyHash :--> PScriptContext :--> PUnit)
```

This is a good starting point for "admin must sign" or "multisig-like" patterns.

### 3) A one-shot NFT minting policy

`mkNFTMinting` builds a minting policy that:

- checks only a specific token name is minted,
- mints exactly 1,
- requires a specific `TxOutRef` to be consumed.

```haskell
import Plutarch.Core.Validators (mkNFTMinting)
import PlutusLedgerApi.V3 (TokenName)

-- mkNFTMinting :: TokenName -> ClosedTerm (PTxOutRef :--> PScriptContext :--> PUnit)
```

### 4) Working with datums (safe patterns)

Use `Plutarch.Core.Context` helpers rather than re-parsing `TxOut` fields in each validator:

- `ptxOutDatum :: Term s PTxOut -> Term s POutputDatum`
- `ptxOutInlineDatumRaw :: Term s PTxOut -> Term s PData` (errors if not inline)
- `ptryInlineDatum :: Term s POutputDatum -> Term s PData` (errors if not inline)

These keep the datum-handling cases explicit and consistent.

## Intermediate track: "I know Plutarch; show me the library's idioms"

### 1) Value checks and accounting

Most bugs in production validators are value/accounting mistakes. Prefer the helpers in
`Plutarch.Core.Value` instead of hand-rolling `PValue` traversals:

- `ponlyAsset` / `ponlyAssetC`: enforce "this value contains exactly one asset" and extract `(cs, tn, amount)`.
- `phasSingleToken`: enforce a single token under a specific currency symbol, with the on-chain shape explicit.
- `ptryLookupValue`: get the token list for a currency symbol (errors if missing).
- `pvalueContains`: check that a value contains at least the quantities in another value.
- `pstripAdaSafe` vs `pstripAda`: see trade-offs below (ledger invariant vs defensive code).

Example: treat "Ada-first" as a ledger-provided invariant when you are reading from `ScriptContext`:

```haskell
import Plutarch.Core.Value (plovelaceValueOfFast)

-- plovelaceValueOfFast assumes the ledger keeps Ada as the first entry in a sorted Value.
```

### 2) Common validation building blocks

`Plutarch.Core.ValidationLogic` includes reusable logic that tends to be fiddly to get right:

- `pcountScriptInputs`: count script inputs in a list of inputs.
- `pcountSpendRedeemers` / `penforceNSpendRedeemers`: rely on ledger sorting guarantees for redeemers.
- `pvalueFromCred` / `pvalueToCred`: compute value movement in/out of a credential.
- `pinputsFromCredential`: filter inputs by credential.

These are good candidates to standardize across a codebase, so reviewers learn one pattern.

### 3) Constructing "expected outputs"

If you validate continuing outputs, `pconstructExpectedOutput` can help you build the exact `PTxOut`
shape you want to compare against:

```haskell
import Plutarch.Core.Context (pconstructExpectedOutput)

-- pconstructExpectedOutput
--   :: Term s PAddress
--   -> Term s (PAsData (PValue 'Sorted 'Positive))
--   -> Term s PData
--   -> Term s (PAsData PTxOut)
```

## Advanced track: "I care about performance and minimal overhead"

### 1) Fast list patterns (and why they matter)

The bench suite in this repo exists because list-heavy code is where validators often burn ex-units.
The `Plutarch.Core.List` module provides faster versions of common patterns.

As a concrete example (Iteration 3 in `IterativeBenchmarks.md`):

- `Drops`: `pdropFast` vs `pdropR` is ~5.77x lower CPU.
- `Lengths`: `pbuiltinListLengthFast` vs `plength` is ~5.23x lower CPU.
- `Is Unique`: `pisUniqueSet` ("bit trick") vs `_pIsUnique` ("pow2") is ~46.97x lower CPU.

This is the typical trade-off shape in on-chain code:

- faster execution,
- sometimes slightly larger scripts,
- fewer accidental budget cliffs when the input list grows.

### 2) Unrolling recursion (predictable cost vs script size)

Unrolling can make cost more predictable, but it can increase script size.
This repo benchmarks that trade-off directly:

- `bounded-unroll length` CPU=81,491,500; SIZE=3,824
- `no-unroll recursive length` CPU=162,906,094; SIZE=417

When to use unrolling:

- When the input size is known/bounded and the extra size is acceptable.
- When you want to avoid recursion patterns that become too expensive in worst cases.

When not to:

- When script size is the bottleneck (for example, you are near the transaction size limit).

### 3) Debugging without shipping traces

`Plutarch.Core.Trace` gives you helpers that are useful in development and can be erased in production:

- `pfail`: in non-DEBUG builds becomes `perror` (no message).
- `pdebug` / `pdebugWithPrefix`: in non-DEBUG builds become no-ops.

This supports a workflow where you keep readable checks and messages during development, but you can
produce smaller, cheaper scripts for deployment.

### 4) Raw builtins: when you need exact, low-level control

`Plutarch.Core.Internal.Builtins` exists to contain the sharp edges (`punsafeBuiltin`) in one module.
Used carefully, it enables very low overhead constructions (see `UseCase.md` for a real-world example).

Rule of thumb:

- Use the higher-level helpers first (`Value`, `List`, `ValidationLogic`).
- Reach for raw builtins only when you have measured a bottleneck and you can justify the extra review burden.

### 5) Merkle Patricia Forestry: on-chain membership with proofs

If you want to validate membership/non-membership of key/value pairs on-chain without carrying a full
map in the transaction, the Merkle modules provide a proof-driven interface.

The core membership check is:

```haskell
import Plutarch.MerkleTree.PatriciaForestry (phas)

-- phas :: Term s (PMerklePatriciaForestry :--> PByteString :--> PByteString :--> PProof :--> PBool)
```

And you can update roots with:

- `pinsert :: Term s (PMerklePatriciaForestry :--> PByteString :--> PByteString :--> PProof :--> PMerklePatriciaForestry)`
- `pdelete :: Term s (PMerklePatriciaForestry :--> PByteString :--> PByteString :--> PProof :--> PMerklePatriciaForestry)`
- `pupdate :: Term s (PMerklePatriciaForestry :--> PByteString :--> PProof :--> PByteString :--> PByteString :--> PMerklePatriciaForestry)`

Trade-off:

- Pro: you can keep on-chain verification compact while the off-chain side supplies proofs.
- Con: you must maintain proof generation off-chain and treat proof formats as part of your contract API.

## Trade-offs and when to use what

This section is meant to be actionable: it tells you which function to reach for based on context.

### "Ledger-provided invariant" vs "defensive parsing"

Some helpers rely on invariants the Cardano ledger maintains for values found in `ScriptContext`.
Using these can save cost, but you should only use them when the input really comes from the ledger.

Examples:

- `pstripAda` assumes Ada is the first entry in a sorted `Value` (safe for `ScriptContext` values).
- `pstripAdaSafe` checks the first entry and falls back (safer if the value might be constructed).
- `plovelaceValueOfFast` assumes Ada-first ordering (safe for `ScriptContext` values).

Similarly, in `Plutarch.Core.Integrity`:

- constructor-tag checks (like `pisScriptCredential`) are safe when the term is known to be a credential,
  and the module calls this out explicitly.
- integrity checks (like `pcredentialIntegrityCheck`) are a better choice when you need to defensively
  validate shape before using `punsafeCoerce`-style extraction.

### Readability vs pinpoint error reporting

- `pvalidateConditions [a, b, c]` is compact and consistent, but it fails with a single `perror`.
- If you want per-condition messages during development, pair it with `pdebug` / `pfail` patterns.

### CPU/MEM vs script size

Common trade-off patterns in this repo:

- Fast list utilities tend to reduce CPU/MEM significantly; size may increase slightly.
- Unrolling tends to reduce CPU/MEM for bounded sizes; size can increase a lot.

If you are budget-limited: reach for `Plutarch.Core.List` and consider unrolling.
If you are size-limited: prefer simpler recursion and avoid large unrolled terms.

### Convenience vs review surface (raw builtins)

Higher-level helpers (`Value`, `ValidationLogic`, `Context`) are easier to review and safer to reuse.
Raw builtin wrappers (`Internal.Builtins`) are powerful, but increase the review burden and make
assumptions more subtle. Use them when you have measurements and a clear need.

## Where to look next

- For performance numbers: `IterativeBenchmarks.md` and `src/plutarch-onchain-lib/test/Bench.hs`.
- For a real integration narrative: `UseCase.md`.
- For module intent and scope: `DesignDocument.md`.

