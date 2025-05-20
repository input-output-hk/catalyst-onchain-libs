# Plutarch Onchain Library Integration Report

## Overview
The plutarch-onchain-lib has been extensively integrated into the Djed codebase, providing a robust foundation for smart contract development. The library's integration has significantly improved the development experience and efficiency of the Djed smart contracts thus reducing end-user transaction fees and increasing the dApp's throughput.

## Key Integration Points

### Inline UPLC Optimization
```haskell
    let
        scPair = ppairDataBuiltinRaw # pforgetData (pdata pstablecoinTokenName) # pforgetData (pdata nbSC)
        rcPair = ppairDataBuiltinRaw # pforgetData (pdata preservecoinTokenName) # pforgetData (pdata nbRC)

        onlySCVal = pmapData #$ pcons # scPair # pnil
        onlyRCVal = pmapData #$ pcons # rcPair # pnil

        scAndRcVal = if reservecoinTokenName < stablecoinTokenName
        then pmapData #$ pcons # rcPair #$ pcons # scPair # pnil
        else pmapData #$ pcons # scPair #$ pcons # rcPair # pnil
```
The above demonstrates the use of the raw builtins exposed by the library to achieve performance comparable to maximally optimized hand-written UPLC. We use these primitives extensively throughout the Djed codebase.

### Metaprogramming Abstraction
```haskell
  pmkBuiltinList
    [ pforgetData $ pdata rate
    , pforgetData $ pdata timestamp
    , pforgetData $ pdata mintingSymbol
    ]
```
We use the metaprogramming utilities provided by the library, such as `pmkBuiltinList`, `pand'List`, `pvalidateConditions`, `penforceNSpendRedeemers`, and so forth extensively throughout the djed code-base to achieve abstraction without sacrificing efficiency.

We also extensively use the tracing utilities provided by the library which are guaranteed to be completed erased at compile time as the library uses CPP macros to ensure this. 

## Conclusion
The integration of the plutarch-onchain-lib has significantly improved the development experience and efficiency of this Cardano dapp. The library provides a robust foundation for smart contract development, with strong type safety, optimized operations, and reusable components. The consistent use of library patterns has made the codebase more maintainable and easier to understand.

The library's features have been particularly valuable for:
1. Metaprogramming utilities for transaction validation
2. Efficient list and value operations
3. Efficient smart contract validation logic (managing continuing outputs, enforcing constraints on the inputs or value spent from a given contract, yielding logic to other validators, etc)
