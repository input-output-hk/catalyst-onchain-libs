The catalyst-onchain-libs repository from Input Output HK is a genuinely solid foundation for on-chain development in the Cardano ecosystem. It brings together a secure, optimized standard library tailored for Plutarch—with potential support for Aiken—so developers don’t have to reinvent common functionality when building robust smart contracts and on-chain logic. The library’s emphasis on optimized operations, secure implementations, and a comprehensive test suite makes it a practical and dependable choice for teams serious about quality on-chain code
- Riley Kilgore (Midgard developer)

Been using catalyst-onchain-libs for some Plutarch work and it's genuinely solid. The team clearly understands the pain points of on-chain development — they've ported the merkle patricia forestry from Aiken which saves you from reinventing the wheel, and the optimizations actually matter when you're counting every byte on-chain.
The nix setup is clean. No weird hacks, just nix develop and you're good. Coming from Rust where tooling is a first-class citizen, I appreciate when Haskell projects get this right.
What I really respect is they're not trying to do too much. It's a focused stdlib with proper benchmarks and tests. No bloat, no magic — just well-documented primitives you can actually trust for production use. The design doc shows they thought through the architecture before shipping.
If you're building on Cardano with Plutarch, this should be in your cabal.project.
- Lucas (Aiken developer)


Working on Cardano smart contracts, I've found catalyst-onchain-libs to be an invaluable addition to our development toolkit. The library provides well-optimized, security-focused
implementations of common on-chain operations that would otherwise require significant effort to build from scratch.

The Plutarch utilities are particularly helpful - they abstract away many of the low-level concerns while maintaining the performance characteristics essential for on-chain code
where every byte and CPU unit matters. The Merkle Patricia Forestry implementation alone saved us considerable development time.

What sets this library apart:

- Production-ready primitives - The functions are optimized for on-chain execution, not just correctness
- Security-first approach - Clear documentation on security considerations for each utility
- Comprehensive testing - Confidence that the building blocks we depend on are well-tested
- Active maintenance - Contributions from experienced Plutarch developers in the Cardano ecosystem

If you're building Plutarch-based smart contracts on Cardano, catalyst-onchain-libs provides the foundational utilities that let you focus on your application logic rather than
reinventing standard operations.
- SeungheonOh