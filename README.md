# Catalyst On-Chain Libraries

A secure and optimized on-chain standard library for Plutarch, with potential bindings to Aiken. This library provides essential utilities and tools for building robust on-chain applications in the Cardano ecosystem.

## Features

- Optimized on-chain operations
- Secure standard library implementations
- Compatibility with Plutarch
- Potential Aiken bindings
- Comprehensive test suite
- Performance benchmarks

## Installation

### For Users

To use this library in your project, add the following to your `cabal.project`:

```cabal
source-repository-package
    type: git
    location: https://github.com/input-output-hk/catalyst-onchain-libs
    tag: 6785ba1e924f9d9ce15d335b1b956842e608fa61
    --sha256: sha256-vaUFPrR8RFhEGgXbO1npwo5uSK1jRtKtg+FEVbEGuV0=
    subdir:
      src/plutarch-onchain-lib
```

> **Note**: Replace the `tag` value with the latest commit hash and adjust the `sha256` accordingly. You can get the correct `sha256` by:
> 1. Running `nix develop` with the old `sha256`
> 2. Copying the correct `sha256` from the error output
> 3. Updating the `sha256` value in your `cabal.project`
> 4. Running `nix develop` again

### For Contributors & Maintainers

1. Clone the repository:
```bash
git clone git@github.com:input-output-hk/catalyst-onchain-libs.git
cd catalyst-onchain-libs
```

2. Build the project:
```bash
cabal update
cabal build -j all
```

3. Run tests and benchmarks:
```bash
cabal run plutarch-onchain-lib-tests
cabal run plutarch-onchain-lib-bench
```

## Nix Configuration

If you encounter build issues with nix, add the following to your nix config (typically at `/etc/nix/nix.conf`):

```nix
extra-experimental-features = nix-command flakes ca-derivations fetch-closure
extra-substituters = https://cache.iog.io https://cache.nixos.org/
allow-import-from-derivation = true
extra-trusted-public-keys = hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ=
```

## Contributing

We welcome contributions! Here's how you can help:

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Run tests and ensure they pass
5. Submit a pull request

### Development Guidelines

- Follow the existing code style
- Add tests for new features
- Update documentation as needed
- Ensure all tests pass before submitting

## Support

For support, please:
- Open an issue for bug reports
- Create a discussion for questions
- Contact the maintainers for critical issues

## Acknowledgments

This project builds upon and integrates several key components from the Cardano ecosystem:

- The [merkle patricia forestry](https://github.com/aiken-lang/merkle-patricia-forestry) implementation was ported from aiken-lang.
- Special thanks to [SeungheonOh](https://github.com/SeungheonOh) one of the core developers of Plutarch.

We are grateful to all contributors and the broader Cardano community for their support and feedback.