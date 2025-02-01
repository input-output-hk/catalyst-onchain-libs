# Catalyst On-Chain Libraries: Design Document

## Interface

### Overview
The Catalyst On-Chain Libraries are built with a singular focus: **maximizing production efficiency** for on-chain applications within the Cardano ecosystem. Recognizing the highly resource-constrained and competitive nature of blockchain environments, this library prioritizes reducing execution overhead and on-chain costs without sacrificing functionality or readability. 

Unlike traditional software development, where abstractions often trade performance for ease of use, this library adopts a design philosophy that balances high-level abstractions with raw performance. By leveraging meta-programming techniques, it automates the generation of highly optimized Plutarch code, ensuring developers can write clear and maintainable code without incurring significant computational penalties.

### Key Features
- **Production-First Efficiency**: Every function and abstraction is optimized for minimal resource consumption, making the library suitable for real-world, high-throughput applications.
- **Meta-Programming for Optimization**: Tools like `pvalidateConditions`, `punrollBound`, `pand'List`, `pcond`, and `pnTails` enable automated generation of efficient code tailored to specific use cases.
- **Cost-Effective Development**: Developers can focus on solving problems at a high level, confident that the underlying code will be competitive in terms of fees and performance.
- **Type-Safe Interfaces**: Functions are strictly typed, reducing the potential for runtime errors and ensuring correctness.
- **Modular and Composable**: Each namespace encapsulates distinct functionality, promoting reusability and clarity while allowing developers to build complex systems from simple primitives.

### Example Usage
Modules like `Plutarch.Core.List` provide functions such as `pelemAtFast'` to access list elements efficiently, while `Plutarch.Core.Value` offers optimized methods for currency manipulations like `pfilterCSFromValue`. Meta-programming utilities like `pand'List` and `pvalidateConditions` provide abstractions for common code-patterns without compromising on performance.

---

## Namespaces

### 1. `Plutarch.Core.Internal.Builtins` (`Builtins.hs`)
- **Purpose**: Low-level utilities for raw operations on Plutarch types.

### 2. `Plutarch.Core.Crypto` (`Crypto.hs`)
- **Purpose**: Cryptographic utilities for handling public keys and hashes.

### 3. `Plutarch.Core.Data` (`Data.hs`)
- **Purpose**: Abstracts data extraction and handling for `PDataNewtype`.

### 4. `Plutarch.Core.Eval` (`Eval.hs`)
- **Purpose**: Evaluating and serializing Plutarch terms.

### 5. `Plutarch.Core.Integrity` (`Integrity.hs`)
- **Purpose**: Utilities for verifying the correctness of the BuiltinData encoding of various types.

### 6. `Plutarch.Core.List` (`List.hs`)
- **Purpose**: Specialized high efficiency list operations.

### 7. `Plutarch.Core.PByteString` (`PByteString.hs`)
- **Purpose**: ByteString manipulation utilities.

### 8. `Plutarch.Core.Time` (`Time.hs`)
- **Purpose**: Functions for working with time ranges and intervals.

### 9. `Plutarch.Core.Unroll` (`Unroll.hs`)
- **Purpose**: Recursive function unrolling strategies (very strong optimization tool).

### 10. `Plutarch.Core.Value` (`Value.hs`)
- **Purpose**: `PValue` operations, including currency manipulations.

### 11. `Plutarch.Core.Utils` (`Utils.hs`)
- **Purpose**: General purpose smart contract utilities. 
---

## Conclusion
This design document outlines the structure, interface, and high-level decisions underpinning the Catalyst On-Chain Libraries. By placing **production efficiency** at the core of its design, this library ensures developers can create cost-effective, high-performance dApps without sacrificing readability or maintainability. Leveraging meta-programming techniques and rigorous optimization, the library sets a standard for balancing abstraction with performance in on-chain development.
