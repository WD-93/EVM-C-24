# EVMC

## Design

EVMC is a smart contract language inspired by C and Haskell. It targets the Ethereum Virtual Machine (EVM), the VM used by Ethereum, the first and dominant blockchain to support Turing-complete smart contracts. The EVM is a bytecode-interpreting stack machine with 256-bit words (!) and a variety of different memory spaces (calldata, volatile memory, persistent storage, etc.), each accessed through a different set of instructions.

Despite its idiosyncratic design, the EVM's popularity with developers and associated tooling has also led it to be ported to many other chains and L2s (performant off-chain ledgers secured by a main chain).

Blockchain smart contracts are very interesting from a programming language design perspective: they require both excellent performance (because transaction execution is massively replicated) and correctness (because vulnerabilities translate directly to massive and irreversible economic loss).

EVMC is intended to occupy a niche between Solidity (a relatively high-level language and the most popular language for Ethereum smart contract development) and low-level bytecode generation languages such as Huff or my own Ecomp DSL.

The intention is to permit the user to access the EVM's low-level features (avoiding Solidity's costly abstractions) through a structured, typed interface (enabling automatic optimization and avoiding the tedious, error-prone task of programming at an abstraction level close to bytecode).

EVMC borrows most of its syntax from C; like C, it gives the user access to structs, arrays, and pointers. The latter type is also parameterized by a _region_ parameter, denoting which memory space the pointer references.

Unlike C, EVMC has merged enums and structs into a single Haskell-like datatype construct; both boxed and unboxed datatypes can be defined and pattern-matching can be used.

The most important feature EVMC has borrowed from Haskell is its **Hindley-Milner type system**, allowing functions such as:

```text
alloc : () -> Ptr r a
map   : (a -> b, List r a) -> List r b
```

to be defined. In contrast to Haskell, EVMC uses C++-like template polymorphism rather than dictionary passing; it cannot afford the luxury of closures or a heap!

---

## Status

I implemented a prototype with a simple type system and IR. While it worked, I missed Haskell's brevity and expressive power, and feared adding additional optimizations to the ad hoc IR would be difficult.

Consequently, I've transitioned to using a Hindley-Milner type system and a Haskell Core-inspired IR. The transition necessitated rewriting most of the pipeline from scratch; I've currently completed:

- Parsing  
- Desugaring  
- Hindley-Milner type inference  
- Monomorphization

The next step is conversion of the monomorphized module to **EVMC Core**.

Like GHC Core, EVMC Core is intended to be a simple, theoretically tractable lambda calculus amenable to optimization. Core is intended to eliminate:

- The nonlinear control flow of C (`break`, `continue`, `return`)  
- The EVM's side effects (`REVERT`, `RETURN`, pointer writes, etc.)

Instead, the program is modeled as a pure lambda calculus expression that can be reasoned about symbolically.

Certain optimizations such as constant expansion, inlining, and tail calls should be relatively straightforward. However, I expect symbolic reasoning about memory access (e.g. to use scratch memory instead of bumping the allocation pointer, or detecting pointer aliasing/the absence thereof) to be more challenging.

I am currently in the process of designing Core and its semantics to meet those challenges.

---

## Vision

The immediate intended use case of EVMC is implementing a high-level interpreter running on the EVM in order to enable _virtual smart contracts_ to be developed in a functional language. Contracts written in that language would then run together within a single Ethereum smart contract call, able to safely interact with each other and share resources.

### Key advantages:

- **Volatile memory** could be used for internal interactions (e.g. decrementing a token balance and updating the recipient¡¦s), rather than **persistent storage** (which is much more expensive).  
- **Batching:** Many user transactions could be executed together.  
- **Compact state:** Persistent state (contract data, balances, etc.) could be stored as a single Merkle root on-chain, enabling major gas savings.  
- **Alternative authentication:** I am interested in supporting a hash preimage revelation-based protocol, which could provide **80¡V90% compute cost savings** over traditional signature verification.

---

### Roadmap for the Language

Once the compiler pipeline is complete, the highest-priority improvements are:

1. **Library support for the Solidity ABI**  
2. **Typed interface between smart contracts** (CALL/RETURN), similar to Solidity  
   _(This would likely require GADT support in EVMC.)_

---

I¡¦ve also considered additional features from a programming languages research perspective. They¡¦re a bit esoteric, but I¡¦d be happy to discuss them.
