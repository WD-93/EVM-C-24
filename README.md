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

The EVMC compiler functions and has been used to compile complex programs such
as HLM, a functional interpreter with a Merklized heap.
Programs which demonstrate its capabilities can be found at <https://github.com/WD-93/evmc-demo-display/>.
EVMC is not yet production-ready: neither the standard library nor the finer details of its syntax or semantics should be assumed to be stable.
UX requires improvement; type errors in particular are inscrutable and will result in walls of error text for large programs.
The compiler requires further testing and verification before it can be used safely in production.

---

## Installation
Install cabal, Haskell's package manager.
Clone this branch, then navigate to it and run "cabal install exe:evmc --overwrite-policy=always". That should generate an evmc.exe executable in your cabal/bin/ folder. Add that folder to your system path.

---

## Usage
To compile SomeModuleName.evmc, run "evmc SomeModuleName". If the program compiles successfully, that will create a SomeModuleName.evm file containing EVM bytecode in hex. To deploy a compiled EVMC program to a simulated Ethereum blockchain in Hardhat 3, copy u.js from evmc-demo-display to the root of your Hardhat project. Then run:

npx hardhat console

u = await import("./u.js")

u.newConnection() //Creates a new simulated chain, do this only once per session

addr = await u.deploy("SomeModuleName.evm")

Now the created contract's address is bound to addr and you can interact with it!