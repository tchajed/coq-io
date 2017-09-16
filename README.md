# Free monads for modeling IO in Coq

A small example of how to model various kinds of IO using a _free monad_ over primitive operations in Coq, including how to extract and run code written in this style.

In [FSCQ](https://github.com/mit-pdos/fscq), we need to model programs that have access to a disk. We write our code in a shallow embedding of programs with primitives for reading and writing to and from the disk. This shallow embedding is a free monad over the desired, primitive disk operations. We give the monadic programs a semantics as a transition system from one state to another. Programs are values in a monad, and the type argument gives the type of a return value for finished programs. The state is manipulated by the primitives, whose behavior is also specified in the semantics.

The code here has a similar model, but is written in a more general way and attempts to expose only the details needed to understand the concepts and get a simple example running. It works almost the same way as FSCQ disk programs, but is phrased in terms of accessing a single input file with a simple single-byte API.

# Overview

The Coq model has a very generic definition `prog`, which takes an argument `OpT : Type -> Type` giving the type constructor for the primitives (the type argument indicates the return type). Primitives are chained using `Ret` and `Bind`. Then there's an execution semantics, which is expresses the behavior of a program in terms of how it transforms some state type and what return values are allowed (the semantics are relational, so non-determinism is allowed). These semantics specify how `Ret` and `Bind` work and take a parameter `step` for the behavior of the primitives.

As an example, we define `FileOp`, a set of primitives for access to a single input file. These operations have a semantics, in terms of a state which is simply a list of bytes (which we call a `File`). Then there are two example programs of type `prog FileOp T`: one copies a byte, the other is a fixpoint `countNewlines` that counts newlines in the file.

On the Haskell side, any given `prog` extracts to a Haskell data type, a sort of abstract syntax tree of operations, but with Haskell functions extracted from Gallina implementing important functionality. Due to a limitation with Coq extraction, we extract `prog` specialized to `FileOp`.

Then we have some non-Coq components that won't be under verification. These are fairly simple: there's an "interpreter" that runs extracted `prog FileOp`'s, and then a driver program that calls the interpreter on the `countNewlines` program, with some command line parsing and file setup that falls outside of the Coq model.

# Compiling

Run `make` to compile the Coq code and generate the Haskell library. This compiles `Prog.v` with Coq and extracts to `word-count/src/Prog.hs`.

From there, we have a hand-written interpreter (`word-count/src/Interpreter.hs`), and a driver program (`word-count/app/Main.hs`) around the `countNewlines` example in `Prog.v`.

To compile the driver program and produce the `word-count` binary, use Haskell Stack. Stack requires a one-time setup to download the compiler:

```
cd word-count
stack setup
```

Then you can compile and run the binary:

```
stack build
stack exec word-count <file>
```
