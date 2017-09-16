# Free monads for modeling IO in Coq

A small example of how to model various kinds of IO using a _free monad_ over primitive operations in Coq, including how to extract and run code written in this style.

In [FSCQ](https://github.com/mit-pdos/fscq), we need to model programs that have access to a disk. We write our code in a shallow embedding of programs with primitives for reading and writing to and from the disk. This shallow embedding is a free monad over the desired, primitive disk operations. We give the monadic programs a semantics as a transition system from one state to another. Programs are values in a monad, and the type argument gives the type of a return value for finished programs. The state is manipulated by the primitives, whose behavior is also specified in the semantics.

The code here has a similar model, but is written in a more general way and attempts to expose only the details needed to understand the concepts and get a simple example running. It works almost the same way as FSCQ disk programs, but is phrased in terms of accessing a single input file with a simple single-byte API.

# Compiling

Run `make` to compile the Coq code and generate the Haskell library.

Compile the Haskell library, interpreter, and a small driver program around the `countNewlines` example in `Prog.v` using Haskell Stack.

Stack requires a one-time setup to download the compiler:

```
cd word-count
stack setup
```

Then you can compile and run the binary:

```
stack build
stack exec word-count <file>
```
