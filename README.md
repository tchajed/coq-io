# Free monads for modeling IO in Coq

A small example of how to model various kinds of IO using a _free monad_ over primitive operations in Coq, including how to extract and run code written in this style.

In [FSCQ](https://github.com/mit-pdos/fscq), we need to model programs that have access to a disk. We write our code in a shallow embedding of programs with primitives for reading and writing to and from the disk. This shallow embedding is a free monad over the desired, primitive disk operations. We give the monadic programs a semantics as a transition system from one state to another. Programs are values in a monad, and the type argument gives the type of a return value for finished programs. The state is manipulated by the primitives, whose behavior is also specified in the semantics.
