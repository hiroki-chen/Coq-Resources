# Coq Resources

This repository contains a bunch of interesting and useful tools, materials, and many other stuffs that help one with doing verification with Coq.

## You are a noob!

Resources for noobs who have never ever played with Coq.

* [Inria - Official Reference Manual](https://coq.inria.fr/doc/V8.18.0/refman/)
* [Inria - Standard Library](https://coq.inria.fr/doc/V8.18.0/stdlib/)
* [Coq-cheatsheet](https://julesjacobs.com/notes/coq-cheatsheet/coq-cheatsheet.pdf)
* [Software Foundations](https://softwarefoundations.cis.upenn.edu/): This book is just fantastic: it teaches you how to write correct code and prove it in Coq. It gives rise to basic PL stuffs like verification techniques and types.
* [VSCoq](https://github.com/coq-community/vscoq): Extension for VS Code.

## Intermediate

Till now, you should be able to verify something non-trivial...

* [Ltac / Ltac2](https://coq.inria.fr/refman/proofs/creating-tactics/index.html)
* [Ltac2 Tutorial](https://github.com/tchajed/ltac2-tutorial)
* [Mathematical Components](https://math-comp.github.io/mcb/): Mathematical Components is the name of a library of formalized mathematics for the Coq proof assistants.
* [Verified C Compiler](https://github.com/AbsInt/CompCert)
* [Coq formalization for Haskell](https://github.com/jwiegley/coq-haskell)
* [Extraction from Coq to OCaml](https://coq.inria.fr/refman/addendum/extraction.html)
* [Coq Tricks](https://github.com/tchajed/coq-tricks): All the things that Coq manual won't teach you.
* [Dependent Types](http://adam.chlipala.net/papers/CpdtJFR/CpdtJFR.pdf): This manual teaches you how to write code in Coq for playing with dependent types like $\Pi_{n: \mathbb{N}} P(n)$
* [Coq's "Standard Library"](https://gitlab.mpi-sws.org/iris/stdpp): This project contains an extended "Standard Library" for Coq called coq-std++.

### Some Real-World Projects Verified by Coq

* [ConCert](https://github.com/AU-COBRA/ConCert): Verified Smart Contract Implementation
* [CIFC](https://github.com/HarvardPL/CIFC): Oakland'21 Enforcing information flow control for Java-like language
* [YNOT](https://github.com/hiroki-chen/Coq-RDB) and [this](https://github.com/ynot-harvard/ynot): Verifying a database
* [Jasmin](https://github.com/jasmin-lang/jasmin): Writing secure cryptographic code

## Esoteric Stuffs

You probably won't like them...

* [Homotopy Type Theory for Coq](https://github.com/HoTT/Coq-HoTT)
* [MetaCoq](https://github.com/MetaCoq/metacoq): You can even play with Coq's core calculus and AST!
* [UniMath](https://github.com/UniMath/UniMath): This coq library aims to formalize a substantial body of mathematics using the univalent point of view.
* [Category Theory](https://github.com/jwiegley/category-theory): Formalized category theory in Coq.
* [MathClasses](https://github.com/coq-community/math-classes)
* [Iris](https://gitlab.mpi-sws.org/iris/iris): A general proof mode for carrying out *separation logic proofs* (proof for languages that allow programmers to play with memory stores; for those interested, please refer to JC Reynolds's paper at CMU) in Coq.
* [More dependent types](./dependent_types.md)

## Some Awesome Coq Pupils

* [Ralf Jung @ ETHz](https://research.ralfj.de/): He is also the core contributor of rust-lang.
* [Tej Chajed](https://www.chajed.io/): Proofs, logics, and verification for systems.
* [Inria](https://www.inria.fr/fr): People at this institute made Coq!
