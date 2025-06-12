#import "@preview/charged-ieee:0.1.3": ieee

#show: ieee.with(
  title: [`bv_decide` at the SMT-COMP 2025],
  abstract: [
    In this paper, we present our SMT solver `bv_decide` as submitted to SMT-COMP 2025.
    `bv_decide` is a solver for the quantifier-free theory of bit-vectors.
  ],
  authors: (
    (
      name: "Henrik Böving",
      organization: [Lean FRO],
    ),
    (
      name: "Siddharth Bhat",
      organization: [University of Cambridge],
    ),
    (
      name: "Alex Keizer",
      organization: [University of Cambridge],
    ),
    (
      name: "Luisa Cicolini",
      organization: [University of Cambridge],
    ),
    (
      name: "Leon Frenot",
      organization: [ENS Lyon],
    ),
    (
      name: "Abdalrhman Mohamed",
      organization: [Stanford University],
    ),
    (
      name: "Léo Stefanesco",
      organization: [University of Cambridge],
    ),
    (
      name: "Harun Khan",
      organization: [Stanford University],
    ),
    (
      name: "Josh Clune",
      organization: [Carnegie Mellon University],
    ),
    (
      name: "Clark Barrett",
      organization: [Stanford University],
    ),
    (
      name: "Tobias Grosser",
      organization: [University of Cambridge],
    ),
  ),
  bibliography: bibliography("refs.bib"),
)

= Introduction
`bv_decide` is a Satisfiability Module Theories (SMT) solver for the quantifier-free theory of
bit-vectors. It implements an eager SMT approach, consisting of a rewriting and a bit-blasting phase.
Algorithmically the system follows the approach of the Bitwuzla SMT solver @bitwuzla with the
crucial twist that the rewriting and bit-blasting engine is implemented and verified as part of the
Lean 4 theorem prover and programming language @lean4. Furthermore, in order to ensure end-to-end
correctness of the result, `bv_decide` also checks the LRAT @lrat certificate produced by the SAT
backend, using a formally verified LRAT checker written in Lean.

Because `bv_decide` was originally developed as an integrated tactic for Lean itself it does not natively
speak the SMT-LIB format. For this we developed a wrapper called `leanwuzla` @leanwuzla that is able
to translate problems from the `QF_BV` SMT-LIB logic into a Lean problem that `bv_decide` can work
on, this wrapper is not formally verified. There are thus three sources of error that could, in
theory, still cause `bv_decide` to output a wrong result.

First `leanwuzla` could mis-parse an SMT-LIB file and thus let `bv_decide` work on an entirely different
problem than requested. We thus tested the `leanwuzla` component on all of SMT-LIB 2024 in order
to gain confidence that the parser is indeed correct.

Secondly the Lean compiler could have compiled the `bv_decide` source code to a binary that does not
semantically correspond to the source. We use the same approach as for the `leanwuzla` parsing
issues to deal with this source of error.

Lastly the Lean kernel could have wrongfully accepted a proof of the correctness of `bv_decide`. This is
very unlikely as the kernel is implemented in a very minimal fashion and thus quite unlikely to
have bugs. In particular unlikely to have bugs that let it accept a random proof that makes sense
to a human as opposed to a specifically crafted one to exploit a particular vulnerability in the
implementation.

= Configurations
`bv_decide` participates in the single query track of the `QF_BV` logic. It uses CaDiCaL version
2.1.2 @cadical as the SAT backend.

= License
`bv_decide` as well as `leanwuzla` are licensed under the Apache 2.0 license.
