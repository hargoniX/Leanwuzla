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
crucial twist that the solver is implemented and verified as part of the Lean 4 theorem prover
and programming language @lean4. Furthermore, in order to ensure end-to-end correctness of the result,
`bv_decide` also checks the LRAT @lrat certificate produced by the SAT backend. Overall `bv_decide`
contains three key verified components:

(1) The rewriting engine, which is heavily inspired by Bitwuzla's rewrite rules.
We also formally verify all rewrites used by `bv_decide` for arbitrary bit-widths within Lean.

(2) The bit-blasting engine, which is based on a formally verified AIG framework that uses
Lean's built-in support for imperative data structures such as arrays and hash maps to achieve
imperative performance characteristics.

(3) The verified LRAT checker, which is used to import proofs of UNSAT from the SAT solving
backend (the `cadical` solver) into the Lean logic. As an additional optimization step the LRAT checker trims the LRAT file
to drop unused proof steps with the same strategy as `lrat-trim` @lrat-trim.

The `bv_decide` tactic is originally developed as an integrated tactic for Lean,
and thus does not natively speak the SMT-LIB format.
To remedy this, we developed a wrapper called `leanwuzla` @leanwuzla that is able
to translate problems from the `QF_BV` SMT-LIB logic into a Lean problem that `bv_decide`
can decide. Note that this wrapper is not formally verified.

Thus, despite being an end-to-end formally verified solver,
there are three sources of error that could, in
theory, still cause `bv_decide` to output a wrong result from an input SMT-LIB expression:

Firstly, `leanwuzla` could mis-parse an SMT-LIB file.
This would cause `bv_decide` to solve a different problem than the one intended by the SMT-LIB input.
We thus tested the `leanwuzla` component on all of SMT-LIB 2024 in order
to gain confidence that the parser is indeed correct.

Secondly, the Lean compiler could have compiled the `bv_decide` source code to a binary that does not
semantically correspond to the source. Once again, since `leanwuzla` has been tested on SMT-LIB 2024,
we have reasonable confidence that there are no Lean compiler bugs that affect `bv_decide`.

Lastly, the Lean kernel have a soundness bug.
This would allow us to falsely establish the correctness of the bitblasting of `bv_decide`.
This is highly unlikely, as the Lean kernel is implemented with the De Bruijn criterion in mind @barendregt2005challenge,
ensuring that the Lean kernel has a small trusted code base, which has undergone careful review and heavy testing.
It is particularly unlike to have bugs that allow it to accept incorrect, but nevertheless non-adverserial proofs.
Most soundness issues in the past have been exploted by proofs that are specifically crafted one to exploit a particular vulnerability in the
implementation.
Since we perform fairly standard reasoning, we do not believe this to be a serious issue/

= Configurations
`bv_decide` participates in the single query track of the `QF_BV` logic. It uses CaDiCaL version
2.1.2 @cadical as the SAT backend.

= License
`bv_decide` as well as `leanwuzla` are licensed under the Apache 2.0 license.
