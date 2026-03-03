#import "../00-lib/header/lib.typ": *

#show smallcaps: set text(font: "New Computer Modern")

= Introduction

Lookup arguments allow a prover to convince a verifier that a set of values
all appear in some predetermined table, without the verifier inspecting
each entry. This is a useful tool; many desirable operations in a SNARK
circuit, such as range checks and bitwise operations, are expensive to
express as primitive arithmetic constraints but trivial to verify via table
lookup. Early lookup arguments required the prover to commit to the full
table, limiting practical table sizes to roughly $2^20$ entries.

Lasso@lasso is the primary component of Jolt, the SNARK‑based virtual
machine (zkVM) that proves correct execution for RISC-V programs via
large table lookups, drastically reducing complexity and prover costs
compared to earlier zkVMs. Lasso's core contribution was that many tables
of interest are _decomposable_, meaning that a lookup into a table of size
$N$ can be replaced by $c$ lookups into sub-tables of size $N^(frac(style:
"horizontal", 1, c))$.

The lookups into these sub-tables are based on the same machinery that
drives Spark, the sparse polynomial commitment scheme, employed by
Spartan@spartan. With these techniques, Lasso achieves prover costs that
scale with the number of lookups $k$ and the sub-table size, rather than
the full table size $N$. This makes lookups into tables as large as $2^128$
concretely feasible.

This document presents the constructions that Lasso builds on, introducing
them within this single mostly self-contained reference, before arriving
at Lasso itself. We assume knowledge of basic algebra (finite fields,
polynomials) and basic familiarity with proof systems. These priors are
very briefly discussed in @sec:prerequisites.

The structure is as follows:

- @sec:sumcheck-and-mle briefly introduces multilinear extensions and
  the sumcheck protocol, the building blocks underlying all other protocols
  in this document. If these short expositions are insufficient, the reader
  is encouraged to consult Justin Thaler's book@thaler-book.
- @sec:gkr presents the GKR interactive proof for layered arithmetic
  circuits. The exposition mostly follows Thaler's book@thaler-book,
  but uses the linear-combination technique from Libra@libra to reduce
  two claims to one at each layer.
- @sec:productcheck specializes GKR to a binary tree of multiplication
  gates, yielding an interactive proof for the grand product $y meq
  product_(vec(b) in bits^lg(n)) w(vec(b))$ with a linear-time prover. This
  follows from a result in Thaler's 2013 paper@thaler-2013.
- @sec:spartan shows how R1CS satisfiability can be reduced to two rounds
  of sumcheck, both with linear-time provers, following Spartan@spartan,
  assuming there exists an efficient sparse polynomial commitment scheme.
- @sec:spark introduces Spark, the sparse polynomial commitment scheme
  that enables Spartan's linear prover. Spark uses offline memory
  checking@blum1991checking to prove that the prover read the sparse matrix
  entries honestly.
- @sec:lasso finally presents the Lasso lookup argument itself.

If the reader is already comfortable with sumcheck, multilinear extensions
and the GKR protocol, feel free to start from @sec:spartan.
