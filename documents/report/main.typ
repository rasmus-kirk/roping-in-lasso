#import "./00-lib/lib.typ": *
#import "@preview/theorion:0.4.1": *

  // title: [Roping in Lasso],
    // An accessible guide to Lasso, which enables lookup arguments from much
    // larger tables than previously possible. Lasso is the primary component
    // of Jolt, the SNARK‑based virtual machine (zkVM) that proves correct
    // execution for RISC-V programs via large table lookups, drastically reducing
    // complexity and prover costs compared to earlier zkVMs. The document
    // assumes minimal familiarity with the constructions that Lasso builds
    // on, by introcing them within a single reference.

#show: show-theorion
#show: ilm.with(
  title: [Succinct Proof Systems - GKR],
  author: "Rasmus Kirk Jakobsen",
  date: datetime.today(),
  abstract: text(size: 10pt, [
    This report presents the GKR protocol, detailing its structure, soundness,
    and asymptotic costs. We then examine a specialized version for proving a
    grand product, which leverages algebraic structure to achieve a linear-time
    prover. The exposition highlights both the general GKR framework and its
    application to structured computations.
  ]),
  date-format: "[year repr:full]-[month padding:zero]-[day padding:zero]",
  bibliography: bibliography("refs.bib", style: "./refs-style-2.csl"),
  figure-index: (enabled: false),
  table-index: (enabled: true),
  listing-index: (enabled: true),
)

// - Memory checking
//   - [ ] Read and understand proofs/paper
//   - [ ] Fluff
//   - [ ] Proofs

#include "./01-introduction/00-introduction.typ"
#include "./02-prerequisites/00-prerequisites.typ"
#include "./03-gkr/00-gkr.typ"
#include "./04-specialized-gkr/00-specialized-gkr.typ"
// #include "./05-offline-memory-checking/00-offline-memory-checking.typ"
#include "./06-conclusion/00-conclusion.typ"
