#import "./00-lib/lib.typ": *
#import "@preview/theorion:0.4.1": *


#show: show-theorion
#show: ilm.with(
  title: [Roping in Lasso],
  author: "Rasmus Kirk Jakobsen",
  date: datetime.today(),
  abstract: text(size: 10pt, [
    An accessible guide to Lasso, which enables lookup arguments from much
    larger tables than previously possible. Lasso is the primary component
    of Jolt, the SNARK‑based virtual machine (zkVM) that proves correct
    execution for RISC-V programs via large table lookups, drastically reducing
    complexity and prover costs compared to earlier zkVMs. The document
    assumes minimal familiarity with the constructions that Lasso builds
    on, by introcing them within a single reference.
  ]),
  date-format: "[year repr:full]-[month padding:zero]-[day padding:zero]",
  bibliography: bibliography("refs.bib", style: "./refs-style.csl"),
  figure-index: (enabled: false),
  table-index: (enabled: true),
  listing-index: (enabled: true),
)

#include "./01-introduction/00-introduction.typ"
#include "./02-prerequisites/00-prerequisites.typ"
#include "./03-gkr/00-gkr.typ"
#include "./04-specialized-gkr/00-specialized-gkr.typ"
#include "./05-r1cs/00-r1cs.typ"
#include "./06-offline-memory-checking/00-offline-memory-checking.typ"
