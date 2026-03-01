#import "./00-lib/lib.typ": *
#import "@preview/theorion:0.4.1": *

#set math.mat(delim: "[")
#set text(font: "New Computer Modern")
// #show smallcaps: set text(font: "New Computer Modern")
#show math.equation: set text(font: "New Computer Modern Math")

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
    on, by introducing them within a single reference.
  ]),
  date-format: "[year repr:full]-[month padding:zero]-[day padding:zero]",
  bibliography: bibliography("refs.bib", style: "./refs-style.csl"),
  figure-index: (enabled: false),
  table-index: (enabled: false),
  listing-index: (enabled: true),
)

#include "./01-introduction/00-introduction.typ"
#include "./02-prerequisites/00-prerequisites.typ"
#include "./03-sumcheck/00-sumcheck.typ"
#include "./04-gkr/00-gkr.typ"
#include "./05-specialized-gkr/00-specialized-gkr.typ"
#include "./06-spartan/00-spartan.typ"
#include "./07-spark/00-spark.typ"
#include "./08-lasso/00-lasso.typ"
