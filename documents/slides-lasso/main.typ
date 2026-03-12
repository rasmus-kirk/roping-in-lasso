#import "./00-lib/lib.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/polylux:0.4.0": *

#show: setup

#set math.mat(delim: "[")
// #set text(font: "New Computer Modern")
// #show smallcaps: set text(font: "New Computer Modern")
#show math.equation: set text(font: "New Computer Modern Math")

#slide[
  #set page(header: none, footer: none, margin: 3em)

  #text(size: 1.3em)[
    *Roping in Lasso*
  ]

  Spartan

  #divider

  #set text(size: .8em, weight: "light")
  Rasmus Kirk Jakobsen

  #datetime.today().display()
]

#slide[
  = Agenda

  #outline
]

#include "01-spartan/00-spartan.typ"
#include "02-spark/00-spark.typ"
#include "03-lasso/00-lasso.typ"
