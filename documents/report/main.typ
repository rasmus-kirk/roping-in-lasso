#import "./lib/template/lib.typ": *
#import "@preview/gruvy:2.1.0": gruvbox, theme-colors, colors
#import "@preview/zebraw:0.6.0": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/xarrow:0.3.1": xarrow, xarrowSquiggly, xarrowTwoHead
#import "@preview/theorion:0.4.1": *
#import cosmos.clouds: *
#import cosmos.clouds: render-fn as render-fn-2
#show: show-theorion

#set text(lang: "en")
#let theme = theme-colors.light.hard;
#show: zebraw.with(
    background-color: theme.bg0,
    lang-color: theme-colors.dark.soft.strong.blue,
)
#show: gruvbox.with(
    theme-color: theme,
    accent: theme.strong.blue,
    hl: theme.muted.yellow,
    print: true,
)
#show ref: set text(fill: theme.fg1)
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
  bibliography: bibliography("refs.bib", style: "./refs-style-2.csl"),
  figure-index: (enabled: false),
  table-index: (enabled: true),
  listing-index: (enabled: true),
)
#let remark = remark.with(fill: theme.muted.blue)
#let tip-box = tip-box.with(fill: theme.strong.green)
#let caution-box = caution-box.with(fill: theme.muted.red)
#let warning-box = warning-box.with(fill: theme.muted.yellow)
#let theorem = theorem.with(fill: theme.muted.blue.lighten(80%))
#let lemma = lemma.with(fill: theme-colors.dark.soft.strong.blue.lighten(80%))
#let (example-counter, example-box, example, show-example) = make-frame(
  "definition",
  theorion-i18n-map.at("example"),
  counter: none,
  render: render-fn-2.with(fill: theme.bg0.lighten(30%)),
)
#let todo-box = note-box.with(
  fill: theme.strong.aqua,
  title: "To-Do",
  icon-name: "pencil",
)

// Math
#let meq = math.eq.quest;
#let wildcard = underline("  ")
#let prover = math.cal("P")
#let verifier = math.cal("V")
#let circuit = math.cal("C")
#let Oc = math.cal("O")
#let Xc = math.cal("X")
#let bits = math.bb("B")
#let Fb = math.bb("F")
#let inrand = $attach(in, br: R)$
#let vec(body) = $bold(body)$

= Introduction

This document generally assumes that you're familiar with Bulletproofs,
specifically the Inner Product Arguments used. It also assumes basic
familiarity with Interactive Arguments and Pedersen commitments. These concepts
are well presented, somewhat less formal than the relevant original papers,
but in an understandable manner in Adam Gibson's excellent write-up "From Zero
(Knowledge) to Bulletproofs"@from0k2bp.

= Prerequisites

== Multilinear Extensions

== Sumcheck

$ H := sum_(b_1 in bits) sum_(b_2 in bits) dots sum_(b_v in bits) g(b_1, dots, b_v) $

#align(center)[
  #set math.equation(numbering: none)
  #set text(10pt)
  #let w = 0.7
  #diagram({
    let h = 0.7
    let (P, M, V) = ((0, 0), (1.5, 0), (3, 0))

    node(P, text(size: 12pt, weight: "black", "Prover"))
    node(V, text(size: 12pt, weight: "black", "Verifier"))
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    // -------------------- Round 1 -------------------- //
    node(M, $#text(size: 12pt, weight: "black", $"Round" 1$)$)
    edge(P, M, "=")
    edge(M, V, "=")
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    node(P, move(dy: .35em, $ g_1(X) := limits(sum)_(x_(2:v) in bits^(v-1)) g(X, x_(2:v))$))
    node(V, $ H meq g_1(0) + g_1(1)$)
    edge(P, V, "->", $H, g_1(X)$)
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    node(P, )
    node(V, $ deg(g_1) meq deg_1(g) $)
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    node(P, "")
    node(V, $ r_1 inrand Fb $)
    edge(V, P, "->", $r_1$)
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    // -------------------- Round j -------------------- //
    node(M, $#text(size: 12pt, weight: "black", $"Round" j in [2..d]$)$)
    edge(P, M, "=")
    edge(M, V, "=")
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    node(P, move(dy: .35em, $ g_(j)(X) := limits(sum)_(x_(j+1:v) in bits^(v-j)) g(r_(1:j-1), X, x_(j+1:v))$))
    node(V, $ g_(j-1)(r_(j-1)) meq g_(j)(0) + g_(j)(1)$)
    edge(P, V, "->", $g_(j)(X)$)
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    node(P, )
    node(V, $ deg(g_j) meq deg_(j)(g) $)
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    node(P, "")
    node(V, $ r_j inrand Fb $)
    edge(V, P, "->", $r_j$)
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    // -------------------- Round v -------------------- //
    node(M, $#text(size: 12pt, weight: "black", $"Round" v$)$)
    edge(P, M, "=")
    edge(M, V, "=")
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    node(P, move(dy: .35em, $ g_(v)(X) := g(r_(1:v-1), X)$))
    node(V, $ g_(v-1)(r_(j-1)) meq g_(v)(0) + g_(v)(1)$)
    edge(P, V, "->", $g_(v)(X)$)
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    node(P, )
    node(V, $ deg(g_v) meq deg_(v)(g) $)
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    node(P, "")
    node(V, $ r_v inrand Fb $)
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    node(P, "")
    node(V, $ g_(v)(r_v) meq g(r_(1:v)) $)
  })
]

= GKR

Given a circuit $circuit$, with $d$ layers, $n$ inputs and $m$ outputs,
a prover ($prover$) wishes to prove to a verifier ($verifier$) a specific
input $vec(w) in bits^n$ applied to $circuit$ produces some output $vec(o)
in bits^m$. To do this, we can leverage the sumcheck protocol, defined earlier.

#figure(
  align(center)[
    #set math.equation(numbering: none)
    #set text(10pt)
    #let w = 0.8
    #let h = 0.8
    #diagram(
      node-stroke: 1pt,
      {
        let O = (3*w, -1.5*h)
        let N00 = (3*w, 0*h)
        let (N10, N11) = ((1*w, 1*h), (5*w, 1*h))
        let (N20, N21, N22, N23) = (
          (0*w, 2*h),
          (2*w, 2*h),
          (4*w, 2*h),
          (6*w, 2*h),
        )
        let (N30, N31, N32, N33) = (
          (0*w, 3.5*h),
          (2*w, 3.5*h),
          (4*w, 3.5*h),
          (6*w, 3.5*h),
        )

        // Really hacky centering lol
        node((8.25*w, 0*h), "", stroke: none)
        node((-1.2*w, -1.5*h), "Outputs")
        node((-1.2*w, 0*h), "Layer 0")
        node((-1.2*w, 1*h), "Layer 1")
        node((-1.2*w, 2*h), "Layer 2")
        node((-1.2*w, 3.5*h), "Inputs")
        node(O, [$o_1$], shape: rect)
        node(N00, [$times_(0)$], radius: 1.2em)
        node(N10, [$times_(0)$], radius: 1.2em)
        node(N11, [$times_(1)$], radius: 1.2em)
        node(N20, [$times_(00)$], radius: 1.2em)
        node(N21, [$times_(01)$], radius: 1.2em)
        node(N22, [$times_(10)$], radius: 1.2em)
        node(N23, [$times_(11)$], radius: 1.2em)
        node(N30, [$w_1$], shape: rect)
        node(N31, [$w_2$], shape: rect)
        node(N32, [$w_3$], shape: rect)
        node(N33, [$w_4$], shape: rect)
        edge(N10, N00, "-|>")
        edge(N11, N00, "-|>")
        edge(N20, N10, "-|>")
        edge(N21, N10, "-|>")
        edge(N22, N11, "-|>")
        edge(N23, N11, "-|>")
        edge(N30, N20, "-->")
        edge(N31, N21, "-->")
        edge(N32, N22, "-->")
        edge(N33, N23, "-->")
        edge(N00, O, "-->")
      }
    )
  ],
  caption: text[
    A layered arithmetic circuit for the computation $o_1 = product_(i=1)^k
    a_i$. Each node-label below represents the type of computation and the
    gate-label for the given layer, so $(times_0)$ is a multiplication gate
    with label $0$, for layer $0$. Note that $d = 3$, $n = 4$, $m = 1$
  ],
  // supplement: [Diagram],
) <example_circuit>

// We define the following functions:

// - $"in"_(1,i)(a) ~> b : a in bits^(k_i), b in bits^(k_(i+1))$ which takes the gate-label of a node and gives the gate-label of the left input.
// - $"in"_(2,i)(a) ~> c : a in bits^(k_i), c in bits^(k_(i+1))$ which takes the gate-label of a node and gives the gate-label of the right input.

To represent a layered circuit in a form amenable to the sum check protocol,
we must first provide an adequate polynomial representation of the circuit. We
start with the following three functions:

- $"add"_(i)(a,b,c) in bits^(k_i+2k_(i+1)) -> bits$ which outputs $1$ if and only if gate $a$ is an addition gate and $b$ is the left input and $c$ is the right input of gate $a$.
- $"mul"_(i)(a,b,c) in bits^(k_i+2k_(i+1)) -> bits$ which outputs $1$ if and only if gate $a$ is a multiplication gate and $b$ is the left input and $c$ is the right input of gate $a$.
- $W_(i)(a) in bits^(k_i) -> bits$ which, given the gate-label $a$, outputs the value of node $a$.

#example[
  For @example_circuit $"add"_i, "mul"_i$ would evaluate to the following values:

  #math.equation(
    block: true,
    numbering: none,
    $
      mat(delim: #none, column-gap: #3em, align: #left,
        "mul"_0(0 || 0 || 0) = 1, "mul"_1(0 || 00 || 01) = 1;
        "mul"_0(0 || 0 || 1) = 1, "mul"_1(1 || 10 || 11) = 1;
        "mul"_0(wildcard) = 0,    "mul"_1(wildcard) = 0;
        "add"_0(wildcard) = 0,    "add"_1(wildcard) = 0;
      )
    $
  )
]

We can use the multilinear extensions of $"add"_i$ and $"mul"_i$ to represent
$W_(i)$ in a form that lets us use sumcheck:

$ tilde(W)_(i)(a) = sum_(b,c in bits^(k_(i+1))) tilde("add")_(i)(a,b,c)(tilde(W)_(i+1)(b) + tilde(W)_(i+1)(c)) + tilde("mult")_(i)(a,b,c) dot tilde(W)_(i+1)(b) dot tilde(W)_(i+1)(c) $

Assume that the prover convinces the verifier that some polynomial $D(X_1,
dots, X_(k_0)) = tilde(W)_0(X_1, dots, X_(k_0))$, meaning that the above
holds recursively all the way to layer $d$. Then the verifier can confirm
that the evaluations of the circuit given input $vec(w)$ evaluates to $vec(o)$
by simply evaluating $D(X_1, dots, X_(k_0))$ on all gate labels in the output
layer. To prove this, the verifier chooses a random point $r$ and wishes to
verify that $D(r) = W_0(r)$, which by Schwarz-Zippel means that $D(X_1,
dots, X_(k_0)) = W_0(X_1, dots, X_(k_0))$. Therefore, the prover and verifier
apply sumcheck to the following polynomial:

$ tilde(f)^((0))_(r)(b, c) = tilde("add")_(0)(r,b,c)(tilde(W)_1(b) + tilde(W)_1(c)) + tilde("mult")_(0)(r,b,c) dot tilde(W)_1(b) dot tilde(W)_1(c) $

Which, if succesful, convinces the verifier that $D(X_1, dots, X_(k_0)) =
W_0(X_1, dots, X_(k_0))$ as desired. But in the final round of the sumcheck
protocol, the verifier must be able to evaluate the above polynomial
at a random point. The functions $tilde("add")_0$ and $tilde("mul")_0$
are part of the circuit description, and can thus be computed by the
verifier without help from the prover #footnote[Luckily this can be done
by the verifier in $Oc(lg(k_0))$ time, which is important for achieving an
efficient verifier.] But the verifier also needs to evaluate $tilde(W_1)$
at two separate $k_i$ random points $b'_1, c'_1 inrand Fb^(k_1)$ corresponding
to $b, c$. In principle, we could run the sumcheck protocol twice,
on the polynomials:

$
  tilde(f)^((1))_(b'_1)(b, c) &= tilde("add")_(1)(b'_1,b,c)(tilde(W)_2(b) + tilde(W)_2(c)) + tilde("mult")_(1)(b'_1,b,c) dot tilde(W)_2(b) dot tilde(W)_2(c) \
  tilde(f)^((1))_(c'_1)(b, c) &= tilde("add")_(1)(c'_1,b,c)(tilde(W)_2(b) + tilde(W)_2(c)) + tilde("mult")_(1)(c'_1,b,c) dot tilde(W)_2(b) dot tilde(W)_2(c)
$ <eq:two-fs>

But this would result in an exponential amount of sumchecks in the depth $d$,
which would be quite a problem! Instead, we can reduce two checks into one,
using a linear combination.

== Combining two claims to one

Suppose we were to apply sumcheck to the following polynomial instead:

$
  tilde(q)(alpha) := tilde(W)_(1)(b'_1) + alpha dot tilde(W)_(1)(c'_1)
$

Which can be derived as:

$
  tilde(q)(alpha) &= &&(sum_(b,c in bits^(k_(2))) tilde("add")_(1)(b'_1,b,c)(tilde(W)_(2)(b) + tilde(W)_(2)(c)) + tilde("mul")_(1)(b'_1,b,c) dot tilde(W)_(2)(b) dot tilde(W)_(2)(c)) + \
                  &  &&alpha dot (sum_(b,c in bits^(k_(2))) tilde("add")_(1)(c'_1,b,c)(tilde(W)_(2)(b) + tilde(W)_(2)(c)) + tilde("mul")_(1)(c'_1,b,c) dot tilde(W)_(2)(b) dot tilde(W)_(2)(c)) \
                  &= &&sum_(b,c in bits^(k_(2))) tilde("add")_(1)(b'_1,b,c)(tilde(W)_(2)(b) + tilde(W)_(2)(c)) + tilde("mul")_(1)(b'_1,b,c) dot tilde(W)_(2)(b) dot tilde(W)_(2)(c) + \
                  &  &&alpha dot tilde("add")_(1)(c'_1,b,c)(tilde(W)_(2)(b) + tilde(W)_(2)(c)) + alpha dot tilde("mul")_(1)(c'_1,b,c) dot tilde(W)_(2)(b) dot tilde(W)_(2)(c) \
                  &= &&sum_(b,c in bits^(k_(2))) (tilde("add")_(1)(b'_1,b,c) + alpha dot tilde("add")_(1)(c'_1,b,c))(tilde(W)_(2)(b) + tilde(W)_(2)(c)) + \
                  &  &&(tilde("mul")_(1)(b'_1,b,c) + alpha dot tilde("mul")_(1)(c'_1,b,c))(tilde(W)_(2)(b) dot tilde(W)_(2)(c))
$ <eq:combined-poly>

The below Lemma shows how this will help the prover-verifier pair in showing
that $v_(b'_1) = tilde(W)_1(b'_1) and v_(b'_1) = tilde(W)_1(c'_1)$, thus
enabling the verifier to compute $tilde(f)_(r)^((0))(b'_1, c'_1)$:

#lemma[
  #set math.equation(numbering: none)
  For a polynomial $p(X_1, ..., X_k)$, if a prover wants to convince a verifier
  of two claims $v_1 = p(r_1), v_2 = p(r_2)$, then they can reduce this to a
  single claim over a polynomial $q(r_1, r_2)$:

  $
    q(X_1, .., X_(2k)) := p(X_1, ..., X_k) + alpha dot p(X_(k+1), ..., X_(2k))
  $

  The verifier can then check that $q(r_1, r_2) = p(r_1) + alpha dot p(r_2)$.
  The claim that $v_1 = p(r_1) and v_2 = p(r_2)$ will then hold except with
  negligible probability, given that $q(X_1, ..., X_(2k))$ is defined as above.
]

#proof[
  #set math.equation(numbering: none)
  If $q(r_1, r_2) = p(r_1) + alpha dot p(r_2)$ but the claim does not hold,
  i.e. $v_1 != p(r_1), v_2 != p(r_2)$, then that means that the univariate
  non-zero polynomial:

  $ e(X) = q(r_1, r_2) - p(r_1) + X dot p(r_2) $

  Evaluated to zero, which by the Schwarz-Zippel Lemma, has probability:

  $ Pr[e(alpha) = 0 | e(X) != 0] = frac(d, |Fb|) $

  In this case $d = 1$ which is negligible in the size of the field.
] <lem:multiple-evals-same-poly>

In the GKR protocol, running sumcheck on @eq:combined-poly convinces
the verifier that $tilde(q)_1(b'_1, c'_1) = tilde(W)_1(b'_1) + alpha dot
tilde(W)_1(c'_1)$, which means that the verifier knows that $tilde(q)_1(X)$
is defined as in <lem:multiple-evals-same-poly> and they know the evaluation
of $tilde(q)_1(X)$ at $b'_1, c'_1$. The verifier can then verify that $v_(b'_1)
= tilde(W)_1(b'_1)$ and $v_(c'_1) = tilde(W)_1(c'_1)$ by additionally checking
that $tilde(q)_1(b'_1, c'_1) = v_(b'_1) + alpha dot v_(c'_1)$.

With $v_(b'_1)$ and $v_(c'_1)$ the verifier can compute the evaluation of
$tilde(f)_(r)^((0))(b'_1, c'_1)$:

$ tilde(f)^((0))_(r)(b', c') = tilde("add")_(0)(r,b'_1,c'_1)(v_(b'_1) + v_(c'_1)) + tilde("mult")_(0)(r,b'_1,c'_1) dot v_(b'_1) dot v_(c'_1) $

Thus, when we proceed from the first layer, the polynomial we do sumcheck
on would be:

$
  tilde(f)^((1))_((b'_1, c'_1))(b, c) &:= &&(tilde("add")_(1)(b'_1,b,c) + alpha dot tilde("add")_(1)(c'_1,b,c))(tilde(W)_(2)(b) + tilde(W)_(2)(c)) + \
                                      &   &&(tilde("mul")_(1)(b'_1,b,c) + alpha dot tilde("mul")_(1)(c'_1,b,c))(tilde(W)_(2)(b) dot tilde(W)_(2)(c))
$

It should already now be apparent that we can repeat this procedure, all
the way to the input layer $d$.

== Completing the protocol

In the input layer, the final check in the sumcheck protocol requires the
verifier to evaluate the following polynomial at $b'_d, c'_d$:

$
  tilde(f)^((d-1))_((b'_(d-1), c'_(d-1)))(b, c) &:= &&(tilde("add")_(d-1)(b'_(d-1),b,c) + alpha dot tilde("add")_(d-1)(c'_(d-1),b,c))(tilde(W)_(d)(b) + tilde(W)_(d)(c)) + \
                                                &   &&(tilde("mul")_(d-1)(b'_(d-1),b,c) + alpha dot tilde("mul")_(d-1)(c'_(d-1),b,c))(tilde(W)_(d)(b) dot tilde(W)_(d)(c))
$

The polynomials $tilde("add")_(d-1)$ and $tilde("mul")_(d-1)$ can be evaluated
as usual. The polynomial $tilde(W)_(d)(X, dots, X_(k_d))$ corresponds to the
values of the input layer $vec(w)$. Since the verifier knows $vec(w)$ they
can compute the multilinear extension of $vec(w)$ corresponding to $W_(d)(X,
..., X_(k_d))$. From this the verifier can compute $tilde(W)_(d)(b'_d),
tilde(W)_(d)(c'_d)$ and thus the evaluation of $tilde(f)^((d-1))_((b'_(d-1),
c'_(d-1)))(b, c)$.

The entire protocol can be seen below:

#let zero-width-box(body) = context {
  let width = 35em
  let (height,) = measure(width: width, body)
  place(center + horizon, box(width: width, height: height, body))
  box(width: 0%, height: 2 * height)
}

#align(center)[
  #set math.equation(numbering: none)
  #set text(10pt)
  #let w = 0.7
  #let h = 0.7

  #diagram(debug: 0, {
    let (P, M, V) = ((0, 0), (1.5, 0), (3, 0))

    node(M,
      zero-width-box(text(theme.fg2)[$#text(size: 12pt, $
        hat(x) &:= ("add"_0, ..., "add"_d, "mul"_0, ..., "mul"_d)
      $)$])
    )

    P.at(1) += h/3; M.at(1) += h/3; V.at(1) += h/3;

    node(P, $#text(size: 12pt, $bold("Prover")(hat(x), vec(w))$)$)
    node(V, $#text(size: 12pt, $bold("Verifier")(hat(x), vec(w))$)$)
    P.at(1) += h/2; M.at(1) += h/2; V.at(1) += h/2; 

    // -------------------- Preprocessing -------------------- //
    node(M, $#text(size: 12pt, weight: "black", $"Preprocessing"$)$)
    edge(P, M, "=")
    edge(M, V, "=")
    P.at(1) += h/1.5; M.at(1) += h/1.5; V.at(1) += h/1.5; 

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      $prover$ sends $W'$ to $verifier$ claiming that $W' = W_0$. $verifier$
      then picks out a random $r$. After this point, $prover$ wants to
      prove that $m_0 = tilde(W)_0(r)$.
    ]))
    P.at(1) += h/1.5; M.at(1) += h/1.5; V.at(1) += h/1.5;

    node(P, $W': bits^(k_0) -> Fb$)
    node(V, $ r inrand Fb, m_0 := tilde(W)'(r) $)
    edge(P, V, "->", $ W' $)
    P.at(1) += h/2; M.at(1) += h/2; V.at(1) += h/2; 

    // -------------------- Round 0 -------------------- //
    node(M, $#text(size: 12pt, weight: "black", $"Round" 0$)$)
    edge(P, M, "=")
    edge(M, V, "=")
    P.at(1) += h/1.3; M.at(1) += h/1.3; V.at(1) += h/1.3; 

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      $prover$ defines the $(2k_i)$-variate polynomial,
      $tilde(f)^((0))_(r)(b, c)$, $prover$ and $verifier$ then perform
      sumcheck on the polynomial:
      $ tilde(f)^((0))_(r)(b, c) = tilde("add")_(0)(r,b,c)(tilde(W)_1(b) + tilde(W)_1(c)) + tilde("mul")_(0)(r,b,c) tilde(W)_1(b) dot tilde(W)_1(c) $
    ]))
    P.at(1) += h; M.at(1) += h; V.at(1) += h;

    // node(P, $ tilde(f)^((0))_(r)(b', c')$)
    edge(P, V, "<->", $sum_(b, c in bits^(k_1)) tilde(f)^((0))_(r)(b, c) meq m_0$)
    P.at(1) += h/1.5; M.at(1) += h/1.5; V.at(1) += h/1.5; 

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      At the end of the protocol, $prover$ sends $verifier$ the evaluations
      of $v_(b'_0) := tilde(W)_1(b'_0)$ and $v_(c'_0) := tilde(W)_1(c'_0)$, so
      $verifier$ can make the final check in the sumcheck protocol.
    ]))
    P.at(1) += h; M.at(1) += h; V.at(1) += h;

    node(P, $v_(b'_0) := tilde(W)_1(b'_0), v_(c'_0) := tilde(W)_1(c'_0)$)
    node(V, $
      m_0 meq &tilde("add")_0(r, b'_0, c'_0) dot (v_(b'_0) + v_(c'_0)) + \
              &tilde("mul")_0(r, b'_0, c'_0) dot v_(b'_0) dot v_(c'_0)
    $)
    edge(P, V, "->", $v_(b'_0), v_(c'_0)$)
    P.at(1) += h/1.5; M.at(1) += h/1.5; V.at(1) += h/1.5; 

    // -------------------- Round i -------------------- //
    node(M, $#text(size: 12pt, weight: "black", $"Round" i in [1..d]$)$)
    edge(P, M, "=")
    edge(M, V, "=")
    P.at(1) += h/1.3; M.at(1) += h/1.3; V.at(1) += h/1.3; 

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      To verify the values $v_(b'_(i-1)), v_(c'_(i-1))$ from the previous round,
      $verifier$ picks out a randomly sampled value $alpha$ and sends it
      to $prover$. $prover$ uses $alpha$ to construct the combined-claim
      polynomial, for which $prover$ and $verifier$ perform the sumcheck over:

      $
        tilde(f)^((i))_((b'_i, c'_i))(b, c) := (tilde("add")_(i)(b'_i,b,c) + tilde("add")_(i)(c'_i,b,c))(tilde(W)_(i+1)(b) + tilde(W)_(i+1)(c)) +
                                               (tilde("mul")_(i)(b'_i,b,c) + tilde("mul")_(i)(c'_i,b,c))(tilde(W)_(i+1)(b) dot tilde(W)_(i+1)(c))
      $
    ]))
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    node(P, $tilde(f)^((i))_((b'_i, c'_i))(b, c)$)
    node(V, $ alpha inrand Fb $)
    edge(V, P, "->", $alpha$)
    P.at(1) += h/2; M.at(1) += h/2; V.at(1) += h/2; 

    edge(P, V, "<->", $sum_(b, c in bits^(k_(i+1))) tilde(f)^((i))_((b'_i, c'_i))(b, c) meq m_i$)
    P.at(1) += h/1.3; M.at(1) += h/1.3; V.at(1) += h/1.3;

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      At the end of the protocol, $prover$ sends $verifier$ the evaluations of
      $v_(b'_i) := tilde(W)_(i)(b'_i)$ and $v_(c'_i) := tilde(W)_(i)(c'_i)$,
      so $verifier$ can make the final check in the sumcheck protocol:

      $
        m'_i &:= &&(tilde("add")_(i)(b'_i,b'_(i+1),c'_(i+1)) + tilde("add")_(i)(c'_i,b'_(i+1),c'_(i+1)))(tilde(W)_(i+1)(b'_(i+1)) + tilde(W)_(i+1)(c'_(i+1))) + \
             &   &&(tilde("mul")_(i)(b'_i,b'_(i+1),c'_(i+1)) + tilde("mul")_(i)(c'_i,b'_(i+1),c'_(i+1)))(tilde(W)_(i+1)(b'_(i+1)) dot tilde(W)_(i+1)(c'_(i+1)))
      $
      
    ]))
    P.at(1) += h; M.at(1) += h; V.at(1) += h;

    node(P, $v_(b'_i) := tilde(W)_(i)(b'_i), v_(c'_i) := tilde(W)_(i)(c'_i)$)
    node(V, $m_i meq m_i'$)
    edge(P, V, "->", $v_(b'_i), v_(c'_i)$)
    P.at(1) += h/2.4; M.at(1) += h/2.4; V.at(1) += h/2.4; 

    // -------------------- Round d -------------------- //
    node(M, $#text(size: 12pt, weight: "black", $"Round" d$)$)
    edge(P, M, "=")
    edge(M, V, "=")
    P.at(1) += h/1.6; M.at(1) += h/1.6; V.at(1) += h/1.6;

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      At the input layer $d$, $verifier$ has two claims $v_(b')$ and
      $v_(c')$. $verifier$ constructs $tilde(W)_d$ from $vec(w)$. $verifier$
      then finally checks that $tilde(W)_(d)(b') meq v_(b')$ and $tilde(W)_(d)(c')
      meq v_(c')$.
    ]))
    P.at(1) += h/2; M.at(1) += h/2; V.at(1) += h/2; 
    
    node(V, $ tilde(W)_d(b') meq v_(b') and tilde(W)_d(c') meq v_(c') $)
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 
  })
]

== Efficiency

= A specialized GKR protocol

If we consider the circuit consisting of a binary tree of multiplication
gates as in @example_circuit. We can present a simpler expression than that
of regular GKR:

$ tilde(W)_(i)(a) = sum_(b in bits^(k_(i))) tilde("eq")(a, b) dot tilde(W)_(i+1)(a || 0) dot tilde(W)_(i+1)(a || 1) $

It's obvious to see that this expression is equivalent to the one from
regular GKR, but only for the binary tree of multiplication gates.

In each round of the sumcheck protocol, the prover needs to evaluate a
univariate polynomial of the form:

$
  tilde(q)_(i)(alpha) &= &&tilde(W)_(i)(a'_i || 0) + alpha tilde(W)_(i)(a'_i || 1) \
  tilde(q)_(i)(alpha) &= &&(sum_(b in bits^(k_(i))) tilde("eq")(a'_i || 0, b) dot tilde(W)_(i)(b || 0) dot tilde(W)_(i+1)(b || 1)) + \
                      &  && (sum_(b in bits^(k_(i))) alpha dot tilde("eq")(a'_i || 1, b) dot tilde(W)_(i)(b || 0) dot tilde(W)_(i+1)(b || 1)) \
  tilde(q)_(i)(alpha) &= &&sum_(b in bits^(k_(i))) (tilde("eq")(a'_i || 0, b) + alpha dot tilde("eq")(a'_i || 1, b)) dot tilde(W)_(i+1)(b || 0) dot tilde(W)_(i+1)(b || 1)
$

So the sum-check polynomial would be:

$
  tilde(f)_(r)^((0))(b) &= tilde("eq")_(r)(b) dot tilde(W)_(1)(r || 0) dot tilde(W)_(1)(r || 1)
$

$
  tilde(f)_(a'_i)^((i))(b) &= (tilde("eq")_((a'_(i) || 0))(b) + alpha dot tilde("eq")_((a'_(i) || 1))(b)) dot tilde(W)_(i+1)(a'_(i) || 0) dot tilde(W)_(i+1)(a'_(i) || 1)
$

== Efficiency

First note, that the prover, if given the values $tilde("eq")_(r)(b),
tilde("eq")_0(b), tilde("eq")_1, alpha, tilde(W)_(i+1)(0)$ and
$tilde(W)_(i+1)(1)$, they could evaluate this in constant time for each
round of the sum-check. We now present how these values can be computed in
$Oc(S(n))$ time.

We use a general method from dynamic programming throughout the next couple
subsections. The general idea is that if you need to compute something ...

=== Computing $"eq"(a, b)$ in linear time

We start by looking at the definition of $"eq"_(r)(b) in bits -> bits$:

$ "eq"_(r)(b) := r b + (1 - r) (1 - b) $

Note that $r$ is fixed to a random value by the verifier. To compute a table
of all evaluations ($vec("eq")_r in bits^(s_0) -> bits$) of $"eq"_(r)(vec(b))$ it
would naively take $s_0$ time per evaluation, and there are $2^(s_0)$ total
possible evaluations for $b_i in bits$, so $Oc(s_0 2^(s_0))$ time to compute
$vec("eq")$. We use dynamic programming to bring this down to $Oc(2^(s_0))$.

$
  vec("eq")_(r)^((0))[b] = r b + (1 - r) (1 - b)
$

If we take the definition of $tilde("eq")(vec(a), vec(b))$ for a fixed $vec(a) =
vec(v) : |v| = k$, we get:

$
  tilde("eq")_(vec(v))(vec(b)) = product^(k)_(j=1) (v_j b_j + (1 - v_j) (1 - b_j))
$

Given any $vec("eq")_(vec(v))[b_1, ..., b_(s_i)]$, we can trivially compute
$tilde("eq")_((v || 0))$ and $tilde("eq")_((v || 1))$:

$
  vec("eq")_((vec(v) || 0))[b_1, ..., b_(k+1)] &= vec("eq")_(vec(v))[b_1, ..., b_(k)] dot (1 - b_(k + 1)) \
  vec("eq")_((vec(v) || 1))[b_1, ..., b_(k+1)] &= vec("eq")_(vec(v))[b_1, ..., b_(k)] dot b_(k + 1) \
$


For round $i$ of the GKR protocol, in round $j$ in the sumcheck invocation,
let's inspect $"eq"^(i)_((vec(a'_i) || 0))(vec(b))$. Let $vec(a'_i) || 0 = vec(v)$:

$ "eq"^((i))_((vec(a'_i) || 0))(vec(b)) = product^(j)_(k=1) (v_k r_k + (1 - v_k) + (1 - r_k)) + product^(s_i)_(k=j+1) (v_k b_k + (1 - v_k) + (1 - b_k)) $

Since we evaluate $f^((i))_(a')$ at $vec(b) = [ r_1, ..., r_j, b_(j+1), b_(j+2), ..., b_(s_i) ]$, with $b_(j+1) = {0, 1, 2, 3}$:

$
  tilde(f)_(vec(a')_i)^((i))(vec(b)) &= (tilde("eq")_((a'_(i) || 0))(b) + alpha dot tilde("eq")_((a'_(i) || 1))(b)) dot tilde(W)_(i+1)(vec(b)) dot tilde(W)_(i+1)(vec(b))
$

The $r_1, ..., r_j$'s are set by the verifier, as required by the sumcheck
protocol. Remember, the goal is for the prover to evaluate each term
in linear time, and to do so the prover needs an evaluation table of
$tilde("eq")_((a'_(i) || 0))([b_(j+1), dots, b_(s_i)])$ and
$tilde("eq")_((a'_(i) || 1))([b_(j+1), dots, b_(s_i)])$.

For $j=0$ we can compute the table via the following reoccurance

// We start by looking at the definition of $"eq"(a, b) in Fb^(s_i) times Fb^(s_i)
// -> Fb$:

// $ "eq"(vec(a), vec(b)) := product^(s_i)_(j=1) (a_j b_j + (1 - a_j) (1 - b_j)) $

// Note that $vec(b)$ is fixed to a random value by the verifier. To compute a
// table of all evaluations ($vec("eq") in Fb^(s_i) -> Fb$) of $"eq"(vec(a),
// vec(b))$ it would naively take $s_i$ time per evaluation, and there are
// $2^(s_i)$ total possible evaluations for $a_i in bits$, so $Oc(s_i 2^(s_i))$
// time to compute $vec("eq")$. We use dynamic programming to bring this down
// to $Oc(2^(s_i))$.

// $
//   vec("eq")^((0,1)) = a_1 b_1 + (1 - a_1) (1 - b_1) \
//   vec("eq")^((0,j))(a_1, ..., a_j) = vec("eq")^((0, j-1))(a_1, ..., a_(j-1)) dot (a_j b_j + (1 - a_j) (1 - b_j))
// $

// Then $vec("eq")^((0, s_i)) = vec("eq")^((0))$ for round zero.

*The Rounds*

In round zero, then, we need to evaluate $"eq"(vec(a), vec(b))$ at a

$ tilde(f)(X_1, ..., X_k) = sum_(w in bits^k) f(w) dot Xc_(w)(X_1, ..., X_k) $

where, for any $vec(w)$:

$ Xc_(vec(w))(X_1, ..., X_k) := product^k_(j=1) X_j w_i + (1 - X_i)(1-w_i) $

= Spark

Before introducing Spark, we'll first introduce the primary argument that
SPARK builds on, the *PLACEHOLDER*.

// #lemma[
//   #set math.equation(numbering: none)
  
//   If we at any point in an interactive protocol, need evaluations of $k$
//   polynomials at a single random point ($beta$), we can reduce $k$ polynomial
//   evaluations to just one. A protocol for this is sketched out below:

//   #align(center)[
//     #set math.equation(numbering: none)
//     #set text(10pt)
//     #diagram({
//       let height = 0.7
//       let (P, V) = ((0, 0), (3, 0))

//       node(P, $#text(size: 12pt, $#text(size: 12pt, weight: "black", "Prover") #h(0em) (vec(p) in Fb^(k)_(<= d)[X])$)$)
//       node(V, text(size: 12pt, weight: "black", "Verifier"))
//       P.at(1) += height; V.at(1) += height; 

//       node(P)
//       node(V, $alpha inrand Fb$)
//       edge(P, V, "->", $vec(p)$)
//       P.at(1) += height; V.at(1) += height; 

//       node(P, $ q(X) = sum^(k)_(i=1) alpha^(i-1) dot p_(i)(X) $)
//       node(V)
//       edge(V, P, "->", $alpha$)
//       P.at(1) += height; V.at(1) += height; 

//       node(P)
//       node(V, $ beta inrand Fb $)
//       edge(P, V, "->", $q(X)$)
//       P.at(1) += height; V.at(1) += height; 

//       node(P, $forall i in [k] : v_k = p_(k)(beta)$)
//       node(V, $q(beta) meq sum^(k)_(i=1) alpha^(i-1) dot v_(i)(X)$)
//       edge(P, V, "->", $vec(v)$)
//       P.at(1) += height; V.at(1) += height; 

//       node(P)
//       node(V, $forall i in [k] : deg(p_(k)(X)) <= d$)
//       P.at(1) += height; V.at(1) += height; 

//       node(P)
//       node(V, $deg(q(X)) <= d$)
//     })
//   ]

//   So the prover sends the polynomials $vec(p)$ to the verifier, and the verifier
//   responds with a challenge $alpha$. Then the prover constructs $q(X)$ from
//   $vec(p)$ and $alpha$ and send these to the verifier, to which the verifier
//   responds with yet another challenge $beta$. The prover finally evaluates
//   and sends all the $k$ polynomials in $vec(p)$ to the verifier which makes
//   their checks:

//   $ q(beta) meq sum^(k)_(i=1) alpha^(i-1) dot v_(i)(X), #h(2em) forall i in [1..k] : deg(p_(k)(X)) <= d, #h(2em) deg(q(X)) <= d $

//   Now, if the above checks passes the verifier will be convinced that
//   $p_k(beta) = v_k$ with negligible soundness error and by leveraging only
//   a single polynomial evaluation.

//   *Completeness:*

//   It's easy to see that, given an honest prover, the degree bounds will always
//   pass the verifier's check and that definitionally $q(beta) = sum^(k)_(i=1)
//   alpha^(i-1) dot v_(i)(X)$. Giving us perfect completeness.

//   *Soundness:*

//   Soundness follows from Schwartz-Zippel. If you view the polynomial $q(X)$
//   as a univariate polynomial variable in $alpha$, with $v_(i)(X)$ being
//   the constants:

//   $ q(alpha) meq sum^(k)_(i=1) alpha^(i-1) dot v_(i)(X) $

//   Then if the evaluation of $q'(alpha) = sum^(k)_(i=1) alpha^(i-1) dot
//   v_(i)(X)$ at the same $alpha$ are equal, then they are the same polynomial
//   by Schwartz-Zippel.
// ] <lem:poly-batch>

// We can now using @lem:poly-batch reduce the two polynomials in
// @eq:two-fs to a single polynomial $tilde(q)^((1))(b_1, c_1)$:

// $
//   tilde(q)^((1))(b_1, c_1) := tilde(f)^((1))_(b')(b_1, c_1) + alpha dot tilde(f)^((1))_(c')(b_1, c_1)
// $

// We can now do the same for each layer $i$ until we reach the input layer
// #footnote[Remember: GKR starts from the output layer and moves towards the
// input layer.]. At the input layer


// $
//   tilde(q)^((1))(b_1, c_1) &:= tilde(f)^((1))_(b')(b_1, c_1) + alpha dot tilde(f)^((1))_(c')(b_1, c_1) \
//                            &= tilde("add")_(1)(b',b_1,c_1)(tilde(W)_2(b_1) + tilde(W)_2(c_1)) + tilde("mult")_(1)(b',b_1,c_1) dot tilde(W)_2(b_1) dot tilde(W)_2(c_1) \
//                            &+tilde("add")_(1)(c',b_1,c_1)(tilde(W)_2(b_1) + tilde(W)_2(c_1)) + tilde("mult")_(1)(c',b_1,c_1) dot tilde(W)_2(b_1) dot tilde(W)_2(c_1) \
// $
