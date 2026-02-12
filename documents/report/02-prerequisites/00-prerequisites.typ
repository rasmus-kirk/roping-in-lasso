#import "../00-lib/header/lib.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

= Prerequisites

Throughout this document we use the following notation:

#align(center)[
#table(
  columns: 2,
  inset: 10pt,
  align: horizon,
  table.header(
    [*Notation*], [*Meaning*],
  ),
  // Field element
  $a in Fb$,
  [A field element of an unspecified field.],
  // Vector
  $(a_1, ..., a_n) = vec(a) in Fb^n$,
  [A vector of length $n$ consisting of elements from $Fb$.],
  // Random sampling
  $a inrand S$,
  [A value randomly sampled from set $S$.],
  // Vector-vector concatenation
  [$vec(a) || vec(b)$ where $vec(a) in S^n, vec(b) in S^m$],
  [Concatenate $vec(a), vec(b)$ to create a vector $vec(c) in S^(n+m)$.],
  // Vector-element concatenation
  [$vec(a) || b$ where $vec(a) in S^n, b in S$],
  [Concatenate $vec(a), b$ to create a vector $vec(c) in S^(n+1)$.],
  // Boolean
  [$bits = { 0, 1 }$],
  [A boolean or bit.],
  // Multivariate Polynomial
  [$f(x_1, ..., x_n) = f(x in Fb^n)$],
  [A multivariate polynomial with $n$ variables.],
  // MLE
  [$tilde(f)$],
  [A multilinear extension of the function $f$.],
  // Lookup table
  [$hat(f) in bits^n -> Fb$],
  [A lookup table.],
)
]

== Multilinear Extensions<sec:mle>

Given any function $f(vec(x)) in bits^ell -> Fb$, we can create
an extension polynomial $tilde(f)(vec(x))$ such that $forall vec(b)
in bits^ell : tilde(f)(vec(b)) = f(vec(b))$ using Lagrange interpolation:

$ tilde(f)(vec(x)) := sum_(vec(b) in bits^ell) f(vec(b)) dot tilde("eq")_vec(x)(vec(b)) $

Where:

$ tilde("eq")_vec(x)(vec(b)) := product^ell_(i=1) x_i b_i + (1 - x_i) (1 - b_i) $

This is presented and proved as Fact 3.5 in @thaler-book. Furthermore,
this polynomial extension always has degree at most one in each variable
and it is _unique_, a fact that we will use throughout the text. The polynomial
$tilde(f)(vec(x))$ is said to be the multilinear extension (MLE) of $f(vec(x))$
and such an MLE is always denoted using a tilde in this document.

It's clear that evaluating $tilde("eq")(vec(x), vec(y))$ naively would take
$O(ell)$ time, and thus, it would take $Oc(2^ell dot ell)$ time to compute
$tilde(f)(vec(x))$. If we want to remove this $ell$ factor, we can make use
of Dynamic Programming.

#lemma[
  An evaluation table, $hat("eq")_(vec(x))(vec(b))$, for the equality function
  $tilde("eq")_vec(x)(vec(b)) in bits^ell -> bits$, with a fixed $vec(x)$
  can be computed in time $O(2^ell)$ using $O(2^ell)$ space.
]<lem:linear-eq>

#proof[
  To construct $hat("eq")_(vec(x))(vec(b))$ we can use Dynamic Programming.

  $
    hat("eq")_(vec(x))^((1))(vec(b) in bits^1) &= (x_1 b_1 + (1 - x_1) (1 - b_1)) \
    hat("eq")_(vec(x))^((k))(vec(b) in bits^k) &= hat("eq")_vec(x)^((k-1))((b_(1), dots, b_(k-1))) dot (x_k b_k + (1 - x_k) (1 - b_k)) \
    hat("eq")_(vec(x))(vec(b) in bits^ell) &= hat("eq")_vec(x)^((k))(vec(b)) \
  $<eq:prereq-eq-hat>

  We first trivially construct $hat("eq")_(vec(x))^(1)(vec(b))$ in
  $O(1)$ time. Then, we construct $hat("eq")_(vec(x))^(k)(vec(b))$ for
  each $k in [1..ell]$ using Dynamic Programming, which takes $Oc(2^k)$
  time and space. Finally, we get $hat("eq")_(vec(x))(vec(b)) =
  hat("eq")_vec(x)^((k))(vec(b))$.
]

#example[
  We show a small example for $|vec(x)| = ell = 2$:
  $
    hat("eq")_(vec(x))^((1))[(0)] &:= x_1 dot 0 + (1 - 0)(1 - x_1) &&= 1 - x_1 \
    hat("eq")_(vec(x))^((1))[(1)] &:= x_1 dot 1 + (1 - 1)(1 - x_1) &&= x_1  \
    hat("eq")_(vec(x))^((2))[(0, 0)] &:= hat("eq")_(vec(x))^((1))[(0)] dot (1 - x_2) &&= (1 - x_1) dot (1 - x_2) \
    hat("eq")_(vec(x))^((2))[(0, 1)] &:= hat("eq")_(vec(x))^((1))[(0)] dot x_2 &&= (1 - x_1) dot x_2 \
    hat("eq")_(vec(x))^((2))[(1, 0)] &:= hat("eq")_(vec(x))^((1))[(1)] dot (1 - x_2) &&= x_1 dot (1 - x_2) \
    hat("eq")_(vec(x))^((2))[(1, 1)] &:= hat("eq")_(vec(x))^((1))[(1)] dot x_2 &&= x_1 dot x_2 \
  $
  Each lookup in $hat("eq")_(vec(x))^((k-1))$ is constant and computing each new entry in
  $hat("eq")_(vec(x))^((k))$ takes constant time. There are $2^k$ entries in
  $hat("eq")_(vec(x))^((k))$, so it takes $O(2^k)$ time to compute the table.
]

Then we can compute the evaluation of any $tilde(f)(vec(x))$ by utilizing
@lem:linear-eq to get $hat("eq")_(vec(x))(vec(b))$ and then computing:

$ tilde(f)(vec(x)) := sum_(vec(b) in bits^ell) f(vec(b)) dot hat("eq")_(vec(x))(vec(b)) $

#corollary[
  For any function $f(vec(x)) in bits^ell -> Fb$, its multilinear extension
  $tilde(f)(vec(x))$ can be computed using $O(2^ell)$ time and space.
]<cor:linear-mle>

== Sumcheck<sec:sumcheck>

The sumcheck protocol is an Interactive Proof where the prover, $prover$,
wishes to convince the verifier, $verifier$, of a statement of the following
form:

$ y := sum_(b_1 in bits) sum_(b_2 in bits) dots sum_(b_ell in bits) g(b_1, dots, b_ell) $

At a high-level, $prover$ starts by sending the claimed value of $g(vec(x))$.
The protocol then proceeds in $ell$ rounds, wherein each round a single sum
is shaved off the expression. For round one, $prover$ sends a specification
of the univariate polynomial $g_1$:

$ g_1(X) := sum_(b_(2:ell) in bits^(ell-1)) g(X, b_(2:ell)) $

Here "specification" may sound vague, but that's intentional. The protocol is
indifferent to whether $prover$ sends $g_1(x)$ in coefficient or evaluation
form. $prover$ can either send $deg(g_1(x))+1$ evaluations of the polynomial
or the coefficients of $g_1(x)$ to $verifier$. Then, $verifier$ checks that:

$
  y &meq g_1(0) + g_1(1) \
    &=   (sum_(vec(b)_(2:ell) in bits^(ell-1)) g(0, vec(b)_(2:ell))) + (sum_(vec(b)_(2:ell) in bits^(ell-1)) g(1, vec(b)_(2:ell))) \
    &=   sum_(vec(b) in bits^ell) g(vec(b))
$

Along with a degree check that $deg(g_1) meq deg_1(g)$. The rest of the
rounds proceed in a similar manner, until the final round, where $verifier$
also need to additionally check that $g_(ell)(r_ell) meq g(vec(r))$.

*Soundness and Completeness:*

The protocol is both sound and complete, with completeness error of $delta_c =
0$ and a soundness error of $delta_s <= frac(ell d, |Fb|)$. Here $d$ is the
degree bound of each univariate polynomial sent in the protocol, i.e. $forall i
in [1.. ell] : deg(g_i) <= d$. A proof can be seen in @thaler-book Proposition
4.1

*Efficiency:*

- *Communication Cost:* In each round $deg_(j)(g(vec(x)))$ field elements
  are sent by $prover$ and a single field element is sent by $verifier$. So,
  $Oc(sum^ell_(j=1) deg_j(g(vec(x))))$.
- *Verifier Runtime:* The verifiers runtime is proportional to the
  communication cost plus an additional evaluation of $g(vec(x))$, so
  $Oc("Eval"_g + sum^ell_(j=1) deg_j(g(vec(x))))$.
- *Provers Runtime:* In each round, the prover must evaluate $g(vec(x))$
  at $deg_j(g)+1$ points for each $2^(ell-j)$ term. This gives
  $Oc(sum^(ell)_(j=1) deg_j(g) dot 2^(ell-j) dot T)$, where $T$ is the cost of
  a single evaluation of $g(vec(x))$. Usually $deg_(j)(g(vec(x)))$ is bounded
  by some constant, in which case the cost is $Oc(2^(ell) dot T)$, since
  $sum^(ell)_(j=1) 2^(ell-j) = 2^(ell)$.

If the individual degree of $g(vec(x))$ is bounded, and $T$ is constant
($Oc(1)$) then the prover has a runtime of only $Oc(2^ell)$. Unfortunately,
$T$ is rarely constant, but in @sec:specialized-gkr we give an example of
an IP where this is the case, which lets us build an IP that proves that $y
meq product_(w_i in vec(w)) w_i$ with a prover runtime linear in $|vec(w)|$.

The entire sumcheck protocol can be seen below:

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

    node(P, move(dy: .35em, $ g_1(X) := limits(sum)_(vec(b)_(2:ell) in bits^(ell-1)) g(X, vec(b)_(2:ell))$))
    node(V, $ y meq g_1(0) + g_1(1)$)
    edge(P, V, "->", $y, g_1(X)$)
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    node(P, )
    node(V, $ deg(g_1) meq deg_1(g) $)
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    node(P, "")
    node(V, $ r_1 inrand Fb $)
    edge(V, P, "->", $r_1$)
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    // -------------------- Round j -------------------- //
    node(M, $#text(size: 12pt, weight: "black", $"Round" j in [2..ell - 1]$)$)
    edge(P, M, "=")
    edge(M, V, "=")
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    node(P, move(dy: .35em, $ g_(j)(X) := limits(sum)_(vec(b)_(j+1:ell) in bits^(ell-j)) g(vec(r)_(1:j-1), X, vec(b)_(j+1:ell))$))
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

    // -------------------- Round ell -------------------- //
    node(M, $#text(size: 12pt, weight: "black", $"Round" ell$)$)
    edge(P, M, "=")
    edge(M, V, "=")
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    node(P, move(dy: .35em, $ g_(ell)(X) := g(vec(r)_(1:ell-1), X)$))
    node(V, $ g_(ell-1)(r_(j-1)) meq g_(ell)(0) + g_(ell)(1)$)
    edge(P, V, "->", $g_(ell)(X)$)
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    node(P, )
    node(V, $ deg(g_ell) meq deg_(ell)(g) $)
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    node(P, "")
    node(V, $ r_ell inrand Fb $)
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 

    node(P, "")
    node(V, $ g_(ell)(r_ell) meq g(vec(r)) $)
  })
]
