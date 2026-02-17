#import "../00-lib/header/lib.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/algo:0.3.6": algo, i, d, comment, code

= R1CS

A popular alternative to GKR's layered circuit representation is R1CS. This
proof system represents computation of an arithmetic circuit as a system of
linear constraints combined with a single multiplication per constraint:

$ vec(C) vec(w) &= vec(A) vec(w) hadamard vec(B) vec(w) $<eq:r1cs-claim>

Where $vec(w) in Fb^N$ is the witness vector containing all inputs, outputs,
and intermediate variables of the circuit and $vec(A), vec(B), vec(C) in
Fb^(M times N)$ are sparse matrices encoding the structure of the circuit.

Unlike GKR, which requires the circuit to be organized into layers of uniform
depth, R1CS allows for "flat" structures where any variable can interact
with any other. This has led to R1CS becoming a sort of _lingua franca_
for SNARK circuits the last decade or so.

#example(title: "A Small R1CS Circuit")[
  Consider the following example circuit, which computes $y_1 = (w_1 + w_2)
  dot w_3$:

  #align(center, [
    #diagram(debug: 0, node-stroke: 1pt, {
      // Layer 1
      let w1 = (0, 0)
      let w2 = (0, 1)
      let w3 = (0, 2)
      node(shape: rect, w1, [$w_1$])
      node(shape: rect, w2, [$w_2$])
      node(shape: rect, w3, [$w_3$])

      // Layer 2
      let add = (1, 0.5)
      node(shape: circle, add, $+$)
      edge(w1, (add.at(0), w1.at(1)), add, "->")
      edge(w2, (add.at(0), w2.at(1)), add, "->")

      // Layer 3
      let w1_plus_w2 = (2, 0.5)
      node(stroke: 0em, w1_plus_w2, $w_1 + w_2$)
      edge(add, w1_plus_w2, "-")

      // Layer 4
      let mult = (3, 1.25)
      node(shape: circle, mult, $times$)
      edge(w3, (mult.at(0), w3.at(1)), mult, "->")
      edge(w1_plus_w2, (mult.at(0), w1_plus_w2.at(1)), mult, "->")

      // Layer 5
      let res = (4, 1.25)
      node(stroke: 0em, res, $(w_1 + w_2) dot w_3$)
      edge(mult, res, "-")

      // Layer 6
      let out = (5, 1.25)
      node(shape: rect, out, $y_1$)
      edge(res, out, "->")
    })
  ])

  First, we define the witness vector $w$. It contains the constant $1$,
  the input variables, and the output variable:

  $ vec(w) = mat(1, w_1, w_2, w_3, y_1)^top $

  The constant one, is so that we may model constants in the circuit. Since
  there is only one multiplication gate in our example, the matrices will
  have only a single row.

  - *Matrix $vec(A)$ (Left Input):* Selects $w_1, w_2$. Note, addition does
    not grow the dimension of the matrices.
  - *Matrix $vec(B)$ (Right Input):* Selects $w_3$.
  - *Matrix $vec(C)$ (Output):* Selects $y_1$.

  $
    vec(A) = mat(0, 1, 1, 0, 0), quad
    vec(B) = mat(0, 0, 0, 1, 0), quad
    vec(C) = mat(0, 0, 0, 0, 1)
  $

  $ vec(A) vec(w) hadamard vec(B) vec(w) = vec(C) vec(w) $

  To verify, we take the dot product of the row with the witness:

  $

  vec(C) vec(w) &= vec(A) vec(w) hadamard vec(B) vec(w) ==> \ 
  underbrace( (0 + 0 + 0 + 0 + 1 dot y_1), "Output: " y_1 )
  &=
  underbrace( (0 dot 1 + 1 dot w_1 + 1 dot w_2 + 0 + 0), "Left Input: " (w_1 + w_2) )
  dot
  underbrace( (0 + 0 + 0 + 1 dot w_3 + 0), "Right Input: " w_3 ) ==> \
  y_1 &= w_1 + w_2 dot w_3
  $

  So to check whether the circuit is satisfied, the verifier can boil the
  check down to just $vec(C) vec(w) &= vec(A) vec(w) hadamard vec(B) vec(w)$.
]

== From Matrices to Polynomials (QAP)

Without loss of generality, we simplify the domain of $vec(A), vec(B), vec(C)$
to $Fb^(m times m)$ and $vec(w) in Fb^m$, then define $s := lg(m)$. To avoid
writing everything thrice we denote $vec(M) in {vec(A), vec(B), vec(C) }$. We
also define $"toBits"(x) : nats -> bits^(ceil(lg(x)))$ and $"toInt"(vec(x))
: bits^(|vec(x)|) -> nats$ representing the isomorphic functions between
the natural numbers and their corresponding bitstrings. We can naturally
express $vec(M), vec(w)$ as a functions:

$
  forall vec(x),vec(y) in bits^s &: M(vec(x), vec(y)) &&= M_("toInt"(vec(x)),"toInt"(vec(y))) \
  forall vec(x) in bits^s        &: w(vec(x))         &&= w_("toInt"(vec(x)))
$


We now define a helpful function $F : Bool^s -> Bool$ which can model whether
an R1CS instance is satisfied:

$ F(vec(x)) = (sum_(vec(b) in bits^s) A(vec(x), vec(b)) dot w(vec(b))) dot (sum_(vec(b) in bits^s) B(vec(x), vec(b)) dot w(vec(b))) - sum_(vec(b) in bits^s) C(vec(x), vec(b)) dot w(vec(b)) $

Since the R1CS instance will only be satisfied if and only if

$ forall vec(x) in bits^s : F(vec(x)) = 0 $<eq:r1cs-F-equals-zero>

#todo-box[
  Why?
]

We can of course also define the multilinear extensions of $A, B, C : Bool^s times Bool^s -> Bool, w : Bool^s -> Bool$ and model $F$ as a polynomial:

$
  tilde(M)(vec(x), vec(y)) &= sum_(vec(a) in bits^s) M(vec(a), vec(b)) dot tilde("eq")(vec(x), vec(a)) dot tilde("eq")(vec(y), vec(b)) \
  tilde(w)(vec(x))         &= sum_(vec(b) in bits^s) w(vec(b)) dot tilde("eq")(vec(x), vec(b)) \
  f(vec(x))                &= (sum_(vec(b) in bits^n) tilde(A)(vec(x), vec(b)) dot tilde(w)(vec(b))) dot (sum_(vec(b) in bits^n) tilde(C)(vec(x), vec(b)) dot tilde(w)(vec(b))) - sum_(vec(b) in bits^n) tilde(C)(vec(x), vec(b)) dot tilde(w)(vec(b))
$

Now, it may be tempting to simply run sumcheck over this polynomial to make
sure the sum equals zero:

$ 0 meq sum_(vec(b) in bits) f(vec(b)) $

But since the terms can cancel out that won't work. Instead, we can once
again make use of Schwartz-Zippel. Consider the following polynomial:

$ q(vec(x)) = sum_(vec(b) in bits^(s)) tilde("eq")(vec(x), vec(b)) dot f(vec(b)) $

Given @eq:r1cs-F-equals-zero holds then it will obviously be true that $forall
vec(x) in Bool^s : q(vec(x)) = 0$. Since $tilde("eq")(vec(x), vec(b)) = 1$
if and only if $vec(x) = vec(b)$, and zero otherwise, then $q$ must also
evaluate to zero outside the domain. From here we can evaluate this polynomial
at a random point, and by Schwartz-Zippel, if it evaluates to zero, the
claim will hold.

#todo-box[
  With what probibility?
]

== Our Old Friend Sumcheck

The above exposition established that if the prover succeeds in convincing
the verifier that the following equation holds:

$ sum_(vec(b) in bits^s) tilde("eq")(vec(gamma), vec(b)) dot f(vec(b)) meq 0 $<eq:spartan-sumcheck-one-raw>

Then, the verifier will now be convinced that @eq:r1cs-claim holds,
i.e. the circuit is satisfied. The prover can of course apply sumcheck to
@eq:spartan-sumcheck-one-raw in order to convince the verifier of this fact.
However, in the final round of the sumcheck, the verifier needs to compute
the evaluation of the sumcheck polynomial ($g_1$) at a uniformly random point
($zeta$), chosen by the verifier:

$ g_1(vec(zeta)) = tilde("eq")(vec(gamma), vec(zeta)) dot f(vec(zeta)) $<eq:spartan-sumcheck-one-poly>

The verifier can of course compute $tilde("eq")(vec(gamma), vec(zeta))$
on their own in time $O(m)$. As for $f(vec(zeta))$:

$ f(vec(zeta)) = (sum_(vec(b) in bits^s) tilde(A)(vec(zeta), vec(b)) dot tilde(w)(vec(b))) dot (sum_(vec(b) in bits^s) tilde(B)(vec(zeta), vec(b)) dot tilde(w)(vec(b))) - sum_(vec(b) in bits^s) tilde(C)(vec(zeta), vec(b)) dot tilde(w)(vec(b)) $

Which can be simplified to:

$ f(vec(zeta)) = macron(A)(vec(zeta)) dot macron(B)(vec(zeta)) - macron(C)(vec(zeta)) $

Using the following helper polynomials:

$
  macron(A)(vec(x)) := sum_(vec(b) in bits^s) tilde(A)(vec(x), vec(b)) dot tilde(w)(vec(b)), #h(3em)
  macron(B)(vec(x)) := sum_(vec(b) in bits^s) tilde(B)(vec(x), vec(b)) dot tilde(w)(vec(b)), #h(3em)
  macron(C)(vec(x)) := sum_(vec(b) in bits^s) tilde(C)(vec(x), vec(b)) dot tilde(w)(vec(b))
$<eq:macron-polys>

Now, an evaluation of $f$ simply boils down to evaluating these three
polynomials at the same point. We will use a trick to reduce these three
claims down to a single claim. But first, we'll show why this sumcheck will
also have a linear-time prover.

#theorem[
  A sumcheck performed on $g_1$ will have a linear-time prover running in
  time $O(n)$.
]
#proof[
  Compute $vec(t) = vec(M) vec(w)$ and as usual denote $forall vec(b) in Bool^s
  : t(vec(b)) = t_"toBits"(vec(b))$. Now, note that for all entries of each
  $macron(M) in { macron(A), macron(B), macron(C) }$:

  $ forall vec(b) in Bool^s : macron(M)(vec(b)) = t(vec(b)) $<eq:equality-between-macron-M-and-t>

  This means the prover can compute $vec(t)$ in time $O(n)$ and then:

  $ tilde(t)(vec(x)) = sum_(vec(b) in bits^lg(n)) tilde("eq")(vec(x), vec(b)) t(vec(b)) $

  Since @eq:equality-between-macron-M-and-t holds, then it must also be true
  that the polynomials $tilde(t)$ and $macron(M)$ are equal, i.e. $tilde(t)
  = macron(M)$. Since we can use $vec(t)$ as a lookup table, we can use
  techniques similar to the ones applied in @sec:computing-eq-linear
  and @sec:computing-w-linear, to compute lookup tables for $hat("eq")$
  and $hat(t)$ in time $O(n)$. This of course mean that we can compute
  lookup-tables for $macron(A), macron(B), macron(C)$, evaluate $g_1$ in
  constant time and have a prover runtime of $O(n)$ for the sumcheck.
]

In the final round, the verifier needs to evaluate $g_1(vec(zeta))
= tilde("eq")(vec(gamma), vec(zeta)) (v_macron(A) dot v_macron(B) -
v_macron(C))$, where the prover sends:

$
  v_macron(A) = macron(A)(vec(zeta), vec(b)), #h(3em)
  v_macron(B) = macron(B)(vec(zeta), vec(b)), #h(3em)
  v_macron(C) = macron(C)(vec(zeta), vec(b)) \
$

But the verifier then need to verify that these are defined as in
@eq:macron-polys. This can once again be boiled down to a sumcheck:
$
  v_macron(A) + alpha dot v_macron(B) + alpha^2 dot v_macron(C) &meq sum_(vec(b) in Bool^s) tilde(A)(vec(zeta), vec(b)) dot tilde(w)(vec(b)) + alpha dot tilde(B)(vec(zeta), vec(b)) dot tilde(w)(vec(b)) + alpha^2 dot tilde(C)(vec(zeta), vec(b)) dot tilde(w)(vec(b)) \
                                                                &meq sum_(vec(b) in Bool^s) ( tilde(A)(vec(zeta), vec(b)) + alpha dot tilde(B)(vec(zeta), vec(b)) + alpha^2 dot tilde(C)(vec(zeta), vec(b))) dot tilde(w)(vec(b))
$<eq:spartan-sumcheck-two-raw>

#todo-box[
  Create the theorem here that we can reduce three claims (three polynomials
  evaluated at the same point) to a single one. Ala the previous theorem
  for two evaluations of the same polynomial at two different points.
]

Applying sumcheck to @eq:spartan-sumcheck-two-raw yields our second sumcheck
polynomial:

$ g_2(vec(x)) = ( tilde(A)(vec(zeta), vec(x)) + alpha dot tilde(B)(vec(zeta), vec(x)) + alpha^2 dot tilde(C)(vec(zeta), vec(x))) dot tilde(w)(vec(x)) $<eq:spartan-sumcheck-two-poly>

#theorem[
  A sumcheck performed on $g_2$ will have a linear-time prover running in
  time $O(n)$.
]
#proof[
  To evaluate the sumcheck for $g_2(vec(x))$ efficiently, the prover must construct the
  evaluation form (lookup table) of the matrix polynomials inside the parenthesis
  ($tilde(M)(vec(zeta), vec(x))$).

  Naively computing the lookup table $hat(M)$ by iterating over all $2^s$ entries
  of the domain $bits^s$ for $vec(zeta)$ and $vec(x)$ would take $O((2^s)^2)$
  time. However, we can exploit the sparsity of the matrices. Let $S_M$ be
  the set of nonzero entries for a matrix $M$, defined as tuples $(v, c, r)$
  corresponding to value, column index, row index. The multilinear extension
  of a matrix $M$ with respect to a fixed $vec(zeta)$ can be rewritten as a
  sum over these sparse entries:

  $
    tilde(M)(vec(zeta), vec(b)) &= sum_(vec(a) in bits^s) M(vec(a), vec(b)) dot tilde("eq")(vec(zeta), vec(a)) \
                                &= sum_((v, c, r) in S_M : "toBits"(c) = vec(b)) "toBits"(v) dot tilde("eq")(vec(zeta), "toBits"(r))
  $

  Then, using this sparse representation, we can create the lookup table
  $hat(M)_vec(zeta)$ in $O(n + m)$ time using the algorithm below:

  #figure(
    [
    #algo(
      fill: theme.bg0.lighten(30%),
      block-align: left,
      strong-keywords: false,
      indent-guides: 1pt + theme.fg4,
    )[

    $O(m)$: Initialize an array $vec(t)$ of size $m$ with zeros.\
    $O(n)$: For each $(v, r, c) in S_M : t_c <- t_c + v dot hat("eq")_vec(zeta)["toBits"(r)]$. \
    The resulting array $vec(t)$ is exactly $hat(M)_vec(zeta)$.\
    ]
  ])

  By applying this algorithm to matrices $A, B$, and $C$, the prover computes
  $hat(A), hat(B), hat(C)$ in time $O(n + m)$ each. Since we have lookup tables
  for all terms in the sumcheck, we can once again apply the techniques from
  @sec:specialized-gkr to get a linear-time prover ($O(n + m)$).
]

While the prover can compute the sumcheck efficiently, a problem arises in the final
check. At the end of the sumcheck protocol for $g_2$, the verifier must evaluate
the sumcheck polynomial at a random point $vec(gamma)$:

$
  g_2(vec(gamma)) = (tilde(A)(vec(zeta), vec(gamma)) + alpha dot tilde(B)(vec(zeta), vec(gamma)) + alpha^2 dot tilde(C)(vec(zeta), vec(gamma))) dot tilde(w)(vec(gamma))
$

For the verifier to evaluate $tilde(A)(vec(zeta), vec(r))$ directly, they would
need to perform at least $O(n)$ work, destroying the succinctness of the verifier.
To resolve this, we need a mechanism that allows the prover to commit to the
nonzero entries of the matrices and prove the evaluation of sparse polynomials
without the verifier iterating over the entries. This mechanism is provided
by _Spark_.
