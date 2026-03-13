#import "../00-lib/lib.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/polylux:0.4.0": *

#let hadamard = $dot.o$
#let graph-text-size = 18pt

#new-section[Spartan]

// ─────────────────────────────────────────────
// SubSection 1: R1CS
// ─────────────────────────────────────────────

#slide[
  = Rank-1 Constraint System

  Represent arithmetic circuit satisfiability with matrices:

  $ vec(A) vec(w) hadamard vec(B) vec(w) = vec(C) vec(w) $

  #show: later

  - $vec(w) in Fb^N$ — _witness_: inputs, outputs, intermediates
  - $vec(A), vec(B), vec(C) in Fb^(m times N)$ — sparse matrices encoding circuit structure

  #show: later

  De-facto _lingua franca_ for SNARK circuits
]

#slide[
  = R1CS Example: $y_1 = (w_1 + w_2) dot w_3$

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
      let add = (0.75, 0.5)
      node(shape: circle, add, $+$)
      edge(w1, (add.at(0), w1.at(1)), add, "->")
      edge(w2, (add.at(0), w2.at(1)), add, "->")

      // Layer 3
      let w1_plus_w2 = (1.5, 0.5)
      node(stroke: 0em, w1_plus_w2, $w_1 + w_2$)
      edge(add, w1_plus_w2, "-")

      // Layer 4
      let mult = (2.1, 1.25)
      node(shape: circle, mult, $times$)
      edge(w3, (mult.at(0), w3.at(1)), mult, "->")
      edge(w1_plus_w2, (mult.at(0), w1_plus_w2.at(1)), mult, "->")

      // Layer 5
      let res = (2.85, 1.25)
      node(stroke: 0em, res, $(w_1 + w_2) dot w_3$)
      edge(mult, res, "-")

      // Layer 6
      let out = (3.70, 1.25)
      node(shape: rect, out, $y_1$)
      edge(res, out, "->")
    })
  ])

  #show: later

  $ vec(w) = mat(1, w_1, w_2, w_3, y_1)^top $

  $
    vec(A) = mat(0, 1, 1, 0, 0), quad
    vec(B) = mat(0, 0, 0, 1, 0), quad
    vec(C) = mat(0, 0, 0, 0, 1)
  $

  $
    vec(C) vec(w) = vec(A) vec(w) hadamard vec(B) vec(w)
    ==> y_1 = (w_1 + w_2) dot w_3
  $
]

// ─────────────────────────────────────────────
// SubSection 2: Arithmetizing R1CS
// ─────────────────────────────────────────────

#slide[
  = Encoding as Functions over the Boolean Hypercube

  Simplify: $vec(A), vec(B), vec(C) in Fb^(m times m)$, $M in {A,B,C}$, $vec(w) in Fb^m$, $s := lg(m)$

  Represent as functions over the boolean hypercube:

  $
    forall vec(x), vec(y) in bits^s &: M(vec(x), vec(y)) &&= M_("toInt"(vec(x)), "toInt"(vec(y))) \
    forall vec(x) in bits^s        &: w(vec(x))          &&= w_("toInt"(vec(x)))
  $

  #show: later

  Define $F : bits^s -> Fb$ to check R1CS row by row:

  #text(size: 0.85em)[$
    F(vec(x)) = (sum_(vec(b) in bits^s) A(vec(x), vec(b)) dot w(vec(b))) dot
                (sum_(vec(b) in bits^s) B(vec(x), vec(b)) dot w(vec(b))) -
                sum_(vec(b) in bits^s) C(vec(x), vec(b)) dot w(vec(b))
  $]

  $ forall vec(b) in bits^s : F(vec(b)) meq 0 $
]

#slide[
  = Encoding as Polynomials

  Define the MLEs of $M in {A,B,C}$ and $w$:

  $
    tilde(M)(vec(x), vec(y)) &= sum_(vec(a), vec(b) in bits^s) M(vec(a), vec(b)) dot tilde("eq")(vec(x), vec(a)) dot tilde("eq")(vec(y), vec(b)) \
    tilde(w)(vec(x))         &= sum_(vec(b) in bits^s) w(vec(b)) dot tilde("eq")(vec(x), vec(b))
  $

  #show: later

  Lift $F$ to a polynomial $f$ over these MLEs:

  #text(size: 0.85em)[$
    f(vec(x)) = (sum_(vec(b)) tilde(A)(vec(x), vec(b)) dot tilde(w)(vec(b))) dot
                (sum_(vec(b)) tilde(B)(vec(x), vec(b)) dot tilde(w)(vec(b))) -
                sum_(vec(b)) tilde(C)(vec(x), vec(b)) dot tilde(w)(vec(b))
  $]
]

#slide[
  = R1CS Satisfiability via Zero Test

  $ "R1CS satisfied" <==> forall vec(b) in bits^s : f(vec(b)) = 0 $

  #show: later

  *Schwartz-Zippel?* Check $f(vec(gamma)) = 0$ for random $vec(gamma)$

  #show: later

  *Problem:* $f(vec(x))$ has _degree 2_ in each variable of $vec(x)$ and
  can vanish on all of $bits^s$ without being the zero polynomial!

  This would break completeness...

  #show: later

  *Fix:* use the _multilinear extension_ of $f$
]

#slide[
  = MLE of $f$

  Compute the multilinear extension of $f$:

  $ tilde(f)(vec(x)) = sum_(vec(b) in bits^s) tilde("eq")(vec(x), vec(b)) dot f(vec(b)) $

  #show: later

  From the definition of MLE, $forall vec(b) in bits^s : f(vec(b)) =
  tilde(f)(vec(b))$, and thus:

  $ forall vec(b) in bits^s : tilde(f) equiv 0 <==> f(vec(b)) = 0 <==> "R1CS satisfied" $

  #show: later

  Now we can apply Schwartz-Zippel:

  $ vec(gamma) inrand Fb^s : tilde(f)(vec(gamma)) = 0 ==> "R1CS satisfied" $

  *Goal:* use sumcheck to prove $tilde(f)(vec(gamma)) = sum_(vec(b) in bits^s) tilde("eq")(vec(x), vec(b)) dot f(vec(b)) = 0$
]

// ─────────────────────────────────────────────
// SubSection 3: Spartan Protocol
// ─────────────────────────────────────────────

#slide[
  = First Sumcheck

  Run sumcheck on the polynomial:

  $ g_1(vec(x)) = tilde("eq")(vec(gamma), vec(x)) dot f(vec(x)) $

  #show: later

  At the last round, verifier samples $vec(zeta) inrand Fb^s$ and needs:

  $
    g_1(vec(zeta)) &= tilde("eq")(vec(gamma), vec(zeta)) dot f(vec(zeta)) \
                   &= tilde("eq")(vec(gamma), vec(zeta)) dot (macron(A)(vec(zeta)) dot macron(B)(vec(zeta)) - macron(C)(vec(zeta)))
  $

  Where:

  $
    macron(A)(vec(x)) := sum_(vec(b) in bits^s) tilde(A)(vec(x), vec(b)) dot tilde(w)(vec(b)), #h(2em)
    macron(B)(vec(x)) := sum_(vec(b) in bits^s) tilde(B)(vec(x), vec(b)) dot tilde(w)(vec(b)) \
    macron(C)(vec(x)) := sum_(vec(b) in bits^s) tilde(C)(vec(x), vec(b)) dot tilde(w)(vec(b))
  $

  // $tilde("eq")(vec(gamma), vec(zeta))$ is computable in $O(s)$ — but what about $macron(A), macron(B), macron(C)$?
]

#slide[
  = Helper Polynomials $macron(A), macron(B), macron(C)$

  Prover simply sends claimed evaluations:

  $ v_macron(A) := macron(A)(vec(zeta)), quad v_macron(B) := macron(B)(vec(zeta)), quad v_macron(C) := macron(C)(vec(zeta)) $

  Verifier checks $g_1(vec(zeta)) meq tilde("eq")(vec(gamma), vec(zeta)) dot (v_macron(A) dot v_macron(B) - v_macron(C))$

  #show: later

  $$

  How does the verifier know that $v_macron(A), v_macron(B), v_macron(C)$ are valid?
]

// #slide[
//   = Linear-Time Prover for $g_1$

//   *Observation:* $forall vec(b) in bits^s : macron(M)(vec(b)) = (vec(M) vec(w))_("toInt"(vec(b)))$

//   #show: later

//   *Prover strategy:*
//   - Compute $vec(t)_M = vec(M) vec(w)$ — sparse matrix-vector product in $O(n)$
//   - Use $vec(t)_M$ as lookup table for $macron(M)$

//   #show: later

//   Build lookup tables $hat("eq")$ and $hat(t)_M$ via the linear-time techniques from GKR:

//   $
//     tilde(t)_M (vec(x)) = sum_(vec(b) in bits^s) tilde("eq")(vec(x), vec(b)) dot t_M (vec(b))
//   $

//   *Result:* $O(n + m)$ prover for the first sumcheck
// ]

#slide[
  = Second Sumcheck

  New problem... The verifier now needs to check the three claimed evaluations
  $v_macron(A), v_macron(B), v_macron(C)$

  #show: later

  *Reduce 3 claims to 1* using random $alpha inrand Fb$:

  #text(size: 0.85em)[$
    v_macron(A) + alpha dot v_macron(B) + alpha^2 dot v_macron(C) meq
    sum_(vec(b) in bits^s) (tilde(A)(vec(zeta), vec(b)) + alpha dot tilde(B)(vec(zeta), vec(b)) + alpha^2 dot tilde(C)(vec(zeta), vec(b))) dot tilde(w)(vec(b))
  $]

  #show: later

  Run sumcheck on:

  $ g_2(vec(x)) = (tilde(A)(vec(zeta), vec(x)) + alpha dot tilde(B)(vec(zeta), vec(x)) + alpha^2 dot tilde(C)(vec(zeta), vec(x))) dot tilde(w)(vec(x)) $
]

// #slide[
//   = Linear-Time Prover for $g_2$

//   Naive approach: build lookup table for $tilde(M)(vec(zeta), vec(x))$ over all $vec(x) in bits^s$ — costs $O(m^2)$

//   #show: later

//   *Exploit sparsity:* let $M_"nz" = {(v_i, r_i, c_i)}$ be the nonzero entries

//   $
//     tilde(M)(vec(zeta), vec(x)) = sum_(i) v_i dot tilde("eq")(vec(zeta), "toBits"(r_i)) dot tilde("eq")(vec(x), "toBits"(c_i))
//   $

//   #show: later

//   *Algorithm* — build lookup table $hat(M)_vec(zeta)$ in $O(n + m)$:

//   + Initialize array $vec(t)$ of size $m$ with zeros — $O(m)$
//   + $forall i : t[c_i] <- t[c_i] + v_i dot hat("eq")_vec(zeta)["toBits"(r_i)]$ — $O(n)$

//   *Result:* $O(n + m)$ prover for the second sumcheck
// ]

#slide[
  = Final Evaluation

  At the end of the second sumcheck, verifier samples $vec(eta) inrand Fb^s$ and needs:

  $
    g_2(vec(eta)) = (tilde(A)(vec(zeta), vec(eta)) + alpha dot tilde(B)(vec(zeta), vec(eta)) + alpha^2 dot tilde(C)(vec(zeta), vec(eta))) dot tilde(w)(vec(eta))
  $

  #show: later

  - $tilde(w)(vec(eta))$: evaluation of the _witness polynomial_ $-->$
    Regular polynomial commitment scheme

  - $tilde(A)(vec(zeta), vec(eta)), tilde(B)(vec(zeta), vec(eta)), tilde(C)(vec(zeta), vec(eta))$:
    evaluations of sparse matrix polynomials $-->$ _Sparse_ polynomial commitment scheme.
]

#slide[
  = Spartan: Summary

  Sumcheck on $g_1(vec(x))$ shows that $tilde(f) equiv 0 ==> "R1CS satisfied"$

  #show: later

  _Given that_ $v_macron(A) = macron(A)(vec(zeta)), v_macron(B) = macron(B)(vec(zeta)), v_macron(C) = macron(C)(vec(zeta))$...

  #show: later

  Which sumcheck on $g_2(vec(x))$ shows

  #show: later

  _Given that_ $tilde(A)(vec(zeta), vec(eta)), tilde(B)(vec(zeta), vec(eta)), tilde(C)(vec(zeta), vec(eta))$ are correct evaluations...
]

#slide[
  #show: focus
  Solved by Spark!
]
