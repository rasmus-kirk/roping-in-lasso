#import "../00-lib/lib.typ": *
#import "@preview/polylux:0.4.0": *

// ─────────────────────────────────────────────
// Section 1: Prover-Committed Spark
// ─────────────────────────────────────────────

#new-section[Lasso]

#slide[
  = Spark's Remaining Issue

  Spark assumed a *trusted party* commits to:

  $ tilde("val"), tilde("row"), tilde("col"), tilde("readTS")_"row", tilde("readTS")_"col", tilde("auditTS")_"row", tilde("auditTS")_"col" $

  Fine for Spartan, but not for a general-purpose sparse PCS

  #show: later

  *Goal:* let the *prover* commit to all of these

  #show: later

  *Obstacle:* if the prover controls the timestamps, can't they cheat the memory check?

  #show: later

  *Lasso's first result:* No, Spark is secure _even with prover-committed timestamps_.
]

#slide[
  = Read-Consistency with Local Counters

  *Proof sketch:* suppose an invalid read $(a, v^*, t) in "RS"$ with $v^* != "RAM"[a]$. It must appear in $Init union "WS"$:

  + *In $Init$:* impossible, $Init$ contains only $(a, "RAM"[a], 0)$

  + *In $"WS"$:* then a "parent" $(a, v^*, t-1) in "RS"$ must exist

  #show: later

  Going down the chain, $(a, v^*, 0)$ must appear in $Init$, but $v^* != "RAM"[a]$, thus we have a contradiction.
]

// ─────────────────────────────────────────────
// Section 2: The Lookup Argument
// ─────────────────────────────────────────────

// #new-section[The Lasso Lookup Argument]

#slide[
  = The Lookup Problem

  Prove a lookup into a table $hat(T)$ of size $N$ using memory-checking

  *Problem:* $N$ may be too large to instantiate or commit to

  #show: later

  *From Spark:* the $eq$ decomposition avoided a similar issue:

  $ eq(vec(x) || vec(y), row(vec(b)) || col(vec(b))) = eq(vec(x), row(vec(b))) dot eq(vec(y), col(vec(b))) $

  Two separate RAMs of size $m$ instead of one of size $m^2$

  #show: later

  *Lasso's insight:* this decomposability trick is broadly useful, many real tables decompose similarly
]

#slide[
  = Decomposable Tables

  *Idea:* split one large table into $c$ smaller sub-tables of size $N^(1/c)$:

  $ hat(T)[vec(b)] = g(hat(T)_1[overline(vec(b))_1], ..., hat(T)_c[overline(vec(b))_c]) $

  where $vec(b) = overline(vec(b))_1 || ... || overline(vec(b))_c$

  #show: later

  The sub-tables are small enough to instantiate and commit to concretely

  For Spark: $g$ is *multiplication*

  For other tables (e.g. range checks, bitwise ops): $g$ can be *bit-concatenation*:

  $ g(v_1, ..., v_c) = sum_(i=1)^c v_i dot 2^(w(c-i)) $
]

#slide[
  = Batching $k$ Lookups: Matrix-Vector Product

  To prove $k$ lookups at once, model them as a matrix-vector product:

  $ vec(M) vec(t) = vec(a) $

  - $vec(t) in Fb^N$: table values
  - $vec(a) in Fb^k$: lookup results
  - $vec(M) in bits^(k times N)$: one $1$ per row selecting the looked-up index

  #show: later

  In polynomial form, use Schwartz-Zippel on random $vec(r) inrand Fb^(lg(k))$:

  $
    tilde(a)(vec(r)) meq sum_(vec(b) in bits^(lg(k))) tilde(M)(vec(r), vec(b)) dot tilde(t)(vec(b))
  $
]

#slide[
  = Sparse Lookup Identity

  Since $vec(M)$ has exactly one nonzero per row, the sum simplifies:

  $
    tilde(a)(vec(r)) meq sum_(vec(b) in bits^(lg(k))) tilde("eq")(vec(r), vec(b)) dot hat(T)["nz"(vec(b))]
  $

  where $"nz"(vec(b))$ is the index accessed on lookup $vec(b)$

  #show: later

  Since $hat(T)$ is decomposable, replace $hat(T)["nz"(vec(b))]$ with $g$ applied to $c$ sub-table lookups
]

#slide[
  = The Lasso Sumcheck

  Let $tilde(e)_i(vec(x))$ be the MLE of the $k$ lookups into sub-table $hat(T)_i$

  Substituting the decomposition:

  $
    tilde(a)(vec(r)) = sum_(vec(b) in bits^(lg(k))) tilde("eq")(vec(r), vec(b)) dot g(tilde(e)_1(vec(b)), ..., tilde(e)_c(vec(b)))
  $

  #show: later

  Run sumcheck over this with polynomial:

  $ f_"Lasso"(vec(x)) := tilde("eq")(vec(r), vec(x)) dot g(tilde(e)_1(vec(x)), ..., tilde(e)_c(vec(x))) $

  #show: later

  Assuming each $tilde(e)_i$ is correct, this proves all $k$ lookups at once
]

#slide[
  = Verifying Each $tilde(e)_i$

  Each $tilde(e)_i$ must encode honest lookups into sub-table $hat(T)_i$

  #show: later

  *Use Spark!* For each sub-table $i in [c]$, the prover commits to:

  $
    tilde("nz")_i, quad tilde(e)_i, quad tilde("readTS")_i, quad tilde("auditTS")_i
  $

  and runs a memory-checking argument using the productcheck/grand-product GKR

  #show: later

  Sub-table $hat(T)_i$ is of size $N^(1/c)$, small enough to instantiate concretely

  $Init_i union "WS"_i meq "RS"_i union "Audit"_i$
]

// ─────────────────────────────────────────────
// Section 3: Efficiency
// ─────────────────────────────────────────────

#new-section[Efficiency]

#slide[
  = Prover Costs (Before Batching)

  #set text(size: 0.82em)
  #table(
    columns: (auto, auto, auto),
    stroke: none,
    table.header([*Operation*], [*Polynomials*], [*Cost each*]),
    table.hline(stroke: 0.5pt),
    [Commit], [$tilde("nz")_i, tilde(e)_i, tilde("readTS")_i$], [$O(c dot k)$],
    [Commit], [$tilde("auditTS")_i$], [$O(c dot N^(1/c))$],
    [Eval proof], [$tilde("nz")_i, tilde(e)_i, tilde("readTS")_i$], [$O(c dot k)$],
    [Eval proof], [$tilde("auditTS")_i$], [$O(c dot N^(1/c))$],
    [Productchecks], [$"RS"_i, "WS"_i$], [$O(c dot k)$],
    [Productchecks], [$"Init"_i, "Audit"_i$], [$O(c dot N^(1/c))$],
    [Sumcheck], [$f_"Lasso"$], [$O(c dot k)$],
  )

  #show: later

  After *batching* sumchecks, productchecks, and eval proofs:

  $ O(c dot k + c dot N^(1/c)) $

  Choose $c$ so that $N^(1/c) approx k$, cost scales with lookups $k$, not table size $N$
]

#slide[
  = Batching Techniques

  *Sumcheck batching:* combine $n$ sumchecks over the same domain with random $alpha$:

  $ sum_(i=1)^n alpha^(i-1) dot sigma_i meq sum_(vec(b)) sum_(i=1)^n alpha^(i-1) dot f_i(vec(b)) $

  #show: later

  *Eval proof batching:* with additively homomorphic commitments, batch $n$ openings at the same point:

  $
    q(vec(x)) = sum_(i=1)^n alpha^(i-1) dot f_i(vec(x)), quad
    "PCCheck"(C_q, d, vec(zeta), q(vec(zeta)), pi_q)
  $

  Reduces $O(n dot k)$ → $O(k)$, one opening proof for all
]

#slide[
  = Verifier Costs

  Let $lambda_k = lg^2(k) + lg(k)$ and $lambda_N = lg^2(N^(1/c)) + lg(N^(1/c))$

  After batching:

  $
    O(underbrace(lg(k) + lg(N^(1/c)), "eval proofs") + underbrace(lambda_k + lambda_N, "productchecks") + underbrace(c + lg(k), "sumcheck"))
  $

  *Polylogarithmic* in both $k$ and $N^(1/c)$, plus $O(c)$ for recomposition
]

// ─────────────────────────────────────────────
// Section 4: Soundness
// ─────────────────────────────────────────────

#slide[
  = Soundness

  Let $m = max(k, N^(1/c))$. By union bound:

  #table(
    columns: (auto, 1fr),
    stroke: none,
    table.header([*Sub-protocol*], [*Soundness error*]),
    table.hline(stroke: 0.5pt),
    [Sumcheck over $lg(k)$ vars],      [$O(lg(k) \/ |Fb|)$],
    [$4c$ productchecks],              [$O(c dot lg^2(m) \/ |Fb|)$],
    [Memory checking ($c$ sub-tables)],[$O(c dot m \/ |Fb|)$],
  )

  #show: later

  $
    delta_s <= O(frac(lg(k) + c dot lg^2(m) + c dot m, |Fb|))
  $

  Negligible for any cryptographically sized field
]

#slide[
  #show: focus
  Fin
]
