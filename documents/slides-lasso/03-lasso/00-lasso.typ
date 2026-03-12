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

  Fine for Spartan — but not for a general-purpose sparse PCS

  #show: later

  *Goal:* let the *prover* commit to all of these

  #show: later

  *Obstacle:* if the prover controls the timestamps, can they cheat the memory check?

  #show: later

  *Lasso's first result:* No — Spark is secure with prover-committed timestamps
]

#slide[
  = Read-Consistency with Local Counters

  *Theorem:* using local per-address counters and $"WS" = {(a,v,t+1) mid (a,v,t) in "RS"}$, the multiset equality check $Init union "WS" = "RS" union "Audit"$ enforces read-consistency with probability one

  #show: later

  *Proof sketch* — suppose an invalid read $(a, v^*, t) in "RS"$ with $v^* != "RAM"[a]$. It must appear in $Init union "WS"$:

  + *In $Init$:* impossible — $Init$ contains $(a, "RAM"[a], 0)$ only

  + *In $"WS"$:* then a "parent" $(a, v^*, t-1) in "RS"$ must exist

  #show: later

  Chasing the chain down: $(a, v^*, 0)$ must appear in $Init$, but $v^* != "RAM"[a]$ — contradiction
]

// ─────────────────────────────────────────────
// Section 2: The Lookup Argument
// ─────────────────────────────────────────────

#new-section[The Lasso Lookup Argument]

#slide[
  = Lookup as Matrix-Vector Product

  $k$ lookups into a table $hat(T)$ of size $N$:

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

  *Problem:* $hat(T)$ may be astronomically large — e.g. $2^128$ for 64-bit XOR

  We cannot instantiate or commit to such a table

  #show: later

  *Lasso's insight:* many useful tables are _decomposable_
]

#slide[
  = Decomposable Tables

  *Idea:* split one large table into $c$ smaller sub-tables of size $N^(1/c)$:

  $ hat(T)[vec(b)] = g(hat(T)_1[overline(vec(b))_1], ..., hat(T)_c[overline(vec(b))_c]) $

  where $vec(b) = overline(vec(b))_1 || ... || overline(vec(b))_c$

  #show: later

  *Example:* 64-bit XOR with table size $2^128$
  - Split into $c = 8$ sub-tables of size $2^16$
  - $g$ = bit-concatenation: $sum_(i=1)^c v_i dot 2^(w(c-i))$, window $w = 16$

  $
    #text(size: 0.75em)[$"XOR"("0100_0001", "0010_0000")$]
    = hat("XOR")_2(01_2, 00_2) || hat("XOR")_2(00_2, 10_2) || hat("XOR")_2(00_2, 00_2) || hat("XOR")_2(01_2, 00_2)
    = 01_2 || 10_2 || 00_2 || 01_2
  $

  #show: later

  For $eq$: decomposition uses *multiplication* — this is precisely what enabled Spark!
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

  Sub-table $hat(T)_i$ is of size $N^(1/c)$ — small enough to instantiate concretely

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

  Choose $c$ so that $N^(1/c) approx k$ — cost scales with lookups $k$, not table size $N$
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

  Reduces $O(n dot k)$ → $O(k)$ — one opening proof for all
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
