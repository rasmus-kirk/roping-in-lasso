#import "../00-lib/lib.typ": *
#import "@preview/polylux:0.4.0": *

// ─────────────────────────────────────────────
// Section 1: The Problem
// ─────────────────────────────────────────────

#new-section[Spark]

#slide[
  = The Problem Left by Spartan

  At the end of $g_2$ sumcheck, verifier needs:

  $
    tilde(A)(vec(zeta), vec(eta)), quad
    tilde(B)(vec(zeta), vec(eta)), quad
    tilde(C)(vec(zeta), vec(eta))
  $

  #show: later

  *Ideas:*

  - Iterate over $m^2$ entries? ($O(m^2)$)
  - Iterate only over nonzero entries? ($O(n)$)
  - Standard PCS opening proof? $O(m^2)$ prover time

  #show: later

  *Goal:* a _sparse_ polynomial commitment scheme with $O(n + m)$ prover
]

#slide[
  = Sparse Evaluation as a Sum

  Use the nonzero representation $M_"nz" = {("val"_i, "row"_i, "col"_i)}$:

  $
    tilde(M)(vec(zeta), vec(eta))
      = sum_(vec(k) in bits^(ceil(lg(n))))
        underbrace("val"(vec(k)), v_i)
        dot underbrace(tilde("eq")(vec(zeta), "row"(vec(k))), e_("row")(vec(k)))
        dot underbrace(tilde("eq")(vec(eta), "col"(vec(k))), e_("col")(vec(k)))
  $

  #show: later

  This _is_ a sumcheck, but the prover must provide honest $e_"row", e_"col"$ polynomials

  #show: later

  *Idea:* model $e_"row"$ and $e_"col"$ as reads from a trusted RAM
]

// ─────────────────────────────────────────────
// Section 2: Offline Memory Checking
// ─────────────────────────────────────────────

// #new-section[Offline Memory Checking]

#slide[
  #show: focus
  Offline Memory Checking
]

#slide[
  = Offline Memory Checking

  RAM as a set of _(address, value, timestamp)_ tuples:

  $ "RAM" = { (1, v_1, t_1), ..., (m, v_m, t_m) } $

  #show: later

  - $prover$ controls the RAM
  - $verifier$ reads and writes via protocols, with local sets $WS, RS$ and a timestamp $ts$

  #pseudocode(title: "Read", args: ($a$,), [
    #let arrow_len = context $#h(measure($prover --> verifier$).width - measure($verifier$).width)$
    + $prover --> verifier$: $verifier$ receives $v_"read"$ and timestamp $t$ from $prover$.\
    + $#arrow_len verifier$: $verifier$ adds the tuple $(a, v_"read", t)$ to its local set $RS$.\
    + $#arrow_len verifier$: $verifier$ updates $ts_("new") <- max(ts, t) + 1$.\
    + $#arrow_len verifier$: $verifier$ adds new tuple $(a, v_"read", ts_("new"))$ to $WS$.\
    + $verifier --> prover$: $verifier$ sends $(a, v_"read", ts_("new"))$ back to $prover$.\
  ])
]

#slide[
  = The Four Sets

  $
    &Init  &&= { (a, v_"initial", 0) }        &&#h(1em) "Initial write of all values to the RAM." \
    &RS    &&= { (a, v_"read", t) }           &&#h(1em) "The tuples taken from RAM." \
    &WS    &&= { (a, v, ts_("new")) }         &&#h(1em) "The tuples put back into RAM." \
    &Audit &&= { (a, v_"final", t_"final") }  &&#h(1em) "Read pass on final state of the RAM."
  $

  #show: later

  *Verifying check:*

  $ Init union WS meq RS union Audit $

  #show: later

  Think of it as a _coin mint_:
  - $Init, WS$: minted coins
  - $RS, Audit$: spent / unspent coins
  - Check that every coin spent was once minted
]

#slide[
  = Read Consistency

  If the check $Init union WS = RS union Audit$ passes, the RAM is _read-consistent_: every read returns the most recently written value

  #show: later

  *Why?* Only two ways a prover could cheat:

  + *Fake value:* $(a, v_"fake", t)$ added to $RS$, but never in $WS$.
  + *Old value:* $(a, v_"old", t_"old")$ added to $RS$ twice, but $WS$ has it only once.

  #show: later

  *In practice:* store sets as running hash digests
]

// ─────────────────────────────────────────────
// Section 3: Proving Multiset Equality
// ─────────────────────────────────────────────

// #new-section[Proving Multiset Equality]

// #slide[
//   = Tuple Equality

//   *Lemma:* to prove $vec(a) = vec(b)$ (element-wise), check for random $alpha inrand Fb$:

//   $ sum^n_(i=1) alpha^(i-1) dot a_i meq sum^n_(i=1) alpha^(i-1) dot b_i $

//   Soundness error: $frac(n-1, |Fb|)$

//   #show: later

//   *Proof:* each side is a degree-$n$ univariate polynomial in $alpha$ with coefficients $vec(a)$ resp. $vec(b)$. If they differ, Schwartz-Zippel bounds the collision probability.
// ]

// #slide[
//   = Multiset Equality

//   *Lemma:* to prove $F = G$ as multisets, check for random $beta inrand Fb$:

//   $
//     product_(vec(b) in bits^(ceil(lg(n)))) tilde(f)(vec(b)) - beta
//     meq
//     product_(vec(b) in bits^(ceil(lg(n)))) tilde(g)(vec(b)) - beta
//   $

//   Soundness error: $frac(n-1, |Fb|)$

//   #show: later

//   *Proof:* both sides are univariate polynomials in $beta$ whose roots are the elements of $F$ resp. $G$. Equal polynomials $==>$ equal multisets.

//   #show: later

//   *Excellent use-case for the specialized GKR grand product!*
// ]

// ─────────────────────────────────────────────
// Section 4: Spark Construction
// ─────────────────────────────────────────────

// #new-section[Spark Construction]

#slide[
  #show: focus
  Back to Spark
]

#slide[
  = Counters

  In Spark the RAM is _read-only_, the prover reads, a trusted party wrote

  #show: later

  *Simplification:* replace global timestamps with _per-address counters_

  - $"writeTS" = "readTS" + 1$ no need to commit to $"writeTS"$
]

// #slide[
//   = Proving $Init union WS = RS union Audit$

//   In a SNARK context we use polynomials...
  
//   Use the productcheck to check:

//   $
//     &h meq product_((a, v, t) in RS union Audit) (a + alpha v + alpha^2 t - beta) \
//     &h meq product_((a, v, t) in Init union WS)  (a + alpha v + alpha^2 t - beta)
//   $
// ]


#slide[
  = RAM Polynomials

  $forall i in [0, m-1], j in [0, n-1]$ define $vec(i) = toBits(i), vec(j) = toBits(j)$:

  $
    tilde(id)(vec(i))        &= i                              quad &&tilde("zero")(vec(i))        &&= 0 \
    tilde(mem)_(row)(vec(i)) &= tilde("eq")(vec(zeta), vec(i)) quad &&tilde("mem")_("col")(vec(i)) &&= tilde("eq")(vec(eta),  vec(i)) \
    tilde("row")(vec(j))     &= "row"_j,                       quad &&tilde("col")(vec(j))         &&= "col"_j
  $

  #show: later

  Then:

  $
    Init_(row)(vec(x))  &= tilde("id")(vec(x)) &&+ alpha dot tilde("mem")_(row)(vec(x)) &&+ alpha^2 dot tilde("zero")(vec(x)) - beta \
    RS_(row)(vec(x))    &= tilde(row)(vec(x))  &&+ alpha dot e_(row)(vec(x))            &&+ alpha^2 dot tilde("readTS")_(row)(vec(x)) - beta \
    WS_(row)(vec(x))    &= tilde(row)(vec(x))  &&+ alpha dot e_(row)(vec(x))            &&+ alpha^2 dot (tilde("readTS")_(row)(vec(x)) + 1) - beta \
    Audit_(row)(vec(x)) &= tilde("id")(vec(x)) &&+ alpha dot tilde("mem")_(row)(vec(x)) &&+ alpha^2 dot tilde("auditTS")_(row)(vec(x)) - beta
  $
]

#slide[
  = Memory Check

  Productcheck (same for column RAM):

  $
    h &meq product_(vec(b) in bits^(ceil(lg(m)))) Init_(row)(vec(b))  &&dot product_(vec(b) in bits^(ceil(lg(n)))) WS_(row)(vec(b)) \
    h &meq product_(vec(b) in bits^(ceil(lg(m)))) Audit_(row)(vec(b)) &&dot product_(vec(b) in bits^(ceil(lg(n)))) RS_(row)(vec(b))
  $
]

// #slide[
//   = Final Evaluation in the Grand Product

//   At the end of the grand product argument, verifier evaluates at random $vec(r)$

//   *Verifier can compute in $O(lg(m))$:*
//   $
//     tilde("mem")_"row"(vec(r)) &= tilde("eq")_(vec(zeta))(vec(r)) \
//     tilde("zero")(vec(r))       &= 0 \
//     tilde("id")(vec(r))         &= sum_(j=1)^(lg(m)) r_j dot 2^(lg(m) - j)
//   $

//   #show: later

//   *Prover provides PCS openings for:*
//   - $tilde("row")(vec(r)), tilde("col")(vec(r))$ — committed during setup
//   - $tilde("readTS")_"row"(vec(r)), tilde("readTS")_"col"(vec(r))$ — committed during setup
//   - $tilde("auditTS")_"row"(vec(r)), tilde("auditTS")_"col"(vec(r))$ — committed during setup
//   - $e_"row"(vec(r)), e_"col"(vec(r))$ — committed during open (prover is trusted via OMC)
// ]

// #slide[
//   = Spark: Summary

//   #set text(size: 0.9em)

//   #table(
//     columns: (auto, 1fr),
//     stroke: none,
//     table.header([*Component*], [*Role*]),
//     table.hline(stroke: 0.5pt),
//     [Sparse sum], [Express $tilde(M)(vec(zeta), vec(eta))$ as sumcheck over $n$ terms],
//     [OMC],        [Prove prover used the RAM honestly],
//     [Grand product], [Prove multiset equality ($Init union WS = RS union Audit$)],
//     [Dense PCS],  [Open committed polynomials $tilde("val"), tilde("row"), tilde("col"), ...$],
//     [Sumcheck],   [Reduce to evaluations of $tilde("val"), tilde(e)_"row", tilde(e)_"col"$],
//   )

//   #show: later

//   *End-to-end prover cost: $O(n + m)$*

//   Looking up memory cells $->$ Lookup Argument #emoji.face.think Lasso next!
// ]

// #slide[
//   #show: focus
//   Lasso
// ]
