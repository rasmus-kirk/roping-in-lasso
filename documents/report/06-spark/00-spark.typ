#import "../00-lib/header/lib.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/algo:0.3.6": algo, i, d, comment, code

#let Init = "Init"
#let WS = "WS"
#let RS = "RS"
#let Audit = "Audit"
#let mem = "mem"
#let row = "row"
#let col = "col"
#let eq = $tilde("eq")$
#let readTS = "read_ts"
#let writeTS = "write_ts"
#let auditTS = "audit_ts"
#let toBits = "toBits"
#let toInt = "toInt"
#let TODO = text(weight: "bold", size: 1.2em,  "TODO")
#let ts = $t s$

= Spark

We left off in the last section with an argument for R1CS based on sumcheck with
a linear prover. This is indeed Spartan, but we're still missing the core
contribution of Spartan, namely _Spark_. Spark solves our last problem, that
the verifier still needs the evaluations of $tilde(A), tilde(B), tilde(C)$
in the last round of the $g_2$ sumcheck. Of course, the verifier could do
this themselves, but this would take at least $O(n + m)$ time, making the
verifier linear. Another option is to use a PCS as described in @sec:pcs,
but any standard scheme would slow down the prover to at least $O(m^2)$
when doing an opening proof, since each of the matrix-polynomials is defined
over $m times m$ entries.

In Spark the prover only suffers a penalty of $O(n + m)$, meaning we get
the desired prover time. Note that committing to the matrices $tilde(A),
tilde(B), tilde(C)$ is a _preprocessing_ step (Section 6 of the Spartan
paper), while Spark itself (Section 7 of the Spartan paper) is the _runtime_
sparse polynomial commitment scheme that enables efficient evaluation at a
queried point. To see Spark's contribution, let's start by looking at the
multilinear extension of $M$:

$ tilde(M)(vec(zeta), vec(gamma)) = sum_(vec(a), vec(b) in bits^s) M(vec(a), vec(b)) dot tilde("eq")(vec(zeta), vec(a)) dot tilde("eq")(vec(gamma), vec(b)) $

This obviously cannot be represented as a sumcheck instance. We would need each
factor of each term in the sum to be a polynomial, and the multilinear
extension of $M$ is $tilde(M)$ itself. But, we can represent the evaluation
of $tilde(M)$ in its sparse form.

$ M_"nz" = { ("val"_1, "row"_1, "col"_1), ..., ("val"_n, "row"_n, "col"_n) } $

And model the evaluation of $tilde(M)$ with this form:

$
  tilde(M)(vec(zeta), vec(gamma)) &= sum_(vec(k) in bits^ceil(lg(n))) "val"(vec(k)) dot e_("row")(vec(k)) dot e_("col")(vec(k)) \
                                  &= sum_(vec(k) in bits^ceil(lg(n))) "val"(vec(k)) dot tilde("eq")(vec(zeta), "row"(vec(k))) dot tilde("eq")(vec(gamma), "col"(vec(k)))
$<eq:spark-sumcheck>

Where for all $i in [1, n]$:
- $"val"(toBits(i)) : bits^(ceil(lg(n))) -> Fb$ maps a bitstring to the value of the $i$'th nonzero entry of $M$.
- $"row"(toBits(i)) : bits^(ceil(lg(n))) -> bits^s$ maps a bitstring to the row index of the $i$'th nonzero entry of $M$.
- $"col"(toBits(i)) : bits^(ceil(lg(n))) -> bits^s$ maps a bitstring to the column index of the $i$'th nonzero entry of $M$.

#example-box(title: "Sparse Representation of a Small Matrix")[
  Consider the following small matrix:
  $ vec(A) = mat(
    0,7,0,6;
    5,0,0,4;
    0,3,2,0;
    0,0,1,0;
  ) $

  In its sparse form (with simplified function domains of $Fb -> Fb$):

  $
    A_"nz" &= { &&(7,1,2), &&(6,1,4), &&(5,2,1), &&(4,2,4), &&(3,3,2), &&(2,3,3), &&(1,4,3) }, \
    "val"  &= { &&1 -> 7,  &&2 -> 6,  &&3 -> 5,  &&4 -> 4,  &&5 -> 3,  &&6 -> 2,  &&7 -> 1 }, \
    "row"  &= { &&1 -> 1,  &&2 -> 1,  &&3 -> 2,  &&4 -> 2,  &&5 -> 3,  &&6 -> 3,  &&7 -> 4 }, \
    "col"  &= { &&1 -> 2,  &&2 -> 4,  &&3 -> 1,  &&4 -> 4,  &&5 -> 2,  &&6 -> 3,  &&7 -> 3 }, \
  $
]

In the preprocessing of the R1CS instance, a trusted party (sometimes the
verifier itself) computes a succinct representation of the R1CS instance. This
is how SNARKs are even able to achieve sublinear verification. A polynomial
commitment to $"val"$ can be computed at this stage, but notice that the other two
products of each term depend on the challenges $vec(zeta)$ and $vec(gamma)$.

If the prover could access a trusted RAM, consisting of all $m$ values of
$
  (tilde("eq")(vec(zeta), "row"("toBits"(1))), dots, tilde("eq")(vec(zeta), "row"("toBits"(m))) \
  (tilde("eq")(vec(gamma), "col"("toBits"(1))), dots, tilde("eq")(vec(gamma), "col"("toBits"(m)))
$

Then we _could_ perform sumcheck of the sum in @eq:spark-sumcheck. The next
section will introduce the concept of _offline memory checking_, which solves
this problem and lies at the heart of Spark. Offline memory checking also
serves as the backbone of Jolt, since when we need to model instruction sets,
we also need to handle reads and writes to registers. This document will
not cover Jolt, but understanding Jolt mostly boils down to understanding
Lasso and offline memory checking.

== Offline Memory Checking

Offline memory checking @blum1991checking allows a potentially malicious prover
($prover$) to control a RAM for the verifier to access. The verifier
($verifier$) can read and write to this RAM and verify that each read
accesses the last write performed on that address. We can model a RAM as
list of values:

$ vec("RAM") = [v_1, ..., v_m] $

We can include _timestamps_ in this list corresponding to the time that the
last write occurred at an address. The timestamp is a global monotonically
increasing counter, where each read or write operation increments it:

$ vec("RAM") = [(v_1, t_1), ..., (v_m, t_m)] $

Of course, it's equally valid to model this as a multi-set with an extra
tuple value indicating the address:

$ "RAM" = { (a_1, v_1, t_1), ..., (a_m, v_m, t_m) } = { (1, v_1, t_1), ..., (m, v_m, t_m) } $

This is what the untrusted RAM stores controlled by $prover$, $verifier$ can
then use the following algorithms to modify this untrusted ram by performing
reads or writes:

#figure(
  caption: [Verifier procedure for reading and writing to the untrusted RAM.],
  [
  #algo(
    title: "Read",
    parameters: ("a",),
    fill: theme.bg0.lighten(30%),
    block-align: left,
    strong-keywords: false,
    indent-guides: 1pt + theme.fg4,
  )[
    #let arrow_len = context $#h(measure($prover --> verifier$).width - measure($verifier$).width)$
    $prover --> verifier$: The verifier receives value $v_"read"$ and timestamp $t$ from the prover.\
    $#arrow_len verifier$: The verifier adds the tuple $(a, v_"read", t)$ to its local set $RS$.\
    $#arrow_len verifier$: The verifier updates its local timestamp counter, i.e. $ts_("new") <- max(ts, t) + 1$.\
    $#arrow_len verifier$: The verifier adds the new tuple $(a, v_"read", ts_("new"))$ to its local set $WS$.\
    $verifier --> prover$: The verifier sends $(a, v_"read", ts_("new"))$ back to the prover.\
  ]

  #algo(
    title: "Write",
    parameters: ("a, v",),
    fill: theme.bg0.lighten(30%),
    block-align: left,
    strong-keywords: false,
    indent-guides: 1pt + theme.fg4,
  )[
    #let arrow_len = context $#h(measure($prover --> verifier$).width - measure($verifier$).width)$
    $prover --> verifier$: The verifier receives value $v_("read")$ and timestamp $t$ from the prover.\
    $#arrow_len verifier$: The verifier adds the tuple $(a, v_("read"), t)$ to its local read set $RS$.\
    $#arrow_len verifier$: The verifier updates its local timestamp counter, i.e. $ts_("new") <- max(ts, t) + 1$.\
    $#arrow_len verifier$: The verifier adds the new tuple $(a, v, ts_("new"))$ to its local write set $WS$.\
    $verifier --> prover$: The verifier sends $(a, v, ts_("new"))$ back to the prover.\
  ]
])<fig:omc-verifier-procedure>

Here, $verifier$ locally stores and modifies the sets $WS, RS$. We
also denote the sets $Init, Audit$ which represents the initial writes and a
final read pass respectively, giving $verifier$ the following sets:

$
  &Init  &&= { (a, v_"initial", 0) }        &&#h(1em) "Represents the initial write of all values to the RAM." \
  &RS    &&= { (a, v_"read", t) }           &&#h(1em) "The Read Set; the tuples taken from RAM." \
  &WS    &&= { (a, v, ts_("new")) }         &&#h(1em) "The Write Set; the tuples put back into RAM." \
  &Audit &&= { (a, v_"final", t_"final") }  &&#h(1em) "A read pass on the final state of the RAM."
$

After performing the desired numbers of reads and writes, $verifier$ can
perform the following multiset equality check:

$ Init union WS meq RS union Audit $<eq:omc-set-check>

One way to view @eq:omc-set-check is as a coin-mint. Where each entry is a
"coin" and each time $verifier$ adds a tuple to $WS$ a coin is "minted"
and each time $verifier$ adds a tuple to $RS$ a coin is "spent".

#align(center)[
  #table(
    columns: 2,
    rows: 2,
    align: left,
    [$Init$: Initially minted coins],
    [$RS$: Spent coins],
    [$WS$: Minted coins throughout],
    [$Audit$: Unspent coins],
  )
]

By this logic, @eq:omc-set-check checks that, in total, each coin spent
(memory read) is exactly equal to each coin minted (memory written):

$ "Coins Spent" + "Coins Unspent" = "Coins Minted" $

And intuitively fake coins would not have a corresponding member in the
"Coins Minted" set. More formally, we state that following the protocol in
@eq:omc-set-check ensures _read-consistency_ with probability one.

#definition(title: "Read Consistency")[
  Any value read from the RAM will always be the most recently written value.
]<def:read-consistency>

#lemma[
  A verifier interacting with a potentially malicious prover that manages
  the RAM by leveraging the protocol above will have read-consistency with
  probability one.
]<lem:read-consistency>

#proof[
  Assume that for some read, $prover$ was able to convince $verifier$ that
  a wrong value was correctly read, i.e. the value at address $a$, was $v'$
  when it was actually $v$.

  There are only two cases in which the prover could cheat. They can either
  fabricate fake values that were never in the RAM to begin with, or they
  can try to convince the verifier a current value is a previous (but at
  the time, valid) value. These are the only two cases as we assume that
  as for any value, it must either have never been in the RAM (fake value)
  or it was previously valid.

  *Fake value case:* $prover$ sends $(v_"fake", t)$ in step one of
  the Read protocol. The verifier then adds $(a, v_"fake", t)$ to the $RS$
  set. But this value was never written to the set $WS$, so the check in
  @eq:omc-set-check will fail with probability one.

  *Previously valid value case:* $prover$ sends $(v_"old", t_"old")$
  in step one of the Read protocol. The verifier then adds $(a, v_"old",
  t_"old")$ to the $RS$ set. This means that $RS$ has two entries of $(a,
  v_"old", t_"old")$, but since timestamps are always increasing, $WS$ will
  only have a single entry. Thus the check in @eq:omc-set-check will fail
  with probability one.
]

The sets $WS, RS$ quickly grow to be potentially bigger than the size of
the RAM, which might make you wonder why this approach is viable at all. The
answer is that we can store these sets as a digest instead. Each time we add
to each set we append the element to the running hash and in the end of the
protocol we compare the digests rather than the multi-sets.

== Constructing a Sparse Polynomial Commitment Scheme

In Spark, we apply the offline memory-checking primitive in an alternative
way. Here, the prover itself is the one that reads a public read-only RAM,
and the prover wishes to convince the verifier that these reads were performed
correctly. Specifically, the algorithms in @fig:omc-verifier-procedure are
run by a trusted party and the resulting data is committed. Then the prover
wishes to prove to a verifier that @eq:omc-set-check passes.

To do this, we must first be able to prove the equality of multisets as
an argument. Furthermore, upon further inspection, you might notice that
each entry in the multisets are tuples, so we also need an argument for
proving tuple equality. The two lemmas below handle each of these cases:

#theorem[
  If a prover holds two n-length tuples and wishes to prove that they're equal:

  $
    vec(a) &= ( a_1, dots, a_n ) \
    vec(b) &= ( b_1, dots, b_n ) \
  $

  That is $forall i in [1..n] : f_i = g_i$, the prover can try to convince the verifier that:

  $
    sum^n_(i=1) alpha^(i-1) dot a_i meq sum^n_(i=1) alpha^(i-1) dot b_i
  $<eq:tuple-equality>

  For a uniformly random $alpha$ and with soundness bound $frac(style:
  "horizontal",  n, |Fb|)$ and completeness of one.
]<thm:tuple-equality-proof>

#proof[
  Completeness is trivial, as for soundness notice that each side in
  @eq:tuple-equality is a univariate polynomial evaluated at $alpha$ and with
  coefficients of $vec(a), vec(b)$ respectively. If the polynomials are
  equal, then the coefficients, which represent each element in the list,
  are equal. By Schwarz-Zippel, the probability of the check passing, given
  that the claim does not hold is $frac(style: "horizontal",  n, |Fb|)$.
]

#theorem[
  If a prover holds two multisets and wishes to prove that they're equal:

  $
    F &= { a_1, dots, a_n } \
    G &= { b_1, dots, b_n } \
  $

  That is that there exists some permutation, $pi$, s.t. $forall i in [1..n]
  : F_i = G_(pi(i))$. Let $tilde(f), tilde(g)$ be the multilinear extensions
  of $F, G$ respectively. The prover can try to convince the verifier that:

  $
    product_(vec(b) in bits^(ceil(lg(n)))) tilde(f)(vec(b)) - beta &meq product_(vec(b) in bits^(ceil(lg(n)))) tilde(g)(vec(b)) - beta
  $

  For a uniformly random $beta$ and with soundness bound $frac(style:
  "horizontal",  n, |Fb|)$ and completeness of one.
]<thm:multiset-equality-proof>

#proof[
  Completeness is trivial. As for soundness. We can interpret each side of
  the equality as a polynomial variable in $beta$:

  $
    p(X) &= product_(vec(b) in bits^(ceil(lg(n)))) tilde(f)(vec(b)) - X \
    q(X) &= product_(vec(b) in bits^(ceil(lg(n)))) tilde(g)(vec(b)) - X \
  $

  Then by Schwarz-Zippel, if we consider $e(X) = p(X) - q(X)$ then $e(beta)
  = 0$ implies that $p = q$ with probability $frac(style:"horizontal", n,
  |Fb|)$. Now, we just need to prove that $p = q ==> { a_1, dots,
  a_n } = { b_1, dots, b_n }$.

  Consider the roots of $p$ and $q$, starting with $p$:

  $ p(X) = product_((b_1, dots, b_n) in bits) tilde(f)(b_1, dots, b_n) - X $

  This polynomial evaluates to zero only if one of the factors equals
  $tilde(f)(vec(b))$, so the roots are:

  $
    "roots"(p) &= { &&tilde(f)(0, ..., 0), &&tilde(f)(0, ..., 1), &&#h(1em)dots,#h(1em) &&tilde(f)(1, ..., 1) &&} \
               &= { &&a_1,                 &&a_2,                 &&#h(1em)dots,#h(1em) &&a_n                 &&}, \
    "roots"(q) &= { &&tilde(g)(0, ..., 0), &&tilde(g)(0, ..., 1), &&#h(1em)dots,#h(1em) &&tilde(g)(1, ..., 1) &&} \
               &= { &&b_1,                 &&b_2,                 &&#h(1em)dots,#h(1em) &&b_n                 &&}
  $

  Since the two polynomials are equal, they must have the same roots. Thus:

  $
    "roots"(p) &= "roots"(q) ==> \
    { a_1, dots, a_n } &= { b_1, dots, b_n }
  $
]

Combining @thm:tuple-equality-proof and @thm:multiset-equality-proof a prover can prove that:

$ Init union WS meq RS union Audit $

With the verifier checking whether all the elements of the read set and all
the elements of the write set, are equal to some claimed value $h$:

$ h meq product_((a, v, t) in RS union Audit) (a + alpha v + alpha^2 t - beta) meq product_((a,v,t) in Init union WS) (a + alpha v + alpha^2 t - beta) $

Which is an excellent use-case for the specialized GKR protocol from
@sec:specialized-gkr, since it can efficiently prove the correctness of a
product of field elements.

== Putting the Pieces Together

One first thing notice before we start piecing together the puzzle is that our
RAM is read-only. This means that we don't need the "Write" algorithm from
@fig:omc-verifier-procedure and the $max(ts, t)$ will always be $ts$. This
further means that $writeTS = readTS + 1$ and we can avoid committing to it
entirely. With this in mind, we can start defining our multisets. For all
$i in [0, m-1]$ we let:

$
  &tilde("id")(toBits(i))      &&= i \
  &tilde("zero")(toBits(i))    &&= 0 \
  &tilde(col)(toBits(i))       &&= col_i \
  &tilde(row)(toBits(i))       &&= row_i \
  &tilde(mem)_(row)(toBits(i)) &&= eq_vec(gamma)(toBits(i)) \
  &tilde(mem)_(col)(toBits(i)) &&= eq_vec(zeta)(toBits(i)) \
$

And then define the multilinear extensions of $Init, RS, WS$ and
$Audit$, modeling these multisets using @thm:tuple-equality-proof and
@thm:multiset-equality-proof. Note that there are two RAMs here, for the rows:

$
  Init_(row)(vec(x))  &= tilde("id")(vec(x)) &&+ alpha dot tilde(mem)_(row)(vec(x)) &&+ alpha^2 dot tilde("zero")(vec(x)), \
  RS_(row)(vec(x))    &= tilde(row)(vec(x))  &&+ alpha dot e_(row)(vec(x))          &&+ alpha^2 dot tilde(readTS)_(row)(vec(x)), \
  WS_(row)(vec(x))    &= tilde(row)(vec(x))  &&+ alpha dot e_(row)(vec(x))          &&+ alpha^2 dot (tilde(readTS)_(row)(vec(x)) + 1), \
  Audit_(row)(vec(x)) &= tilde("id")(vec(x)) &&+ alpha dot tilde(mem)_(row)(vec(x)) &&+ alpha^2 dot tilde(auditTS)_(row)(vec(x)), \
$

And the columns:

$
  Init_(col)(vec(x))  &= tilde("id")(vec(x)) &&+ alpha dot tilde(mem)_(col)(vec(x)) &&+ alpha^2 dot tilde("zero")(vec(x)), \
  RS_(col)(vec(x))    &= tilde(col)(vec(x))  &&+ alpha dot e_(col)(vec(x))          &&+ alpha^2 dot tilde(readTS)_(col)(vec(x)), \
  WS_(col)(vec(x))    &= tilde(col)(vec(x))  &&+ alpha dot e_(col)(vec(x))          &&+ alpha^2 dot (tilde(readTS)_(col)(vec(x)) + 1), \
  Audit_(col)(vec(x)) &= tilde("id")(vec(x)) &&+ alpha dot tilde(mem)_(col)(vec(x)) &&+ alpha^2 dot tilde(auditTS)_(col)(vec(x)), \
$

Where $tilde(readTS)_row, tilde(auditTS)_row, tilde(readTS)_col$ and
$tilde(auditTS)_col$ are computed as in @fig:omc-verifier-procedure. Then,
we can use the specialized Grand Product GKR protocol of @sec:specialized-gkr
to verify each of the below grand products:

$
  "eval"_(WS)^((1)) &= product_(vec(b) in bits^ceil(lg(m))) Init_(row)(vec(b)),  #h(3em) &&"eval"_(WS)^((2)) &&= product_(vec(b) in bits^ceil(lg(n))) WS_(row)(vec(b)), \
  "eval"_(RS)^((1)) &= product_(vec(b) in bits^ceil(lg(m))) Audit_(row)(vec(b)), #h(3em) &&"eval"_(RS)^((2)) &&= product_(vec(b) in bits^ceil(lg(n))) RS_(row)(vec(b)), \
$

Which the verifier can use to check whether:

$ "eval"_(WS)^((1)) dot "eval"_(WS)^((2)) meq "eval"_(RS)^((1)) dot "eval"_(RS)^((2)) $

Thus, showing the correctness of the memory-checking. In the final round
of the grand product argument, the verifier will need to evaluate each of
these polynomials at a uniformly randomly chosen $vec(r)$. Taking
$Init_(row)(vec(x))$ as an example:

$ Init_(row)(vec(x)) &= tilde("id")(vec(x)) + alpha dot tilde(mem)_(row)(vec(x)) + alpha^2 dot tilde("zero")(vec(x)) $

We run the specialized GKR protocol over this polynomial, and at the end
of the protocol, the verifier needs to evaluate $Init_(row)$ at a randomly
sampled point $vec(r) inrand Fb$. All three polynomials $tilde("id"),
tilde(mem)_(row), tilde("zero")$ can be evaluated by the verifier on their
own in logarithmic time:

$ tilde(mem)_(row)(vec(r)) = eq_(vec(gamma))(vec(r)), #h(3em) tilde("zero")(vec(r)) = 0, #h(3em) tilde("id")(vec(r)) = sum_(j=1)^(lg(m)) r_j dot 2^(lg(m - j)) $

As for $tilde(row), tilde(col), tilde(readTS)_row, tilde(readTS)_col,
tilde(auditTS)_row$ and $tilde(auditTS)_col$, they have no structure to
exploit, so the verifier needs the prover to perform evaluation proofs on
them on behalf of the verifier. But, a trusted party makes the commitments,
so the verifier trusts that they are the right polynomials.

The remaining $e_col$ and $e_row$ polynomials are committed to by the prover
but the verifier need not check their structure! If the prover committed to
invalid polynomials here, it would be equivalent to breaking read-consistency,
which we proved was impossible in @lem:read-consistency#footnote[Technically
possible in our case since we prove the multi-set equality using interactive
arguments, but negligible.]
