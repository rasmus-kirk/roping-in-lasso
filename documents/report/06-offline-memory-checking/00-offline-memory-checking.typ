#import "../00-lib/header/lib.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/algo:0.3.6": algo, i, d, comment, code

#let Init = "Init"
#let WS = "WS"
#let RS = "RS"
#let Audit = "Audit"
#let TODO = text(weight: "bold", size: 1.2em,  "TODO")
#let ts = $t s$

= Offline Memory-Checking

In offline-memory checking the goal is for a potentially malicious prover
($prover$) to control a RAM for the verifier to access. The verifier
($verifier$) can read and write to this RAM and verify that each read
accesses the last write performed on that address. We can model a RAM as
list of values:

$ vec("RAM") = [v_1, ..., v_m] $

We can include _timestamps_ in this list corresponding to the time that
the last write occurred at an address. Specifically, this represents the
number of times each address has been accessed:

$ vec("RAM") = [(v_1, t_1), ..., (v_m, t_m)] $

Of course, it's equally valid to model this as a multi-set with an extra
tuple value indicating the address:

$ "RAM" = { (a_1, v_1, t_1), ..., (a_m, v_m, t_m) } = { (1, v_1, t_1), ..., (n, v_m, t_m) } $

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

Here, $verifier$ keeps locally stores, and modifies, the sets $WS, RS$. We
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
    [$WS$: Minted coins throughout],
    [$RS$: Spent coins],
    [$Audit$: Unspent coins],
    [$Init$: Initially minted coins],
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
]

#lemma[
  A verifier interacting with a potentially malicious prover that manages
  the RAM by leveraging the protocol above will have read-consistency with
  probability one.
]

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
  set. But this value was never written to the set $WS$, so when the verifier
  makes the check in @eq:omc-set-check will fail with probability one.

  *Previously valid value case:* $prover$ sends $(v_"old", t_"old")$
  in step one of the Read protocol. The verifier then adds $(a, v_"old",
  t_"old")$ to the $RS$ set. This means that $RS$ has two entries of $(a,
  v_"old", t_"old")$, but since timestamps are always increasing, $WS$ will
  only have a single entry. Thus when the verifier makes the check in
  @eq:omc-set-check will fail with probability one.
]

The sets $WS, RS$ quickly grow to be potentially bigger than the size of
the RAM, which might make you wonder why this approach is viable at all. The
answer is that we can store these sets as a digest instead. Each time we add
to each set we append the element to the running hash and in the end of the
protocol we compare the digests rather than the multi-sets.

== Spark - Constructing a Sparse Polynomial Commitment Scheme

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
    product_(vec(b) in bits^n) tilde(f)(vec(b)) - beta &meq product_(vec(b) in bits^n) tilde(g)(vec(b)) - beta
  $

  For a uniformly random $beta$ and with soundness bound $frac(style:
  "horizontal",  n, |Fb|)$ and completeness of one.
]<thm:multiset-equality-proof>

#proof[
  Completeness is trivial. As for soundness. We can interpret each side of
  the equality as a polynomial variable in $beta$:

  $
    p(X) &= product_(vec(b) in bits^n) tilde(f)(vec(b)) - X \
    q(X) &= product_(vec(b) in bits^n) tilde(g)(vec(b)) - X \
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

$ h meq product_((a, v, t) in RS union Audit) a + alpha v + alpha^2 t meq product_((a,v,t) in Init union WS) a + alpha v + alpha^2 t $

Which is an excellent use-case for the specialized GKR protocol in
@sec:specialized-gkr.
