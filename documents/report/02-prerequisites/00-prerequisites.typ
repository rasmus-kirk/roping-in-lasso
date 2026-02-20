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

== Proof Systems

An Interactive Proof System consists of two Interactive Turing Machines:
a computationally unbounded Prover, $prover$, and a polynomial-time bounded
Verifier, $verifier$. The Prover tries to convince the Verifier of a statement
$X in L$, with language $L$ in NP. The following properties must be true:

- *Completeness:* $forall prover in "ITM", X in L ==> Pr[verifier_"out" = bot] <= epsilon(X)$

  For all honest provers, $prover$, where $X$ is true, the probability that the
  verifier remains unconvinced ($verifier_("out") = bot$) is negligible in the
  length of $X$.

- *Soundness:* $forall prover^* in "ITM", X not in L ==> Pr[verifier_"out" = top] <= epsilon(X)$

  For all provers, honest or otherwise, $prover^*$, that try to convince the
  verifier of a claim, $X$, that is not true, the probability that the verifier
  will be convinced ($verifier_"out" = top$) is negligible in the length of $X$.

An Interactive Argument is similar, but the honest and malicious prover
are now polynomially bounded and receive a Private Auxiliary Input, $w$,
not known by $verifier$. This is such that $verifier$ can't just compute the answer
themselves. Definitions follow:

- *Completeness*: $forall prover(w) in "PPT", X in L ==> Pr[verifier_"out" = bot] <= epsilon(X)$
- *Soundness*: $forall prover^* in "PPT", X not in L ==> Pr[verifier_"out" = top] <= epsilon(X)$

Proofs of knowledge are another type of Proof System, here the prover claims
to know a _witness_, $w$, for a statement $X$. Let $X in L$ and $W(X)$ be the
set of witnesses for $X$ that should be accepted in the proof. This allows
us to define the following relation: $Rc = { (X,w) : X in L , w in W(X) }$

A proof of knowledge for relation $Rc$ is a two party protocol $(prover, verifier)$
with the following two properties:

- *Knowledge Completeness:* $Pr[prover(w) iff verifier_"out" = top] = 1$, i.e. as in
  Interactive Proof Systems, after an interaction between the prover and
  verifier the verifier should be convinced with certainty.  
- *Knowledge Soundness:* Loosely speaking, Knowledge Soundness requires
  the existence of an efficient extractor $Ec$ that, when given a possibly
  malicious prover $prover^*$ as input, can extract a valid witness with
  probability at least as high as the probability that $prover^*$ convinces the
  verifier $verifier$.

The above proof systems may be _zero-knowledge_, which in loose terms means
that anyone looking at the transcript, that is the interaction between
prover and verifier, will not be able to tell the difference between a real
transcript and one that is simulated. This ensures that an adversary gains
no new information beyond what they could have computed on their own. We
now define the property more formally:

- *Zero-knowledge:* $forall verifier^*(delta). exists S_(verifier^*)(X) in "PPT". S_(verifier^*) tilde^C (prover,verifier^*)$

$verifier^*$ denotes a verifier, honest or otherwise, $delta$ represents
information that $verifier^*$ may have from previous executions of the protocol
and $(prover,verifier^*)$ denotes the transcript between the honest prover
and (possibly) malicious verifier. There are three kinds of zero-knowledge:

- *Perfect Zero-knowledge:* $forall verifier^*(delta). exists S_(verifier^*)(X) in "PPT". S_(verifier^*) tilde^prover (prover,verifier^*)$,
  the transcripts $S_(verifier^*)(X)$ and $(prover,verifier^*)$ are perfectly indistinguishable.
- *Statistical Zero-knowledge:* $forall verifier^*(delta). exists S_(verifier^*)(X) in "PPT". S_(verifier^*) tilde^S (prover,verifier^*)$,
  the transcripts $S_(verifier^*)(X)$ and $(prover,verifier^*)$ are statistically indistinguishable.
- *Computational Zero-knowledge:* $forall verifier^*(delta). exists S_(verifier^*)(X) in "PPT". S_(verifier^*) tilde^C (prover,verifier^*)$,
  the transcripts $S_(verifier^*)(X)$ and $(prover,verifier^*)$ are computationally
  indistinguishable, i.e. no polynomially bounded adversary $Ac$ can
  distinguish them.

Where two distributions $D_1, D_2$ are:

- _Perfectly indistinguishable_ if they are identical, meaning no observer can tell them apart:
  $ forall x : Pr[D_1 = x] = Pr[D_2 = x] $
- _Statistically indistinguishable_ if their statistical distance is negligible,
  meaning that they may differ, but the difference is vanishingly small,
  even for an unbounded adversary:
  $ forall x : Delta(D_1, D_2) := frac(1,2) sum_x abs(Pr[D_1 = x] - Pr[D_2 = x]) <= "negl"(lambda) $
- _Computationally indistinguishable_ if no probabilistic polynomial-time
  distinguisher $Ac$ can tell them apart with more than negligible advantage,
  though an unbounded adversary might:
  $ forall x : abs(Pr[Ac(x) -> D_1] - Pr[Ac(x) = D_2]) <= "negl"(lambda) $

== SNARKS

#let SNARKProver = smallcaps("SNARKProver")
#let SNARKVerifier = smallcaps("SNARKVerifier")

SNARKs - Succinct Noninteractive Arguments of Knowledge - have seen increased
usage due to their application in blockchains and cryptocurrencies. They
also typically function as general-purpose proof schemes. This means that,
given any solution to an NP-problem, the SNARK prover will produce a proof
that they know the solution to said NP-problem. Most SNARKs also allow for
zero-knowledge arguments, making them zk-SNARKs.

More concretely, imagine that Alice has today's Sudoku problem $X in
"NP"$: She claims to have a solution to this problem, her witness, $w$,
and wants to convince Bob without having to reveal the entire solution. She
could then use a SNARK to generate a proof for Bob. To do this she must
first encode the Sudoku verifier as a circuit $R_X$, then let $x$ represent
public inputs to the circuit, such as today's Sudoku values/positions, etc,
and then give the SNARK prover the public inputs and her witness, $pi =
SNARKProver(R_X, x, w)$. Finally she sends this proof, $pi$, to Bob along
with the public Sudoku verifying circuit, $R_X$, and he can check the proof
and be convinced using the SNARK verifier ($SNARKVerifier(R_X, x, pi)$).

== Commitment Schemes

#let CMCommit = smallcaps("CMCommit")

A commitment scheme is a cryptographic primitive that allows one to commit
to a chosen value while keeping it hidden to others, with the ability to
reveal the committed value later. Commitment schemes are designed so that
the committing party cannot change the value after they have committed to
it, i.e. it is _binding_. The fact that anyone that receives the commitment
cannot compute the value from the it is called _hiding_. For $C = CMCommit(m)$

- *Perfect Hiding:* Given $C$, it is impossible to determine $m$, no matter your computational power.
- *Computational Hiding:* It is computationally infeasible to determine the value committed, from the commitment.
- *Perfect Binding:* It is impossible to change the value committed to, no matter your computational power.
- *Computational Binding:* It is computationally infeasible to change the value committed to.

To reveal a value one can simply send the value to a party that previously
received the commitment, and the receiving party can compute the commitment
themselves and compare to the previously received commitment.

Pedersen commitments@pedersen are an instance of a highly useful type of commitment
scheme for proof systems is that of a _homomorphic commitment scheme_, where:

$
  CMCommit(m_1) + CMCommit(m_2) = CMCommit(m_1 + m_2)
$

That is, you can add the commitments which corresponds to adding the committed
inputs and then committing.

== Polynomial Commitment Schemes <sec:pcs>

// --- Definitions ---
#let poly = math.op("poly")
#let negl = math.op("negl")
#let PC = "PC"
#let PCCheck = smallcaps("PCCheck")
#let PCSetup = smallcaps("PCSetup")
#let PCCommit = smallcaps("PCCommit")
#let PCOpen = smallcaps("PCOpen")
#let EvalProof = $bold(#smallcaps("EvalProof"))$
#let Instance = $bold(#smallcaps("Instance"))$
#let ppPC = $"pp"_"PC"$
#let prob-game(left, right, end) = {
  $ Pr [
    #grid(
      columns: 2,
      column-gutter: 0.8em,
      stroke: (x, y) => if x == 0 { (right: 0.5pt) },
      inset: 0.4em,
      // align: (center + horizon, left + horizon),
      left,
      right
    )
  ] #end $
}

In the SNARK section, general-purpose proof schemes were described. Modern
general-purpose (zero-knowledge) proof schemes, such as Sonic@sonic,
Plonk@plonk, Marlin@marlin and of course Spartan@spartan, commonly use
_Polynomial Commitment Schemes_ (PCSs) for creating their proofs. This means
that different PCSs can be used to get security under weaker or stronger
assumptions.

- *KZG PCSs:* Uses a trusted setup, which involves generating a Structured
  Reference String for the KZG commitment scheme@kzg. This would give you
  a traditional SNARK.
- *Bulletproofs PCSs:* Uses an untrusted setup, assumed secure if the
  Discrete Log problem is hard, the verifier is linear.
- *FRI PCSs:* Also uses an untrusted setup, assumes secure one way functions
  exist. It has a higher constant overhead than PCSs based on the Discrete
  Log assumption, but because it instead assumes that secure one-way functions
  exist, you end up with a quantum secure PCS.

A PCS allows a prover to prove to a verifier that a committed polynomial
evaluates to a certain value, $v$, given an evaluation input $z$. There
are five main functions used to prove this:

- $PCSetup(lambda, D)^rho -> ppPC$

  The setup routine. Given security parameter $lambda$ in unary and a maximum
  degree bound $D$. Creates the public parameters $ppPC$.

- $PCCommit(p in Fb^(d')[X], d in Nb) -> Eb(Fb)$

  Commits to a degree-$d'$ polynomial $p$ with degree bound $d$ where $d'
  <= d$.

- $PCOpen^(rho)(p in Fb^(d')[X], C in Eb(Fb), d in Nb, z in Fb) -> EvalProof$

  Creates a proof, $pi in EvalProof$, that the degree $d'$ polynomial $p$,
  with commitment $C$, and degree bound $d$ where $d' <= d$, evaluated at
  $z$ gives $v = p(z)$.

- $PCCheck^(rho)(C in Eb(Fb), d in Nb, z in Fb, v in Fb, pi in EvalProof) -> bits$

  Checks the proof $pi$ that claims that the degree $d'$ polynomial $p$,
  with commitment $C$, and degree bound $d$ where $d' <= d$, evaluates to
  $v = p(z)$.

Any NP-problem, $X in "NP"$, with a witness $w$ can be compiled into a
circuit $R_X$. This circuit can then be fed to a general-purpose proof scheme
prover $prover_X$ along with the witness and public input $(x, w) in X$, that
creates a proof of the statement $R_(X)(x, w) = top$. Simplifying slightly,
they typically consists of a series of pairs representing opening proofs:

$ (q_1 = (C_1, d, z_1, v_1, pi_1), ..., q_m = (C_m, d, z_m, v_m, pi_m)) $

These pairs can then be verified using $PCCheck$:

$ PCCheck(C_1, d, z_1, v_1, pi_1) meq 1 and ... and PCCheck(C_m, d, z_m, v_m, pi_m) meq 1 $

Along with some checks that the structure of the underlying polynomials
$vec(p)$, that $vec(q)$ was created from, satisfies any desired relations
associated with the circuit $R_X$.

Then the verifier $verifier_X$ will be convinced that $w$ is a
valid witness for $X$. In this way, a proof of knowledge of a witness for
any NP-problem can be represented as a series of PCS evaluation proofs.

A PCS has soundness and completeness properties, as well as a binding property:

*Completeness:* For every maximum degree bound $D = poly(lambda) in NN$
and publicly agreed upon $d in NN$:
#prob-game(
  $
    deg(p) <= d <= D, \
    PCCheck^rho (C, d, z, v, pi) = 1
  $,
  $
    rho           &<- cal(U)(lambda) \
    ppPC          &<- PCSetup^rho (1^lambda, D), \
    (p, d, z) &<- cal(A)^rho (ppPC), \
    v             &<- p(z), \
    C             &<- PCCommit^rho (p, d), \
    pi            &<- PCOpen^rho (p, C, d, z)
  $,
  $= 1$
)

In other words, an honest prover will always convince an honest verifier.

*Knowledge Soundness:* For every maximum degree bound $D = poly(lambda)
in NN$, polynomial-size adversary $cal(A)$ and publicly agreed upon $d$,
there exists an efficient extractor $cal(E)$ such that the following holds:
#prob-game(
  $
    PCCheck^rho (C, d, z, v, pi) = 1 \
    arrow.b.double \
    C = PCCommit^rho (p, d) \
    v = p(z), thin deg(p) <= d <= D
  $,
  $
    rho               &<- cal(U)(lambda) \
    ppPC              &<- PCSetup^rho (1^lambda, D) \
    (C, d, z, v, pi)  &<- cal(A)^rho (ppPC) \
    (p)        &<- cal(E)^rho (ppPC) \
  $,
  $>= 1 - negl(lambda)$
)

In other words, for any adversary, $cal(A)$, outputting an instance, the knowledge extractor
can recover $p$ such that the following holds: $C$ is a commitment to $p$,
$v = p(c)$, and the degree of $p$ is properly bounded. Note that for this
protocol, we have _knowledge soundness_, meaning that $cal(A)$, must actually
have knowledge of $p$ (i.e. the $cal(E)$ can extract it).

*Binding:* For every maximum degree bound $D = poly(lambda)
in NN$ and publicly agreed upon $d$, no polynomial-size adversary $cal(A)$
can find two polynomials s.t:

#prob-game(
  $
    p_1 in FF[X]_(<= d), thin
    p_2 in FF[X]_(<= d), thin
    p_1 != p_2 \
    and \
    C_1 = C_2
  $,
  $
    rho                       &<- cal(U)(lambda) \
    ppPC                      &<- PCSetup^rho (1^lambda, D) \
    (p_1, p_2, d) &<- cal(A)^rho (ppPC) \
    C_1                       &<- PCCommit(p_1, d) \
    C_2                       &<- PCCommit(p_2, d) \
  $,
  $<= negl(lambda).$
)

In other words, the adversary cannot change the polynomial that he committed to.

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
$O(ell)$ time, and thus, it would take $O(2^ell dot ell)$ time to compute
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
  each $k in [1..ell]$ using Dynamic Programming, which takes $O(2^k)$
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
  $O(sum^ell_(j=1) deg_j(g(vec(x))))$.
- *Verifier Runtime:* The verifiers runtime is proportional to the
  communication cost plus an additional evaluation of $g(vec(x))$, so
  $O("Eval"_g + sum^ell_(j=1) deg_j(g(vec(x))))$.
- *Provers Runtime:* In each round, the prover must evaluate $g(vec(x))$
  at $deg_j(g)+1$ points for each $2^(ell-j)$ term. This gives
  $O(sum^(ell)_(j=1) deg_j(g) dot 2^(ell-j) dot T)$, where $T$ is the cost of
  a single evaluation of $g(vec(x))$. Usually $deg_(j)(g(vec(x)))$ is bounded
  by some constant, in which case the cost is $O(2^(ell) dot T)$, since
  $sum^(ell)_(j=1) 2^(ell-j) = 2^(ell)$.

If the individual degree of $g(vec(x))$ is bounded, and $T$ is constant
($O(1)$) then the prover has a runtime of only $O(2^ell)$. Unfortunately,
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
