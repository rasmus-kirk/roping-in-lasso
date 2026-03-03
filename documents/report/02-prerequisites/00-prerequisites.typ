#import "../00-lib/header/lib.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#show smallcaps: set text(font: "New Computer Modern")

= Prerequisites <sec:prerequisites>

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
  [A field element of an unspecified field $Fb$.],
  // Vector
  $[a_1, ..., a_n] = vec(a) in Fb^n$,
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

- *Completeness:* $forall prover in "ITM", X in L ==> Pr[lr(chevron.l prover, verifier chevron.r) = bot] <= epsilon(X)$

  For all honest provers, $prover$, where $X$ is true, the probability that the
  verifier remains unconvinced ($lr(chevron.l prover, verifier chevron.r)
  = bot$) is negligible in the length of $X$.

- *Soundness:* $forall prover^* in "ITM", X in.not L ==> Pr[lr(chevron.l prover^*, verifier chevron.r) = top] <= epsilon(X)$

  For all provers, honest or otherwise, $prover^*$, that try to convince
  the verifier of a claim, $X$, that is not true, the probability that the
  verifier will be convinced ($lr(chevron.l prover^*, verifier chevron.r)
  = top$) is negligible in the length of $X$.

An Interactive Argument is similar, but the honest and malicious prover
are now polynomially bounded and receive a Private Auxiliary Input, $w$,
not known by $verifier$. This is such that $verifier$ can't just compute the answer
themselves. Definitions follow:

- *Completeness*: $forall prover(w) in "PPT", X in L ==> Pr[lr(chevron.l prover(w), verifier chevron.r) = bot] <= epsilon(X)$
- *Soundness*: $forall prover^* in "PPT", X in.not L ==> Pr[lr(chevron.l prover^*, verifier chevron.r) = top] <= epsilon(X)$

Proofs of knowledge are another type of Proof System. Here the prover claims
to know a _witness_, $w$, for a statement $X$. Let $X in L$ and $W(X)$ be the
set of witnesses for $X$ that should be accepted in the proof. This allows
us to define the following relation: $Rc = { (X,w) : X in L , w in W(X) }$

A proof of knowledge for relation $Rc$ is a two party protocol $(prover, verifier)$
with the following two properties:

- *Knowledge Completeness:* $Pr[lr(chevron.l prover(w), verifier chevron.r) = top] = 1$, i.e. as in
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

#let View = "View"

- *Zero-Knowledge:* For every PPT verifier $V^*$, there exists a PPT
  simulator $S$ such that for every $x in L$ and auxiliary input $z in
  bits^*$, the transcripts produced by $S$ are indistinguishable from
  the interaction between any verifier and an honest prover:
  $ S(x, z) tilde View(lr(chevron.l prover(x), verifier^*(z) chevron.r)) $

Where $(tilde)$ denotes indistinguishability. The flavor of Zero-Knowledge
depends on the indistinguishability of the transcripts.

#definition(title: "Distinguishability")[
  Two distributions $D_1, D_2$ are said to be:

  - _Perfectly indistinguishable_ $(tilde^P)$ if they are identical, meaning no observer can tell them apart:
    $ forall x : Pr[D_1 = x] = Pr[D_2 = x] $
  - _Statistically indistinguishable_ $(tilde^S)$ if their statistical distance is negligible,
    meaning that they may differ, but the difference is vanishingly small,
    even for an unbounded adversary:
    $ Delta(D_1, D_2) := frac(1,2) sum_x abs(Pr[D_1 = x] - Pr[D_2 = x]) <= negl(lambda) $
  - _Computationally indistinguishable_ $(tilde^C)$ if no probabilistic polynomial-time
    distinguisher $Ac$ can tell them apart with more than negligible advantage,
    though an unbounded adversary might:
    $ forall x : abs(Pr[Ac(x) -> D_1] - Pr[Ac(x) = D_2]) <= negl(lambda) $
]

There are generally three types of Zero-Knowledge:

- *Perfect Zero-Knowledge:* $S(x, z) tilde^P View(lr(chevron.l prover(x), verifier^*(z) chevron.r))$.
- *Statistical Zero-Knowledge:* $S(x, z) tilde^S View(lr(chevron.l prover(x), verifier^*(z) chevron.r))$.
- *Computational Zero-Knowledge:* $S(x, z) tilde^C View(lr(chevron.l prover(x), verifier^*(z) chevron.r))$.

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

A commitment scheme is a cryptographic primitive that allows one to commit
to a chosen value while keeping it hidden to others, with the ability to
reveal the committed value later. Commitment schemes are designed so that
the committing party cannot change the value after they have committed to it,
i.e. it is _binding_. The fact that anyone who receives the commitment cannot
compute the value from the commitment is called _hiding_. For $C = CMCommit(m)$

- *Perfect Hiding:* Given $C$, it is impossible to determine $m$, no matter your computational power.
- *Computational Hiding:* It is computationally infeasible to determine the value committed, from the commitment.
- *Perfect Binding:* It is impossible to change the value committed to, no matter your computational power.
- *Computational Binding:* It is computationally infeasible to change the value committed to.

To reveal a value one can simply send the value to a party that previously
received the commitment, and the receiving party can compute the commitment
themselves and compare to the previously received commitment.

Pedersen commitments@pedersen are an instance of a highly useful type of
commitment scheme. One of the reasons of its usefulness is due to fact that
it's a _homomorphic commitment scheme_. Specifically, Pedersen commitments
are additively homomorphic, meaning:

$
  CMCommit(m_1) + CMCommit(m_2) = CMCommit(m_1 + m_2)
$

That is, you can add the commitments which corresponds to adding the committed
inputs and then committing to the result.

== Polynomial Commitment Schemes <sec:pcs>

// --- Definitions ---
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
- *Bulletproofs PCSs:* Uses an untrusted setup, which is secure assuming the
  Discrete Log problem is hard, the verifier is linear.
- *FRI PCSs:* Also uses an untrusted setup, assumes secure one way functions
  exist. It has a higher constant overhead than PCSs based on the Discrete
  Log assumption, but because it only assumes that secure one-way functions
  exist, you end up with a quantum secure PCS.

A PCS allows a prover to prove to a verifier that a committed polynomial
evaluates to a certain value, $v$, given an evaluation input $z$. There
are four main functions used to prove this:

- $PCSetup(lambda, D)^rho -> ppPC$

  The setup routine. Given security parameter $lambda$ in unary and a maximum
  degree bound $D$. Creates the public parameters $ppPC$.

- $PCCommit(p in Fb^(d')[X], d in Nb) -> Commit$

  Commits to a degree-$d'$ polynomial $p$ with degree bound $d$ where $d'
  <= d$.

- $PCOpen^(rho)(p in Fb^(d')[X], C in Commit, d in Nb, z in Fb) -> EvalProof$

  Creates a proof, $pi in EvalProof$, that the degree $d'$ polynomial $p$,
  with commitment $C$, and degree bound $d$ where $d' <= d$, evaluated at
  $z$ gives $v = p(z)$.

- $PCCheck^(rho)(C in Commit, d in Nb, z in Fb, v in Fb, pi in EvalProof) -> bits$

  Checks the proof $pi$ that claims that the degree $d'$ polynomial $p$,
  with commitment $C$, and degree bound $d$ where $d' <= d$, evaluates to
  $v = p(z)$.

Any NP-problem, $X in "NP"$, with a witness $w$ can be compiled into a
circuit $R_X$. This circuit can then be fed to a general-purpose proof scheme
prover $prover_X$ along with the witness and public input $(x, w) in X$, that
creates a proof of the statement $R_(X)(x, w) = top$. Simplifying slightly,
they typically consists of a series of tuples representing opening proofs:

$ (q_1 = (C_1, d, z_1, v_1, pi_1), ..., q_m = (C_m, d, z_m, v_m, pi_m)) $

These tuples can then be verified using $PCCheck$:

$ PCCheck(C_1, d, z_1, v_1, pi_1) meq 1 and ... and PCCheck(C_m, d, z_m, v_m, pi_m) meq 1 $

Along with some checks that the structure of the underlying polynomials
$vec(p)$, that $vec(q)$ was created from, satisfies any desired relations
associated with the circuit $R_X$.

Then the verifier $verifier_X$ will be convinced that $w$ is a
valid witness for $X$. In this way, a proof of knowledge of a witness for
any NP-problem can be represented as a series of PCS evaluation proofs.

A PCS has soundness and completeness properties, as well as a binding property:

#definition(title: "PCS Completeness")[
  For every maximum degree bound $D = poly(lambda) in Nb$ and publicly agreed
  upon $d in Nb$:
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
]

#definition(title: "Knowledge Soundness")[
  For every maximum degree bound $D = poly(lambda) in Nb$, polynomial-size
  adversary $cal(A)$ and publicly agreed upon $d$, there exists an efficient
  extractor $cal(E)$ such that the following holds:
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
  $v = p(z)$, and the degree of $p$ is properly bounded. Note that for this
  protocol, we have _knowledge soundness_, meaning that $cal(A)$, must actually
  have knowledge of $p$ (i.e. the $cal(E)$ can extract it).
]

#definition(title: "Binding")[
  For every maximum degree bound $D = poly(lambda) in Nb$ and publicly agreed
  upon $d$, no polynomial-size adversary $cal(A)$ can find two polynomials s.t:

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

  In other words, the adversary cannot change the polynomial that they committed to.
]

== The Schwartz-Zippel Lemma<sec:schwartz-zippel>

The Schwartz-Zippel lemma is commonly used in succinct proof systems to test
polynomial identities. Formally it states:

$ xi inrand Fb : Pr[p(xi) = 0 | p(X) != 0] <= frac(d, |Fb|) $

Meaning that if $p(X)$ is not the zero-polynomial, the evaluation at a
uniformly random point from $Fb$, will equal zero with at most $frac(style:
"horizontal", d, |Fb|)$ probability. This can also be used to check equality
between polynomials:

$
  xi    &inrand Fb \
  r(X)  &= p(X) - q(X) \
  r(xi) &meq 0
$

Or equivalently:

$ p(xi) meq q(xi) $

Meaning that $p(X) = q(X)$ with probability at least $1 - frac(style:
"horizontal", d, |Fb|)$.
