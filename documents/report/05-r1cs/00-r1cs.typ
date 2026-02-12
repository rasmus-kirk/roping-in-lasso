#import "../00-lib/header/lib.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

= R1CS

A popular alternative to GKR's layered circuit representation is R1CS. This
proof system represents computation of an arithmetic circuit as a system of
linear constraints combined with a single multiplication per constraint:

$ vec(C) vec(w) &= vec(A) vec(w) hadamard vec(B) vec(w) $

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

$ F(vec(x)) = (sum_(vec(b) in bits^s) A(vec(x), vec(b)) dot w(vec(x))) dot (sum_(vec(b) in bits^s) B(vec(x), vec(b)) dot w(vec(x))) - sum_(vec(b) in bits^s) C(vec(x), vec(b)) dot w(vec(x)) $

Since the R1CS instance will only be satisfied if and only if

$ forall vec(x) in bits^s : F(vec(x)) = 0 $<eq:r1cs-F-equals-zero>

#todo-box[
  Proof? Why?
]

We can of course also define the multilinear extensions of $A, B, C : Bool^s times Bool^s -> Bool, w : Bool^s -> Bool$ and model $F$ as a polynomial:

$
  tilde(M)(vec(x), vec(y)) &= sum_(vec(a) in bits^s) M(vec(a), vec(b)) dot tilde("eq")(vec(x), vec(a)) dot tilde("eq")(vec(y), vec(b)) \
  tilde(w)(vec(x))         &= sum_(vec(b) in bits^s) w(vec(b)) dot tilde("eq")(vec(x), vec(b)) \
  f(vec(x))                &= (sum_(vec(b) in bits^n) tilde(A)(vec(x), vec(b)) dot tilde(w)(vec(x))) dot (sum_(vec(b) in bits^n) tilde(C)(vec(x), vec(b)) dot tilde(w)(vec(x))) - sum_(vec(b) in bits^n) tilde(C)(vec(x), vec(b)) dot tilde(w)(vec(x))  
$

Now, it may be tempting to simply run sumcheck over this polynomial to make
sure the sum equals zero:

$ 0 meq sum_(vec(b) in bits) f(vec(b)) $

But since the terms can cancel out that won't work. Instead, we can once
again make use of Schwartz-Zippel. Consider the following polynomial:

$ q(vec(x)) = sum_(vec(b) in bits^(m)) tilde("eq")(vec(x), vec(b)) dot f(vec(b)) $

Given @eq:r1cs-F-equals-zero holds then it will obviously be true that $forall
vec(x) in Bool^s : q(vec(x)) = 0$. Since $tilde("eq")(vec(x), vec(b)) = 1$
if and only if $vec(x) = vec(b)$, and zero otherwise, then $q$ must also
evaluate to zero outside the domain. From here we can evaluate this polynomial
at a random point, and by Schwartz-Zippel, if it evaluates to zero, the
claim will hold.

#todo-box[
  With what probibility?
]
