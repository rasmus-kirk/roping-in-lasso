#import "../00-lib/header/lib.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

= GKR<sec:gkr>

Given a circuit $circuit$, with $d$ layers, $n$ inputs and $m$ outputs,
a prover ($prover$) wishes to prove to a verifier ($verifier$) a specific
input $vec(w) in bits^n$ applied to $circuit$ produces some output $vec(y)
in bits^m$. Each layer $i$ has a number of either addition or multiplication
gates $S_i$ and for notational purposes we also introduce $s_i := lg(S_i)$. The
size of the circuit is the number of gates $S = sum_(i=0)^d S_i$. $prover$
can leverage the sumcheck protocol, defined earlier.

#figure(
  align(center)[
    #set math.equation(numbering: none)
    #set text(10pt)
    #let w = 0.8
    #let h = 0.8
    #diagram(
      node-stroke: 1pt,
      {
        let O = (3*w, -1.5*h)
        let N00 = (3*w, 0*h)
        let (N10, N11) = ((1*w, 1*h), (5*w, 1*h))
        let (N20, N21, N22, N23) = (
          (0*w, 2*h),
          (2*w, 2*h),
          (4*w, 2*h),
          (6*w, 2*h),
        )
        let (N30, N31, N32, N33) = (
          (0*w, 3.5*h),
          (2*w, 3.5*h),
          (4*w, 3.5*h),
          (6*w, 3.5*h),
        )

        // Really hacky centering lol
        node((8.25*w, 0*h), "", stroke: none)
        node((-1.2*w, -1.5*h), "Outputs")
        node((-1.2*w, 0*h), "Layer 0")
        node((-1.2*w, 1*h), "Layer 1")
        node((-1.2*w, 2*h), "Layer 2")
        node((-1.2*w, 3.5*h), "Inputs")
        node(O, [$y_1$], shape: rect)
        node(N00, [$times_(0)$], radius: 1.2em)
        node(N10, [$times_(0)$], radius: 1.2em)
        node(N11, [$times_(1)$], radius: 1.2em)
        node(N20, [$times_(00)$], radius: 1.2em)
        node(N21, [$times_(01)$], radius: 1.2em)
        node(N22, [$times_(10)$], radius: 1.2em)
        node(N23, [$times_(11)$], radius: 1.2em)
        node(N30, [$w_1$], shape: rect)
        node(N31, [$w_2$], shape: rect)
        node(N32, [$w_3$], shape: rect)
        node(N33, [$w_4$], shape: rect)
        edge(N10, N00, "-|>")
        edge(N11, N00, "-|>")
        edge(N20, N10, "-|>")
        edge(N21, N10, "-|>")
        edge(N22, N11, "-|>")
        edge(N23, N11, "-|>")
        edge(N30, N20, "-->")
        edge(N31, N21, "-->")
        edge(N32, N22, "-->")
        edge(N33, N23, "-->")
        edge(N00, O, "-->")
      }
    )
  ],
  caption: text[
    A layered arithmetic circuit for the computation $y_1 = product_(i=1)^k
    w_i$. Each node-label below represents the type of computation and the
    gate-label for the given layer, so $(times_0)$ is a multiplication gate
    with label $0$, for layer $0$. Note that $d = 3, n = 4, m = 1, S_1 = 1,
    S_2 = 2, S_3 = 4, S = 7$.
  ],
  // supplement: [W'iagram],
) <fig:example_circuit>

To represent a layered circuit in a form amenable to the sum check protocol,
we must first provide an adequate polynomial representation of the circuit. We
start with the following three functions:

- $"add"_(i)(vec(a),vec(b),vec(c)) in bits^(s_i+2s_(i+1)) -> bits$ which outputs $1$ if and only if gate $a$ is an addition gate and $b$ is the left input and $c$ is the right input of gate $a$.
- $"mul"_(i)(vec(a),vec(b),vec(c)) in bits^(s_i+2s_(i+1)) -> bits$ which outputs $1$ if and only if gate $a$ is a multiplication gate and $b$ is the left input and $c$ is the right input of gate $a$.
- $W_(i)(vec(a)) in bits^(s_i) -> bits$ which, given the gate-label $a$, outputs the value of node $a$.

#example[
  For @fig:example_circuit $"add"_i, "mul"_i$ would evaluate to the following
  values, with $(wildcard)$ denoting any other input:

  #math.equation(
    block: true,
    numbering: none,
    $
      mat(delim: #none, column-gap: #3em, align: #left,
        "mul"_0(0 || 0 || 0) = 1, "mul"_1(0 || 00 || 01) = 1;
        "mul"_0(0 || 0 || 1) = 1, "mul"_1(1 || 10 || 11) = 1;
        "mul"_0(wildcard) = 0,    "mul"_1(wildcard) = 0;
        "add"_0(wildcard) = 0,    "add"_1(wildcard) = 0;
      )
    $
  )
]

We can use the multilinear extensions of $"add"_i$ and $"mul"_i$ to represent
$W_(i)$ in a form that lets us use sumcheck:

$ tilde(W)_(i)(vec(a)) = sum_(vec(b),vec(c) in bits^(s_(i+1))) tilde("add")_(i)(vec(a),vec(b),vec(c))(tilde(W)_(i+1)(vec(b)) + tilde(W)_(i+1)(vec(c))) + tilde("mult")_(i)(vec(a),vec(b),vec(c)) dot tilde(W)_(i+1)(vec(b)) dot tilde(W)_(i+1)(vec(c)) $<eq:tilde-w>

#lemma[
  The above equation for $tilde(W)_(i)(vec(a))$ is indeed the multilinear extension of $W_(i)(vec(a))$
]<lem:tilde-w-mle>

#proof[
  In order to prove the Lemma, we need to first prove multilinearity,
  i.e. that each individual degree of $tilde(W)_(i)(vec(a)) <= 1$. This
  is apparent, since even though we multiply polynomials, only the
  $vec(b), vec(c)$ variables are affected, not $vec(a)$.

  Next, we need to argue that $forall vec(a) in bits^(s_i) :
  tilde(W)_(i)(vec(a)) = W_(i)(vec(a))$. This follows from the fact that
  $tilde("add")_i, tilde("mul")_i, tilde(W)_(i+1)$ are all multilinear
  extensions of their respective functions. We should therefore also be able
  to rewrite @eq:tilde-w like so:

  $ tilde(W)_(i)(vec(a) in bits^(s_i)) = sum_(vec(b),vec(c) in bits^(s_(i+1))) "add"_(i)(vec(a),vec(b),vec(c))(W_(i+1)(vec(b)) + W_(i+1)(vec(c))) + "mult"_(i)(vec(a),vec(b),vec(c)) dot W_(i+1)(vec(b)) dot W_(i+1)(vec(c)) $

  The definitions of $"add"_i, "mul"_i$ state that they are only active when
  the given gate label is an addition or multiplication gate respectively. Thus,
  for any valid circuit, only one may be active at a time. Additionally,
  again for any valid circuit, only a single of these terms in the sum will
  output a value of either:

  $ W_(i+1)(vec(b)) + W_(i+1)(vec(c)), #h(2em) W_(i+1)(vec(b)) dot W_(i+1)(vec(c)) $

  Depending on whether the gate-label refers to an addition or multiplication
  gate. This is exactly the value that's produced by $W_(i)$, as long as
  $tilde(W)_(i+1)$ is indeed the MLE of $W_(i+1)$. Applying this argument
  recursively proves the claim.
]

Assume that $prover$ convinces $verifier$ that some polynomial $W'(X_1,
dots, X_(s_0)) = W_0(X_1, dots, X_(s_0))$, then by @lem:tilde-w-mle,
$W'$ describes the output of the circuit given the chosen input. Then the
verifier can confirm that the evaluations of the circuit given input $vec(w)$
evaluates to $vec(y)$ by simply evaluating $W'(X_1, dots, X_(s_0))$ on all
gate labels in the output layer. To prove $W' = W_0$, $verifier$ chooses
a uniformly random $vec(r)$ and wishes to verify that $tilde(W)'(vec(r))
= tilde(W)_0(vec(r))$, which by Schwarz-Zippel means that $tilde(W)' =
tilde(W)_0$, and by definition of MLE's $W' = W_0$. Therefore, $prover$
and verifier apply sumcheck to the following polynomial:

$ f_(0)(vec(b), vec(c)) = tilde("add")_(0)(vec(r),vec(b),vec(c))(tilde(W)_1(vec(b)) + tilde(W)_1(vec(c))) + tilde("mult")_(0)(vec(r),vec(b),vec(c)) dot tilde(W)_1(vec(b)) dot tilde(W)_1(vec(c)) $

Which, if succesful, convinces $verifier$ that $tilde(W)'(vec(r)) =
tilde(W)_0(vec(r)) ==> W' = W_0$ as desired. But in the final round of the
sumcheck protocol, $verifier$ must be able to evaluate the above polynomial
at a random point. The functions $tilde("add")_0$ and $tilde("mul")_0$ are part
of the circuit description, and can thus be computed by $verifier$ without
help from $prover$ #footnote[This can be done by $verifier$ in at least
time $O(S_i)$ time, reducing this to $O(lg(S_i))$ is important to achieve a
sublinear verifier if this IP is turned into an Interactive Argument.]. But
$verifier$ also needs to evaluate $tilde(W_1)$ at two separate random points
$vec(b)'_0, vec(c)'_0 inrand Fb^(s_1)$ corresponding to $vec(b), vec(c)$:

$ f_(0)(vec(b)'_0, vec(c)'_0) = tilde("add")_(0)(vec(r),vec(b)'_0,vec(c)'_0)(tilde(W)_1(vec(b)'_0) + tilde(W)_1(vec(c)'_0)) + tilde("mult")_(0)(vec(r),vec(b)'_0,vec(c)'_0) dot tilde(W)_1(vec(b)'_0) dot tilde(W)_1(vec(c)'_0) $

In principle, we could run the sumcheck protocol twice, on the polynomials:

$
  f_(1)(vec(b), vec(c)) &= tilde("add")_(1)(vec(b)'_0,vec(b),vec(c))(tilde(W)_2(vec(b)) + tilde(W)_2(vec(c))) + tilde("mult")_(1)(vec(b)'_1,vec(b),vec(c)) dot tilde(W)_2(vec(b)) dot tilde(W)_2(vec(c)) \
  f_(1)(vec(b), vec(c)) &= tilde("add")_(1)(vec(c)'_0,vec(b),vec(c))(tilde(W)_2(vec(b)) + tilde(W)_2(vec(c))) + tilde("mult")_(1)(vec(c)'_1,vec(b),vec(c)) dot tilde(W)_2(vec(b)) dot tilde(W)_2(vec(c))
$ <eq:two-fs>

But this would result in an exponential amount of sumchecks in the depth $d$,
which would be quite a problem! Instead, we can reduce two checks into one,
using a linear combination.

== Combining two claims to one

Suppose we were to apply sumcheck to the following polynomial instead:

$
  q(vec(b)'_0, vec(c)'_0) := tilde(W)_(1)(vec(b)'_0) + alpha dot tilde(W)_(1)(vec(c)'_0)
$

Which can be derived as:

$
  q(vec(b)'_0, vec(c)'_0) &= &&(sum_(vec(b),vec(c) in bits^(s_(2))) tilde("add")_(1)(vec(b)'_0,vec(b),vec(c))(tilde(W)_(2)(vec(b)) + tilde(W)_(2)(vec(c))) + tilde("mul")_(1)(vec(b)'_0,vec(b),vec(c)) dot tilde(W)_(2)(vec(b)) dot tilde(W)_(2)(vec(c))) + \
                          &  &&alpha dot (sum_(b,c in bits^(s_(2))) tilde("add")_(1)(vec(c)'_0,vec(b),vec(c))(tilde(W)_(2)(vec(b)) + tilde(W)_(2)(vec(c))) + tilde("mul")_(1)(vec(c)'_0,vec(b),vec(c)) dot tilde(W)_(2)(vec(b)) dot tilde(W)_(2)(vec(c))) \
                          &= &&sum_(vec(b),vec(c) in bits^(s_(2))) tilde("add")_(1)(vec(b)'_0,vec(b),vec(c))(tilde(W)_(2)(vec(b)) + tilde(W)_(2)(vec(c))) + tilde("mul")_(1)(vec(b)'_0,vec(b),vec(c)) dot tilde(W)_(2)(vec(b)) dot tilde(W)_(2)(vec(c)) + \
                          &  &&alpha dot tilde("add")_(1)(vec(c)'_0,vec(b),vec(c))(tilde(W)_(2)(vec(b)) + tilde(W)_(2)(vec(c))) + alpha dot tilde("mul")_(1)(vec(c)'_0,vec(b),vec(c)) dot tilde(W)_(2)(vec(b)) dot tilde(W)_(2)(vec(c)) \
                          &= &&sum_(vec(b),vec(c) in bits^(s_(2))) (tilde("add")_(1)(vec(b)'_0,vec(b),vec(c)) + alpha dot tilde("add")_(1)(vec(c)'_0,vec(b),vec(c)))(tilde(W)_(2)(vec(b)) + tilde(W)_(2)(vec(c))) + \
                          &  &&(tilde("mul")_(1)(vec(b)'_0,vec(b),vec(c)) + alpha dot tilde("mul")_(1)(vec(c)'_0,vec(b),vec(c)))(tilde(W)_(2)(vec(b)) dot tilde(W)_(2)(vec(c)))
$ <eq:combined-poly>

The Lemma #footnote[This approach is also used in Libra@libra, but they don't
present a soundness proof since they deem it "trivial". The Lemma in this
document also uses a single random variable rather than two.] below shows
how this will help the prover-verifier pair in showing that $v_(vec(b)'_0)
= tilde(W)_1(vec(b)'_0) and v_(vec(b)'_0) = tilde(W)_1(vec(c)'_0)$, thus
enabling $verifier$ to compute $f_(0)(vec(b)'_0, vec(c)'_0)$:

#lemma[
  #set math.equation(numbering: none)
  For a polynomial $p(X_1, ..., X_ell)$, if a prover wants to convince a verifier
  of two claims $v_1 = p(vec(r)_1), v_2 = p(vec(r)_2)$, then they can reduce this to a
  single claim over a polynomial $q(vec(r)_1, vec(r)_2)$:

  $
    q(X_1, .., X_(2ell)) := p(X_1, ..., X_ell) + alpha dot p(X_(ell+1), ..., X_(2ell))
  $

  $verifier$ can then check that $q(vec(r)_1, vec(r)_2) = v_1 + alpha dot v_2$.
  The claim that $v_1 = p(vec(r)_1) and v_2 = p(vec(r)_2)$ will then hold except with
  negligible probability of $frac(1, |Fb|)$, given that $q(X_1, ..., X_(2ell))$
  is defined as above.
] <lem:multiple-evals-same-poly>

#proof[
  #set math.equation(numbering: none)
  If $q(vec(r)_1, vec(r)_2) = p(vec(r)_1) + alpha dot p(vec(r)_2)$ but the
  claim does not hold, i.e. $v_1 != p(vec(r)_1), v_2 != p(vec(r)_2)$ then that
  would mean that the following univariate polynomial is a non-zero polynomial:

  $ e(X) = v_1 + X dot v_2 - (p(vec(r)_1) + X dot p(vec(r)_2)) $

  And that it still evaluated to zero, which by the Schwarz-Zippel Lemma,
  has probability:

  $ Pr[e(alpha) = 0 | e(X) != 0] = frac(deg(p), |Fb|) = frac(1, |Fb|) $

  Which is negligible in the size of the field.
]

In the GKR protocol, running sumcheck on @eq:combined-poly convinces
$verifier$ that $q(vec(b)'_0, vec(c)'_0) = tilde(W)_1(vec(b)'_0) + alpha dot
tilde(W)_1(vec(c)'_0)$, which means that $verifier$ knows that $q$
is defined as in @lem:multiple-evals-same-poly and they know the evaluation
of $q$ at $vec(b)'_0, vec(c)'_0$. $verifier$ can then verify that $v_(vec(b)'_0)
= tilde(W)_1(vec(b)'_0)$ and $v_(vec(c)'_0) = tilde(W)_1(vec(c)'_0)$ by additionally checking
that $q(vec(b)'_0, vec(c)'_0) = v_(vec(b)'_0) + alpha dot v_(vec(c)'_0)$.

With $v_(vec(b)'_0)$ and $v_(vec(c)'_0)$ $verifier$ can compute the evaluation of
$f_(0)(vec(b)'_0, vec(c)'_0)$:

$ f_(0)(vec(b)'_0, vec(c)'_0) = tilde("add")_(0)(vec(r),vec(b)'_0,vec(c)'_0)(v_(vec(b)'_0) + v_(vec(c)'_0)) + tilde("mult")_(0)(vec(r),vec(b)'_0,vec(c)'_0) dot v_(vec(b)'_0) dot v_(vec(c)'_0) $

Thus, when we proceed to layer one, the polynomial we do sumcheck on
would be:

$
  f_(1)(vec(b), vec(c)) &:= &&(tilde("add")_(1)(vec(b)'_0,vec(b),vec(c)) + alpha dot tilde("add")_(1)(vec(c)'_0,vec(b),vec(c)))(tilde(W)_(2)(vec(b)) + tilde(W)_(2)(vec(c))) + \
                        &   &&(tilde("mul")_(1)(vec(b)'_0,vec(b),vec(c)) + alpha dot tilde("mul")_(1)(vec(c)'_0,vec(b),vec(c)))(tilde(W)_(2)(vec(b)) dot tilde(W)_(2)(vec(c)))
$

It should already now be apparent that we can repeat this procedure, all
the way to the input layer $d$.

== Completing the protocol

In the layer before the input layer ($d-1$), the final check in the
sumcheck protocol requires $verifier$ to evaluate the following polynomial
at $vec(b)'_(d-1), vec(c)'_(d-1)$:

$
  f_(d-1)(vec(b), vec(c)) &:= &&(tilde("add")_(d-1)(vec(b)'_(d-2),vec(b),vec(c)) + alpha dot tilde("add")_(d-1)(vec(c)'_(d-2),vec(b),vec(c)))(tilde(W)_(d)(vec(b)) + tilde(W)_(d)(vec(c))) + \
                                                                    &   &&(tilde("mul")_(d-1)(vec(b)'_(d-2),vec(b),vec(c)) + alpha dot tilde("mul")_(d-1)(vec(c)'_(d-2),vec(b),vec(c)))(tilde(W)_(d)(vec(b)) dot tilde(W)_(d)(vec(c)))
$

The polynomials $tilde("add")_(d-1)$ and $tilde("mul")_(d-1)$ can be evaluated
as usual. The polynomial $tilde(W)_(d)$ corresponds to the values of the
input layer $vec(w)$. Since $verifier$ knows $vec(w)$ they can compute the
multilinear extension of $vec(w)$ corresponding to $W_(d)$. From this the
verifier can compute $tilde(W)_(d)(vec(b)'_d), tilde(W)_(d)(vec(c)'_d)$
and thus the evaluation of $f_(d-1)(vec(b)'_(d-1), vec(c)'_(d-1))$.

The entire protocol can be seen on the next page:

#let zero-width-box(body) = context {
  let width = 35em
  let (height,) = measure(width: width, body)
  place(center + horizon, box(width: width, height: height, body))
  box(width: 0%, height: 2 * height)
}

#align(center)[
  #set math.equation(numbering: none)
  #set text(10pt)
  #let w = 0.7
  #let h = 0.7

  #diagram(debug: 0, {
    let (P, M, V) = ((0, 0), (1.5, 0), (3, 0))

    node(M,
      zero-width-box([$#text(size: 12pt, $
        hat(x) &:= ("add"_0, ..., "add"_d, "mul"_0, ..., "mul"_d)
      $)$])
    )

    P.at(1) += h/3; M.at(1) += h/3; V.at(1) += h/3;

    node(P, $#text(size: 12pt, $bold("Prover")(hat(x), vec(w))$)$)
    node(V, $#text(size: 12pt, $bold("Verifier")(hat(x), vec(w))$)$)
    P.at(1) += h/2; M.at(1) += h/2; V.at(1) += h/2; 

    // -------------------- Preprocessing -------------------- //
    node(M, $#text(size: 12pt, weight: "black", $"Preprocessing"$)$)
    edge(P, M, "=")
    edge(M, V, "=")
    P.at(1) += h/1.5; M.at(1) += h/1.5; V.at(1) += h/1.5; 

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      $prover$ sends $W'$ to $verifier$ claiming that $W' = W_0$. $verifier$
      then picks out a random $vec(r)$. After this point, $prover$ wants to
      prove that $m_0 = tilde(W)_0(vec(r))$.
    ]))
    P.at(1) += h/1.5; M.at(1) += h/1.5; V.at(1) += h/1.5;

    node(P, $W': bits^(s_0) -> Fb$)
    node(V, $ vec(r) inrand Fb^(s_0), m_0 := tilde(W)'(vec(r)) $)
    edge(P, V, "->", $ W' $)
    P.at(1) += h/2; M.at(1) += h/2; V.at(1) += h/2; 

    // -------------------- Round 0 -------------------- //
    node(M, $#text(size: 12pt, weight: "black", $"Round" 0$)$)
    edge(P, M, "=")
    edge(M, V, "=")
    P.at(1) += h/1.3; M.at(1) += h/1.3; V.at(1) += h/1.3; 

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      $prover$ defines the $(2s_i)$-variate polynomial,
      $f_(0)(vec(b), vec(c))$, $prover$ and $verifier$ then perform
      sumcheck on the polynomial:
      $ f_(0)(vec(b), vec(c)) = tilde("add")_(0)(vec(r),vec(b),vec(c))(tilde(W)_1(vec(b)) + tilde(W)_1(vec(c))) + tilde("mul")_(0)(vec(r),vec(b),vec(c)) tilde(W)_1(vec(b)) dot tilde(W)_1(vec(c)) $
    ]))
    P.at(1) += h; M.at(1) += h; V.at(1) += h;

    // node(P, $ f_(0)_(r)(b', c')$)
    edge(P, V, "<->", $sum_(vec(b), vec(c) in bits^(s_1)) f_(0)(vec(b), vec(c)) meq m_0$)
    P.at(1) += h/1.5; M.at(1) += h/1.5; V.at(1) += h/1.5; 

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      At the end of the protocol, $prover$ sends $verifier$ the evaluations
      of $v_(vec(b)'_0) := tilde(W)_1(vec(b)'_0)$ and $v_(vec(c)'_0) := tilde(W)_1(vec(c)'_0)$, so
      $verifier$ can make the final check in the sumcheck protocol.
    ]))
    P.at(1) += h/1.3; M.at(1) += h/1.3; V.at(1) += h/1.3;

    node(P, $v_(vec(b)'_0) := tilde(W)_1(vec(b)'_0), v_(vec(c)'_0) := tilde(W)_1(vec(c)'_0)$)
    node(V, $
      m_0 meq &tilde("add")_0(vec(r), vec(b)'_0, vec(c)'_0) dot (v_(vec(b)'_0) + v_(vec(c)'_0)) + \
              &tilde("mul")_0(vec(r), vec(b)'_0, vec(c)'_0) dot v_(vec(b)'_0) dot v_(vec(c)'_0)
    $)
    edge(P, V, "->", $v_(vec(b)'_0), v_(vec(c)'_0)$)
    P.at(1) += h/2.5; M.at(1) += h/2.5; V.at(1) += h/2.5; 

    // -------------------- Round i -------------------- //
    node(M, $#text(size: 12pt, weight: "black", $"Round" i in [1..d-1]$)$)
    edge(P, M, "=")
    edge(M, V, "=")
    P.at(1) += h/1.4; M.at(1) += h/1.4; V.at(1) += h/1.4; 

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      To verify the values $v_(vec(b)'_(i-1)), v_(vec(c)'_(i-1))$ from the
      previous round, $verifier$ picks out a randomly sampled value $alpha$
      and sends it to $prover$. $prover$ uses $alpha$ to construct the
      combined-claim polynomial, for which $prover$ and $verifier$ perform
      the sumcheck over:

      $
        f_(i)(vec(b), vec(c)) &:= &&(tilde("add")_(i)(vec(b)'_(i-1),vec(b),vec(c)) + tilde("add")_(i)(vec(c)'_(i-1),vec(b),vec(c)))(tilde(W)_(i+1)(vec(b)) + tilde(W)_(i+1)(vec(c))) + \
                                       &   &&(tilde("mul")_(i)(vec(b)'_(i-1),vec(b),vec(c)) + tilde("mul")_(i)(vec(c)'_(i-1),vec(b),vec(c)))(tilde(W)_(i+1)(vec(b)) dot tilde(W)_(i+1)(vec(c)))
      $
    ]))
    P.at(1) += h/1.8; M.at(1) += h/1.8; V.at(1) += h/1.8; 

    node(P, $f_(i)(vec(b), vec(c))$)
    node(V, $ alpha inrand Fb $)
    edge(V, P, "->", $alpha$)
    P.at(1) += h/2.8; M.at(1) += h/2.8; V.at(1) += h/2.8; 

    edge(P, V, "<->", $sum_(vec(b), vec(c) in bits^(s_(i+1))) f_(i)(vec(b), vec(c)) meq m_i$)
    P.at(1) += h/2.3; M.at(1) += h/2.3; V.at(1) += h/2.3;

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      At the end of the protocol, $prover$ sends $verifier$ the evaluations
      of $v_(vec(b)'_i) := tilde(W)_(i+1)(vec(b)'_i)$ and $v_(vec(c)'_i) :=
      tilde(W)_(i+1)(vec(c)'_i)$, so $verifier$ can make the final check in
      the sumcheck protocol:
      $
        m'_i &:= &&(tilde("add")_(i)(vec(b)'_(i-1),vec(b)'_(i),vec(c)'_(i)) + alpha dot tilde("add")_(i)(vec(c)'_(i-1),vec(b)'_i,vec(c)'_i))(v_(vec(b)'_i) + v_(vec(c)'_i)) + \
             &   &&(tilde("mul")_(i)(vec(b)'_(i-1),vec(b)'_(i),vec(c)'_(i)) + alpha dot tilde("mul")_(i)(vec(c)'_(i-1),vec(b)'_i,vec(c)'_i))(v_(vec(b)'_i) dot v_(vec(c)'_i))
      $
    ]))
    P.at(1) += h/1.3; M.at(1) += h/1.3; V.at(1) += h/1.3;

    node(P, $v_(vec(b)'_i) := tilde(W)_(i)(vec(b)'_i), v_(vec(c)'_i) := tilde(W)_(i)(vec(c)'_i)$)
    node(V, $m_i meq m'_i$)
    edge(P, V, "->", $v_(vec(b)'_i), v_(vec(c)'_i)$)
    P.at(1) += h/2.4; M.at(1) += h/2.4; V.at(1) += h/2.4; 

    // -------------------- Round d -------------------- //
    node(M, $#text(size: 12pt, weight: "black", $"Round" d$)$)
    edge(P, M, "=")
    edge(M, V, "=")
    P.at(1) += h/2.3; M.at(1) += h/2.3; V.at(1) += h/2.3;

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      At the input layer $d$, $verifier$ has two claims $v_(vec(b)'_(d-1))$
      and $v_(vec(c)'_(d-1))$. $verifier$ constructs $tilde(W)_d$
      from $vec(w)$. $verifier$ then finally checks that
      $tilde(W)_(d)(vec(b)'_(d-1)) meq v_(vec(b)'_(d-1))$ and
      $tilde(W)_(d)(vec(c)'_(d-1)) meq v_(vec(c)'_(d-1))$.
    ]))
    P.at(1) += h/1.5; M.at(1) += h/1.5; V.at(1) += h/1.5; 
    
    node(V, $
      tilde(W)_(d)(vec(b)'_(d-1)) &meq v_(vec(b)'_(d-1)) and \
      tilde(W)_(d)(vec(c)'_(d-1)) &meq v_(vec(c)'_(d-1))
    $)
    P.at(1) += h; M.at(1) += h; V.at(1) += h; 
  })
]

== Efficiency<sec:gkr-efficiency>

*Communication:* $O(S_0 + d dot lg(S))$

The GKR protocol has the following communication costs:

- *Preprocessing:* $W'$, which has size $2^(s_0) = S_0$.
- *Round 0:* $O(s_1)$
  - One sumcheck: $O(sum^(2 s_1)_(j=1) deg_(j)(f_(0)))$, and since $deg_(j)(f_(0))$ is constant; $O(s_1)$
  - Two evaluations: $v_(b'_0), v_(c'_0)$
- *Round $i$:* $O(s_(i+1))$
  - One challenge: $alpha$
  - One sumcheck: $O(sum^(2 s_(i+1))_(j=1) deg_(j)(f_(i)))$, and since $deg_(j)(f_(i))$ is constant; $O(s_(i+1))$
  - Two evaluations: $v_(b'_i), v_(c'_i)$

For a total of $O(S_0 + sum^(d-1)_(i=0) s_(i+1)) = O(S_0 + sum^(d-1)_(i=0) lg(S_i)) = O(S_0 + d dot lg(S))$ communication.

*Evaluating $tilde("add")_(i)(vec(a),vec(b),vec(c)),
tilde("mul")_(i)(vec(a),vec(b),vec(c))$ in linear time:*

Before discussing the runtime cost of $prover$ and $verifier$,
we first describe how $tilde("add")_(i)(vec(a),vec(b),vec(c))$ and
$tilde("mul")_(i)(vec(a),vec(b),vec(c))$ can be evaluated in $O(S_i)$ time.

First we define two functions $"in"^((i))_(L)(vec(a)), "in"^((i))_(R)(vec(a))
in bits^(s_i) -> bits^(s_(i+1))$ which, when given a node-label returns
the left and right incoming node's labels respectively. We also define the
functions $"isAdd"(vec(a)), "isMul"(vec(a)) in bits^(s_i) -> bits$, that define
whether $vec(a)$ is an addition or multiplication gate respectively. Then
we can define:

$
  "add"_(i)(vec(a),vec(b),vec(c)) &:= "isAdd"(vec(a)) and vec(b) meq "in"^((i))_(L)(vec(a)) and vec(c) meq "in"^((i))_(R)(vec(a)) \
  "mul"_(i)(vec(a),vec(b),vec(c)) &:= "isMul"(vec(a)) and vec(b) meq "in"^((i))_(L)(vec(a)) and vec(c) meq "in"^((i))_(R)(vec(a)) 
$

And their MLE's:

$
  tilde("add")_(i)(vec(a),vec(b),vec(c)) &:= sum_(vec(a)' in bits^(s_i)) tilde("eq")_vec(a)(vec(a)') dot "isAdd"_(i)(vec(a)') dot tilde("eq")_(vec(b))("in"^((i))_(L)(vec(a)')) dot tilde("eq")_(vec(c))("in"^((i))_(R)(vec(a)')) \
  tilde("mul")_(i)(vec(a),vec(b),vec(c)) &:= sum_(vec(a)' in bits^(s_i)) tilde("eq")_vec(a)(vec(a)') dot "isMul"_(i)(vec(a)') dot tilde("eq")_(vec(b))("in"^((i))_(L)(vec(a)')) dot tilde("eq")_(vec(c))("in"^((i))_(R)(vec(a)')) 
$

Upon evaluation, we can create a table for each $tilde("eq")_(vec(a))(vec(a)'),
tilde("eq")_(vec(b))("in"^((i))_(L)(vec(a)')),
tilde("eq")_(vec(c))("in"^((i))_(R)(vec(a)'))$ in $O(3 dot
2^(s_i)) = O(S_i)$ time, using @lem:linear-eq. Thus, an
evaluation of $tilde("add")_(i)(vec(a),vec(b),vec(c))$ or
$tilde("mul")_(i)(vec(a),vec(b),vec(c))$ is bounded by $O(S_i)$ time.

*Verifier Runtime:* $O(S_0 + d dot lg(S) + S + n)$

In each round, $verifier$ needs to do work roughly proportional to the
communication complexity, i.e. $O(d dot lg(S))$ across all rounds. Note that
$verifier$ does not evaluate each sumcheck polynomial fully in the final round
of sumcheck, as $v_(b'_i), v_(c'_i)$ are provided by $prover$. $verifier$
only needs to evaluate $tilde("add")(vec(a),vec(b),vec(c)),
tilde("mul")(vec(a),vec(b),vec(c))$ in each round. Let's say _all_
these evaluations throughout the protocol costs $t$. If $tilde("add"),
tilde("add")$ has no special structure for $verifier$ to exploit, we
can set $t = O(sum_(i=0)^d S_i) = O(S)$ following the discussion above. In the
final round, $verifier$ needs to evaluate $tilde(W)_(d)(vec(b)'_(d-1)),
tilde(W)_(d)(vec(c)'_(d-1))$. Both evaluations cost $2^(s_d) = n$ by
@lem:linear-eq. Then we get a verifier runtime of $O(S_0 + d dot lg(S) +
S + n)$.

*Prover Runtime*: $O(S^3)$

For each round of the GKR protocol, the dominant cost for $prover$ will always
be the sumcheck which was stated to be $O(2^ell dot T)$ in @sec:sumcheck. Where
$ell$ is the number of variables in each sumcheck polynomial $(2s_(i+1))$
and $T$ is the cost to evaluate the sumcheck polynomial at a single point. In
order to evaluate the sumcheck polynomial, $prover$ needs to evaluate
$tilde("add")_(i)(vec(a)'_(i-1), vec(b), vec(c)), tilde("mul")_(i)(vec(a)'_(i-1),
vec(b), vec(c)), tilde(W)_(i)(vec(b))$ and $tilde(W)_(i)(vec(b))$. It was
argued earlier that $tilde("add")_i, tilde("mul")_i$ could be evaluated in
$O(S_i)$ time. The polynomial $tilde(W)_i$ can be evaluated in $O(S_(i+1))$
using @lem:linear-eq, totaling $O(S_i + S_(i+1))$ to evaluate the sumcheck
polynomial at a single point.

Then $prover$'s runtime for each round in the GKR protocol is:

$
  O(2^ell dot T) &= O(2^(2s_(i+1)) dot T) \
                 &= O(2^(s_(i+1)) dot 2^(s_(i+1)) dot T) \
                 &= O(S_(i+1) dot S_(i+1) dot (S_i + S_(i+1))) \
                 &= O(S_(i+1)^3 + S_i S_(i+1)^2)
$

And the total runtime of $prover$ is:

$
  sum^(d-1)_(i=0) O(S_i S_(i+1)^2 + S_(i+1)^3) &= O(sum^(d-1)_(i=0) (S_i S_(i+1)^2 + S_(i+1)^3)) \
                                               &= O((sum^(d-1)_(i=0) S_(i+1))^3 + (sum^(d-1)_(i=0) S_(i+1))^2(sum^(d-1)_(i=0) S_(i))) \
                                               &= O((sum^(d)_(i=1) S_(i))^3 + (sum^(d)_(i=1) S_(i))^2(sum^(d-1)_(i=0) S_(i))) \
                                               &= O((sum^(d)_(i=0) S_(i))^3 + (sum^(d)_(i=0) S_(i))^2(sum^(d)_(i=0) S_(i))) \
                                               &= O(S^3)
$

== Soundness and Completeness<sec:gkr-soundness>

Given @lem:tilde-w-mle, @lem:multiple-evals-same-poly and the completeness
of the sumcheck protocol, it's easy to see that the GKR protocol is complete.

As for soundness, assume that $prover$ wants to cheat, and wishes to
convince $verifier$ that the output of $circuit$ when given input $vec(w)$
is $vec(y)'$, when it's actually $vec(y)$, i.e. $vec(y)' != vec(y)$ but the
verifier still accepts. This must then mean that $W' != W_0$.

Schwartz-Zippel states that the probability of $e(vec(x)) = tilde(W)'(vec(x)) -
tilde(W)_0(vec(x))$ evaluating to zero for a random input $r$ is bounded by
$frac(deg(E), |Fb|) = frac(s_0, |Fb|)$. Let's call this event $E_(W')$.

For each round in the sumcheck protocol $prover$ sends $g_j$ and the
verifier checks that $g_(j)(r_(j-1)) meq g_(j)(0) + g_(j)(1)$. This
has a $frac(deg(g_j), |Fb|)$ probability of cheating $verifier$ by
Schwartz-Zippel. The individual degree of $g_j$ is at most two, so we can write;
$frac(2, |Fb|)$. Call this event $E_j$.

For round zero in the GKR protocol:

$
  m_0 meq tilde("add")_0(vec(r), vec(b)'_0, vec(c)'_0) dot (v_(vec(b)'_0) + v_(vec(c)'_0)) + 
          tilde("mul")_0(vec(r), vec(b)'_0, vec(c)'_0) dot v_(vec(b)'_0) dot v_(vec(c)'_0)
$

Since all this computation (including $m_0$) is computed by $verifier$,
$prover$ can't cheat here, except in each round of the sumcheck, which
has already been covered. This assumes that $v_(vec(b)'_0), v_(vec(c)'_0)$
are indeed the correct evaluations, which is verified in the next round.

For each GKR round $i in [1..d-1]$, the probability that the check:

$
  m_i &meq &&(tilde("add")_(i)(vec(b)'_(i-1),vec(b)'_(i),vec(c)'_(i)) + alpha dot tilde("add")_(i)(vec(c)'_(i-1),vec(b)'_i,vec(c)'_i))(v_(vec(b)'_i) + v_(vec(c)'_i)) + \
      &    &&(tilde("mul")_(i)(vec(b)'_(i-1),vec(b)'_(i),vec(c)'_(i)) + alpha dot tilde("mul")_(i)(vec(c)'_(i-1),vec(b)'_i,vec(c)'_i))(v_(vec(b)'_i) dot v_(vec(c)'_i))
$

Passing without the statement holding is $frac(1,|Fb|)$ by
@lem:multiple-evals-same-poly, again provided that $v_(vec(b)'_(i)),
v_(vec(c)'_(i))$ are indeed the correct evaluations. Call this event $E_i$.

$prover$ can't cheat in the final round, as they cannot affect the
verifier's check.

We can union-bound these events to get a soundness bound.

$
  delta_s &= Pr[E_(W')] + union.big^(d-1)_(i=0) union.big^(s_i)_(j=0) Pr[E_j] + union.big^(d-1)_(i=1) Pr[E_i] \
          &<= frac(s_0, |Fb|) + sum^(d-1)_(i=0) sum^(s_i)_(j=0) frac(2, |Fb|) + sum^(d-1)_(i=1) frac(1, |Fb|) \
          &= frac(s_0, |Fb|) + sum^(d-1)_(i=0) s_i frac(2, |Fb|) + sum^(d-1)_(i=1) frac(1, |Fb|) \
          &= frac(s_0, |Fb|) + sum^(d-1)_(i=0) lg(S_i) frac(2, |Fb|) + sum^(d-1)_(i=1) frac(1, |Fb|) \
          &<= frac(lg(S), |Fb|) + sum^(d)_(i=0) frac(2 lg(S), |Fb|) + sum^(d)_(i=1) frac(1, |Fb|) \
          &= frac(lg(S), |Fb|) + frac(2 d lg(S), |Fb|) + frac(d, |Fb|) \
          &= frac(3 d lg(S) + d, |Fb|) \
$

Which is negligible in the size of the field.

