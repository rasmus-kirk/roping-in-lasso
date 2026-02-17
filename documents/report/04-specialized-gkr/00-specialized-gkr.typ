#import "../00-lib/header/lib.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

= A specialized GKR protocol <sec:specialized-gkr>

If we consider GKR for a specific circuit, then we can improve both the
runtime of the prover and verifier. Concretely, our goal is to end up with
an IP of the statement $y meq product_(i=1)^n w_i$, i.e. that the grand
product of the input values $vec(w)$ equals some value $y$. With a linear
prover $O(n)$ and a sublinear verifier (except for the final round which
takes $O(n)$ time) meaning that the verifier's runtime will be bounded by
$O(lg^2(n) + n)$.

== The Protocol

If we consider the circuit consisting of a binary tree of multiplication
gates as in @fig:example_circuit. We can present a simpler expression than that
of regular GKR:

$ tilde(W)_(i)(vec(a)) = sum_(b in bits^i) tilde("eq")(vec(a), vec(b)) dot tilde(W)_(i+1)(vec(b) || 0) dot tilde(W)_(i+1)(vec(b) || 1) $

It's clear that this expression is equivalent to the one from regular GKR,
but only for the binary tree of multiplication gates. Using
@lem:multiple-evals-same-poly we get the following polynomial:

$
  q(vec(r)_(i-1)) &= &&tilde(W)_(i+1)(vec(r)_(i-1) || 0) + alpha tilde(W)_(i+1)(vec(r)_(i-1) || 1) \
                  &= &&(sum_(vec(b) in bits^i) tilde("eq")_((vec(r)_(i-1) || 0))(vec(b)) dot tilde(W)_(i+1)(vec(b) || 0) dot tilde(W)_(i+1)(vec(b) || 1)) + \
                  &  &&(sum_(vec(b) in bits^i) alpha dot tilde("eq")_((vec(r)_(i-1) || 1))(vec(b)) dot tilde(W)_(i+1)(vec(b) || 0) dot tilde(W)_(i+1)(vec(b) || 1)) \
                  &= &&sum_(vec(b) in bits^i) (tilde("eq")_((vec(r)_(i-1) || 0))(vec(b)) + alpha dot tilde("eq")_((vec(r)_(i-1) || 1))(vec(b))) dot tilde(W)_(i+1)(vec(b) || 0) dot tilde(W)_(i+1)(vec(b) || 1)
$

Which means that our sumcheck polynomial is:

$
  f_(i)(vec(b)) = (tilde("eq")_((vec(r)_(i-1) || 0))(vec(b)) + alpha dot tilde("eq")_((vec(r)_(i-1) || 1))(vec(b))) dot tilde(W)_(i+1)(vec(b) || 0) dot tilde(W)_(i+1)(vec(b) || 1)
$

But what about round zero? Well, since round zero is always only a single
gate, the prover/verifier pair doesn't need to perform a sumcheck at all. The
prover can simply send $m_0 in bits$, the output of the circuit, along with the
evaluations of $tilde(W)_1(0), tilde(W)_1(1)$. Since checking these
evaluations recursively is already round one's job, we're still good:

$
  tilde(W)_0(x) &= sum_(b in bits^0) tilde("eq")(x, b) dot tilde(W)_(1)(b || 0) dot tilde(W)_(1)(b || 1) \
                &= tilde("eq")(x, ()) dot tilde(W)_(1)(() || 0) dot tilde(W)_(1)(() || 1) \
                &= tilde(W)_(1)(0) dot tilde(W)_(1)(1) \
$

We skip discussions of soundness and completeness as there's nothing notably
different from what was argued in @sec:gkr-soundness, but the full protocol
is still outlined below:

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
        hat(x) &:= (d)
      $)$])
    )

    P.at(1) += h/10; M.at(1) += h/10; V.at(1) += h/10;

    node(P, $#text(size: 12pt, $bold("Prover")(hat(x), vec(w))$)$)
    node(V, $#text(size: 12pt, $bold("Verifier")(hat(x), vec(w))$)$)
    P.at(1) += h/2; M.at(1) += h/2; V.at(1) += h/2; 

    // -------------------- Preprocessing -------------------- //
    node(M, $#text(size: 12pt, weight: "black", $"Preprocessing"$)$)
    edge(P, M, "=")
    edge(M, V, "=")
    P.at(1) += h/1.5; M.at(1) += h/1.5; V.at(1) += h/1.5; 

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      The prover sends evaluations $v^((0))_0, v^((0))_1$ claiming that $v^((0))_0 =
      tilde(W)_1(0), v^((0))_1 = tilde(W)_1(1)$ and thus $y = v^((0))_0 dot v^((0))_1$.
    ]))
    P.at(1) += h/1.5; M.at(1) += h/1.5; V.at(1) += h/1.5;

    node(P, $v^((0))_0 := tilde(W)_1(0), v^((0))_1 := tilde(W)_1(1)$)
    edge(P, V, "->", $v^((0))_0, v^((0))_1$)
    node(V, $ m_0 := v^((0))_0 dot v^((0))_1$)
    P.at(1) += h/2.4; M.at(1) += h/2.4; V.at(1) += h/2.4; 

    // -------------------- Round 1 -------------------- //
    node(M, $#text(size: 12pt, weight: "black", $"Round" 1$)$)
    edge(P, M, "=")
    edge(M, V, "=")
    P.at(1) += h/1.5; M.at(1) += h/1.5; V.at(1) += h/1.5; 

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      To verify the values $v^((0))_0, v^((0))_1$ from the
      previous round, $verifier$ picks out a randomly sampled value $alpha$
      and sends it to $prover$. $prover$ uses $alpha$ to construct the
      combined-claim polynomial, for which $prover$ and $verifier$ perform
      the sumcheck over:
      $
        f_(1)(vec(b)) &= (tilde("eq")_(0)(vec(b)) + alpha dot tilde("eq")_(1)(vec(b))) dot tilde(W)_(2)(vec(b) || 0) dot tilde(W)_(2)(vec(b) || 1)
      $
    ]))
    P.at(1) += h/1.3; M.at(1) += h/1.3; V.at(1) += h/1.3; 

    node(P, $f_(1)(vec(b))$)
    node(V, $ alpha inrand Fb $)
    edge(V, P, "->", $alpha$)
    P.at(1) += h/1.8; M.at(1) += h/1.8; V.at(1) += h/1.8; 

    edge(P, V, "<->", $sum_(vec(b) in bits^(1)) f_(1)(vec(b)) meq m_1$)
    P.at(1) += h/1.4; M.at(1) += h/1.4; V.at(1) += h/1.4;

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      At the end of the protocol, $prover$ sends $verifier$ the evaluations
      of $tilde(W)_(2)(vec(r)_1 || 0)$ and $tilde(W)_(2)(vec(r)_1 || 1)$, so
      $verifier$ can make the final check in the sumcheck protocol:
    ]))
    P.at(1) += h/1.2; M.at(1) += h/1.2; V.at(1) += h/1.2;

    node(P, $
      v^((1))_0 := tilde(W)_(2)(vec(r)_1 || 0), \
      v^((1))_1 := tilde(W)_(2)(vec(r)_1 || 1)
    $)
    node(V, $
      m_i &meq &&tilde("eq")_(0)(vec(r)_1) dot v^((1))_0 dot v^((1))_1 + \
          &    &&alpha dot tilde("eq")_(1)(vec(r)_1) dot v^((1))_0 dot v^((1))_1
    $)
    edge(P, V, "->", $v^((0))_0, v^((0))_1$)
    P.at(1) += h/2.4; M.at(1) += h/2.4; V.at(1) += h/2.4; 

    // -------------------- Round i -------------------- //
    node(M, $#text(size: 12pt, weight: "black", $"Round" i in [2..d-1]$)$)
    edge(P, M, "=")
    edge(M, V, "=")
    P.at(1) += h/1.5; M.at(1) += h/1.5; V.at(1) += h/1.5; 

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      To verify the values $v^((i-1))_0, v^((i-1))_1$ from the
      previous round, $verifier$ picks out a randomly sampled value $alpha$
      and sends it to $prover$. $prover$ uses $alpha$ to construct the
      combined-claim polynomial, for which $prover$ and $verifier$ perform
      the sumcheck over:

      $
        f_(i)(vec(b)) &= (tilde("eq")_((vec(r)_(i-1) || 0))(vec(b)) + alpha dot tilde("eq")_((vec(r)_(i-1) || 1))(vec(b))) dot tilde(W)_(i+1)(vec(b) || 0) dot tilde(W)_(i+1)(vec(b) || 1)
      $
    ]))
    P.at(1) += h/1.4; M.at(1) += h/1.4; V.at(1) += h/1.4; 

    node(P, $f_(i)(vec(b))$)
    node(V, $ alpha inrand Fb $)
    edge(V, P, "->", $alpha$)
    P.at(1) += h/2.0; M.at(1) += h/2.0; V.at(1) += h/2.0; 

    edge(P, V, "<->", $sum_(vec(b), vec(c) in bits^i) f^(i)(vec(b)) meq m_i$)
    P.at(1) += h/2.0; M.at(1) += h/2.0; V.at(1) += h/2.0;

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      At the end of the protocol, $prover$ sends $verifier$ the evaluations
      of $tilde(W)_(2)(vec(r)_i || 0)$ and $tilde(W)_(2)(vec(r)_i ||
      0)$, so $verifier$ can make the final check in the sumcheck protocol:
    ]))
    P.at(1) += h/1.2; M.at(1) += h/1.2; V.at(1) += h/1.2;

    node(P, $
      v^((i))_0 &:= tilde(W)_(i+1)(vec(r)_i || 0), \
      v^((i))_1 &:= tilde(W)_(i+1)(vec(r)_i || 1)
    $)
    node(V, $
      m_i &meq &&tilde("eq")_((vec(r)_(i-1) || 0))(vec(r)_i) dot v^((i))_0 dot v^((i))_1 + \
          &    &&alpha dot tilde("eq")_((vec(r)_(i-1) || 1))(vec(r)_i) dot v^((i))_0 dot v^((i))_1
    $)
    edge(P, V, "->", $v^((i))_0, v^((i))_1$)
    P.at(1) += h/1.5; M.at(1) += h/1.5; V.at(1) += h/1.5; 

    // -------------------- Round d -------------------- //
    node(M, $#text(size: 12pt, weight: "black", $"Round" d$)$)
    edge(P, M, "=")
    edge(M, V, "=")
    P.at(1) += h/1.6; M.at(1) += h/1.6; V.at(1) += h/1.6;

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      At the input layer $d$, $verifier$ has two claims. $verifier$ constructs
      $tilde(W)_d$ from $vec(w)$ and perform a final check.
    ]))
    P.at(1) += h/1.5; M.at(1) += h/1.5; V.at(1) += h/1.5; 

    node(V, $
      v^((d-1))_0 &meq tilde(W)_(d)(r_(d-1) || 0) and \
      v^((d-1))_1 &meq tilde(W)_(d)(r_(d-1) || 1)
    $)
  })
]

== Efficiency

We reuse the same trick as in @cor:linear-mle, by computing tables for
each term and product in the sumcheck polynomials in and using them to
evaluate $f_(i)$ in round $j$ of the sumcheck protocol. Crucially, we
need to construct the tables required to evaluate $f_(i)$ in round $j$
of the sumcheck protocol in $O(2^(i-j))$ time.

=== Computing $tilde("eq")$ in linear time<sec:computing-eq-linear>

For round $i$ of the GKR protocol, in round $j$ in the sumcheck invocation,
we want to evaluate $f_(i)$ at $vec(x) = ( r_1, ..., r_j, t,
b_(j+2), ..., b_(s_i) )$, with $t = {0, 1, 2, 3}$:

$
  f_(i)(vec(x)) &= (tilde("eq")_((vec(r)_(i-1) || 0))(vec(x)) + alpha dot tilde("eq")_((vec(r)_(i-1) || 1))(vec(x))) dot tilde(W)_(i+1)(vec(vec(x))) dot tilde(W)_(i+1)(vec(vec(x)))
$

Let $vec(v) = vec(r)_(i-1) || 0$ for $tilde("eq")_((vec(r)_(i-1) || 0))$, $vec(v)
= vec(r)_(i-1) || 1$ for $tilde("eq")_((vec(r)_(i-1) || 1))$ and $ell := |vec(v)| = i$.
Then the definition of $tilde("eq")_vec(v)$ is:

$ tilde("eq")_vec(v)(vec(b)) = product^(j)_(k=1) (v_k r_k + (1 - v_k) (1 - r_k)) dot product^(ell)_(k=j+1) (v_k b_k + (1 - v_k) (1 - b_k)) $

With the $r_1, ..., r_j$'s set by the verifier, as required by
the sumcheck protocol. Now, $prover$ needs an evaluation table of
$tilde("eq")_vec(v)((b_(j+1), dots, b_(ell)))$ for each round in
the sumcheck protocol. In round zero, $prover$ can compute the table,
$hat("eq")^((0))$ by leveraging @lem:linear-eq in $O(2^(ell))$
time. Then in round $j$, $prover$ can compute the evaluation table of
$tilde("eq")^((j))_vec(v)$ using the following recurrence:

$
  hat("eq")_(j)[(b_(j+1), ..., b_(ell))] = v_j^(-1) dot hat("eq")_(j-1)[(1, b_(j+1), ..., b_(ell))] dot v_j r_j + (1 - v_j) (1 - r_j)
$<eq:eq-hat>

#remark[
  If $v_j = 0$ then this process won't work. To circumvent this, $verifier$
  can instead sample each $v_j$ from $Fb^*$ with only negligible soundness
  overhead.
]

In $O(2^(ell - j))$ time. To see why, we can inspect the expression
$hat("eq")_(j-1)[(1, b_(j+1), ..., b_(ell))]$:

$
  hat("eq")_(j-1)[(1, b_(j+1), ..., b_(ell))] &= &&( product^(j-1)_(k=1) (v_k r_k + (1 - v_k) (1 - r_k)) ) dot \
                                              &  &&( v_(j) dot 1 + (1 - v_(j)) dot (1 - 1) ) dot \
                                              &  &&( product^(ell)_(k=j+2) (v_k b_k + (1 - v_k) (1 - b_k)) ) \
                                              &= &&v_j dot ( product^(j-1)_(k=1) (v_k r_k + (1 - v_k) (1 - r_k) )) dot ( product^(ell)_(k=j+2) (v_k b_k + (1 - v_k) (1 - b_k)) )
$

So, substituting back into @eq:eq-hat, we get:

$ hat("eq")_(j)[(b_(j+1), ..., b_(ell))] = ( product^(j)_(k=1) (v_k r_k + (1 - v_k) (1 - r_k)) ) dot ( product^(ell)_(k=j+1) (v_k b_k + (1 - v_k) (1 - b_k)) ) $

As expected. This process works for both $tilde("eq")_((vec(r)_(i-1) || 0))$ and $tilde("eq")_((vec(r)_(i-1) || 1))$.

=== Computing $tilde(W)$ in linear time <sec:computing-w-linear>

*Constructing the lookup table:*

Note that in round zero of the sumcheck, the prover already has a lookup
table of $hat(W)_(0)$:

$
  hat(W)_(0)[vec(x) in bits^ell] := W_(i+1)(vec(x))
$

Where $ell = i+1$. Define $hat(W)_(j)$ such that:

$
  hat(W)_(j)[(x_(j+1), ..., x_ell)] = tilde(W)_(i+1)(r_1, ..., r_j, x_(j+1), ..., x_ell)
$<eq:w-lookup-base-case>

Assuming $prover$ already have $hat(W)_(j-1)$, they can compute $hat(W)_(j)$:

$
  hat(W)_(j)[(x_(j+1), ..., x_ell)] := tilde("eq")_0(r_j) dot hat(W)_(j-1)[(0, x_(j+1), ..., x_ell)] + tilde("eq")_1(r_j) dot hat(W)_(j-1)[(1, x_(j+1), ..., x_ell)]
$

In $O(2^(ell-j)) = O(2^(i+1-j)) = O(2^(i-j))$ time.

*Using the lookup table:*

Once the prover has a $hat(W)_(j-1)$ lookup table, they can compute $tilde("W")^((j-1))(r_1, ..., r_(j-1), t, x_(j+1), ..., x_(ell))$:

$
  tilde(W)(r_1, ..., r_(j-1), t, x_(j+1), ..., x_(ell)) &= &&sum_(vec(b) in bits^ell) tilde("eq")(r_1, ..., r_(j-1), t, x_(j+1), ..., x_(ell), vec(b)) dot W_(i+1)(vec(b)) \
                                                        &= &&sum_(vec(b) in bits^ell) tilde("eq")_vec(r)(b_1, ..., b_(j-1)) dot tilde("eq")_(t)(b_j) dot tilde("eq")_vec(x)(b_(j+1), ..., b_ell) dot W_(i+1)(vec(b)) \
                                                        &= &&sum_(vec(b) in bits^ell) tilde("eq")_vec(r)(b_1, ..., b_(j-1)) dot tilde("eq")_(t)(b_j) dot W_(i+1)(b_1, ..., b_j, x_(j+1), ..., x_ell) \
                                                        &= &&sum_(vec(b) in bits^ell) tilde("eq")_vec(r)(b_1, ..., b_(j-1)) dot tilde("eq")_(0)(b_j) dot W_(i+1)(b_1, ..., b_j, x_(j+1), ..., x_ell) + \
                                                        &  &&sum_(vec(b) in bits^ell) tilde("eq")_vec(r)(b_1, ..., b_(j-1)) dot tilde("eq")_(1)(b_j) dot W_(i+1)(b_1, ..., b_j, x_(j+1), ..., x_ell)   \
                                                        &= &&hat(W)_(j-1)[(0,x_(j+1), ..., x_ell)] dot tilde("eq")_0(t) + hat(W)_(j-1)[(1,x_(j+1), ..., x_ell)] dot tilde("eq")_1(t) \
$

In constant time.

=== Putting it all together

*Communication:* $O(lg^2(n))$

As argued in @sec:gkr-efficiency, for each round in the GKR protocol
the dominating communication cost is a sumcheck with $O(sum^(i)_(j=1)
deg_(j)(f_(i)))$ communication. Since $deg_(j)(f_(i))$ is constant,
there is $O(i)$ communication. Across all rounds we have

$ O(sum^(d-1)_(i=1) i) = O(frac(d(d+1), 2)) = O(d^2) = O(lg^2(n)) $

*Prover runtime:* $O(n)$

In the above subsections, we established that the prover can compute
$hat("eq")_(j)$ (for both $tilde("eq")_((vec(r)_(i-1) || 0))$ and
$tilde("eq")_((vec(r)_(i-1) || 1))$) and $ hat(W)_(j)$ in $O(2^(i-j))$
time. Then the prover can use them to evaluate:

$
  f_(i)(vec(b)) &= (tilde("eq")_((vec(r)_(i-1) || 0))(vec(b)) + alpha dot tilde("eq")_((vec(r)_(i-1) || 1))(vec(b))) dot tilde(W)_(i+1)(vec(b) || 0) dot tilde(W)_(i+1)(vec(b) || 1)
$

With $vec(b) = (r_1, ..., r_(j-1), t, x_(j+1), ..., x_(s_i))$ in constant
time. Thus, the prover spends $O(3 dot 2^(i - j))$ time in each round of
the sumcheck protocol. For all rounds of the sumcheck protocol is
$O(sum^(i)_(j=1) 2^(i - j)) = O(2^(s_i) - 1) = O(2^i)$.

As argued in the sumcheck section, the dominating runtime of the prover in
GKR is dedicated to the sumchecks. Since we have a binary tree of gates,
$n = 2^d$. Now we can compute the prover runtime:

$
  O(sum^d_(i=0) 2^i) = O(2^(d+1)) = O(2^d) = O(n)
$

*Verifier runtime:* $O(lg^2(n) + n)$

As argued in @sec:gkr-efficiency, the verifier workload is proportional to
the communication cost $O(lg^2(n))$, plus an evaluation of the input layer $O(n)$, plus
all the evaluations of $tilde("add"), tilde("mul")$ ($O(t)$). Evaluating
$tilde("add"), tilde("mul")$ is just evaluating $tilde("eq")$, which as
argued in @sec:mle, can be done in $O(ell) = O(i)$ time. This gives us:

$ O(lg^2(n) + t + n) &= O(lg^2(n) + sum^(d-1)_(i=1) i + n) = O(lg^2(n) + lg^2(n) + n) = O(lg^2(n) + n) $


