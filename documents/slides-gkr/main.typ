#import "./00-lib/lib.typ": *
#import "@preview/fletcher:0.5.8": *
#import "@preview/polylux:0.4.0": *

#show: setup

#let graph-text-size = 18pt

#slide[
  #set page(header: none, footer: none, margin: 3em)

  #text(size: 1.3em)[
    *Succinct Proofs*
  ]

  GKR

  #divider
  
  #set text(size: .8em, weight: "light")
  Rasmus Kirk Jakobsen

  #datetime.today().display()
]

#slide[
  = Agenda

  #outline
]

#new-section[The GKR Protocol]

#slide[
  = GKR Circuit

  Layered arithmetic circuit $circuit(vec(w) in Fb^n) = vec(y) in Fb^m$
  - Only addition and multiplication gates
  - $n$ inputs
  - $m$ outputs,
  - $d$ layers
]

#slide[
    = Example

    $ S_0 = 1, S_1 = 2, S_2 = 4, s_i = lg(S_i), n = 4, m = 1, d = 3 $

    #align(center)[
      #set math.equation(numbering: none)
      #set text(graph-text-size)
      #let w = 0.8
      #let h = 0.8
      #diagram(
        node-stroke: 1pt,
        {
          let O = (3*w, -1*h)
          let N00 = (3*w, 0*h)
          let (N10, N11) = ((1*w, 1*h), (5*w, 1*h))
          let (N20, N21, N22, N23) = (
            (0*w, 2*h),
            (2*w, 2*h),
            (4*w, 2*h),
            (6*w, 2*h),
          )
          let (N30, N31, N32, N33) = (
            (0*w, 3*h),
            (2*w, 3*h),
            (4*w, 3*h),
            (6*w, 3*h),
          )

          // Really hacky centering lol
          node((8.0*w, 0*h), "", stroke: none)
          node((-1.2*w, -1*h), "Outputs")
          node((-1.2*w, 0*h), "Layer 0")
          node((-1.2*w, 1*h), "Layer 1")
          node((-1.2*w, 2*h), "Layer 2")
          node((-1.2*w, 3*h), "Inputs")
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
    ]
]

#slide[
  = Polynomial Extension of $W_i$

  $
    W_(i)(vec(a)) &in bits^(s_i) -> Fb \
    "add"_(i)(vec(a),vec(b),vec(c)) &in bits^(s_i+2s_(i+1)) -> bits \
    "mul"_(i)(vec(a),vec(b),vec(c)) &in bits^(s_i+2s_(i+1)) -> bits \
  $

  #show: later

  $ tilde(W)_(i)(vec(a)) = sum_(vec(b),vec(c) in bits^(s_(i+1))) &tilde("add")_(i)(vec(a),vec(b),vec(c))(tilde(W)_(i+1)(vec(b)) + tilde(W)_(i+1)(vec(c))) + \
                                                                 &tilde("mul")_(i)(vec(a),vec(b),vec(c)) dot tilde(W)_(i+1)(vec(b)) dot tilde(W)_(i+1)(vec(c)) $
]

#slide[
  = Proving the Output of the Circuit

  - Prover claims output of circuit is $vec(y)' tilde.equiv W'$
  - Actual output is $vec(y) tilde.equiv W_0$

  #show: later

  $ vec(r) inrand Fb^(s_0) : tilde(W)'(vec(r)) = tilde(W)_0(vec(r)) ==> tilde(W)' = tilde(W)_0 ==> W' = W_0 $
]

#slide[
  = Sumcheck

  $ tilde(W)_(0)(vec(r)) = sum_(vec(b),vec(c) in bits^(s_(1))) &tilde("add")_(0)(vec(r),vec(b),vec(c))(tilde(W)_(1)(vec(b)) + tilde(W)_(1)(vec(c))) + \
                                                               &tilde("mul")_(0)(vec(r),vec(b),vec(c)) dot tilde(W)_(1)(vec(b)) dot tilde(W)_(1)(vec(c)) $

  #show: later

  == Sumcheck polynomial

  $ f_(0)(vec(b), vec(c)) = tilde("add")_(0)(vec(r),vec(b),vec(c))(tilde(W)_1(vec(b)) + tilde(W)_1(vec(c))) + tilde("mul")_(0)(vec(r),vec(b),vec(c)) dot tilde(W)_1(vec(b)) dot tilde(W)_1(vec(c)) $

  #show: later

  == Last round of sumcheck

  $
    vec(b)'_1, vec(c)'_1 &inrand &&Fb^(s_(i+1)) \
    f_(0)(vec(b)'_1, vec(c)'_1) &= &&tilde("add")_(0)(vec(r),vec(b)'_1,vec(c)'_1)(tilde(W)_1(vec(b)'_1) + tilde(W)_1(vec(c)'_1)) + \
                                &  &&tilde("mul")_(0)(vec(r)'_0,vec(b)'_1,vec(c)'_1) dot tilde(W)_1(vec(b)'_1) dot tilde(W)_1(vec(c)'_1)
  $
]

#slide[
  = Idea: Verify Evaluations using Sumcheck

  $
    f_(1)(vec(b), vec(c)) &= tilde("add")_(1)(vec(b)'_0,vec(b),vec(c))(tilde(W)_2(vec(b)) + tilde(W)_2(vec(c))) + tilde("mul")_(1)(vec(b)'_1,vec(b),vec(c)) dot tilde(W)_2(vec(b)) dot tilde(W)_2(vec(c)) \
    f_(1)(vec(b), vec(c)) &= tilde("add")_(1)(vec(c)'_0,vec(b),vec(c))(tilde(W)_2(vec(b)) + tilde(W)_2(vec(c))) + tilde("mul")_(1)(vec(c)'_1,vec(b),vec(c)) dot tilde(W)_2(vec(b)) dot tilde(W)_2(vec(c))
  $
]

#slide[
  #show: focus
  Exponential!
]

#slide[
  #show math.equation: set text(18pt)
  = Combining two claims to one
  $
    q(vec(b)'_0, vec(c)'_0) &= &&tilde(W)_(1)(vec(b)'_0) + alpha dot tilde(W)_(1)(vec(c)'_0) \
                            &= &&(sum_(vec(b),vec(c) in bits^(s_(2))) tilde("add")_(1)(vec(b)'_0,vec(b),vec(c))(tilde(W)_(2)(vec(b)) + tilde(W)_(2)(vec(c))) + tilde("mul")_(1)(vec(b)'_0,vec(b),vec(c)) dot tilde(W)_(2)(vec(b)) dot tilde(W)_(2)(vec(c))) + \
                            &  &&alpha dot (sum_(b,c in bits^(s_(2))) tilde("add")_(1)(vec(c)'_0,vec(b),vec(c))(tilde(W)_(2)(vec(b)) + tilde(W)_(2)(vec(c))) + tilde("mul")_(1)(vec(c)'_0,vec(b),vec(c)) dot tilde(W)_(2)(vec(b)) dot tilde(W)_(2)(vec(c))) \
                            &= &&sum_(vec(b),vec(c) in bits^(s_(2))) tilde("add")_(1)(vec(b)'_0,vec(b),vec(c))(tilde(W)_(2)(vec(b)) + tilde(W)_(2)(vec(c))) + tilde("mul")_(1)(vec(b)'_0,vec(b),vec(c)) dot tilde(W)_(2)(vec(b)) dot tilde(W)_(2)(vec(c)) + \
                            &  &&alpha dot tilde("add")_(1)(vec(c)'_0,vec(b),vec(c))(tilde(W)_(2)(vec(b)) + tilde(W)_(2)(vec(c))) + alpha dot tilde("mul")_(1)(vec(c)'_0,vec(b),vec(c)) dot tilde(W)_(2)(vec(b)) dot tilde(W)_(2)(vec(c)) \
                            &= &&sum_(vec(b),vec(c) in bits^(s_(2))) (tilde("add")_(1)(vec(b)'_0,vec(b),vec(c)) + alpha dot tilde("add")_(1)(vec(c)'_0,vec(b),vec(c)))(tilde(W)_(2)(vec(b)) + tilde(W)_(2)(vec(c))) + \
                            &  &&(tilde("mul")_(1)(vec(b)'_0,vec(b),vec(c)) + alpha dot tilde("mul")_(1)(vec(c)'_0,vec(b),vec(c)))(tilde(W)_(2)(vec(b)) dot tilde(W)_(2)(vec(c)))
  $
]

#slide[
  = Combining two claims to one

  *We have:*
  $
    v_1 &:= p(vec(r)_1), v_2 := p(vec(r)_2) \
    q(X_1, .., X_(2ell)) &:= p(X_1, ..., X_ell) + alpha dot p(X_(ell+1), ..., X_(2ell)g) \
    q(vec(r)_1, vec(r)_2) &meq v_1 + alpha dot v_2
  $

  #show: later

  *Proof:* Assume $v_1 &!= p(vec(r)_1) or v_2 != p(vec(r)_2)$, but $q$ is defined as above:
  $
    e(X) &= v_1 + X dot v_2 - (p(vec(r)_1) + X dot p(vec(r)_2)) \
    Pr[e(alpha) &= 0 | e(X) != 0] = frac(deg(e), |Fb|) = frac(1, |Fb|)  
  $
]

#slide[
  = Combining two claims to one

  *The next round we sumcheck:*

  $
    f_(1)(vec(b), vec(c)) &:= &&(tilde("add")_(1)(vec(b)'_0,vec(b),vec(c)) + alpha dot tilde("add")_(1)(vec(c)'_0,vec(b),vec(c)))(tilde(W)_(2)(vec(b)) + tilde(W)_(2)(vec(c))) + \
                          &   &&(tilde("mul")_(1)(vec(b)'_0,vec(b),vec(c)) + alpha dot tilde("mul")_(1)(vec(c)'_0,vec(b),vec(c)))(tilde(W)_(2)(vec(b)) dot tilde(W)_(2)(vec(c)))
  $

  #show: later

  *And the verifier checks:*

  $
    m_i &meq &&(tilde("add")_(i)(vec(b)'_(i-1),vec(b)'_(i),vec(c)'_(i)) + alpha dot tilde("add")_(i)(vec(c)'_(i-1),vec(b)'_i,vec(c)'_i))(v_(vec(b)'_i) + v_(vec(c)'_i)) + \
        &    &&(tilde("mul")_(i)(vec(b)'_(i-1),vec(b)'_(i),vec(c)'_(i)) + alpha dot tilde("mul")_(i)(vec(c)'_(i-1),vec(b)'_i,vec(c)'_i))(v_(vec(b)'_i) dot v_(vec(c)'_i))
  $
]

#let zero-width-box(body) = context {
  let width = 35em
  let (height,) = measure(width: width, body)
  place(center + horizon, box(width: width, height: height, body))
  box(width: 0%, height: 2 * height)
}

#slide[
  = Full Protocol: Preprocessing

  #align(center)[
    #set text(graph-text-size)
    #let w = 1
    #let h = 1

    #diagram(debug: 0, {
      let (P, M, V) = ((0, 0), (1.5, 0), (3, 0))

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
  })]
]

#slide[
  = Full Protocol: Round zero

  #align(center)[
    #set text(graph-text-size)
    #let w = 0.7
    #let h = 0.7

    #diagram(debug: 0, {
      let (P, M, V) = ((0, 0), (1.5, 0), (3, 0))

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      $ f_(0)(vec(b), vec(c)) = tilde("add")_(0)(vec(r),vec(b),vec(c))(tilde(W)_1(vec(b)) + tilde(W)_1(vec(c))) + tilde("mul")_(0)(vec(r),vec(b),vec(c)) dot tilde(W)_1(vec(b)) dot tilde(W)_1(vec(c)) $
    ]))
    P.at(1) += h/1; M.at(1) += h/1; V.at(1) += h/1;

    // node(P, $ f_(0)_(r)(b', c')$)
    edge(P, V, "<->", $sum_(vec(b), vec(c) in bits^(s_1)) f_(0)(vec(b), vec(c)) meq m_0$)
    P.at(1) += h/1.3; M.at(1) += h/1.3; V.at(1) += h/1.3; 

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      At the end of the protocol, $prover$ sends $verifier$ the evaluations
      of $v_(vec(b)'_0) := tilde(W)_1(vec(b)'_0)$ and $v_(vec(c)'_0) := tilde(W)_1(vec(c)'_0)$, so
      $verifier$ can make the final check in the sumcheck protocol.
    ]))
    P.at(1) += h/1; M.at(1) += h/1; V.at(1) += h/1;

    node(P, $v_(vec(b)'_0) := tilde(W)_1(vec(b)'_0), v_(vec(c)'_0) := tilde(W)_1(vec(c)'_0)$)
    node(V, $
      m_0 meq &tilde("add")_0(vec(r), vec(b)'_0, vec(c)'_0) dot (v_(vec(b)'_0) + v_(vec(c)'_0)) + \
              &tilde("mul")_0(vec(r), vec(b)'_0, vec(c)'_0) dot v_(vec(b)'_0) dot v_(vec(c)'_0)
    $)
    edge(P, V, "->", $v_(vec(b)'_0), v_(vec(c)'_0)$)
  })]
]

#slide[
  = Full Protocol: Round $i$

  #align(center)[
    #set text(graph-text-size)
    #let w = 0.7
    #let h = 0.7

    #diagram(debug: 0, {
      let (P, M, V) = ((0, 0), (1.5, 0), (3, 0))

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      $
        f_(i)(vec(b), vec(c)) &:= &&(tilde("add")_(i)(vec(b)'_(i-1),vec(b),vec(c)) + alpha dot tilde("add")_(i)(vec(c)'_(i-1),vec(b),vec(c)))(tilde(W)_(i+1)(vec(b)) + tilde(W)_(i+1)(vec(c))) + \
                              &   &&(tilde("mul")_(i)(vec(b)'_(i-1),vec(b),vec(c)) + alpha dot tilde("mul")_(i)(vec(c)'_(i-1),vec(b),vec(c)))(tilde(W)_(i+1)(vec(b)) dot tilde(W)_(i+1)(vec(c)))
      $
    ]))
    P.at(1) += h/1.8; M.at(1) += h/1.8; V.at(1) += h/1.8; 

    node(P, $f_(i)(vec(b), vec(c))$)
    node(V, $ alpha inrand Fb $)
    edge(V, P, "->", $alpha$)
    P.at(1) += h/2.1; M.at(1) += h/2.1; V.at(1) += h/2.1; 

    edge(P, V, "<->", $sum_(vec(b), vec(c) in bits^(s_(i+1))) f_(i)(vec(b), vec(c)) meq m_i$)
    P.at(1) += h/2.1; M.at(1) += h/2.1; V.at(1) += h/2.1;

    node(M, inset: 0em, zero-width-box(text(theme.fg2)[
      $
        m'_i &:= &&(tilde("add")_(i)(vec(b)'_(i-1),vec(b)'_(i),vec(c)'_(i)) + alpha dot tilde("add")_(i)(vec(c)'_(i-1),vec(b)'_i,vec(c)'_i))(v_(vec(b)'_i) + v_(vec(c)'_i)) + \
             &   &&(tilde("mul")_(i)(vec(b)'_(i-1),vec(b)'_(i),vec(c)'_(i)) + alpha dot tilde("mul")_(i)(vec(c)'_(i-1),vec(b)'_i,vec(c)'_i))(v_(vec(b)'_i) dot v_(vec(c)'_i))
      $
    ]))
    P.at(1) += h/1.2; M.at(1) += h/1.2; V.at(1) += h/1.2;

    node(P, $
      v_(vec(b)'_i) &:= tilde(W)_(i+1)(vec(b)'_i), \
      v_(vec(c)'_i) &:= tilde(W)_(i+1)(vec(c)'_i)
    $)
    node(V, $m_i meq m'_i$)
    edge(P, V, "->", $v_(vec(b)'_i), v_(vec(c)'_i)$)
  })]
]

#slide[
  = Full Protocol: Round $d$

  #align(center)[
    #set text(graph-text-size)
    #let w = 0.7
    #let h = 0.7

    #diagram(debug: 0, {
      let (P, M, V) = ((0, 0), (1.5, 0), (3, 0))

      node(M, inset: 0em, zero-width-box(text(theme.fg2)[
        At the input layer $d$, $verifier$ has two claims $v_(vec(b)'_(d-1))$
        and $v_(vec(c)'_(d-1))$. $verifier$ constructs $tilde(W)_d$
        from $vec(w)$. $verifier$ then finally checks that
        $tilde(W)_(d)(vec(b)'_(d-1)) meq v_(vec(b)'_(d-1))$ and
        $tilde(W)_(d)(vec(c)'_(d-1)) meq v_(vec(c)'_(d-1))$.
      ]))
      P.at(1) += h/1; M.at(1) += h/1; V.at(1) += h/1; 
    
      node(P, "                          ")
      node(V, $
        tilde(W)_(d)(vec(b)'_(d-1)) &meq v_(vec(b)'_(d-1)) and \
        tilde(W)_(d)(vec(c)'_(d-1)) &meq v_(vec(c)'_(d-1))
      $)
      P.at(1) += h; M.at(1) += h; V.at(1) += h; 
  })]
]

#new-section[Soundness]

#slide[
  = Soundness: Checks

  == Preprocessing:
  - *Check* $tilde(W)' meq tilde(W)_0$
  - *Soundness Error:* $frac(style: "horizontal", s_0, |Fb|)$

  #show: later

  == Sumcheck Round $j$:
  - *Check* $f^((j))_(i)(r_(j-1)) meq f^((j))_(i)(0) + f^((j))_(i)(1)$
  - *Soundness Error:* $frac(style: "horizontal", deg(f^((j))_(i)), |Fb|) = frac(style: "horizontal", 2, |Fb|)$

  #show: later

  == GKR Round $i$:
  - *Check:* $m_i meq m'_i$
  - *Soundness Error:* $frac(1,|Fb|)$
]

#slide[
  = Soundness Bound

  $
    delta_s &= Pr[E_(W')] + union.big^(d-1)_(i=0) union.big^(s_i)_(j=0) Pr[E_j] + union.big^(d-1)_(i=1) Pr[E_i] \
            &<= frac(s_0, |Fb|) + sum^(d-1)_(i=0) sum^(s_i)_(j=0) frac(2, |Fb|) + sum^(d-1)_(i=1) frac(1, |Fb|) \
            &= frac(s_0, |Fb|) + sum^(d-1)_(i=0) s_i frac(2, |Fb|) + sum^(d-1)_(i=1) frac(1, |Fb|) \
            &<= frac(lg(S), |Fb|) + sum^(d)_(i=0) frac(2 lg(S), |Fb|) + sum^(d)_(i=1) frac(1, |Fb|) \
            &= frac(3 d lg(S) + d, |Fb|) \
  $
]

#new-section[Efficiency]

#slide[
  = Efficiency: Communication $O(S_0 + d dot lg(S))$

  - *Preprocessing:* $W'$, which has size $2^(s_0) = S_0$.
  - *Round $i$:* $O(s_(i+1))$
    - One sumcheck: $O(sum^(2 s_(i+1))_(j=1) deg_(j)(f^((j))_(i))) = O(s_(i+1))$

  #show: later

  $ O(S_0 + sum^(d-1)_(i=0) s_(i+1)) = O(S_0 + sum^(d-1)_(i=0) lg(S_i)) = O(S_0 + d dot lg(S)) $
]

#slide[
  = Efficiency: Verifier $O(S_0 + d dot lg(S) + S + n)$

  - Proportional to communication cost: $O(S_0 + d dot lg(S))$
  - Evaluating $tilde("add"), tilde("mul")$: $O(t)$ (bounded by $O(S)$)
  - The input layer: $O(n)$

  #show: later

  $ O(S_0 + d dot lg(S) + t + n) = O(S_0 + d dot lg(S) + S + n) $
]

#slide[
  = Efficiency: Prover $O(S^3)$

  == Efficiency: Prover Runtime per Sumcheck
  $
    O(2^ell dot T) &= O(2^(2s_(i+1)) dot T) \
                   &= O(S_(i+1)^2 dot (S_i + S_(i+1))) \
                   &= O(S_(i+1)^3 + S_i S_(i+1)^2)
  $

  #show: later

  == Efficiency: Prover Total
  $ O(sum^(d-1)_(i=0) (S_i S_(i+1)^2 + S_(i+1)^3)) = O(S^3) $
]

#new-section[Need for Speed - A GKR-Based Grand Product Proof]

#slide[
    = The Grand Product Proof

    #align(center)[
      #set math.equation(numbering: none)
      #set text(graph-text-size)
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
          node((-1.2*w, 0*h), "Layer 0")
          node((-1.2*w, 1*h), "Layer 1")
          node((-1.2*w, 2*h), "Layer 2")
          node(N00, [$times_(0)$], radius: 1.2em)
          node(N10, [$times_(0)$], radius: 1.2em)
          node(N11, [$times_(1)$], radius: 1.2em)
          node(N20, [$times_(00)$], radius: 1.2em)
          node(N21, [$times_(01)$], radius: 1.2em)
          node(N22, [$times_(10)$], radius: 1.2em)
          node(N23, [$times_(11)$], radius: 1.2em)
          edge(N10, N00, "-|>")
          edge(N11, N00, "-|>")
          edge(N20, N10, "-|>")
          edge(N21, N10, "-|>")
          edge(N22, N11, "-|>")
          edge(N23, N11, "-|>")
        }
      )
    ]

    #show: later

    $
      tilde(W)_(i)(vec(a)) = sum_(b in bits^i) tilde("eq")(vec(a), vec(b)) dot tilde(W)_(i+1)(vec(b) || 0) dot tilde(W)_(i+1)(vec(b) || 1) \
      s_i = i, #h(3em) S_i = 2^i
    $

    #show: later

    $
      S = sum_(i=0)^(d) 2^i = 2^(d+1) - 1 = 2n - 1
    $
]

#slide[
  = The Sumcheck Polynomial

  $
    q(vec(r)_(i-1)) &= &&tilde(W)_(i+1)(vec(r)_(i-1) || 0) + alpha tilde(W)_(i+1)(vec(r)_(i-1) || 1) \
                    &= &&(sum_(vec(b) in bits^i) tilde("eq")_((vec(r)_(i-1) || 0))(vec(b)) dot tilde(W)_(i+1)(vec(b) || 0) dot tilde(W)_(i+1)(vec(b) || 1)) + \
                    &  &&(sum_(vec(b) in bits^i) alpha dot tilde("eq")_((vec(r)_(i-1) || 1))(vec(b)) dot tilde(W)_(i+1)(vec(b) || 0) dot tilde(W)_(i+1)(vec(b) || 1)) \
                    &= &&sum_(vec(b) in bits^i) (tilde("eq")_((vec(r)_(i-1) || 0))(vec(b)) + alpha dot tilde("eq")_((vec(r)_(i-1) || 1))(vec(b))) dot tilde(W)_(i+1)(vec(b) || 0) dot tilde(W)_(i+1)(vec(b) || 1)
  $

  #show: later

  *Sumcheck Polynomial:*
  $
    f_(i)(vec(b)) = (tilde("eq")_((vec(r)_(i-1) || 0))(vec(b)) + alpha dot tilde("eq")_((vec(r)_(i-1) || 1))(vec(b))) dot tilde(W)_(i+1)(vec(b) || 0) dot tilde(W)_(i+1)(vec(b) || 1)
  $
]

#slide[
  = Round Zero? 

  #align(center)[
    *What about round zero? There's only a single gate.*
  ]

  $$
  #show: later

  #align(center)[
    *We simply skip it!*
  ]

  $$
  #show: later

  $
    tilde(W)_0(x) &= sum_(b in bits^0) tilde("eq")(x, b) dot tilde(W)_(1)(b || 0) dot tilde(W)_(1)(b || 1) \
                  &= tilde("eq")(x, ()) dot tilde(W)_(1)(() || 0) dot tilde(W)_(1)(() || 1) \
                  &= tilde(W)_(1)(0) dot tilde(W)_(1)(1) \
  $
]

#slide[
  = Full Protocol: Preprocessing

  #align(center)[
    #set text(graph-text-size)
    #let w = 0.7
    #let h = 0.7

    #diagram(debug: 0, {
    let (P, M, V) = ((0, 0), (1.5, 0), (3, 0))

      node(M, inset: 0em, zero-width-box(text(theme.fg2)[
        The prover sends evaluations $v^((0))_0, v^((0))_1$ claiming that $v^((0))_0 =
        tilde(W)_1(0), v^((0))_1 = tilde(W)_1(1)$ and thus $y = v^((0))_0 dot v^((0))_1$.
      ]))
      P.at(1) += h/1; M.at(1) += h/1; V.at(1) += h/1;

      node(P, $
        v^((0))_0 &:= tilde(W)_1(0), \
        v^((0))_1 &:= tilde(W)_1(1)
      $)
      edge(P, V, "->", $v^((0))_0, v^((0))_1$)
      node(V, $ m_0 := v^((0))_0 dot v^((0))_1$)
    })
  ]
]

// #slide[
//   = Full Protocol: Round one

//   #align(center)[
//     #set text(graph-text-size)
//     #let w = 0.7
//     #let h = 0.7

//     #diagram(debug: 0, {
//     let (P, M, V) = ((0, 0), (1.5, 0), (3, 0))

//       node(M, inset: 0em, zero-width-box(text(theme.fg2)[
//         $
//           f_(1)(vec(b)) &= (tilde("eq")_(0)(vec(b)) + alpha dot tilde("eq")_(1)(vec(b))) dot tilde(W)_(2)(vec(b) || 0) dot tilde(W)_(2)(vec(b) || 1)
//         $
//       ]))
//       P.at(1) += h/1.3; M.at(1) += h/1.3; V.at(1) += h/1.3; 

//       node(P, $f_(1)(vec(b))$)
//       node(V, $ alpha inrand Fb $)
//       edge(V, P, "->", $alpha$)
//       P.at(1) += h/1.8; M.at(1) += h/1.8; V.at(1) += h/1.8; 

//       edge(P, V, "<->", $sum_(vec(b) in bits^(1)) f_(1)(vec(b)) meq m_1$)
//       P.at(1) += h/1.4; M.at(1) += h/1.4; V.at(1) += h/1.4;

//       node(M, inset: 0em, zero-width-box(text(theme.fg2)[
//         At the end of the protocol, $prover$ sends $verifier$ the evaluations
//         of $tilde(W)_(2)(vec(r)_1 || 0)$ and $tilde(W)_(2)(vec(r)_1 || 1)$, so
//         $verifier$ can make the final check in the sumcheck protocol:
//       ]))
//       P.at(1) += h/1.2; M.at(1) += h/1.2; V.at(1) += h/1.2;

//       node(P, $
//         v^((1))_0 := tilde(W)_(2)(vec(r)_1 || 0), \
//         v^((1))_1 := tilde(W)_(2)(vec(r)_1 || 1)
//       $)
//       node(V, $
//         m_i &meq &&tilde("eq")_(0)(vec(r)_1) dot v^((1))_0 dot v^((1))_1 + \
//             &    &&alpha dot tilde("eq")_(1)(vec(r)_1) dot v^((1))_0 dot v^((1))_1
//       $)
//       edge(P, V, "->", $v^((0))_0, v^((0))_1$)
//     })
//   ]
// ]

#slide[
  = Full Protocol: Round $i$

  #align(center)[
    #set text(graph-text-size)
    #let w = 0.7
    #let h = 0.7

    #diagram(debug: 0, {
      let (P, M, V) = ((0, 0), (1.5, 0), (3, 0))

      // -------------------- Round i -------------------- //
      node(M, inset: 0em, zero-width-box(text(theme.fg2)[
        $
          f_(i)(vec(b)) &= (tilde("eq")_((vec(r)_(i-1) || 0))(vec(b)) + alpha dot tilde("eq")_((vec(r)_(i-1) || 1))(vec(b))) dot tilde(W)_(i+1)(vec(b) || 0) dot tilde(W)_(i+1)(vec(b) || 1)
        $
      ]))
      P.at(1) += h/1.0; M.at(1) += h/1.0; V.at(1) += h/1.0; 

      node(P, $f_(i)(vec(b))$)
      node(V, $ alpha inrand Fb $)
      edge(V, P, "->", $alpha$)
      P.at(1) += h/1.0; M.at(1) += h/1.0; V.at(1) += h/1.0; 

      edge(P, V, "<->", $sum_(vec(b), vec(c) in bits^i) f^(i)(vec(b)) meq m_i$)
      P.at(1) += h/1.0; M.at(1) += h/1.0; V.at(1) += h/1.0;

      node(P, $
        v^((i))_0 &:= tilde(W)_(i+1)(vec(r)_i || 0), \
        v^((i))_1 &:= tilde(W)_(i+1)(vec(r)_i || 1)
      $)
      node(V, $
        m_i &meq &&tilde("eq")_((vec(r)_(i-1) || 0))(vec(r)_i) dot v^((i))_0 dot v^((i))_1 + \
            &    &&alpha dot tilde("eq")_((vec(r)_(i-1) || 1))(vec(r)_i) dot v^((i))_0 dot v^((i))_1
      $)
      edge(P, V, "->", $v^((i))_0, v^((i))_1$)
    })
  ]
]

#slide[
  = Full Protocol: Round $d$

  #align(center)[
    #set text(graph-text-size)
    #let w = 0.7
    #let h = 0.7

    #diagram(debug: 0, {
      let (P, M, V) = ((0, 0), (1.5, 0), (3, 0))

      node(M, inset: 0em, zero-width-box(text(theme.fg2)[
        At the input layer $d$, $verifier$ has two claims. $verifier$ constructs
        $tilde(W)_d$ from $vec(w)$ and perform a final check.
      ]))
      P.at(1) += h/1.0; M.at(1) += h/1.0; V.at(1) += h/1.0; 

      node(P, "                                  ")
      node(V, $
        v^((d-1))_0 &meq tilde(W)_(d)(r_(d-1) || 0) and \
        v^((d-1))_1 &meq tilde(W)_(d)(r_(d-1) || 1)
      $)
    })
  ]
]

#new-section[The GKR-Based Grand Product Proof - Efficiency]

#slide[
  // #show math.equation: set text(22pt)

  = Linear Prover: Main idea

  - If each round of sumcheck takes $O(2^(i-j))$ time, then:

  $ O(sum_(j=1)^(i) 2^(i-j)) = O(sum_(j=1)^(i-1) 2^(i-j)) = O(2^i - 1) = O(2^i) $

  #show: later

  - Prover cost is dominated by the sumchecks, so this leads to:
  $
    O(sum^d_(i=0) 2^i) = O(2^(d+1)) = O(2^d) = O(n)
  $
]

#slide[
  // #show math.equation: set text(22pt)

  = Linear Prover: Use Lookup Tables

  $
    vec(a) &= (r_1, ..., r_j, t, x_1, dots, x_i), \
    f_(i)(vec(a)) &= (tilde("eq")_((vec(r)_(i-1) || 0))(vec(a)) + alpha dot tilde("eq")_((vec(r)_(i-1) || 1))(vec(a))) dot tilde(W)_(i+1)(vec(vec(a))) dot tilde(W)_(i+1)(vec(vec(a))) \
                  &= (hat("eq")_((vec(r)_(i-1) || 0))(vec(a)) + alpha dot hat("eq")_((vec(r)_(i-1) || 1))(vec(a))) dot hat(W)_(i+1)(vec(vec(a))) dot hat(W)_(i+1)(vec(vec(a))) \
  $

  #show: later

  - Constant time evaluation of $f_i$!
  - $deg(f_i) + 1 = 4$ points, still constant time.

  #show: later

  $$
  #align(center)[Assuming $hat("eq"), hat(W)_(i+1)$ can be computed in $O(2^(i-j))$ time...]
  
]

#slide[
  = Linear Prover: $hat("eq")_j$

  $
    vec(v) &= (vec(r)_(i-1) || 0) or (vec(r)_(i-1) || 1), \
    hat("eq")_(j)[(b_(j+1), ..., b_(ell))] &= v_j^(-1) dot hat("eq")_(j-1)[(1, b_(j+1), ..., b_(ell))] dot v_j r_j + (1 - v_j) (1 - r_j)
  $

  - $hat("eq")_(0)$ can be computed in $O(2^ell) = O(2^i)$ time
  - $hat("eq")_(j)$ can be computed in $O(2^(ell - j)) = O(2^(i - j))$ time.
]

#slide[
  = Linear Prover: $hat("W")_j$

  == Computing $hat("W")_j$:
  $
    hat(W)_(0)[vec(x) in bits^ell]    &:= &&W_(i+1) \
    hat(W)_(j)[(x_(j+1), ..., x_ell)] &:= &&tilde("eq")_0(r_j) dot hat(W)_(j-1)[(0, x_(j+1), ..., x_ell)] + \
                                      &   &&tilde("eq")_1(r_j) dot hat(W)_(j-1)[(1, x_(j+1), ..., x_ell)]
  $
  $$

  #show: later
  
  #align(center)[*$O(2^(ell-j)) = O(2^(i+1-j)) = O(2^(i-j))$ time!*]
  $$

  #show: later

  == Using $hat("W")_j$:
  $
    tilde(W)(r_1, ..., r_(j-1), t, x_(j+1), ..., x_(ell)) &= &&tilde("eq")_0(t) dot hat(W)_(j-1)[(0,x_(j+1), ..., x_ell)] + \
                                                          &  &&tilde("eq")_1(t) dot hat(W)_(j-1)[(1,x_(j+1), ..., x_ell)] \
  $
]

#slide[
  #show: focus

  *Linear Prover!*
]

#slide[
  = Communication $O(lg^2(n))$

  - *Round $i$:* $O(s_(i+1))$
    - One sumcheck: $O(sum^(2 s_(i+1))_(j=1) deg_(j)(f_(i))) = O(i)$

  $ O(sum^(d-1)_(i=1) i) = O(frac(d(d+1), 2)) = O(d^2) = O(lg^2(n)) $
]

#slide[
  = Verifier $O(lg^2(n) + n)$

  $
    O(lg^2(n) + t + n) &= O(lg^2(n) + sum^(d-1)_(i=1) i + n) \
                       &= O(lg^2(n) + lg^2(n) + n) \
                       &= O(lg^2(n) + n)
  $
]

#slide[
  = Conclusion

  - _Linear_ prover
  - Almost _sublinear_ verifier
  - Sublinear communication costs
  - All in the size of the _witness_, not just the circuit

  #show: later

  $$
  #align(center)[Excellent construction for SNARKs (Spartan, Lasso)]
]

#slide[
  #show: focus
  Fin
]
