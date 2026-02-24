#import "../00-lib/header/lib.typ": *
#import "@preview/algo:0.3.6": algo, i, d, comment, code

#let Init = "Init"
#let WS = "WS"
#let RS = "RS"
#let Audit = "Audit"
#let TODO = text(weight: "bold", size: 1.2em,  "TODO")
#let ts = $t s$

= Lasso

== Improved Security Analysis

#slop-box[
  *The Trap: Why the Prover Cannot Lie*

  If the prover wants to return a fake value to cheat the lookup argument,
  here is what happens (as detailed in Claim 2 of the paper):

  - *The Lie:* The prover claims they read a fake value $v_"fake"$ at address
    $k$ with timestamp $t$. They put $(k, v_"fake", t)$ into $RS$.

  - *The Requirement:* For the check $WS = RS union S$ to pass, the exact
    tuple $(k, v_"fake", t)$ must exist in $WS$.

  - *The Infinite Regress:* How did it get into $WS$?
    - It didn't come from the Initial State, because the verifier strictly
      locked the Initial State to $(k, v_"real", 0)$.
    - Therefore, the only way $(k, v_"fake", t)$ is in $WS$ is if the prover
      wrote it back during a previous read. This means the prover must have
      claimed a previous read of $(k, v_"fake", t-1)$.

  - *The Contradiction:* To justify $t$, they must fake $t-1$. To justify
    $t-1$, they must fake $t-2$... all the way down to $(k, v_"fake", 0)$. But
    the verifier absolutely controls timestamp $0$ in the Initial State and
    knows the value is $v_"real"$.

  Because the number of memory reads $m$ is strictly smaller than the size of
  the finite field, the prover cannot "wrap around" the timestamps to escape
  this chain.
]

== Surge <sec:surge>


