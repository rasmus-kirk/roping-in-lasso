#import "../00-lib/header/lib.typ": *

= Offline Memory Checking

#let RS = $R S$
#let Init = $"Init"$
#let Audit = $"Audit"$
#let WS = $W S$

Suppose a RAM $vec(v) in Fb^n$ and a set of timestamps $t = { t_1, ..., t_n }$

$RS = WS = { (a_1, v_1, t_1 ), ..., (a_n, v_n, t_n ) }$

- Start with $WS = {}, RS = {}$
- Then, upon write $v$ to address $a$:
  - Reads value $v'$ and time $t'$ stored in address $a$
  - Checks that $t' < t$
  - Updates $RS = RS union {(v', a, t')}$
  - Writes new value $v$ and current time $t$ to address $a$
  - Updates $WS = WS union {(v, a, t)}$
- Upon read of address $a$:
  - Reads value $v'$ and time $t'$ stored in address $a$
  - Checks that $t' < t$
  - Updates $RS = RS union {(v', a, t')}$
  - Writes stored value $v'$ and current time $t$ to address $a$
  - Updates $WS = WS union {(v, a, t)}$

Read-consistency: Every value read from memory for location $a$ is the last
written value written to location $a$

We wish to prove that $RS = WS$ implies read consistency.

Suppose that $RS = WS$ but we _don't_ have read-consistency. Then it must
be the case that the last write to $a$ was $(a, v_"prev", t_"prev")$ and
the read was $(a, v_"read", t_"prev")$ with $v_"prev" != v_"read"$. Then,
given that the prover follows the procedure outlined, then $RS$ must be
updated with $(a, v_"read", t_"prev")$. 
