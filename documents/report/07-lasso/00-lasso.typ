#import "../00-lib/header/lib.typ": *
#import "@preview/algo:0.3.6": algo, i, d, comment, code

= Lasso

== Improved Security Analysis <sec:lasso-improved-security-analysis>

While Spark, and its application in Spartan, is certainly neat, the assumption
that a trusted party committed to each $tilde(M)$ hinders it in practice. In
general it would be quite useful to get a polynomial commitment scheme that
takes only $O(n)$ time to perform an evaluation proof. This is the first
important result shown in the Lasso paper, and remarkably the authors show
that Spark is already such a scheme, as it maintains its security even
when the prover commits to $tilde(row), tilde(col), tilde(readTS)_row,
tilde(readTS)_col, tilde(auditTS)_row, tilde(auditTS)_col$ themselves.

#slop-box[
  #lemma(title: "Read-Consistency for Read-Only Tables")[
    Let $T$ be a predetermined table. If the verifier enforces the multiset equality 
    $Init union WS meq RS union Audit$ where $WS = { (a, v, t+1) | (a, v, t) in RS }$, 
    then any value read by the prover is guaranteed to be the correct table value, 
    i.e., for all $(a, v, t) in RS$, $v = T[a]$.
  ]<lem:lasso-read-consistency>

  #proof[
    Let the initial state of the table be rigorously defined as 
    $Init = { (a, T[a], 0) }_(a=0)^(N-1)$. 
  
    Assume for contradiction that the $prover$ successfully constructs $RS$, $WS$, 
    and $Audit$ such that the multiset equality holds, but $RS$ contains an invalid 
    read. Namely, there exists some tuple $X = (a, v^*, t) in RS$ where $v^* != T[a]$.

    To satisfy $Init union WS meq RS union Audit$, the invalid tuple $X$ must have 
    a matching counterpart in the left-hand side of the equation: $Init union WS$.
  
    We evaluate the two disjoint sets on the left-hand side:
  
    1. *Could $X in Init$?* By definition, all tuples in $Init$ take the form $(x, T[x], 0)$. 
       Since $v^* != T[a]$, $X$ strictly cannot be in $Init$.
     
    2. *Could $X in WS$?* By the structural definition of read-only updates, every tuple in $WS$ is 
       derived directly from a prior read in $RS$, taking the form $(a_i, v_i, t_i + 1)$. 
       If $X = (a, v^*, t) in WS$, then there must necessarily exist a corresponding 
       "parent" read tuple $X' = (a, v^*, t-1)$ in $RS$.

    By mathematical induction, if an invalid read of $v^*$ exists in $RS$ at timestamp $t$, 
    an identical invalid read must exist in $RS$ at timestamp $t-1$. Recursively applying 
    this logic forces the prover to include the base tuple $X_0 = (a, v^*, 0)$ in $RS$.

    Now we must balance $X_0$: it must exist in $Init union WS$.
    - $X_0 in.not WS$, because all tuples in $WS$ have strictly positive timestamps ($t > 0$).
    - $X_0 in.not Init$, because $v^* != T[a]$.

    Thus, $X_0$ cannot be balanced on the left-hand side. The multiset equality 
    $Init union WS meq RS union Audit$ breaks entirely, establishing a contradiction. 
    The prover cannot successfully commit to an invalid read.
  ]
]

#todo-box[
  The above is surprisingly good. But I still need to understand why the prover
  can't cheat by using $tilde(row)^*, tilde(col)^*$ instead of $tilde(row),
  tilde(col)$. That is, use the wrong indices for the nonzero entries.
]

== Surge <sec:surge>

Suppose we wanted to prove a lookup into a table to a verifier. One way of
viewing this is with a single read of a read-only RAM. Suppose the table is
of size $N$, we could use memory-checking techniques to prove this.

$ hat(T)[vec(b)] $

But imagine that this memory was extremely large, such as $2^128$. In this
case the instantiated memory from the offline memory checking would also be
$2^128$, far too large to instantiate in an interactive argument. We can use
the same trick as was employed in Spark however, recall that in that case,
we wanted to evaluate the multilinear extension of $M$. We did so using two
$eq$ polynomials, but what would happen if we used the natural MLE of $M$?

$ tilde(M)(vec(x), vec(y)) = sum_(vec(a), vec(b) in bits^m) M(vec(a), vec(b)) dot eq(vec(x) || vec(y), vec(a) || vec(b)) $

We would then of course still use the sparse representation of $M$ to compute
this evaluation:

$ tilde(M)(vec(x), vec(y)) = sum_(vec(b) in bits^ceil(lg(n))) val(vec(b)) dot eq(vec(x) || vec(y), row(vec(b)) || col(vec(b))) $

Besides the fact that the above equation looks more complicated than the
one we arrived at in the Spark section, it also has a major disadvantage
when used with our offline memory checking technique. The consequence is
that we would be reading from a memory of size $m^2$, and the resulting
memory-checking argument would take time $O(n + m^2)$, ruining our hopes
for a sparse polynomial commitment scheme. Luckily, we were able to decompose
$eq$ using the identity:

$ eq(vec(x) || vec(y), row(vec(b)) || col(vec(b))) = eq(vec(x), row(vec(b))) dot eq(vec(y), col(vec(b))) $

A key insight of Lasso was that this trick is actually generally
useful. Suppose we wanted to construct a lookup argument of bitwise-XOR,
and suppose we wanted to perform this lookup on unreasonably large values
of $2^128$. This table would of course be way too large to ever concretely
instantiate or especially commit to.

But bitwise-XOR is exactly just that, bitwise, and this means that this table
too, is _decomposable_. Instead of a single lookup in a table of size $2^128$
we could do eight lookups into sub-tables of size $2^16$ and then concatenate
them together.

#example(title: "XOR decomposition")[
  #let b = b.with(fill: color.rgb("#fbf1c7"), l: 2)

  If we take a simple example, where we want to do a bitwise-XOR on two inputs
  of size $2^8$, meaning we have a lookup on a table of size $2^16$. This
  might be small enough that it won't need decomposition, but it might
  be useful for demonstration purposes. We can split this table in four
  identical sub-tables of size $2^4$:
  #figure(
    align(center)[
      #table(
        columns: 17,
        // rows: 3,
        column-gutter: (0.5pt, auto),
        row-gutter: (auto, 2.2pt),
        align: left,
        $vec(x)_i$, b(00), b(00), b(00), b(00), b(01), b(01), b(01), b(01), b(10), b(10), b(10), b(10), b(11), b(11), b(11), b(11),
        $vec(y)_i$, b(00), b(01), b(10), b(11), b(00), b(01), b(10), b(11), b(00), b(01), b(10), b(11), b(00), b(01), b(10), b(11),
        $vec(z)_i$, b(00), b(01), b(10), b(11), b(01), b(00), b(11), b(10), b(10), b(11), b(00), b(01), b(11), b(10), b(01), b(00),
      )
    ]
  )

  Where $vec(x)_i xor vec(y)_i = vec(z)_i$. We can then perform eight lookups
  into these smaller tables and concatenate them:

  $
    #b(l: 8, 01000001) xor #b(l: 8, 00100000) &= (hat(xor))_2(#b(01), #b(00)) || (hat(xor))_2(#b(00), #b(10)) || (hat(xor))_2(#b(00), #b(00)) || (hat(xor))_2(#b(01), #b(00)) \
                                                  &= #b(01) || #b(10) || #b(00) || #b(01) \
                                                  &= #b(01100001)
  $
]<ex:xor-decomposed>

So, for $eq$ we combined the two sub-tables with multiplication, but in this
case we're combining the tables using bit concatenation. Since our tables
take in bits and return a field element we can model this bit concatenation
with in the following way:

$ sum_(i=1)^(c) v_i dot 2^(w dot (i-1)) $

Where $c$ is the number of chunks and $w$ is the _window size_, the number
of bits per limb. Finally $vec(v)$ represents the result of each lookup into
the sub-tables. For reference, in @ex:xor-decomposed, $c = 4, w = 2, vec(v) =
[1,2,0,1]$. In general, we can abstract away how the sub-tables are recomposed
with some function $g$ and require the following to hold:

$ hat(T)[vec(b)] = g(hat(T)_1[vec(overline(b))_1], ..., hat(T)_(c)[vec(overline(b))_c]) $

Where $vec(b) = vec(overline(b)_1) || ... || vec(overline(b)_c)$. Following
this line of thought, we could already start constructing an interactive
argument. We simply perform $c$ offline memory checks as in @sec:spark,
then let the verifier recompose using $g$. But Lasso has one more trick up
its sleeve, using Spark, we can actually batch $k$ arguments into one.

In general, this is:

$
  vec(M) vec(t) &= vec(a) \
$

We can of course use our usual tricks to convert this to a polynomial form:

$
  sum_(vec(x) in bits^s, vec(y) in bits^m) tilde(M)(vec(x), vec(y)) dot tilde(t)(vec(y)) = sum_(vec(x) in bits^s) tilde(a)(vec(x))
$

Then, using Schwartz-Zippel, we wish to prove the following polynomial identity:

$
  sum_(vec(y) in bits^m) tilde(M)(vec(r), vec(y)) dot tilde(t)(vec(y)) = sum_(vec(x) in bits^s) tilde(a)(vec(r))
$

Since there is only a single entry in $M$ which is nonzero, then the above
is also equal to:

$
  sum_(vec(x) in bits^s) eq(vec(x), vec(b)) dot T["nz"(vec(b))]
$

Where $nz$ is 

$
  sum_(vec(x) in bits^s) eq(vec(x), vec(b)) dot g(T_1["nz"(vec(b))], ..., T_(c)["nz"(vec(b))])
$

$
  sum_(vec(x) in bits^s) eq(vec(x), vec(b)) dot g(e_1(vec(b)), ..., e_(c)(vec(b)))
$


// The eight sub-tables are identical $(hat(xor))_8 : bits^16 -> bits^8$. We
// could of course also view this table as a vector of

// Consider the usual XOR table:

// #align(center)[
//   #let b = b.with(l: 1, fill: none)
//   #table(
//     column-gutter: (0.5pt, auto),
//     row-gutter: (auto, 2.2pt),
//     columns: 5,
//     align: left,
//     $x$, b(0), b(0), b(1), b(1),
//     $y$, b(0), b(1), b(0), b(1),
//     $z$, b(0), b(1), b(1), b(0),
//   )
// ]

// Say we wanted to perform three lookups into this table. One way to model
// such a lookup is using linear algebra:

// $
//   mat(
//     0,0,0,1;
//     0,1,0,0;
//     0,0,1,0;
//   ) mat(0;1;1;0) &= mat(0;1;1) \
// $

// Which corresponds to the lookups for:


// $
//   #let b = b.with(fill: none, l: 1)
//   #b(1) xor #b(1) = #b(0), #h(3em) #b(0) xor #b(1) = #b(1), #h(3em) #b(1) xor #b(0) = #b(1)
// $

// In general, this is:

// $
//   vec(M) vec(t) &= vec(a) \
// $

// We can of course use our usual tricks to convert this to a polynomial form:

// - rows = $s$
// - cols = $N$

