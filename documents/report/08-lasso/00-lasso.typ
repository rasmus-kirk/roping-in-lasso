#import "../00-lib/header/lib.typ": *

#show smallcaps: set text(font: "New Computer Modern")

= Lasso <sec:lasso>

== Improved Security Analysis <sec:lasso-improved-security-analysis>

In the previous section we defined SPARK, the sparse PCS, and in section
@sec:spartan we showed how such a scheme could be used to create a linear-time
SNARK prover for R1CS instances. However, SPARK as presented thus far has a
glaring flaw which makes it impractical as a general-purpose PCS. This is due
to the required assumption that a trusted party commits to $tilde(M)$. This
is not an issue in Spartan, where it was already assumed that a trusted party
committed to the matrices $vec(A), vec(B), vec(C)$. In general it would be
quite useful to get a polynomial commitment scheme that takes only $O(n)$
time to perform an evaluation proof. That is, the evaluation proof is linear
in the _nonzero entries_ of $vec(M)$.

This is the first important result shown in the Lasso paper, and remarkably
the authors show that Spark is already such a scheme, as it maintains its
security even when the prover commits to $tilde(val), tilde(row), tilde(col),
tilde(readTS)_row, tilde(readTS)_col, tilde(auditTS)_row, tilde(auditTS)_col$
themselves. While this wasn't necessary for Spartan, it's required when we
apply the same principles to Lasso.

Before getting into the proof, it's important to understand
that $tilde(val), tilde(row), tilde(col)$ need not be committed "honestly". If
the prover commits some other polynomials $tilde(val)', tilde(row)',
tilde(col)'$ this is then just equivalent to the prover committing to another
matrix $vec(M)'$.

So, to get the desired result that the prover can perform
#smallcaps("SPARK.Commit") themselves, we need to show that the multi-set
equality check already implies read-consistency regardless of the committed
timestamps. The key to this result is the local counter trick we adopted
for optimization purposes (see @ex:global-timestamps-vs-counters).

#lemma(title: "Read-Consistency for Read-Only Memory")[
  Let $T$ be a memory array, $k$ the number of reads and $N$ the size of
  the memory. Assume that $k <= |Fb|, N <= |Fb|$. If the verifier enforces
  the multi-set equality check from @eq:omc-set-check using local counters
  and where $WS = { (a, v, t+1) | (a, v, t) in RS }$, then the check will
  enforce read-consistency with probability one.
]<lem:lasso-read-consistency>

#proof[
    First, let the initial state of the memory be defined as:

    $ Init = { (i, vec(RAM)[i], 0) }_(i=0)^(N-1) $

    Which is enforced by the verifier.
  
    We'll prove this using a proof of contradiction. Assume that $prover$
    successfully constructs $RS$, $WS$, and $Audit$ such that the multiset
    equality holds, but $RS$ contains an invalid read. Namely, there exists
    some tuple $tau = (a, v^*, t) in RS$ where $v^* != vec(RAM)[a]$.

    To satisfy $Init union WS meq RS union Audit$, the invalid tuple $tau$
    must have a matching counterpart in the left-hand side of the equation
    ($Init union WS$). In this event there are two cases:

    1. $tau in Init$: By definition, all tuples in $Init$ take the form $(i,
       vec(RAM)[i], 0)$. Since $v^* != vec(RAM)[a]$, $tau$ cannot be in $Init$.
     
    2. $tau in WS$: By the structural definition of read-only updates,
       every tuple in $WS$ is derived directly from a prior read in $RS$,
       taking the form $(a_i, v_i, t_i + 1)$. If $tau = (a, v^*, t) in WS$,
       then there must necessarily exist a corresponding "parent" read tuple
       $tau' = (a, v^*, t-1)$ in $RS$.

    In the second case, if $tau' in RS$, then this tuple must also exist
    on the left-hand side of the equation. Recursively applying this logic
    means that the prover would have to include the tuple $tau_0 = (a, v^*,
    0)$ in $RS$. Then this tuple must also exist on the left-hand side,
    leading to two cases:

    1. $tau_0 in WS$: Which is impossible because all tuples in $WS$ have
       strictly positive timestamps ($t > 0$).
    2. $tau_0 in Init$: Which is impossible because $v^* != vec(RAM)[a]$.
  
    Thus, we get read-consistency.
]

You might wonder why $Audit$ is not mentioned in the above proof, but this
is because it's simply not relied on to achieve read-consistency. It is
however necessary to guarantee that the multi-set check from @eq:omc-set-check
passes in the first place; remember that the above proof is conditioned on the
multi-set check passing, but this can only happen if $Audit$ is well-formed.

== The Lasso Lookup Argument

Suppose we wanted to prove a lookup into a table to a verifier. One way of
viewing this is with a single read of a read-only RAM. Suppose the table
is of size $N$ and that $N$ is a power of two, we could use memory-checking
techniques to prove this. But imagine that this memory was extremely large,
such as $2^128$. In this case the instantiated memory from the offline
memory checking would also be $2^128$, far too large to instantiate in an
interactive argument. We can use the same trick as was employed in Spark.
However, recall that in that case, we wanted to evaluate the multilinear
extension of $M$. We did so using two $eq$ polynomials, but what would happen
if we used the natural MLE of $M$?

$ tilde(M)(vec(x), vec(y)) = sum_(vec(a), vec(b) in bits^ceil(lg(m))) M(vec(a), vec(b)) dot eq(vec(x) || vec(y), vec(a) || vec(b)) $

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
useful. Suppose we wanted to construct a lookup argument of bitwise-XOR, and
suppose we wanted to perform this lookup on two unreasonably large values of
two 64-bit values giving us a truth-table of size $2^128$. This table would of
course be way too large to ever concretely instantiate or especially commit to.

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
in the following way:

$ sum_(i=1)^(c) v_i dot 2^(w dot (c-i)) $

Where $c$ is the number of chunks and $w$ is the _window size_, the number
of bits per limb. Finally $vec(v)$ represents the result of each lookup into
the sub-tables. For reference, in @ex:xor-decomposed, $c = 4, w = 2, vec(v) =
[1,2,0,1]$. In general, we can abstract away how the sub-tables are recomposed
with some function $g$ and require the following to hold:

$ hat(T)[vec(b)] = g(hat(T)_1[vec(overline(b))_1], ..., hat(T)_(c)[vec(overline(b))_c]) $

Where $vec(b) = vec(overline(b)_1) || ... || vec(overline(b)_c)$, $hat(T)$
is the large lookup table of size $N$ and $hat(T)_1, ..., hat(T)_c$ are the
small sub-tables of size $N^(frac(style: "horizontal", 1, c))$. Following
this line of thought, we could already start constructing an interactive
argument. We simply perform $c$ offline memory checks as in @sec:spark,
then let the verifier recompose using $g$.

But Lasso has one more trick up its sleeve, using Spark, we can actually
batch $k$ arguments into one. In general, we can view a lookup operation
as a simple matrix-vector multiplication:

$ vec(M) vec(t) = vec(a) $

Where $vec(t)$ is our table of size $N$, $vec(a)$ is our vector of $k$ lookup
results, and $vec(M)$ is a $k times N$ sparse matrix where each row has
exactly one $1$ corresponding to the accessed index.

#example(title: "Matrix-Vector Lookup for 1-bit XOR")[
  Let the lookup table $vec(t)$ be the XOR truth table and the result of our lookups $vec(a)$.
  The matrix $vec(M)$ has a single $1$ per row to select the index.

  $
    underbrace(
      mat(
        0, 1, 0, 0;
        0, 0, 0, 1;
        0, 0, 1, 0
      ),
      vec(M)
    )
    dot
    underbrace(
      mat(0; 1; 1; 0),
      vec(t)
    )
    =
    underbrace(
      mat(1; 0; 1),
      vec(a)
    )
  $
]

We can of course use the usual methods to convert this to a polynomial form:

$ tilde(M)(vec(x), vec(y)) dot tilde(t)(vec(y)) = tilde(a)(vec(x)) $

Where $vec(x) in bits^lg(k), vec(y) in Fb^lg(N)$. We now wish to establish
that the above equality holds, which we can of course use Schwartz-Zippel
for. This means the verifier wants to check the evaluation $tilde(a)(vec(r))$
at some random point $vec(r) inrand bits^lg(N)$ equals:

$ tilde(a)(vec(r)) meq sum_(vec(b) in bits^lg(k)) tilde(M)(vec(r), vec(b)) dot tilde(t)(vec(b)) $<eq:lasso-lookup-dense>

Since there is only a single entry in $M$ which is nonzero, then the above
expression is the same as:

$ tilde(a)(vec(r)) meq sum_(vec(b) in bits^lg(k)) eq(vec(r), vec(b)) dot hat(T)[nz(vec(b))] $<eq:lasso-lookup-sparse>

Where $nz$ denotes the nonzero entry of each row of $vec(M)$. This
follows from the fact that the polynomials of @eq:lasso-lookup-dense and
@eq:lasso-lookup-sparse are both MLE and agree on all points on the boolean
hypercube.

As previously established because the table $hat(T)$ is decomposable,
we can replace $hat(T)[nz(vec(b))]$ with our recomposition function $g$
applied to $c$ smaller sub-table lookups. Let $tilde(e)_(i)(vec(x))$ be the
multilinear extension of the $k$ lookups into $hat(T)_i$. By substituting
in the recomposition function $g$, the identity collapses to:

$ tilde(a)(vec(r)) = sum_(vec(b) in bits^lg(k)) eq(vec(r), vec(b)) dot g(tilde(e)_1(vec(b)), ..., tilde(e)_(c)(vec(b))) $

Once the $e_i$ sub-lookups are verified, the verifier simply runs a standard
sum-check protocol over the $lg(k)$-variate boolean hypercube on the above
sum, with the following sumcheck polynomial:

$ f_("Lasso")(vec(x)) := eq(vec(r), vec(x)) dot g(tilde(e)_1(vec(x)), ..., tilde(e)_(c)(vec(x))) $

Assuming the verifying checks pass, this proves the correctness of the
lookups into the massive table $hat(T)$.

== Efficiency of the Lasso Lookup Argument <sec:lasso-efficiency>

*Prover Costs:*

Assuming linear commitment costs in the number of variables (for MLE
polynomials) of $O(n)$, the prover runtime is dominated by the following
operations:

#table(
  columns: 5,
  row-gutter: (auto, 2.2pt, auto, 2.2pt, auto, 2.2pt, auto),
  
  [*Commitments:*], $tilde(nz)_1, ..., tilde(nz)_c$, $tilde(e)_1, ..., tilde(e)_c$, $tilde(readTS)_1, ..., tilde(readTS)_c$, $tilde(auditTS)_1, ..., tilde(auditTS)_c$,
  [*Cost:*], $O(c dot k)$, $O(c dot k)$, $O(c dot k)$, $O(c dot N^(frac(style: "horizontal", 1, c)))$,
  [*EvalProofs:*], $tilde(nz)_1, ..., tilde(nz)_c$, $tilde(e)_1, ..., tilde(e)_c$, $tilde(readTS)_1, ..., tilde(readTS)_c$, $tilde(auditTS)_1, ..., tilde(auditTS)_c$,
  [*Cost:*], $O(c dot k)$, $O(c dot k)$, $O(c dot k)$, $O(c dot N^(frac(style: "horizontal", 1, c)))$,
  [*Productchecks:*], $RS_1, ..., RS_c$, $WS_1, ..., WS_c$, $Init_1, ..., Init_c$, $Audit_1, ..., Audit_c$, 
  [*Cost:*], $O(c dot k)$, $O(c dot k)$, $O(c dot N^(frac(style: "horizontal", 1, c)))$, $O(c dot N^(frac(style: "horizontal", 1, c)))$,
  [*Sumchecks:*], $f_"Lasso"$, $$, $$, $$,
  [*Cost:*], $O(c dot k)$,
)

For a total of:

$ O((3 dot c dot k + c dot N^(frac(style: "horizontal", 1, c))) + (3 dot c dot k + c dot N^(frac(style: "horizontal", 1, c))) + (2 dot c dot k + 2 dot c dot N^(frac(style: "horizontal", 1, c))) + c dot k) $

We can batch sumchecks, productchecks and evaluation proofs. These batching techniques follow
trivially from Schwartz-Zippel. If you have $n$ sumchecks, all over $lg(k)$ variables:

$ sigma_1 meq sum_(vec(b) in bits^lg(k)) f_1(vec(b)) and ... and sigma_n meq sum_(vec(b) in bits^lg(k)) f_(n)(vec(b)) $

Then we can batch them using a uniformly random value $alpha inrand Fb$:

$ sum_(i=1)^(n) alpha^(i-1) dot sigma_i meq sum_(vec(b) in bits^lg(k)) sum_(i=1)^(n) alpha^(i-1) dot f_i(vec(b)) $

The same holds for our productchecks. Since the productchecks only apply
sumcheck in the same manner as the GKR protocol we can use the sumcheck
batching technique on the sumcheck polynomials of the productcheck, as long
as the grand products have the same number of entries.

As for the evaluation proofs, consider the evaluations:

$ v_1 = f_1(vec(zeta)), ..., v_n = f_n(vec(zeta)) $

Proved correct using evaluation proofs, with corresponding commitments:

$ C_1 = PCCommit(f_1, d), ..., C_n = PCCommit(f_n, d) $

Then we could of course verify each on its own, with an assumed linear cost
of $O(k)$ each, for a total cost of $O(n dot k)$:

$ PCCheck(C_1, d, vec(zeta), v_1, pi_1) and ... and PCCheck(C_(n), d, vec(zeta), v_(n), pi_(n)) $

But, assuming we have additively homomorphic commitments, the prover could
also instead construct a batching polynomial $q$, using a uniformly random
value $alpha$.

$ q(vec(x)) = sum_(i=1)^(n) alpha^(i-1) dot f_i(vec(x)) $

Send the evaluation and proof for $g(vec(zeta))$ along with the evaluations
$v_1, dots, v_n$. The verifier can then check whether:

$ PCCheck(C_q, d, vec(zeta), q(vec(zeta)), pi_q) and q(vec(zeta)) meq sum_(i=1)^(n) alpha^(i-1) dot v_i $

Which has only a $O(n)$ cost for the prover. Applying these batching
techniques, the cost for the prover becomes:

$ O((3 dot c dot k + c dot N^(frac(style: "horizontal", 1, c))) + (k + N^(frac(style: "horizontal", 1, c))) + (k + N^(frac(style: "horizontal", 1, c))) + c dot k) $

Since the first term is dominant, we can simplify this to:

$ O(c dot k + c dot N^(frac(style: "horizontal", 1, c))) $

Picking $c$ such that $N^(frac(style: "horizontal", 1, c)) < c dot k$
means that the prover cost primarily scales with the number of lookups,
not the size of the table. Another thing to note is that the primary cost
to the prover is from the commitments, due to the batching techniques applied
above. This is also why the Lasso paper primarily focuses on the commitment
cost in their discussion.

*Verifier Cost:*

Assuming that an evaluation proof takes $O(lg(n))$ in the number of
variables. Let:

$ lambda_(k) = lg^2(k) + lg(k), #h(2em) lambda_(N) = lg^2(N^(frac(style: "horizontal", 1, c))) + lg(N^(frac(style: "horizontal", 1, c))) $

#table(
  columns: 5,
  row-gutter: (auto, 2.2pt, auto, 2.2pt, auto, 2.2pt),
  [*EvalProofs:*], $tilde(nz)_1, ..., tilde(nz)_c$, $tilde(e)_1, ..., tilde(e)_c$, $tilde(readTS)_1, ..., tilde(readTS)_c$, $tilde(auditTS)_1, ..., tilde(auditTS)_c$,
  [*Cost:*], $O(c dot lg(k))$, $O(c dot lg(k))$, $O(c dot lg(k))$, $O(c dot lg(N^(frac(style: "horizontal", 1, c))))$,
  [*Productchecks:*], $RS_1, ..., RS_c$, $WS_1, ..., WS_c$, $Init_1, ..., Init_c$, $Audit_1, ..., Audit_c$, 
  [*Cost:*], $O(c dot lambda_k)$, $O(c dot lambda_k)$, $O(c dot lambda_N)$, $O(c dot lambda_N)$,
  [*Sumchecks:*], $f_"Lasso"$, $$, $$, $$,
  [*Cost:*], $O(c + lg(k))$,
)

With batching this then becomes:

$ O((lg(k) + lg(N^(frac(style: "horizontal", 1, c)))) + (lambda_k + lambda_N) + (c + lg(k))) $
