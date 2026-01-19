#import "../00-lib/header/lib.typ": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#let Init = "Init"
#let Audit = "Audit"

= Offline Memory Checking

== Non-slop

We need to prove that

$ product_(tau in S_W) tau_0 + gamma tau_1 + gamma^2 tau_2 = product_(tau in S_R) tau_0 + gamma tau_1 + gamma^2 tau_2 $

Where:

$
  tau_i &:= (a, v, t) \
  S_W &:= Init union W \
  S_R &:= Audit union R \
$

$a$ is the address, $v$ is the value stored at that address and $t$ is the
timestamp associated with that address. The Specialized Grand product allows
us to compute whether $y meq product_(i = 1)^(|vec(w)|)$, but we also need
to make sure that the entries has additional structure. For example for $Init$:

$
  Init := { tau_i = (i, tilde("eq")(i, r_x)), 0 }
$

The verifier could of course compute this themselves, but I'm still not sure
how this would be handled if we wanted to use a commitment to $vec(w)$. We
want to support commitments to eliminate the linear factor in the verifier's
verification and the linear factor in the proof size/communication complexity.

== Slop

In the previous chapters, we established efficient protocols for checking layered arithmetic circuits (GKR) and specialized structures like Grand Products. However, standard circuit models struggle to efficiently represent Random Access Memory (RAM). Simulating a RAM access in a circuit requires a multiplexer of size $O(N)$ (where $N$ is the memory size) or a permutation network, both of which are prohibitively expensive for large memories.

To support efficient RAM (and by extension, Lookup Tables as used in Lasso), we turn to *Offline Memory Checking*. Instead of verifying every memory access as it happens (Online), the Prover commits to a trace of all memory operations, and the Verifier checks the consistency of this trace globally.

This section presents the foundational logic for offline memory checking using multiset equality.

== The Memory Model

We model memory as a collection of cells addressed by indices $a in {0, ..., N-1}$. The state of the memory evolves over a series of $M$ operations (Reads and Writes). 

To ensure consistency—specifically, that "every Read returns the value of the most recent Write"—we must track not just the value $v$ and address $a$, but also a timestamp $t$.

We define a *Memory Tuple* as:
$ tau = (a, v, t) $
Where:
- $a$ is the memory address.
- $v$ is the value stored at that address.
- $t$ is the global logical time step at which this value was written.

=== The Multisets

We track the lifecycle of memory cells using two multisets (sets allowing duplicates), $S_"in"$ and $S_"out"$. Conceptually, $S_"in"$ represents all tuples *entering* the memory, and $S_"out"$ represents all tuples *leaving* the memory.

Let the sequence of operations be $"op"_1, ..., "op"_M$. We maintain a global clock $T$, initialized to $0$.

1.  *Init:* At $T=0$, the memory is initialized. For every address $a$, we implicitly write an initial value (e.g., $0$).
    $ "Init" = { (a, 0, 0) | a in {0, ..., N-1} } $

2.  *Execution:* For each operation $k$ accessing address $a$ with a new value $v_"new"$ (for a Read, $v_"new" = v_"old"$):
    - The Prover reads the current state of address $a$, retrieving a tuple $(a, v_"old", t_"old")$.
    - This tuple is added to the read-set $R$.
    - The Prover updates the memory with the new tuple $(a, v_"new", k)$.
    - This tuple is added to the write-set $W$.

3.  *Audit:* After step $M$, the memory is in a final state. We read out the entire memory state to ensure these final values are accounted for.
    $ "Audit" = { (a, v, t)_"final" | a in {0, ..., N-1} } $

We define our two primary sets for comparison:
$
  S_"in" &:= "Init" union W \
  S_"out" &:= R union "Audit"
$

== Correctness of Memory

For a memory trace to be valid, the history of values read must exactly match the history of values written. Furthermore, time must move forward.

#theorem[
  A sequence of memory operations is valid if and only if:
  1.  *Multiset Equality:* The multiset of tuples entering memory equals the multiset of tuples leaving memory:
      $ "Init" union W equiv R union "Audit" $
  2.  *Temporal Ordering:* For every read operation at global time $T_"curr"$ retrieving a tuple $(a, v, t_"prev")$, it holds that $t_"prev" < T_"curr"$.
] <thm:mem-check>

The *Temporal Ordering* check is a local check (usually performed via range checks or bit decomposition on $T_"curr" - t_"prev"$). The *Multiset Equality* is the difficult part, which we solve efficiently using probabilistic techniques (Grand Product Argument).

=== Proof of Consistency <sec:mem-proof>

We must prove that if $Init union W equiv R union Audit$, the memory has been
untampered with. That is, every Read operation retrieved the value from the
immediately preceding Write operation to that address.

#proof[
  Let $S_"in" = "Init" union W$ and $S_"out" = R union "Audit"$.
  Assume the multiset equality holds: $S_"in" equiv S_"out"$.

  We can conceptually reorder the multisets. Since the tuples contain the address $a$, let us partition the multisets by address. For the equality to hold globally, it must hold for each address sub-multiset:
  $ forall a: S_"in"|_a equiv S_"out"|_a $

  Consider a specific address $a$. Let the elements of $S_"in"|_a$ be sorted strictly by their timestamp $t$. Since $W$ is constructed by a sequential execution with a global clock, all timestamps in $W$ are unique. $Init$ provides the timestamp $0$. Thus, $S_"in"|_a$ forms a strictly increasing sequence of writes to address $a$:
  $ w_0, w_1, w_2, ..., w_k $
  Where $w_0 in "Init"$, and $w_1...w_k in W$.

  Since $S_"in"|_a equiv S_"out"|_a$, the set $S_"out"|_a$ must contain the exact same tuples.
  
  In the execution model, an element is added to $R$ (part of $S_"out"$) *only* when we perform an operation at address $a$. Specifically, if operation $op_j$ accesses $a$, it reads a tuple $(a, v, t)$ from memory and adds it to $R$.

  Let us inductively match the writes to the reads.
  1.  $w_0$ (from $Init$) enters memory at $t=0$.
  2.  Because $S_"out"|_a$ is a permutation of $S_"in"|_a$, $w_0$ must appear in $S_"out"$.
  3.  $w_0$ can effectively only leave memory when the *next* operation on address $a$ occurs (or during Audit). Let the first operation on $a$ occur at time $T_1$. It reads the current state.
  4.  If the Prover was honest, it reads $w_0$. If the Prover tries to return a fake tuple $w'$, then $w'$ must exist in $S_"in"$. However, since timestamps are unique and strictly increasing, the Prover cannot return a "future" write $w_2$ because its timestamp would be greater than the current clock $T_1$ (violating the Temporal Ordering check). The Prover cannot return a "past" write that doesn't exist.
  
  Therefore, the read at step $i$ must consume the tuple produced by the write at step $i-1$. The multiset equality enforces that no tuples are created out of thin air and no tuples are dropped. The "Audit" set ensures that the final write $w_k$ is accounted for, closing the loop.

  Thus, the value read at any point must be the value written by the most recent preceding write.
]

#figure(
  align(center)[
    #set text(10pt)
    #let w = 2.5em
    #let h = 3em
    #diagram(
      node-stroke: 1pt,
      spacing: (2em, 2em),
      {
        let (n_init, n_w1, n_w2, n_audit) = ((0,0), (2,0), (4,0), (6,0))
        let (n_r1, n_r2, n_r3) = ((1, 1), (3, 1), (5, 1))

        // Timeline nodes
        node(n_init, [$(v_0, 0)$], shape: rect, fill: rgb("#e1f5fe"))
        node(n_w1, [$(v_1, 5)$], shape: rect, fill: rgb("#e1f5fe"))
        node(n_w2, [$(v_2, 9)$], shape: rect, fill: rgb("#e1f5fe"))
        
        // Operation / Read nodes
        node(n_r1, [$op_5 \ R: (v_0, 0)$], shape: rect, stroke: (dash: "dashed"))
        node(n_r2, [$op_9 \ R: (v_1, 5)$], shape: rect, stroke: (dash: "dashed"))
        node(n_audit, [$Audit: (v_2, 9)$], shape: rect, stroke: (dash: "dashed"))

        // Edges representing lifecycle
        edge(n_init, n_r1, "->", label: "Read consumes Write")
        edge(n_r1, n_w1, "..>", label: "Op produces Write")
        edge(n_w1, n_r2, "->")
        edge(n_r2, n_w2, "..>")
        edge(n_w2, n_audit, "->")
      }
    )
  ],
  caption: [The lifecycle of a single memory address. Solid boxes represent $S_"in"$ ($Init union W$), dashed boxes represent $S_"out"$ ($R union Audit$). If the multisets are identical, every arrow connects a valid Write to a valid Read.],
) <fig:mem-lifecycle>

== Connecting to Grand Products

To verify the multiset equality condition $Init union W equiv R union Audit$ efficiently, we treat the tuples as field elements.

// We can map a tuple $\tau = (a, v, t)$ to a single field element using random linear combination (RLC). The Verifier samples random weights $\rho_1, \rho_2, \rho_3 \in \mathbb{F}$ and defines:
// $ \text{compress}(\tau) = a \cdot \rho_1 + v \cdot \rho_2 + t \cdot \rho_3 $

// By the Schwartz-Zippel lemma, if two multisets of tuples are distinct, their multisets of compressed values will also be distinct with high probability.

// We then verify multiset equality by checking the equality of their characteristic polynomials, or more simply, by checking the Grand Product of the terms:
// $ \prod_{\tau \in Init \cup W} (X - \text{compress}(\tau)) = \prod_{\tau \in R \cup Audit} (X - \text{compress}(\tau)) $

// By binding $X$ to a random challenge $\gamma$, this reduces to proving:
// $ \frac{\prod_{\tau \in Init \cup W} (\gamma - \text{compress}(\tau))}{\prod_{\tau \in R \cup Audit} (\gamma - \text{compress}(\tau))} = 1 $

This specific check can be proven in $O(M)$ time using the specialized GKR protocol (or similar Grand Product arguments) described in @sec:specialized-gkr. This provides us with a Linear Prover and sublinear Verifier for arbitrary RAM correctness.

== Implications for Lasso and Jolt

This offline memory checking technique is the primitive underlying **lookup arguments**. In the context of Lasso:
- The "Memory" is a Read-Only Table (where $Init$ contains the table values).
- The "Operations" are the Lookups into that table.
// - Since the table is Read-Only, $v_{new}$ is always equal to $v_{old}$, and the timestamp logic simplifies or is handled via counts.

By proving that the multiset of Lookups is contained in the multiset of the Table (plus appropriate counts), we achieve the core mechanism of modern efficient SNARKs.
