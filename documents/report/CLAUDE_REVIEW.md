# Document Review: "Roping in Lasso"

Reviews Done:
- Chapter 1: 1
- Chapter 2: 1
- Chapter 3: 1
- Chapter 4: 1
- Chapter 5: 1
- Chapter 6: 1

## TODOs

- [ ] Line 222: "across each" should be "across all three" or "in total" — $n$ is the total across all
  three matrices, not per matrix.
- [ ] Line 175 uses $\vec{\alpha}$ as the random challenge but line 182 onward uses $\vec{\gamma}$ —
  align the notation.

### Chapter 6 (Spark) — First Pass

**Completeness**

- [ ] **"Putting the Pieces Together" section is empty (line 341).** This is the most significant issue.
  The chapter introduces all the building blocks — sparse representation, offline memory checking,
  tuple equality, multiset equality — but never actually constructs the full Spark protocol. The
  Spartan paper's section 7.2.2 shows the complete PC^SPARK construction with Commit, Open, and
  Eval. Without this, the reader is left with the pieces but no assembly instructions.

**Mathematical errors**

- [ ] Lines 45–47: The function signatures for `val`, `row`, `col` are wrong. The domain is written as
  `bits^n` but should be `bits^(ceil(lg(n)))` (since there are $n$ nonzero entries, we need
  $\lceil\lg n\rceil$ bits to index them). Additionally, the codomain of `row` and `col` is written as
  `bits^n` but should be `bits^s` (since row/column indices are $s$-bit identifiers, where
  $s = \lg m$). The codomain of `val` ($\mathbb{F}$) is correct.
- [ ] Lines 285, 297–298, 308: In the multiset equality theorem and proof, the product iterates over
  `bits^n` (i.e., $\{0,1\}^n$, the $n$-dimensional Boolean hypercube with $2^n$ elements). This
  should be `bits^(ceil(lg(n)))` ($\{0,1\}^{\lceil\lg n\rceil}$, which has $n$ elements for
  $n = 2^k$). The MLE of a set with $n$ elements is defined on a $\lceil\lg n\rceil$-dimensional
  hypercube, not an $n$-dimensional one.
- [ ] Line 107: The RAM multiset uses `n` instead of `m` at the end:
  `{ (1, v_1, t_1), ..., (n, v_m, t_m) }` — the last address should be `m` not `n`, since the RAM
  has $m$ entries and addresses range from $1$ to $m$.
- [ ] Line 335: The combined multiset product check is missing the random shift $\beta$ from the
  multiset equality theorem (@thm:multiset-equality-proof). The formula writes
  `$\prod (a + \alpha v + \alpha^2 t)$` on each side, but per the theorem it should be
  `$\prod (a + \alpha v + \alpha^2 t - \beta)$` for a random $\beta$. Alternatively the $\beta$ may
  be folded into the Init tuples, but this should be clarified.

**Prose / grammar**

- [ ] Line 14: "We left off last section" → "We left off in the last section" or "Continuing from
  the last section".
- [ ] Line 30: "This can obviously not be represented with a sumcheck" → "This obviously cannot be
  represented as a sumcheck instance" (split infinitive / awkward phrasing).
- [ ] Line 71: "A polynomial commitment to $\text{val}$ can be at this stage" → "...can be
  **computed** at this stage".
- [ ] Line 72: "the other two products of each term depends" → "depend" (subject-verb agreement:
  "products...depend").
- [ ] Line 149: "Here, $\mathscr{V}$ keeps locally stores, and modifies, the sets" → "Here,
  $\mathscr{V}$ locally stores and modifies the sets" (garbled phrasing).
- [ ] Lines 215, 222: "so when the verifier makes the check in @eq:omc-set-check will fail" —
  broken sentence structure. Should be "the check in @eq:omc-set-check will fail with probability
  one" or "when the verifier performs the check in @eq:omc-set-check, it will fail...".
- [ ] Line 98–100: "Specifically, this represents the number of times each address has been
  accessed" — not quite right. The timestamp is a global monotonically increasing counter, not a
  per-address access count. Each operation (read or write, on any address) increments the global
  counter.

**Missing references / context**

- [ ] The offline memory checking section should cite Blum, Evans, Gemmell, Kannan, Naor (1991) —
  this is [31] in the Spartan paper and is the foundational work for the technique.
- [ ] Line 337–338 says the product check is "an excellent use-case for the specialized GKR protocol"
  but doesn't explain why. A brief note (e.g., "since the specialized GKR protocol from
  @sec:specialized-gkr can efficiently prove the correctness of a product of field elements") would
  help the reader connect the dots.

**Structural / pedagogical**

- [ ] The chapter conflates Spartan's Section 6 (computation commitments — preprocessing to commit to
  $\tilde{A}, \tilde{B}, \tilde{C}$) and Section 7 (the SPARK compiler — a sparse polynomial commitment
  scheme using memory checking). This is acceptable for an educational document, but a brief
  remark distinguishing the two ideas (preprocessing vs. runtime sparse evaluation) could clarify
  the architecture for the reader.
- [ ] The coin-mint table (lines 170–179) lists WS, RS, Audit, Init in a 2x2 grid, but the equation
  is $\text{Init} \cup \text{WS} = \text{RS} \cup \text{Audit}$. Reordering the table to match the
  equation's left/right sides would make the analogy more immediate.
