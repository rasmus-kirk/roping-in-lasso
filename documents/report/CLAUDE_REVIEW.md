# Document Review: "Roping in Lasso"

Reviews Done:
- Chapter 1: 1
- Chapter 2: 1
- Chapter 3: 1
- Chapter 4: 1
- Chapter 5: 1
- Chapter 6: 1
- Chapter 6.3: 1

## TODOs

- [ ] Define $n$ properly...

### Chapter 6.3 (Putting the Pieces Together) — First Pass

**Mathematical errors**

- [x] Lines 369–370: `mem_row` and `mem_col` have $\vec{\gamma}$ and $\vec{\zeta}$ **swapped**. From
  @eq:spark-sumcheck (line 55), $e_{\text{row}}(\vec{k}) = \tilde{\text{eq}}(\vec{\zeta},
  \text{row}(\vec{k}))$ and $e_{\text{col}}(\vec{k}) = \tilde{\text{eq}}(\vec{\gamma},
  \text{col}(\vec{k}))$. So the row RAM stores $\tilde{\text{eq}}(\vec{\zeta}, \cdot)$ and the col RAM
  stores $\tilde{\text{eq}}(\vec{\gamma}, \cdot)$. But line 369 defines
  $\tilde{\text{mem}}_{\text{row}}$ with $\text{eq}_{\vec{\gamma}}$ and line 370 defines
  $\tilde{\text{mem}}_{\text{col}}$ with $\text{eq}_{\vec{\zeta}}$ — these are backwards. Line 420
  repeats this error: $\tilde{\text{mem}}_{\text{row}}(\vec{r}) = \text{eq}_{\vec{\gamma}}(\vec{r})$
  should be $\text{eq}_{\vec{\zeta}}(\vec{r})$.
- [x] Line 420: The formula for $\tilde{\text{id}}(\vec{r})$ has a parenthesization bug. The Typst source
  writes `2^(lg(m - j))` which renders as $2^{\lg(m-j)}$, but the correct binary-decomposition
  exponent is $2^{\lg m - j}$, i.e., `2^(lg(m) - j)`.
- [x] Lines 377–391: The multiset polynomial definitions are missing the random shift $-\beta$ from
  @thm:multiset-equality-proof. Section 6.2 (line 349) correctly includes $\beta$ in the combined
  product check, but here in 6.3 each polynomial (e.g., $\text{Init}_{\text{row}}(\vec{x}) =
  \tilde{\text{id}}(\vec{x}) + \alpha \cdot \tilde{\text{mem}}_{\text{row}}(\vec{x}) + \alpha^2 \cdot
  \tilde{\text{zero}}(\vec{x})$) should have a $- \beta$ term. The products at lines 398–401 and the
  check at line 405 are similarly missing $\beta$.
- [x] Lines 361–370: The scope "For all $i \in [0, m-1]$" covers all six polynomial definitions, but
  $\tilde{\text{row}}$ and $\tilde{\text{col}}$ are only defined for $n$ nonzero entries (domain
  $\text{bits}^{\lceil\lg n\rceil}$, indices $[0, n-1]$), not $m$ RAM addresses. The scope should be
  split: one for the $m$-indexed RAM polynomials ($\tilde{\text{id}}, \tilde{\text{zero}},
  $\tilde{\text{mem}}_{\text{row}}, \tilde{\text{mem}}_{\text{col}}$) and one for the $n$-indexed sparse
  polynomials ($\tilde{\text{row}}, \tilde{\text{col}}$).
- [x] Line 322 (in section 6.2 proof, missed in earlier pass): The expanded product
  $\prod_{(b_1, \dots, b_n) \in \text{bits}}$ should be
  $\prod_{(b_1, \dots, b_{\lceil\lg n\rceil}) \in \text{bits}^{\lceil\lg n\rceil}}$. Both the tuple
  length and the `bits` superscript need updating — this was missed when the `bits^n` instances in the
  theorem statement were corrected.

**Prose / grammar**

- [x] Line 357: "One first thing notice before we start" — garbled. Should be "The first thing to
  notice before we start" or "Before we start piecing together the puzzle, note that".
- [x] Line 407: "Thus, showing the correctness of the memory-checking." — sentence fragment. Consider
  "This shows the correctness of the memory checking."

**Structural / completeness**

- [x] Lines 398–401: Only the row RAM products are shown. The column RAM needs the same four products
  ($\text{Init}_{\text{col}}, \text{WS}_{\text{col}}, \text{RS}_{\text{col}},
  \text{Audit}_{\text{col}}$) and corresponding check. At minimum, add a note like "and analogously
  for the column RAM."
- [x] Lines 393–394: "computed as in @fig:omc-verifier-procedure" is vague. Since the RAM is read-only,
  the timestamps simplify to a sequential counter (each of the $n$ reads gets timestamp $1, 2, \dots,
  n$, and the audit timestamps capture the final state). A brief note on how
  $\tilde{\text{readTS}}$ values are assigned would help the reader.
