# Document Review: "Roping in Lasso"

Reviews Done:
- Chapter 1: 0
- Chapter 2: 1
- Chapter 3: 1
- Chapter 4: 1
- Chapter 5: 1
- Chapter 6: 1
- Chapter 7: 1
- Chapter 8: 1

## Chapter 2: Prerequisites (`02-prerequisites/00-prerequisites.typ`)

### Errors (mathematical)

6. **Line 122: Computational indistinguishability formula issues.** Two
   problems: (a) the quantifier should be over PPT distinguishers
   $\mathcal{A}$, not over $x$; (b) the notation is inconsistent — one
   probability uses `->` and the other uses `=`. The standard form is
   `$|Pr[A(D_1) = 1] - Pr[A(D_2) = 1]| <= negl(lambda)$`.

## Chapter 8: Lasso (`08-lasso/00-lasso.typ`)

### Structural

16. **Line 370: Section ends abruptly.** The verifier cost subsection stops
    after the batched cost expression with no simplification or concluding
    paragraph. At minimum, a final simplified expression and a sentence or two
    summarising the overall Lasso costs would close the chapter.

17. **Lines 187–192: Stale commented-out paragraph.** Should be removed.

18. **No soundness discussion.** The section gives no soundness bound for the
    overall Lasso lookup argument. Even a brief union-bound over the
    constituent sumcheck, productcheck, and memory-checking errors (similar to
    the treatment in §4.5 for GKR) would strengthen the chapter.
