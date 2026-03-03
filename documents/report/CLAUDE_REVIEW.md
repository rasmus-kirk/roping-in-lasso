# Document Review: "Roping in Lasso"

Reviews Done:
- Chapter 1: 1
- Chapter 2: 2
- Chapter 3: 2
- Chapter 4: 2
- Chapter 5: 2
- Chapter 6: 2
- Chapter 7: 2
- Chapter 8: 1

## Chapter 1: Introduction (`01-introduction/00-introduction.typ`)

## Chapter 2: Prerequisites (`02-prerequisites/00-prerequisites.typ`)

### Errors (mathematical)

2. **Line 123: Computational indistinguishability formula issues.** Two
   problems: (a) the quantifier `$forall x$` should be over PPT
   distinguishers $\mathcal{A}$, not over $x$; (b) the probabilities are
   written `$Pr[Ac(x) = D_1]$` and `$Pr[Ac(x) = D_2]$` — the notation
   should be `$Pr[Ac(D_1) = 1] - Pr[Ac(D_2) = 1]$` (the distinguisher
   receives a sample from the distribution and outputs a bit).

## Chapter 3: Sumcheck and MLE (`03-sumcheck-and-mle/00-sumcheck-and-mle.typ`)

## Chapter 4: GKR (`04-gkr/00-gkr.typ`)

## Chapter 5: Productcheck (`05-productcheck/00-productcheck.typ`)

### Structural

12. **Lines 318–323: Sum index not updated after absorption.** After
    absorbing the sum over $b_{j+1}, \ldots, b_\ell$ in line 320, the
    remaining sum should only range over $b_1, \ldots, b_j$, but the
    displayed index stays `$sum_(vec(b) in bits^ell)$` through line 322.

## Chapter 6: Spartan (`06-spartan/00-spartan.typ`)

## Chapter 7: Spark (`07-spark/00-spark.typ`)

**Line 64:** Only if preprocessing is done by a TTP? Better to explain this
as done only once, so it amortizes across multiple verifications of the
same circuit.

## Chapter 8: Lasso (`08-lasso/00-lasso.typ`)

### Structural

16. **Line 370: Section ends abruptly.** The verifier cost subsection stops
    after the batched cost expression with no simplification or concluding
    paragraph. At minimum, a final simplified expression and a sentence or two
    summarising the overall Lasso costs would close the chapter.

18. **No soundness discussion.** The section gives no soundness bound for the
    overall Lasso lookup argument. Even a brief union-bound over the
    constituent sumcheck, productcheck, and memory-checking errors (similar to
    the treatment in §4.5 for GKR) would strengthen the chapter.
