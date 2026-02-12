# Document Review: "Roping in Lasso"

## Critical Mathematical Errors

### 1. Equality polynomial has addition instead of multiplication (04-specialized-gkr, line 230)

The expression for `eq_v` uses addition where it should use multiplication:

```
(v_k r_k + (1 - v_k) + (1 - r_k))
```

Should be:

```
(v_k r_k + (1 - v_k)(1 - r_k))
```

This is `(1 - v_k)` **times** `(1 - r_k)`, not plus. This error appears in
lines 230, 241, 254-257, and 262 — i.e. throughout the "Computing eq in linear
time" subsection.

### 2. Mismatched `tilde("add")` duplicate (03-gkr, line 490)

> If `tilde("add"), tilde("add")` has no special structure...

Should be `tilde("add"), tilde("mul")`.

### 3. Missing `alpha` in GKR round-i protocol diagram (03-gkr, lines 377-378)

In the protocol diagram for round `i in [1..d-1]`, the combined-claim
polynomial is missing the `alpha dot` factors before the second `tilde("add")`
and `tilde("mul")` terms. Compare lines 377-378 (protocol diagram, wrong) with
lines 257-258 (prose derivation, correct).

### 4. Missing `dot` in round-0 protocol diagram (03-gkr, line 340)

The formula is missing a `dot` between `tilde("mul")_0(...)` and
`tilde(W)_1(vec(b))`. Compare with line 156 which has it.

### 5. R1CS example final line has operator precedence issue (05-omc, line 375)

The final line of the worked example renders as:

> y_1 = w_1 + w_2 dot w_3

By standard mathematical precedence this reads as `w_1 + (w_2 * w_3)`, but the
circuit computes `(w_1 + w_2) * w_3`. Needs parentheses:

```
y_1 &= (w_1 + w_2) dot w_3
```

### 6. Lookup table derivation typo (04-specialized-gkr, line 299)

Extra closing parenthesis: `sum_(vec(b))) in bits^ell)` should be
`sum_(vec(b) in bits^ell)`.

### 7. Lookup table derivation wrong index (04-specialized-gkr, line 301)

The final line uses `hat(W)_(j-1)[(0,x_(j+1), ..., x_ell)]` for **both**
terms. The second term should use `hat(W)_(j-1)[(1,x_(j+1), ..., x_ell)]`.

### 8. Verifier runtime typo (04-specialized-gkr, line 344)

> the verifier workload is proportional to the communication cost `O(n^2)`

This should be `O(lg^2(n))`, which is what was argued. `O(n^2)` is a
completely different bound.


## Structural Issues

### 9. Two sections both named "Spark" (05-omc, lines 162 and 279)

There are two `== Spark` headings in the same chapter (sections 5.2 and 5.4).
The second one (line 279) is a sentence fragment: "In our case, the prover ".

### 10. "Introducing Cryptographic Assumptions" is a stub (05-omc, line 272)

This section is a single paragraph that trails off with "More concretely, we
can introduce a _commitment scheme_." and doesn't introduce one.

### 11. Chapter intro is placeholder text (05-omc, lines 12-14)

"This chapter is dedicated to Spark..." followed by a single sentence is
clearly placeholder. The chapter titled "Spark" should have a substantive
introduction explaining what Spark is before diving into offline
memory-checking.

### 12. TODO checklist rendered in output (main.typ, lines 26-29)

The checklist items on lines 26-29 of `main.typ` will appear in the compiled
PDF. These should be wrapped in a comment or removed.

### 13. Abstract typo (main.typ, line 17)

"introcing" should be "introducing".

### 14. No Lasso or Jolt content yet

Despite the project title "Roping in Lasso", neither Lasso nor Jolt are
discussed anywhere in the document. The refs.bib also has no entries for the
Lasso or Jolt papers.


## Notation / Consistency Issues

### 15. Notation table: set `S` vs field `F` (02-prerequisites, line 20-21)

The notation table describes vectors as "elements from set `S`" but the
notation column shows `F^n`. The description should say "from field `F`" or the
notation should use `S^n`.

### 16. Misplaced comment in notation table (02-prerequisites, line 31)

The comment `// Vector-element concatenation` appears above the `bits = {0,1}`
entry, but that entry isn't about concatenation.

### 17. MLE definition is too restrictive (02-prerequisites, line 48)

The MLE is defined for `f: {0,1}^l -> {0,1}`, but throughout the document
MLEs are used for functions `f: {0,1}^l -> F` (like `W_i` mapping gate
labels to field elements). The definition should use the codomain `F`.

### 18. Range variable typo in proof (02-prerequisites, line 86)

"each `k in [1..k]`" should be "each `k in [1..ell]`".

### 19. Duplicate entry in eq-hat example (02-prerequisites, line 99)

The last entry shows `hat("eq")^(2)[(1, 0)]` twice. The second occurrence
should be `hat("eq")^(2)[(1, 1)]`.

### 20. Sumcheck uses undefined variable (02-prerequisites, line 122)

`g(b_1, ..., b_v)` uses `v` but the section defines the number of variables as
`ell`. Should be `g(b_1, ..., b_ell)`.

### 21. `mul` vs `mult` inconsistency (03-gkr)

Line 87 defines `"mul"_i` but line 111 (@eq:tilde-w) uses `tilde("mult")_i`.
These should be consistent.

### 22. RAM size variable confusion (05-omc, line 27 vs 38)

Line 27 uses `m` entries in the RAM vector, but line 38 writes
`{(1, v_1, t_1), ..., (n, v_m, t_m)}` mixing `n` addresses with `m` values.
Either clarify `m = n` or pick one variable.

### 23. Tuple equality theorem uses wrong variables (05-omc, line 184)

The theorem states `forall i in [1..n] : f_i = g_i`, but the tuples are named
`vec(a)` and `vec(b)`. Should be `a_i = b_i`.


## Minor Writing Issues

### 24. Grammar: "keeps locally stores" (05-omc, line 80)

> "Here, V keeps locally stores, and modifies, the sets WS, RS."

Should be: "Here, V locally stores and modifies the sets WS, RS."

### 25. Sentence fragment (01-introduction, lines 18-22)

> "Demonstrating that languages in P admit proofs where the verifier runs in
> polylogarithmic time in the circuit size, while the prover runs in polynomial
> time."

This is a dangling fragment from the previous sentence. The period after
"arithmetic circuit" (line 19) should be a comma (or the fragment should be
rewritten as a full sentence).

### 26. Apostrophe in plural (05-omc, line 17)

"ZKVM's" should be "ZKVMs" (no apostrophe for plurals).

### 27. "succesful" typo (03-gkr, line 158)

Should be "successful".
