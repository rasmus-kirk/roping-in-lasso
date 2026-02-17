# Document Review: "Roping in Lasso"

Reviews Done:
- Chapter 1: 1
- Chapter 2: 1
- Chapter 3: 1
- Chapter 4: 1
- Chapter 5: 1
- Chapter 6: 0

## Chapter 5 Review

### Mathematical Errors

- [x] **Line 97**: Missing parentheses: `y_1 &= w_1 + w_2 dot w_3` renders with wrong precedence. Should be `y_1 &= (w_1 + w_2) dot w_3`.
- [x] **Line 120**: Wrong codomain: `$F : Bool^s -> Bool$` should be `$F : Bool^s -> Fb$`. $F$ returns field elements, not bits.
- [x] **Line 138**: Same codomain issue: `$A, B, C : Bool^s times Bool^s -> Bool, w : Bool^s -> Bool$` — codomains should be `Fb`.
- [x] **Line 141**: Missing sum over `vec(b)`. The MLE of a matrix requires a double sum `sum_(vec(a)) sum_(vec(b))`, not just `sum_(vec(a))`.
- [x] **Line 143**: Second factor uses `tilde(C)` instead of `tilde(B)`. Expression reads A·C - C but should be A·B - C.
- [x] **Line 143**: Uses `bits^n` but `n` is undefined at this point. Should be `bits^s`.
- [x] **Line 149**: `bits` missing superscript: `sum_(vec(b) in bits)` should be `sum_(vec(b) in bits^s)`.
- [x] **Line 213**: `t_"toBits"(vec(b))` should be `t_"toInt"(vec(b))` — vectors are indexed by integers, not bitstrings.
- [x] **Line 220**: `bits^(lg(n))` should be `bits^s` (or `bits^(lg(m))`).
- [x] **Lines 237–239**: `macron(A)(vec(zeta), vec(b))` should be `macron(A)(vec(zeta))` — per @eq:macron-polys these are single-argument functions. Same for B and C.
- [x] **Line 301**: `"toBits"(v)` should just be `v` — value is a field element, not an index to convert.
- [x] **Line 336**: Uses `vec(r)` but the random point from line 330 is `vec(gamma)`.

### Grammar / Typos

- [x] **Line 70**: "The constant one, is so that" — remove comma.
- [x] **Line 101**: `&=` alignment character unnecessary in inline math.
- [x] **Line 112**: "as a functions" → "as functions".
- [x] **Line 125**: "Since the R1CS instance will only be satisfied if and only if" — dangling subordinate clause. Suggested: "The R1CS instance is satisfied if and only if".
- [x] **Line 163**: "Schwartz-Zippel applies here since if" — "since if" is awkward/redundant.
- [x] **Line 242**: "the verifier then need to verify" → "needs".

### Notation Consistency

- [x] `Bool` vs `bits` used interchangeably for {0,1} in close proximity (e.g., line 120 vs 123). Consider standardizing.
- [x] Variable `n` used in several places (lines 143, 208, 220) without formal definition in this section.
- [x] Sparse entry tuple ordering inconsistent: defined as (v, c, r) at line 294 but written as (v, r, c) at line 317.
- [x] R1CS equation sides swapped between line 11 and line 85 (minor).
