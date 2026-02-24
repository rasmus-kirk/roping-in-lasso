# Roping in Lasso

Lasso and Jolt represent a shift in how we build SNARKs. Rather than encoding
every computation as a massive arithmetic circuit, Lasso shows that the bulk
of the work can be replaced by lookups into structured tables, thus enabling
the _lookup singularity_ - yielding a prover that is faster by orders of
magnitude. Jolt then applies this insight to build a practical zkVM for RISC-V.

The papers are dense. They sit at the intersection of sumcheck, GKR, R1CS,
sparse polynomial commitments, and offline memory checking - each of which
has its own body of literature. _Roping in Lasso_ is a self-contained
resource that walks through all of these building blocks from scratch, in a
single document, so that you can understand Lasso without constantly
cross-referencing half a dozen other papers.

The report covers:

1. **GKR Protocol** - The interactive proof for layered arithmetic circuits.
2. **A Specialized GKR Protocol** - A faster GKR protocol tailored to specifically grand-product arguments, employed by both Lasso and Spartan
3. **Spartan** - Encoding R1CS satisfiability as a polynomial identity verified via sumcheck
4. **Spark** - A sparse polynomial commitment scheme based on offline memory checking
5. **Lasso** - The lookup argument itself

Each chapter builds directly on the previous one, with worked examples and full
proofs throughout. The only prerequisites are basic finite field arithmetic,
comfort with polynomial notation (including multivariate polynomials) and
at least some notion of interactive arguments/proofs.
