= Introduction

The GKR protocol@gkr, is a central result in the study of succinct interactive
proofs for circuit computation. Classical research on interactive proofs often
focuses on their expressive power, showing that a computationally unbounded
prover (“Merlin”) can convince a verifier (“Arthur”) of the correctness
of intractable computations. In this setting, the verifier’s efficiency
is paramount, but the prover is assumed to have unlimited computational power.

GKR takes a different approach: it considers languages that are efficiently
computable and asks whether there exists an interactive proof in which both the
prover and the verifier run efficiently. Specifically, for any computation that
can be represented as a layered arithmetic circuit, the GKR protocol allows
a polynomial-time prover to convince a verifier, running in only logarithmic
time compared to the circuit size, of the correct output. Communication is
also polylogarithmic.

From a complexity-theoretic perspective, GKR provides a constructive
interactive proof for any layered arithmetic circuit, demonstrating that
languages in P admit proofs where the verifier runs in polylogarithmic time
in the circuit size, while the prover runs in polynomial time. The protocol
leverages the algebraic structure of circuits to achieve these bounds.

In this report, we present the general GKR protocol in @sec:gkr, detailing
its structure, soundness guarantees, and asymptotic costs. This section
mostly mirrors the GKR section of Thaler's book@thaler-book, but with the
combined-claims method replaced with techniques mirroring those used in
Libra@libra and Hyrax@hyrax. We then examine a specialized version for proving
a grand product in @sec:specialized-gkr, which leverages algebraic structure
to achieve a linear prover. This is based on Thaler's 2013 paper@thaler-2013.
This specialization proves especially useful when combined with cryptographic
techniques to turn it into a SNARK, yielding a linear prover and a sublinear
verifier, as was done with Spartan@spartan.
