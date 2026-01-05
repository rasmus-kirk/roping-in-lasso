= Conclusion

We've shown the GKR protocol and argued its soundness and costs. We've also
shown how a specialized GKR protocol with a linear prover and a verifier
bounded by $O(lg^2(n) + n)$. This protocol can be especially useful when
combined with standard cryptographic techniques (a polynomial commitment
scheme and the Fiat-Shamir Heuristic), since the $O(n)$ term can be reduced
to $O(sqrt(n))$ or even $O(lg(n))$, thus creating a SNARK with a linear prover.
