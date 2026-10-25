# Exact theorem and proof scope

This manuscript proves the full stated Conjectures 2 and 6 for all relevant orders. It computes Wormald's analytic Hessian from its defining implicit function and proves the rational-square property for every regular tournament, and the cyclic limit cosh(1)/cos(1). The written argument closes the analytic identification; its absence from Lean is a formalization boundary, not an assumed mathematical lemma.

The revised proof writes every first/second derivative in that identification, proves a quantitative positive-definiteness corollary, supplies an elementary spectral-radius argument and handles the zero-remainder boundary in the convex upper bound. The exact checker compares all Hessian entries, not just determinants, on 41 examples (3136 entries) and verifies the rational matrix bounds. These finite checks do not prove the universal statements.

The exact unchanged Lean source tree has a successful full build and 23 axiom reports, all using only propext, Classical.choice and Quot.sound. Analytic implicit differentiation, the asymptotic expansion, general spectral bounds and the quantitative corollary have written proofs and are not claimed as Lean-formalized. Raw run logs and source hashes accompany this audit.

The new related preprint by Divoux and Wang (https://arxiv.org/html/2610.23755v1) is credited for the broader global maximum asymptotic. The earlier claim that h(n)=Theta(g(n)) was still open has been removed. Its Proposition 7.1 also supplies the sharper finite-order determinant-ratio comparison, which is explicitly credited. That preprint is background rather than an assumption in the Hessian proof. This package makes no first-priority claim for the numerical constant or broader global theorem. The stronger finite-order maximization of Hamilton-cycle counts themselves is not a theorem claimed by this package.

The paper remains a sole-authored work of Deep Bhattacharjee. The submitting author explicitly confirmed the all-parts human-understanding declaration for Paper 8. This is a record of that declaration, not a claim that an automated audit can certify a person's understanding or journal acceptance.
