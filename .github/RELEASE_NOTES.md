Proofs of Conjectures 2 and 6 of N. C. Wormald, *Tournaments with many Hamilton cycles*
(arXiv:2610.16245). For a regular tournament on d vertices with skew adjacency matrix S, Wormald's
Hessian determinant is H = d det(d²I + S²)/det(d²I − S²), so H ≠ 0 and d/H is the square of the
rational det(dI − S)/det(dI − iS) (Conjecture 6). For the cyclic tournament,
√(d/H) = ((d+1)^d + (d−1)^d)/((d+i)^d + (d−i)^d), and ρ_R(R_d) → cosh 1/cos 1 = 2.8559578925…
(Conjecture 2), which identifies Wormald's constant 2.855958.

Attached: the paper (PDF), its LaTeX source with the figures as PNG, and the arXiv tarball. The
repository contains the Lean 4 proof with Mathlib (23 theorems, standard axioms only), the C,
Python and PARI/GP checks, and the dated priority check. Proposition 3.1 of the paper (Wormald's
analytic H equals a determinant) is a paper proof checked by exact computation, not formalised.

Author: Deep Bhattacharjee (ORCID 0000-0003-0466-750X).
