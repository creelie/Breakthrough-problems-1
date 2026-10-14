# Two conjectures of Wormald on Hamilton cycles in tournaments

N. C. Wormald, *Tournaments with many Hamilton cycles*
([arXiv:2610.16245](https://arxiv.org/abs/2610.16245); on his Monash page since at least 2013),
lower-bounds the largest number h(n) of Hamilton cycles in an n-vertex tournament by averaging over
random blow-ups of a fixed regular tournament T on d vertices. His Theorems 1 and 4 give an expected
number ρ_R(T) g(dn), where g(n) = 2^(-n) (n-1)! and ρ_R(T) = e^(1/d) √(d/H), with H the determinant
of the Hessian of an implicit function attached to T. He computed H by computer algebra for small
examples and conjectured:

- **Conjecture 6.** For every regular tournament, H ≠ 0 and d/H is the square of a rational.
- **Conjecture 2.** For the cyclic tournaments R_d, the limit of ρ_R(R_d) as d → ∞ exists.

His fits put the limit at 2.8559579, and he conjectured that this constant is lim h(n)/g(n).

**Both conjectures hold.** For a regular tournament with skew adjacency matrix S = A − Aᵀ,

    H = d · det(d²I + S²) / det(d²I − S²),     √(d/H) = det(dI − S) / det(dI − iS),

where both determinants are positive integers. For the cyclic tournament,

    √(d/H) = ((d+1)^d + (d−1)^d) / ((d+i)^d + (d−i)^d)  →  cosh 1 / cos 1 = 2.85595789256511371…,

so Wormald's constant is cosh 1 / cos 1, and lim sup h(n)/g(n) ≥ cosh 1 / cos 1 (also for Hamilton
paths). The expansion ρ_R(R_d) = (cosh 1/cos 1)(1 − (tan 1 − tanh 1)/(3d²) + O(d⁻⁴)) has no d⁻¹ and
d⁻³ terms and a d⁻⁵ term, which is the pattern Wormald saw in his fits. Over all regular
tournaments on d vertices, ((d+1)/(d−1))^((d−1)/2) ≤ √(d/H) ≤ U_d, with equality on the left
exactly for doubly regular tournaments and lim U_d = (π²+4)(3π²−8)/((π²−4)(π²+8)) = 2.8574011776…

## What is proved, and how

The paper (`preprint/main.tex`, built into `dist/`) proves everything by hand. The Lean 4 proof
with Mathlib (v4.34.1) covers the algebra:

| Statement | Lean theorem |
|---|---|
| Conjecture 6, given Proposition 3.1 (H = det(Eᵀ F E)) | `WormaldTournament.conjecture6` |
| det(Eᵀ F E) = d · det(d²I + S²)/det(d²I − S²) | `WormaldTournament.det_conjB_hessF` |
| F = (I + Y²)(I − Y²)⁻¹ | `WormaldTournament.hessian_identity`, `det_hessian` |
| det(Eᵀ F E) = d · det F when F has unit row and column sums | `WormaldTournament.det_conjB` |
| det(d²I ± S²) ≠ 0 and their ratio is a rational square | `IsSignSkew.det_add_ne_zero`, `IsSignSkew.det_sub_ne_zero`, `ratio_isSquare`, `conj6_algebraic` |
| R_d is a regular tournament; S(I + P) = I − P; 2 det(aI + bS) = (a+b)^d + (a−b)^d | `isTournament_cyclicT`, `isRegular_cyclicT`, `cayley`, `two_mul_det_cyclic` |
| closed form for R_d, including Re (d+i)^d > 0 | `rhoT_cyclic_eq`, `re_add_I_pow_pos` |
| Conjecture 2: e^(1/d) √(d/det(Eᵀ F E)) → cosh 1/cos 1 along R_d | `WormaldTournament.conjecture2` |

```lean
theorem conjecture6 {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ} (hA : IsTournament A) {m : ℤ}
    (hR : IsRegular A m) (hd : ((n + 1 : ℕ) : ℤ) = 2 * m + 1) :
    (conjB (hessF A)).det ≠ 0 ∧
      ((n + 1 : ℕ) : ℚ) / (conjB (hessF A)).det = (detMinus A : ℚ) / (detPlus A : ℚ) ∧
      ∃ r : ℚ, r ≠ 0 ∧ ((n + 1 : ℕ) : ℚ) / (conjB (hessF A)).det = r ^ 2

theorem conjecture2 :
    Tendsto (fun m : ℕ => rhoR (cyclicT (m + 1))) atTop (𝓝 (Real.cosh 1 / Real.cos 1))
```

`lean/Check.lean` prints the axioms of 23 theorems, and `scripts/audit_axioms.py` checks that only
`propext`, `Classical.choice` and `Quot.sound` occur (`verification/axioms.txt`).

**Not formalized.** Proposition 3.1, which identifies Wormald's analytic H (the Hessian of an
implicit function) with det(Eᵀ F E), is proved in the paper by the implicit function theorem and a
second-order expansion; the Lean statements above use det(Eᵀ F E) for H. The asymptotic expansion
in Theorem 1.3 and the bounds of Theorem 1.5 are also proved only in the paper. All three are checked
by computer:

- `verification/python/wormald_hessian.py` computes H exactly from Wormald's definition (implicit
  differentiation of K = det(I − (I/2 + A) diag(y))) and compares it with the formula, for one
  regular tournament of each skew spectrum on d ≤ 9 vertices, R_11, R_13, Wormald's 7-vertex example
  and random regular tournaments on 11 and 13 vertices (41 checks).
- `verification/gp/wormald.gp` does the same symbolically in PARI/GP and compares the closed form
  for R_d with the eigenvalue product for d ≤ 61 to 60 digits.
- `verification/python/spectral_bounds.py` checks Theorem 1.5 on all classes with d ≤ 9 and on
  random regular tournaments with up to 21 vertices, and Wormald's seven 9-vertex circulants.
- `verification/python/check_paper.py` parses Table 1 and the stated values out of
  `preprint/main.tex` and recomputes all of them (142 checks), including the two corrections the
  paper makes to Wormald's text: his ρ_R(R_81) = 2.855842467… should end in …468…, and his
  factorization 53 · 297535471 is the denominator for d = 13, not d = 11.
- `verification/c/regtour.c` lists all regular tournaments on 3, 5, 7, 9 vertices with
  N⁺(0) = {1, …, m} (4, 132 and 46144 for d = 5, 7, 9) and their characteristic polynomials
  (`data/classes*.txt`).

## Layout

```
lean/                       Lean 4 + Mathlib (v4.34.1)
  WormaldTournament/        Nonsingular, Square, Hessian, Tournament, Bordered, Main, Cyclic, Limit
  Check.lean                axiom audit
verification/c/             regtour.c
verification/python/        wormald_hessian.py, spectral_bounds.py, check_paper.py
verification/gp/            wormald.gp
verification/axioms.txt     output of Check.lean
data/                       classes3.txt ... classes9.txt (output of regtour.c)
preprint/                   the paper (amsart) and its TikZ figures
dist/                       the paper as PDF, as LaTeX with PNG figures, and as an arXiv tarball
scripts/                    gen_figures.py, build_paper.sh, run_all.sh, audit_axioms.py
PRIORITY-CHECK.md           the dated check that the conjectures were still open
```

To reproduce: `scripts/run_all.sh` (C compiler, Python 3 with numpy and mpmath, PARI/GP),
`cd lean && lake exe cache get && lake build && lake env lean Check.lean`, and
`scripts/build_paper.sh` (TeX Live). The workflow `.github/workflows/verify.yml` runs all three on
every pull request.

## Author

Deep Bhattacharjee, formerly Electro-Gravitational Space Propulsion Laboratory (EGSPL),
Bhubaneswar, Odisha 751030, India. d.bhattacharjee@erl-forschung.de, itsdeep@live.com,
ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X).

The author used Claude (Anthropic) to search the literature, to run the computer checks and the
Lean formalization, and to draft the text; the author verified every step and is responsible for
the content.

MIT License.
