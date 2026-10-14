import WormaldTournament.Nonsingular
import WormaldTournament.Square
import WormaldTournament.Hessian

/-!
# Tournaments

`A` is the 0/1 adjacency matrix of a tournament on `Fin d`, `S = A - Aᵀ` its skew matrix and `J`
the all-ones matrix. This file connects the general statements to tournaments:

* `conj6_algebraic`: for every tournament, `det(d²I + S²)` and `det(d²I - S²)` are nonzero and
  their ratio is the square of a nonzero rational (the paper's Theorem 1.1 shows that `d / H`
  equals this ratio, so this is Wormald's Conjecture 6);
* `I + 2A = J + S`, and for a regular tournament `JS = SJ = 0` and `J² = dJ`, so
  `N = (I + 2A)/d = P + Y` with `P = J/d`, `Y = S/d`, `P² = P` and `PY = YP = 0`, which are the
  hypotheses of `hessian_identity`;
* `regular_hessian_det`: for a regular tournament, the determinant of `I + R#N + (R#N)ᵀ` equals
  `det(d²I + S²) / det(d²I - S²)`;
* `mul_transpose_skew`: for a regular tournament, `SSᵀ = 4AAᵀ + (2 - d)J - I`, so `SSᵀ = dI - J`
  exactly when `AAᵀ = ((d + 1)I + (d - 3)J)/4`, i.e. when the tournament is doubly regular.
-/

open Matrix Finset

namespace WormaldTournament

variable {d : ℕ}

/-- The 0/1 adjacency matrix of a tournament on `Fin d`. -/
structure IsTournament (A : Matrix (Fin d) (Fin d) ℤ) : Prop where
  zero_one : ∀ i j, A i j = 0 ∨ A i j = 1
  diag : ∀ i, A i i = 0
  anti : ∀ i j, i ≠ j → A i j + A j i = 1

/-- A tournament is regular of out-degree `m` (then `d = 2m + 1`). -/
def IsRegular (A : Matrix (Fin d) (Fin d) ℤ) (m : ℤ) : Prop := ∀ i, ∑ j, A i j = m

/-- The skew matrix `S = A - Aᵀ`. -/
def skew (A : Matrix (Fin d) (Fin d) ℤ) : Matrix (Fin d) (Fin d) ℤ := A - Aᵀ

/-- The all-ones matrix. -/
def allOnes (d : ℕ) : Matrix (Fin d) (Fin d) ℤ := Matrix.of fun _ _ => 1

lemma skew_transpose (A : Matrix (Fin d) (Fin d) ℤ) : (skew A)ᵀ = -skew A := by
  simp [skew, transpose_sub]

lemma abs_skew_le {A : Matrix (Fin d) (Fin d) ℤ} (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (i j : Fin d) : |skew A i j| ≤ 1 := by
  simp only [skew, Matrix.sub_apply, transpose_apply]
  rcases h01 i j with h | h <;> rcases h01 j i with h' | h' <;> simp [h, h']

/-- The skew matrix of a 0/1 matrix, read over `ℝ`, is skew-symmetric with entries in `[-1, 1]`. -/
lemma isSignSkew_skew {A : Matrix (Fin d) (Fin d) ℤ} (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    IsSignSkew ((Int.castRingHom ℝ).mapMatrix (skew A)) := by
  constructor
  · rw [RingHom.mapMatrix_apply, ← transpose_map, skew_transpose]
    ext i j
    simp
  · intro i j
    simp only [RingHom.mapMatrix_apply, map_apply, eq_intCast]
    exact_mod_cast abs_skew_le h01 i j

lemma map_cast_add (S : Matrix (Fin d) (Fin d) ℤ) :
    (Int.castRingHom ℝ).mapMatrix (((d ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) + S * S) =
      (d : ℝ) ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) +
        (Int.castRingHom ℝ).mapMatrix S * (Int.castRingHom ℝ).mapMatrix S := by
  rw [map_add, map_mul, map_intCast]
  congr 1
  ext i j
  rw [Matrix.intCast_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, one_apply_ne h]

lemma map_cast_sub (S : Matrix (Fin d) (Fin d) ℤ) :
    (Int.castRingHom ℝ).mapMatrix (((d ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) - S * S) =
      (d : ℝ) ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) -
        (Int.castRingHom ℝ).mapMatrix S * (Int.castRingHom ℝ).mapMatrix S := by
  rw [map_sub, map_mul, map_intCast]
  congr 1
  ext i j
  rw [Matrix.intCast_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, one_apply_ne h]

/-- **Wormald's Conjecture 6, algebraic form.** For every 0/1 matrix `A` (in particular every
tournament) with skew matrix `S = A - Aᵀ`, the determinants of `d²I + S²` and `d²I - S²` are
nonzero and `det(d²I - S²) / det(d²I + S²)` is the square of a nonzero rational. -/
theorem conj6_algebraic {A : Matrix (Fin d) (Fin d) ℤ} (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    (((d ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) + skew A * skew A).det ≠ 0 ∧
    (((d ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) - skew A * skew A).det ≠ 0 ∧
    ∃ r : ℚ, r ≠ 0 ∧
      ((((d ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) - skew A * skew A).det : ℚ) /
        ((((d ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) + skew A * skew A).det : ℚ) = r ^ 2 := by
  have hs := isSignSkew_skew h01
  have hp : (((d ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) + skew A * skew A).det ≠ 0 := by
    intro h0
    apply hs.det_add_ne_zero
    rw [← map_cast_add, ← RingHom.map_det, h0, map_zero]
  have hm : (((d ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) - skew A * skew A).det ≠ 0 := by
    intro h0
    apply hs.det_sub_ne_zero
    rw [← map_cast_sub, ← RingHom.map_det, h0, map_zero]
  exact ⟨hp, hm, by
    simpa using ratio_isSquare (skew A) (skew_transpose A) (d : ℤ) (by simpa using hp)
      (by simpa using hm)⟩

/-- `I + 2A = J + S` for a tournament. -/
theorem one_add_two_mul_eq {A : Matrix (Fin d) (Fin d) ℤ} (hA : IsTournament A) :
    1 + 2 • A = allOnes d + skew A := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, skew, Matrix.sub_apply, transpose_apply, allOnes,
    of_apply]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  by_cases h : i = j
  · subst h
    simp [hA.diag]
  · have := hA.anti i j h
    simp only [one_apply_ne h]
    linarith

/-- In a regular tournament of out-degree `m`, every in-degree is `d - 1 - m`. -/
lemma col_sum {A : Matrix (Fin d) (Fin d) ℤ} (hA : IsTournament A) {m : ℤ} (hR : IsRegular A m)
    (i : Fin d) : ∑ j, A j i = (d - 1 : ℤ) - m := by
  have e : ∀ j, A j i = (if j = i then 0 else 1) - (if j = i then 0 else A i j) := by
    intro j
    by_cases h : j = i
    · subst h; simp [hA.diag]
    · have := hA.anti i j (Ne.symm h)
      simp [h]
      linarith
  rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_sub_distrib]
  have h1 : ∑ j : Fin d, (if j = i then (0 : ℤ) else 1) = (d - 1 : ℤ) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.filter_ne' univ i, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
    have : 1 ≤ d := i.pos
    push_cast [this]
    ring
  have h2 : ∑ j : Fin d, (if j = i then (0 : ℤ) else A i j) = m := by
    rw [← hR i]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j = i
    · subst h; simp [hA.diag]
    · simp [h]
  rw [h1, h2]

/-- `S J = 0` for a regular tournament with `d = 2m + 1`. -/
lemma skew_mul_allOnes {A : Matrix (Fin d) (Fin d) ℤ} (hA : IsTournament A) {m : ℤ}
    (hR : IsRegular A m) (hd : (d : ℤ) = 2 * m + 1) : skew A * allOnes d = 0 := by
  ext i j
  simp only [mul_apply, skew, allOnes, of_apply, mul_one, Matrix.sub_apply, transpose_apply,
    Finset.sum_sub_distrib, Matrix.zero_apply]
  rw [hR i, col_sum hA hR i, hd]
  ring

/-- `J S = 0` for a regular tournament with `d = 2m + 1`. -/
lemma allOnes_mul_skew {A : Matrix (Fin d) (Fin d) ℤ} (hA : IsTournament A) {m : ℤ}
    (hR : IsRegular A m) (hd : (d : ℤ) = 2 * m + 1) : allOnes d * skew A = 0 := by
  ext i j
  simp only [mul_apply, skew, allOnes, of_apply, one_mul, Matrix.sub_apply, transpose_apply,
    Finset.sum_sub_distrib, Matrix.zero_apply]
  rw [hR j, col_sum hA hR j, hd]
  ring

lemma allOnes_mul_self : allOnes d * allOnes d = (d : ℤ) • allOnes d := by
  ext i j
  simp [allOnes, mul_apply]

/-- Integer matrices read over `ℚ`. -/
abbrev toQ : Matrix (Fin d) (Fin d) ℤ →+* Matrix (Fin d) (Fin d) ℚ := (Int.castRingHom ℚ).mapMatrix

/-- `P = J/d`, the projection onto the constant vectors. -/
def projP (d : ℕ) : Matrix (Fin d) (Fin d) ℚ := (d : ℚ)⁻¹ • toQ (allOnes d)

/-- `Y = S/d`. -/
def scaledY (A : Matrix (Fin d) (Fin d) ℤ) : Matrix (Fin d) (Fin d) ℚ := (d : ℚ)⁻¹ • toQ (skew A)

lemma toQ_intCast (c : ℤ) :
    toQ ((c : Matrix (Fin d) (Fin d) ℤ)) = (c : ℚ) • (1 : Matrix (Fin d) (Fin d) ℚ) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.intCast_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, one_apply_ne h]

lemma toQ_allOnes_mul_self :
    toQ (allOnes d) * toQ (allOnes d) = (d : ℚ) • toQ (allOnes d) := by
  ext i j
  simp [allOnes, mul_apply]

/-- For a regular tournament, `P = J/d` and `Y = S/d` over `ℚ` satisfy the hypotheses of
`hessian_identity`, `N = (I + 2A)/d` equals `P + Y`, and the determinant of
`I + (I - Y)⁻¹Y + ((I - Y)⁻¹Y)ᵀ` is `det(d²I + S²) / det(d²I - S²)`. -/
theorem regular_hessian_det {A : Matrix (Fin d) (Fin d) ℤ} (hA : IsTournament A) {m : ℤ}
    (hR : IsRegular A m) (hd : (d : ℤ) = 2 * m + 1) :
    (d : ℚ)⁻¹ • (1 + 2 • toQ A) = projP d + scaledY A ∧
    projP d * projP d = projP d ∧ projP d * scaledY A = 0 ∧ scaledY A * projP d = 0 ∧
    (scaledY A)ᵀ = -scaledY A ∧
    (1 + (1 - scaledY A)⁻¹ * scaledY A + ((1 - scaledY A)⁻¹ * scaledY A)ᵀ).det =
      ((((d ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) + skew A * skew A).det : ℚ) /
        ((((d ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) - skew A * skew A).det : ℚ) := by
  have hdpos : (0 : ℚ) < d := by
    have : (0 : ℤ) < (d : ℤ) := by omega
    exact_mod_cast this
  have hd0 : (d : ℚ) ≠ 0 := hdpos.ne'
  have hSJ : toQ (skew A) * toQ (allOnes d) = 0 := by
    rw [← map_mul, skew_mul_allOnes hA hR hd, map_zero]
  have hJS : toQ (allOnes d) * toQ (skew A) = 0 := by
    rw [← map_mul, allOnes_mul_skew hA hR hd, map_zero]
  have hN : (d : ℚ)⁻¹ • (1 + 2 • toQ A) = projP d + scaledY A := by
    have e := congrArg toQ (one_add_two_mul_eq hA)
    rw [map_add, map_one, map_nsmul, map_add] at e
    rw [e, smul_add, projP, scaledY]
  have hP : projP d * projP d = projP d := by
    rw [projP, smul_mul_smul_comm, toQ_allOnes_mul_self, smul_smul]
    congr 1
    field_simp
  have hPY : projP d * scaledY A = 0 := by
    rw [projP, scaledY, smul_mul_smul_comm, hJS, smul_zero]
  have hYP : scaledY A * projP d = 0 := by
    rw [projP, scaledY, smul_mul_smul_comm, hSJ, smul_zero]
  have hYT : (scaledY A)ᵀ = -scaledY A := by
    rw [scaledY, transpose_smul, RingHom.mapMatrix_apply, ← transpose_map, skew_transpose,
      ← smul_neg]
    congr 1
  refine ⟨hN, hP, hPY, hYP, hYT, ?_⟩
  set Y := scaledY A with hY
  have hscale1 : (1 : Matrix (Fin d) (Fin d) ℚ) + Y * Y = ((d : ℚ) ^ 2)⁻¹ •
      (toQ (((d ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) + skew A * skew A)) := by
    rw [map_add, map_mul, toQ_intCast, smul_add, hY, scaledY, smul_mul_smul_comm, smul_smul]
    congr 1
    · push_cast
      field_simp
      simp
    · congr 1
      ring
  have hscale2 : (1 : Matrix (Fin d) (Fin d) ℚ) - Y * Y = ((d : ℚ) ^ 2)⁻¹ •
      (toQ (((d ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) - skew A * skew A)) := by
    rw [map_sub, map_mul, toQ_intCast, smul_sub, hY, scaledY, smul_mul_smul_comm, smul_smul]
    congr 1
    · push_cast
      field_simp
      simp
    · congr 1
      ring
  obtain ⟨hp, hm, -⟩ := conj6_algebraic (d := d) hA.zero_one
  have hc : ((d : ℚ) ^ 2)⁻¹ ^ Fintype.card (Fin d) ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hd0))
  have hdetm : (1 - Y * Y).det ≠ 0 := by
    rw [hscale2, det_smul, ← RingHom.map_det]
    exact mul_ne_zero hc (by rw [eq_intCast]; exact_mod_cast hm)
  have h1 : IsUnit (1 - Y).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hdetm
    rw [one_sub_mul_self, det_mul, h0, zero_mul]
  have h2 : IsUnit (1 + Y).det := by
    have : (1 + Y) = (1 - Y)ᵀ := by rw [transpose_sub, transpose_one, hYT, sub_neg_eq_add]
    rw [this, det_transpose]
    exact h1
  rw [det_hessian Y hYT h1 h2, hscale1, hscale2, det_smul, det_smul, ← RingHom.map_det,
    ← RingHom.map_det, mul_div_mul_left _ _ hc]
  simp

/-- `I - Y² = d⁻² (d²I - S²)`. -/
lemma one_sub_scaledY_mul_self (A : Matrix (Fin d) (Fin d) ℤ) (hd0 : (d : ℚ) ≠ 0) :
    (1 : Matrix (Fin d) (Fin d) ℚ) - scaledY A * scaledY A = ((d : ℚ) ^ 2)⁻¹ •
      (toQ (((d ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) - skew A * skew A)) := by
  rw [map_sub, map_mul, toQ_intCast, smul_sub, scaledY, smul_mul_smul_comm, smul_smul]
  congr 1
  · push_cast
    field_simp
    simp
  · congr 1
    ring

/-- `I - Y` is invertible for every 0/1 matrix `A` (in particular every tournament). -/
lemma isUnit_one_sub_scaledY {A : Matrix (Fin d) (Fin d) ℤ}
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) (hd0 : (d : ℚ) ≠ 0) :
    IsUnit (1 - scaledY A).det := by
  obtain ⟨-, hm, -⟩ := conj6_algebraic (d := d) h01
  have hc : ((d : ℚ) ^ 2)⁻¹ ^ Fintype.card (Fin d) ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hd0))
  have hdetm : (1 - scaledY A * scaledY A).det ≠ 0 := by
    rw [one_sub_scaledY_mul_self A hd0, det_smul, ← RingHom.map_det]
    exact mul_ne_zero hc (by rw [eq_intCast]; exact_mod_cast hm)
  rw [isUnit_iff_ne_zero]
  intro h0
  apply hdetm
  rw [one_sub_mul_self, det_mul, h0, zero_mul]

/-- `SSᵀ = 4AAᵀ + (2 - d)J - I` for a regular tournament with `d = 2m + 1`. -/
theorem mul_transpose_skew {A : Matrix (Fin d) (Fin d) ℤ} (hA : IsTournament A) {m : ℤ}
    (hR : IsRegular A m) (hd : (d : ℤ) = 2 * m + 1) :
    skew A * (skew A)ᵀ = 4 • (A * Aᵀ) + (2 - (d : ℤ)) • allOnes d - 1 := by
  -- `S = 2A - J + I`
  have hS : skew A = 2 • A - allOnes d + 1 := by
    have := one_add_two_mul_eq hA
    rw [← sub_eq_iff_eq_add'.mpr this.symm]
    abel
  have hAJ : A * allOnes d = m • allOnes d := by
    ext i j
    simp [allOnes, mul_apply, hR i]
  have hJt : (allOnes d)ᵀ = allOnes d := by ext i j; simp [allOnes]
  have hJAt : allOnes d * Aᵀ = m • allOnes d := by
    have := congrArg transpose hAJ
    rw [transpose_mul, hJt, transpose_smul, hJt] at this
    exact this
  have hAAt : A + Aᵀ = allOnes d - 1 := by
    ext i j
    by_cases h : i = j
    · subst h; simp [allOnes, hA.diag]
    · have := hA.anti i j h
      simp [allOnes, one_apply_ne h, transpose_apply]
      linarith
  have hJJ := allOnes_mul_self (d := d)
  rw [hS, transpose_add, transpose_sub, transpose_smul, transpose_one, hJt]
  have e : (2 • A - allOnes d + 1) * (2 • Aᵀ - allOnes d + 1) =
      4 • (A * Aᵀ) - 2 • (A * allOnes d) - 2 • (allOnes d * Aᵀ) + allOnes d * allOnes d
        + 2 • (A + Aᵀ) - 2 • allOnes d + 1 := by
    simp only [two_nsmul, show (4 : ℕ) = 2 + 2 from rfl, add_nsmul, add_mul, mul_add, sub_mul,
      mul_sub, one_mul, mul_one]
    noncomm_ring
  rw [e, hAJ, hJAt, hJJ, hAAt, hd]
  module

end WormaldTournament
