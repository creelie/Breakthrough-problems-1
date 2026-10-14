import WormaldTournament.Tournament
import WormaldTournament.Bordered

/-!
# The Hessian determinant `H` and Wormald's Conjecture 6

For a regular tournament `A` on `d = n + 1` vertices put `Y = S/d` and
`F = I + (I - Y)⁻¹Y + ((I - Y)⁻¹Y)ᵀ`, which equals `I + R#N + (R#N)ᵀ` (`groupInv_mul`). The paper
(Proposition 3.1) shows that Wormald's Hessian determinant is `H = det(Bᵀ F B)`, with `B` the
matrix whose columns are `e_j - e_d`; that step is the implicit function theorem and a second-order
Taylor expansion of `det(I - N e^U)`. Given it, this file proves

  `H = d · det(d²I + S²) / det(d²I - S²)`,

so `H ≠ 0` and `d / H = det(d²I - S²) / det(d²I + S²)` is the square of a nonzero rational.
-/

open Matrix Finset

namespace WormaldTournament

variable {n : ℕ}

/-- `F = I + (I - Y)⁻¹Y + ((I - Y)⁻¹Y)ᵀ` with `Y = S/d`. -/
noncomputable def hessF (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  1 + (1 - scaledY A)⁻¹ * scaledY A + ((1 - scaledY A)⁻¹ * scaledY A)ᵀ

/-- The all-ones vector. -/
def ones (n : ℕ) : Fin (n + 1) → ℚ := fun _ => 1

lemma scaledY_mulVec_ones {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ} (hA : IsTournament A)
    {m : ℤ} (hR : IsRegular A m) (hd : ((n + 1 : ℕ) : ℤ) = 2 * m + 1) :
    scaledY A *ᵥ ones n = 0 := by
  have h := congrArg toQ (skew_mul_allOnes hA hR hd)
  ext i
  have hi := congrFun (congrFun h i) i
  simp only [map_mul, map_zero, RingHom.mapMatrix_apply, mul_apply, map_apply, allOnes, of_apply,
    Matrix.zero_apply, eq_intCast, Int.cast_one, mul_one] at hi
  simp only [scaledY, mulVec, dotProduct, ones, Matrix.smul_apply, RingHom.mapMatrix_apply,
    map_apply, eq_intCast, smul_eq_mul, mul_one, Pi.zero_apply]
  rw [← Finset.mul_sum, hi, mul_zero]

lemma ones_vecMul_scaledY {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ} (hA : IsTournament A)
    {m : ℤ} (hR : IsRegular A m) (hd : ((n + 1 : ℕ) : ℤ) = 2 * m + 1) :
    ones n ᵥ* scaledY A = 0 := by
  have h := congrArg toQ (allOnes_mul_skew hA hR hd)
  ext j
  have hj := congrFun (congrFun h j) j
  simp only [map_mul, map_zero, RingHom.mapMatrix_apply, mul_apply, map_apply, allOnes, of_apply,
    Matrix.zero_apply, eq_intCast, Int.cast_one, one_mul] at hj
  simp only [scaledY, vecMul, dotProduct, ones, Matrix.smul_apply, RingHom.mapMatrix_apply,
    map_apply, eq_intCast, smul_eq_mul, one_mul, Pi.zero_apply]
  rw [← Finset.mul_sum, hj, mul_zero]

/-- The row and column sums of `F` are all `1`. -/
lemma hessF_sums {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ} (hA : IsTournament A) {m : ℤ}
    (hR : IsRegular A m) (hd : ((n + 1 : ℕ) : ℤ) = 2 * m + 1) :
    (∀ a, ∑ b, hessF A a b = 1) ∧ (∀ b, ∑ a, hessF A a b = 1) := by
  set Y := scaledY A
  have hY1 : Y *ᵥ ones n = 0 := scaledY_mulVec_ones hA hR hd
  have h1Y : ones n ᵥ* Y = 0 := ones_vecMul_scaledY hA hR hd
  have hdet := (regular_hessian_det (d := n + 1) hA hR hd)
  obtain ⟨-, -, -, -, hYT, -⟩ := hdet
  -- `(I - Y)` fixes the all-ones vector on both sides, hence so does its inverse
  have hfix : (1 - Y) *ᵥ ones n = ones n := by rw [sub_mulVec, one_mulVec, hY1, sub_zero]
  have hfix' : ones n ᵥ* (1 - Y) = ones n := by rw [vecMul_sub, vecMul_one, h1Y, sub_zero]
  have hunit : IsUnit (1 - Y).det :=
    isUnit_one_sub_scaledY hA.zero_one (by positivity)
  have hinv1 : (1 - Y)⁻¹ *ᵥ ones n = ones n := by
    conv_lhs => rw [← hfix]
    rw [mulVec_mulVec, nonsing_inv_mul _ hunit, one_mulVec]
  have hinv1' : ones n ᵥ* (1 - Y)⁻¹ = ones n := by
    conv_lhs => rw [← hfix']
    rw [vecMul_vecMul, mul_nonsing_inv _ hunit, vecMul_one]
  -- `X = (I - Y)⁻¹ Y` has zero row and column sums
  have hX1 : ((1 - Y)⁻¹ * Y) *ᵥ ones n = 0 := by rw [← mulVec_mulVec, hY1, mulVec_zero]
  have h1X : ones n ᵥ* ((1 - Y)⁻¹ * Y) = 0 := by rw [← vecMul_vecMul, hinv1', h1Y]
  have hF1 : hessF A *ᵥ ones n = ones n := by
    simp only [hessF]
    rw [add_mulVec, add_mulVec, one_mulVec, hX1, mulVec_transpose, h1X]
    simp
  have h1F : ones n ᵥ* hessF A = ones n := by
    simp only [hessF]
    rw [vecMul_add, vecMul_add, vecMul_one, h1X, vecMul_transpose, hX1]
    simp
  constructor
  · intro a
    have := congrFun hF1 a
    simpa [mulVec, dotProduct, ones] using this
  · intro b
    have := congrFun h1F b
    simpa [vecMul, dotProduct, ones] using this

/-- `det(d²I + S²)`. -/
def detPlus {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) : ℤ :=
  (((d ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) + skew A * skew A).det

/-- `det(d²I - S²)`. -/
def detMinus {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) : ℤ :=
  (((d ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) - skew A * skew A).det

/-- **The Hessian determinant.** For a regular tournament on `d = n + 1` vertices,
`det(Bᵀ F B) = d · det(d²I + S²) / det(d²I - S²)`. -/
theorem det_conjB_hessF {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ} (hA : IsTournament A) {m : ℤ}
    (hR : IsRegular A m) (hd : ((n + 1 : ℕ) : ℤ) = 2 * m + 1) :
    (conjB (hessF A)).det = ((n + 1 : ℕ) : ℚ) * ((detPlus A : ℚ) / (detMinus A : ℚ)) := by
  obtain ⟨hrow, hcol⟩ := hessF_sums hA hR hd
  rw [det_conjB _ hrow hcol, hessF, (regular_hessian_det (d := n + 1) hA hR hd).2.2.2.2.2]
  simp only [detPlus, detMinus]
  push_cast
  ring

/-- **Wormald's Conjecture 6** (given the paper's Proposition 3.1, `H = det(Bᵀ F B)`): for every
regular tournament on `d = n + 1` vertices, `H ≠ 0` and `d / H` is the square of a nonzero
rational, namely `d / H = det(d²I - S²) / det(d²I + S²)`. -/
theorem conjecture6 {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ} (hA : IsTournament A) {m : ℤ}
    (hR : IsRegular A m) (hd : ((n + 1 : ℕ) : ℤ) = 2 * m + 1) :
    (conjB (hessF A)).det ≠ 0 ∧
      ((n + 1 : ℕ) : ℚ) / (conjB (hessF A)).det = (detMinus A : ℚ) / (detPlus A : ℚ) ∧
      ∃ r : ℚ, r ≠ 0 ∧ ((n + 1 : ℕ) : ℚ) / (conjB (hessF A)).det = r ^ 2 := by
  obtain ⟨hp, hm, r, hr, hsq⟩ := conj6_algebraic (d := n + 1) hA.zero_one
  have hp' : (detPlus A : ℚ) ≠ 0 := by exact_mod_cast hp
  have hm' : (detMinus A : ℚ) ≠ 0 := by exact_mod_cast hm
  have hdq : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hratio : ((n + 1 : ℕ) : ℚ) / (conjB (hessF A)).det = (detMinus A : ℚ) / (detPlus A : ℚ) := by
    rw [det_conjB_hessF hA hR hd]
    field_simp
  refine ⟨by rw [det_conjB_hessF hA hR hd]; exact mul_ne_zero hdq (div_ne_zero hp' hm'),
    hratio, r, hr, ?_⟩
  rw [hratio, ← hsq]
  simp [detPlus, detMinus]

end WormaldTournament
