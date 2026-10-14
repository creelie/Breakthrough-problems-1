import Mathlib

/-!
# The matrices `d²I + S²` and `d²I - S²` are nonsingular

Let `S` be a real skew-symmetric matrix of order `d` whose entries lie in `[-1, 1]`; the skew
matrix `A - Aᵀ` of a tournament with adjacency matrix `A` is one. Then both `d²I + S²` and
`d²I - S²` are strictly diagonally dominant, hence nonsingular (Gershgorin). In the paper this gives
`H ≠ 0` (the first half of Wormald's Conjecture 6) and the finiteness of `d / H`.
-/

open Matrix Finset

namespace WormaldTournament

variable {d : ℕ}

/-- `S` is skew-symmetric with all entries in `[-1, 1]`. -/
def IsSignSkew (S : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  Sᵀ = -S ∧ ∀ i j, |S i j| ≤ 1

lemma IsSignSkew.apply_swap {S : Matrix (Fin d) (Fin d) ℝ} (h : IsSignSkew S) (i j : Fin d) :
    S j i = -S i j := by
  have := congrFun (congrFun h.1 i) j
  simpa [transpose_apply] using this

lemma IsSignSkew.diag {S : Matrix (Fin d) (Fin d) ℝ} (h : IsSignSkew S) (i : Fin d) :
    S i i = 0 := by
  have := h.apply_swap i i
  linarith

/-- Every entry of `S²` has absolute value at most `d`. -/
lemma IsSignSkew.abs_mul_self_le {S : Matrix (Fin d) (Fin d) ℝ} (h : IsSignSkew S)
    (i j : Fin d) : |(S * S) i j| ≤ d := by
  rw [mul_apply]
  calc |∑ l, S i l * S l j| ≤ ∑ l, |S i l * S l j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : Fin d, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro l _
        rw [abs_mul]
        simpa using mul_le_mul (h.2 i l) (h.2 l j) (abs_nonneg _) zero_le_one
    _ = d := by simp

lemma card_erase_fin (k : Fin d) : ((univ.erase k).card : ℝ) = (d : ℝ) - 1 := by
  rw [card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin]
  have : 1 ≤ d := k.pos
  push_cast [this]
  ring

/-- The diagonal entries of `S²` lie in `[-(d - 1), 0]`. -/
lemma IsSignSkew.mul_self_diag {S : Matrix (Fin d) (Fin d) ℝ} (h : IsSignSkew S) (i : Fin d) :
    -((d : ℝ) - 1) ≤ (S * S) i i ∧ (S * S) i i ≤ 0 := by
  have e : (S * S) i i = -∑ l, S i l ^ 2 := by
    rw [mul_apply, ← Finset.sum_neg_distrib]
    congr 1
    ext l
    rw [h.apply_swap i l]
    ring
  have hle : ∑ l, S i l ^ 2 ≤ (d : ℝ) - 1 := by
    rw [← Finset.add_sum_erase _ _ (mem_univ i), h.diag i]
    have hs : ∑ l ∈ univ.erase i, S i l ^ 2 ≤ ∑ _l ∈ univ.erase i, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro l _
      have h1 := h.2 i l
      have h2 := abs_nonneg (S i l)
      nlinarith [sq_abs (S i l)]
    rw [sum_const, nsmul_eq_mul, mul_one, card_erase_fin] at hs
    linarith
  have hnn : 0 ≤ ∑ l, S i l ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  constructor <;> linarith

/-- `d²I + S²` is nonsingular. -/
theorem IsSignSkew.det_add_ne_zero {S : Matrix (Fin d) (Fin d) ℝ} (h : IsSignSkew S) :
    ((d : ℝ) ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) + S * S).det ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  intro k
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast k.pos
  have hoff : ∀ j ∈ univ.erase k,
      ‖((d : ℝ) ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) + S * S) k j‖ ≤ d := by
    intro j hj
    have hkj : k ≠ j := (ne_of_mem_erase hj).symm
    simpa [one_apply_ne hkj, Real.norm_eq_abs] using h.abs_mul_self_le k j
  have hdiag := h.mul_self_diag k
  have hkk : ‖((d : ℝ) ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) + S * S) k k‖ =
      (d : ℝ) ^ 2 + (S * S) k k := by
    simp only [Matrix.add_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, Real.norm_eq_abs]
    apply abs_of_nonneg
    nlinarith
  calc ∑ j ∈ univ.erase k, ‖((d : ℝ) ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) + S * S) k j‖
      ≤ ∑ _j ∈ univ.erase k, (d : ℝ) := sum_le_sum hoff
    _ = ((d : ℝ) - 1) * d := by rw [sum_const, nsmul_eq_mul, card_erase_fin]
    _ < (d : ℝ) ^ 2 - ((d : ℝ) - 1) := by nlinarith
    _ ≤ _ := by rw [hkk]; linarith [hdiag.1]

/-- `d²I - S²` is nonsingular. -/
theorem IsSignSkew.det_sub_ne_zero {S : Matrix (Fin d) (Fin d) ℝ} (h : IsSignSkew S) :
    ((d : ℝ) ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) - S * S).det ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  intro k
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast k.pos
  have hoff : ∀ j ∈ univ.erase k,
      ‖((d : ℝ) ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) - S * S) k j‖ ≤ d := by
    intro j hj
    have hkj : k ≠ j := (ne_of_mem_erase hj).symm
    simpa [one_apply_ne hkj, Real.norm_eq_abs, abs_neg] using h.abs_mul_self_le k j
  have hdiag := h.mul_self_diag k
  have hkk : ‖((d : ℝ) ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) - S * S) k k‖ =
      (d : ℝ) ^ 2 - (S * S) k k := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, Real.norm_eq_abs]
    apply abs_of_nonneg
    nlinarith
  calc ∑ j ∈ univ.erase k, ‖((d : ℝ) ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) - S * S) k j‖
      ≤ ∑ _j ∈ univ.erase k, (d : ℝ) := sum_le_sum hoff
    _ = ((d : ℝ) - 1) * d := by rw [sum_const, nsmul_eq_mul, card_erase_fin]
    _ < (d : ℝ) ^ 2 := by nlinarith
    _ ≤ _ := by rw [hkk]; linarith [hdiag.2]

end WormaldTournament
