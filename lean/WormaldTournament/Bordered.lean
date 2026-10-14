import Mathlib

/-!
# Restricting a quadratic form to the hyperplane `x₁ + ⋯ + x_d = 0`

The implicit function `u_d = ψ(u₁, …, u_{d-1})` of the paper has Hessian `-Bᵀ F B` at the origin,
where `F` is a `d × d` matrix with all row and column sums equal to `1` and `B` is the `d × (d-1)`
matrix whose `j`-th column is `e_j - e_d`. This file proves `det(Bᵀ F B) = d · det F` for every such
`F`, which turns the determinant of the `(d-1) × (d-1)` Hessian into a determinant on all of `K^d`.
Here `d = n + 1` and the last index plays the role of `d`.
-/

open Matrix Finset

namespace WormaldTournament

variable {K : Type*} [Field K] {n : ℕ}

/-- The matrix `B` whose `j`-th column is `e_j - e_last`. -/
def bord (n : ℕ) : Matrix (Fin (n + 1)) (Fin n) K :=
  Matrix.of fun i j => if i = j.castSucc then 1 else if i = Fin.last n then -1 else 0

/-- The square matrix `Q = [B | 1]`. -/
def bordQ (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  Matrix.of fun i j => if h : j = Fin.last n then 1 else bord n i (j.castPred h)

/-- `Bᵀ F B`. -/
def conjB (F : Matrix (Fin (n + 1)) (Fin (n + 1)) K) : Matrix (Fin n) (Fin n) K :=
  Matrix.transpose (bord n : Matrix (Fin (n + 1)) (Fin n) K) * F * (bord n : Matrix (Fin (n + 1)) (Fin n) K)

/-- `Qᵀ F Q`. -/
def conjQ (F : Matrix (Fin (n + 1)) (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  Matrix.transpose (bordQ n : Matrix (Fin (n + 1)) (Fin (n + 1)) K) * F *
    (bordQ n : Matrix (Fin (n + 1)) (Fin (n + 1)) K)

lemma bord_castSucc (i j : Fin n) :
    (bord n (Fin.castSucc i) j : K) = if i = j then 1 else 0 := by
  simp [bord, Fin.castSucc_inj, Fin.castSucc_ne_last]

lemma bord_last (j : Fin n) : (bord n (Fin.last n) j : K) = -1 := by
  simp [bord, (Fin.castSucc_ne_last j).symm]

lemma bordQ_castSucc (i : Fin (n + 1)) (j : Fin n) :
    (bordQ n i (Fin.castSucc j) : K) = bord n i j := by
  simp [bordQ, Fin.castSucc_ne_last]

lemma bordQ_last (i : Fin (n + 1)) : (bordQ n i (Fin.last n) : K) = 1 := by
  simp [bordQ]

/-- The columns of `B` sum to zero. -/
lemma sum_bord (j : Fin n) : ∑ i, (bord n i j : K) = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp only [bord_castSucc, bord_last, sum_ite_eq', mem_univ, ite_true]
  ring

/-- Laplace expansion along the last row, when that row vanishes off the diagonal. -/
lemma det_of_last_row (X : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (h : ∀ j : Fin n, X (Fin.last n) (Fin.castSucc j) = 0) :
    X.det = X (Fin.last n) (Fin.last n) * (X.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [det_succ_row X (Fin.last n), Fin.sum_univ_castSucc]
  have hz : ∑ j : Fin n, (-1 : K) ^ ((Fin.last n : ℕ) + (Fin.castSucc j : ℕ)) *
      X (Fin.last n) (Fin.castSucc j) *
        (X.submatrix (Fin.last n).succAbove (Fin.castSucc j).succAbove).det = 0 := by
    apply sum_eq_zero
    intro j _
    rw [h j, mul_zero, zero_mul]
  rw [hz, zero_add]
  simp [Fin.succAbove_last]

lemma conjQ_last_castSucc (F : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hcol : ∀ b, ∑ a, F a b = 1) (j : Fin n) : conjQ F (Fin.last n) (Fin.castSucc j) = 0 := by
  simp only [conjQ, mul_apply, transpose_apply, bordQ_last, one_mul, bordQ_castSucc, hcol]
  exact sum_bord j

lemma conjQ_last_last (F : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hrow : ∀ a, ∑ b, F a b = 1) : conjQ F (Fin.last n) (Fin.last n) = n + 1 := by
  simp only [conjQ, mul_apply, transpose_apply, bordQ_last, one_mul, mul_one]
  rw [Finset.sum_comm]
  simp [hrow]

lemma conjQ_submatrix (F : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    (conjQ F).submatrix Fin.castSucc Fin.castSucc = conjB F := by
  ext i j
  simp [conjQ, conjB, mul_apply, transpose_apply, bordQ_castSucc]

lemma det_conjQ (F : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hrow : ∀ a, ∑ b, F a b = 1) (hcol : ∀ b, ∑ a, F a b = 1) :
    (conjQ F).det = ((n : K) + 1) * (conjB F).det := by
  rw [det_of_last_row _ (conjQ_last_castSucc F hcol), conjQ_last_last F hrow, conjQ_submatrix]

/-- `BᵀB = I + J`. -/
lemma conjB_one :
    conjB (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
      1 + replicateCol (Fin 1) (fun _ => (1 : K)) * replicateRow (Fin 1) (fun _ => (1 : K)) := by
  ext i j
  simp only [conjB, Matrix.mul_one, mul_apply, transpose_apply, Matrix.add_apply,
    replicateCol_apply, replicateRow_apply, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, one_smul]
  rw [Fin.sum_univ_castSucc]
  simp only [bord_castSucc, bord_last]
  by_cases h : i = j
  · subst h
    simp
  · rw [one_apply_ne h, Finset.sum_eq_zero]
    · ring
    · intro k _
      by_cases hk : k = i
      · subst hk; simp [h]
      · simp [hk]

lemma det_conjB_one : (conjB (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K)).det = n + 1 := by
  have h := det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) (fun _ : Fin n => (1 : K))
    (fun _ => 1)
  rw [conjB_one]
  refine h.trans ?_
  simp [dotProduct]
  ring

/-- `det(Bᵀ F B) = d · det F` for every `F` whose row and column sums are all `1`. -/
theorem det_conjB [CharZero K] (F : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hrow : ∀ a, ∑ b, F a b = 1) (hcol : ∀ b, ∑ a, F a b = 1) :
    (conjB F).det = ((n : K) + 1) * F.det := by
  have hn : (n : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h1 := det_conjQ F hrow hcol
  have hI := det_conjQ (n := n) (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (fun a => by simp [one_apply]) (fun b => by simp [one_apply])
  rw [det_conjB_one] at hI
  rw [conjQ, det_mul, det_mul, det_transpose] at h1
  rw [conjQ, Matrix.mul_one, det_mul, det_transpose] at hI
  have : ((n : K) + 1) * (conjB F).det = ((n : K) + 1) * (((n : K) + 1) * F.det) := by
    rw [← h1]
    have e : (bordQ n : Matrix (Fin (n + 1)) (Fin (n + 1)) K).det * F.det *
        (bordQ n : Matrix (Fin (n + 1)) (Fin (n + 1)) K).det =
          ((bordQ n : Matrix (Fin (n + 1)) (Fin (n + 1)) K).det *
            (bordQ n : Matrix (Fin (n + 1)) (Fin (n + 1)) K).det) * F.det := by ring
    rw [e, hI]
    ring
  exact mul_left_cancel₀ hn this

end WormaldTournament
