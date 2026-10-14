import Mathlib

/-!
# The matrix identity behind Wormald's Hessian

In the paper, `N = (I + 2A)/d` for a regular tournament `A`, and `N = P + Y` with `P = J/d` the
projection onto the constants and `Y = S/d`, `S = A - Aᵀ`. Then `PY = YP = 0`, and the matrix
`R = I - N` has group inverse `R# = (I - Y)⁻¹ - P`. The second-order part of `det(I - N e^U)` on
the hyperplane `K = 0` is the quadratic form of `I + R#N + (R#N)ᵀ`, and this matrix equals
`(I + Y²)(I - Y²)⁻¹`. This file proves these identities over any field, for any `P` and `Y` with
`P² = P`, `PY = YP = 0` and `Yᵀ = -Y`.
-/

open Matrix

namespace WormaldTournament

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

section GroupInverse

variable (P Y : Matrix n n K)

lemma inv_one_sub_mul_eq (hYP : Y * P = 0) (h1 : IsUnit (1 - Y).det) : (1 - Y)⁻¹ * P = P := by
  have e : (1 - Y) * P = P := by rw [sub_mul, one_mul, hYP, sub_zero]
  calc (1 - Y)⁻¹ * P = (1 - Y)⁻¹ * ((1 - Y) * P) := by rw [e]
    _ = P := by rw [← mul_assoc, nonsing_inv_mul _ h1, one_mul]

lemma mul_inv_one_sub_eq (hPY : P * Y = 0) (h1 : IsUnit (1 - Y).det) : P * (1 - Y)⁻¹ = P := by
  have e : P * (1 - Y) = P := by rw [mul_sub, mul_one, hPY, sub_zero]
  calc P * (1 - Y)⁻¹ = (P * (1 - Y)) * (1 - Y)⁻¹ := by rw [e]
    _ = P := by rw [mul_assoc, mul_nonsing_inv _ h1, mul_one]

/-- `R# = (I - Y)⁻¹ - P` is a right inverse of `R = I - (P + Y)` on the complement of `P`. -/
theorem mul_groupInv (hP : P * P = P) (hPY : P * Y = 0) (hYP : Y * P = 0)
    (h1 : IsUnit (1 - Y).det) :
    (1 - (P + Y)) * ((1 - Y)⁻¹ - P) = 1 - P := by
  have hPP' : P * (1 - Y)⁻¹ = P := mul_inv_one_sub_eq P Y hPY h1
  have e : (1 - (P + Y)) * ((1 - Y)⁻¹ - P) =
      (1 - Y) * (1 - Y)⁻¹ - P * (1 - Y)⁻¹ - (P - P * P - Y * P) := by noncomm_ring
  rw [e, mul_nonsing_inv _ h1, hPP', hYP, hP]
  noncomm_ring

/-- `R# N = (I - Y)⁻¹ Y` for `N = P + Y`. -/
theorem groupInv_mul (hP : P * P = P) (hPY : P * Y = 0) (hYP : Y * P = 0)
    (h1 : IsUnit (1 - Y).det) :
    ((1 - Y)⁻¹ - P) * (P + Y) = (1 - Y)⁻¹ * Y := by
  have hIP : (1 - Y)⁻¹ * P = P := inv_one_sub_mul_eq P Y hYP h1
  rw [sub_mul, mul_add, mul_add, hIP, hP, hPY]
  abel

end GroupInverse

section Identity

variable (Y : Matrix n n K)

lemma commute_inv_one_sub (h1 : IsUnit (1 - Y).det) : Y * (1 - Y)⁻¹ = (1 - Y)⁻¹ * Y := by
  have hc : (1 - Y) * Y = Y * (1 - Y) := by noncomm_ring
  calc Y * (1 - Y)⁻¹ = (1 - Y)⁻¹ * (1 - Y) * Y * (1 - Y)⁻¹ := by
        rw [nonsing_inv_mul _ h1, one_mul]
    _ = (1 - Y)⁻¹ * ((1 - Y) * Y) * (1 - Y)⁻¹ := by noncomm_ring
    _ = (1 - Y)⁻¹ * Y * ((1 - Y) * (1 - Y)⁻¹) := by rw [hc]; noncomm_ring
    _ = (1 - Y)⁻¹ * Y := by rw [mul_nonsing_inv _ h1, mul_one]

lemma commute_inv_one_add (h2 : IsUnit (1 + Y).det) : Y * (1 + Y)⁻¹ = (1 + Y)⁻¹ * Y := by
  have hc : (1 + Y) * Y = Y * (1 + Y) := by noncomm_ring
  calc Y * (1 + Y)⁻¹ = (1 + Y)⁻¹ * (1 + Y) * Y * (1 + Y)⁻¹ := by
        rw [nonsing_inv_mul _ h2, one_mul]
    _ = (1 + Y)⁻¹ * ((1 + Y) * Y) * (1 + Y)⁻¹ := by noncomm_ring
    _ = (1 + Y)⁻¹ * Y * ((1 + Y) * (1 + Y)⁻¹) := by rw [hc]; noncomm_ring
    _ = (1 + Y)⁻¹ * Y := by rw [mul_nonsing_inv _ h2, mul_one]

/-- The transpose of `(I - Y)⁻¹ Y` is `-Y (I + Y)⁻¹` when `Y` is skew-symmetric. -/
lemma transpose_inv_mul (hY : Yᵀ = -Y) :
    ((1 - Y)⁻¹ * Y)ᵀ = -(Y * (1 + Y)⁻¹) := by
  rw [transpose_mul, transpose_nonsing_inv, transpose_sub, transpose_one, hY, sub_neg_eq_add,
    neg_mul]

lemma one_sub_mul_self (Y : Matrix n n K) : 1 - Y * Y = (1 - Y) * (1 + Y) := by noncomm_ring

/-- The Hessian identity: `I + (I - Y)⁻¹ Y + ((I - Y)⁻¹ Y)ᵀ = (I + Y²)(I - Y²)⁻¹` for skew `Y`. -/
theorem hessian_identity (hY : Yᵀ = -Y) (h1 : IsUnit (1 - Y).det) (h2 : IsUnit (1 + Y).det) :
    1 + (1 - Y)⁻¹ * Y + ((1 - Y)⁻¹ * Y)ᵀ = (1 + Y * Y) * (1 - Y * Y)⁻¹ := by
  rw [transpose_inv_mul Y hY]
  have hW : IsUnit (1 - Y * Y).det := by
    rw [one_sub_mul_self, det_mul]
    exact h1.mul h2
  -- multiply out against `1 - Y² = (1 - Y)(1 + Y) = (1 + Y)(1 - Y)`
  have key : (1 + (1 - Y)⁻¹ * Y + -(Y * (1 + Y)⁻¹)) * (1 - Y * Y) = 1 + Y * Y := by
    have a : (1 - Y)⁻¹ * Y * (1 - Y * Y) = Y + Y * Y := by
      rw [one_sub_mul_self, ← commute_inv_one_sub Y h1]
      calc Y * (1 - Y)⁻¹ * ((1 - Y) * (1 + Y)) = Y * ((1 - Y)⁻¹ * (1 - Y)) * (1 + Y) := by
            noncomm_ring
        _ = Y + Y * Y := by rw [nonsing_inv_mul _ h1]; noncomm_ring
    have b : Y * (1 + Y)⁻¹ * (1 - Y * Y) = Y - Y * Y := by
      have e : 1 - Y * Y = (1 + Y) * (1 - Y) := by noncomm_ring
      rw [e]
      calc Y * (1 + Y)⁻¹ * ((1 + Y) * (1 - Y)) = Y * ((1 + Y)⁻¹ * (1 + Y)) * (1 - Y) := by
            noncomm_ring
        _ = Y - Y * Y := by rw [nonsing_inv_mul _ h2]; noncomm_ring
    calc (1 + (1 - Y)⁻¹ * Y + -(Y * (1 + Y)⁻¹)) * (1 - Y * Y)
        = (1 - Y * Y) + (1 - Y)⁻¹ * Y * (1 - Y * Y) - Y * (1 + Y)⁻¹ * (1 - Y * Y) := by
          noncomm_ring
      _ = 1 + Y * Y := by rw [a, b]; noncomm_ring
  calc 1 + (1 - Y)⁻¹ * Y + -(Y * (1 + Y)⁻¹)
      = (1 + (1 - Y)⁻¹ * Y + -(Y * (1 + Y)⁻¹)) * (1 - Y * Y) * (1 - Y * Y)⁻¹ := by
        rw [mul_nonsing_inv_cancel_right _ _ hW]
    _ = (1 + Y * Y) * (1 - Y * Y)⁻¹ := by rw [key]

/-- Its determinant is `det(I + Y²) / det(I - Y²)`. -/
theorem det_hessian (hY : Yᵀ = -Y) (h1 : IsUnit (1 - Y).det) (h2 : IsUnit (1 + Y).det) :
    (1 + (1 - Y)⁻¹ * Y + ((1 - Y)⁻¹ * Y)ᵀ).det = (1 + Y * Y).det / (1 - Y * Y).det := by
  rw [hessian_identity Y hY h1 h2, det_mul, det_nonsing_inv, Ring.inverse_eq_inv', div_eq_mul_inv]

end Identity

end WormaldTournament
