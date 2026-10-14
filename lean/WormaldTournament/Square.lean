import Mathlib

/-!
# `det(c²I - S²)` and `det(c²I + S²)` are squares of integers

For an integer skew-symmetric matrix `S` and an integer `c`:

* `c²I - S² = (cI - S)(cI - S)ᵀ`, so `det(c²I - S²) = det(cI - S)²`;
* over the Gaussian integers, `M = cI - iS` satisfies `conj M = Mᵀ`, so `det M` is a rational
  integer `m`, and `c²I + S² = M Mᵀ` gives `det(c²I + S²) = m²`.

Hence `det(c²I - S²) / det(c²I + S²)` is the square of a rational number whenever the denominator
is nonzero. With `c = d` and `S = A - Aᵀ` this is the second half of Wormald's Conjecture 6, once
the paper's Theorem 1.1 identifies `d / H` with this ratio.
-/

open Matrix

namespace WormaldTournament

variable {d : ℕ}

/-- `c²I - S² = (cI - S)(cI - S)ᵀ` when `Sᵀ = -S`. -/
theorem sub_mul_self_eq (S : Matrix (Fin d) (Fin d) ℤ) (hS : Sᵀ = -S) (c : ℤ) :
    ((c ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) - S * S =
      ((c : Matrix (Fin d) (Fin d) ℤ) - S) * ((c : Matrix (Fin d) (Fin d) ℤ) - S)ᵀ := by
  rw [transpose_sub, hS, transpose_intCast, sub_neg_eq_add]
  have hcomm : (c : Matrix (Fin d) (Fin d) ℤ) * S = S * (c : Matrix (Fin d) (Fin d) ℤ) :=
    Int.cast_comm c S
  calc ((c ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) - S * S
      = (c : Matrix (Fin d) (Fin d) ℤ) * (c : Matrix (Fin d) (Fin d) ℤ) +
          ((c : Matrix (Fin d) (Fin d) ℤ) * S - S * (c : Matrix (Fin d) (Fin d) ℤ)) - S * S := by
        rw [hcomm, sub_self, add_zero, sq, Int.cast_mul]
    _ = ((c : Matrix (Fin d) (Fin d) ℤ) - S) * ((c : Matrix (Fin d) (Fin d) ℤ) + S) := by
        noncomm_ring

/-- `det(c²I - S²) = det(cI - S)²` when `Sᵀ = -S`. -/
theorem det_sub_mul_self (S : Matrix (Fin d) (Fin d) ℤ) (hS : Sᵀ = -S) (c : ℤ) :
    (((c ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) - S * S).det =
      (((c : Matrix (Fin d) (Fin d) ℤ) - S).det) ^ 2 := by
  rw [sub_mul_self_eq S hS c, det_mul, det_transpose, sq]

/-- The scalar matrix `iI` over the Gaussian integers. -/
def iI : Matrix (Fin d) (Fin d) GaussianInt := Matrix.scalar (Fin d) (Zsqrtd.sqrtd : GaussianInt)

lemma iI_mul_iI : (iI : Matrix (Fin d) (Fin d) GaussianInt) * iI = -1 := by
  rw [iI, ← map_mul, Zsqrtd.dmuld, map_intCast]
  simp

lemma iI_commute (M : Matrix (Fin d) (Fin d) GaussianInt) : Commute iI M :=
  scalar_commute _ (fun r => Commute.all _ r) M

lemma iI_transpose : (iI : Matrix (Fin d) (Fin d) GaussianInt)ᵀ = iI := by
  simp [iI, scalar_apply, diagonal_transpose]

lemma conj_iI : (starRingEnd GaussianInt).mapMatrix (iI : Matrix (Fin d) (Fin d) GaussianInt) = -iI := by
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j
  · subst h
    apply Zsqrtd.ext <;> simp [iI, scalar_apply, starRingEnd_apply]
  · simp [iI, scalar_apply, h]

/-- `S` read in the Gaussian integers. -/
def gS (S : Matrix (Fin d) (Fin d) ℤ) : Matrix (Fin d) (Fin d) GaussianInt :=
  (Int.castRingHom GaussianInt).mapMatrix S

lemma conj_gS (S : Matrix (Fin d) (Fin d) ℤ) :
    (starRingEnd GaussianInt).mapMatrix (gS S) = gS S := by
  refine Matrix.ext fun i j => ?_
  apply Zsqrtd.ext <;> simp [gS]

lemma gS_transpose (S : Matrix (Fin d) (Fin d) ℤ) (hS : Sᵀ = -S) : (gS S)ᵀ = -gS S := by
  rw [gS, RingHom.mapMatrix_apply, ← transpose_map, hS]
  refine Matrix.ext fun i j => ?_
  simp

/-- The Gaussian-integer matrix `M = cI - iS`. -/
def gaussM (S : Matrix (Fin d) (Fin d) ℤ) (c : ℤ) : Matrix (Fin d) (Fin d) GaussianInt :=
  (c : Matrix (Fin d) (Fin d) GaussianInt) - iI * gS S

lemma gaussM_transpose (S : Matrix (Fin d) (Fin d) ℤ) (hS : Sᵀ = -S) (c : ℤ) :
    (gaussM S c)ᵀ = (c : Matrix (Fin d) (Fin d) GaussianInt) + iI * gS S := by
  rw [gaussM, transpose_sub, transpose_intCast, transpose_mul, gS_transpose S hS, iI_transpose,
    neg_mul, ← (iI_commute (gS S)).eq, sub_neg_eq_add]

/-- Conjugating `cI - iS` entrywise gives its transpose. -/
lemma conj_gaussM (S : Matrix (Fin d) (Fin d) ℤ) (hS : Sᵀ = -S) (c : ℤ) :
    (starRingEnd GaussianInt).mapMatrix (gaussM S c) = (gaussM S c)ᵀ := by
  rw [gaussM_transpose S hS c, gaussM, map_sub, map_mul, conj_iI, conj_gS, map_intCast, neg_mul,
    sub_neg_eq_add]

/-- `(cI - iS)(cI - iS)ᵀ = c²I + S²`, read in the Gaussian integers. -/
lemma gaussM_mul_transpose (S : Matrix (Fin d) (Fin d) ℤ) (hS : Sᵀ = -S) (c : ℤ) :
    gaussM S c * (gaussM S c)ᵀ =
      (Int.castRingHom GaussianInt).mapMatrix (((c ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) + S * S) := by
  rw [gaussM_transpose S hS c, map_add, map_mul, map_intCast, gaussM]
  change _ = _ + gS S * gS S
  have h1 : (c : Matrix (Fin d) (Fin d) GaussianInt) * (iI * gS S) =
      iI * gS S * (c : Matrix (Fin d) (Fin d) GaussianInt) := (Int.cast_comm c _)
  have h2 : iI * gS S * (iI * gS S) = -(gS S * gS S) := by
    rw [mul_assoc, ← mul_assoc (gS S), ← (iI_commute (gS S)).eq, mul_assoc, ← mul_assoc,
      iI_mul_iI, neg_one_mul]
  calc ((c : Matrix (Fin d) (Fin d) GaussianInt) - iI * gS S) *
        ((c : Matrix (Fin d) (Fin d) GaussianInt) + iI * gS S)
      = (c : Matrix (Fin d) (Fin d) GaussianInt) * (c : Matrix (Fin d) (Fin d) GaussianInt) +
          ((c : Matrix (Fin d) (Fin d) GaussianInt) * (iI * gS S) -
            iI * gS S * (c : Matrix (Fin d) (Fin d) GaussianInt)) - iI * gS S * (iI * gS S) := by
        noncomm_ring
    _ = _ := by rw [h1, sub_self, add_zero, h2, sub_neg_eq_add, sq, Int.cast_mul]

/-- `det(cI - iS)` is a rational integer. -/
lemma det_gaussM_real (S : Matrix (Fin d) (Fin d) ℤ) (hS : Sᵀ = -S) (c : ℤ) :
    (gaussM S c).det = ((gaussM S c).det.re : GaussianInt) := by
  have h : star (gaussM S c).det = (gaussM S c).det := by
    have := (starRingEnd GaussianInt).map_det (gaussM S c)
    rw [conj_gaussM S hS c, det_transpose] at this
    exact this
  have him : (gaussM S c).det.im = 0 := by
    have := congrArg Zsqrtd.im h
    simp only [Zsqrtd.im_star] at this
    linarith
  ext
  · simp
  · simp [him]

/-- `det(c²I + S²)` is the square of an integer when `Sᵀ = -S`. -/
theorem det_add_mul_self_isSquare (S : Matrix (Fin d) (Fin d) ℤ) (hS : Sᵀ = -S) (c : ℤ) :
    (((c ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) + S * S).det = ((gaussM S c).det.re) ^ 2 := by
  apply Int.cast_injective (α := GaussianInt)
  have e := (Int.castRingHom GaussianInt).map_det
    (((c ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) + S * S)
  rw [eq_intCast] at e
  rw [e, ← gaussM_mul_transpose S hS c, det_mul, det_transpose, det_gaussM_real S hS c]
  simp only [Zsqrtd.re_intCast]
  push_cast
  ring

/-- The ratio `det(c²I - S²) / det(c²I + S²)` is the square of a nonzero rational whenever both
determinants are nonzero. -/
theorem ratio_isSquare (S : Matrix (Fin d) (Fin d) ℤ) (hS : Sᵀ = -S) (c : ℤ)
    (hp : (((c ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) + S * S).det ≠ 0)
    (hm : (((c ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) - S * S).det ≠ 0) :
    ∃ r : ℚ, r ≠ 0 ∧
      ((((c ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) - S * S).det : ℚ) /
        ((((c ^ 2 : ℤ) : Matrix (Fin d) (Fin d) ℤ) + S * S).det : ℚ) = r ^ 2 := by
  have hp' := det_add_mul_self_isSquare S hS c
  have hm' := det_sub_mul_self S hS c
  have hre : (gaussM S c).det.re ≠ 0 := by
    intro h0
    rw [h0] at hp'
    exact hp (by simpa using hp')
  have hdet : ((c : Matrix (Fin d) (Fin d) ℤ) - S).det ≠ 0 := by
    intro h0
    rw [h0] at hm'
    exact hm (by simpa using hm')
  refine ⟨(((c : Matrix (Fin d) (Fin d) ℤ) - S).det : ℚ) / ((gaussM S c).det.re : ℚ), ?_, ?_⟩
  · exact div_ne_zero (by exact_mod_cast hdet) (by exact_mod_cast hre)
  · rw [hp', hm', div_pow]
    push_cast
    ring

end WormaldTournament
