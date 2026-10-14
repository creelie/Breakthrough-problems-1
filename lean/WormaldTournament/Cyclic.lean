import WormaldTournament.Main

/-!
# The cyclic tournament `R_d`

`R_d` has vertices `0, …, d - 1` (`d = 2m + 1`) and arcs `i → i + r` for `1 ≤ r ≤ m`. Its skew
adjacency matrix `S` satisfies the Cayley relation `S (I + P) = I - P`, where `P` is the shift by
`m + 1`. Since `P` is conjugate to the cyclic shift `C`, and `det(aI + bC) = a^d + b^d` for odd `d`,

  `2 det(aI + bS) = (a + b)^d + (a - b)^d`

over every commutative ring. With `a = d`, `b = ∓1` and `b = ±i` this gives
`det(d²I - S²) = (((d + 1)^d + (d - 1)^d) / 2)²` and `det(d²I + S²) = (Re (d + i)^d)²`.
-/

open Matrix Finset

namespace WormaldTournament

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The cyclic shift on `Fin (n + 1)`: `C i j = 1` iff `j = i + 1`. -/
def shiftM (n : ℕ) (R : Type*) [CommRing R] : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j => if j = i + 1 then 1 else 0

lemma castSucc_add_one_val (i : Fin n) : ((Fin.castSucc i + 1 : Fin (n + 1)) : ℕ) = i + 1 := by
  rw [Fin.val_add_one_of_lt (Fin.castSucc_lt_last i), Fin.val_castSucc]

/-- `det(aI + bC) = a^(n+1) + b^(n+1)` when `n` is even and positive. -/
theorem det_smul_one_add_smul_shift (hn : Even n) (hn0 : n ≠ 0) (a b : R) :
    (a • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) + b • shiftM n R).det =
      a ^ (n + 1) + b ^ (n + 1) := by
  set M := a • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) + b • shiftM n R with hM
  have hentry : ∀ i j, M i j = (if i = j then a else 0) + (if j = i + 1 then b else 0) := by
    intro i j
    simp only [hM, shiftM, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, of_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero]
  have h0 : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  -- the minor at the last row and column is upper triangular with diagonal `a`
  have hup : (M.submatrix (Fin.last n).succAbove (Fin.last n).succAbove).det = a ^ n := by
    rw [Fin.succAbove_last, det_of_isUpperTriangular]
    · have hd : ∀ i : Fin n, M (Fin.castSucc i) (Fin.castSucc i) = a := by
        intro i
        rw [hentry]
        have : Fin.castSucc i ≠ Fin.castSucc i + 1 := by
          intro h
          have := congrArg Fin.val h
          rw [castSucc_add_one_val, Fin.val_castSucc] at this
          omega
        rw [ite_eq_left rfl, ite_eq_right this, add_zero]
      simp [submatrix_apply, hd]
    · intro i j hij
      have hij' : (j : ℕ) < i := hij
      simp only [submatrix_apply]
      rw [hentry]
      have h1 : Fin.castSucc i ≠ Fin.castSucc j := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      have h2 : Fin.castSucc j ≠ Fin.castSucc i + 1 := by
        intro h
        have := congrArg Fin.val h
        rw [castSucc_add_one_val, Fin.val_castSucc] at this
        omega
      rw [ite_eq_right h1, ite_eq_right h2, add_zero]
  -- the minor at the last row and the first column is lower triangular with diagonal `b`
  have hlow : (M.submatrix (Fin.last n).succAbove (0 : Fin (n + 1)).succAbove).det = b ^ n := by
    rw [Fin.succAbove_last, Fin.succAbove_zero, det_of_isLowerTriangular]
    · have hd : ∀ i : Fin n, M (Fin.castSucc i) (Fin.succ i) = b := by
        intro i
        rw [hentry]
        have h1 : Fin.castSucc i ≠ Fin.succ i := by
          intro h
          have := congrArg Fin.val h
          simp at this
        have h2 : Fin.succ i = Fin.castSucc i + 1 := by
          ext
          rw [castSucc_add_one_val, Fin.val_succ]
        rw [ite_eq_right h1, ite_eq_left h2, zero_add]
      simp [submatrix_apply, hd]
    · intro i j hij
      have hij' : (i : ℕ) < j := hij
      simp only [submatrix_apply]
      rw [hentry]
      have h1 : Fin.castSucc i ≠ Fin.succ j := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      have h2 : Fin.succ j ≠ Fin.castSucc i + 1 := by
        intro h
        have := congrArg Fin.val h
        rw [castSucc_add_one_val, Fin.val_succ] at this
        omega
      rw [ite_eq_right h1, ite_eq_right h2, add_zero]
  have hl0 : Fin.last n ≠ 0 := h0.symm
  have hM0 : M (Fin.last n) 0 = b := by
    rw [hentry, ite_eq_right hl0, ite_eq_left (Fin.last_add_one n).symm, zero_add]
  have hMl : M (Fin.last n) (Fin.last n) = a := by
    rw [hentry, ite_eq_left rfl, Fin.last_add_one, ite_eq_right hl0, add_zero]
  rw [det_succ_row M (Fin.last n), Fintype.sum_eq_add 0 (Fin.last n) h0]
  · rw [hup, hlow, hM0, hMl, Fin.val_zero, Fin.val_last, add_zero, hn.neg_one_pow,
      (hn.add hn).neg_one_pow]
    ring
  · intro x ⟨hx0, hxl⟩
    rw [hentry]
    have h1 : Fin.last n ≠ x := fun h => hxl h.symm
    have h2 : x ≠ Fin.last n + 1 := by rw [Fin.last_add_one]; exact hx0
    rw [ite_eq_right h1, ite_eq_right h2, add_zero, mul_zero, zero_mul]


/-! ### Wormald's cyclic tournament -/

section Cyclic

open Fin.NatCast

variable (m : ℕ)

/-- Wormald's cyclic tournament `R_d` on `d = 2m + 1` vertices: `i → j` iff `j - i ∈ {1, …, m}`
modulo `d`. -/
def cyclicT : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℤ :=
  Matrix.of fun i j =>
    if 1 ≤ ((j - i : Fin (2 * m + 1)) : ℕ) ∧ ((j - i : Fin (2 * m + 1)) : ℕ) ≤ m then 1 else 0

/-- The entries of the skew adjacency matrix of `R_d`, as a function of `j - i`. -/
def sgnC (k : ℕ) : ℤ := if k = 0 then 0 else if k ≤ m then 1 else -1

variable {m}

lemma val_sub_ne {d : ℕ} [NeZero d] {i j : Fin d} (h : i ≠ j) :
    ((j - i : Fin d) : ℕ) ≠ 0 := by
  intro h0
  apply h
  have : j - i = 0 := Fin.ext (by rw [h0]; simp)
  exact (sub_eq_zero.mp this).symm

lemma val_sub_swap {d : ℕ} [NeZero d] {i j : Fin d} (h : i ≠ j) :
    ((i - j : Fin d) : ℕ) = d - ((j - i : Fin d) : ℕ) := by
  rw [← neg_sub, Fin.val_neg']
  have h1 := val_sub_ne h
  have h2 := (j - i).isLt
  exact Nat.mod_eq_of_lt (by omega)

lemma skew_cyclicT :
    skew (cyclicT m) = Matrix.of fun i j => sgnC m ((j - i : Fin (2 * m + 1)) : ℕ) := by
  ext i j
  simp only [skew, cyclicT, Matrix.sub_apply, transpose_apply, of_apply, sgnC]
  by_cases h : i = j
  · subst h
    simp
  · rw [val_sub_swap h]
    have h1 := val_sub_ne h
    have h2 := (j - i).isLt
    split_ifs <;> omega

theorem isTournament_cyclicT : IsTournament (cyclicT m) where
  zero_one i j := by
    simp only [cyclicT, of_apply]
    split_ifs <;> simp
  diag i := by simp [cyclicT]
  anti i j h := by
    simp only [cyclicT, of_apply]
    rw [val_sub_swap h]
    have h1 := val_sub_ne h
    have h2 := (j - i).isLt
    split_ifs <;> omega

theorem isRegular_cyclicT : IsRegular (cyclicT m) m := by
  intro i
  simp only [cyclicT, of_apply]
  have hs := Equiv.sum_comp (Equiv.subRight i)
    (fun k : Fin (2 * m + 1) => if 1 ≤ (k : ℕ) ∧ (k : ℕ) ≤ m then (1 : ℤ) else 0)
  simp only [Equiv.subRight_apply] at hs
  rw [hs]
  rw [Fin.sum_univ_eq_sum_range (fun k => if 1 ≤ k ∧ k ≤ m then (1 : ℤ) else 0) (2 * m + 1),
    Finset.sum_boole]
  have : Finset.filter (fun k => 1 ≤ k ∧ k ≤ m) (Finset.range (2 * m + 1)) = Finset.Icc 1 m := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [this, Nat.card_Icc]
  push_cast
  omega

/-- `m + 1` as an element of `Fin (2m + 1)`. -/
def cC (m : ℕ) : Fin (2 * m + 1) := ((m + 1 : ℕ) : Fin (2 * m + 1))

lemma cC_val (hm : 1 ≤ m) : ((cC m : Fin (2 * m + 1)) : ℕ) = m + 1 := by
  rw [cC, Fin.val_natCast]
  exact Nat.mod_eq_of_lt (by omega)

/-- `2 (m + 1) = 1` in `Fin (2m + 1)`. -/
lemma two_mul_cC : (2 : Fin (2 * m + 1)) * cC m = 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · apply Fin.ext
    have h1 := (2 * cC 0 : Fin (2 * 0 + 1)).isLt
    have h2 := (1 : Fin (2 * 0 + 1)).isLt
    omega
  · apply Fin.ext
    have h2 : ((2 : Fin (2 * m + 1)) : ℕ) = 2 := by
      simp
      omega
    have h1 : ((1 : Fin (2 * m + 1)) : ℕ) = 1 := by
      simp
      omega
    rw [Fin.val_mul, cC_val hm, h2, h1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- Multiplication by `m + 1`, a permutation of `Fin (2m + 1)` with inverse multiplication by `2`. -/
def mulC (m : ℕ) : Fin (2 * m + 1) ≃ Fin (2 * m + 1) where
  toFun v := cC m * v
  invFun v := 2 * v
  left_inv v := by simp only; rw [← mul_assoc, two_mul_cC, one_mul]
  right_inv v := by simp only; rw [← mul_assoc, mul_comm (cC m) 2, two_mul_cC, one_mul]

variable (R : Type*) [CommRing R]

/-- The shift by `m + 1`: `P i j = 1` iff `j = i + (m + 1)`. -/
def shiftC (m : ℕ) : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) R :=
  Matrix.of fun i j => if j = i + cC m then 1 else 0

/-- The skew adjacency matrix of `R_d`, read in `R`. -/
def skewR (m : ℕ) : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) R :=
  Matrix.of fun i j => (sgnC m ((j - i : Fin (2 * m + 1)) : ℕ) : R)

variable {R}

lemma skew_cyclicT_map : (Int.castRingHom R).mapMatrix (skew (cyclicT m)) = skewR R m := by
  rw [skew_cyclicT]
  ext i j
  simp [skewR]

lemma shiftC_submatrix :
    (shiftC R m).submatrix (mulC m) (mulC m) = shiftM (2 * m) R := by
  ext i j
  have key : cC m * j = cC m * i + cC m ↔ j = i + 1 := by
    constructor
    · intro h
      have h' := congrArg (fun x => 2 * x) h
      simp only [mul_add, ← mul_assoc, two_mul_cC, one_mul] at h'
      exact h'
    · intro h
      rw [h, mul_add, mul_one]
  simp only [submatrix_apply, shiftC, shiftM, of_apply, mulC, Equiv.coe_fn_mk, key]

theorem det_smul_one_add_smul_shiftC (hm : 1 ≤ m) (a b : R) :
    (a • (1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) R) + b • shiftC R m).det =
      a ^ (2 * m + 1) + b ^ (2 * m + 1) := by
  rw [← det_submatrix_equiv_self (mulC m)]
  have : (a • (1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) R) + b • shiftC R m).submatrix
      (mulC m) (mulC m) = a • 1 + b • shiftM (2 * m) R := by
    ext i j
    simp only [submatrix_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      EmbeddingLike.apply_eq_iff_eq, ← shiftC_submatrix]
  rw [this]
  exact det_smul_one_add_smul_shift (even_two_mul m) (by omega) a b

lemma sub_cC_val (hm : 1 ≤ m) (x : Fin (2 * m + 1)) :
    ((x - cC m : Fin (2 * m + 1)) : ℕ) = if (x : ℕ) ≤ m then (x : ℕ) + m else (x : ℕ) - (m + 1) := by
  rw [Fin.val_sub, cC_val hm]
  have := x.isLt
  split_ifs with h
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

lemma sgnC_cayley (hm : 1 ≤ m) (k : ℕ) (hk : k ≤ 2 * m) :
    sgnC m k + sgnC m (if k ≤ m then k + m else k - (m + 1)) =
      (if k = 0 then 1 else 0) - (if k = m + 1 then 1 else 0) := by
  unfold sgnC
  split_ifs <;> omega

/-- The Cayley relation `S (I + P) = I - P`. -/
theorem cayley (hm : 1 ≤ m) : skewR R m * (1 + shiftC R m) = 1 - shiftC R m := by
  ext i l
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.sub_apply, mul_apply]
  have hsum : ∑ j, skewR R m i j * shiftC R m j l = skewR R m i (l - cC m) := by
    rw [Finset.sum_eq_single (l - cC m)]
    · simp [shiftC]
    · intro j _ hj
      have : ¬ l = j + cC m := fun h => hj (by rw [h]; abel)
      simp [shiftC, this]
    · simp
  rw [hsum]
  have e : l - cC m - i = (l - i) - cC m := by abel
  have h1 : i = l ↔ ((l - i : Fin (2 * m + 1)) : ℕ) = 0 := by
    rw [Fin.val_eq_zero_iff, sub_eq_zero, eq_comm]
  have h2 : l = i + cC m ↔ ((l - i : Fin (2 * m + 1)) : ℕ) = m + 1 := by
    rw [← sub_eq_iff_eq_add', Fin.ext_iff, cC_val hm]
  have hk := (l - i).isLt
  have key := sgnC_cayley hm ((l - i : Fin (2 * m + 1)) : ℕ) (by omega)
  have keyR := congrArg (fun z : ℤ => (z : R)) key
  simp only [skewR, shiftC, of_apply, Matrix.one_apply, e, sub_cC_val hm]
  push_cast at keyR
  simp only [h1, h2]
  exact keyR

/-- `2 det(aI + bS) = (a + b)^d + (a - b)^d` for the cyclic tournament. -/
theorem two_mul_det_cyclic (hm : 1 ≤ m) (a b : R) :
    2 * (a • (1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) R) + b • skewR R m).det =
      (a + b) ^ (2 * m + 1) + (a - b) ^ (2 * m + 1) := by
  have h1 : (a • (1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) R) + b • skewR R m) *
      (1 + shiftC R m) = (a + b) • 1 + (a - b) • shiftC R m := by
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, cayley hm]
    module
  have h2 := congrArg Matrix.det h1
  rw [det_mul, det_smul_one_add_smul_shiftC hm] at h2
  have h3 : (1 + shiftC R m).det = 2 := by
    have := det_smul_one_add_smul_shiftC (R := R) hm 1 1
    rw [one_smul, one_smul] at this
    rw [this]
    norm_num
  rw [h3] at h2
  rw [mul_comm]
  exact h2

lemma intCast_eq_smul_one {k : ℕ} (c : ℤ) :
    ((c : Matrix (Fin k) (Fin k) ℤ)) = c • (1 : Matrix (Fin k) (Fin k) ℤ) := by
  ext i j
  simp [Matrix.one_apply, Matrix.intCast_apply]

lemma skew_cyclicT_eq : skew (cyclicT m) = skewR ℤ m := by
  rw [skew_cyclicT]
  ext i j
  simp [skewR]

/-- `4 det(d²I - S²) = ((d + 1)^d + (d - 1)^d)²` for the cyclic tournament. -/
theorem four_mul_detMinus_cyclic (hm : 1 ≤ m) :
    4 * detMinus (cyclicT m) =
      ((((2 * m + 1 : ℕ) : ℤ) + 1) ^ (2 * m + 1) + (((2 * m + 1 : ℕ) : ℤ) - 1) ^ (2 * m + 1)) ^ 2 := by
  set d : ℤ := ((2 * m + 1 : ℕ) : ℤ)
  have hfac : ((d ^ 2 : ℤ) : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℤ) - skew (cyclicT m) *
      skew (cyclicT m) = (d • 1 + (-1 : ℤ) • skewR ℤ m) * (d • 1 + (1 : ℤ) • skewR ℤ m) := by
    rw [intCast_eq_smul_one, skew_cyclicT_eq]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul]
    module
  have h1 := two_mul_det_cyclic (R := ℤ) hm d (-1)
  have h2 := two_mul_det_cyclic (R := ℤ) hm d 1
  rw [detMinus, hfac, det_mul]
  calc 4 * ((d • 1 + (-1 : ℤ) • skewR ℤ m).det * (d • 1 + (1 : ℤ) • skewR ℤ m).det)
      = (2 * (d • 1 + (-1 : ℤ) • skewR ℤ m).det) * (2 * (d • 1 + (1 : ℤ) • skewR ℤ m).det) := by
        ring
    _ = _ := by rw [h1, h2]; ring

/-- `4 det(d²I + S²) = ((d + i)^d + (d - i)^d)²` for the cyclic tournament. -/
theorem four_mul_detPlus_cyclic (hm : 1 ≤ m) :
    4 * (detPlus (cyclicT m) : ℂ) =
      ((((2 * m + 1 : ℕ) : ℂ) + Complex.I) ^ (2 * m + 1) +
        (((2 * m + 1 : ℕ) : ℂ) - Complex.I) ^ (2 * m + 1)) ^ 2 := by
  have expand : (((2 * m + 1 : ℕ) : ℂ) • (1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℂ) +
      Complex.I • skewR ℂ m) * (((2 * m + 1 : ℕ) : ℂ) • 1 + (-Complex.I) • skewR ℂ m) =
      (((2 * m + 1 : ℕ) : ℂ) * ((2 * m + 1 : ℕ) : ℂ)) • 1 +
        (Complex.I * -Complex.I) • (skewR ℂ m * skewR ℂ m) := by
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul]
    module
  have hI : Complex.I * -Complex.I = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
  have hmap : (Int.castRingHom ℂ).mapMatrix
      (((((2 * m + 1 : ℕ) : ℤ) ^ 2 : ℤ) : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℤ) +
        skew (cyclicT m) * skew (cyclicT m)) =
      (((2 * m + 1 : ℕ) : ℂ) • 1 + Complex.I • skewR ℂ m) *
        (((2 * m + 1 : ℕ) : ℂ) • 1 + (-Complex.I) • skewR ℂ m) := by
    rw [expand, hI, one_smul, map_add, map_mul, skew_cyclicT_map, intCast_eq_smul_one, map_zsmul,
      map_one, ← Int.cast_smul_eq_zsmul ℂ]
    push_cast
    ring_nf
  have h1 := two_mul_det_cyclic (R := ℂ) hm ((2 * m + 1 : ℕ) : ℂ) Complex.I
  have h2 := two_mul_det_cyclic (R := ℂ) hm ((2 * m + 1 : ℕ) : ℂ) (-Complex.I)
  have e : (detPlus (cyclicT m) : ℂ) = (Int.castRingHom ℂ) (detPlus (cyclicT m)) := rfl
  rw [e, detPlus, RingHom.map_det, hmap, det_mul]
  rw [sub_eq_add_neg]
  rw [sub_neg_eq_add] at h2
  rw [sub_eq_add_neg] at h1
  linear_combination (2 * (((2 * m + 1 : ℕ) : ℂ) • 1 + (-Complex.I) • skewR ℂ m).det) * h1 +
    ((((2 * m + 1 : ℕ) : ℂ) + Complex.I) ^ (2 * m + 1) +
      (((2 * m + 1 : ℕ) : ℂ) + -Complex.I) ^ (2 * m + 1)) * h2

end Cyclic

end WormaldTournament
