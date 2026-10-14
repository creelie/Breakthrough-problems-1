import WormaldTournament.Cyclic

/-!
# Wormald's constants and Conjecture 2

`ρ_T(T) = √(d / H)` and `ρ_R(T) = e^{1/d} ρ_T(T)` are the constants of Wormald's Theorems 4 and 1,
with `H = det(Bᵀ F B)` (the paper's Proposition 3.1). For the cyclic tournament,

  `ρ_T(R_d) = ((d + 1)^d + (d - 1)^d) / (2 Re (d + i)^d)
            = ((1 + 1/d)^d + (1 - 1/d)^d) / (2 Re (1 + i/d)^d)`,

which tends to `(e + e⁻¹) / (2 cos 1) = cosh 1 / cos 1`; so does `ρ_R(R_d)`. This is Wormald's
Conjecture 2, with the value of the limit.
-/

open Matrix Finset

namespace WormaldTournament

/-! ### The constants `ρ_T` and `ρ_R`, and Conjecture 2 -/

section Limit

open Filter Topology

/-- Wormald's Hessian determinant `H`, through the paper's Proposition 3.1: `H = det(Bᵀ F B)`. -/
noncomputable def hessDet {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) : ℚ :=
  (conjB (hessF A)).det

/-- `ρ_T = √(d / H)` (Wormald's Theorem 4). -/
noncomputable def rhoT {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) : ℝ :=
  Real.sqrt (((n + 1 : ℕ) : ℝ) / (hessDet A : ℝ))

/-- `ρ_R = e^{1/d} ρ_T` (Wormald's Theorem 1). -/
noncomputable def rhoR {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) : ℝ :=
  Real.exp (1 / ((n + 1 : ℕ) : ℝ)) * rhoT A

theorem div_hessDet_real {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ} (hA : IsTournament A)
    {m : ℤ} (hR : IsRegular A m) (hd : ((n + 1 : ℕ) : ℤ) = 2 * m + 1) :
    ((n + 1 : ℕ) : ℝ) / (hessDet A : ℝ) = (detMinus A : ℝ) / (detPlus A : ℝ) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (conjecture6 hA hR hd).2.1
  simp only [Rat.cast_div, Rat.cast_natCast, Rat.cast_intCast] at h
  rw [hessDet]
  exact h

variable {m : ℕ}

lemma add_I_pow_add_sub_I_pow (x : ℝ) (k : ℕ) :
    ((x : ℂ) + Complex.I) ^ k + ((x : ℂ) - Complex.I) ^ k =
      ((2 * (((x : ℂ) + Complex.I) ^ k).re : ℝ) : ℂ) := by
  have : ((x : ℂ) - Complex.I) ^ k = (starRingEnd ℂ) (((x : ℂ) + Complex.I) ^ k) := by
    rw [map_pow, map_add, Complex.conj_ofReal, Complex.conj_I, sub_eq_add_neg]
  rw [this, Complex.add_conj]

theorem detPlus_cyclic_real (hm : 1 ≤ m) :
    (detPlus (cyclicT m) : ℝ) =
      (((((2 * m + 1 : ℕ) : ℝ) : ℂ) + Complex.I) ^ (2 * m + 1)).re ^ 2 := by
  have h := four_mul_detPlus_cyclic hm
  rw [show (((2 * m + 1 : ℕ) : ℂ)) = ((((2 * m + 1 : ℕ) : ℝ) : ℂ)) by push_cast; rfl,
    add_I_pow_add_sub_I_pow] at h
  have h' : (((4 * (detPlus (cyclicT m) : ℝ)) : ℝ) : ℂ) =
      (((2 * (((((2 * m + 1 : ℕ) : ℝ) : ℂ) + Complex.I) ^ (2 * m + 1)).re) ^ 2 : ℝ) : ℂ) := by
    push_cast
    push_cast at h
    exact h
  have := Complex.ofReal_injective h'
  nlinarith [this]

theorem detMinus_cyclic_real (hm : 1 ≤ m) :
    (detMinus (cyclicT m) : ℝ) =
      (((((2 * m + 1 : ℕ) : ℝ) + 1) ^ (2 * m + 1) + (((2 * m + 1 : ℕ) : ℝ) - 1) ^ (2 * m + 1)) / 2) ^ 2 := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (four_mul_detMinus_cyclic hm)
  push_cast at h ⊢
  rw [div_pow, show ((2 : ℝ)) ^ 2 = 4 by norm_num]
  linarith

/-- **`d / H` for the cyclic tournament.** With `d = 2m + 1`,
`d / H = (((d + 1)^d + (d - 1)^d) / (2 Re (d + i)^d))²`. -/
theorem div_hessDet_cyclic (hm : 1 ≤ m) :
    ((2 * m + 1 : ℕ) : ℝ) / (hessDet (cyclicT m) : ℝ) =
      (((((2 * m + 1 : ℕ) : ℝ) + 1) ^ (2 * m + 1) + (((2 * m + 1 : ℕ) : ℝ) - 1) ^ (2 * m + 1)) /
        (2 * (((((2 * m + 1 : ℕ) : ℝ) : ℂ) + Complex.I) ^ (2 * m + 1)).re)) ^ 2 := by
  have hd : (((2 * m + 1 : ℕ) : ℕ) : ℤ) = 2 * (m : ℤ) + 1 := by push_cast; ring
  rw [div_hessDet_real isTournament_cyclicT isRegular_cyclicT hd, detMinus_cyclic_real hm,
    detPlus_cyclic_real hm]
  ring

theorem rhoT_cyclic (hm : 1 ≤ m) :
    rhoT (cyclicT m) =
      |((((2 * m + 1 : ℕ) : ℝ) + 1) ^ (2 * m + 1) + (((2 * m + 1 : ℕ) : ℝ) - 1) ^ (2 * m + 1)) /
        (2 * (((((2 * m + 1 : ℕ) : ℝ) : ℂ) + Complex.I) ^ (2 * m + 1)).re)| := by
  rw [rhoT, div_hessDet_cyclic hm, Real.sqrt_sq_eq_abs]

/-- `Re (k + i)^k > 0`: the argument of `k + i` is `arctan (1/k) ≤ 1/k`, so `k · arg < π/2`. -/
theorem re_add_I_pow_pos (k : ℕ) (hk : 1 ≤ k) : 0 < ((((k : ℝ) : ℂ) + Complex.I) ^ k).re := by
  set z : ℂ := ((k : ℝ) : ℂ) + Complex.I with hzdef
  have hre : z.re = k := by simp [z]
  have him : z.im = 1 := by simp [z]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hz0 : z ≠ 0 := fun h => by simp [h] at him
  have hz : z ^ k = ((‖z‖ ^ k : ℝ) : ℂ) * Complex.exp (((k * z.arg : ℝ) : ℂ) * Complex.I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
    rw [mul_pow, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  rw [hz, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  refine mul_pos (pow_pos (norm_pos_iff.mpr hz0) _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
  · have h0 : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr (by rw [him]; norm_num)
    have := Real.pi_pos
    nlinarith
  · have h1 : z.arg < Real.pi / 2 := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hre]; exact hkpos))
    have h0 : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr (by rw [him]; norm_num)
    have htan : Real.tan z.arg = 1 / k := by rw [Complex.tan_arg, hre, him]
    have harc : z.arg = Real.arctan (1 / k) := by
      rw [← htan, Real.arctan_tan (by linarith [Real.pi_pos]) h1]
    have hle : z.arg ≤ 1 / k := harc ▸ Real.arctan_le_self (by positivity)
    have hk1 : (k : ℝ) * z.arg ≤ 1 := by
      calc (k : ℝ) * z.arg ≤ k * (1 / k) := mul_le_mul_of_nonneg_left hle hkpos.le
        _ = 1 := by field_simp
    linarith [Real.pi_gt_three]

/-- **`ρ_T` of the cyclic tournament.** `ρ_T(R_d) = ((d + 1)^d + (d - 1)^d) / (2 Re (d + i)^d)`. -/
theorem rhoT_cyclic_eq (hm : 1 ≤ m) :
    rhoT (cyclicT m) =
      ((((2 * m + 1 : ℕ) : ℝ) + 1) ^ (2 * m + 1) + (((2 * m + 1 : ℕ) : ℝ) - 1) ^ (2 * m + 1)) /
        (2 * (((((2 * m + 1 : ℕ) : ℝ) : ℂ) + Complex.I) ^ (2 * m + 1)).re) := by
  rw [rhoT_cyclic hm, abs_of_pos]
  have hpos := re_add_I_pow_pos (2 * m + 1) (by omega)
  have h1 : (0 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) - 1 := by push_cast; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have h2 : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) + 1 := by positivity
  positivity

/-- The normalized form of the ratio, `((1 + 1/k)^k + (1 - 1/k)^k) / (2 Re (1 + i/k)^k)`. -/
noncomputable def cycRatio (k : ℕ) : ℝ :=
  ((1 + 1 / (k : ℝ)) ^ k + (1 - 1 / (k : ℝ)) ^ k) / (2 * ((1 + Complex.I / (k : ℂ)) ^ k).re)

lemma cycRatio_eq (k : ℕ) (hk : k ≠ 0) :
    (((k : ℝ) + 1) ^ k + ((k : ℝ) - 1) ^ k) / (2 * ((((k : ℝ) : ℂ) + Complex.I) ^ k).re) =
      cycRatio k := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have e1 : (k : ℝ) + 1 = k * (1 + 1 / k) := by field_simp
  have e2 : (k : ℝ) - 1 = k * (1 - 1 / k) := by field_simp
  have e3 : ((k : ℝ) : ℂ) + Complex.I = ((k : ℝ) : ℂ) * (1 + Complex.I / (k : ℂ)) := by
    have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    push_cast
    field_simp
  have e4 : ((((k : ℝ) : ℂ) + Complex.I) ^ k).re = (k : ℝ) ^ k * ((1 + Complex.I / (k : ℂ)) ^ k).re := by
    rw [e3, mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  rw [e1, e2, e4, mul_pow, mul_pow, ← mul_add, cycRatio]
  have hkk : (k : ℝ) ^ k ≠ 0 := pow_ne_zero _ hk'
  rw [show 2 * ((k : ℝ) ^ k * ((1 + Complex.I / (k : ℂ)) ^ k).re) =
      (k : ℝ) ^ k * (2 * ((1 + Complex.I / (k : ℂ)) ^ k).re) by ring, mul_div_mul_left _ _ hkk]

lemma tendsto_cycRatio :
    Tendsto cycRatio atTop (𝓝 ((Real.exp 1 + Real.exp (-1)) / (2 * Real.cos 1))) := by
  have hA := Real.tendsto_one_add_div_pow_exp 1
  have hB : Tendsto (fun n : ℕ => (1 - 1 / (n : ℝ)) ^ n) atTop (𝓝 (Real.exp (-1))) := by
    refine (Real.tendsto_one_add_div_pow_exp (-1)).congr fun n => ?_
    rw [show (1 : ℝ) + -1 / n = 1 - 1 / n by ring]
  have hC := (Complex.continuous_re.tendsto _).comp (Complex.tendsto_one_add_div_pow_exp Complex.I)
  have hcos : (Complex.exp Complex.I).re = Real.cos 1 := by
    simpa using Complex.exp_ofReal_mul_I_re 1
  rw [hcos] at hC
  have h2 : 2 * Real.cos 1 ≠ 0 := by have := Real.cos_one_pos; positivity
  have := (hA.add hB).div (hC.const_mul 2) h2
  refine this.congr fun k => ?_
  simp only [cycRatio, Function.comp_apply, Pi.div_apply]

/-- **Wormald's Conjecture 2.** `ρ_R(R_d) → cosh 1 / cos 1` as `d → ∞` through odd values. -/
theorem conjecture2 :
    Tendsto (fun m : ℕ => rhoR (cyclicT (m + 1))) atTop (𝓝 (Real.cosh 1 / Real.cos 1)) := by
  have hD : Tendsto (fun m : ℕ => 2 * (m + 1) + 1) atTop atTop :=
    tendsto_atTop_mono (fun m => by simp only [id]; omega) tendsto_id
  have hexp : Tendsto (fun m : ℕ => Real.exp (1 / ((2 * (m + 1) + 1 : ℕ) : ℝ))) atTop (𝓝 1) := by
    have : Tendsto (fun m : ℕ => 1 / ((2 * (m + 1) + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hD
    have h := (Real.continuous_exp.tendsto 0).comp this
    rw [Real.exp_zero] at h
    exact h
  have hrat := (continuous_abs.tendsto _).comp (tendsto_cycRatio.comp hD)
  have hlim := hexp.mul hrat
  have hval : 1 * |(Real.exp 1 + Real.exp (-1)) / (2 * Real.cos 1)| = Real.cosh 1 / Real.cos 1 := by
    have hc := Real.cos_one_pos
    rw [one_mul, abs_of_pos (by positivity), Real.cosh_eq]
    field_simp
  rw [hval] at hlim
  refine hlim.congr fun m => ?_
  simp only [Function.comp_apply, rhoR]
  rw [rhoT_cyclic (by omega), cycRatio_eq _ (by omega)]

end Limit

end WormaldTournament
