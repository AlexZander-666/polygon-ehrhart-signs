import Polygon.FormalCosine
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

/-! Bernoulli and odd Dirichlet series formulas for the formal logarithm of secant. -/
namespace Polygon.FormalCosine

open PowerSeries
open scoped PowerSeries

local notation "𝐄[" a "]" => rescale a (exp ℂ)

/-- The actual coefficients of the even powers of the formal log-secant. -/
noncomputable def c (k : ℕ) : ℝ := coeff (2 * k) logSec

private theorem eulerPower (z : ℂ) (hz : z ^ 2 = -1) :
    𝐄[z] = cos ℂ + C z * sin ℂ := by
  ext n
  rw [coeff_rescale, coeff_exp, map_add, coeff_C_mul]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have hd : 2 * k / 2 = k := by omega
    simp [sin, cos, hd, pow_mul z, hz, div_eq_mul_inv]
  · have hd : (2 * k + 1) / 2 = k := by omega
    simp [sin, cos, hd, pow_succ z (2 * k), pow_mul z, hz, div_eq_mul_inv]
    ring

/-- The normalized cotangent obtained from the Bernoulli generating series. -/
noncomputable def normalizedCot : ℂ⟦X⟧ :=
  rescale (2 * Complex.I) (bernoulliPowerSeries ℂ) + C Complex.I * X

theorem normalizedCot_mul_sin : normalizedCot * sin ℂ = X * cos ℂ := by
  have hb := congrArg (rescale (2 * Complex.I)) (bernoulliPowerSeries_mul_exp_sub_one ℂ)
  change rescale (2 * Complex.I) (bernoulliPowerSeries ℂ * (exp ℂ - 1)) =
    rescale (2 * Complex.I) X at hb
  rw [map_mul, map_sub, map_one, rescale_X] at hb
  have ep := eulerPower Complex.I Complex.I_sq
  have em := eulerPower (-Complex.I) (by rw [neg_sq, Complex.I_sq])
  have cancel : 𝐄[Complex.I] * 𝐄[-Complex.I] = 1 := by
    rw [exp_mul_exp_eq_exp_add, add_neg_cancel]
    simp
  have factor : 𝐄[2 * Complex.I] - 1 =
      C (2 * Complex.I) * (sin ℂ * 𝐄[Complex.I]) := by
    have doubling : 𝐄[2 * Complex.I] = 𝐄[Complex.I] * 𝐄[Complex.I] := by
      rw [exp_mul_exp_eq_exp_add, two_mul]
    rw [doubling, ← cancel, ← mul_sub, ep, em, map_neg, map_mul]
    rw [show C (2 : ℂ) = 2 from map_ofNat _ _]
    ring
  have cnz : C (2 * Complex.I) ≠ (0 : ℂ⟦X⟧) := by
    intro h
    have h₀ := congrArg constantCoeff h
    simp [Complex.I_ne_zero] at h₀
  rw [factor, mul_left_comm] at hb
  have hc := mul_left_cancel₀ cnz hb
  have hd := congrArg (fun f : ℂ⟦X⟧ ↦ f * 𝐄[-Complex.I]) hc
  rw [mul_assoc _ _ 𝐄[-Complex.I], mul_assoc _ _ 𝐄[-Complex.I], cancel, mul_one] at hd
  unfold normalizedCot
  rw [add_mul, hd, em, map_neg]
  ring

private theorem sin_double :
    rescale (2 : ℂ) (sin ℂ) = 2 * (sin ℂ * cos ℂ) := by
  have h := congrArg (PowerSeries.map Complex.ofRealHom) ((add_angles 1 1).2)
  simp only [cosAt, sinAt, map_add, map_mul, ← rescale_map, map_sin, map_cos] at h
  norm_num [rescale_one] at h
  linear_combination h

private theorem cos_double :
    rescale (2 : ℂ) (cos ℂ) = (cos ℂ)^2 - (sin ℂ)^2 := by
  have h := congrArg (PowerSeries.map Complex.ofRealHom) ((add_angles 1 1).1)
  simp only [cosAt, sinAt, map_sub, map_mul, ← rescale_map, map_sin, map_cos] at h
  norm_num [rescale_one] at h
  simpa only [pow_two] using h

private theorem sin_ne_zero : sin ℂ ≠ 0 := by
  intro h
  have hc := congrArg (coeff 1) h
  norm_num [sin] at hc

private theorem cos_ne_zero : cos ℂ ≠ 0 := by
  intro h
  have hc := congrArg (coeff 0) h
  norm_num [cos] at hc

/-- The difference between consecutive scales of normalized cotangent gives normalized tangent. -/
theorem cot_difference_mul_cos :
    (normalizedCot - rescale 2 normalizedCot) * cos ℂ = X * sin ℂ := by
  have h := congrArg (rescale (2 : ℂ)) normalizedCot_mul_sin
  change rescale 2 (normalizedCot * sin ℂ) = rescale 2 (X * cos ℂ) at h
  rw [map_mul, map_mul, rescale_X, sin_double, cos_double,
    show C (2 : ℂ) = 2 from map_ofNat _ _] at h
  have h' : rescale 2 normalizedCot * (sin ℂ * cos ℂ) =
      X * ((cos ℂ)^2 - (sin ℂ)^2) := by
    have ht : (2 : ℂ⟦X⟧) ≠ 0 := by
      intro hzero
      have hc := congrArg (constantCoeff (R := ℂ)) hzero
      rw [← map_ofNat (C (R := ℂ)) 2, constantCoeff_C] at hc
      norm_num at hc
    apply mul_right_cancel₀ ht
    linear_combination h
  apply mul_right_cancel₀ sin_ne_zero
  linear_combination cos ℂ * normalizedCot_mul_sin - h'


private theorem derivative_cos_real :
    derivative ℝ (cos ℝ) = -(sin ℝ) := by
  ext n
  rw [coeff_derivative, map_neg]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · simp [sin, cos]
  · simp [sin, cos, (show Even (2 * k + 1 + 1) from ⟨k + 1, by omega⟩),
      (show (2 * k + 1 + 1) / 2 = k + 1 by omega), (show (2 * k + 1) / 2 = k by omega),
      Nat.factorial_succ, pow_succ]
    field_simp

/-- Scaled formal derivative of the actual log-secant. -/
theorem mapped_logSec_derivative :
    PowerSeries.map Complex.ofRealHom (X * derivative ℝ logSec) =
      normalizedCot - rescale 2 normalizedCot := by
  have h₀ : constantCoeff (cos ℝ) = 1 := by norm_num [← coeff_zero_eq_constantCoeff_apply, cos]
  have h := Polygon.TraceSeries.times_derivative_logOf h₀
  rw [derivative_cos_real] at h
  have hreal : (X * derivative ℝ logSec) * cos ℝ = X * sin ℝ := by
    rw [logSec, map_neg]
    linear_combination -X * h
  have hc := congrArg (PowerSeries.map Complex.ofRealHom) hreal
  simp only [map_mul, map_X, map_cos, map_sin] at hc
  rw [map_mul, map_X]
  exact mul_right_cancel₀ cos_ne_zero (hc.trans cot_difference_mul_cos.symm)

/-- Bernoulli formula before replacing the Bernoulli number by Euler's zeta value. -/
theorem two_mul_c_bernoulli {k : ℕ} (hk : 0 < k) :
    2 * (k : ℝ) * c k =
      (-1 : ℝ) ^ k * (2 : ℝ) ^ (2 * k) * (1 - (2 : ℝ) ^ (2 * k)) *
        (bernoulli (2 * k) : ℝ) / (2 * k).factorial := by
  have hi : 2 * k ≠ 1 := by omega
  have hpred : 2 * k - 1 + 1 = 2 * k := by omega
  have h := congrArg (coeff (2 * k)) mapped_logSec_derivative
  rw [coeff_map] at h
  have hshift (f : ℝ⟦X⟧) : coeff (2 * k) (X * f) = coeff (2 * k - 1) f := by
    simpa only [hpred] using coeff_succ_X_mul (2 * k - 1) f
  rw [hshift, coeff_derivative, hpred] at h
  rw [map_sub, coeff_rescale, normalizedCot, map_add, coeff_rescale, coeff_C_mul, coeff_X,
    if_neg hi, mul_zero, add_zero] at h
  have hcast : ((2 * k - 1 : ℕ) : ℝ) + 1 = 2 * (k : ℝ) := by exact_mod_cast hpred
  rw [hcast, mul_pow, pow_mul Complex.I, Complex.I_sq] at h
  have hAlg (r : ℚ) : (algebraMap ℚ ℂ) r = (r : ℂ) := rfl
  simp only [bernoulliPowerSeries, coeff_mk, hAlg, Complex.ofRealHom_eq_coe] at h
  apply Complex.ofReal_injective
  unfold c
  push_cast at h ⊢
  linear_combination h

/-- The positive odd part of the Dirichlet series at exponent 2k. -/
noncomputable def sigma (k : ℕ) : ℝ :=
  ∑' n : ℕ, 1 / (2 * (n : ℝ) + 1) ^ (2 * k)

private theorem even_terms_summable {k : ℕ} (hk : 0 < k) :
    Summable (fun n : ℕ ↦ 1 / ((2 * n : ℕ) : ℝ) ^ (2 * k)) := by
  exact (hasSum_zeta_nat (by omega : k ≠ 0)).summable.comp_injective
    (show Function.Injective (fun n : ℕ ↦ 2 * n) from by intro a b h; dsimp at h; omega)

theorem sigma_summable {k : ℕ} (hk : 0 < k) :
    Summable (fun n : ℕ ↦ 1 / (2 * (n : ℝ) + 1) ^ (2 * k)) := by
  have h := (hasSum_zeta_nat (by omega : k ≠ 0)).summable.comp_injective
    (show Function.Injective (fun n : ℕ ↦ 2 * n + 1) from by intro a b h; dsimp at h; omega)
  simpa [Function.comp_def, Nat.cast_add, Nat.cast_mul] using h

/-- Separating the odd and even terms of the convergent zeta series. -/
theorem sigma_zeta {k : ℕ} (hk : 0 < k) :
    sigma k = (1 - 1 / (2 : ℝ) ^ (2 * k)) * ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * k) := by
  let f (n : ℕ) : ℝ := 1 / (n : ℝ) ^ (2 * k)
  have ho : Summable (fun n : ℕ ↦ f (2 * n + 1)) := by
    simpa only [f, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using sigma_summable hk
  have h := tsum_even_add_odd (f := f) (even_terms_summable hk) ho
  have he : (∑' n : ℕ, f (2 * n)) = (1 / (2 : ℝ) ^ (2 * k)) * ∑' n : ℕ, f n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp [f]
    rw [Nat.cast_mul, Nat.cast_ofNat, mul_pow, one_div_mul_one_div]
  have hs : (∑' n : ℕ, f (2 * n + 1)) = sigma k := by
    simp only [f, sigma, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [he, hs, add_comm] at h
  rw [sub_mul, one_mul]
  exact eq_sub_of_add_eq h

/-- Exact log-secant coefficient in the normalization used by the polygon trace. -/
theorem c_eq_sigma {k : ℕ} (hk : 0 < k) :
    c k = (4 / Real.pi ^ 2) ^ k * sigma k / (k : ℝ) := by
  let q := (2 : ℝ) ^ (2 * k)
  let p := Real.pi ^ (2 * k)
  let Z := ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * k)
  let b := (bernoulli (2 * k) : ℝ) / (2 * k).factorial
  have hq : q ≠ 0 := by dsimp [q]; positivity
  have hp : p ≠ 0 := by dsimp [p]; positivity
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hB : 2 * (k : ℝ) * c k = (-1 : ℝ) ^ k * q * (1 - q) * b := by
    rw [two_mul_c_bernoulli hk]
    dsimp [q, b]
    ring
  have hS : q * sigma k = (q - 1) * Z := by
    rw [sigma_zeta hk]
    change q * ((1 - 1 / q) * Z) = (q - 1) * Z
    field_simp
  have hZ : 2 * Z = -(-1 : ℝ) ^ k * q * p * b := by
    have hz := (hasSum_zeta_nat (by omega : k ≠ 0)).tsum_eq
    have ht : (2 : ℝ) ^ (2 * k - 1) * 2 = q := by
      rw [← pow_succ, show 2 * k - 1 + 1 = 2 * k by omega]
    change Z = _ at hz
    rw [pow_succ] at hz
    dsimp [p, b]
    linear_combination 2 * hz - (-1 : ℝ) ^ k * Real.pi ^ (2 * k) *
      (bernoulli (2 * k) : ℝ) / (2 * k).factorial * ht
  have target : (k : ℝ) * p * c k = q * sigma k := by
    linear_combination (p * hB - 2 * hS - (q - 1) * hZ) / 2
  have hf : (4 / Real.pi ^ 2) ^ k = q / p := by
    dsimp [q, p]
    rw [div_pow, ← pow_mul, pow_mul (2 : ℝ)]
    norm_num
  rw [hf]
  field_simp
  linear_combination target

theorem sigma_one : sigma 1 = Real.pi ^ 2 / 8 := by
  rw [sigma_zeta (by decide : 0 < 1)]
  have hz : (∑' n : ℕ, 1 / (n : ℝ) ^ (2 * 1)) = Real.pi ^ 2 / 6 :=
    hasSum_zeta_two.tsum_eq
  rw [hz]
  ring

theorem sigma_one_le {k : ℕ} (hk : 0 < k) : 1 ≤ sigma k := by
  have h := (sigma_summable hk).sum_le_tsum {0} (fun n _ ↦ by positivity)
  simpa [sigma] using h

theorem sigma_antitone {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) : sigma b ≤ sigma a := by
  apply (sigma_summable (ha.trans_le hab)).tsum_le_tsum _ (sigma_summable ha)
  intro n
  have h : 1 ≤ 2 * (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ h (by omega))

theorem sigma_bounds {k : ℕ} (hk : 0 < k) :
    1 ≤ sigma k ∧ sigma k ≤ Real.pi ^ 2 / 8 ∧ Real.pi ^ 2 / 8 < 5 / 4 := by
  refine ⟨sigma_one_le hk, (sigma_antitone (by decide : 0 < 1) hk).trans_eq sigma_one, ?_⟩
  have ht : Real.pi < 63 / 20 := by linarith [Real.pi_lt_d2]
  have h := pow_lt_pow_left₀ ht Real.pi_pos.le (by decide : (2 : ℕ) ≠ 0)
  norm_num at h
  linarith

theorem c_pos {k : ℕ} (hk : 0 < k) : 0 < c k := by
  rw [c_eq_sigma hk]
  have hσ := sigma_one_le hk
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  positivity

/-- Ratio between arbitrary positive index coefficients, with all scaling factors displayed. -/
theorem c_ratio {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    c a / c b = ((b : ℝ) / (a : ℝ)) * (Real.pi ^ 2 / 4) ^ (b - a) *
      (sigma a / sigma b) := by
  have hb := ha.trans_le hab
  have hσ : sigma b ≠ 0 := ne_of_gt (zero_lt_one.trans_le (sigma_one_le hb))
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hp : (4 / Real.pi ^ 2 : ℝ) ^ a ≠ 0 := by positivity
  have hsplit : (4 / Real.pi ^ 2 : ℝ) ^ b =
      (4 / Real.pi ^ 2) ^ a * (4 / Real.pi ^ 2) ^ (b - a) := by
    rw [← pow_add, Nat.add_sub_of_le hab]
  rw [c_eq_sigma ha, c_eq_sigma hb, hsplit]
  let u := (4 / Real.pi ^ 2 : ℝ) ^ a
  let v := (4 / Real.pi ^ 2 : ℝ) ^ (b - a)
  let w := (Real.pi ^ 2 / 4) ^ (b - a)
  have hpow : w * v = 1 := by
    dsimp [w, v]
    rw [← mul_pow, show Real.pi ^ 2 / 4 * (4 / Real.pi ^ 2) = 1 by field_simp, one_pow]
  have hv : v ≠ 0 := by dsimp [v]; positivity
  have hw : w = 1 / v := (eq_div_iff hv).mpr hpow
  change u * sigma a / (a : ℝ) / (u * v * sigma b / (b : ℝ)) =
    (b : ℝ) / (a : ℝ) * w * (sigma a / sigma b)
  rw [hw]
  field_simp
  rw [mul_comm u, mul_div_cancel_right₀ _ (show u ≠ 0 from hp)]

theorem c_ratio_le {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    c a / c b ≤ (Real.pi ^ 2 / 8) * ((b : ℝ) / (a : ℝ)) *
      (Real.pi ^ 2 / 4) ^ (b - a) := by
  have hσ : sigma a / sigma b ≤ Real.pi ^ 2 / 8 := by
    have h₁ := sigma_bounds ha
    have h₂ := sigma_one_le (ha.trans_le hab)
    apply (div_le_iff₀ (zero_lt_one.trans_le h₂)).mpr
    exact h₁.2.1.trans (by nlinarith [sq_nonneg Real.pi])
  rw [c_ratio ha hab, mul_assoc (Real.pi ^ 2 / 8), mul_comm (Real.pi ^ 2 / 8)]
  exact mul_le_mul_of_nonneg_left hσ (by positivity)

/-- Degree zero of the normalized formal logarithm. -/
theorem c_zero : c 0 = 0 := by
  have h₀ : constantCoeff (cos ℝ) = 1 := by norm_num [← coeff_zero_eq_constantCoeff_apply, cos]
  simp [c, logSec, coeff_zero_eq_constantCoeff_apply, constantCoeff_logOf h₀]

/-- The exact identity after canceling the logarithmic denominator. -/
theorem c_mul_eq {k : ℕ} (hk : 0 < k) :
    (k : ℝ) * c k = (4 / Real.pi ^ 2) ^ k * sigma k := by
  have h : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [mul_comm]
  exact (eq_div_iff h).mp (c_eq_sigma hk)

/-- The ratio with the index factors already canceled for use with the factorial ratio. -/
theorem c_normalized_ratio_le {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    ((a : ℝ) * c a) / ((b : ℝ) * c b) ≤
      (Real.pi ^ 2 / 8) * (Real.pi ^ 2 / 4) ^ (b - a) := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (ha.trans_le hab).ne'
  rw [mul_div_mul_comm]
  refine (mul_le_mul_of_nonneg_left (c_ratio_le ha hab) (by positivity)).trans_eq ?_
  field_simp

#print axioms normalizedCot_mul_sin
#print axioms cot_difference_mul_cos
#print axioms mapped_logSec_derivative
#print axioms two_mul_c_bernoulli
#print axioms sigma_zeta
#print axioms sigma_bounds
#print axioms c_eq_sigma
#print axioms c_pos
#print axioms c_ratio
#print axioms c_ratio_le
#print axioms c_zero
#print axioms c_mul_eq
#print axioms c_normalized_ratio_le

end Polygon.FormalCosine
