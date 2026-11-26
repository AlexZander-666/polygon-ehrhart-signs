import PolygonKernel.SeriesBridge
import Mathlib.NumberTheory.Bernoulli

/-! Closed coefficients of the polygon kernel from the formal Bernoulli series. -/
namespace PolygonKernel

open PowerSeries
open scoped PowerSeries

local notation "E" => fun a : ℚ ↦ rescale a (exp ℚ)

/-- The normalized reciprocal of formal sinh, expressed through Bernoulli numbers. -/
noncomputable def normalizedCsch : ℚ⟦X⟧ :=
  C (2 : ℚ) * bernoulliPowerSeries ℚ - rescale 2 (bernoulliPowerSeries ℚ)

theorem coeff_normalizedCsch (n : ℕ) :
    coeff n normalizedCsch = (2 - (2 : ℚ) ^ n) * bernoulli n / n.factorial := by
  simp [normalizedCsch, bernoulliPowerSeries, coeff_rescale]
  ring

private theorem exp_one_ne_one : E 1 - 1 ≠ 0 := by
  intro h
  have c := congrArg (coeff 1) h
  norm_num [coeff_rescale] at c

theorem normalizedCsch_mul_sinh : normalizedCsch * formalSinh = X := by
  have h₁ : bernoulliPowerSeries ℚ * (E 1 - 1) = X := by
    simpa using bernoulliPowerSeries_mul_exp_sub_one ℚ
  have h₂ := congrArg (rescale (2 : ℚ)) (bernoulliPowerSeries_mul_exp_sub_one ℚ)
  change rescale 2 (bernoulliPowerSeries ℚ * (exp ℚ - 1)) = rescale 2 X at h₂
  rw [map_mul, map_sub, map_one, rescale_X] at h₂
  change rescale 2 (bernoulliPowerSeries ℚ) * (E 2 - 1) = C (2 : ℚ) * X at h₂
  have e₂ : E 2 = E 1 ^ 2 := by
    rw [pow_two, exp_mul_exp_eq_exp_add]
    norm_num
  have hb : rescale 2 (bernoulliPowerSeries ℚ) * (E 1 + 1) =
      C (2 : ℚ) * bernoulliPowerSeries ℚ := by
    apply mul_right_cancel₀ exp_one_ne_one
    rw [mul_assoc, mul_assoc, h₁, ← h₂, e₂]
    ring
  have he : E (-1) * E 1 = 1 := by
    rw [exp_mul_exp_eq_exp_add]
    norm_num
  have hs : E 1 * formalSinh = C (1 / 2 : ℚ) * (E 2 - 1) := by
    rw [formalSinh, e₂, mul_left_comm (E 1), mul_sub, mul_comm (E 1) (E (-1)), he, pow_two]
  unfold normalizedCsch
  rw [← hb, show rescale 2 (bernoulliPowerSeries ℚ) * (E 1 + 1) -
    rescale 2 (bernoulliPowerSeries ℚ) = rescale 2 (bernoulliPowerSeries ℚ) * E 1 by ring]
  rw [mul_assoc, hs, mul_left_comm, h₂, ← mul_assoc, ← map_mul]
  norm_num

private theorem derivative_rescaled_exp (a : ℚ) :
    d⁄dX ℚ (E a) = C a * E a := by
  ext n
  rw [coeff_derivative, coeff_C_mul, coeff_rescale, coeff_rescale]
  simp only [coeff_exp, Algebra.algebraMap_self_apply, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hs : (n : ℚ) + 1 ≠ 0 := by positivity
  rw [pow_succ]
  field_simp

private theorem derivative_sinh :
    d⁄dX ℚ formalSinh = C (1 / 2 : ℚ) * (E 1 + E (-1)) := by
  rw [formalSinh, Derivation.leibniz, map_sub, derivative_C,
    derivative_rescaled_exp, derivative_rescaled_exp]
  simp [smul_eq_mul]

private theorem fivefold :
    E 5 = C (1 / 2 : ℚ) * (E 1 + E (-1)) + C 5 * formalSinh +
      formalSinh ^ 2 * (C 8 * E 1 + C 4 * E 3) := by
  have e₃ : E 3 = E 1 ^ 3 := by
    rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, pow_two,
      exp_mul_exp_eq_exp_add, exp_mul_exp_eq_exp_add]
    norm_num
  have e₅ : E 5 = E 1 ^ 2 * E 3 := by
    rw [pow_two, exp_mul_exp_eq_exp_add, exp_mul_exp_eq_exp_add]
    norm_num
  have he : E 1 * E (-1) = 1 := by
    rw [exp_mul_exp_eq_exp_add]
    norm_num
  rw [e₅, e₃, formalSinh]
  have half : C (1 / 2 : ℚ) * 2 = 1 := by
    rw [← map_ofNat (C (R := ℚ)) 2, ← map_mul]
    norm_num
  have quarter : C (1 / 2 : ℚ) ^ 2 * 4 = 1 := by
    linear_combination (2 * C (1 / 2 : ℚ) + 1) * half
  have c₄ : C (4 : ℚ) = 4 := map_ofNat _ _
  have c₅ : C (5 : ℚ) = 5 := map_ofNat _ _
  have c₈ : C (8 : ℚ) = 8 := map_ofNat _ _
  rw [c₄, c₅, c₈]
  linear_combination
    (2 * E 1 ^ 3 - E 1 ^ 2 * E (-1) - E 1 + 4 * E 1 - 2 * E (-1)) * he -
    (3 * E 1 - 2 * E (-1)) * half -
    (E 1 - E (-1)) ^ 2 * (2 * E 1 + E 1 ^ 3) * quarter

/-- Decomposition into the normalized reciprocal sinh and an entire exponential part. -/
theorem F_bernoulli_series :
    F = normalizedCsch - X * d⁄dX ℚ normalizedCsch + C 5 * X * normalizedCsch +
      X ^ 2 * (C 8 * E 1 + C 4 * E 3) := by
  symm
  apply F_eq_of_formalSinh
  have hd := congrArg (d⁄dX ℚ) normalizedCsch_mul_sinh
  rw [Derivation.leibniz, derivative_X, smul_eq_mul, smul_eq_mul] at hd
  change _ = X ^ 2 * E 5
  rw [fivefold, ← derivative_sinh]
  linear_combination
    (formalSinh + X * d⁄dX ℚ formalSinh + C 5 * X * formalSinh) *
      normalizedCsch_mul_sinh - X * formalSinh * hd

/-- The contribution from the entire part for each index at least two. -/
def regularCoeff (d : ℕ) : ℚ := (8 + 4 * (3 : ℚ) ^ (d - 2)) / (d - 2).factorial

/-- The formula applies to all indices at least two, uniformly in their parity. -/
theorem g_eq_bernoulli (d : ℕ) (hd : 2 ≤ d) :
    g d = regularCoeff d +
      (1 - (d : ℚ)) * ((2 - (2 : ℚ) ^ d) * bernoulli d / d.factorial) +
      5 * ((2 - (2 : ℚ) ^ (d - 1)) * bernoulli (d - 1) / (d - 1).factorial) := by
  have hpred : d - 1 + 1 = d := by omega
  have shift (f : ℚ⟦X⟧) : coeff d (X * f) = coeff (d - 1) f := by
    simpa only [hpred] using coeff_succ_X_mul (d - 1) f
  have hcast : ((d - 1 : ℕ) : ℚ) + 1 = d := by exact_mod_cast hpred
  unfold g
  rw [F_bernoulli_series, map_add, map_add, map_sub, coeff_normalizedCsch,
    shift, coeff_derivative, hpred, coeff_normalizedCsch,
    mul_assoc (C 5), coeff_C_mul, shift, coeff_normalizedCsch,
    coeff_X_pow_mul', if_pos hd, map_add, coeff_C_mul, coeff_C_mul, coeff_rescale, coeff_rescale]
  simp only [coeff_exp, Algebra.algebraMap_self_apply, one_pow, hcast]
  unfold regularCoeff
  ring

/-- The two initial coefficients, followed by the general coefficient formula above. -/
theorem g_zero_one : g 0 = 1 ∧ g 1 = 5 := by
  constructor
  · simpa [eCoeff] using recurrence 0
  · simpa [hCoeff, eCoeff] using recurrence 1

#print axioms normalizedCsch_mul_sinh
#print axioms F_bernoulli_series
#print axioms g_eq_bernoulli

end PolygonKernel
