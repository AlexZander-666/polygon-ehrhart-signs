import PolygonKernel.BernoulliBridge
import Mathlib.NumberTheory.ZetaValues

/-! Signed coefficients of the polygon kernel via the Fourier expansion at one half. -/
namespace PolygonKernel

open PowerSeries
open scoped PowerSeries

/-- The alternating Dirichlet series at the even positive argument 2k. -/
noncomputable def etaEven (k : ℕ) : ℝ :=
  ∑' i : ℕ, (-1 : ℝ) ^ i * (1 / ((i : ℝ) + 1) ^ (2 * k))

theorem etaEven_bounds {k : ℕ} (hk : k ≠ 0) :
    1 - 1 / (2 : ℝ) ^ (2 * k) ≤ etaEven k ∧ etaEven k ≤ 1 := by
  let f (i : ℕ) : ℝ := 1 / ((i : ℝ) + 1) ^ (2 * k)
  have hf : Summable f := by
    simpa only [f, Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 (hasSum_zeta_nat hk).summable
  have hanti : Antitone f := by
    intro i j hij
    have hle : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by gcongr
    dsimp [f]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hle _)
  have ht := hf.tendsto_alternating_series_tsum
  constructor
  · have h := hanti.alternating_series_le_tendsto ht 1
    simpa [etaEven, f, Finset.sum_range_succ, sub_eq_add_neg, one_add_one_eq_two] using h
  · have h := hanti.tendsto_le_alternating_series ht 0
    simpa [etaEven, f, Finset.sum_range_succ] using h

/-- The true coefficient of normalized reciprocal sinh, via Bernoulli Fourier evaluation. -/
theorem coeff_normalizedCsch_eta {k : ℕ} (hk : k ≠ 0) :
    ((coeff (2 * k) normalizedCsch : ℚ) : ℝ) =
      (-1 : ℝ) ^ k * 2 * etaEven k / Real.pi ^ (2 * k) := by
  have h := hasSum_one_div_nat_pow_mul_cos hk (x := (2 : ℝ)⁻¹) (by norm_num)
  have hterm (n : ℕ) : Real.cos (2 * Real.pi * n * (2 : ℝ)⁻¹) = (-1 : ℝ) ^ n := by
    rw [show 2 * Real.pi * (n : ℝ) * (2 : ℝ)⁻¹ = n * Real.pi by ring,
      Real.cos_nat_mul_pi]
  simp only [hterm] at h
  have ht := h.tsum_eq
  rw [h.summable.tsum_eq_zero_add] at ht
  have hexp : 2 * k ≠ 0 := by omega
  simp only [Nat.cast_zero, zero_pow hexp, div_zero, pow_zero, mul_one, zero_add] at ht
  have hsum :
      (∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ (2 * k) * (-1 : ℝ) ^ (n + 1)) =
        -etaEven k := by
    rw [etaEven, ← tsum_neg]
    congr 1
    ext n
    push_cast
    rw [pow_succ]
    ring
  rw [hsum] at ht
  change -etaEven k = (-1 : ℝ) ^ (k + 1) * (2 * Real.pi) ^ (2 * k) / 2 /
    ((2 * k).factorial : ℝ) * bernoulliFun (2 * k) (2 : ℝ)⁻¹ at ht
  rw [bernoulliFun_eval_half, mul_pow, pow_succ] at ht
  rw [coeff_normalizedCsch]
  push_cast
  have htwo : (2 : ℝ) ^ (2 * k) ≠ 0 := by positivity
  have hpi : Real.pi ^ (2 * k) ≠ 0 := by positivity
  have hfact : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
  have hs : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
  field_simp at ht ⊢
  linear_combination (-1 : ℝ) ^ k * ht -
    Real.pi ^ (2 * k) * (bernoulli (2 * k) : ℝ) *
      (2 - (2 : ℝ) ^ (2 * k)) * hs

private theorem coeff_normalizedCsch_odd (k : ℕ) :
    coeff (2 * k + 1) normalizedCsch = 0 := by
  rw [coeff_normalizedCsch]
  by_cases hk : k = 0
  · subst k
    norm_num
  · rw [bernoulli_eq_zero_of_odd (Nat.odd_iff.mpr (by omega)) (by omega)]
    ring

private theorem g_eq_csch (d : ℕ) (hd : 2 ≤ d) :
    g d = regularCoeff d + (1 - (d : ℚ)) * coeff d normalizedCsch +
      5 * coeff (d - 1) normalizedCsch := by
  simpa only [coeff_normalizedCsch] using g_eq_bernoulli d hd

/-- The regular part and the exact oscillating term at even indices. -/
theorem g_even_eta {k : ℕ} (hk : k ≠ 0) :
    (g (2 * k) : ℝ) = (regularCoeff (2 * k) : ℝ) +
      (-1 : ℝ) ^ (k + 1) * (2 * (2 * (k : ℝ) - 1)) * etaEven k /
        Real.pi ^ (2 * k) := by
  rw [g_eq_csch (2 * k) (by omega), show 2 * k - 1 = 2 * (k - 1) + 1 by omega,
    coeff_normalizedCsch_odd, mul_zero, add_zero]
  push_cast
  rw [coeff_normalizedCsch_eta hk, pow_succ]
  ring

/-- The regular part and the exact oscillating term at odd indices. -/
theorem g_odd_eta {k : ℕ} (hk : k ≠ 0) :
    (g (2 * k + 1) : ℝ) = (regularCoeff (2 * k + 1) : ℝ) +
      (-1 : ℝ) ^ k * 10 * etaEven k / Real.pi ^ (2 * k) := by
  rw [g_eq_csch (2 * k + 1) (by omega), coeff_normalizedCsch_odd, mul_zero, add_zero,
    Nat.add_sub_cancel, Rat.cast_add, Rat.cast_mul, coeff_normalizedCsch_eta hk]
  norm_num
  ring

#print axioms etaEven_bounds
#print axioms coeff_normalizedCsch_eta
#print axioms g_even_eta
#print axioms g_odd_eta

end PolygonKernel
