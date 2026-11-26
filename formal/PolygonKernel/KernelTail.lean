import PolygonKernel.ZetaBridge
import PolygonKernel.Certificate
import Mathlib.Analysis.Real.Pi.Bounds

/-! Explicit signs and adjacent-ratio bounds for the entire kernel. -/
namespace PolygonKernel

open Real

private theorem pi_bound : π < 63 / 20 := by
  convert Real.pi_lt_d2 using 1
  norm_num

private theorem pi_square_bound : π ^ 2 < 10 := by
  have h := pow_lt_pow_left₀ pi_bound pi_pos.le (by decide : (2 : ℕ) ≠ 0)
  norm_num at h
  linarith

private theorem regular_nonneg (d : ℕ) : 0 ≤ (regularCoeff d : ℝ) := by
  unfold regularCoeff
  push_cast
  positivity

/-- After scaling by the even power of π, the regular term decreases on each parity. -/
noncomputable def scaledRegular (k δ : ℕ) : ℝ :=
  (regularCoeff (2 * k + δ) : ℝ) * π ^ (2 * k)

private theorem scaledRegular_decrease (k δ : ℕ) (hk : 13 ≤ k) :
    scaledRegular (k + 1) δ ≤ scaledRegular k δ := by
  let d := 2 * k + δ
  have hd : 26 ≤ d := by dsimp [d]; omega
  obtain ⟨a, ha⟩ : ∃ a : ℕ, d = a + 2 := ⟨d - 2, by omega⟩
  have hidx : 2 * (k + 1) + δ = d + 2 := by dsimp [d]; omega
  have hexp : 2 * (k + 1) = 2 * k + 2 := by omega
  change (regularCoeff (2 * (k + 1) + δ) : ℝ) * π ^ (2 * (k + 1)) ≤
    (regularCoeff d : ℝ) * π ^ (2 * k)
  rw [hidx, hexp, pow_add]
  rw [ha] at hd ⊢
  have hfac : (a + 2).factorial = (a + 2) * ((a + 1) * a.factorial) := by
    simp only [Nat.factorial_succ]
  have ha₀ : (24 : ℝ) ≤ a := by exact_mod_cast (show 24 ≤ a by omega)
  have hproducts : (9 : ℝ) * π ^ 2 ≤ ((a : ℝ) + 2) * (a + 1) := by
    nlinarith [pi_square_bound, sq_nonneg (a : ℝ)]
  simp only [regularCoeff, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_natCast, Nat.add_sub_cancel, hfac,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  have hnum : (8 + 4 * (3 : ℝ) ^ (a + 2)) ≤ 9 * (8 + 4 * (3 : ℝ) ^ a) := by
    rw [pow_add]
    norm_num
    linarith
  have hA : (0 : ℝ) ≤ 8 + 4 * 3 ^ a := by positivity
  have hmul : (8 + 4 * (3 : ℝ) ^ (a + 2)) * π ^ 2 ≤
      (8 + 4 * 3 ^ a) * (((a : ℝ) + 2) * (a + 1)) := by
    calc
      _ ≤ (9 * (8 + 4 * 3 ^ a)) * π ^ 2 := mul_le_mul_of_nonneg_right hnum (by positivity)
      _ = (8 + 4 * 3 ^ a) * (9 * π ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hproducts hA
  have hfact : (0 : ℝ) < a.factorial := by positivity
  have ha1 : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have ha2 : (0 : ℝ) < (a : ℝ) + 2 := by positivity
  have hden : (0 : ℝ) < ((a : ℝ) + 2) * (((a : ℝ) + 1) * (a.factorial : ℝ)) := by positivity
  have hdiv : (8 + 4 * (3 : ℝ) ^ (a + 2)) * π ^ 2 /
        (((a : ℝ) + 2) * (((a : ℝ) + 1) * (a.factorial : ℝ))) ≤
      (8 + 4 * 3 ^ a) / a.factorial := by
    rw [div_le_div_iff₀ hden hfact]
    convert mul_le_mul_of_nonneg_right hmul hfact.le using 1; ring
  convert mul_le_mul_of_nonneg_right hdiv (pow_nonneg pi_pos.le (2 * k)) using 1
  all_goals first | rfl | ring

private theorem scaledRegular_mono (k₀ k δ : ℕ) (h₀ : 13 ≤ k₀) (hk : k₀ ≤ k) :
    scaledRegular k δ ≤ scaledRegular k₀ δ := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih => exact (scaledRegular_decrease k δ (h₀.trans hk)).trans ih

private theorem scaledRegular_even_bound {k : ℕ} (hk : 14 ≤ k) :
    scaledRegular k 0 ≤ 2 * (2 * (k : ℝ) - 1) / 5 := by
  have hs : scaledRegular 14 0 ≤ 3 := by
    have h := pow_le_pow_left₀ pi_pos.le pi_bound.le 28
    unfold scaledRegular regularCoeff
    norm_num
    exact (mul_le_mul_of_nonneg_left h (by positivity)).trans (by norm_num)
  have hk' : (14 : ℝ) ≤ k := by exact_mod_cast hk
  have h := scaledRegular_mono 14 k 0 (by decide) hk
  linarith

private theorem scaledRegular_odd_bound {k : ℕ} (hk : 13 ≤ k) : scaledRegular k 1 ≤ 2 := by
  have hs : scaledRegular 13 1 ≤ 2 := by
    have h := pow_le_pow_left₀ pi_pos.le pi_bound.le 26
    unfold scaledRegular regularCoeff
    norm_num
    exact (mul_le_mul_of_nonneg_left h (by positivity)).trans (by norm_num)
  exact (scaledRegular_mono 13 k 1 (by decide) hk).trans hs

private theorem eta_lower {k : ℕ} (hk : 13 ≤ k) : 19 / 20 < etaEven k := by
  have h := (etaEven_bounds (by omega : k ≠ 0)).1
  have hp : (2 : ℝ) ^ 6 ≤ 2 ^ (2 * k) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hd := one_div_le_one_div_of_le (by positivity) hp
  norm_num at hd
  rw [one_div] at h
  linarith

private theorem control {G J A η s : ℝ} (hg : G = J + s * A * η)
    (hs : s = 1 ∨ s = -1) (hA : 0 < A) (hJ : 0 ≤ J) (hJA : J ≤ A / 5)
    (heta₁ : 19 / 20 < η) (heta₂ : η ≤ 1) :
    3 * A / 4 < |G| ∧ |G| ≤ 6 * A / 5 ∧ (G < 0 ↔ s = -1) := by
  have hlo := mul_lt_mul_of_pos_left heta₁ hA
  have hhi := mul_le_mul_of_nonneg_left heta₂ hA.le
  rcases hs with rfl | rfl
  · have hpos : 0 < G := by linarith
    rw [abs_of_pos hpos]
    refine ⟨by linarith, by linarith, ?_⟩
    norm_num [not_lt_of_ge hpos.le]
  · have hneg : G < 0 := by linarith
    rw [abs_of_neg hneg]
    exact ⟨by linarith, by linarith, by simp [hneg]⟩

private theorem sign_pow (j : ℕ) : (-1 : ℝ) ^ j = 1 ∨ (-1 : ℝ) ^ j = -1 := by
  rcases Nat.even_or_odd j with h | h
  · left
    rw [h.neg_pow, one_pow]
  · right
    rw [h.neg_pow, one_pow]

private theorem neg_pow_neg_iff (j : ℕ) : (-1 : ℝ) ^ j = -1 ↔ Odd j := by
  rcases Nat.even_or_odd j with h | h
  · have hno : ¬ Odd j := by
      have hmod := Nat.even_iff.mp h
      rw [Nat.odd_iff]
      omega
    norm_num [h.neg_pow, hno]
  · simp [h.neg_pow, h]

/-- A strictly positive lower envelope, an upper envelope, and the even-index sign. -/
theorem even_tail {k : ℕ} (hk : 14 ≤ k) :
    3 * (2 * (2 * (k : ℝ) - 1)) / 4 < π ^ (2 * k) * |(g (2 * k) : ℝ)| ∧
    π ^ (2 * k) * |(g (2 * k) : ℝ)| ≤ 6 * (2 * (2 * (k : ℝ) - 1)) / 5 ∧
    (g (2 * k) < 0 ↔ Odd (k + 1)) := by
  have hp : 0 < π ^ (2 * k) := by positivity
  have hg := g_even_eta (by omega : k ≠ 0)
  have hscale : π ^ (2 * k) * (g (2 * k) : ℝ) = scaledRegular k 0 +
      (-1 : ℝ) ^ (k + 1) * (2 * (2 * (k : ℝ) - 1)) * etaEven k := by
    rw [hg]
    simp only [scaledRegular, add_zero]
    field_simp
  have hk' : (14 : ℝ) ≤ k := by exact_mod_cast hk
  have h := control hscale (sign_pow _) (by linarith) (by
    exact mul_nonneg (regular_nonneg _) hp.le)
    (scaledRegular_even_bound hk) (eta_lower (by omega)) (etaEven_bounds (by omega)).2
  have hsign (b : ℝ) : π ^ (2 * k) * b < 0 ↔ b < 0 := by
    simpa only [mul_zero] using (mul_lt_mul_iff_right₀ (b := b) (c := 0) hp)
  rwa [abs_mul, abs_of_pos hp, hsign, Rat.cast_lt_zero,
    neg_pow_neg_iff] at h

/-- The corresponding envelopes and sign at odd indices. -/
theorem odd_tail {k : ℕ} (hk : 13 ≤ k) :
    3 * (10 : ℝ) / 4 < π ^ (2 * k) * |(g (2 * k + 1) : ℝ)| ∧
    π ^ (2 * k) * |(g (2 * k + 1) : ℝ)| ≤ 6 * (10 : ℝ) / 5 ∧
    (g (2 * k + 1) < 0 ↔ Odd k) := by
  have hp : 0 < π ^ (2 * k) := by positivity
  have hg := g_odd_eta (by omega : k ≠ 0)
  have hscale : π ^ (2 * k) * (g (2 * k + 1) : ℝ) = scaledRegular k 1 +
      (-1 : ℝ) ^ k * 10 * etaEven k := by
    rw [hg]
    unfold scaledRegular
    field_simp
  have hJ : scaledRegular k 1 ≤ (10 : ℝ) / 5 := by
    norm_num
    exact scaledRegular_odd_bound hk
  have h := control hscale (sign_pow _) (by norm_num) (by
    exact mul_nonneg (regular_nonneg _) hp.le) hJ (eta_lower hk) (etaEven_bounds (by omega)).2
  have hsign (b : ℝ) : π ^ (2 * k) * b < 0 ↔ b < 0 := by
    simpa only [mul_zero] using (mul_lt_mul_iff_right₀ (b := b) (c := 0) hp)
  rwa [abs_mul, abs_of_pos hp, hsign, Rat.cast_lt_zero,
    neg_pow_neg_iff] at h

private theorem ratio_from_scaled {u v A B : ℝ} {e : ℕ} (hv : 0 ≤ v)
    (hAB : B ≤ A) (hlo : 3 * A / 4 < π ^ (e + 2) * v)
    (hhi : π ^ e * u ≤ 6 * B / 5) : u ≤ 16 * v := by
  have he : 0 < π ^ e := by positivity
  rw [pow_add] at hlo
  apply (mul_le_mul_iff_right₀ he).mp
  calc
    π ^ e * u ≤ (8 / 5 : ℝ) * ((π ^ e * π ^ 2) * v) := by linarith
    _ = π ^ e * ((8 / 5 * π ^ 2) * v) := by ring
    _ ≤ π ^ e * (16 * v) := by
      apply mul_le_mul_of_nonneg_left _ he.le
      exact mul_le_mul_of_nonneg_right (by linarith [pi_square_bound]) hv

private theorem g_even_ratio {k : ℕ} (hk : 15 ≤ k) :
    |g (2 * k - 2)| ≤ 16 * |g (2 * k)| := by
  have hp : 14 ≤ k - 1 := by omega
  have he : 2 * (k - 1) + 2 = 2 * k := by omega
  have hg : |(g (2 * (k - 1)) : ℝ)| ≤ 16 * |(g (2 * k) : ℝ)| := by
    apply ratio_from_scaled (abs_nonneg _) (B := 2 * (2 * ((k - 1 : ℕ) : ℝ) - 1))
        (A := 2 * (2 * (k : ℝ) - 1)) (e := 2 * (k - 1))
    · have hle : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
      linarith
    · rw [he]
      exact (even_tail (by omega : 14 ≤ k)).1
    · exact (even_tail hp).2.1
  rw [show 2 * (k - 1) = 2 * k - 2 by omega] at hg
  exact_mod_cast hg

private theorem g_odd_ratio {k : ℕ} (hk : 14 ≤ k) :
    |g (2 * k + 1 - 2)| ≤ 16 * |g (2 * k + 1)| := by
  have hp : 13 ≤ k - 1 := by omega
  have he : 2 * (k - 1) + 2 = 2 * k := by omega
  have hg : |(g (2 * (k - 1) + 1) : ℝ)| ≤ 16 * |(g (2 * k + 1) : ℝ)| := by
    apply ratio_from_scaled (abs_nonneg _) (B := 10) (A := 10) (e := 2 * (k - 1)) le_rfl
    · rw [he]
      exact (odd_tail (by omega : 13 ≤ k)).1
    · exact (odd_tail hp).2.1
  rw [show 2 * (k - 1) + 1 = 2 * k + 1 - 2 by omega] at hg
  exact_mod_cast hg

/-- The analytic bound on a backwards step by two holds from degree 29. -/
theorem adjacent_ratio_tail (d : ℕ) (hd : 29 ≤ d) : |g (d - 2)| ≤ 16 * |g d| := by
  by_cases he : d % 2 = 0
  · obtain ⟨k, rfl⟩ : ∃ k, d = 2 * k := ⟨d / 2, by omega⟩
    exact g_even_ratio (by omega)
  · obtain ⟨k, rfl⟩ : ∃ k, d = 2 * k + 1 := ⟨d / 2, by omega⟩
    exact g_odd_ratio (by omega)

/-- The nonvanishing envelope used to control the ordinary degree-one and degree-two corrections. -/
theorem normalized_abs_lower (d : ℕ) (hd : 27 ≤ d) : 1 < π ^ d * |(g d : ℝ)| := by
  by_cases he : d % 2 = 0
  · obtain ⟨k, rfl⟩ : ∃ k, d = 2 * k := ⟨d / 2, by omega⟩
    have hk : 14 ≤ k := by omega
    have hk' : (14 : ℝ) ≤ k := by exact_mod_cast hk
    linarith [(even_tail hk).1]
  · obtain ⟨k, rfl⟩ : ∃ k, d = 2 * k + 1 := ⟨d / 2, by omega⟩
    have h := (odd_tail (by omega : 13 ≤ k)).1
    have hπ : 1 ≤ π := by linarith [pi_gt_three]
    rw [pow_succ, mul_right_comm]
    nlinarith [mul_le_mul_of_nonneg_left hπ (by positivity : 0 ≤ π ^ (2 * k) *
      |(g (2 * k + 1) : ℝ)|)]

/-- Above the initial positive block, the negative indices are exactly 0 and 3 modulo 4. -/
theorem negative_tail (d : ℕ) (hd : 27 ≤ d) : g d < 0 ↔ NegativeIndex d := by
  by_cases he : d % 2 = 0
  · obtain ⟨k, rfl⟩ : ∃ k, d = 2 * k := ⟨d / 2, by omega⟩
    rw [(even_tail (by omega : 14 ≤ k)).2.2, Nat.odd_iff, NegativeIndex]
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, d = 2 * k + 1 := ⟨d / 2, by omega⟩
    rw [(odd_tail (by omega : 13 ≤ k)).2.2, Nat.odd_iff, NegativeIndex]
    omega

/-- The actual formal kernel satisfies the full signed and quantitative coefficient theorem. -/
theorem kernel_all (d : ℕ) :
    g d ≠ 0 ∧
    (g d < 0 ↔ NegativeIndex d) ∧
    (2 ≤ d → |g (d - 2)| ≤ 108 * |g d|) ∧
    (27 ≤ d → |g (d - 2)| ≤ 28 * |g d|) := by
  by_cases hd : d ≤ 95
  · exact finite_kernel d hd
  · have hn : g d ≠ 0 := by
      intro h
      have hl := normalized_abs_lower d (by omega)
      norm_num [h] at hl
    have hs := adjacent_ratio_tail d (by omega)
    exact ⟨hn, negative_tail d (by omega),
      fun _ ↦ hs.trans (by gcongr; norm_num),
      fun _ ↦ hs.trans (by gcongr; norm_num)⟩

/-- Exactly the complementary kernel indices are strictly positive. -/
theorem g_pos_iff (d : ℕ) : 0 < g d ↔ ¬ NegativeIndex d := by
  have h := kernel_all d
  constructor
  · intro hp hn
    exact (not_lt_of_ge hp.le) (h.2.1.mpr hn)
  · intro hp
    exact lt_of_le_of_ne (le_of_not_gt (hp ∘ h.2.1.mp)) h.1.symm

open PowerSeries
open scoped PowerSeries

/-- Transfer the classification to any presentation satisfying the normalized-sinh equation. -/
theorem kernel_all_of_formalSinh {G : ℚ⟦X⟧}
    (h : G * formalSinh ^ 2 = X ^ 2 * rescale (5 : ℚ) (exp ℚ)) (d : ℕ) :
    coeff d G ≠ 0 ∧
    (coeff d G < 0 ↔ NegativeIndex d) ∧
    (2 ≤ d → |coeff (d - 2) G| ≤ 108 * |coeff d G|) ∧
    (27 ≤ d → |coeff (d - 2) G| ≤ 28 * |coeff d G|) := by
  rw [F_eq_of_formalSinh h]
  exact kernel_all d

#print axioms even_tail
#print axioms odd_tail
#print axioms adjacent_ratio_tail
#print axioms normalized_abs_lower
#print axioms negative_tail
#print axioms kernel_all
#print axioms g_pos_iff
#print axioms kernel_all_of_formalSinh

end PolygonKernel
