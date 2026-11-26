import PolygonEndpoint.Diagonal
import PolygonKernel.KernelTail

/-! The exact low-degree additive correction is small compared with the leading term. -/
noncomputable section

namespace PolygonEndpoint

/-- The common leading scale in ordinary degrees one and two. -/
theorem leadingScale_low {n r : ℕ} (hn : 0 < n) (hr : r = 1 ∨ r = 2) :
    leadingScale n r =
      ((2 * n).factorial : ℝ) * Polygon.FormalCosine.sigma n / (2 * Real.pi ^ (2 * n)) := by
  have hdegree : (2 : ℝ) ^ r / (r.factorial : ℝ) = 2 := by
    rcases hr with rfl | rfl <;> norm_num
  calc
    _ = ((2 * n).factorial : ℝ) * ((n : ℝ) * secantCoeff n) / (2 * 4 ^ n) := by
      unfold leadingScale
      rw [hdegree]
      ring
    _ = _ := by
      rw [show (n : ℝ) * secantCoeff n = _ from Polygon.FormalCosine.c_mul_eq hn,
        div_pow, ← pow_mul]
      field_simp

/-- The actual first- and second-degree corrections obey the uniform diagonal budget. -/
theorem correction_small {n r : ℕ} (hn : 65 ≤ n) (hr : 1 ≤ r) (top : r ≤ 2 * n + 2)
    (hd : 27 ≤ 2 * n + 2 - r) :
    |(correction r : ℝ) / (2 * 4 ^ n)| ≤
      leadingScale n r * |kernel (2 * n + 2 - r)| / 32 := by
  let d := 2 * n + 2 - r
  let c : ℝ := correction r
  let F : ℝ := (2 * n).factorial
  have hn' : 0 < n := by omega
  have hscale := leadingScale_positive (r := r) hn'
  by_cases low : r = 1 ∨ r = 2
  · have htotal : d + r = 2 * n + 2 := Nat.sub_add_cancel top
    have hdtop : d ≤ 2 * n + 1 := by omega
    have hcases : 0 ≤ c ∧ c ≤ 5 / 2 := by
      rcases low with h | h <;> norm_num [c, correction, h]
    have hfactor := Polygon.UniformCoefficientBound.factorial_correction_lt hn hdtop
      hcases.1 hcases.2
    have hF : 0 < F := by dsimp [F]; positivity
    have hlead : F / (2 * Real.pi ^ (2 * n)) ≤ leadingScale n r := by
      rw [leadingScale_low hn' low, ← mul_one F]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Polygon.FormalCosine.sigma_one_le hn') hF.le) (by positivity)
    have hkernel : 1 / Real.pi ^ d ≤ |kernel d| := by
      apply (div_le_iff₀ (by positivity : 0 < Real.pi ^ d)).mpr
      rw [mul_comm]
      exact (PolygonKernel.normalized_abs_lower d hd).le
    change |c / (2 * 4 ^ n)| ≤ leadingScale n r * |kernel d| / 32
    rw [abs_of_nonneg (div_nonneg hcases.1 (by positivity))]
    calc
      c / (2 * 4 ^ n) =
          (c * Real.pi ^ (2 * n + d) / (4 ^ n * F)) *
          (F / (2 * Real.pi ^ (2 * n + d))) := by field_simp
      _ ≤ (1 / 32 : ℝ) * (F / (2 * Real.pi ^ (2 * n + d))) :=
        mul_le_mul_of_nonneg_right hfactor.le (by positivity)
      _ = (F / (2 * Real.pi ^ (2 * n)) * (1 / Real.pi ^ d)) / 32 := by
        rw [pow_add]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul hlead hkernel (by positivity) hscale.le) (by norm_num)
  · rw [correction, if_neg (fun h ↦ low (Or.inl h)), if_neg (fun h ↦ low (Or.inr h))]
    simp only [Rat.cast_zero, zero_div, abs_zero]
    positivity

#print axioms leadingScale_low
#print axioms correction_small

end PolygonEndpoint
