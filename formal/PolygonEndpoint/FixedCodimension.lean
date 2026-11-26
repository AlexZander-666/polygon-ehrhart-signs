import PolygonEndpoint.Diagonal
import Polygon.TraceWeights

/-! Fixed codimension in the ordinary powers of the geometric Ehrhart polynomial. -/
noncomputable section
namespace PolygonEndpoint
open Finset Polygon Filter
open scoped Topology

private theorem kernel_zero : kernel 0 = 1 := by
  have one : PolygonKernel.g 0=1 := by simpa [PolygonKernel.eCoeff] using PolygonKernel.recurrence 0
  unfold kernel
  exact_mod_cast one

/-- Real coefficients of the actual face-lattice order polytope of the parabola polygon. -/
abbrev geometricCoeff (n r : ℕ) : ℝ := ((GeneralRealization.geometricEhrhart (n-3)).coeff r : ℝ)

theorem top_coefficient {n : ℕ} (hn : 3≤n) :
    geometricCoeff n (2*n+2) = leadingScale n (2*n+2) := by
  have h := diagonal_row hn (r:=2*n+2) (by omega) le_rfl
  simpa [UniformCoefficientBound.shifted,correction,kernel_zero,show n≠0 by omega] using h

/-- Exact falling-factorial and power of two converting the top scale to the shifted scale. -/
theorem leadingScale_shift (n D d : ℕ) (hd : d≤D) :
    leadingScale n (D-d) = leadingScale n D * (D.descFactorial d : ℝ)/2^d := by
  have fac : ((D-d).factorial:ℝ)*(D.descFactorial d:ℝ)=(D.factorial:ℝ) := by
    exact_mod_cast Nat.factorial_mul_descFactorial hd
  have powers : (2:ℝ)^(D-d)*2^d=2^D := by rw [←pow_add,Nat.sub_add_cancel hd]
  unfold leadingScale
  field_simp
  rw [←fac,←powers]
  ring

private theorem weight_size {n j : ℕ} (hj : j+1<n) :
    |relativeWeight n (j+1)| ≤ ((5/12:ℝ)*(Real.pi^2/8)^(j+1))/(n:ℝ) := by
  have h := TraceWeights.normalized_bound (by omega : 1≤j+1) hj
  apply h.trans
  unfold UniformCoefficientBound.weight
  have tail : 1≤ ∏ i ∈ range j, (2*(n:ℝ)-2*((i+1:ℕ):ℝ)-1) := by
    apply one_le_prod
    intro i hi
    have hi' : ((i+1:ℕ):ℝ)+1 ≤ n := by exact_mod_cast (show i+1+1≤n by have := mem_range.mp hi; omega)
    linarith
  have hn : (1:ℝ)≤n := by exact_mod_cast (by omega : 1≤n)
  have fac : (1:ℝ)≤(j+1).factorial := by exact_mod_cast Nat.factorial_pos (j+1)
  rw [prod_range_succ']
  simp only [Nat.cast_zero,mul_zero,sub_zero]
  have den : (n:ℝ) ≤ ((j+1).factorial:ℝ) *
      ((∏ i ∈ range j, (2*(n:ℝ)-2*((i+1:ℕ):ℝ)-1))*(2*n-1)) := by
    calc
      (n:ℝ) ≤ 2*(n:ℝ)-1 := by linarith
      _ ≤ _ := by
        have t := mul_le_mul_of_nonneg_right tail (show 0≤2*(n:ℝ)-1 by linarith)
        have f := mul_le_mul_of_nonneg_right fac (show 0≤
          (∏ i ∈ range j, (2*(n:ℝ)-2*((i+1:ℕ):ℝ)-1))*(2*n-1) from mul_nonneg (by linarith only [tail]) (by linarith only [hn]))
        linarith
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_left (by positivity) (by linarith) den

def codimensionRatio (n d : ℕ) : ℝ :=
  geometricCoeff n (2*n+2-d) /
    (geometricCoeff n (2*n+2)*((2*n+2).descFactorial d : ℝ)/2^d)

def codimensionErrorConstant (d : ℕ) : ℝ :=
  ∑ j ∈ range d, (5/12:ℝ)*(Real.pi^2/8)^(j+1)*|UniformCoefficientBound.shifted kernel d (j+1)|

/-- Effective fixed-codimension convergence. For n≥max(3,d+2), the endpoint correction
vanishes and only a fixed finite set of offsets can contribute. -/
theorem codimension_error {n d : ℕ} (hn : 3≤n) (hd : d+2≤n) :
    |codimensionRatio n d-kernel d| ≤ codimensionErrorConstant d/n := by
  have row := diagonal_row hn (r:=2*n+2-d) (by omega) (by omega)
  have c : correction (2*n+2-d)=0 := by simp [correction,show 2*n+2-d≠1 by omega,show 2*n+2-d≠2 by omega]
  rw [c,show 2*n+2-(2*n+2-d)=d by omega] at row
  simp only [Rat.cast_zero,zero_div,sub_zero] at row
  have finite : ∑ j ∈ range (n-1), relativeWeight n (j+1)*UniformCoefficientBound.shifted kernel d (j+1) =
      ∑ j ∈ range d, relativeWeight n (j+1)*UniformCoefficientBound.shifted kernel d (j+1) := by
    symm
    apply sum_subset_zero_on_sdiff (range_mono (by omega : d≤n-1))
    · intro i hi
      have := (mem_sdiff.mp hi).2
      simp only [mem_range] at this
      simp [UniformCoefficientBound.shifted,show ¬2*(i+1)≤d by omega]
    · intro i _
      rfl
  rw [finite] at row
  change geometricCoeff n (2*n+2-d) = _ at row
  have hz := (leadingScale_positive (r:=2*n+2-d) (by omega : 0<n)).ne'
  unfold codimensionRatio
  rw [top_coefficient hn,←leadingScale_shift _ _ _ (by omega),row,mul_div_cancel_left₀ _ hz,
    add_sub_cancel_left,codimensionErrorConstant,sum_div]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro j hj
  rw [abs_mul,mul_div_right_comm]
  exact mul_le_mul_of_nonneg_right (weight_size (by have := mem_range.mp hj; omega)) (abs_nonneg _)

/-- For every fixed d, the paper's ratio tends to the actual rational kernel coefficient g_d. -/
theorem fixed_codimension (d : ℕ) : Tendsto (fun n ↦ codimensionRatio n d) atTop (𝓝 (kernel d)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _))
    _ (tendsto_const_div_atTop_nhds_zero_nat (codimensionErrorConstant d))
  filter_upwards [eventually_ge_atTop (max 3 (d+2))] with n hn
  simpa [Real.norm_eq_abs] using codimension_error ((le_max_left ..).trans hn) ((le_max_right ..).trans hn)

/-- The expanded limit with exactly the manuscript's ordinary coefficients, falling
factorial denominator, power of two and the actual formal power-series kernel. -/
theorem geometric_fixed_codimension (d : ℕ) :
    Tendsto (fun n : ℕ ↦
      ((GeneralRealization.geometricEhrhart (n-3)).coeff (2*n+2-d):ℝ) /
      (((GeneralRealization.geometricEhrhart (n-3)).coeff (2*n+2):ℝ) *
        ((2*n+2).descFactorial d:ℝ)/2^d)) atTop (𝓝 (PolygonKernel.g d:ℝ)) :=
  fixed_codimension d

end PolygonEndpoint
