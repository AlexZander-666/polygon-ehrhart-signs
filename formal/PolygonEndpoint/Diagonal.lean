import PolygonEndpoint.Normalization
import Polygon.InverseSineBound
import Polygon.CosineZeta

/-! The actual Ehrhart polynomial in the normalized diagonal coordinates of the sign bound. -/
noncomputable section
namespace PolygonEndpoint
open PowerSeries Polygon Finset

abbrev secantCoeff := FormalCosine.c
abbrev kernel (d : ℕ) : ℝ := (PolygonKernel.g d : ℝ)

def relativeWeight (n j : ℕ) : ℝ :=
  ((2*(n-j)).factorial:ℝ)/(2*n).factorial *
  (secantCoeff (n-j)/secantCoeff n)*InverseSineBound.b n (n-j)

def leadingScale (n r : ℕ) : ℝ :=
  (n:ℝ)/4^n * ((2*n).factorial:ℝ)/4*(2^r/r.factorial)*secantCoeff n

private theorem reverse_interior {n : ℕ} (hn : 0<n) (f : ℕ→ℝ) (hz : f 0=0) :
    ∑ k ∈ range (n+1), f k = f n+∑ j ∈ range (n-1), f (n-(j+1)) := by
  rw [sum_range_succ',hz,add_zero,←sum_range_reflect (fun i ↦ f (i+1)) n]
  have e : ∑ j ∈ range n, f (n-1-j+1) = ∑ j ∈ range n, f (n-j) := by
    apply sum_congr rfl
    intro j hj
    rw [show n-1-j+1=n-j by have := mem_range.mp hj; omega]
  rw [e]
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [sum_range_succ']
  simp only [Nat.sub_zero,Nat.add_one_sub_one]
  ring

/-- The exact normalized diagonal row in the indexing of `sign_of_centered_sum`. -/
theorem diagonal_row {n r : ℕ} (hn : 3≤n) (hr : 1≤r) (top : r≤2*n+2) :
    ((GeneralRealization.geometricEhrhart (n-3)).coeff r : ℝ) =
    leadingScale n r*(kernel (2*n+2-r) +
      ∑ j ∈ range (n-1), relativeWeight n (j+1)*
        UniformCoefficientBound.shifted kernel (2*n+2-r) (j+1)) -
        (correction r:ℝ)/(2*4^n) := by
  have hc : secantCoeff n ≠ 0 := (FormalCosine.c_pos (by omega)).ne'
  let f (k : ℕ) : ℝ := ((if r≤2*k+2 then ((2*k).factorial:ℚ)/4 *
    (PolygonKernel.g (2*k+2-r)*2^r/r.factorial) else 0 : ℚ) : ℝ)*amplit n k
  have e := corrected_coefficient hn hr
  change (_:ℝ)*(_+_) = ∑ k ∈ range (n+1), f k at e
  have hzero : f 0=0 := by
    have h := InverseSineBound.zero_column (n-1)
    rw [show n-1+1=n by omega] at h
    change _ * (secantCoeff 0 * InverseSineBound.b n 0) = 0
    simp only [h,mul_zero]
  rw [reverse_interior (by omega) f hzero] at e
  have normalize (j : ℕ) (hj : j≤n) :
      ((n:ℝ)/4^n)*f (n-j) =
      leadingScale n r * (relativeWeight n j * UniformCoefficientBound.shifted kernel (2*n+2-r) j) := by
    simp only [f,UniformCoefficientBound.shifted,leadingScale,relativeWeight]
    by_cases h : 2*j≤2*n+2-r
    · rw [if_pos h,if_pos (by omega)]
      push_cast
      rw [show 2*(n-j)+2-r = 2*n+2-r-2*j by omega]
      change _ * (_ * (secantCoeff (n-j)*InverseSineBound.b n (n-j))) = _
      unfold kernel
      field_simp
    · rw [if_neg h,if_neg (by omega)]
      simp
  have leading : (n:ℝ)/4^n*f n = leadingScale n r * kernel (2*n+2-r) := by
    simpa [relativeWeight,UniformCoefficientBound.shifted,InverseSineBound.diagonal,hc,Nat.factorial_ne_zero] using
      normalize 0 (by omega)
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
  have cancel : ((n:ℝ)/4^n)*((4:ℝ)^n/n) = 1 := by field_simp
  have total := congrArg (fun t : ℝ ↦ ((n:ℝ)/4^n)*t) e
  change _ * (_*(_+_)) = _ * (_+_) at total
  rw [←mul_assoc,cancel,one_mul,mul_add,leading,mul_sum] at total
  rw [mul_add,mul_sum]
  apply eq_sub_of_add_eq
  rw [total]
  congr 1
  apply sum_congr rfl
  intro j hj
  exact normalize (j+1) (by have := mem_range.mp hj; omega)

theorem leadingScale_positive {n r : ℕ} (hn : 0<n) : 0 < leadingScale n r := by
  have hc := FormalCosine.c_pos hn
  unfold leadingScale secantCoeff
  positivity

theorem relativeWeight_nonnegative {n j : ℕ} (hj : j<n) : 0 ≤ relativeWeight n j := by
  have ha := (FormalCosine.c_pos (by omega : 0<n-j)).le
  have hb := (FormalCosine.c_pos (by omega : 0<n)).le
  have hc := InverseSineBound.nonneg n (n-j)
  unfold relativeWeight secantCoeff
  positivity

end PolygonEndpoint
