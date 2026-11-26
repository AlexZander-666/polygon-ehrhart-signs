import PolygonEndpoint.Diagonal
import PolygonKernel.KernelTail
import Polygon.NewtonInterpolant

/-! The constant coefficient and the positive last 27 coefficients of the genuine polygon. -/
noncomputable section
namespace PolygonEndpoint
open Polygon Finset

theorem geometric_constant {n : ℕ} (hn : 3≤n) :
    (GeneralRealization.geometricEhrhart (n-3)).coeff 0 = 1 := by
  rw [GeneralRealization.ehrhart_by_sides hn,Polynomial.coeff_zero_eq_eval_zero]
  exact (WidthSpectrum.low_inputs (n-1)).1

theorem positive_top {n r : ℕ} (hn : 65≤n) (hr : 1≤r) (top : r≤2*n+2)
    (hd : 2*n+2-r<27) : 0 < (GeneralRealization.geometricEhrhart (n-3)).coeff r := by
  have pos (d : ℕ) (small : d<27) : 0<kernel d := by
    have := (PolygonKernel.g_pos_iff d).mpr (by unfold PolygonKernel.NegativeIndex; omega)
    exact_mod_cast this
  have shifted (j : ℕ) : 0 ≤ UniformCoefficientBound.shifted kernel (2*n+2-r) j := by
    unfold UniformCoefficientBound.shifted
    split
    · exact (pos _ (by omega)).le
    · exact le_rfl
  have off : 0 ≤ ∑ j ∈ range (n-1), relativeWeight n (j+1)*
      UniformCoefficientBound.shifted kernel (2*n+2-r) (j+1) := by
    apply sum_nonneg
    intro j hj
    exact mul_nonneg (relativeWeight_nonnegative (by have := mem_range.mp hj; omega)) (shifted _)
  have c : correction r=0 := by simp [correction,show r≠1 by omega,show r≠2 by omega]
  have h := diagonal_row (by omega : 3≤n) hr top
  rw [c] at h
  simp only [Rat.cast_zero,zero_div,sub_zero] at h
  exact_mod_cast h.symm ▸ mul_pos (leadingScale_positive (by omega : 0<n)) (add_pos_of_pos_of_nonneg (pos _ hd) off)

theorem geometric_above {n r : ℕ} (hn : 3≤n) (hr : 2*n+2<r) :
    (GeneralRealization.geometricEhrhart (n-3)).coeff r = 0 := by
  rw [GeneralRealization.ehrhart_by_sides hn]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  have := FaceOrder.natDegree_ehrhartPolynomial_le (n-1)
  omega

end PolygonEndpoint
