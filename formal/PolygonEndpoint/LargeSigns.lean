import PolygonEndpoint.CorrectionBound
import PolygonEndpoint.TopCoefficients
import Polygon.TraceWeights

/-! Large polygons: the signed diagonal wins at every nontrivial complementary degree. -/
noncomputable section
namespace PolygonEndpoint
open Polygon Finset

theorem geometric_diagonal_sign {n r : ℕ} (hn : 65≤n) (hr : 1≤r) (top : r≤2*n+2)
    (hd : 27≤2*n+2-r) :
    0 < ((GeneralRealization.geometricEhrhart (n-3)).coeff r:ℝ)*kernel (2*n+2-r) := by
  apply UniformCoefficientBound.sign_of_centered_sum hn hd kernel (relativeWeight n)
  · unfold kernel
    exact_mod_cast (PolygonKernel.kernel_all (2*n+2-r)).1
  · intro t ht
    exact_mod_cast (PolygonKernel.kernel_all t).2.2.2 ht
  · intro t ht
    exact_mod_cast (PolygonKernel.kernel_all t).2.2.1 ht
  · intro h ht hj
    exact TraceWeights.normalized_bound ht hj
  · exact leadingScale_positive (r:=r) (by omega : 0<n)
  · exact diagonal_row (by omega) hr top
  · exact correction_small hn hr top hd

/-- Strict classification through the dimension of each large polygon in the realization family. -/
theorem large_geometric_signs {n r : ℕ} (hn : 65 ≤ n) (top : r≤2*n+2) :
    let a := (GeneralRealization.geometricEhrhart (n-3)).coeff r
    (a<0 ↔ NewtonInterpolant.negativeIndex n r) ∧ a≠0 := by
  dsimp only
  by_cases zer : r=0
  · subst r
    rw [geometric_constant (by omega)]
    norm_num [NewtonInterpolant.negativeIndex]
  have hr : 1≤r := by omega
  by_cases deep : 27 ≤ 2*n+2-r
  · have a := geometric_diagonal_sign hn hr top deep
    obtain ⟨s,t⟩ | ⟨s,t⟩ := (mul_pos_iff.mp a)
    · have pos : 0 < (GeneralRealization.geometricEhrhart (n-3)).coeff r := by exact_mod_cast s
      have ker : 0 < PolygonKernel.g (2*n+2-r) := by exact_mod_cast t
      have h := (PolygonKernel.g_pos_iff _).mp ker
      exact ⟨iff_of_false (not_lt.mpr pos.le) (fun hneg ↦ h hneg.2),pos.ne'⟩
    · have neg : (GeneralRealization.geometricEhrhart (n-3)).coeff r < 0 := by exact_mod_cast s
      have ker : PolygonKernel.g (2*n+2-r)<0 := by exact_mod_cast t
      have h := ((PolygonKernel.kernel_all _).2.1).mp ker
      exact ⟨iff_of_true neg ⟨hr,h⟩,neg.ne⟩
  · have pos := positive_top hn hr top (by omega)
    exact ⟨iff_of_false (not_lt.mpr pos.le) (fun hneg ↦ deep hneg.2.1),pos.ne'⟩

end PolygonEndpoint
