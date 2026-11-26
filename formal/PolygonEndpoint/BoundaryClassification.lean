import PolygonEndpoint.NegativeCount
import PolygonEndpoint.FixedCodimension
import Polygon.ConvexBoundary

/-! Coefficient classification and fixed-codimension limit for any strictly ordered polygon. -/
noncomputable section

namespace PolygonEndpoint

open Polygon Filter
open scoped Topology

variable {m : ℕ} {p : GeneralRealization.Index m → ConvexBoundary.Point}

/-- The original complete face-lattice polynomial is invariant under changing vertex coordinates. -/
theorem boundaryEhrhart_eq_reference (h : ConvexBoundary.BoundaryOrder p) :
    ConvexBoundary.geometricEhrhart h = GeneralRealization.geometricEhrhart m := by
  rw [ConvexBoundary.geometricEhrhart_eq_faceOrder h,
    GeneralRealization.geometricEhrhart_eq_faceOrder]

/-- Every coefficient of the actual exposed-face order polytope, including degree zero and
the zero tail above its degree. There are m+3 vertices. -/
theorem boundary_classification (h : ConvexBoundary.BoundaryOrder p) (r : ℕ) :
    let n := m + 3
    let a := (ConvexBoundary.geometricEhrhart h).coeff r
    (a < 0 ↔ NewtonInterpolant.negativeIndex n r) ∧
    (0 < a ↔ r ≤ 2 * n + 2 ∧ ¬ NewtonInterpolant.negativeIndex n r) ∧
    (a = 0 ↔ 2 * n + 2 < r) := by
  rw [boundaryEhrhart_eq_reference h]
  simpa only [Nat.add_sub_cancel, NewtonInterpolant.negativeIndex] using
    geometric_classification (n := m + 3) (by omega) r

/-- Exact number of strictly negative coefficients, where subtraction is truncated. -/
theorem boundary_negative_count (h : ConvexBoundary.BoundaryOrder p) :
    let n := m + 3
    ((Finset.range (2 * n + 3)).filter
      (fun r ↦ (ConvexBoundary.geometricEhrhart h).coeff r < 0)).card = n - 12 := by
  rw [boundaryEhrhart_eq_reference h]
  simpa only [Nat.add_sub_cancel] using negative_count (n := m + 3) (by omega)

/-- Normalized coefficient at fixed codimension, using the leading coefficient of the same hull. -/
def boundaryCodimensionRatio (h : ConvexBoundary.BoundaryOrder p) (d : ℕ) : ℝ :=
  let D := 2 * (m + 3) + 2
  let E := ConvexBoundary.geometricEhrhart h
  (E.coeff (D - d) : ℝ) / ((E.coeff D : ℝ) * (D.descFactorial d : ℝ) / 2 ^ d)

theorem boundaryCodimensionRatio_eq (h : ConvexBoundary.BoundaryOrder p) (d : ℕ) :
    boundaryCodimensionRatio h d = codimensionRatio (m + 3) d := by
  simp only [boundaryCodimensionRatio, codimensionRatio, geometricCoeff, boundaryEhrhart_eq_reference h,
    Nat.add_sub_cancel]

/-- Effective fixed-codimension bound for every such realization. -/
theorem boundary_codimension_error (h : ConvexBoundary.BoundaryOrder p) {d : ℕ}
    (hd : d + 2 ≤ m + 3) :
    |boundaryCodimensionRatio h d - kernel d| ≤ codimensionErrorConstant d / (m + 3 : ℕ) := by
  rw [boundaryCodimensionRatio_eq]
  exact codimension_error (n := m + 3) (by omega) hd

/-- The normalized coefficient tends to the formal kernel along any family of these hulls. -/
theorem boundary_fixed_codimension
    (v : (j : ℕ) → GeneralRealization.Index j → ConvexBoundary.Point)
    (h : ∀ j, ConvexBoundary.BoundaryOrder (v j)) (d : ℕ) :
    Tendsto (fun j ↦ boundaryCodimensionRatio (h j) d) atTop (𝓝 (kernel d)) := by
  simp only [boundaryCodimensionRatio_eq]
  exact (fixed_codimension d).comp (tendsto_add_atTop_nat 3)

#print axioms boundaryEhrhart_eq_reference
#print axioms boundary_classification
#print axioms boundary_negative_count
#print axioms boundaryCodimensionRatio_eq
#print axioms boundary_codimension_error
#print axioms boundary_fixed_codimension

end PolygonEndpoint
