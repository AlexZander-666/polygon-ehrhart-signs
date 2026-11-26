import PolygonEndpoint.BoundaryClassification
import PolygonEndpoint.FixedDegreeGeometry

/-! The fixed ordinary-power theorem along arbitrary families of strictly ordered boundaries. -/
noncomputable section
namespace PolygonEndpoint
open Polygon Filter Asymptotics FixedDegree
open scoped Topology

variable (v : (j : ℕ) → GeneralRealization.Index j → ConvexBoundary.Point)
variable (h : ∀ j, ConvexBoundary.BoundaryOrder (v j))

/-- Signed odd-degree asymptotic with its relative error, for n=j+3 boundary vertices. -/
theorem boundary_fixed_odd_degree (a : ℕ) :
    let f := fun j : ℕ ↦ ((ConvexBoundary.geometricEhrhart (h j)).coeff (2*a+1):ℝ) /
      (factorialScale (j+3)*oddPrincipal (j+3) a)
    Tendsto f atTop (𝓝 1) ∧ ((fun j ↦ f j-1) =O[atTop] (fun j : ℕ ↦ 1/((j+3:ℕ):ℝ))) := by
  dsimp only
  simp_rw [boundaryEhrhart_eq_reference]
  constructor
  · simpa only [Function.comp_def,actual,Nat.add_sub_cancel] using
      (odd_geometric_limit a).comp (tendsto_add_atTop_nat 3)
  · simpa only [Function.comp_def,actual,Nat.add_sub_cancel] using
      (odd_geometric_bigO a).comp_tendsto (tendsto_add_atTop_nat 3)

/-- Signed even-degree asymptotic, retaining the extra factor 2n in the normalization. -/
theorem boundary_fixed_even_degree (a : ℕ) :
    let f := fun j : ℕ ↦ ((ConvexBoundary.geometricEhrhart (h j)).coeff (2*a+2):ℝ) /
      (factorialScale (j+3)*(evenPrincipal (j+3) a*(2*((j+3:ℕ):ℝ))))
    Tendsto f atTop (𝓝 1) ∧ ((fun j ↦ f j-1) =O[atTop] (fun j : ℕ ↦ 1/((j+3:ℕ):ℝ))) := by
  dsimp only
  simp_rw [boundaryEhrhart_eq_reference]
  constructor
  · simpa only [Function.comp_def,actual,Nat.add_sub_cancel] using
      (even_geometric_limit a).comp (tendsto_add_atTop_nat 3)
  · simpa only [Function.comp_def,actual,Nat.add_sub_cancel] using
      (even_geometric_bigO a).comp_tendsto (tendsto_add_atTop_nat 3)

end PolygonEndpoint
