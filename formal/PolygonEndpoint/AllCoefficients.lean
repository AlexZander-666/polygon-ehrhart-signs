import PolygonEndpoint.LargeSigns
import Polygon.Finite64Verified

/-! Complete power-basis sign classification for the lattice-point polynomial of
the full face lattice of each explicit planar polygon with n≥3 vertices. -/
namespace PolygonEndpoint
open Polygon

/-- The geometric polynomial has no missing degrees through dimension 2n+2. -/
theorem geometric_signs {n r : ℕ} (hn : 3≤n) (hr : r≤2*n+2) :
    let a := (GeneralRealization.geometricEhrhart (n-3)).coeff r
    (a<0 ↔ NewtonInterpolant.negativeIndex n r) ∧ a≠0 := by
  by_cases small : n≤64
  · exact Finite64.geometric_signs n r hn small hr
  · exact large_geometric_signs (by omega) hr

/-- Every ordinary coefficient, with no restriction on its index.
The codimension is (2n+2-r). -/
theorem geometric_classification {n : ℕ} (hn : 3≤n) (r : ℕ) :
    let a := (GeneralRealization.geometricEhrhart (n-3)).coeff r
    (a<0 ↔ 0<r ∧ 27≤2*n+2-r ∧ ((2*n+2-r)%4=0 ∨ (2*n+2-r)%4=3)) ∧
    (0<a ↔ r≤2*n+2 ∧ ¬ NewtonInterpolant.negativeIndex n r) ∧
    (a=0 ↔ 2*n+2<r) := by
  dsimp only
  by_cases top : r≤2*n+2
  · obtain ⟨neg,nz⟩ := geometric_signs hn top
    refine ⟨neg,?_,iff_of_false nz (by omega)⟩
    constructor
    · intro pos
      exact ⟨top,fun h ↦ (not_lt_of_ge pos.le) (neg.mpr h)⟩
    · rintro ⟨_,h⟩
      exact lt_of_le_of_ne (le_of_not_gt (h ∘ neg.mp)) nz.symm
  · have above : 2*n+2<r := by omega
    rw [geometric_above hn above]
    dsimp [NewtonInterpolant.negativeIndex]
    have e : 2*n+2-r=0 := by omega
    simp [e,top,above]

/-- The first negative index is degree one for odd polygons and degree two for even
polygons once the corresponding threshold is reached. -/
theorem negative_low_degree {n : ℕ} (hn : 13≤n) :
    (GeneralRealization.geometricEhrhart (n-3)).coeff (if n%2=1 then 1 else 2) < 0 := by
  apply (geometric_classification (by omega : 3≤n) _).1.mpr
  split <;> omega

/-- The face-lattice order polytope in the realization family has a negative ordinary
Ehrhart coefficient exactly from thirteen sides onwards. -/
theorem exists_negative_iff {n : ℕ} (hn : 3≤n) :
    (∃ r, (GeneralRealization.geometricEhrhart (n-3)).coeff r < 0) ↔ 13≤n := by
  constructor
  · rintro ⟨r,neg⟩
    have h := (geometric_classification hn r).1.mp neg
    omega
  · intro h
    exact ⟨_,negative_low_degree h⟩

end PolygonEndpoint
