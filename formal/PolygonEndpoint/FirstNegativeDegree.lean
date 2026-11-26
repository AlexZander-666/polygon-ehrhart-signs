import PolygonEndpoint.UnorderedClassification

/-! Least degree with a negative ordinary coefficient for an unordered convex polygon. -/
namespace PolygonEndpoint
open Polygon

theorem unordered_first_negative_degree (S : PlanarSet) (hf : S.Finite)
    (he : S = (convexHull ℝ S).extremePoints ℝ) (hfull : affineSpan ℝ (convexHull ℝ S) = ⊤)
    (hn : 13 ≤ S.ncard) :
    IsLeast {r : ℕ | (unorderedEhrhart S hf he hfull).coeff r < 0}
      (if S.ncard % 2 = 1 then 1 else 2) := by
  constructor
  · apply (unordered_classification S hf he hfull _).1.mpr
    unfold NewtonInterpolant.negativeIndex
    split <;> omega
  · intro r hr
    have h := (unordered_classification S hf he hfull r).1.mp hr
    unfold NewtonInterpolant.negativeIndex at h
    split <;> omega

#print axioms unordered_first_negative_degree
end PolygonEndpoint
