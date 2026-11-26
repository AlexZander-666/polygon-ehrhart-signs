import PolygonEndpoint.NegativeCount
import Polygon.PolygonTransport

/-! Coefficient signs and the number of negative coefficients depend only
on the full cyclic incidence order, even if the vertices and faces are relabeled. -/
namespace PolygonEndpoint
open Polygon Finset

theorem cyclic_classification {V : Type*} [Fintype V] [PartialOrder V] {n : ℕ}
    (hn : 3 ≤ n) (e : V ≃o FaceOrder.Face (n-1)) (r : ℕ) :
    let a := (Ehrhart.orderPolynomial (fun x y : V ↦ x ≤ y)).coeff r
    (a < 0 ↔ NewtonInterpolant.negativeIndex n r) ∧
      (0 < a ↔ r ≤ 2*n+2 ∧ ¬NewtonInterpolant.negativeIndex n r) ∧
      (a = 0 ↔ 2*n+2 < r) := by
  rw [PolygonTransport.of_cyclic_incidence hn e]
  exact geometric_classification hn r

theorem cyclic_negative_count {V : Type*} [Fintype V] [PartialOrder V] {n : ℕ}
    (hn : 3 ≤ n) (e : V ≃o FaceOrder.Face (n-1)) :
    ((range (2*n+3)).filter (fun r ↦ (Ehrhart.orderPolynomial (fun a b : V ↦ a ≤ b)).coeff r < 0)).card
      = n-12 := by
  rw [PolygonTransport.of_cyclic_incidence hn e]
  exact negative_count hn

end PolygonEndpoint
