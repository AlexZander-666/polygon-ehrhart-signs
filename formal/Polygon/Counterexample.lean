import Polygon.FaceOrder
import Polygon.Realization
import Polygon.Certificate

/-! Ordinary Ehrhart coefficient for the complete geometric face lattice. -/
namespace Polygon.Counterexample

open Realization Ehrhart FaceOrder

private def code : Face 12 ≃ FaceCode where
  toFun
    | .bottom => .bottom
    | .vertex i => .vertex i
    | .edge i => .edge i
    | .top => .top
  invFun
    | .bottom => .bottom
    | .vertex i => .vertex i
    | .edge i => .edge i
    | .top => .top
  left_inv a := by cases a <;> rfl
  right_inv a := by cases a <;> rfl

private instance (a b : Face 12) : Decidable (faceLE a b) := by
  cases a <;> cases b <;> unfold faceLE <;> infer_instance

private theorem check_incidence : ∀ a b : Face 12,
    (Realization.vertices (code a) ⊆ Realization.vertices (code b)) ↔ faceLE a b := by decide +kernel

noncomputable def geometricOrderIso : Face 12 ≃o GeometricFace :=
  (show Face 12 ≃o FaceCode from
    { toEquiv := code, map_rel_iff' := fun {a b} => check_incidence a b }).trans faceOrderIso

noncomputable instance : Fintype GeometricFace :=
  Fintype.ofEquiv FaceCode faceOrderIso.toEquiv

noncomputable def geometricLabelsEquiv (q : ℕ) :
    Labels (fun a b : GeometricFace => a ≤ b) (q+1) ≃ Tally.Labeling 12 q := by
  refine Equiv.trans ?_ (labelsEquivLabeling 12 q)
  exact {
    toFun := fun f => ⟨f.val ∘ geometricOrderIso, fun _ _ h => f.property _ _ (geometricOrderIso.monotone h)⟩
    invFun := fun f => ⟨f.val ∘ geometricOrderIso.symm, fun _ _ h => f.property _ _ (geometricOrderIso.symm.monotone h)⟩
    left_inv := fun f => Subtype.ext (funext fun a => by simp)
    right_inv := fun f => Subtype.ext (funext fun a => by simp) }

noncomputable def geometricEhrhart : Polynomial ℚ := orderPolynomial (fun a b : GeometricFace => a ≤ b)

theorem counts_every_dilate (q : ℕ) : geometricEhrhart.eval (q : ℚ) =
    (Fintype.card (LatticePoints (fun a b : GeometricFace => a ≤ b) q) : ℚ) :=
  eval_orderPolynomial_eq_latticePoints _ q

theorem exact_linear_coefficient : geometricEhrhart.coeff 1 = -298495711/35302608 := by
  apply Cert.slope13
  · apply (natDegree_orderPolynomial_le _).trans
    rw [← Nat.card_eq_fintype_card, card_geometricFaces]
  · intro q
    rw [geometricEhrhart, eval_orderPolynomial, Fintype.card_congr (geometricLabelsEquiv q.val)]

/-- An ordinary Ehrhart coefficient of the order polytope of the full face lattice is negative. -/
theorem negative_linear_coefficient : geometricEhrhart.coeff 1 < 0 := by
  rw [exact_linear_coefficient]
  norm_num

end Polygon.Counterexample
