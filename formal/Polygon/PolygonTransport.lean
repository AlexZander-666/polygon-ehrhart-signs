import Polygon.GeneralRealization

/-! Invariance of the lattice-point counting polynomial under a relabeling
of every element of the face poset, including the empty face and the top. -/
namespace Polygon.PolygonTransport

theorem orderPolynomial_eq {V W : Type*} [Fintype V] [Fintype W]
    {r : V → V → Prop} {s : W → W → Prop} (e : V ≃ W)
    (h : ∀ a b, r a b ↔ s (e a) (e b)) :
    Ehrhart.orderPolynomial r = Ehrhart.orderPolynomial s := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℚ))).mono
  rintro _ ⟨q,rfl⟩
  change (Ehrhart.orderPolynomial r).eval (q:ℚ) = (Ehrhart.orderPolynomial s).eval (q:ℚ)
  rw [Ehrhart.eval_orderPolynomial_eq_latticePoints, Ehrhart.eval_orderPolynomial_eq_latticePoints,
    Fintype.card_congr (Ehrhart.latticePointsCongr e h q)]

/-- Any full face poset with a cyclic incidence labeling has precisely the
same polynomial as the concrete planar realization. -/
theorem of_cyclic_incidence {V : Type*} [PartialOrder V] [Fintype V] {n : ℕ}
    (hn : 3 ≤ n) (e : V ≃o FaceOrder.Face (n-1)) :
    Ehrhart.orderPolynomial (fun a b : V ↦ a ≤ b) =
    GeneralRealization.geometricEhrhart (n-3) := by
  rw [GeneralRealization.ehrhart_by_sides hn]
  exact orderPolynomial_eq e.toEquiv fun _ _ ↦ e.map_rel_iff.symm

end Polygon.PolygonTransport
