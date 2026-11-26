import Polygon.Ehrhart

/-! Integral points in actual real dilates of the order polytope. -/

namespace Polygon.Ehrhart

noncomputable section

open scoped Pointwise

variable {V : Type*}

def orderPolytope (r : V → V → Prop) : Set (V → ℝ) :=
  {f | (∀ v, 0 ≤ f v ∧ f v ≤ 1) ∧ ∀ a b, r a b → f a ≤ f b}

theorem mem_dilate_orderPolytope (r : V → V → Prop) (q : ℕ) (z : V → ℝ) :
    z ∈ (q : ℝ) • orderPolytope r ↔
      (∀ v, 0 ≤ z v ∧ z v ≤ (q : ℝ)) ∧ ∀ a b, r a b → z a ≤ z b := by
  rw [Set.mem_smul_set]
  have hq : 0 ≤ (q : ℝ) := by positivity
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨fun v ↦ ⟨mul_nonneg hq (hf.1 v).1, ?_⟩, ?_⟩
    · simpa only [Pi.smul_apply, smul_eq_mul, mul_one] using mul_le_mul_of_nonneg_left (hf.1 v).2 hq
    · intro a b hab
      exact mul_le_mul_of_nonneg_left (hf.2 a b hab) hq
  · intro hz
    by_cases hzero : q = 0
    · subst q
      refine ⟨fun _ ↦ 0, ⟨fun _ ↦ ⟨le_rfl, by norm_num⟩, fun _ _ _ ↦ le_rfl⟩, ?_⟩
      funext v
      have hv : z v = 0 := le_antisymm (by simpa using (hz.1 v).2) (hz.1 v).1
      simp [hv]
    · have hpos : 0 < (q : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hzero)
      refine ⟨fun v ↦ z v / (q : ℝ), ⟨?_, ?_⟩, ?_⟩
      · intro v
        exact ⟨div_nonneg (hz.1 v).1 hq, (div_le_one hpos).2 (hz.1 v).2⟩
      · intro a b hab
        exact div_le_div_of_nonneg_right (hz.2 a b hab) hq
      · funext v
        exact mul_div_cancel₀ (z v) hpos.ne'

/-- Integer coordinate vectors whose real casts lie in the actual scalar dilate. -/
def LatticePoints (r : V → V → Prop) (q : ℕ) :=
  {z : V → ℤ // (fun v ↦ (z v : ℝ)) ∈ (q : ℝ) • orderPolytope r}

private theorem lattice_coord_nonneg {r : V → V → Prop} {q : ℕ} (z : LatticePoints r q) (v : V) :
    0 ≤ z.val v := by
  have h := ((mem_dilate_orderPolytope r q _).mp z.property).1 v
  exact_mod_cast h.1

private def latticeToLabels {r : V → V → Prop} {q : ℕ}
    (z : LatticePoints r q) : Labels r (q + 1) := by
  have hz := (mem_dilate_orderPolytope r q _).mp z.property
  refine ⟨fun v ↦ ⟨(z.val v).toNat, ?_⟩, ?_⟩
  · apply Nat.lt_succ_of_le
    have hv : z.val v ≤ (q : ℤ) := by exact_mod_cast (hz.1 v).2
    simpa using Int.toNat_le_toNat hv
  · intro a b hab
    apply Int.toNat_le_toNat
    exact_mod_cast hz.2 a b hab

private def labelsToLattice {r : V → V → Prop} {q : ℕ}
    (f : Labels r (q + 1)) : LatticePoints r q := by
  refine ⟨fun v ↦ ((f.val v).val : ℤ), (mem_dilate_orderPolytope r q _).mpr ⟨?_, ?_⟩⟩
  · intro v
    refine ⟨by positivity, ?_⟩
    change (↑((f.val v).val : ℤ) : ℝ) ≤ (q : ℝ)
    exact_mod_cast Nat.le_of_lt_succ (f.val v).isLt
  · intro a b hab
    have h : (f.val a).val ≤ (f.val b).val := f.property a b hab
    change (↑((f.val a).val : ℤ) : ℝ) ≤ (↑((f.val b).val : ℤ) : ℝ)
    exact_mod_cast h

/-- The coordinate-wise bijection with weak labels, including the whole zero dilate. -/
def latticePointsEquivLabels (r : V → V → Prop) (q : ℕ) :
    LatticePoints r q ≃ Labels r (q + 1) where
  toFun := latticeToLabels
  invFun := labelsToLattice
  left_inv z := by
    apply Subtype.ext
    funext v
    exact Int.toNat_of_nonneg (lattice_coord_nonneg z v)
  right_inv f := by
    apply Subtype.ext
    funext v
    apply Fin.ext
    change (((f.val v).val : ℤ).toNat) = (f.val v).val
    simp

theorem latticePointsEquivLabels_val (r : V → V → Prop) (q : ℕ) (z : LatticePoints r q) (v : V) :
    ((latticePointsEquivLabels r q z).val v).val = (z.val v).toNat := rfl

/-- Reindex weak labels along an equivalence preserving and reflecting the relation. -/
def labelsCongr {W : Type*} {r : V → V → Prop} {s : W → W → Prop}
    (e : V ≃ W) (h : ∀ a b, r a b ↔ s (e a) (e b)) (m : ℕ) : Labels r m ≃ Labels s m where
  toFun f := ⟨fun w ↦ f.val (e.symm w), fun a b hab ↦ f.property _ _
    ((h (e.symm a) (e.symm b)).mpr (by simpa using hab))⟩
  invFun f := ⟨fun v ↦ f.val (e v), fun a b hab ↦ f.property _ _ ((h a b).mp hab)⟩
  left_inv f := by
    apply Subtype.ext
    funext v
    change f.val (e.symm (e v)) = f.val v
    rw [e.symm_apply_apply]
  right_inv f := by
    apply Subtype.ext
    funext w
    change f.val (e (e.symm w)) = f.val w
    rw [e.apply_symm_apply]

def latticePointsCongr {W : Type*} {r : V → V → Prop} {s : W → W → Prop}
    (e : V ≃ W) (h : ∀ a b, r a b ↔ s (e a) (e b)) (q : ℕ) :
    LatticePoints r q ≃ LatticePoints s q :=
  (latticePointsEquivLabels r q).trans
    ((labelsCongr e h (q + 1)).trans (latticePointsEquivLabels s q).symm)

variable [Fintype V]

noncomputable instance (r : V → V → Prop) (q : ℕ) : Fintype (LatticePoints r q) :=
  Fintype.ofEquiv _ (latticePointsEquivLabels r q).symm

theorem eval_orderPolynomial_eq_latticePoints (r : V → V → Prop) (q : ℕ) :
    (orderPolynomial r).eval (q : ℚ) = (Fintype.card (LatticePoints r q) : ℚ) := by
  rw [eval_orderPolynomial, Fintype.card_congr (latticePointsEquivLabels r q)]

theorem card_latticePoints_zero (r : V → V → Prop) : Fintype.card (LatticePoints r 0) = 1 := by
  rw [Fintype.card_congr (latticePointsEquivLabels r 0)]
  let f : Labels r 1 := ⟨fun _ ↦ 0, fun _ _ _ ↦ le_rfl⟩
  let : Unique (Labels r 1) := ⟨⟨f⟩, fun g ↦ Subtype.ext (funext fun _ ↦ Subsingleton.elim _ _)⟩
  exact Fintype.card_unique

end
end Polygon.Ehrhart
