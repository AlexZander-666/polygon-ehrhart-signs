import Mathlib

/-! Weak labels of a finite relation are counted by a rational polynomial. -/

namespace Polygon.Ehrhart

noncomputable section

open Polynomial Finset
open scoped BigOperators

variable {V : Type*} [Fintype V]

/-- Labels in an ordered set of `m` elements that respect the specified relation. -/
abbrev Labels (r : V → V → Prop) (m : ℕ) :=
  {f : V → Fin m // ∀ a b, r a b → f a ≤ f b}

/-- Weak labels using every one of the `m` values. -/
abbrev SurjectiveLabels (r : V → V → Prop) (m : ℕ) :=
  {f : Labels r m // Function.Surjective f.val}

noncomputable instance (r : V → V → Prop) (m : ℕ) : Fintype (Labels r m) :=
  Fintype.ofFinite _

noncomputable instance (r : V → V → Prop) (m : ℕ) : Fintype (SurjectiveLabels r m) :=
  Fintype.ofFinite _

private def values {r : V → V → Prop} {m : ℕ} (f : Labels r m) : Finset (Fin m) :=
  univ.image f.val

private def intoRange {r : V → V → Prop} {m : ℕ} (s : Finset (Fin m))
    (f : {f : Labels r m // values f = s}) (v : V) : s :=
  ⟨f.val.val v, by
    have he := congrArg (fun t : Finset (Fin m) ↦ f.val.val v ∈ t) f.property
    exact he.mp (mem_image_of_mem _ (mem_univ _))⟩

private theorem intoRange_surjective {r : V → V → Prop} {m : ℕ} (s : Finset (Fin m))
    (f : {f : Labels r m // values f = s}) : Function.Surjective (intoRange s f) := by
  intro y
  have he := congrArg (fun t : Finset (Fin m) ↦ y.val ∈ t) f.property
  have hy := he.mpr y.property
  obtain ⟨v, _, hv⟩ := mem_image.mp hy
  exact ⟨v, Subtype.ext hv⟩

private def compress {r : V → V → Prop} {m : ℕ} (s : Finset (Fin m))
    (f : {f : Labels r m // values f = s}) : SurjectiveLabels r s.card := by
  let e := s.orderIsoOfFin rfl
  refine ⟨⟨fun v ↦ e.symm (intoRange s f v), ?_⟩, ?_⟩
  · intro a b hab
    exact e.symm.monotone (f.val.property a b hab)
  · exact e.symm.surjective.comp (intoRange_surjective s f)

private def decompress {r : V → V → Prop} {m : ℕ} (s : Finset (Fin m))
    (f : SurjectiveLabels r s.card) : {f : Labels r m // values f = s} := by
  let e := s.orderIsoOfFin rfl
  refine ⟨⟨fun v ↦ (e (f.val.val v)).val, ?_⟩, ?_⟩
  · intro a b hab
    exact e.monotone (f.val.property a b hab)
  · ext y
    change y ∈ univ.image (fun v ↦ (e (f.val.val v)).val) ↔ y ∈ s
    constructor
    · intro h
      obtain ⟨v, _, rfl⟩ := mem_image.mp h
      exact (e (f.val.val v)).property
    · intro h
      obtain ⟨v, hv⟩ := f.property (e.symm ⟨y, h⟩)
      refine mem_image.mpr ⟨v, mem_univ _, ?_⟩
      rw [hv, e.apply_symm_apply]

private def fiberEquiv {r : V → V → Prop} {m : ℕ} (s : Finset (Fin m)) :
    {f : Labels r m // values f = s} ≃ SurjectiveLabels r s.card where
  toFun := compress s
  invFun := decompress s
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    exact congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply (intoRange s f v))
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    exact (s.orderIsoOfFin rfl).symm_apply_apply (f.val.val v)

private theorem card_labels_sum_support (r : V → V → Prop) (m : ℕ) :
    Fintype.card (Labels r m) =
      ∑ s : Finset (Fin m), Fintype.card (SurjectiveLabels r s.card) := by
  classical
  let eqv := (Equiv.sigmaFiberEquiv (values (r := r) (m := m))).symm
  rw [Fintype.card_congr eqv, Fintype.card_sigma]
  exact sum_congr rfl fun s _ ↦ Fintype.card_congr (fiberEquiv s)

private theorem card_surjectiveLabels_eq_zero (r : V → V → Prop) {k : ℕ}
    (hk : Fintype.card V < k) : Fintype.card (SurjectiveLabels r k) = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun f ↦ ?_⟩
  have hle := Fintype.card_le_of_surjective f.val.val f.property
  rw [Fintype.card_fin] at hle
  exact (not_le_of_gt hk hle).elim

private theorem sum_finset_card {m : ℕ} (a : ℕ → ℕ) :
    (∑ s : Finset (Fin m), a s.card) = ∑ k ∈ range (m + 1), m.choose k * a k := by
  classical
  let u : Finset (Fin m) := univ
  have hu : u.card = m := Fintype.card_fin m
  change (∑ s ∈ (univ : Finset (Finset (Fin m))), a s.card) = _
  rw [← Finset.powerset_univ, Finset.powerset_card_biUnion, Finset.sum_biUnion
    (u.pairwise_disjoint_powersetCard.set_pairwise _), hu]
  refine sum_congr rfl fun k _ ↦ ?_
  change (∑ s ∈ u.powersetCard k, a s.card) = m.choose k * a k
  calc
    _ = ∑ _s ∈ u.powersetCard k, a k := by
      exact sum_congr rfl fun s hs ↦ congrArg a (mem_powersetCard.mp hs).2
    _ = _ := by simp [card_powersetCard, hu]

/-- The number of labels is obtained by choosing the used values and then
assigning their increasing ranks surjectively. -/
theorem card_labels_eq_sum_choose (r : V → V → Prop) (m : ℕ) :
    Fintype.card (Labels r m) =
      ∑ k ∈ range (Fintype.card V + 1), m.choose k * Fintype.card (SurjectiveLabels r k) := by
  rw [card_labels_sum_support, sum_finset_card (fun k ↦ Fintype.card (SurjectiveLabels r k))]
  let n := Fintype.card V
  let term k := m.choose k * Fintype.card (SurjectiveLabels r k)
  have hm : m + 1 ≤ max m n + 1 := Nat.succ_le_succ (le_max_left _ _)
  have hn : n + 1 ≤ max m n + 1 := Nat.succ_le_succ (le_max_right _ _)
  change (∑ k ∈ range (m + 1), term k) = ∑ k ∈ range (n + 1), term k
  calc
    _ = ∑ k ∈ range (max m n + 1), term k := by
      refine sum_subset (range_mono hm) fun k _ hk ↦ ?_
      have hlt : m < k := by simp only [mem_range] at hk; omega
      simp [term, Nat.choose_eq_zero_of_lt hlt]
    _ = _ := by
      symm
      refine sum_subset (range_mono hn) fun k _ hk ↦ ?_
      have hlt : Fintype.card V < k := by
        change n < k
        simp only [mem_range] at hk
        omega
      simp [term, card_surjectiveLabels_eq_zero r hlt]

/-- The polynomial `binom(X+1,k)` over the rationals. -/
def choosePolynomial (k : ℕ) : ℚ[X] :=
  ((descPochhammer ℚ k).comp (X + 1)) * C ((k.factorial : ℚ)⁻¹)

theorem eval_choosePolynomial (q k : ℕ) :
    (choosePolynomial k).eval (q : ℚ) = ((q + 1).choose k : ℚ) := by
  rw [choosePolynomial, eval_mul, eval_comp]
  simp only [eval_add, eval_X, eval_one, eval_C]
  rw [← Nat.cast_succ, Nat.cast_choose_eq_descPochhammer_div]
  exact (div_eq_mul_inv _ _).symm

theorem natDegree_choosePolynomial_le (k : ℕ) : (choosePolynomial k).natDegree ≤ k := by
  unfold choosePolynomial
  refine natDegree_mul_le.trans ?_
  rw [natDegree_C, add_zero]
  apply natDegree_comp_le.trans
  rw [descPochhammer_natDegree, show (1 : ℚ[X]) = C (1 : ℚ) by simp,
    natDegree_X_add_C, mul_one]

/-- The order polynomial for weak labels with allowed values `0,...,q`. -/
def orderPolynomial (r : V → V → Prop) : ℚ[X] :=
  ∑ k ∈ range (Fintype.card V + 1),
    C (Fintype.card (SurjectiveLabels r k) : ℚ) * choosePolynomial k

theorem natDegree_orderPolynomial_le (r : V → V → Prop) :
    (orderPolynomial r).natDegree ≤ Fintype.card V := by
  unfold orderPolynomial
  refine natDegree_sum_le_of_forall_le _ _ fun k hk ↦ ?_
  apply natDegree_mul_le.trans
  rw [natDegree_C, zero_add]
  exact (natDegree_choosePolynomial_le k).trans (Nat.le_of_lt_succ (mem_range.mp hk))

theorem eval_orderPolynomial (r : V → V → Prop) (q : ℕ) :
    (orderPolynomial r).eval (q : ℚ) = (Fintype.card (Labels r (q + 1)) : ℚ) := by
  rw [card_labels_eq_sum_choose]
  simp only [orderPolynomial, eval_finsetSum, eval_mul, eval_C, eval_choosePolynomial,
    Nat.cast_sum, Nat.cast_mul]
  exact sum_congr rfl fun _ _ ↦ mul_comm _ _

end
end Polygon.Ehrhart
