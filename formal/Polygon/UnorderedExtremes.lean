import Polygon.ConvexBoundary
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Finset.Sort

/-! A finite full-dimensional set of extreme points admits a strict cyclic listing. -/
noncomputable section

namespace Polygon.UnorderedExtremes

abbrev Point := ℝ × ℝ

private def projection (t : ℝ) (x : Point) : ℝ := x.1 + t * x.2

private def coordinates (t : ℝ) (a x : Point) : Point :=
  (projection t x - projection t a, x.2 - a.2)

private def det (u v : Point) : ℝ := u.1 * v.2 - u.2 * v.1

private def area (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

private theorem coordinates_det (t : ℝ) (a b c : Point) :
    det (coordinates t a b) (coordinates t a c) = area a b c := by
  unfold det coordinates projection area
  dsimp
  ring

private theorem area_chain (a b c d : Point) :
    area b c d = area a b c + area a c d - area a b d := by
  unfold area
  ring

private theorem exists_separating_projection (S : Finset Point) :
    ∃ t, Set.InjOn (projection t) (S : Set Point) := by
  classical
  let forbidden : Finset ℝ := (S ×ˢ S).image (fun (xy : Point × Point) ↦
    (xy.2.1 - xy.1.1) / (xy.1.2 - xy.2.2))
  obtain ⟨t, ht⟩ := forbidden.exists_notMem
  refine ⟨t, fun a ha b hb he ↦ ?_⟩
  change a.1 + t * a.2 = b.1 + t * b.2 at he
  by_cases h : a.2 = b.2
  · apply Prod.ext
    · linarith [congrArg (t * ·) h]
    · exact h
  · exfalso
    apply ht
    refine Finset.mem_image.mpr ⟨(a,b), Finset.mem_product.mpr ⟨ha,hb⟩, ?_⟩
    apply (div_eq_iff (sub_ne_zero.mpr h)).mpr
    nlinarith only [he]

/-- Planar affine span of dimension two requires at least three generators. -/
theorem card_ge_three (S : Finset Point)
    (hfull : affineSpan ℝ (convexHull ℝ (S : Set Point)) = ⊤) : 3 ≤ S.card := by
  have hspan : affineSpan ℝ (S : Set Point) = ⊤ := by
    rwa [affineSpan_convexHull] at hfull
  have hne : S.Nonempty := by
    by_contra hs
    have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hz, Finset.coe_empty, AffineSubspace.span_empty] at hspan
    exact bot_ne_top hspan
  let _ : Nonempty S := hne.to_subtype
  have h := finrank_vectorSpan_range_add_one_le ℝ (fun x : S ↦ (x : Point))
  have hr : Set.range (fun x : S ↦ (x : Point)) = (S : Set Point) := by
    exact Subtype.range_coe_subtype
  rw [hr, ← direction_affineSpan, hspan, AffineSubspace.direction_top,
    finrank_top, Module.finrank_prod, Fintype.card_coe] at h
  norm_num [Module.finrank_self] at h
  exact h

private theorem excluded_hull {S : Set Point} (h : S ⊆ (convexHull ℝ S).extremePoints ℝ)
    {x : Point} (hx : x ∈ S) : x ∉ convexHull ℝ (S \ {x}) := by
  have he := ((convex_convexHull ℝ S).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff.mp
    (h hx)).2
  have hsub : S \ {x} ⊆ convexHull ℝ S \ {x} := by
    intro y hy
    exact ⟨subset_convexHull ℝ S hy.1, hy.2⟩
  exact fun hw ↦ he (convexHull_mono hsub hw)

private theorem affine_from_coordinates {t α β : ℝ} {a u v w : Point}
    (h : coordinates t a v = α • coordinates t a u + β • coordinates t a w) :
    v = (1 - α - β) • a + α • u + β • w := by
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [coordinates, projection, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at h₁ h₂
  apply Prod.ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    linear_combination h₁ - t * h₂
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    linear_combination h₂

private theorem triple_hull {S : Set Point} {a u w : Point} (ha : a ∈ S) (hu : u ∈ S)
    (hw : w ∈ S) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hSum : α + β ≤ 1) :
    (1 - α - β) • a + α • u + β • w ∈ convexHull ℝ S := by
  let z : Fin 3 → Point := ![a,u,w]
  let wt : Fin 3 → ℝ := ![1-α-β,α,β]
  refine mem_convexHull_of_exists_fintype wt z ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · simp [wt]
      linarith
    · simpa [wt] using hα
    · simpa [wt] using hβ
  · simp [wt, Fin.sum_univ_three]
    ring
  · intro i
    fin_cases i <;> simpa [z] using (by first | exact ha | exact hu | exact hw)
  · simp [wt, z, Fin.sum_univ_three]

private def slope (u : Point) : ℝ := u.2 / u.1

private theorem det_pos_of_slope_lt {u v : Point} (hu : 0 < u.1) (hv : 0 < v.1)
    (h : slope u < slope v) : 0 < det u v := by
  unfold slope at h
  have h' := (div_lt_div_iff₀ hu hv).mp h
  unfold det
  linarith only [mul_comm v.2 u.1 ▸ h']

private theorem equal_slope_ray {u v : Point} (hv : 0 < v.1) (hu : 0 < u.1)
    (h : slope u = slope v) : u = (u.1 / v.1) • v + (0 : ℝ) • (0 : Point) := by
  unfold slope at h
  have he := (div_eq_div_iff (ne_of_gt hu) (ne_of_gt hv)).mp h
  apply Prod.ext
  · simp only [zero_smul, add_zero, Prod.smul_fst, smul_eq_mul]
    field_simp
  · simp only [zero_smul, add_zero, Prod.smul_snd, smul_eq_mul]
    field_simp
    linarith only [mul_comm v.2 u.1 ▸ he]

private theorem strict_slope_distinct {S : Set Point} {t : ℝ} {a u v : Point}
    (hS : S ⊆ (convexHull ℝ S).extremePoints ℝ) (ha : a ∈ S) (hu : u ∈ S) (hv : v ∈ S)
    (hau : a ≠ u) (huv : u ≠ v) (hpos : 0 < (coordinates t a u).1)
    (hlt : (coordinates t a u).1 < (coordinates t a v).1)
    (he : slope (coordinates t a u) = slope (coordinates t a v)) : False := by
  let x := coordinates t a u
  let y := coordinates t a v
  have hy : 0 < y.1 := hpos.trans hlt
  have hxy := equal_slope_ray hy hpos he
  have hxy' : x = (x.1 / y.1) • y + (0 : ℝ) • coordinates t a a := by simpa using hxy
  have huEq := affine_from_coordinates hxy'
  have hm := triple_hull (S := S \ {u}) (show a ∈ S \ {u} by exact ⟨ha, hau⟩)
    (show v ∈ S \ {u} by exact ⟨hv, huv.symm⟩)
    (show a ∈ S \ {u} by exact ⟨ha, hau⟩)
    (div_nonneg hpos.le hy.le) (le_refl (0 : ℝ))
    (by simpa only [add_zero] using (div_le_one hy).mpr hlt.le)
  exact excluded_hull hS hu (Eq.mpr (congrArg (· ∈ convexHull ℝ (S \ {u})) huEq) hm)

private theorem coordinates_barycentric {u v w : Point} (h : det u w ≠ 0) :
    v = (det v w / det u w) • u + (det u v / det u w) • w := by
  apply Prod.ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    field_simp
    unfold det
    ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    field_simp
    unfold det
    ring

/-- With three distinct increasing slopes based at an anchor, a nonpositive turn
would place the middle vertex in the convex hull of the other three vertices. -/
private theorem positive_turn {S : Set Point} {t : ℝ} {a u v w : Point}
    (hS : S ⊆ (convexHull ℝ S).extremePoints ℝ) (ha : a ∈ S) (hu : u ∈ S)
    (hv : v ∈ S) (hw : w ∈ S) (hav : a ≠ v) (huv : u ≠ v) (hwv : w ≠ v)
    (hup : 0 < (coordinates t a u).1) (hvp : 0 < (coordinates t a v).1)
    (hwp : 0 < (coordinates t a w).1)
    (h₁ : slope (coordinates t a u) < slope (coordinates t a v))
    (h₂ : slope (coordinates t a v) < slope (coordinates t a w)) : 0 < area u v w := by
  let x := coordinates t a u
  let y := coordinates t a v
  let z := coordinates t a w
  have hxy : 0 < det x y := det_pos_of_slope_lt hup hvp h₁
  have hyz : 0 < det y z := det_pos_of_slope_lt hvp hwp h₂
  have hxz : 0 < det x z := det_pos_of_slope_lt hup hwp (h₁.trans h₂)
  by_contra! hturn
  rw [area_chain a, ← coordinates_det t, ← coordinates_det t, ← coordinates_det t] at hturn
  change det x y + det y z - det x z ≤ 0 at hturn
  have ht : det y z / det x z + det x y / det x z ≤ 1 := by
    rw [← add_div, div_le_one hxz]
    linarith
  have hvEq : v = _ := affine_from_coordinates (coordinates_barycentric (v := y) (ne_of_gt hxz))
  have hm := triple_hull (S := S \ {v}) (show a ∈ S \ {v} by exact ⟨ha, hav⟩)
    (show u ∈ S \ {v} by exact ⟨hu, huv⟩) (show w ∈ S \ {v} by exact ⟨hw, hwv⟩)
    (div_nonneg hyz.le hxz.le) (div_nonneg hxy.le hxz.le) ht
  exact excluded_hull hS hv (Eq.mpr (congrArg (· ∈ convexHull ℝ (S \ {v})) hvEq) hm)

private theorem exists_order_key (S : Finset Point) (hne : S.Nonempty)
    (hS : (S : Set Point) ⊆ (convexHull ℝ (S : Set Point)).extremePoints ℝ) :
    ∃ f : S → WithBot ℝ, Function.Injective f ∧
      ∀ ⦃x y z : S⦄, f x < f y → f y < f z → 0 < area x y z := by
  classical
  obtain ⟨t, hinj⟩ := exists_separating_projection S
  obtain ⟨a, ha, hmin⟩ := S.exists_min_image (projection t) hne
  let key (x : S) : WithBot ℝ :=
    if (x : Point) = a then ⊥ else (slope (coordinates t a x) : WithBot ℝ)
  have hpos (x : S) (hx : (x : Point) ≠ a) : 0 < (coordinates t a x).1 := by
    change 0 < projection t x - projection t a
    exact sub_pos.mpr (lt_of_le_of_ne (hmin x x.2) fun he ↦ hx (hinj ha x.2 he).symm)
  refine ⟨key, ?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    by_cases hx : (x : Point) = a
    · by_cases hy : (y : Point) = a
      · exact hx.trans hy.symm
      · simp [key, hx, hy] at hxy
    · by_cases hy : (y : Point) = a
      · simp [key, hx, hy] at hxy
      have hslopes : slope (coordinates t a x) = slope (coordinates t a y) := by
        simpa [key, hx, hy] using hxy
      by_contra hne'
      have hdiv : (coordinates t a x).1 ≠ (coordinates t a y).1 := by
        intro he
        change projection t x - projection t a = projection t y - projection t a at he
        exact hne' (hinj x.2 y.2 (by linarith))
      rcases lt_or_gt_of_ne hdiv with hlt | hlt
      · exact strict_slope_distinct hS ha x.2 y.2 (fun h ↦ hx h.symm) hne' (hpos x hx) hlt hslopes
      · exact strict_slope_distinct hS ha y.2 x.2 (fun h ↦ hy h.symm) (fun h ↦ hne' h.symm) (hpos y hy) hlt hslopes.symm
  · intro x y z hxy hyz
    have hy : (y : Point) ≠ a := by
      intro h
      simp [key, h] at hxy
    have hz : (z : Point) ≠ a := by
      intro h
      simp [key, h] at hyz
    have h₂ : slope (coordinates t a y) < slope (coordinates t a z) := by
      simpa [key, hy, hz] using hyz
    by_cases hx : (x : Point) = a
    · rw [hx, ← coordinates_det t]
      exact det_pos_of_slope_lt (hpos y hy) (hpos z hz) h₂
    · have h₁ : slope (coordinates t a x) < slope (coordinates t a y) := by
        simpa [key, hx, hy] using hxy
      have hne₁ : (x : Point) ≠ y := fun h ↦ (hxy.ne (congrArg key (Subtype.ext h)))
      have hne₂ : (z : Point) ≠ y := fun h ↦ (hyz.ne (congrArg key (Subtype.ext h.symm)))
      exact positive_turn hS ha x.2 y.2 z.2 (fun h ↦ hy h.symm) hne₁ hne₂
        (hpos x hx) (hpos y hy) (hpos z hz) h₁ h₂

/-- A finite set of extreme points, with at least three members, has an injective
counterclockwise listing. The index parameter is the number of vertices minus three. -/
theorem exists_listing_of_card {S : Finset Point} {m : ℕ} (hcard : S.card = m + 3)
    (hS : (S : Set Point) ⊆ (convexHull ℝ (S : Set Point)).extremePoints ℝ) :
    ∃ p : GeneralRealization.Index m → Point, Set.range p = (S : Set Point) ∧
      Function.Injective p ∧
      ∀ ⦃i j k : GeneralRealization.Index m⦄, i < j → j < k →
        0 < ConvexBoundary.signedArea p i j k := by
  classical
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨key, hkey, hturn⟩ := exists_order_key S hne hS
  let T := (Finset.univ : Finset S).image key
  let f (x : S) : T := ⟨key x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      exact hkey (congrArg Subtype.val he)
    · intro y
      obtain ⟨x, _, he⟩ := Finset.mem_image.mp y.2
      exact ⟨x, Subtype.ext he⟩
  let e := Equiv.ofBijective f hf
  have hTcard : T.card = m + 3 := by
    rw [← Fintype.card_coe T, ← Fintype.card_congr e, Fintype.card_coe S, hcard]
  let order := T.orderIsoOfFin hTcard
  let pointIndex : GeneralRealization.Index m ≃ S := order.toEquiv.trans e.symm
  let p : GeneralRealization.Index m → Point := fun i ↦ pointIndex i
  have hread (i : GeneralRealization.Index m) :
      key (pointIndex i) = (order i : WithBot ℝ) :=
    congrArg Subtype.val (e.apply_symm_apply (order i))
  refine ⟨p, ?_, Subtype.val_injective.comp pointIndex.injective, ?_⟩
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (pointIndex i).2
    · intro hx
      obtain ⟨i, hi⟩ := pointIndex.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  · intro i j k hij hjk
    apply hturn (x := pointIndex i) (y := pointIndex j) (z := pointIndex k)
    · rw [hread, hread]
      exact order.strictMono hij
    · rw [hread, hread]
      exact order.strictMono hjk

/-- For an unordered finite full-dimensional set of extreme points, there exists a
strict cyclic listing of all the points, indexed by its cardinality. -/
theorem exists_boundary_listing {S : Set Point} (hf : S.Finite)
    (hS : S = (convexHull ℝ S).extremePoints ℝ)
    (hfull : affineSpan ℝ (convexHull ℝ S) = ⊤) :
    ∃ (m : ℕ) (p : GeneralRealization.Index m → Point), m + 3 = S.ncard ∧
      Set.range p = S ∧ Function.Injective p ∧ ConvexBoundary.BoundaryOrder p := by
  let T := hf.toFinset
  have hT : (T : Set Point) = S := hf.coe_toFinset
  have hc : 3 ≤ T.card := card_ge_three T (by simpa only [hT] using hfull)
  have hcard : T.card = (T.card - 3) + 3 := by omega
  have hext : (T : Set Point) ⊆ (convexHull ℝ (T : Set Point)).extremePoints ℝ := by
    rw [hT]
    exact hS.le
  obtain ⟨p, hp, hinj, horder⟩ := exists_listing_of_card hcard hext
  rw [hT] at hp
  exact ⟨T.card - 3, p, hcard.symm.trans (Set.ncard_eq_toFinset_card S hf).symm,
    hp, hinj, ConvexBoundary.boundaryOrder_iff_same_sign.mpr (Or.inl horder)⟩

/-- The full exposed face lattice of a finite planar polytope, supplied by its unordered
set of all extreme points. -/
theorem faceOrderIso_of_extremes {S : Set Point} (hf : S.Finite)
    (hS : S = (convexHull ℝ S).extremePoints ℝ)
    (hfull : affineSpan ℝ (convexHull ℝ S) = ⊤) :
    Nonempty (FaceOrder.Face (S.ncard - 1) ≃o
      {F : Set Point // IsExposed ℝ (convexHull ℝ S) F}) := by
  obtain ⟨m, p, hm, hp, _, horder⟩ := exists_boundary_listing hf hS hfull
  rw [← hm, show m + 3 - 1 = m + 2 by omega]
  exact ConvexBoundary.exists_faceOrderIso_of_set S ⟨p, hp, horder⟩

#print axioms card_ge_three
#print axioms exists_listing_of_card
#print axioms exists_boundary_listing
#print axioms faceOrderIso_of_extremes

end Polygon.UnorderedExtremes
