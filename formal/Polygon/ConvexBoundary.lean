import Polygon.GeneralIncidence

/-! Every ordered strictly convex planar polygon has the standard cyclic exposed face lattice. -/
noncomputable section

namespace Polygon.ConvexBoundary

open GeneralRealization (Index Code vertices_subset_iff)

abbrev Point := ℝ × ℝ
variable {n : ℕ} {p : Index n → Point}

/-- The signed determinant of the two edge vectors based at the first point. -/
def signedArea (p : Index n → Point) (i j k : Index n) : ℝ :=
  ((p j).1 - (p i).1) * ((p k).2 - (p i).2) -
    ((p j).2 - (p i).2) * ((p k).1 - (p i).1)

/-- The points are given in a strict cyclic boundary order, in either orientation. -/
def BoundaryOrder (p : Index n → Point) : Prop :=
  ∃ s : ℝ, s ≠ 0 ∧ ∀ ⦃i j k : Index n⦄, i < j → j < k → 0 < s * signedArea p i j k

theorem boundaryOrder_iff_same_sign :
    BoundaryOrder p ↔
      (∀ ⦃i j k : Index n⦄, i < j → j < k → 0 < signedArea p i j k) ∨
      (∀ ⦃i j k : Index n⦄, i < j → j < k → signedArea p i j k < 0) := by
  constructor
  · rintro ⟨s, hs, h⟩
    rcases lt_or_gt_of_ne hs with hneg | hpos
    · exact Or.inr (fun ⦃_ _ _⦄ hij hjk ↦ neg_of_mul_pos_right (h hij hjk) hneg.le)
    · exact Or.inl (fun ⦃_ _ _⦄ hij hjk ↦ pos_of_mul_pos_right (h hij hjk) hpos.le)
  · rintro (h | h)
    · exact ⟨1, one_ne_zero, fun ⦃_ _ _⦄ hij hjk ↦ by simpa using h hij hjk⟩
    · exact ⟨-1, by norm_num, fun ⦃_ _ _⦄ hij hjk ↦ by simpa using h hij hjk⟩

private theorem rotate_area (i j k : Index n) :
    signedArea p i j k = signedArea p k i j := by
  unfold signedArea
  ring

private theorem reverse_area (i j k : Index n) :
    signedArea p i j k = -signedArea p j i k := by
  unfold signedArea
  ring

private theorem swap_last_area (i j k : Index n) :
    signedArea p i j k = -signedArea p i k j := by
  unfold signedArea
  ring

private abbrev OrderedOn (p : Index n → Point) (s : ℝ) : Prop :=
  ∀ ⦃i j k : Index n⦄, i < j → j < k → 0 < s * signedArea p i j k

private theorem area_inside {s : ℝ} (h : OrderedOn p s) {i j k : Index n}
    (hik : i < k) (hkj : k < j) : s * signedArea p i j k < 0 := by
  rw [swap_last_area, mul_neg, neg_lt_zero]
  exact h hik hkj

private theorem area_outside {s : ℝ} (h : OrderedOn p s) {i j k : Index n}
    (hij : i < j) (hk : k < i ∨ j < k) : 0 < s * signedArea p i j k := by
  rcases hk with hki | hjk
  · rw [rotate_area]
    exact h hki hij
  · exact h hij hjk

private theorem area_ne_zero {s : ℝ} (h : OrderedOn p s) {i j k : Index n}
    (hij : i < j) (hki : k ≠ i) (hkj : k ≠ j) : s * signedArea p i j k ≠ 0 := by
  rcases lt_or_gt_of_ne hki with hlt | hgt
  · exact (area_outside h hij (Or.inl hlt)).ne'
  · rcases lt_or_gt_of_ne hkj with hlt | hgt'
    · exact (area_inside h hgt hlt).ne
    · exact (area_outside h hij (Or.inr hgt')).ne'

private theorem points_injective {s : ℝ} (h : OrderedOn p s) : Function.Injective p := by
  suffices hne : ∀ ⦃i j : Index n⦄, i < j → p i ≠ p j by
    intro i j he
    rcases lt_trichotomy i j with hij | hij | hji
    · exact (hne hij he).elim
    · exact hij
    · exact (hne hji he.symm).elim
  intro i j hij hp
  have hcard : ({i,j} : Finset (Index n)).card < (Finset.univ : Finset (Index n)).card := by
    rw [Finset.card_pair hij.ne, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  have hne := area_ne_zero h hij hk.1 hk.2
  simp [signedArea, hp] at hne

private theorem next_value (i : Index n) :
    (i + 1).val = if i.val + 1 < n + 3 then i.val + 1 else 0 := by
  rw [Fin.val_add, Fin.val_one]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [show i.val + 1 = n + 3 by omega, Nat.mod_self]

private theorem next_ne (i : Index n) : i + 1 ≠ i := by simp

private theorem previous_ne_next (i : Index n) : i - 1 ≠ i + 1 := by
  intro h
  have he := congrArg (fun j : Index n ↦ j + 1) h
  simp only [sub_add_cancel, add_assoc] at he
  have hz : (0 : Index n) = 1 + 1 := add_left_cancel (by simpa only [add_zero] using he)
  have hv := congrArg Fin.val hz
  rw [Fin.val_zero, Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt (by omega)] at hv
  omega

private theorem area_next {s : ℝ} (h : OrderedOn p s) (i : Index n) {k : Index n}
    (hki : k ≠ i) (hkn : k ≠ i + 1) : 0 < s * signedArea p i (i + 1) k := by
  have hvi : k.val ≠ i.val := fun he ↦ hki (Fin.ext he)
  have hvn : k.val ≠ (i + 1).val := fun he ↦ hkn (Fin.ext he)
  have hv := next_value i
  split_ifs at hv with hn
  · have hij : i < i + 1 := Fin.lt_def.mpr (by omega)
    have hk : k < i ∨ i + 1 < k := by simp only [Fin.lt_def]; omega
    exact area_outside h hij hk
  · have hk₁ : i + 1 < k := Fin.lt_def.mpr (by omega)
    have hk₂ : k < i := Fin.lt_def.mpr (by omega)
    rw [reverse_area, mul_neg, neg_pos]
    exact area_inside h hk₁ hk₂

private def linear (a b : ℝ) : StrongDual ℝ Point :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ

private theorem eval_linear (a b : ℝ) (x : Point) :
    linear a b x = a * x.1 + b * x.2 := by simp [linear, smul_eq_mul]

private theorem eval_functional (l : StrongDual ℝ Point) (x : Point) :
    l x = l (1, 0) * x.1 + l (0, 1) * x.2 := by
  have h : x = x.1 • ((1,0) : Point) + x.2 • ((0,1) : Point) := by
    apply Prod.ext <;> simp
  conv_lhs => rw [h, map_add, map_smul, map_smul]
  simp [smul_eq_mul, mul_comm]

private def side (p : Index n → Point) (s : ℝ) (i : Index n) : StrongDual ℝ Point :=
  linear (s * ((p (i + 1)).2 - (p i).2)) (-s * ((p (i + 1)).1 - (p i).1))

private theorem side_diff (s : ℝ) (i k : Index n) :
    side p s i (p k) - side p s i (p i) = -(s * signedArea p i (i + 1) k) := by
  unfold side signedArea
  simp only [eval_linear]
  ring

private theorem side_eq_next (s : ℝ) (i : Index n) :
    side p s i (p (i + 1)) = side p s i (p i) := by
  apply sub_eq_zero.mp
  rw [side_diff]
  unfold signedArea
  ring

private theorem side_strict {s : ℝ} (h : OrderedOn p s) (i : Index n) {k : Index n}
    (hki : k ≠ i) (hkn : k ≠ i + 1) : side p s i (p k) < side p s i (p i) := by
  rw [← sub_neg, side_diff, neg_lt_zero]
  exact area_next h i hki hkn

private theorem side_bound {s : ℝ} (h : OrderedOn p s) (i k : Index n) :
    side p s i (p k) ≤ side p s i (p i) := by
  by_cases hki : k = i
  · simp [hki]
  by_cases hkn : k = i + 1
  · rw [hkn, side_eq_next]
  exact (side_strict h i hki hkn).le

private def corner (p : Index n → Point) (s : ℝ) (i : Index n) : StrongDual ℝ Point :=
  side p s (i - 1) + side p s i

private theorem corner_strict {s : ℝ} (h : OrderedOn p s) (i : Index n) {k : Index n}
    (hki : k ≠ i) : corner p s i (p k) < corner p s i (p i) := by
  have he : side p s (i - 1) (p i) = side p s (i - 1) (p (i - 1)) := by
    simpa only [sub_add_cancel] using side_eq_next (p := p) s (i - 1)
  simp only [corner, add_apply, he]
  by_cases hkn : k = i + 1
  · have hkp : k ≠ i - 1 := fun hk ↦ previous_ne_next i (hk.symm.trans hkn)
    exact add_lt_add_of_lt_of_le (side_strict h (i - 1) hkp (by simpa only [sub_add_cancel]))
      (side_bound h i k)
  · exact add_lt_add_of_le_of_lt (side_bound h (i - 1) k) (side_strict h i hki hkn)

/-- The convex hull of the stated ordered points. -/
def polytope (p : Index n → Point) : Set Point := convexHull ℝ (Set.range p)

private def maximizingIndices (p : Index n → Point) (l : StrongDual ℝ Point) : Set (Index n) :=
  {i | ∀ j, l (p j) ≤ l (p i)}

private theorem max_nonempty (l : StrongDual ℝ Point) : (maximizingIndices p l).Nonempty := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i ↦ l (p i))
    ⟨0, Finset.mem_univ _⟩
  exact ⟨i, fun j ↦ hi j (Finset.mem_univ _)⟩

private theorem side_maximizers {s : ℝ} (h : OrderedOn p s) (i : Index n) :
    maximizingIndices p (side p s i) = (GeneralRealization.vertices (.edge i) : Set (Index n)) := by
  ext k
  change (∀ j, side p s i (p j) ≤ side p s i (p k)) ↔ k ∈ (GeneralRealization.vertices (.edge i) : Finset _)
  simp only [GeneralRealization.vertices, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hk
    by_contra! hki
    exact (not_lt_of_ge (hk i)) (side_strict h i hki.1 hki.2)
  · rintro (hki | hkn) j
    · rw [hki]
      exact side_bound h i j
    · rw [hkn, side_eq_next]
      exact side_bound h i j

private theorem corner_maximizers {s : ℝ} (h : OrderedOn p s) (i : Index n) :
    maximizingIndices p (corner p s i) = (GeneralRealization.vertices (.vertex i) : Set (Index n)) := by
  ext k
  change (∀ j, corner p s i (p j) ≤ corner p s i (p k)) ↔ k ∈ (GeneralRealization.vertices (.vertex i) : Finset _)
  simp only [GeneralRealization.vertices, Finset.mem_singleton]
  constructor
  · intro hk
    by_contra hki
    exact (not_lt_of_ge (hk i)) (corner_strict h i hki)
  · rintro rfl j
    by_cases hj : j = k
    · rw [hj]
    · exact (corner_strict h k hj).le

private theorem functional_diff (l : StrongDual ℝ Point) (i k : Index n) :
    l (p k) - l (p i) =
      l (1, 0) * ((p k).1 - (p i).1) + l (0, 1) * ((p k).2 - (p i).2) := by
  rw [eval_functional l (p k), eval_functional l (p i)]
  ring

private theorem tied_functional {s : ℝ} (hs : s ≠ 0) (h : OrderedOn p s)
    {l : StrongDual ℝ Point} (hl : l ≠ 0) {i j : Index n} (hij : i < j)
    (ht : l (p j) = l (p i)) :
    ∃ μ : ℝ, μ ≠ 0 ∧ ∀ k, l (p k) - l (p i) = μ * (s * signedArea p i j k) := by
  let a := l (1, 0)
  let b := l (0, 1)
  let dx := (p j).1 - (p i).1
  let dy := (p j).2 - (p i).2
  have hrel : a * dx + b * dy = 0 := (functional_diff l i j).symm.trans (sub_eq_zero.mpr ht)
  have hzero (ha : a = 0) (hb : b = 0) : False := by
    apply hl
    apply ContinuousLinearMap.ext
    intro x
    rw [eval_functional]
    change a * x.1 + b * x.2 = 0
    simp only [ha, hb, zero_mul, add_zero]
  by_cases hx : dx = 0
  · have hy : dy ≠ 0 := by
      intro hy
      have hpoints : p j = p i := Prod.ext (sub_eq_zero.mp hx) (sub_eq_zero.mp hy)
      exact hij.ne ((points_injective h hpoints).symm)
    have hb : b = 0 := by
      simp only [hx, mul_zero, zero_add] at hrel
      exact (mul_eq_zero.mp hrel).resolve_right hy
    have ha : a ≠ 0 := fun ha ↦ hzero ha hb
    refine ⟨-a / (s * dy), div_ne_zero (neg_ne_zero.mpr ha) (mul_ne_zero hs hy), fun k ↦ ?_⟩
    rw [functional_diff]
    change a * ((p k).1 - (p i).1) + b * ((p k).2 - (p i).2) =
      (-a / (s * dy)) * (s * (dx * ((p k).2 - (p i).2) - dy * ((p k).1 - (p i).1)))
    rw [hb, hx]
    field_simp
    ring
  · have hb : b ≠ 0 := by
      intro hb
      simp only [hb, zero_mul, add_zero] at hrel
      exact hzero ((mul_eq_zero.mp hrel).resolve_right hx) hb
    refine ⟨b / (s * dx), div_ne_zero hb (mul_ne_zero hs hx), fun k ↦ ?_⟩
    rw [functional_diff]
    change a * ((p k).1 - (p i).1) + b * ((p k).2 - (p i).2) =
      (b / (s * dx)) * (s * (dx * ((p k).2 - (p i).2) - dy * ((p k).1 - (p i).1)))
    field_simp
    linear_combination ((p k).1 - (p i).1) * hrel

private theorem adjacent_or_wrap {i j : Index n} (hij : i < j)
    (hno : ∀ u v, i < u → u < j → (v < i ∨ j < v) → False) :
    j = i + 1 ∨ i = j + 1 := by
  have hv : i.val < j.val := hij
  by_cases hconsecutive : i.val + 1 = j.val
  · left
    apply Fin.ext
    rw [next_value, if_pos (by omega), hconsecutive]
  let u : Index n := ⟨i.val + 1, by omega⟩
  have hiu : i < u := Fin.lt_def.mpr (by dsimp [u]; omega)
  have huj : u < j := Fin.lt_def.mpr (by dsimp [u]; omega)
  have hi₀ : i.val = 0 := by
    by_contra hpos
    exact hno u 0 hiu huj (Or.inl (Fin.lt_def.mpr (by simpa only [Fin.val_zero] using
      (show 0 < i.val by omega))))
  have hjlast : j.val + 1 = n + 3 := by
    by_contra hlast
    exact hno u (Fin.last (n + 2)) hiu huj (Or.inr (Fin.lt_def.mpr (by
      rw [Fin.val_last]
      omega)))
  right
  apply Fin.ext
  rw [next_value, if_neg (by omega), hi₀]

private theorem classify_pair {s : ℝ} (hs : s ≠ 0) (h : OrderedOn p s)
    {l : StrongDual ℝ Point} (hl : l ≠ 0) {i j : Index n}
    (hij : i < j) (hi : i ∈ maximizingIndices p l) (hj : j ∈ maximizingIndices p l) :
    ∃ e : Index n, maximizingIndices p l = (GeneralRealization.vertices (.edge e) : Set (Index n)) := by
  have hdiff : l (p j) = l (p i) := (hi j).antisymm (hj i)
  obtain ⟨μ, hμ, hlinear⟩ := tied_functional hs h hl hij hdiff
  have hno (u v : Index n) (hiu : i < u) (huj : u < j) (hv : v < i ∨ j < v) : False := by
    have hu : s * signedArea p i j u < 0 := area_inside h hiu huj
    have hv' : 0 < s * signedArea p i j v := area_outside h hij hv
    rcases lt_or_gt_of_ne hμ with hneg | hpos
    · exact not_lt_of_ge (sub_nonpos.mpr (hi u)) (hlinear u ▸ mul_pos_of_neg_of_neg hneg hu)
    · exact not_lt_of_ge (sub_nonpos.mpr (hi v)) (hlinear v ▸ mul_pos hpos hv')
  have hset : maximizingIndices p l = ({i,j} : Set (Index n)) := by
    ext k
    change k ∈ maximizingIndices p l ↔ k = i ∨ k = j
    constructor
    · intro hk
      by_contra! hne
      have ht : l (p k) - l (p i) = 0 := sub_eq_zero.mpr ((hi k).antisymm (hk i))
      rw [hlinear] at ht
      exact (mul_ne_zero hμ (area_ne_zero h hij hne.1 hne.2)) ht
    · rintro (rfl | rfl)
      · exact hi
      · exact hj
  rcases adjacent_or_wrap hij hno with hnext | hnext
  · exact ⟨i, by simp [hset, GeneralRealization.vertices, hnext]⟩
  · exact ⟨j, by simp [hset, GeneralRealization.vertices, hnext, Set.pair_comm]⟩

private theorem classifies_maximizers {s : ℝ} (hs : s ≠ 0) (h : OrderedOn p s)
    (l : StrongDual ℝ Point) :
    ∃ c : Code n, maximizingIndices p l = (GeneralRealization.vertices c : Set (Index n)) := by
  by_cases hl : l = 0
  · refine ⟨.top, ?_⟩
    ext i
    simp [maximizingIndices, GeneralRealization.vertices, hl]
  obtain ⟨i, hi⟩ := max_nonempty (p := p) l
  by_cases other : ∃ j, j ∈ maximizingIndices p l ∧ j ≠ i
  · obtain ⟨j, hj, hji⟩ := other
    have hc : ∃ e : Index n, maximizingIndices p l = (GeneralRealization.vertices (.edge e) : Set (Index n)) := by
      rcases lt_or_gt_of_ne hji with hj' | hj'
      · exact classify_pair hs h hl hj' hj hi
      · exact classify_pair hs h hl hj' hi hj
    obtain ⟨e, he⟩ := hc
    exact ⟨.edge e, he⟩
  · refine ⟨.vertex i, ?_⟩
    ext j
    simp only [GeneralRealization.vertices, Finset.mem_coe, Finset.mem_singleton]
    exact ⟨fun hj ↦ not_ne_iff.mp fun hji ↦ other ⟨j, hj, hji⟩, fun he ↦ he.symm ▸ hi⟩

-- This convex-hull argument is independent of the coordinates of the generators.
/-- The support of a linear functional on a convex hull is the hull of the
    generators at which the attained maximum occurs. -/
private theorem exposed_hull (l : StrongDual ℝ Point) (S : Set Point) (m : ℝ)
    (hbound : ∀ x ∈ S, l x ≤ m) (hmax : ∃ x ∈ S, l x = m) :
    l.toExposed (convexHull ℝ S) = convexHull ℝ {x ∈ S | l x = m} := by
  let F := convexHull ℝ {x ∈ S | l x = m}
  let C : Set Point := {x | l x ≤ m ∧ (l x = m → x ∈ F)}
  have hc : Convex ℝ C := by
    apply convex_iff_forall_pos.mpr
    intro x hx y hy a b ha hb hab
    change l x ≤ m ∧ _ at hx
    change l y ≤ m ∧ _ at hy
    change l (a • x + b • y) ≤ m ∧ _
    rw [map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    have hm : a * m + b * m = m := by linear_combination m * hab
    refine ⟨(add_le_add (mul_le_mul_of_nonneg_left hx.1 ha.le)
      (mul_le_mul_of_nonneg_left hy.1 hb.le)).trans_eq hm, ?_⟩
    intro he
    have hxe : l x = m := hx.1.eq_of_not_lt fun hlt ↦ by
      linarith only [he, hm, add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hlt ha)
        (mul_le_mul_of_nonneg_left hy.1 hb.le)]
    have hye : l y = m := hy.1.eq_of_not_lt fun hlt ↦ by
      linarith only [he, hm, add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hx.1 ha.le)
        (mul_lt_mul_of_pos_left hlt hb)]
    exact (convex_convexHull ℝ _) (hx.2 hxe) (hy.2 hye) ha.le hb.le hab
  have hall : convexHull ℝ S ⊆ C := convexHull_min (fun x hx ↦
    ⟨hbound x hx, fun he ↦ subset_convexHull ℝ _ ⟨hx, he⟩⟩) hc
  obtain ⟨u, hu, hum⟩ := hmax
  ext x
  constructor
  · rintro ⟨hx, hh⟩
    exact (hall hx).2 ((hall hx).1.antisymm (hum ▸ hh u (subset_convexHull ℝ S hu)))
  · intro hx
    have hx₁ : x ∈ convexHull ℝ S := convexHull_mono (fun _ h ↦ h.1) hx
    have hx₂ : m ≤ l x :=
      convexHull_min (fun y (h : y ∈ {z ∈ S | l z = m}) ↦ h.2.ge)
        (convex_halfSpace_ge l.toLinearMap.isLinear m) hx
    exact ⟨hx₁, fun y hy ↦ (hall hy).1.trans hx₂⟩

private theorem exposed_polytope (l : StrongDual ℝ Point) :
    l.toExposed (polytope p) = convexHull ℝ (p '' maximizingIndices p l) := by
  obtain ⟨i, hi⟩ := max_nonempty (p := p) l
  have hbound : ∀ x ∈ Set.range p, l x ≤ l (p i) := by
    rintro _ ⟨j, rfl⟩
    exact hi j
  rw [polytope, exposed_hull l _ _ hbound ⟨p i, ⟨i, rfl⟩, rfl⟩]
  congr 1
  ext z
  constructor
  · rintro ⟨⟨j, rfl⟩, hj⟩
    exact ⟨j, fun k ↦ (hi k).trans_eq hj.symm, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, rfl⟩, (hi j).antisymm (hj i)⟩

/-- Each listed point is distinguishable in the convex hull of any selected subset. -/
theorem point_mem_hull (h : BoundaryOrder p) (S : Set (Index n)) (i : Index n) :
    p i ∈ convexHull ℝ (p '' S) ↔ i ∈ S := by
  obtain ⟨s, _, hs⟩ := h
  constructor
  · intro hi
    by_contra hni
    let l := corner p s i
    have hsub : convexHull ℝ (p '' S) ⊆ {x | l x < l (p i)} := by
      apply convexHull_min _ (convex_halfSpace_lt l.toLinearMap.isLinear _)
      rintro _ ⟨j, hj, rfl⟩
      exact corner_strict hs i (fun he ↦ hni (he ▸ hj))
    have hl : l (p i) < l (p i) := hsub hi
    exact (lt_irrefl _) hl
  · exact fun hi ↦ subset_convexHull ℝ _ ⟨i, hi, rfl⟩

/-- The geometric face associated to a cyclic incidence code. -/
def indexedFace (p : Index n → Point) (c : Code n) : Set Point :=
  convexHull ℝ (p '' (GeneralRealization.vertices c : Set (Index n)))

theorem indexedFace_subset_iff (h : BoundaryOrder p) {c d : Code n} :
    indexedFace p c ⊆ indexedFace p d ↔ c ≤ d := by
  constructor
  · intro hs
    apply vertices_subset_iff.mp
    intro i hi
    exact (point_mem_hull h _ i).mp (hs ((point_mem_hull h _ i).mpr hi))
  · intro hs
    exact convexHull_mono (Set.image_mono (vertices_subset_iff.mpr hs))

@[simp] theorem indexedFace_bottom : indexedFace p .bottom = ∅ := by
  simp [indexedFace, GeneralRealization.vertices]

@[simp] theorem indexedFace_top : indexedFace p .top = polytope p := by
  simp [indexedFace, GeneralRealization.vertices, polytope]

@[simp] theorem indexedFace_vertex (i : Index n) : indexedFace p (.vertex i) = {p i} := by
  simp [indexedFace, GeneralRealization.vertices]

@[simp] theorem indexedFace_edge (i : Index n) :
    indexedFace p (.edge i) = segment ℝ (p i) (p (i + 1)) := by
  simp [indexedFace, GeneralRealization.vertices, Set.image_pair, convexHull_pair]

theorem indexedFace_isExposed (h : BoundaryOrder p) (c : Code n) :
    IsExposed ℝ (polytope p) (indexedFace p c) := by
  obtain ⟨s, _, hs⟩ := h
  cases c with
  | bottom => rw [indexedFace_bottom]; exact isExposed_empty
  | top => rw [indexedFace_top]
  | vertex i =>
    have he := exposed_polytope (p := p) (corner p s i)
    rw [corner_maximizers hs] at he
    rw [show indexedFace p (.vertex i) = (corner p s i).toExposed (polytope p) from he.symm]
    exact ContinuousLinearMap.toExposed.isExposed
  | edge i =>
    have he := exposed_polytope (p := p) (side p s i)
    rw [side_maximizers hs] at he
    rw [show indexedFace p (.edge i) = (side p s i).toExposed (polytope p) from he.symm]
    exact ContinuousLinearMap.toExposed.isExposed

/-- The full set of exposed faces, including the bottom and top faces. -/
abbrev GeometricFace (p : Index n → Point) := { S : Set Point // IsExposed ℝ (polytope p) S }

private def realize (h : BoundaryOrder p) (c : Code n) : GeometricFace p :=
  ⟨indexedFace p c, indexedFace_isExposed h c⟩

private theorem realize_injective (h : BoundaryOrder p) : Function.Injective (realize h) := by
  intro c d he
  have hval := congrArg Subtype.val he
  exact le_antisymm
    ((indexedFace_subset_iff h).mp hval.le) ((indexedFace_subset_iff h).mp hval.ge)

private theorem realize_surjective (h : BoundaryOrder p) : Function.Surjective (realize h) := by
  intro F
  by_cases hnonempty : F.val.Nonempty
  · obtain ⟨l, hl⟩ := F.property hnonempty
    obtain ⟨s, hs, horient⟩ := h
    obtain ⟨c, hc⟩ := classifies_maximizers hs horient l
    have he := exposed_polytope (p := p) l
    rw [hc] at he
    exact ⟨c, Subtype.ext (he.symm.trans hl.symm)⟩
  · refine ⟨.bottom, Subtype.ext ?_⟩
    exact indexedFace_bottom.trans (Set.not_nonempty_iff_eq_empty.mp hnonempty).symm

/-- Complete incidence, with edge i joining the cyclically successive points i and i+1. -/
def faceOrderIso (h : BoundaryOrder p) : Code n ≃o GeometricFace p where
  toEquiv := Equiv.ofBijective (realize h) ⟨realize_injective h, realize_surjective h⟩
  map_rel_iff' := indexedFace_subset_iff h

@[simp] theorem faceOrderIso_val (h : BoundaryOrder p) (c : Code n) :
    (faceOrderIso h c).val = indexedFace p c := rfl

/-- Characterization of every exposed subset of the actual hull. -/
theorem geometricFace_cases (h : BoundaryOrder p) (F : GeometricFace p) :
    F.val = ∅ ∨ F.val = polytope p ∨ (∃ i, F.val = {p i}) ∨
      ∃ i, F.val = segment ℝ (p i) (p (i + 1)) := by
  obtain ⟨c, rfl⟩ := (faceOrderIso h).surjective F
  rw [faceOrderIso_val]
  cases c with
  | bottom => exact Or.inl indexedFace_bottom
  | top => exact Or.inr (Or.inl indexedFace_top)
  | vertex i => exact Or.inr (Or.inr (Or.inl ⟨i, indexedFace_vertex i⟩))
  | edge i => exact Or.inr (Or.inr (Or.inr ⟨i, indexedFace_edge i⟩))

/-- Coordinates need not be supplied in advance if the point set admits such a listing. -/
theorem exists_faceOrderIso_of_set (S : Set Point)
    (h : ∃ v : Index n → Point, Set.range v = S ∧ BoundaryOrder v) :
    Nonempty (Code n ≃o { F : Set Point // IsExposed ℝ (convexHull ℝ S) F }) := by
  obtain ⟨v, rfl, hv⟩ := h
  exact ⟨faceOrderIso hv⟩

/-- The finite face type obtained from the complete cyclic incidence equivalence. -/
@[instance_reducible] def geometricFaceFintype (h : BoundaryOrder p) : Fintype (GeometricFace p) :=
  Fintype.ofEquiv (Code n) (faceOrderIso h).toEquiv

/-- The Ehrhart polynomial of the order polytope of the entire exposed face order. -/
def geometricEhrhart (h : BoundaryOrder p) : Polynomial ℚ :=
  letI := geometricFaceFintype h
  Ehrhart.orderPolynomial (fun a b : GeometricFace p ↦ a ≤ b)

/-- All such convex hulls give the same Ehrhart polynomial as the cyclic incidence model. -/
theorem geometricEhrhart_eq_faceOrder (h : BoundaryOrder p) :
    geometricEhrhart h = FaceOrder.ehrhartPolynomial (n + 2) := by
  let := geometricFaceFintype h
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℚ))).mono
  rintro _ ⟨q, rfl⟩
  change (geometricEhrhart h).eval (q : ℚ) =
    (FaceOrder.ehrhartPolynomial (n + 2)).eval (q : ℚ)
  rw [geometricEhrhart, Ehrhart.eval_orderPolynomial_eq_latticePoints,
    FaceOrder.eval_ehrhartPolynomial_eq_latticePoints]
  exact_mod_cast Fintype.card_congr (Ehrhart.latticePointsCongr (faceOrderIso h).symm.toEquiv
    (fun _ _ ↦ (faceOrderIso h).symm.map_rel_iff.symm) q)

#print axioms boundaryOrder_iff_same_sign
#print axioms point_mem_hull
#print axioms indexedFace_subset_iff
#print axioms indexedFace_isExposed
#print axioms faceOrderIso
#print axioms geometricFace_cases
#print axioms exists_faceOrderIso_of_set
#print axioms geometricEhrhart_eq_faceOrder

end Polygon.ConvexBoundary
