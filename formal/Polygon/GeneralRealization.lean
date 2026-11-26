import Polygon.GeneralIncidence

/-! The complete exposed-face lattice of the convex hull of any number, at least three,
of consecutive parabola points. The parameter n is the number of vertices minus three. -/
noncomputable section
namespace Polygon.GeneralRealization
variable {n : ℕ}
abbrev Point := ℝ × ℝ
private abbrev coord (i : Index n) : ℝ := i.val

/-- The ordered parabola points, including the two endpoints of the closing edge. -/
def point (i : Index n) : Point := (coord i, (coord i)^2)

def polytope (n : ℕ) : Set Point := convexHull ℝ (Set.range (point (n:=n)))

private theorem coord_injective : Function.Injective (coord (n:=n)) :=
  fun _ _ h ↦ Fin.ext (by exact_mod_cast h)

private theorem coord_le {i j : Index n} (h : i ≤ j) : coord i ≤ coord j := by
  change i.val ≤ j.val at h
  exact_mod_cast h

private theorem coord_lt {i j : Index n} (h : i < j) : coord i < coord j := by
  change i.val < j.val at h
  exact_mod_cast h

private def score (a b : ℝ) (i : Index n) : ℝ := a * coord i + b * (coord i)^2

private def maximizers (a b : ℝ) : Finset (Index n) :=
  Finset.univ.filter (fun i ↦ ∀ j : Index n, score a b j ≤ score a b i)

@[simp] private theorem mem_maximizers {a b : ℝ} {i : Index n} :
    i ∈ maximizers a b ↔ ∀ j : Index n, score a b j ≤ score a b i := by
  simp [maximizers]

private theorem maximizers_nonempty (a b : ℝ) : (maximizers (n:=n) a b).Nonempty := by
  obtain ⟨i, _, hi⟩ := (Finset.univ : Finset (Index n)).exists_max_image (score a b)
    ⟨0, Finset.mem_univ _⟩
  exact ⟨i, mem_maximizers.mpr (fun j ↦ hi j (Finset.mem_univ _))⟩

private theorem score_diff_of_tie {a b : ℝ} {i j : Index n} (hij : i < j)
    (h : score a b i = score a b j) (k : Index n) :
    score a b k - score a b i = b * ((coord k - coord i) * (coord k - coord j)) := by
  have hz : (coord j - coord i) * (a + b * (coord i + coord j)) = 0 := by
    calc
      _ = score a b j - score a b i := by unfold score; ring
      _ = 0 := sub_eq_zero.mpr h.symm
  have ha := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (coord_lt hij).ne')
  calc
    _ = b * ((coord k - coord i) * (coord k - coord j)) +
        (coord k - coord i) * (a + b * (coord i + coord j)) := by unfold score; ring
    _ = _ := by rw [ha, mul_zero, add_zero]

private theorem index_succ_eq {i j : Index n} (h : i.val + 1 = j.val) : i + 1 = j := by
  apply Fin.ext
  rw [Fin.val_add, Fin.val_one, h, Nat.mod_eq_of_lt j.isLt]

private theorem classifies_maximizers (a b : ℝ) :
    ∃ c : Code n, maximizers a b = vertices c := by
  let S := maximizers (n:=n) a b
  have hS : S.Nonempty := maximizers_nonempty (n:=n) a b
  obtain ⟨i, hi, hmin⟩ := S.exists_min_image Fin.val hS
  obtain ⟨j, hj, hmax⟩ := S.exists_max_image Fin.val hS
  have hbest : ∀ k, score a b k - score a b i ≤ 0 := fun k ↦
    sub_nonpos.mpr (mem_maximizers.mp hi k)
  have hties : ∀ k ∈ S, score a b k = score a b i := fun k hk ↦
    (mem_maximizers.mp hi k).antisymm (mem_maximizers.mp hk i)
  by_cases hsame : i = j
  · refine ⟨.vertex i, ?_⟩
    change S = {i}
    ext k
    rw [Finset.mem_singleton]
    constructor
    · intro hk
      exact Fin.ext (((hmax k hk).trans_eq (congrArg Fin.val hsame.symm)).antisymm (hmin k hk))
    · rintro rfl
      exact hi
  have hij : i < j := lt_of_le_of_ne (hmin j hj) hsame
  have hdiff := score_diff_of_tie hij (hties j hj).symm
  rcases lt_trichotomy b 0 with hb | hb | hb
  · have hadj : i.val + 1 = j.val := by
      by_contra hne
      have hij' : i.val < j.val := hij
      let k : Index n := ⟨i.val + 1, by have := j.isLt; omega⟩
      have hik : i < k := by change i.val < i.val + 1; omega
      have hkj : k < j := by change i.val + 1 < j.val; omega
      have hpos := mul_pos_of_neg_of_neg hb
        (mul_neg_of_pos_of_neg (sub_pos.mpr (coord_lt hik)) (sub_neg.mpr (coord_lt hkj)))
      exact hpos.not_ge ((hdiff k) ▸ hbest k)
    have hjend := index_succ_eq hadj
    refine ⟨.edge i, ?_⟩
    change S = {i, i + 1}
    rw [hjend]
    ext k
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hk
      have hk₁ := hmin k hk
      have hk₂ := hmax k hk
      have he : k.val = i.val ∨ k.val = j.val := by omega
      exact he.imp Fin.ext Fin.ext
    · rintro (rfl | rfl)
      · exact hi
      · exact hj
  · refine ⟨.top, ?_⟩
    change S = Finset.univ
    have he (k : Index n) : score a b k = score a b i := by
      have hk := hdiff k
      rw [hb, zero_mul] at hk
      simpa only [hb] using sub_eq_zero.mp hk
    exact Finset.eq_univ_of_forall fun k ↦ mem_maximizers.mpr fun l ↦ by
      rw [he k, he l]
  · have hi0 : i = 0 := by
      by_contra hn
      have h0i : (0 : Index n) < i := lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hn)
      have h0j := h0i.trans hij
      have hp := mul_pos hb (mul_pos_of_neg_of_neg
        (sub_neg.mpr (coord_lt h0i)) (sub_neg.mpr (coord_lt h0j)))
      exact hp.not_ge ((hdiff 0) ▸ hbest 0)
    have hjLast : j = Fin.last (n+2) := by
      by_contra hn
      have hLast : j < (Fin.last (n+2) : Index n) := by
        have hle : j ≤ Fin.last (n+2) := Fin.le_last _
        exact lt_of_le_of_ne hle hn
      have hp := mul_pos hb (mul_pos (sub_pos.mpr (coord_lt (hij.trans hLast)))
        (sub_pos.mpr (coord_lt hLast)))
      exact hp.not_ge ((hdiff (Fin.last (n+2))) ▸ hbest (Fin.last (n+2)))
    refine ⟨.edge (Fin.last (n+2)), ?_⟩
    have hwrap : (Fin.last (n+2) : Index n) + 1 = 0 := Fin.last_add_one _
    change S = {Fin.last (n+2), (Fin.last (n+2) : Index n) + 1}
    rw [hwrap]
    ext k
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hk
      by_contra hn
      push Not at hn
      have h0k : i < k := hi0.symm ▸ lt_of_le_of_ne (Fin.zero_le _) hn.2.symm
      have hkLast : k < j := hjLast.symm ▸ lt_of_le_of_ne (Fin.le_last _) hn.1
      have hneg := mul_neg_of_pos_of_neg hb
        (mul_neg_of_pos_of_neg (sub_pos.mpr (coord_lt h0k)) (sub_neg.mpr (coord_lt hkLast)))
      exact hneg.ne ((hdiff k).symm.trans (sub_eq_zero.mpr (hties k hk)))
    · rintro (rfl | rfl)
      · exact hjLast ▸ hj
      · exact hi0 ▸ hi

private theorem score_vertex_diff (i k : Index n) :
    score (2 * coord i) (-1) k - score (2 * coord i) (-1) i = -(coord k - coord i)^2 := by
  unfold score
  ring

private theorem vertex_maximizers (i : Index n) : maximizers (2 * coord i) (-1) = {i} := by
  have hbest (k : Index n) : score (2 * coord i) (-1) k ≤ score (2 * coord i) (-1) i := by
    apply sub_nonpos.mp
    rw [score_vertex_diff]
    exact neg_nonpos.mpr (sq_nonneg _)
  ext k
  rw [Finset.mem_singleton, mem_maximizers]
  constructor
  · intro h
    apply coord_injective
    have he : score (2 * coord i) (-1) k = score (2 * coord i) (-1) i :=
      (hbest k).antisymm (h i)
    have hz := (score_vertex_diff i k).symm.trans (sub_eq_zero.mpr he)
    have hz' := neg_eq_zero.mp hz
    by_contra hn
    exact (sq_pos_of_ne_zero (sub_ne_zero.mpr hn)).ne' hz'
  · rintro rfl
    exact hbest

private theorem score_edge_diff (b : ℝ) (i j k : Index n) :
    score (-b * (coord i + coord j)) b k - score (-b * (coord i + coord j)) b i =
      b * ((coord k - coord i) * (coord k - coord j)) := by
  unfold score
  ring

private theorem edge_maximizers_of_sign (b : ℝ) (i j : Index n) (hb : b ≠ 0)
    (h : ∀ k : Index n, b * ((coord k - coord i) * (coord k - coord j)) ≤ 0) :
    maximizers (-b * (coord i + coord j)) b = {i, j} := by
  let a := -b * (coord i + coord j)
  have hbest (k : Index n) : score a b k ≤ score a b i := by
    apply sub_nonpos.mp
    exact (score_edge_diff b i j k).trans_le (h k)
  have hmem (k : Index n) : k ∈ maximizers a b ↔ score a b k = score a b i :=
    ⟨fun hk ↦ (hbest k).antisymm (mem_maximizers.mp hk i),
      fun hk ↦ mem_maximizers.mpr fun l ↦ (hbest l).trans_eq hk.symm⟩
  change maximizers a b = {i, j}
  ext k
  rw [hmem, ← sub_eq_zero, score_edge_diff b i j k]
  simp only [mul_eq_zero, hb, false_or, sub_eq_zero, coord_injective.eq_iff,
    Finset.mem_insert, Finset.mem_singleton]

private theorem edge_exposed_parameters (i : Index n) :
    ∃ a b, maximizers a b = {i, i + 1} := by
  by_cases hi : i = Fin.last (n+2)
  · subst i
    have hwrap : (Fin.last (n+2) : Index n) + 1 = 0 := Fin.last_add_one _
    rw [hwrap]
    refine ⟨-1 * (coord (Fin.last (n+2)) + coord (0 : Index n)), 1, ?_⟩
    apply edge_maximizers_of_sign _ _ _ one_ne_zero
    intro k
    rw [one_mul]
    exact mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (coord_le (Fin.le_last k))) (sub_nonneg.mpr (coord_le (Fin.zero_le _)))
  · let j := i + 1
    have hiv : i.val < n+2 := by
      have hne : i.val ≠ n+2 := fun h ↦ hi (Fin.ext h)
      have := i.isLt
      omega
    have hjv : j.val = i.val + 1 := by
      change (i + 1).val = _
      rw [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt (by omega)]
    refine ⟨-(-1) * (coord i + coord j), -1, ?_⟩
    apply edge_maximizers_of_sign _ _ _ (by norm_num)
    intro k
    have he : k ≤ i ∨ j ≤ k := by
      change k.val ≤ i.val ∨ j.val ≤ k.val
      omega
    rw [neg_one_mul]
    apply neg_nonpos.mpr
    rcases he with hki | hjk
    · have hk₁ : k.val ≤ i.val := hki
      have hk₂ : k ≤ j := show k.val ≤ j.val from by omega
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (coord_le hki))
        (sub_nonpos.mpr (coord_le hk₂))
    · have hk₁ : j.val ≤ k.val := hjk
      have hk₂ : i ≤ k := show i.val ≤ k.val from by omega
      exact mul_nonneg (sub_nonneg.mpr (coord_le hk₂)) (sub_nonneg.mpr (coord_le hjk))

private def expose (a b : ℝ) : StrongDual ℝ Point :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ

private theorem expose_at (a b : ℝ) (i : Index n) : expose a b (point i) = score a b i := by
  simp [expose, point, score, smul_eq_mul]

private theorem functional_at (l : StrongDual ℝ Point) (i : Index n) :
    l (point i) = score (l (1, 0)) (l (0, 1)) i := by
  have he : point i = coord i • ((1, 0) : Point) + (coord i)^2 • ((0, 1) : Point) := by
    apply Prod.ext <;> simp [point]
  rw [he, map_add, map_smul, map_smul]
  simp [score, smul_eq_mul, mul_comm]

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

private theorem exposed_polytope_of_scores (l : StrongDual ℝ Point) (a b : ℝ)
    (hs : ∀ i : Index n, l (point i) = score a b i) :
    l.toExposed (polytope n) = convexHull ℝ (point '' (maximizers (n:=n) a b : Set (Index n))) := by
  obtain ⟨i, hi⟩ := maximizers_nonempty (n:=n) a b
  have hbound : ∀ x ∈ Set.range (point (n:=n)), l x ≤ l (point i) := by
    rintro _ ⟨j, rfl⟩
    rw [hs, hs]
    exact mem_maximizers.mp hi j
  rw [polytope, exposed_hull l (Set.range (point (n:=n))) (l (point i)) hbound
    ⟨point i, ⟨i, rfl⟩, rfl⟩]
  congr 1
  ext z
  constructor
  · rintro ⟨⟨j, rfl⟩, hj⟩
    have he : score a b j = score a b i := by simpa only [hs] using hj
    exact ⟨j, mem_maximizers.mpr (fun k ↦ (mem_maximizers.mp hi k).trans_eq he.symm), rfl⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨⟨j, rfl⟩, ?_⟩
    rw [hs, hs]
    exact (mem_maximizers.mp hi j).antisymm (mem_maximizers.mp hj i)

/-- Every marked point remains distinguishable in the hull of any subset of the vertices. -/
theorem point_mem_vertHull (S : Finset (Index n)) (i : Index n) :
    point i ∈ convexHull ℝ (point '' (S : Set (Index n))) ↔ i ∈ S := by
  constructor
  · intro hi
    by_contra hni
    let l := expose (2 * coord i) (-1)
    have hsub : convexHull ℝ (point '' (S : Set (Index n))) ⊆ {x | l x < l (point i)} := by
      apply convexHull_min _ (convex_halfSpace_lt l.toLinearMap.isLinear _)
      rintro _ ⟨j, hj, rfl⟩
      change expose (2 * coord i) (-1) (point j) < expose (2 * coord i) (-1) (point i)
      rw [expose_at, expose_at, ← sub_neg, score_vertex_diff]
      have hjne : j ≠ i := fun he ↦ hni (he ▸ hj)
      exact neg_lt_zero.mpr (sq_pos_of_ne_zero (sub_ne_zero.mpr (coord_injective.ne hjne)))
    have hl : l (point i) < l (point i) := hsub hi
    exact (lt_irrefl _) hl
  · intro hi
    exact subset_convexHull ℝ _ ⟨i, hi, rfl⟩

def indexedFace (c : Code n) : Set Point := convexHull ℝ (point '' (vertices c : Set (Index n)))

/-- The index-set order agrees exactly with inclusion of the genuine geometric faces. -/
theorem indexedFace_subset_iff {c d : Code n} :
    indexedFace c ⊆ indexedFace d ↔ c ≤ d := by
  constructor
  · intro h
    apply vertices_subset_iff.mp
    intro i hi
    exact (point_mem_vertHull _ i).mp (h ((point_mem_vertHull _ i).mpr hi))
  · intro h
    exact convexHull_mono (Set.image_mono (vertices_subset_iff.mpr h))

@[simp] theorem indexedFace_bottom : indexedFace (n:=n) .bottom = ∅ := by
  simp [indexedFace, vertices]

@[simp] theorem indexedFace_top : indexedFace (n:=n) .top = polytope n := by
  simp [indexedFace, vertices, polytope]

/-- Every code has a supporting linear functional, with the empty face included. -/
theorem indexedFace_isExposed (c : Code n) : IsExposed ℝ (polytope n) (indexedFace c) := by
  cases c with
  | bottom => rw [indexedFace_bottom]; exact isExposed_empty
  | top => rw [indexedFace_top]
  | vertex i =>
    let a := 2 * coord i
    have h := exposed_polytope_of_scores (n:=n) (expose a (-1)) a (-1) (expose_at _ _)
    rw [show maximizers a (-1) = {i} from vertex_maximizers i] at h
    rw [show indexedFace (.vertex i) = (expose a (-1)).toExposed (polytope n) from h.symm]
    exact ContinuousLinearMap.toExposed.isExposed
  | edge i =>
    obtain ⟨a, b, hab⟩ := edge_exposed_parameters i
    have h := exposed_polytope_of_scores (n:=n) (expose a b) a b (expose_at _ _)
    rw [hab] at h
    rw [show indexedFace (.edge i) = (expose a b).toExposed (polytope n) from h.symm]
    exact ContinuousLinearMap.toExposed.isExposed

/-- All actual exposed faces of the parabola hull, ordered by set inclusion. -/
abbrev GeometricFace (n : ℕ) := {S : Set Point // IsExposed ℝ (polytope n) S}

def realize (c : Code n) : GeometricFace n := ⟨indexedFace c, indexedFace_isExposed c⟩

private theorem realize_injective : Function.Injective (realize (n:=n)) := by
  intro c d h
  have he := congrArg Subtype.val h
  exact le_antisymm (indexedFace_subset_iff.mp he.le) (indexedFace_subset_iff.mp he.ge)

private theorem realize_surjective : Function.Surjective (realize (n:=n)) := by
  intro F
  by_cases h : F.val.Nonempty
  · obtain ⟨l, hl⟩ := F.property h
    have he := exposed_polytope_of_scores (n:=n) l _ _ (functional_at l)
    obtain ⟨c, hc⟩ := classifies_maximizers (n:=n) (l (1, 0)) (l (0, 1))
    rw [hc] at he
    exact ⟨c, Subtype.ext (he.symm.trans hl.symm)⟩
  · refine ⟨.bottom, Subtype.ext ?_⟩
    exact indexedFace_bottom.trans (Set.not_nonempty_iff_eq_empty.mp h).symm

/-- The entire face lattice of the concrete convex hull, including both extrema. -/
def faceOrderIso : Code n ≃o GeometricFace n where
  toEquiv := Equiv.ofBijective realize ⟨realize_injective, realize_surjective⟩
  map_rel_iff' := indexedFace_subset_iff

@[simp] theorem faceOrderIso_val (c : Code n) : (faceOrderIso c).val = indexedFace c := rfl

@[simp] theorem indexedFace_vertex (i : Index n) :
    indexedFace (.vertex i) = {point i} := by
  simp [indexedFace,vertices]

@[simp] theorem indexedFace_edge (i : Index n) :
    indexedFace (.edge i) = segment ℝ (point i) (point (i+1)) := by
  simp [indexedFace,vertices,Set.image_pair,convexHull_pair]

/-- Every exposed subset of the actual hull is empty, the entire hull, one of the
generating vertices, or a closed segment between cyclically consecutive generators. -/
theorem geometricFace_cases (F : GeometricFace n) :
    F.val = ∅ ∨ F.val = polytope n ∨ (∃ i, F.val = {point (n:=n) i}) ∨
      ∃ i : Index n, F.val = segment ℝ (point i) (point (i+1)) := by
  obtain ⟨c, rfl⟩ := faceOrderIso.surjective F
  rw [faceOrderIso_val]
  cases c with
  | bottom => exact Or.inl indexedFace_bottom
  | top => exact Or.inr (Or.inl indexedFace_top)
  | vertex i => exact Or.inr (Or.inr (Or.inl ⟨i,indexedFace_vertex i⟩))
  | edge i => exact Or.inr (Or.inr (Or.inr ⟨i,indexedFace_edge i⟩))

/-- A geometric face contains precisely the indexed vertices of its face code. -/
theorem point_mem_faceOrderIso (c : Code n) (i : Index n) :
    point i ∈ (faceOrderIso c).val ↔ i ∈ vertices c :=
  point_mem_vertHull _ _

theorem geometricFace_indices (F : GeometricFace n) :
    ∃ c : Code n, ∀ i : Index n, point i ∈ F.val ↔ i ∈ vertices c := by
  obtain ⟨c, rfl⟩ := faceOrderIso.surjective F
  exact ⟨c, point_mem_faceOrderIso c⟩

theorem card_geometricFaces : Nat.card (GeometricFace n) = 2*(n+3)+2 := by
  rw [← Nat.card_congr faceOrderIso.toEquiv, Nat.card_eq_fintype_card]
  exact FaceOrder.card_face (n+2)

theorem point_mem_polytope (i : Index n) : point i ∈ polytope n :=
  subset_convexHull ℝ _ ⟨i, rfl⟩

/-- The parabola hull has full affine dimension in its ambient plane. -/
theorem vectorSpan_polytope : vectorSpan ℝ (polytope n) = ⊤ := by
  let L := vectorSpan ℝ (polytope n)
  apply top_unique
  intro z _
  have h₁ : ((1, 1) : Point) ∈ L := by
    have h : point (1 : Index n) - point (0 : Index n) ∈ L := vsub_mem_vectorSpan ℝ
      (point_mem_polytope 1) (point_mem_polytope 0)
    have he : point (1 : Index n) - point (0 : Index n) = ((1, 1) : Point) := by
      apply Prod.ext <;> norm_num [point,coord,Fin.val_one]
    exact he ▸ h
  have h₂ : ((2, 4) : Point) ∈ L := by
    have h : point (2 : Index n) - point (0 : Index n) ∈ L := vsub_mem_vectorSpan ℝ
      (point_mem_polytope 2) (point_mem_polytope 0)
    have htwo : coord (2 : Index n) = 2 := by
      change (((2 : Index n).val : ℕ) : ℝ) = 2
      exact_mod_cast (Nat.mod_eq_of_lt (show 2 < n+3 by omega))
    have he : point (2 : Index n) - point (0 : Index n) = ((2, 4) : Point) := by
      apply Prod.ext <;> norm_num [point, htwo,show coord (0 : Index n) = 0 by simp [coord]]
    exact he ▸ h
  let a : ℝ := 2 * z.1 - z.2
  let b : ℝ := (z.2 - z.1) / 2
  have hz : z = a • ((1, 1) : Point) + b • ((2, 4) : Point) := by
    apply Prod.ext <;> simp [a, b] <;> ring
  rw [hz]
  exact L.add_mem (L.smul_mem a h₁) (L.smul_mem b h₂)

theorem affineFinrank_polytope : Module.finrank ℝ (vectorSpan ℝ (polytope n)) = 2 := by
  rw [vectorSpan_polytope, finrank_top, Module.finrank_prod]
  simp


noncomputable instance (n : ℕ) : Fintype (GeometricFace n) :=
  Fintype.ofEquiv (Code n) faceOrderIso.toEquiv

/-- The actual order polytope uses all subsets exposed by continuous linear forms,
including the empty face and the hull itself. -/
def geometricEhrhart (n : ℕ) : Polynomial ℚ :=
  Ehrhart.orderPolynomial (fun a b : GeometricFace n ↦ a ≤ b)

def latticePointsEquivLabeling (n q : ℕ) :
    Ehrhart.LatticePoints (fun a b : GeometricFace n ↦ a ≤ b) q ≃ Tally.Labeling (n+2) q :=
  (Ehrhart.latticePointsCongr faceOrderIso.symm.toEquiv
    (fun _ _ ↦ (faceOrderIso.symm.map_rel_iff).symm) q).trans
      (FaceOrder.latticePointsEquivLabeling (n+2) q)

theorem geometricCounts (n q : ℕ) : (geometricEhrhart n).eval (q : ℚ) =
    (Fintype.card (Ehrhart.LatticePoints (fun a b : GeometricFace n ↦ a ≤ b) q) : ℚ) :=
  Ehrhart.eval_orderPolynomial_eq_latticePoints _ q

theorem geometricEhrhart_eq_faceOrder (n : ℕ) :
    geometricEhrhart n = FaceOrder.ehrhartPolynomial (n+2) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℚ))).mono
  rintro _ ⟨q, rfl⟩
  change (geometricEhrhart n).eval (q : ℚ) = _
  rw [geometricCounts,FaceOrder.eval_ehrhartPolynomial,
      Fintype.card_congr (latticePointsEquivLabeling n q)]

theorem faceOrderCountsGeometricLatticePoints (n q : ℕ) :
    (FaceOrder.ehrhartPolynomial (n+2)).eval (q : ℚ) =
      (Fintype.card (Ehrhart.LatticePoints (fun a b : GeometricFace n ↦ a ≤ b) q) : ℚ) := by
  rw [← geometricEhrhart_eq_faceOrder, geometricCounts]

/-- Standard side-count indexing, with n itself denoting the number of sides. -/
theorem ehrhart_by_sides {n : ℕ} (hn : 3 ≤ n) :
    geometricEhrhart (n-3) = FaceOrder.ehrhartPolynomial (n-1) := by
  simpa only [show n-3+2=n-1 by omega] using geometricEhrhart_eq_faceOrder (n-3)

#print axioms ehrhart_by_sides
#print axioms faceOrderIso
#print axioms geometricFace_cases
#print axioms geometricFace_indices
#print axioms card_geometricFaces
#print axioms affineFinrank_polytope
#print axioms geometricCounts
#print axioms geometricEhrhart_eq_faceOrder
#print axioms faceOrderCountsGeometricLatticePoints

end Polygon.GeneralRealization
