import Polygon.Trace

/-! Counting the weakly increasing labels of the polygon face poset. -/

noncomputable section
open scoped BigOperators

namespace Polygon.Tally

private abbrev prepend {A : Type*} {k : ℕ} (a : A) (x : Fin k → A) : Fin (k + 1) → A :=
  Fin.cons (α := fun _ ↦ A) a x

private abbrev appendLast {A : Type*} {k : ℕ} (x : Fin k → A) (b : A) : Fin (k + 1) → A :=
  Fin.snoc (α := fun _ ↦ A) x b

private def pathWeight {m k : ℕ} (M : Matrix (Fin m) (Fin m) ℕ)
    (a b : Fin m) (x : Fin k → Fin m) : ℕ :=
  let y := appendLast (prepend a x) b
  ∏ i : Fin (k + 1), M (y i.castSucc) (y i.succ)

private theorem pathWeight_cons {m k : ℕ} (M : Matrix (Fin m) (Fin m) ℕ)
    (a z b : Fin m) (x : Fin k → Fin m) :
    pathWeight M a b (prepend z x) = M a z * pathWeight M z b x := by
  unfold pathWeight
  rw [Fin.prod_univ_succ]
  have he : appendLast (prepend a (prepend z x)) b =
      prepend a (appendLast (prepend z x) b) := (Fin.cons_snoc_eq_snoc_cons _ _ _).symm
  rw [he]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Fin.snoc_castSucc]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have hi : prepend a (appendLast (prepend z x) b) i.succ.castSucc = prepend z x i := by
    rw [Fin.castSucc_succ]
    simp
  exact congrArg (fun c : Fin m ↦ M c (appendLast (prepend z x) b i.succ)) hi

private theorem matrix_entry_paths {m : ℕ} (M : Matrix (Fin m) (Fin m) ℕ)
    (k : ℕ) (a b : Fin m) :
    (M ^ (k + 1)) a b = ∑ x : Fin k → Fin m, pathWeight M a b x := by
  induction k generalizing a with
  | zero =>
    rw [pow_one]
    simp [pathWeight]
    have he : appendLast (prepend a (default : Fin 0 → Fin m)) b (1 : Fin 2) = b := by
      change appendLast (prepend a (default : Fin 0 → Fin m)) b (Fin.last 1) = b
      exact Fin.snoc_last ..
    exact congrArg (M a) he.symm
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih, Finset.mul_sum]
    rw [← Fintype.sum_prod_type' (fun z x ↦ M a z * pathWeight M z b x)]
    apply Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (k + 1) ↦ Fin m)
    rintro ⟨z, x⟩
    exact (pathWeight_cons M a z b x).symm

private theorem closedPathWeight {m k : ℕ} (M : Matrix (Fin m) (Fin m) ℕ)
    (a : Fin m) (x : Fin k → Fin m) :
    pathWeight M a a x = ∏ i : Fin (k + 1), M (prepend a x i) (prepend a x (i + 1)) := by
  unfold pathWeight
  apply Finset.prod_congr rfl
  intro i _
  have hnext (j : Fin (k + 1)) :
      appendLast (prepend a x) a j.succ = prepend a x (j + 1) := by
    refine Fin.lastCases ?_ (fun t ↦ ?_) j
    · simp
    · rw [Fin.coeSucc_eq_succ, Fin.succ_castSucc]
      exact Fin.snoc_castSucc ..
  exact congrArg₂ (fun u v : Fin m ↦ M u v) (Fin.snoc_castSucc ..) (hnext i)

/-- A matrix trace sums the products of transition weights of ordered cyclic vertex strings. -/
theorem trace_pow_cycle {m : ℕ} (M : Matrix (Fin m) (Fin m) ℕ) (k : ℕ) :
    Matrix.trace (M ^ (k + 1)) = ∑ x : Fin (k + 1) → Fin m, ∏ i, M (x i) (x (i + 1)) := by
  unfold Matrix.trace
  simp_rw [Matrix.diag_apply, matrix_entry_paths]
  rw [← Fintype.sum_prod_type' (fun a x ↦ pathWeight M a a x)]
  apply Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (k + 1) ↦ Fin m)
  rintro ⟨a, x⟩
  exact closedPathWeight M a x

/-- Vertex labels and the independent edge labels above the two incident vertices,
    after subtracting the common bottom label. The cycle has `k+1` vertices. -/
abbrev Coloring (k m : ℕ) := Σ v : Fin (k + 1) → Fin m,
  ∀ i : Fin (k + 1), {e : Fin m // max (v i) (v (i + 1)) ≤ e}

private theorem upperLabels_card {m : ℕ} (a : Fin m) :
    Fintype.card {e : Fin m // a ≤ e} = m - a.val := by
  let equiv : {e : Fin m // a ≤ e} ≃ ↥(Finset.Ici a) :=
    Equiv.subtypeEquivRight (fun _ ↦ Finset.mem_Ici.symm)
  rw [Fintype.card_congr equiv, Fintype.card_coe, Fin.card_Ici]

theorem card_coloring (k m : ℕ) :
    Fintype.card (Coloring k m) = ∑ v : Fin (k + 1) → Fin m,
      ∏ i, (m - max (v i).val (v (i + 1)).val) := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro v _
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [upperLabels_card]
  rfl

/-- Weak labels of the bottom, the cycle of vertices, the cycle of edges and the top.
    Each listed inequality is an upward cover, except `lo_le_hi`, which follows
    along any of the paths from bottom to top. -/
@[ext]
structure Labeling (k q : ℕ) where
  lo : Fin (q + 1)
  hi : Fin (q + 1)
  vertex : Fin (k + 1) → Fin (q + 1)
  edge : Fin (k + 1) → Fin (q + 1)
  lo_le_hi : lo ≤ hi
  lo_le_vertex : ∀ i, lo ≤ vertex i
  vertex_le_edge : ∀ i, vertex i ≤ edge i
  next_le_edge : ∀ i, vertex (i + 1) ≤ edge i
  edge_le_hi : ∀ i, edge i ≤ hi

private abbrev WidthData (k q : ℕ) :=
  Σ d : Fin (q + 1), Fin (q + 1 - d.val) × Coloring k (d.val + 1)

private theorem vertex_le_hi {k q : ℕ} (L : Labeling k q) (i : Fin (k + 1)) :
    L.vertex i ≤ L.hi := (L.vertex_le_edge i).trans (L.edge_le_hi i)

private theorem lo_le_edge {k q : ℕ} (L : Labeling k q) (i : Fin (k + 1)) :
    L.lo ≤ L.edge i := (L.lo_le_vertex i).trans (L.vertex_le_edge i)

private def width {k q : ℕ} (L : Labeling k q) : Fin (q + 1) :=
  ⟨L.hi.val - L.lo.val, (Nat.sub_le ..).trans_lt L.hi.isLt⟩

private def offset {k q : ℕ} (L : Labeling k q) : Fin (q + 1 - (width L).val) := by
  refine ⟨L.lo.val, ?_⟩
  change L.lo.val < q + 1 - (L.hi.val - L.lo.val)
  have h : L.lo.val ≤ L.hi.val := L.lo_le_hi
  have := L.hi.isLt
  omega

private def subtractBottom {k q : ℕ} (L : Labeling k q) (c : Fin (q + 1)) (hc : c ≤ L.hi) :
    Fin ((width L).val + 1) :=
  ⟨c.val - L.lo.val, Nat.lt_succ_of_le (Nat.sub_le_sub_right hc _)⟩

private def toWidthData {k q : ℕ} (L : Labeling k q) : WidthData k q := by
  let v i := subtractBottom L (L.vertex i) (vertex_le_hi L i)
  refine ⟨width L, offset L, v, fun i ↦ ⟨subtractBottom L (L.edge i) (L.edge_le_hi i), ?_⟩⟩
  apply max_le
  · exact Nat.sub_le_sub_right (L.vertex_le_edge i) _
  · exact Nat.sub_le_sub_right (L.next_le_edge i) _

private def liftColor {q : ℕ} (d : Fin (q + 1)) (a : Fin (q + 1 - d.val))
    (x : Fin (d.val + 1)) : Fin (q + 1) := by
  refine ⟨a.val + x.val, ?_⟩
  have := a.isLt
  have := x.isLt
  omega

private def fromWidthData {k q : ℕ} : WidthData k q → Labeling k q
  | ⟨d, a, v, edges⟩ => by
    have ha := a.isLt
    refine
      { lo := ⟨a.val, by omega⟩
        hi := ⟨a.val + d.val, by omega⟩
        vertex := fun i ↦ liftColor d a (v i)
        edge := fun i ↦ liftColor d a (edges i).val
        lo_le_hi := Nat.le_add_right _ _
        lo_le_vertex := fun _ ↦ Nat.le_add_right _ _
        vertex_le_edge := fun i ↦ Nat.add_le_add_left
          ((le_max_left (v i) (v (i + 1))).trans (edges i).property) _
        next_le_edge := fun i ↦ Nat.add_le_add_left
          ((le_max_right (v i) (v (i + 1))).trans (edges i).property) _
        edge_le_hi := fun i ↦ Nat.add_le_add_left (Nat.le_of_lt_succ (edges i).val.isLt) _ }

private theorem fromWidthData_surjective (k q : ℕ) :
    Function.Surjective (fromWidthData (k := k) (q := q)) := by
  intro L
  refine ⟨toWidthData L, ?_⟩
  apply Labeling.ext
  · exact Fin.ext rfl
  · apply Fin.ext
    change L.lo.val + (L.hi.val - L.lo.val) = L.hi.val
    exact Nat.add_sub_of_le L.lo_le_hi
  · funext i
    apply Fin.ext
    change L.lo.val + ((L.vertex i).val - L.lo.val) = (L.vertex i).val
    exact Nat.add_sub_of_le (L.lo_le_vertex i)
  · funext i
    apply Fin.ext
    change L.lo.val + ((L.edge i).val - L.lo.val) = (L.edge i).val
    exact Nat.add_sub_of_le (lo_le_edge L i)

private theorem fromWidthData_injective (k q : ℕ) :
    Function.Injective (fromWidthData (k := k) (q := q)) := by
  rintro ⟨d, a, v, ev⟩ ⟨e, b, w, ew⟩ h
  have hlo := congrArg (fun L : Labeling k q ↦ L.lo.val) h
  have hhi := congrArg (fun L : Labeling k q ↦ L.hi.val) h
  change a.val = b.val at hlo
  change a.val + d.val = b.val + e.val at hhi
  have hde : d = e := Fin.ext (by omega)
  subst e
  have hab : a = b := Fin.ext hlo
  subst b
  have hvw : v = w := by
    funext i
    apply Fin.ext
    have he := congrArg (fun L : Labeling k q ↦ (L.vertex i).val) h
    change a.val + (v i).val = a.val + (w i).val at he
    omega
  subst w
  have hew : ev = ew := by
    funext i
    apply Subtype.ext
    apply Fin.ext
    have he := congrArg (fun L : Labeling k q ↦ (L.edge i).val) h
    change a.val + (ev i).val.val = a.val + (ew i).val.val at he
    omega
  subst ew
  rfl

/-- Choose the width minus one, the bottom label, and the vertex and edge labels
    shifted into that interval. The width and shift are uniquely determined. -/
def widthEquiv (k q : ℕ) : Labeling k q ≃ WidthData k q :=
  (Equiv.ofBijective fromWidthData
    ⟨fromWidthData_injective k q, fromWidthData_surjective k q⟩).symm

instance (k q : ℕ) : Fintype (Labeling k q) :=
  Fintype.ofEquiv (WidthData k q) (widthEquiv k q).symm

theorem card_coloring_eq_trace (k m : ℕ) :
    Fintype.card (Coloring k m) = (Polygon.Cert.transfer m ^ (k + 1)).trace := by
  rw [card_coloring, trace_pow_cycle]
  rfl

/-- Width `m=d+1` permits `q+1-d` distinct choices of the bottom label. -/
theorem card_labeling_eq_trace (k q : ℕ) :
    Fintype.card (Labeling k q) = ∑ d : Fin (q + 1),
      (q + 1 - d.val) * (Polygon.Cert.transfer (d.val + 1) ^ (k + 1)).trace := by
  rw [Fintype.card_congr (widthEquiv k q), Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin, card_coloring_eq_trace]

theorem card_labeling_eq_traceCount (k q : ℕ) :
    Fintype.card (Labeling k q) = ∑ d : Fin (q + 1),
      (q + 1 - d.val) * Polygon.Cert.traceCount (k + 1) (d.val + 1) := by
  simp only [Polygon.Cert.traceCount_correct, card_labeling_eq_trace]

private theorem sum_widths (q : ℕ) (f : ℕ → ℕ) :
    (∑ d : Fin (q + 1), (q + 1 - d.val) * f (d.val + 1)) =
      ∑ m ∈ Finset.Icc 1 (q + 1), (q + 2 - m) * f m := by
  rw [Fin.sum_univ_eq_sum_range (fun d ↦ (q + 1 - d) * f (d + 1))]
  have himage : (Finset.range (q + 1)).image Nat.succ = Finset.Icc 1 (q + 1) := by
    ext n
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨d, hd, rfl⟩
      omega
    · rintro ⟨hn, hq⟩
      exact ⟨n - 1, by omega, by omega⟩
  rw [← himage, Finset.sum_image Nat.succ_injective.injOn]
  apply Finset.sum_congr rfl
  intro d _
  rw [show q + 1 - d = q + 2 - d.succ by omega]

theorem card_labeling_eq_trace_icc (k q : ℕ) :
    Fintype.card (Labeling k q) = ∑ m ∈ Finset.Icc 1 (q + 1),
      (q + 2 - m) * (Polygon.Cert.transfer m ^ (k + 1)).trace :=
  (card_labeling_eq_trace k q).trans (sum_widths q (fun m ↦ (Polygon.Cert.transfer m ^ _).trace))

theorem card_labeling_eq_traceCount_icc (k q : ℕ) :
    Fintype.card (Labeling k q) = ∑ m ∈ Finset.Icc 1 (q + 1),
      (q + 2 - m) * Polygon.Cert.traceCount (k + 1) m :=
  (card_labeling_eq_traceCount k q).trans (sum_widths q (Polygon.Cert.traceCount (k + 1)))

#print axioms trace_pow_cycle
#print axioms card_coloring
#print axioms widthEquiv
#print axioms card_labeling_eq_trace
#print axioms card_labeling_eq_traceCount
#print axioms card_labeling_eq_trace_icc
#print axioms card_labeling_eq_traceCount_icc

end Polygon.Tally
