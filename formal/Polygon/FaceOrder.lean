import Polygon.Lattice
import Polygon.Tally

/-! The cycle incidence presentation of a polygon's face order. -/

namespace Polygon.FaceOrder

noncomputable section

open Ehrhart Tally

/-- The empty face, the vertices, the edges, and the polygon. Edge `i`
has endpoints `i` and `i+1`, with indexing in the cyclic type. -/
inductive Face (k : ℕ)
  | bottom
  | vertex (i : Fin (k + 1))
  | edge (i : Fin (k + 1))
  | top
  deriving DecidableEq, Fintype

def faceLE {k : ℕ} : Face k → Face k → Prop
  | .bottom, _ => True
  | _, .top => True
  | .vertex i, .vertex j => i = j
  | .edge i, .edge j => i = j
  | .vertex i, .edge j => i = j ∨ i = j + 1
  | _, _ => False

instance (k : ℕ) : DecidableRel (@faceLE k) := fun a b ↦ by
  cases a <;> cases b <;> simp only [faceLE] <;> infer_instance

instance (k : ℕ) : PartialOrder (Face k) where
  le := faceLE
  le_refl a := by cases a <;> simp [faceLE]
  le_trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;> simp_all [faceLE]
  le_antisymm a b hab hba := by
    cases a <;> cases b <;> simp_all [faceLE]

theorem le_iff_faceLE {k : ℕ} (a b : Face k) : a ≤ b ↔ faceLE a b := Iff.rfl

instance {k : ℕ} (a b : Face k) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (faceLE a b))

@[simp] theorem vertex_le_edge_iff {k : ℕ} (i j : Fin (k + 1)) :
    Face.vertex i ≤ Face.edge j ↔ i = j ∨ i = j + 1 := Iff.rfl

private def faceEquiv (k : ℕ) : Face k ≃ Option (Option (Fin (k + 1) ⊕ Fin (k + 1))) where
  toFun
    | .bottom => none
    | .vertex i => some (some (.inl i))
    | .edge i => some (some (.inr i))
    | .top => some none
  invFun
    | none => .bottom
    | some (some (.inl i)) => .vertex i
    | some (some (.inr i)) => .edge i
    | some none => .top
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with _ | (_ | (_ | _)) <;> rfl

theorem card_face (k : ℕ) : Fintype.card (Face k) = 2 * (k + 1) + 2 := by
  rw [Fintype.card_congr (faceEquiv k)]
  simp
  omega

private def toLabeling {k q : ℕ} (f : Labels (@faceLE k) (q + 1)) : Labeling k q where
  lo := f.val .bottom
  hi := f.val .top
  vertex i := f.val (.vertex i)
  edge i := f.val (.edge i)
  lo_le_hi := f.property _ _ trivial
  lo_le_vertex i := f.property .bottom (.vertex i) trivial
  vertex_le_edge i := f.property (.vertex i) (.edge i) (Or.inl rfl)
  next_le_edge i := f.property (.vertex (i + 1)) (.edge i) (Or.inr rfl)
  edge_le_hi i := f.property (.edge i) .top trivial

private def ofLabeling {k q : ℕ} (f : Labeling k q) : Labels (@faceLE k) (q + 1) := by
  let lab : Face k → Fin (q + 1)
    | .bottom => f.lo
    | .top => f.hi
    | .vertex i => f.vertex i
    | .edge i => f.edge i
  refine ⟨lab, ?_⟩
  intro a b hab
  have hlo (i) : f.lo ≤ f.edge i := (f.lo_le_vertex i).trans (f.vertex_le_edge i)
  have hhi (i) : f.vertex i ≤ f.hi := (f.vertex_le_edge i).trans (f.edge_le_hi i)
  cases a <;> cases b <;>
    simp_all [faceLE, lab, f.lo_le_hi, f.lo_le_vertex, f.edge_le_hi]
  rcases hab with rfl | rfl
  · exact f.vertex_le_edge _
  · exact f.next_le_edge _

/-- Restrict an order-preserving assignment to each of the four kinds of faces. -/
def labelsEquivLabeling (k q : ℕ) : Labels (@faceLE k) (q + 1) ≃ Labeling k q where
  toFun := toLabeling
  invFun := ofLabeling
  left_inv f := by
    apply Subtype.ext
    funext a
    cases a <;> rfl
  right_inv f := by cases f; rfl

def latticePointsEquivLabeling (k q : ℕ) : LatticePoints (@faceLE k) q ≃ Labeling k q :=
  (latticePointsEquivLabels (@faceLE k) q).trans (labelsEquivLabeling k q)

theorem card_latticePoints_eq_labeling (k q : ℕ) :
    Fintype.card (LatticePoints (@faceLE k) q) = Fintype.card (Labeling k q) :=
  Fintype.card_congr (latticePointsEquivLabeling k q)

def ehrhartPolynomial (k : ℕ) : Polynomial ℚ := orderPolynomial (@faceLE k)

theorem natDegree_ehrhartPolynomial_le (k : ℕ) :
    (ehrhartPolynomial k).natDegree ≤ 2 * (k + 1) + 2 := by
  rw [← card_face k]
  exact natDegree_orderPolynomial_le _

theorem eval_ehrhartPolynomial (k q : ℕ) :
    (ehrhartPolynomial k).eval (q : ℚ) = (Fintype.card (Labeling k q) : ℚ) := by
  rw [ehrhartPolynomial, eval_orderPolynomial, Fintype.card_congr (labelsEquivLabeling k q)]

theorem eval_ehrhartPolynomial_eq_latticePoints (k q : ℕ) :
    (ehrhartPolynomial k).eval (q : ℚ) = (Fintype.card (LatticePoints (@faceLE k) q) : ℚ) :=
  eval_orderPolynomial_eq_latticePoints _ q

end
end Polygon.FaceOrder
