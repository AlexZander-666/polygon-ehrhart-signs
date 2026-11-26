import Polygon.FaceOrder

/-! Vertex-set inclusion for every cyclic incidence poset of a polygon with at least three vertices. -/
namespace Polygon.GeneralRealization
open FaceOrder

variable {n : ℕ}
abbrev Index (n : ℕ) := Fin (n+3)
abbrev Code (n : ℕ) := Face (n+2)

def vertices : Code n → Finset (Index n)
  | .bottom => ∅
  | .vertex i => {i}
  | .edge i => {i,i+1}
  | .top => Finset.univ

private theorem next_ne (i : Index n) : i+1 ≠ i := by
  simp

private theorem next_next_ne (i : Index n) : i+1+1 ≠ i := by
  intro h
  have hz : (1:Index n)+1=0 := add_left_cancel (a:=i) (by simpa [← add_assoc] using h)
  have he := congrArg Fin.val hz
  rw [Fin.val_add,Fin.val_one,Fin.val_zero,Nat.mod_eq_of_lt (by omega)] at he
  omega

private theorem edges_subset (i j : Index n) :
    ({i,i+1} : Finset _) ⊆ {j,j+1} ↔ i=j := by
  constructor
  · intro h
    have hi := h (Finset.mem_insert_self i {i+1})
    have hs := h (show i+1 ∈ ({i,i+1} : Finset _) by simp)
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi hs
    obtain rfl | h' := hi
    · rfl
    · subst i
      exact ((hs.elim (next_next_ne j) (next_ne (j+1)))).elim
  · rintro rfl
    exact fun _ hi ↦ hi

theorem vertices_subset_iff {c d : Code n} : vertices c ⊆ vertices d ↔ c ≤ d := by
  rw [le_iff_faceLE]
  have pair_card (i : Index n) : ({i,i+1} : Finset _).card = 2 :=
    Finset.card_pair (next_ne i).symm
  cases c <;> cases d <;> simp [vertices,faceLE,edges_subset,Finset.singleton_subset_iff]
  all_goals first
    | rename_i i j; exact fun h ↦ next_ne i (by grind)
    | (try constructor) <;> intro h <;> have he := congrArg Finset.card h <;>
        simp only [pair_card,Finset.card_univ,Fintype.card_fin,Finset.card_empty,Finset.card_singleton] at he <;> omega

end Polygon.GeneralRealization
