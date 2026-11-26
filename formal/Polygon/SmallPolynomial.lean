import Polygon.FaceOrder

/-! A monomial coefficient table checked against all necessary dilate counts. -/
namespace Polygon.Small
open Polynomial

noncomputable def fromCoeffs : List ℚ → ℚ[X]
  | [] => 0
  | a::l => C a + X * fromCoeffs l

def horner (x : ℚ) : List ℚ → ℚ
  | [] => 0
  | a::l => a + x * horner x l

theorem eval_fromCoeffs (l : List ℚ) (x : ℚ) : (fromCoeffs l).eval x = horner x l := by
  induction l with
  | nil => simp [fromCoeffs, horner]
  | cons a l ih => simp [fromCoeffs, horner, ih]

theorem coeff_fromCoeffs (l : List ℚ) (j : ℕ) : (fromCoeffs l).coeff j = l.getD j 0 := by
  induction l generalizing j with
  | nil => simp [fromCoeffs]
  | cons a l ih =>
    cases j with
    | zero => simp [fromCoeffs]
    | succ j => simp [fromCoeffs, coeff_X_mul, ih]

theorem degree_fromCoeffs_lt (l : List ℚ) : (fromCoeffs l).degree < (l.length : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro j hj
  rw [coeff_fromCoeffs]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by exact_mod_cast hj : l.length ≤ j)]

/-- Both polynomial sides are determined by the indicated integer arguments. -/
theorem check_table (k : ℕ) (l : List ℚ) (len : l.length = 2*(k+1)+3)
    (h : ∀ j : Fin (2*(k+1)+3), horner (j.val : ℚ) l = (Fintype.card (Tally.Labeling k j.val) : ℚ)) :
    FaceOrder.ehrhartPolynomial k = fromCoeffs l := by
  apply eq_of_degrees_lt_of_eval_index_eq (v := fun j : Fin (2*(k+1)+3) => (j.val : ℚ)) Finset.univ
  · intro a _ b _ hab
    apply Fin.ext
    change (a.val : ℚ) = b.val at hab
    exact_mod_cast hab
  · have hd := FaceOrder.natDegree_ehrhartPolynomial_le k
    rw [Finset.card_univ, Fintype.card_fin]
    exact (degree_le_of_natDegree_le hd).trans_lt (by exact_mod_cast Nat.lt_succ_self (2*(k+1)+2))
  · simpa [len] using degree_fromCoeffs_lt l
  · intro i _
    rw [FaceOrder.eval_ehrhartPolynomial, eval_fromCoeffs, h]

def observation (traces : List ℕ) (q : ℕ) : ℕ :=
  ∑ d : Fin (q+1), (q+1-d.val) * traces.getD d.val 0

theorem certify (k : ℕ) (cs : List ℚ) (traces : List ℕ) (len : cs.length = 2*(k+1)+3)
    (ht : ∀ i : Fin (2*(k+1)+3), Cert.traceCount (k+1) (i.val+1) = traces.getD i.val 0)
    (hv : ∀ j : Fin (2*(k+1)+3), horner (j.val : ℚ) cs = (observation traces j.val : ℚ)) :
    FaceOrder.ehrhartPolynomial k = fromCoeffs cs := by
  apply check_table k cs len
  intro j
  rw [hv, Tally.card_labeling_eq_traceCount]
  congr 1
  unfold observation
  apply Finset.sum_congr rfl
  intro d _
  rw [ht ⟨d.val, by omega⟩]

end Polygon.Small
