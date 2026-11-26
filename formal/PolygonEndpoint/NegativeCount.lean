import PolygonEndpoint.AllCoefficients

/-! Exact number of negative ordinary coefficients, including the small polygons. -/
namespace PolygonEndpoint
open Polygon Finset

private def mark (n i : ℕ) : ℕ := if NewtonInterpolant.negativeIndex n (i+1) then 1 else 0

private def negativeCount (n : ℕ) := ∑ i ∈ range (2*n+2), mark n i

private theorem count_step {n : ℕ} (h : 12≤n) : negativeCount (n+1)=negativeCount n+1 := by
  have shift (i : ℕ) : mark (n+1) (i+1+1)=mark n i := by
    have eq : NewtonInterpolant.negativeIndex (n+1) (i+1+1+1) ↔
        NewtonInterpolant.negativeIndex n (i+1) := by unfold NewtonInterpolant.negativeIndex; omega
    simp only [mark,eq]
  have two : mark (n+1) 1 + mark (n+1) 0 = 1 := by
    by_cases a : NewtonInterpolant.negativeIndex (n+1) (1+1) <;>
      by_cases b : NewtonInterpolant.negativeIndex (n+1) (0+1) <;>
        simp only [mark,a,b,if_true,if_false] <;>
          unfold NewtonInterpolant.negativeIndex at a b <;> omega
  unfold negativeCount
  rw [show 2*(n+1)+2=(2*n+2)+1+1 by omega,sum_range_succ',sum_range_succ']
  simp only [shift,Nat.zero_add]
  omega

private theorem count_formula (n : ℕ) : negativeCount n=n-12 := by
  induction n with
  | zero => decide
  | succ n ih =>
    by_cases h : 12≤n
    · rw [count_step h,ih]
      omega
    · have small : negativeCount (n+1)=0 := by
        apply sum_eq_zero
        intro i _
        exact if_neg (by unfold NewtonInterpolant.negativeIndex; omega)
      omega

/-- Among degrees 0 through 2n+2, exactly max(n−12,0) have negative coefficient. -/
theorem negative_count {n : ℕ} (hn : 3≤n) :
    ((range (2*n+3)).filter (fun r ↦ (GeneralRealization.geometricEhrhart (n-3)).coeff r < 0)).card = n-12 := by
  classical
  rw [←count_formula n]
  let neg (r : ℕ) := (GeneralRealization.geometricEhrhart (n-3)).coeff r < 0
  change ((range (2*n+3)).filter neg).card = _
  calc
    _ = ∑ r ∈ range (2*n+3), (if neg r then (1:ℕ) else 0) := (sum_boole neg _).symm
    _ = _ := by
      rw [sum_range_succ']
      have eq (r : ℕ) : neg r ↔ NewtonInterpolant.negativeIndex n r := (geometric_classification hn r).1
      simp only [eq]
      have hz : ¬NewtonInterpolant.negativeIndex n 0 := by simp [NewtonInterpolant.negativeIndex]
      simp only [if_neg hz,add_zero]
      rfl

end PolygonEndpoint
