import Polygon.Tally
import Polygon.TraceTable
import Polygon.Interpolation

/-! The negative ordinary coefficient, checked against actual weak face labelings. -/
namespace Polygon.Cert
open Polynomial

def observation (q : ℕ) : ℕ :=
  ∑ d : Fin (q+1), (q+1-d.val) * traceValue d.val

theorem count13_at (q : Fin 29) :
    Fintype.card (Tally.Labeling 12 q.val) = observation q.val := by
  rw [Tally.card_labeling_eq_traceCount, observation]
  apply Finset.sum_congr rfl
  intro d _
  have hd : d.val < 29 := by omega
  rw [checked_trace ⟨d.val,hd⟩]

private theorem weighted_observations :
    ∑ j : Fin 29, slopeWeight j * (observation j.val : ℚ) = -298495711/35302608 := by
  decide +kernel

/-- Any rational polynomial of degree at most 28 that counts weak labelings
of all faces of the 13-gon on these integer inputs has this exact linear coefficient. -/
theorem slope13 (p : ℚ[X]) (hd : p.natDegree ≤ 28)
    (hcount : ∀ q : Fin 29, p.eval (q.val : ℚ) = (Fintype.card (Tally.Labeling 12 q.val) : ℚ)) :
    p.coeff 1 = -298495711/35302608 := by
  rw [← extract_linear p hd]
  simp_rw [hcount, count13_at]
  exact weighted_observations

#print axioms count13_at
#print axioms slope13
end Polygon.Cert
