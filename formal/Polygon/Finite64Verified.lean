import Polygon.GeneralRealization
import Polygon.Finite64.N03
import Polygon.Finite64.N04
import Polygon.Finite64.N05
import Polygon.Finite64.N06
import Polygon.Finite64.N07
import Polygon.Finite64.N08
import Polygon.Finite64.N09
import Polygon.Finite64.N10
import Polygon.Finite64.N11
import Polygon.Finite64.N12
import Polygon.Finite64.N13
import Polygon.Finite64.N14
import Polygon.Finite64.N15
import Polygon.Finite64.N16
import Polygon.Finite64.N17
import Polygon.Finite64.N18
import Polygon.Finite64.N19
import Polygon.Finite64.N20
import Polygon.Finite64.N21
import Polygon.Finite64.N22
import Polygon.Finite64.N23
import Polygon.Finite64.N24
import Polygon.Finite64.N25
import Polygon.Finite64.N26
import Polygon.Finite64.N27
import Polygon.Finite64.N28
import Polygon.Finite64.N29
import Polygon.Finite64.N30
import Polygon.Finite64.N31
import Polygon.Finite64.N32
import Polygon.Finite64.N33
import Polygon.Finite64.N34
import Polygon.Finite64.N35
import Polygon.Finite64.N36
import Polygon.Finite64.N37
import Polygon.Finite64.N38
import Polygon.Finite64.N39
import Polygon.Finite64.N40
import Polygon.Finite64.N41
import Polygon.Finite64.N42
import Polygon.Finite64.N43
import Polygon.Finite64.N44
import Polygon.Finite64.N45
import Polygon.Finite64.N46
import Polygon.Finite64.N47
import Polygon.Finite64.N48
import Polygon.Finite64.N49
import Polygon.Finite64.N50
import Polygon.Finite64.N51
import Polygon.Finite64.N52
import Polygon.Finite64.N53
import Polygon.Finite64.N54
import Polygon.Finite64.N55
import Polygon.Finite64.N56
import Polygon.Finite64.N57
import Polygon.Finite64.N58
import Polygon.Finite64.N59
import Polygon.Finite64.N60
import Polygon.Finite64.N61
import Polygon.Finite64.N62
import Polygon.Finite64.N63
import Polygon.Finite64.N64

/-! Full coefficient classifications for the complete geometric face lattices
at all 62 side counts from three through sixty-four. -/
namespace Polygon.Finite64

open NewtonInterpolant

set_option maxHeartbeats 1000000 in
private theorem indexed (i : Fin 62) (j : ℕ) (hj : j ≤ 2 * (i.val + 3) + 2) :
    (((FaceOrder.ehrhartPolynomial (i.val + 3 - 1)).coeff j < 0) ↔
      negativeIndex (i.val + 3) j) ∧
    (FaceOrder.ehrhartPolynomial (i.val + 3 - 1)).coeff j ≠ 0 := by
  fin_cases i
  · exact N03.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 8 from hj)⟩
  · exact N04.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 10 from hj)⟩
  · exact N05.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 12 from hj)⟩
  · exact N06.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 14 from hj)⟩
  · exact N07.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 16 from hj)⟩
  · exact N08.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 18 from hj)⟩
  · exact N09.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 20 from hj)⟩
  · exact N10.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 22 from hj)⟩
  · exact N11.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 24 from hj)⟩
  · exact N12.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 26 from hj)⟩
  · exact N13.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 28 from hj)⟩
  · exact N14.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 30 from hj)⟩
  · exact N15.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 32 from hj)⟩
  · exact N16.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 34 from hj)⟩
  · exact N17.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 36 from hj)⟩
  · exact N18.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 38 from hj)⟩
  · exact N19.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 40 from hj)⟩
  · exact N20.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 42 from hj)⟩
  · exact N21.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 44 from hj)⟩
  · exact N22.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 46 from hj)⟩
  · exact N23.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 48 from hj)⟩
  · exact N24.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 50 from hj)⟩
  · exact N25.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 52 from hj)⟩
  · exact N26.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 54 from hj)⟩
  · exact N27.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 56 from hj)⟩
  · exact N28.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 58 from hj)⟩
  · exact N29.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 60 from hj)⟩
  · exact N30.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 62 from hj)⟩
  · exact N31.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 64 from hj)⟩
  · exact N32.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 66 from hj)⟩
  · exact N33.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 68 from hj)⟩
  · exact N34.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 70 from hj)⟩
  · exact N35.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 72 from hj)⟩
  · exact N36.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 74 from hj)⟩
  · exact N37.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 76 from hj)⟩
  · exact N38.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 78 from hj)⟩
  · exact N39.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 80 from hj)⟩
  · exact N40.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 82 from hj)⟩
  · exact N41.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 84 from hj)⟩
  · exact N42.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 86 from hj)⟩
  · exact N43.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 88 from hj)⟩
  · exact N44.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 90 from hj)⟩
  · exact N45.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 92 from hj)⟩
  · exact N46.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 94 from hj)⟩
  · exact N47.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 96 from hj)⟩
  · exact N48.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 98 from hj)⟩
  · exact N49.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 100 from hj)⟩
  · exact N50.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 102 from hj)⟩
  · exact N51.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 104 from hj)⟩
  · exact N52.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 106 from hj)⟩
  · exact N53.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 108 from hj)⟩
  · exact N54.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 110 from hj)⟩
  · exact N55.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 112 from hj)⟩
  · exact N56.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 114 from hj)⟩
  · exact N57.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 116 from hj)⟩
  · exact N58.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 118 from hj)⟩
  · exact N59.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 120 from hj)⟩
  · exact N60.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 122 from hj)⟩
  · exact N61.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 124 from hj)⟩
  · exact N62.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 126 from hj)⟩
  · exact N63.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 128 from hj)⟩
  · exact N64.signs ⟨j, Nat.lt_succ_of_le (show j ≤ 130 from hj)⟩

/-- Ordinary power coefficients through the actual dimension, for every
geometric polygon with three to sixty-four sides in the realization family. -/
theorem geometric_signs (n j : ℕ) (lo : 3 ≤ n) (hi : n ≤ 64) (hj : j ≤ 2 * n + 2) :
    let E := GeneralRealization.geometricEhrhart (n - 3)
    (E.coeff j < 0 ↔ negativeIndex n j) ∧ E.coeff j ≠ 0 := by
  dsimp only
  rw [GeneralRealization.ehrhart_by_sides lo]
  let i : Fin 62 := ⟨n - 3, by omega⟩
  have hn : i.val + 3 = n := by dsimp [i]; omega
  simpa only [hn] using indexed i j (by rw [hn]; exact hj)

/-- The negative-degree criterion holds without a separate restriction on
the coefficient index. Ordinary coefficients above the dimension are zero. -/
theorem geometric_negative_iff (n j : ℕ) (lo : 3 ≤ n) (hi : n ≤ 64) :
    (GeneralRealization.geometricEhrhart (n - 3)).coeff j < 0 ↔ negativeIndex n j := by
  by_cases hj : j ≤ 2 * n + 2
  · exact (geometric_signs n j lo hi hj).1
  · rw [GeneralRealization.ehrhart_by_sides lo]
    have hz : (FaceOrder.ehrhartPolynomial (n - 1)).coeff j = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have bound := FaceOrder.natDegree_ehrhartPolynomial_le (n - 1)
      omega
    have neg : ¬ negativeIndex n j := by unfold negativeIndex; omega
    simp [hz, neg]

#print axioms geometric_signs
#print axioms geometric_negative_iff

end Polygon.Finite64
