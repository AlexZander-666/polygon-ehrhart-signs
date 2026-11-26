import Mathlib

/-! Exact extraction of the ordinary linear coefficient from values at 0,...,28. -/
namespace Polygon.Cert
open Polynomial

def slopeWeight (i : Fin 29) : ℚ :=
  if i.val = 0 then -∑ j : Fin 28, (1 : ℚ)/(j.val+1)
  else (-1 : ℚ)^(i.val+1) * Nat.choose 28 i.val / i.val

private theorem slope_moments : ∀ k : Fin 29,
    ∑ i : Fin 29, slopeWeight i * (i.val : ℚ)^k.val = if k.val = 1 then 1 else 0 := by
  decide +kernel

/-- The identity follows by linearity from 29 checked monomial moments. -/
theorem extract_linear (p : ℚ[X]) (hd : p.natDegree ≤ 28) :
    ∑ i : Fin 29, slopeWeight i * p.eval (i.val : ℚ) = p.coeff 1 := by
  have he (i : Fin 29) : p.eval (i.val : ℚ) =
      ∑ k : Fin 29, p.coeff k.val * (i.val : ℚ)^k.val := by
    rw [Polynomial.eval_eq_sum_range' (n := 29) (by omega),
      Fin.sum_univ_eq_sum_range (fun k ↦ p.coeff k * (i.val : ℚ)^k)]
  simp_rw [he, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_left_comm (slopeWeight _) (p.coeff _), ← Finset.mul_sum, slope_moments]
  have h1 (k : Fin 29) : k.val = 1 ↔ k = 1 :=
    ⟨fun h ↦ Fin.ext h, fun h ↦ h ▸ rfl⟩
  simp [h1]

#print axioms extract_linear
end Polygon.Cert
