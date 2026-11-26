import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Formal power series and the rational convolution of the polygon kernel. -/
namespace PolygonKernel

open Finset PowerSeries
open scoped PowerSeries

/-- Coefficients of the square of the formal normalized hyperbolic sine. -/
def hCoeff (d : ℕ) : ℚ :=
  if d % 2 = 0 then (2 : ℚ) ^ (d + 1) / (d + 2).factorial else 0

/-- Coefficients of the exponential at scale five. -/
def eCoeff (d : ℕ) : ℚ := (5 : ℚ) ^ d / d.factorial

def H : ℚ⟦X⟧ := PowerSeries.mk hCoeff

noncomputable def F : ℚ⟦X⟧ := rescale (5 : ℚ) (exp ℚ) * H⁻¹

noncomputable def g (d : ℕ) : ℚ := coeff d F

@[simp] theorem hCoeff_zero : hCoeff 0 = 1 := by norm_num [hCoeff, Nat.factorial]

private theorem H_constant : constantCoeff H = 1 := by
  rw [← coeff_zero_eq_constantCoeff]
  simp [H]

theorem H_mul_F : H * F = rescale (5 : ℚ) (exp ℚ) := by
  unfold F
  rw [← mul_left_comm, PowerSeries.mul_inv_cancel H (by simp [H_constant]), mul_one]

/-- Any candidate coefficient table can be compared to the exact rational
convolution using a finite, executable list sum. -/
def convolution (row : List ℚ) (d : ℕ) : ℚ :=
  ((List.range d).map fun i ↦ hCoeff (i + 1) * row.getD (d - (i + 1)) 0).sum

def Agreement (row : List ℚ) (d : ℕ) : Prop :=
  row.getD d 0 + convolution row d = eCoeff d

instance (row : List ℚ) (d : ℕ) : Decidable (Agreement row d) :=
  inferInstanceAs (Decidable (_ = _))

theorem recurrence (d : ℕ) :
    g d + ∑ i ∈ range d, hCoeff (i + 1) * g (d - (i + 1)) = eCoeff d := by
  have h := congrArg (coeff d) H_mul_F
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ'] at h
  simpa [H, g, eCoeff, coeff_rescale, div_eq_mul_inv, add_comm, mul_comm] using h

private theorem sum_list_range (f : ℕ → ℚ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- A complete initial segment of exact convolution checks determines the actual
coefficients of the formal generating function. -/
theorem g_eq_of_agreement (row : List ℚ) (n : ℕ)
    (checked : ∀ d ≤ n, Agreement row d) :
    ∀ d ≤ n, g d = row.getD d 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    have fromF := recurrence d
    have fromTable := checked d hd
    unfold Agreement convolution at fromTable
    rw [sum_list_range] at fromTable
    have matching : (∑ i ∈ range d, hCoeff (i + 1) * g (d - (i + 1))) =
        ∑ i ∈ range d, hCoeff (i + 1) * row.getD (d - (i + 1)) 0 := by
      apply sum_congr rfl
      intro i hi
      have hlt : d - (i + 1) < d := by
        have := mem_range.mp hi
        omega
      rw [ih _ hlt (hlt.le.trans hd)]
    rw [matching, ← fromTable] at fromF
    exact add_right_cancel fromF

#print axioms H_mul_F
#print axioms recurrence
#print axioms g_eq_of_agreement

end PolygonKernel
