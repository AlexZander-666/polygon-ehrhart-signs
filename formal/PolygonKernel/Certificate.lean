import PolygonKernel.Data
import PolygonKernel.SeriesBridge
import Mathlib.Tactic.FinCases

/-! Kernel checks for all 96 rational rows and both ratios. -/
namespace PolygonKernel

def NegativeIndex (d : ℕ) : Prop := 27 ≤ d ∧ (d % 4 = 0 ∨ d % 4 = 3)

def entry (d : ℕ) : ℚ := table.getD d 0

def CheckedAt (d : ℕ) : Prop :=
  Agreement table d ∧
  entry d ≠ 0 ∧
  (entry d < 0 ↔ NegativeIndex d) ∧
  (2 ≤ d → |entry (d - 2)| ≤ 108 * |entry d|) ∧
  (27 ≤ d → |entry (d - 2)| ≤ 28 * |entry d|)

instance (d : ℕ) : Decidable (CheckedAt d) := by
  unfold CheckedAt NegativeIndex
  infer_instance

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem checked_table (d : Fin 96) : CheckedAt d.val := by
  fin_cases d <;> decide +kernel

theorem entry_eq_g (d : ℕ) (hd : d ≤ 95) : entry d = g d := by
  symm
  apply g_eq_of_agreement table 95 _ d hd
  intro k hk
  exact (checked_table ⟨k, by omega⟩).1

/-- The four checked inequalities and sign assertions about the formal kernel
at every degree in the finite range. -/
theorem finite_kernel (d : ℕ) (hd : d ≤ 95) :
    g d ≠ 0 ∧
    (g d < 0 ↔ NegativeIndex d) ∧
    (2 ≤ d → |g (d - 2)| ≤ 108 * |g d|) ∧
    (27 ≤ d → |g (d - 2)| ≤ 28 * |g d|) := by
  have h := (checked_table ⟨d, by omega⟩).2
  rw [entry_eq_g d hd, entry_eq_g (d - 2) (by omega)] at h
  exact h

/-- A readout stated directly for the power series satisfying the normalized
sinh identity. This links the checked rational table to the kernel in the paper. -/
theorem finite_kernel_of_formalSinh {G : PowerSeries ℚ}
    (h : G * formalSinh ^ 2 = PowerSeries.X ^ 2 * PowerSeries.rescale (5 : ℚ) (PowerSeries.exp ℚ))
    (d : ℕ) (hd : d ≤ 95) :
    PowerSeries.coeff d G ≠ 0 ∧
      (PowerSeries.coeff d G < 0 ↔ NegativeIndex d) ∧
      (2 ≤ d → |PowerSeries.coeff (d - 2) G| ≤ 108 * |PowerSeries.coeff d G|) ∧
      (27 ≤ d → |PowerSeries.coeff (d - 2) G| ≤ 28 * |PowerSeries.coeff d G|) := by
  rw [F_eq_of_formalSinh h]
  exact finite_kernel d hd

#print axioms checked_table
#print axioms entry_eq_g
#print axioms finite_kernel
#print axioms finite_kernel_of_formalSinh

end PolygonKernel
