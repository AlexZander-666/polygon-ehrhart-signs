import Polygon.TransferDeterminant
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Closed binomial coefficients of the determinant for the actual crown transfer. -/
namespace Polygon.BinomialContinuant

open Polynomial TransferDeterminant
noncomputable section

/-- Polynomial whose value is the transfer determinant with positive parameter. -/
def positive : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | m+2 => (C 2 + X) * positive (m+1) - positive m

theorem determinant_eval (m : ℕ) (z : ℝ) :
    (positive m).eval z = characteristic m (-z) := by
  induction m using Nat.twoStepInduction with
  | zero => simp [positive, characteristic, Matrix.det_isEmpty]
  | one =>
    simp [positive, characteristic_eq_band, Matrix.det_unique, band]
  | more m ih jh =>
    rw [positive, recurrence]
    simp [ih, jh]

private theorem second_pascal (a b : ℕ) :
    (a+2).choose (b+2) + a.choose (b+2) =
      2 * (a+1).choose (b+2) + a.choose b := by
  rw [Nat.choose_succ_succ' (a+1) (b+1), Nat.choose_succ_succ' a b,
    Nat.choose_succ_succ' a (b+1)]
  norm_num only [Nat.add_assoc, Nat.reduceAdd]
  omega

/-- Every coefficient is a single binomial integer, including coefficients beyond the width. -/
theorem coefficient (m k : ℕ) :
    (positive m).coeff k = (Nat.choose (m+k) (2*k) : ℝ) := by
  induction m using Nat.twoStepInduction generalizing k with
  | zero =>
    cases k with
    | zero => simp [positive]
    | succ k =>
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp [positive, coeff_one]
  | one =>
    rcases k with _|k
    · simp [positive]
    rcases k with _|k
    · norm_num [positive, coeff_one]
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp [positive, coeff_one, coeff_X]
  | more m ih jh =>
    cases k with
    | zero =>
      simp [positive, add_mul, ih, jh]
      norm_num
    | succ t =>
      rw [positive, add_mul, coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul, ih, jh, jh]
      have hp := second_pascal (m+t+1) (2*t)
      have hr : ((((m+t+1)+2).choose (2*t+2) + (m+t+1).choose (2*t+2) : ℕ) : ℝ) =
          ((2*((m+t+1)+1).choose (2*t+2) + (m+t+1).choose (2*t) : ℕ) : ℝ) := by exact_mod_cast hp
      push_cast at hr
      rw [show m+2+(t+1) = m+t+1+2 by omega,
        show m+1+(t+1) = m+t+1+1 by omega,
        show m+(t+1) = m+t+1 by omega,
        show m+1+t = m+t+1 by omega,
        show 2*(t+1) = 2*t+2 by omega]
      linarith only [hr]


private theorem eval_charpolyRev_at (m : ℕ) (z : ℝ) :
    (((Cert.transfer m).map (Nat.cast : ℕ → ℝ)).charpolyRev).eval z = characteristic m z := by
  let A := (Cert.transfer m).map (Nat.cast : ℕ → ℝ)
  change A.charpolyRev.eval z = (1 - z • A).det
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  rcases eq_or_ne i j with h|h <;>
    simp [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, h] <;> apply mul_comm

/-- The reverse characteristic polynomial of the actual transfer, with its original sign. -/
theorem reverse_coeff (m k : ℕ) :
    (((Cert.transfer m).map (Nat.cast : ℕ → ℝ)).charpolyRev).coeff k =
      (-1 : ℝ)^k * (Nat.choose (m+k) (2*k) : ℝ) := by
  have eqn : ((Cert.transfer m).map (Nat.cast : ℕ → ℝ)).charpolyRev =
      (positive m).comp (C (-1) * X) := by
    apply Polynomial.funext
    intro z
    simp [eval_charpolyRev_at, determinant_eval]
  rw [eqn, comp_C_mul_X_coeff, coefficient, mul_comm]

#print axioms reverse_coeff

#print axioms determinant_eval
#print axioms coefficient
end
end Polygon.BinomialContinuant
