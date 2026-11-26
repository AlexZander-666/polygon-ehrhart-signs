import Mathlib

/-! The crown transfer matrix and an integer implementation of its trace. -/
namespace Polygon.Cert

def transfer (m : ℕ) : Matrix (Fin m) (Fin m) ℕ :=
  fun i j ↦ m - max i.val j.val

private def step {m : ℕ} (v : Vector ℕ m) : Vector ℕ m :=
  Vector.ofFn fun j ↦ (List.ofFn fun i : Fin m ↦ v[i.val] * transfer m i j).sum

private def row {m : ℕ} (i : Fin m) : ℕ → Vector ℕ m
  | 0 => Vector.ofFn fun j ↦ if i = j then 1 else 0
  | k+1 => step (row i k)

private theorem row_correct {m : ℕ} (i j : Fin m) (k : ℕ) :
    (row i k)[j.val] = (transfer m ^ k) i j := by
  induction k generalizing j with
  | zero => simp [row, Matrix.one_apply]
  | succ k ih =>
    simp only [row, step, Vector.getElem_ofFn, Fin.eta, List.sum_ofFn, pow_succ, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ ↦ congrArg (· * transfer m a j) (ih a)

def traceCount (n m : ℕ) : ℕ :=
  (List.ofFn fun i : Fin m ↦ (row i n)[i.val]).sum

theorem traceCount_correct (n m : ℕ) : traceCount n m = (transfer m ^ n).trace := by
  simp [traceCount, List.sum_ofFn, Matrix.trace, Matrix.diag, row_correct]

end Polygon.Cert
