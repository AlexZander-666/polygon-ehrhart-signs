import Polygon.BinomialTrace
import Polygon.SmallPolynomial

/-! Executable Newton sums for the actual integer crown transfer matrix. -/
namespace Polygon.NewtonExecutor

open Finset

/-- A factorial-quotient implementation avoids Pascal-tree reduction in the kernel. -/
def chooseFast (n k : ℕ) : ℕ :=
  if k ≤ n then n.factorial / (k.factorial * (n - k).factorial) else 0

theorem chooseFast_eq (n k : ℕ) : chooseFast n k = n.choose k := by
  unfold chooseFast
  split
  · exact (Nat.choose_eq_factorial_div_factorial ‹_›).symm
  · exact (Nat.choose_eq_zero_of_lt (by omega)).symm

def signed (m k : ℕ) : ℤ := (-1 : ℤ) ^ k * (m + k).choose (2 * k)

def signedFast (m k : ℕ) : ℤ := (-1 : ℤ) ^ k * chooseFast (m + k) (2 * k)

def coefficientRow (m cap : ℕ) : List ℤ :=
  (List.range (cap + 1)).map (signedFast m)

private theorem coefficientRow_get (m cap i : ℕ) (hi : i ≤ cap) :
    (coefficientRow m cap).getD i 0 = signed m i := by
  have h : i < (coefficientRow m cap).length := by simpa [coefficientRow] using Nat.lt_succ_of_le hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  simp [coefficientRow, signedFast, signed, chooseFast_eq]

/-- Dot product of two prefixes. Each integer is consumed once. -/
def prefixDot : ℕ → List ℤ → List ℤ → ℤ
  | 0, _, _ => 0
  | k + 1, a, b => a.getD 0 0 * b.getD 0 0 + prefixDot k a.tail b.tail

private theorem getD_tail (l : List ℤ) (i : ℕ) : l.tail.getD i 0 = l.getD (i + 1) 0 := by
  cases l <;> rfl

private theorem prefixDot_eq (k : ℕ) (a b : List ℤ) :
    prefixDot k a b = ∑ i ∈ range k, a.getD i 0 * b.getD i 0 := by
  induction k generalizing a b with
  | zero => simp [prefixDot]
  | succ k ih =>
    rw [prefixDot, ih, Finset.sum_range_succ']
    simp only [getD_tail]
    exact add_comm _ _

/-- The trace history is stored newest first. The last entry is always the width,
the trace of the zeroth matrix power. -/
def history (m : ℕ) (a : List ℤ) : ℕ → List ℤ
  | 0 => [m]
  | k + 1 =>
    let previous := history m a k
    (- (k + 1 : ℕ) * a.getD (k + 1) 0 - prefixDot k a.tail previous) :: previous

private theorem trace_zero (m : ℕ) : Cert.traceCount 0 m = m := by
  rw [Cert.traceCount_correct, pow_zero]
  simp [Matrix.trace, Matrix.diag]

private theorem trace_succ_sum (m n : ℕ) :
    (Cert.traceCount (n + 1) m : ℤ) =
      - (n + 1 : ℕ) * signed m (n + 1) -
      ∑ i ∈ range n, signed m (i + 1) * (Cert.traceCount (n - i) m : ℤ) := by
  have h := BinomialTrace.trace_integer m (n + 1) (by omega)
  rw [Finset.sum_filter, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ', Finset.sum_range_succ] at h
  have hsum :
      (∑ i ∈ range n, if (i + 1, n + 1 - (i + 1)).1 ∈ Set.Ioo 0 (n + 1)
        then (-1 : ℤ) ^ (i + 1) * (Nat.choose (m + (i + 1)) (2 * (i + 1)) : ℤ) *
          (Cert.traceCount (n + 1 - (i + 1)) m : ℤ) else 0) =
      ∑ i ∈ range n, signed m (i + 1) * (Cert.traceCount (n - i) m : ℤ) := by
    apply sum_congr rfl
    intro i hi
    have mid : (i + 1) ∈ Set.Ioo 0 (n + 1) := ⟨by omega, by have := mem_range.mp hi; omega⟩
    simp [mid, signed, Nat.add_sub_add_right]
  rw [hsum] at h
  have bound : ¬ n + 1 ∈ Set.Ioo 0 (n + 1) := by simp
  simp only [bound, if_false, Set.mem_Ioo, lt_irrefl, false_and, add_zero] at h
  rw [h]
  simp only [signed, pow_succ, Int.natCast_succ]
  ring

theorem history_get (m cap n i : ℕ) (hn : n ≤ cap) (hi : i ≤ n) :
    (history m (coefficientRow m cap) n).getD i 0 = (Cert.traceCount (n - i) m : ℤ) := by
  induction n generalizing i with
  | zero =>
    have : i = 0 := by omega
    subst i
    simp [history, trace_zero]
  | succ n ih =>
    cases i with
    | zero =>
      simp only [history, List.getD_cons_zero, Nat.sub_zero]
      rw [trace_succ_sum, prefixDot_eq, coefficientRow_get _ _ _ hn]
      congr 1
      apply sum_congr rfl
      intro i hi
      have il := mem_range.mp hi
      rw [getD_tail, coefficientRow_get _ _ _ (by omega), ih i (by omega) (by omega)]
    | succ i =>
      simp only [history, List.getD_cons_succ, Nat.add_sub_add_right]
      exact ih i (by omega) (by omega)

def trace (n m : ℕ) : ℤ :=
  (history m (coefficientRow m n) n).getD 0 0

/-- The executable integer calculation returns the original matrix trace at every width. -/
theorem trace_correct (n m : ℕ) : trace n m = (Cert.traceCount n m : ℤ) := by
  simpa [trace] using history_get m n n 0 le_rfl (Nat.zero_le n)

#print axioms chooseFast_eq
#print axioms trace_succ_sum
#print axioms history_get
#print axioms trace_correct

end Polygon.NewtonExecutor
