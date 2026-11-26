import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-! The off-diagonal majorant in the linear and quadratic polygon estimates. -/
namespace Polygon.PoleBound

/-- The explicit majorant indexed by the offset from the diagonal. -/
noncomputable def term (n : ℕ) : ℕ → ℝ
  | 0 => 1
  | r+1 => term n r * (Real.pi ^ 4 / 8) /
      (((r : ℝ) + 1) * (2 * (n : ℝ) - 2 * ((r : ℝ) + 1) + 1))

private lemma fourth_lt : Real.pi ^ 4 < 100 := by
  calc
    Real.pi ^ 4 < (3.15 : ℝ) ^ 4 := by gcongr; exact Real.pi_lt_d2
    _ < 100 := by norm_num

private lemma denominator {n r : ℕ} (hn : 13 ≤ n) (lo : 2 ≤ r) (hi : r < n) :
    36 ≤ (r : ℝ) * (2 * (n : ℝ) - 2 * (r : ℝ) + 1) := by
  have hn' : (13 : ℝ) ≤ n := by exact_mod_cast hn
  have lo' : (2 : ℝ) ≤ r := by exact_mod_cast lo
  have hi' : (r : ℝ) + 1 ≤ n := by exact_mod_cast hi
  nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 1 - r by linarith)
    (show 0 ≤ 2 * (r : ℝ) - 3 by linarith)]


/-- Every off-diagonal term has the same geometric majorant for all n ≥ 13. -/
theorem term_bound (n j : ℕ) (hn : 13 ≤ n) (hj : j + 1 < n) :
    term n (j+1) ≤ (1/2 : ℝ) * (25/72 : ℝ)^j := by
  have hn' : (13 : ℝ) ≤ n := by exact_mod_cast hn
  induction j with
  | zero =>
    simp only [term, Nat.cast_zero, zero_add, one_mul, pow_zero, mul_one]
    apply (div_le_iff₀ (by linarith : 0 < 2 * (n : ℝ) - 2 + 1)).2
    linarith [fourth_lt]
  | succ j ih =>
    have old := ih (by omega)
    have hd := denominator hn (r := j + 2) (by omega) (by omega)
    push_cast at hd
    let d : ℝ := ((j : ℝ) + 1 + 1) * (2 * (n : ℝ) - 2 * ((j : ℝ) + 1 + 1) + 1)
    have h36 : 36 ≤ d := by dsimp [d]; convert hd using 1; ring
    have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) h36
    have ratio : (Real.pi^4 / 8) / d ≤ 25/72 := by
      apply (div_le_iff₀ hdpos).2
      linarith [fourth_lt]
    rw [term, Nat.cast_succ, mul_div_assoc]
    change term n (j+1) * ((Real.pi^4/8)/d) ≤ _
    calc
      _ ≤ ((1/2 : ℝ) * (25/72 : ℝ)^j) * (25/72) :=
        mul_le_mul old ratio (by positivity) (by positivity)
      _ = _ := by rw [pow_succ]; ring



/-- The sum of all non-diagonal majorants at every admissible size. -/
theorem total_lt (n : ℕ) (hn : 13 ≤ n) :
    (5/12 : ℝ) * ∑ j ∈ Finset.range (n-1), term n (j+1) < 15/47 := by
  have hsum : ∑ j ∈ Finset.range (n-1), term n (j+1) ≤
      (1/2 : ℝ) * ∑ j ∈ Finset.range (n-1), (25/72 : ℝ)^j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    exact term_bound n j hn (by have := Finset.mem_range.mp hj; omega)
  have hgeom := geom_sum_mul_neg (25/72 : ℝ) (n-1)
  have hpos : 0 < (25/72 : ℝ)^(n-1) := by positivity
  linarith

#print axioms total_lt


/-- The recursion gives the factorial and descending odd factors of the analytic estimate. -/
theorem term_eq (n r : ℕ) :
    term n r = (Real.pi^4 / 8)^r /
      ((r.factorial : ℝ) * ∏ i ∈ Finset.range r, (2*(n:ℝ)-2*(i:ℝ)-1)) := by
  induction r with
  | zero => simp [term]
  | succ r ih =>
    rw [term, ih, pow_succ, Nat.factorial_succ, Finset.prod_range_succ]
    push_cast
    have last : 2*(n:ℝ)-2*((r:ℝ)+1)+1 = 2*(n:ℝ)-2*(r:ℝ)-1 := by ring
    rw [last]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem explicit_total_lt (n : ℕ) (hn : 13 ≤ n) :
    (5/12 : ℝ) * ∑ j ∈ Finset.range (n-1),
      ((Real.pi^4/8)^(j+1) / (((j+1).factorial : ℝ) *
        ∏ i ∈ Finset.range (j+1), (2*(n:ℝ)-2*(i:ℝ)-1))) < 15/47 := by
  simpa only [← term_eq] using total_lt n hn

#print axioms explicit_total_lt

end Polygon.PoleBound
