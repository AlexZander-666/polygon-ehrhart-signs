import Polygon.InverseSineBound
import Polygon.CosineZeta

/-! Cancellation of the even factorial factors in diagonal-normalized trace weights. -/
namespace Polygon.TraceWeights

open Finset PowerSeries FormalCosine

private def odds (n j : ℕ) : ℝ :=
  ∏ i ∈ range j, (2*(n:ℝ)-2*i-1)

private theorem odds_pos {n j : ℕ} (h : j ≤ n) : 0 < odds n j := by
  apply prod_pos
  intro i hi
  have hn : (i:ℝ)+1 ≤ n := by exact_mod_cast (show i+1≤n by have := mem_range.mp hi; omega)
  linarith

private theorem paired (n j : ℕ) (hj : j ≤ n) :
    ((2*n).factorial : ℝ) = ((2*(n-j)).factorial : ℝ)*2^j*(n.descFactorial j : ℝ)*odds n j := by
  induction j with
  | zero => simp [odds]
  | succ j ih =>
    have old := ih (by omega)
    have hd : 2*(n-j) = 2*(n-(j+1))+1+1 := by omega
    have fac : ((2*(n-j)).factorial:ℝ) =
        (2*(n:ℝ)-2*j)*(2*(n:ℝ)-2*j-1)*((2*(n-(j+1))).factorial:ℝ) := by
      rw [hd,Nat.factorial_succ,Nat.factorial_succ]
      push_cast [Nat.cast_sub (by omega : j+1 ≤ n)]
      ring
    rw [old,fac,pow_succ,Nat.descFactorial_succ]
    simp only [Nat.cast_mul,Nat.cast_sub (by omega : j ≤ n), odds,prod_range_succ]
    ring

private theorem choose_scale {n j : ℕ} (hj : j < n) :
    (n:ℝ)/(n-j) * ((n-1).choose j : ℝ) = n.choose j := by
  have hn : 1 ≤ n := by omega
  have h := Nat.add_one_mul_choose_eq (n-1) (n-1-j)
  rw [show n-1+1=n by omega, show n-1-j+1=n-j by omega,
    Nat.choose_symm (n:=n-1) (k:=j) (by omega),
    Nat.choose_symm (n:=n) (k:=j) (by omega)] at h
  have hr : (n:ℝ) * ((n-1).choose j:ℝ) = (n.choose j:ℝ)*(n-j) := by
    rw [← Nat.cast_sub (show j ≤ n by omega)]
    exact_mod_cast h
  have jlt : (j:ℝ)<n := by exact_mod_cast hj
  have den := (sub_pos.mpr jlt).ne'
  field_simp
  linarith only [hr]

/-- Exact cancellation before applying any analytic inequalities. -/
theorem cancellation {n j : ℕ} (hj : j<n) :
    (Real.pi^2/4)^j *((n:ℝ)/(n-j))*((n-1).choose j : ℝ)*
      (((2*(n-j)).factorial : ℝ)/(2*n).factorial) = UniformCoefficientBound.weight n j := by
  rw [mul_assoc ((Real.pi^2/4)^j),choose_scale hj]
  have hdesc := Nat.descFactorial_eq_factorial_mul_choose n j
  have hc := paired n j (by omega)
  rw [hdesc,Nat.cast_mul] at hc
  change _ = (Real.pi^2/8)^j/((j.factorial : ℝ)*odds n j)
  have plus := odds_pos (n:=n) (j:=j) (by omega)
  have den : (0:ℝ)<(2*n).factorial := by positivity
  have halv : (Real.pi^2/4)^j = (Real.pi^2/8)^j*2^j := by
    rw [← mul_pow]
    congr 1
    ring
  rw [halv]
  field_simp
  rw [hc]
  ring

/-- The weight which multiplies g at distance 2j from the diagonal. -/
noncomputable def normalized (n j : ℕ) : ℝ :=
  (((2*(n-j)).factorial : ℝ)/(2*n).factorial) *
  (coeff (2*(n-j)) logSec / coeff (2*n) logSec) * InverseSineBound.b n (n-j)

theorem bound_of_ratio {n j : ℕ} (hj : 1 ≤ j) (hn : j < n)
    (hc0 : 0 ≤ coeff (2*(n-j)) logSec / coeff (2*n) logSec)
    (hc : coeff (2*(n-j)) logSec / coeff (2*n) logSec ≤
      (5/4:ℝ)*(Real.pi^2/4)^j*((n:ℝ)/(n-j))) :
    |normalized n j| ≤ (5/12:ℝ)*UniformCoefficientBound.weight n j := by
  have hb := InverseSineBound.trace_weight_bound hj hn
  change 0 ≤ InverseSineBound.b n (n-j) ∧
    InverseSineBound.b n (n-j) ≤ (1/3:ℝ)*((n-1).choose j : ℝ) at hb
  let t : ℝ := ((2*(n-j)).factorial : ℝ)/(2*n).factorial
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hden : 0 < (n:ℝ)-j := sub_pos.mpr (by exact_mod_cast hn)
  have hprod : 0 ≤ (5/4:ℝ)*(Real.pi^2/4)^j*((n:ℝ)/(n-j)) := by positivity
  have prod := mul_le_mul_of_nonneg_left (mul_le_mul hc hb.2 hb.1 hprod) ht
  unfold normalized
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg ht hc0) hb.1), ← cancellation hn]
  dsimp [t] at prod
  linarith only [prod]

theorem normalized_bound {n j : ℕ} (hj : 1 ≤ j) (hn : j < n) :
    |normalized n j| ≤ (5/12:ℝ)*UniformCoefficientBound.weight n j := by
  have ha : 0 < n-j := by omega
  have hb : 0 < n := by omega
  have hc := FormalCosine.c_ratio_le (b:=n) ha (Nat.sub_le n j)
  rw [show n-(n-j)=j by omega, Nat.cast_sub (by omega : j≤n)] at hc
  apply bound_of_ratio hj hn (div_nonneg (c_pos ha).le (c_pos hb).le)
  have hp : Real.pi^2/8 ≤ 5/4 := by
    have hs : Real.pi^2 < (3.15:ℝ)^2 := by gcongr; exact Real.pi_lt_d2
    linarith
  have hden : 0 < (n:ℝ)-j := sub_pos.mpr (by exact_mod_cast hn)
  apply hc.trans
  rw [mul_right_comm (5/4:ℝ)]
  gcongr

#print axioms normalized_bound
#print axioms cancellation
#print axioms bound_of_ratio
end Polygon.TraceWeights
