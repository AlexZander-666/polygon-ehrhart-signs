import PolygonEndpoint.Diagonal
import PolygonKernel.KernelTail

/-! Quantitative small tails for the three genuine scalar factors in the fixed-degree diagonal. -/
noncomputable section
namespace PolygonEndpoint.FixedDegree
open Polygon Polygon.FormalCosine PolygonKernel Real Filter Finset

private theorem pow_growth (k : ℕ) : (k:ℝ)^2 ≤ (2:ℝ)^(2*k) := by
  have h : (k:ℝ)≤(2:ℝ)^k := by exact_mod_cast k.lt_two_pow_self.le
  rw [mul_comm 2 k,pow_mul]
  exact pow_le_pow_left₀ (by positivity) h 2

theorem eta_error {k : ℕ} (hk : 0<k) : |etaEven k-1|≤1/(k:ℝ)^2 := by
  have h := etaEven_bounds hk.ne'
  rw [abs_of_nonpos (by linarith only [h.2])]
  have e := one_div_le_one_div_of_le (show 0<(k:ℝ)^2 by positivity) (pow_growth k)
  linarith only [h.1,e]

private def oddTerm (k i : ℕ) := 1/(2*((i:ℝ)+1)+1)^(2*k)
private theorem oddSum {k : ℕ} (hk : 0<k) : Summable (oddTerm k) := by
  unfold oddTerm
  simpa [Nat.cast_add] using (summable_nat_add_iff 1).mpr (sigma_summable hk)
private theorem oddTail {k : ℕ} (hk : 0<k) : sigma k-1=∑' i, oddTerm k i := by
  unfold sigma
  rw [(sigma_summable hk).tsum_eq_zero_add]
  simp [oddTerm]

theorem sigma_error {k : ℕ} (hk : 0<k) : |sigma k-1|≤1/(k:ℝ)^2 := by
  have pos : 0<(k:ℝ) := by exact_mod_cast hk
  have e : k^2≤2^(2*(k-1)) := by
    have h := (k-1).lt_two_pow_self
    have t : k≤2^(k-1) := by omega
    rw [mul_comm 2 (k-1),pow_mul]
    exact Nat.pow_le_pow_left t 2
  have term (i : ℕ) : oddTerm k i ≤ (1/(k:ℝ)^2)*oddTerm 1 i := by
    let b := 2*((i:ℝ)+1)+1
    have b2 : 2≤b := by dsimp [b]; linarith [Nat.cast_nonneg (α:=ℝ) i]
    have h : (k:ℝ)^2 ≤ b^(2*(k-1)) :=
      (show (k:ℝ)^2≤(2:ℝ)^(2*(k-1)) by exact_mod_cast e).trans
        (pow_le_pow_left₀ (by norm_num) b2 _)
    change 1/b^(2*k) ≤ 1/(k:ℝ)^2 * (1/b^2)
    rw [one_div_mul_one_div,show 2*k=2*(k-1)+2 by omega,pow_add]
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  have tail := (oddSum hk).tsum_le_tsum term ((oddSum (by decide : 0<1)).mul_left _)
  rw [abs_of_nonneg (sub_nonneg.mpr (sigma_one_le hk)),oddTail hk]
  apply tail.trans
  rw [tsum_mul_left,←oddTail (by decide : 0<1)]
  have s := sigma_bounds (by decide : 0<1)
  exact mul_le_of_le_one_right (by positivity) (by linarith [s.2.1,s.2.2])

/-- A single absolute constant for both parity classes of the entire regular contribution. -/
def regularCap : ℝ := 12*π^2*exp (12*π)

theorem regular_error {k δ : ℕ} (hk : 1≤k) (_hδ : δ≤1) :
    |scaledRegular k δ| ≤ regularCap / (k:ℝ)^2 := by
  let m := 2*k+δ-2
  have plus : m+2=2*k+δ := by dsimp [m]; omega
  have le : 2*k≤ m+2 := by omega
  have kp : 0<(k:ℝ) := by exact_mod_cast hk
  have p1 : 1 ≤ π := by linarith [Real.pi_gt_three]
  have mge : k≤ m+1 := by dsimp [m]; omega
  have kpow : (k:ℝ)≤2^m := by exact_mod_cast mge.trans (Nat.succ_le_of_lt m.lt_two_pow_self)
  have ksq : (k:ℝ)^2≤4^m := by
    have h := pow_le_pow_left₀ kp.le kpow 2
    rwa [←pow_mul,mul_comm m 2,pow_mul,show (2:ℝ)^2=4 by norm_num] at h
  have mass : (8+4*(3:ℝ)^m)≤12*3^m := by
    linarith [one_le_pow₀ (by norm_num : (1:ℝ)≤3) (n:=m)]
  have pir : π^(2*k)≤π^m*π^2 := by rw [←pow_add]; exact pow_le_pow_right₀ p1 le
  have expb := Real.pow_div_factorial_le_exp (12*π) (show 0≤12*π by positivity) m
  have fm : (0:ℝ)< m.factorial := by positivity
  unfold scaledRegular regularCoeff
  change |(((8+4*(3:ℚ)^m)/(m.factorial:ℚ):ℚ):ℝ)*π^(2*k)| ≤ regularCap/(k:ℝ)^2
  push_cast
  rw [abs_of_nonneg (by positivity),le_div_iff₀ (by positivity)]
  calc
    _ ≤ ((12*3^m)/(m.factorial:ℝ))*(π^m*π^2)*4^m := by gcongr
    _ = 12*π^2*((12*π)^m/(m.factorial:ℝ)) := by
      rw [show (12:ℝ)*π=3*π*4 by ring,mul_pow,mul_pow]
      ring
    _ ≤ regularCap := by unfold regularCap; gcongr

end PolygonEndpoint.FixedDegree
