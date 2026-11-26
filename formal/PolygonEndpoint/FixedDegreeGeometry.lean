import PolygonEndpoint.FixedDegreeDiagonal
import PolygonEndpoint.UniformApprox

/-! The signed fixed ordinary-degree asymptotics for the actual geometric lattice-point polynomial. -/
noncomputable section
namespace PolygonEndpoint.FixedDegree
open Polygon Filter Asymptotics
open scoped Topology

abbrev actual (n r : ℕ) : ℝ := ((GeneralRealization.geometricEhrhart (n-3)).coeff r : ℝ)

/-- Convert a relative diagonal error into a relative geometric coefficient error.
The normalization P is allowed to have either sign. -/
private theorem lift_approx {n r : ℕ} (hn : 66≤n) (hr : 1≤r) (top : r≤2*n+2)
    {P C : ℝ} (hc : 0≤C) (di : |diagonal n r/P-1|≤C/n) :
    |actual n r/P-1| ≤ (201*(C+1)+C)/(n:ℝ) := by
  have h := uniform_diagonal_error hn hr top
  have hs : 0≤leadingScale n r := (leadingScale_positive (by omega : 0<n)).le
  change |actual n r-diagonal n r| ≤ (201/(n:ℝ))*(leadingScale n r*|kernel (2*n+2-r)|) at h
  replace h : |actual n r-diagonal n r| ≤ (201/(n:ℝ))*|diagonal n r| := by
    simpa only [diagonal,abs_mul,abs_of_nonneg hs] using h
  have npos : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have n1 : 1≤(n:ℝ) := by exact_mod_cast (by omega : 1≤n)
  have small : |(actual n r-diagonal n r)/P| ≤ (201/(n:ℝ))*|diagonal n r/P| := by
    rw [abs_div,abs_div,mul_div_assoc']
    exact div_le_div_of_nonneg_right h (abs_nonneg _)
  have bound : |diagonal n r/P|≤C+1 := by
    have h := abs_add_le (diagonal n r/P-1) 1
    rw [sub_add_cancel,abs_one] at h
    exact h.trans (add_le_add (di.trans (div_le_self hc n1)) le_rfl)
  have e := abs_add_le ((actual n r-diagonal n r)/P) (diagonal n r/P-1)
  rw [sub_div,sub_add_sub_cancel] at e
  rw [sub_div] at small
  apply e.trans
  calc
    _ ≤ (201/n)*(C+1)+C/n := add_le_add (small.trans (mul_le_mul_of_nonneg_left bound (by positivity))) di
    _ = _ := by ring

def oddBudget := 4*tailBudget
def evenBudget (a : ℕ) : ℝ := 4*tailBudget+2*a+1
private theorem budget_nonneg : 0 ≤ tailBudget := by unfold tailBudget regularCap; positivity

theorem odd_geometric_rate {n a : ℕ} (hn : 66≤n) (hr : 2*a+2≤n) :
    |actual n (2*a+1)/(factorialScale n*oddPrincipal n a)-1| ≤
      (201*(oddBudget+1)+oddBudget)/(n:ℝ) := by
  have hb : 0≤oddBudget := mul_nonneg (by norm_num) budget_nonneg
  apply lift_approx hn (by omega) (by omega) hb
  apply (odd_diagonal_rate hr).trans
  have n1 : 1≤(n:ℝ) := by exact_mod_cast (by omega : 1≤n)
  apply div_le_div_of_nonneg_left hb (by linarith)
  nlinarith only [mul_nonneg (sub_nonneg.mpr n1) (Nat.cast_nonneg (α:=ℝ) n)]

theorem even_geometric_rate {n a : ℕ} (hn : 66≤n) (hr : 2*a+2≤n) :
    |actual n (2*a+2)/(factorialScale n*(evenPrincipal n a*(2*(n:ℝ))))-1| ≤
      (201*(evenBudget a+1)+evenBudget a)/(n:ℝ) := by
  have b := budget_nonneg
  have hb : 0≤evenBudget a := by unfold evenBudget; positivity
  exact lift_approx hn (by omega) (by omega) hb (even_diagonal_rate hr)

theorem odd_geometric_bigO (a : ℕ) :
    (fun n ↦ actual n (2*a+1)/(factorialScale n*oddPrincipal n a)-1)
      =O[atTop] (fun n : ℕ ↦ 1/(n:ℝ)) := by
  apply IsBigO.of_bound (201*(oddBudget+1)+oddBudget)
  filter_upwards [eventually_ge_atTop (max 66 (2*a+2))] with n hn
  simpa only [Real.norm_eq_abs,abs_of_nonneg (show 0≤1/(n:ℝ) by positivity),
    mul_one_div] using odd_geometric_rate ((le_max_left ..).trans hn) ((le_max_right ..).trans hn)

theorem even_geometric_bigO (a : ℕ) :
    (fun n ↦ actual n (2*a+2)/(factorialScale n*(evenPrincipal n a*(2*(n:ℝ))))-1)
      =O[atTop] (fun n : ℕ ↦ 1/(n:ℝ)) := by
  apply IsBigO.of_bound (201*(evenBudget a+1)+evenBudget a)
  filter_upwards [eventually_ge_atTop (max 66 (2*a+2))] with n hn
  simpa only [Real.norm_eq_abs,abs_of_nonneg (show 0≤1/(n:ℝ) by positivity),
    mul_one_div] using even_geometric_rate ((le_max_left ..).trans hn) ((le_max_right ..).trans hn)

theorem odd_geometric_limit (a : ℕ) :
    Tendsto (fun n ↦ actual n (2*a+1)/(factorialScale n*oddPrincipal n a)) atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact tendsto_zero_iff_norm_tendsto_zero.mp ((odd_geometric_bigO a).trans_tendsto
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)))

theorem even_geometric_limit (a : ℕ) :
    Tendsto (fun n ↦ actual n (2*a+2)/(factorialScale n*(evenPrincipal n a*(2*(n:ℝ))))) atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact tendsto_zero_iff_norm_tendsto_zero.mp ((even_geometric_bigO a).trans_tendsto
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)))

end PolygonEndpoint.FixedDegree
