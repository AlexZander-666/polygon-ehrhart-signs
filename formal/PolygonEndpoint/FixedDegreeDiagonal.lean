import PolygonEndpoint.FixedDegreeTails

/-! Exact diagonal normalization and quantitative odd/even fixed ordinary-degree estimates. -/
noncomputable section
namespace PolygonEndpoint.FixedDegree
open Polygon Polygon.FormalCosine PolygonKernel Real Filter
open scoped Topology

def factorialScale (n : ℕ) : ℝ := ((2*n).factorial:ℝ)/π^(4*n)
def diagonal (n r : ℕ) : ℝ := leadingScale n r * kernel (2*n+2-r)
def oddPrincipal (n a : ℕ) : ℝ :=
  (-1:ℝ)^(n+a)*(5*2^(2*a)*π^(2*a)/(2*a+1).factorial)
def evenPrincipal (n a : ℕ) : ℝ :=
  (-1:ℝ)^(n+a+1)*(2^(2*a+1)*π^(2*a)/(2*a+2).factorial)

private theorem scale_formula {n : ℕ} (hn : 0<n) (r : ℕ) :
    leadingScale n r/factorialScale n =
      (2^r/(4*(r.factorial:ℝ)))*sigma n*π^(2*n) := by
  have hi : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold leadingScale factorialScale secantCoeff
  rw [c_eq_sigma hn,div_pow,←pow_mul,show 4*n=2*n+2*n by omega,pow_add]
  field_simp

private theorem sign_shift (k a : ℕ) : (-1:ℝ)^((k+a)+a)=(-1:ℝ)^k := by
  rw [show k+a+a=k+2*a by omega,pow_add,pow_mul]
  norm_num

private theorem odd_exact {k : ℕ} (hk : 0<k) (a : ℕ) :
    diagonal (k+a) (2*a+1)/(factorialScale (k+a)*oddPrincipal (k+a) a) =
      sigma (k+a)*(etaEven k+(-1:ℝ)^k*scaledRegular k 1/10) := by
  have d : 2*(k+a)+2-(2*a+1)=2*k+1 := by omega
  rw [diagonal,d,←div_div,mul_div_right_comm,scale_formula (by omega)]
  unfold kernel oddPrincipal scaledRegular
  rw [g_odd_eta hk.ne',sign_shift,show 2*(k+a)=2*k+2*a by omega,pow_add π,pow_succ (2:ℝ)]
  have sg : ((-1:ℝ)^k)^2=1 := by rw [←pow_mul,mul_comm k 2,pow_mul]; norm_num
  rcases sq_eq_one_iff.mp sg with h|h <;> rw [h] <;> field_simp <;> ring

private theorem even_exact {k : ℕ} (hk : 0<k) (a : ℕ) :
    diagonal (k+a) (2*a+2)/(factorialScale (k+a)*
      (evenPrincipal (k+a) a*(2*(k:ℝ)-1))) =
      sigma (k+a)*(etaEven k+(-1:ℝ)^(k+1)*scaledRegular k 0/(2*(2*(k:ℝ)-1))) := by
  have d : 2*(k+a)+2-(2*a+2)=2*k := by omega
  have kp : (1:ℝ)≤k := by exact_mod_cast hk
  have nz : 2*(k:ℝ)-1≠0 := by linarith
  rw [diagonal,d,←div_div,mul_div_right_comm,scale_formula (by omega)]
  unfold kernel evenPrincipal scaledRegular
  rw [g_even_eta hk.ne',pow_succ (-1:ℝ) (k+a+a),sign_shift,show 2*(k+a)=2*k+2*a by omega,pow_add π]
  simp only [Nat.add_zero,pow_succ (-1:ℝ) k]
  have sg : ((-1:ℝ)^k)^2=1 := by rw [←pow_mul,mul_comm k 2,pow_mul]; norm_num
  rw [show (2:ℝ)^(2*a+2)=2^(2*a+1)*2 by rw [pow_succ]]
  rcases sq_eq_one_iff.mp sg with h|h <;> rw [h] <;> field_simp <;> ring

/-- A common explicit budget for the exact odd and double-pole even factors. -/
def tailBudget : ℝ := 3+2*regularCap

private theorem scalar_error {n k : ℕ} (hk : 0<k) (hkn : k≤n) {v : ℝ}
    (hv : |v|≤regularCap/(k:ℝ)^2) :
    |sigma n*(etaEven k+v)-1| ≤ tailBudget/(k:ℝ)^2 := by
  have hn : 0<n := by omega
  have hsig := sigma_bounds hn
  have small := sigma_error hn
  have dist := eta_error hk
  have adj : (1:ℝ)/(n:ℝ)^2 ≤ 1/(k:ℝ)^2 := by
    apply one_div_le_one_div_of_le (by positivity); gcongr
  have absσ : |sigma n|≤2 := by rw [abs_of_nonneg (by linarith [hsig.1])]; linarith [hsig.2.1,hsig.2.2]
  rw [show sigma n*(etaEven k+v)-1=sigma n*((etaEven k-1)+v)+(sigma n-1) by ring]
  apply (abs_add_le ..).trans
  rw [abs_mul]
  calc
    _ ≤ 2*(1/(k:ℝ)^2+regularCap/(k:ℝ)^2)+1/(k:ℝ)^2 :=
      add_le_add (mul_le_mul absσ ((abs_add_le ..).trans (add_le_add dist hv)) (abs_nonneg _) (by norm_num))
        (small.trans adj)
    _ = _ := by unfold tailBudget; ring

private theorem small_regular {k δ : ℕ} (hk : 0<k) (hδ : δ≤1) (i : ℕ) {b : ℝ} (hb : 1≤b) :
    |(-1:ℝ)^i*scaledRegular k δ/b|≤regularCap/(k:ℝ)^2 := by
  rw [abs_div,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,abs_of_pos (by linarith : 0<b)]
  exact (div_le_self (abs_nonneg _) hb).trans (regular_error hk hδ)

theorem odd_refined {k : ℕ} (hk : 0<k) (a : ℕ) :
    |diagonal (k+a) (2*a+1)/(factorialScale (k+a)*oddPrincipal (k+a) a)-1| ≤
      tailBudget/(k:ℝ)^2 := by
  rw [odd_exact hk]
  exact scalar_error hk (by omega) (small_regular hk (by decide) k (by norm_num))

theorem even_refined {k : ℕ} (hk : 0<k) (a : ℕ) :
    |diagonal (k+a) (2*a+2)/(factorialScale (k+a)*(evenPrincipal (k+a) a*(2*(k:ℝ)-1)))-1| ≤
      tailBudget/(k:ℝ)^2 := by
  rw [even_exact hk]
  have h : (1:ℝ)≤k := by exact_mod_cast hk
  exact scalar_error hk (by omega) (small_regular hk (by decide) (k+1) (by linarith))

private theorem tailBudget_nonneg : 0≤tailBudget := by unfold tailBudget regularCap; positivity

private theorem shifted_bound {n a : ℕ} (hn : 2*a+2≤n) :
    tailBudget/((n-a:ℕ):ℝ)^2 ≤ 4*tailBudget/(n:ℝ)^2 := by
  have h : (n:ℝ)≤2*((n-a:ℕ):ℝ) := by exact_mod_cast (show n≤2*(n-a) by omega)
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) n) h 2
  have nh : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have kh : 0<((n-a:ℕ):ℝ) := by exact_mod_cast (by omega : 0<n-a)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hs tailBudget_nonneg]

theorem odd_diagonal_rate {n a : ℕ} (hn : 2*a+2≤n) :
    |diagonal n (2*a+1)/(factorialScale n*oddPrincipal n a)-1| ≤ 4*tailBudget/(n:ℝ)^2 := by
  have h := odd_refined (by omega : 0<n-a) a
  rw [Nat.sub_add_cancel (by omega : a≤n)] at h
  exact h.trans (shifted_bound hn)

/-- The double pole gives the precise linear factor 2n+1-r. Keeping it exposes
a second-order relative remainder about the paper's leading term 2n. -/
theorem even_diagonal_refined {n a : ℕ} (hn : 2*a+2≤n) :
    |diagonal n (2*a+2)/(factorialScale n*(evenPrincipal n a*(2*(n:ℝ)))) -
      (1-(2*(a:ℝ)+1)/(2*n))| ≤ 4*tailBudget/(n:ℝ)^2 := by
  let k := n-a
  have hkn : k+a=n := by dsimp [k]; omega
  have hk : 0<k := by dsimp [k]; omega
  have h := even_refined hk a
  rw [hkn] at h
  have hrate := h.trans (shifted_bound hn)
  have hnpos : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hkpos : 1≤(k:ℝ) := by exact_mod_cast hk
  have hkr : (k:ℝ)+(a:ℝ)=n := by exact_mod_cast hkn
  let u := (2*(k:ℝ)-1)/(2*(n:ℝ))
  have ulo : 0≤u := div_nonneg (by linarith) (by positivity)
  have uhi : u≤1 := by apply (div_le_one (by positivity)).mpr; linarith
  have eu : 1-(2*(a:ℝ)+1)/(2*n)=u := by dsimp [u]; field_simp; linarith
  have nz : 2*(k:ℝ)-1≠0 := by linarith
  have id (z f e : ℝ) : z/(f*(e*(2*(n:ℝ))))-u = (z/(f*(e*(2*(k:ℝ)-1)))-1)*u := by
    dsimp [u]
    by_cases hf : f=0
    · simp [hf]
    by_cases he : e=0
    · simp [he]
    field_simp
  rw [eu,id,abs_mul,abs_of_nonneg ulo]
  exact (mul_le_of_le_one_right (abs_nonneg _) uhi).trans hrate

/-- The paper's relative O(1/n) for positive even degree. -/
theorem even_diagonal_rate {n a : ℕ} (hn : 2*a+2≤n) :
    |diagonal n (2*a+2)/(factorialScale n*(evenPrincipal n a*(2*(n:ℝ))))-1| ≤
      (4*tailBudget+2*(a:ℝ)+1)/(n:ℝ) := by
  have nh : 1≤(n:ℝ) := by exact_mod_cast (by omega : 1≤n)
  have n0 : 0<(n:ℝ) := by linarith
  have u := even_diagonal_refined hn
  let v := diagonal n (2*a+2)/(factorialScale n*(evenPrincipal n a*(2*(n:ℝ))))
  change |v-_|≤_ at u
  change |v-1|≤_
  have e := abs_add_le (v-(1-(2*(a:ℝ)+1)/(2*n))) (-((2*(a:ℝ)+1)/(2*n)))
  rw [show v-(1-(2*(a:ℝ)+1)/(2*n))+-((2*(a:ℝ)+1)/(2*n))=v-1 by ring,abs_neg,
    abs_of_nonneg (by positivity : 0≤(2*(a:ℝ)+1)/(2*n))] at e
  apply e.trans
  calc
    _ ≤ 4*tailBudget/(n:ℝ)^2 + (2*(a:ℝ)+1)/(2*n) := by gcongr
    _ ≤ 4*tailBudget/n+(2*(a:ℝ)+1)/n := by
      apply add_le_add
      · apply div_le_div_of_nonneg_left (mul_nonneg (by norm_num) tailBudget_nonneg) n0
        nlinarith only [mul_nonneg (sub_nonneg.mpr nh) n0.le]
      · apply div_le_div_of_nonneg_left (by positivity) n0; linarith
    _ = _ := by ring

open Asymptotics

theorem odd_diagonal_bigO (a : ℕ) :
    (fun n ↦ diagonal n (2*a+1)/(factorialScale n*oddPrincipal n a)-1)
      =O[atTop] (fun n : ℕ ↦ 1/(n:ℝ)^2) := by
  apply IsBigO.of_bound (4*tailBudget)
  filter_upwards [eventually_ge_atTop (2*a+2)] with n hn
  simpa only [Real.norm_eq_abs,abs_of_nonneg (show 0≤1/(n:ℝ)^2 by positivity),
    mul_one_div] using odd_diagonal_rate hn

theorem even_diagonal_bigO (a : ℕ) :
    (fun n ↦ diagonal n (2*a+2)/(factorialScale n*(evenPrincipal n a*(2*(n:ℝ))))-1)
      =O[atTop] (fun n : ℕ ↦ 1/(n:ℝ)) := by
  apply IsBigO.of_bound (4*tailBudget+2*(a:ℝ)+1)
  filter_upwards [eventually_ge_atTop (2*a+2)] with n hn
  simpa only [Real.norm_eq_abs,abs_of_nonneg (show 0≤1/(n:ℝ) by positivity),
    mul_one_div] using even_diagonal_rate hn

theorem odd_diagonal_limit (a : ℕ) :
    Tendsto (fun n ↦ diagonal n (2*a+1)/(factorialScale n*oddPrincipal n a)) atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) _
    (tendsto_const_div_atTop_nhds_zero_nat (4*tailBudget))
  filter_upwards [eventually_ge_atTop (2*a+2)] with n hn
  apply (odd_diagonal_rate hn).trans
  have h : 1≤(n:ℝ) := by exact_mod_cast (by omega : 1≤n)
  apply div_le_div_of_nonneg_left (mul_nonneg (by norm_num) tailBudget_nonneg) (by linarith)
  nlinarith only [mul_nonneg (sub_nonneg.mpr h) (Nat.cast_nonneg (α:=ℝ) n)]

theorem even_diagonal_limit (a : ℕ) :
    Tendsto (fun n ↦ diagonal n (2*a+2)/(factorialScale n*(evenPrincipal n a*(2*(n:ℝ)))))
      atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) _
    (tendsto_const_div_atTop_nhds_zero_nat (4*tailBudget+2*(a:ℝ)+1))
  filter_upwards [eventually_ge_atTop (2*a+2)] with n hn
  exact even_diagonal_rate hn

end PolygonEndpoint.FixedDegree
