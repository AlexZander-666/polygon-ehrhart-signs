import PolygonEndpoint.LargeSigns

/-! A relative error bound independent of the degree of the coefficient.
The first displaced kernel value is retained in the second estimate. -/
noncomputable section
namespace PolygonEndpoint
open Polygon Finset
open Polygon.UniformCoefficientBound (shifted weight)

/-- A majorant for offset j+1, valid even when the complementary degree is small. -/
private def M (n j : ℕ) : ℝ := (108:ℝ)^(j+1)*weight n (j+1)

private theorem pi_bound : Real.pi^2 < 10 := by
  calc
    _ < (3.15:ℝ)^2 := by gcongr; exact Real.pi_lt_d2
    _ < _ := by norm_num

private theorem m0 {n : ℕ} (hn : 65≤n) : M n 0 ≤ 135/(n:ℝ) := by
  have h : (65:ℝ) ≤ n := by exact_mod_cast hn
  simp only [M,weight,zero_add,pow_one,Nat.factorial_one,Nat.cast_one,prod_range_one,
    Nat.cast_zero,mul_zero,sub_zero,one_mul]
  rw [←mul_div_assoc,div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_right pi_bound.le (show 0≤(n:ℝ) by positivity)]

private theorem m_step (n j : ℕ) : M n (j+1) =
    M n j * (108*(Real.pi^2/8)/(((j:ℝ)+2)*(2*(n:ℝ)-2*j-3))) := by
  have link (i : ℕ) : M n i = (108/28:ℝ)*UniformCoefficientBound.majorant n i := by
    rw [M, UniformCoefficientBound.majorant_eq,pow_succ]; ring
  rw [link,link,UniformCoefficientBound.majorant]; ring

private theorem m_succ {n j : ℕ} (hn : 65≤n) (hj : j+2<n) (hM : 0≤M n j) :
    M n (j+1) ≤ M n j * (135/192:ℝ) := by
  have h : (65:ℝ)≤n := by exact_mod_cast hn
  have q : (j:ℝ)+3 ≤ n := by exact_mod_cast (show j+3 ≤ n by omega)
  have denom : (192:ℝ) ≤ ((j:ℝ)+2)*(2*(n:ℝ)-2*j-3) := by
    nlinarith [mul_nonneg (show 0≤(n:ℝ)-j-3 by linarith)
      (show 0≤2*(j:ℝ)+1 by positivity)]
  rw [m_step]
  apply mul_le_mul_of_nonneg_left _ hM
  apply (div_le_iff₀ (by linarith)).2
  linarith [pi_bound]

private theorem m_nonneg {n j : ℕ} (hj : j+1<n) : 0 ≤ M n j := by
  have key := TraceWeights.normalized_bound (n:=n) (j:=j+1) (by omega) hj
  have hw := (abs_nonneg _).trans key
  unfold M
  apply mul_nonneg (by positivity)
  linarith

private theorem m1 {n : ℕ} (hn : 65≤n) : M n 1 ≤ 10000/(n:ℝ)^2 := by
  have h : (65:ℝ) ≤ n := by exact_mod_cast hn
  have hden : (n:ℝ) ≤ 2*n-3 := by linarith
  have factor : 108*(Real.pi^2/8)/(2*(2*(n:ℝ)-3)) ≤ 135/(2*n) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right pi_bound.le (show 0≤(n:ℝ) by positivity)]
  rw [show 1=0+1 by rfl,m_step]
  simp only [Nat.cast_zero,zero_add,mul_zero,sub_zero]
  calc
    _ ≤ (135/(n:ℝ))*(135/(2*n)) :=
      mul_le_mul (m0 hn) factor (div_nonneg (by positivity) (by linarith)) (by positivity)
    _ ≤ _ := by
      have e : (0:ℝ)<n := by linarith
      field_simp
      norm_num

private theorem m_bound {n j : ℕ} (hn : 65≤n) (hj : j+1<n) :
    M n j ≤ (135/(n:ℝ))*(135/192:ℝ)^j := by
  induction j with
  | zero => simpa using m0 hn
  | succ j ih =>
    rw [pow_succ (135/192:ℝ),←mul_assoc]
    exact (m_succ hn hj (m_nonneg (by omega))).trans
      (mul_le_mul_of_nonneg_right (ih (by omega)) (by norm_num))

private theorem tail_bound {n j : ℕ} (hn : 65≤n) (hj : j+2<n) :
    M n (j+1) ≤ (10000/(n:ℝ)^2)*(135/192:ℝ)^j := by
  induction j with
  | zero => simpa using m1 hn
  | succ j ih =>
    rw [pow_succ (135/192:ℝ),←mul_assoc]
    exact (m_succ hn hj (m_nonneg (by omega))).trans
      (mul_le_mul_of_nonneg_right (ih (by omega)) (by norm_num))

private theorem shifted_all (d h : ℕ) : |shifted kernel d h| ≤ (108:ℝ)^h*|kernel d| := by
  induction h with
  | zero => simp [shifted]
  | succ h ih =>
    by_cases e : 2*(h+1)≤d
    · rw [shifted,if_pos e,show d-2*(h+1)=d-2*h-2 by omega]
      rw [shifted,if_pos (by omega)] at ih
      have q : |kernel (d-2*h-2)| ≤ 108*|kernel (d-2*h)| := by
        exact_mod_cast (PolygonKernel.kernel_all (d-2*h)).2.2.1 (by omega)
      calc
        _ ≤ 108*|kernel (d-2*h)| := q
        _ ≤ 108*(108^h*|kernel d|) := by gcongr
        _ = _ := by rw [pow_succ]; ring
    · rw [shifted,if_neg e,abs_zero]; positivity

private theorem one_term {n j : ℕ} (d : ℕ) (hj : j+1<n) :
    |relativeWeight n (j+1)*shifted kernel d (j+1)| ≤ (5/12:ℝ)*M n j*|kernel d| := by
  have hp : |relativeWeight n (j+1)| ≤ (5/12:ℝ)*weight n (j+1) :=
    TraceWeights.normalized_bound (by omega) hj
  rw [abs_mul]
  calc
    _ ≤ ((5/12:ℝ)*weight n (j+1))*((108:ℝ)^(j+1)*|kernel d|) :=
      mul_le_mul hp (shifted_all _ _) (abs_nonneg _) ((abs_nonneg _).trans hp)
    _ = _ := by unfold M; ring

private theorem geom_cap (t : ℕ) : (∑ j ∈ range t, (135/192:ℝ)^j) ≤ 7/2 := by
  have h := geom_sum_mul_neg (135/192:ℝ) t
  have hp : 0 ≤ (135/192:ℝ)^t := by positivity
  linarith

private theorem mass {n : ℕ} (hn : 65≤n) (d : ℕ) :
    |∑ j ∈ range (n-1), relativeWeight n (j+1)*shifted kernel d (j+1)| ≤
      (200/(n:ℝ))*|kernel d| := by
  have hsum := geom_cap (n-1)
  calc
    _ ≤ ∑ j ∈ range (n-1), |relativeWeight n (j+1)*shifted kernel d (j+1)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range (n-1), ((5/12:ℝ)*(135/n)*|kernel d|)*(135/192:ℝ)^j := by
      apply sum_le_sum
      intro j hj
      have hj' : j+1<n := by have := mem_range.mp hj; omega
      apply (one_term d hj').trans
      calc
        _ ≤ (5/12:ℝ)*((135/n)*(135/192:ℝ)^j)*|kernel d| := by gcongr; exact m_bound hn hj'
        _ = _ := by ring
    _ = ((5/12:ℝ)*(135/n)*|kernel d|)*∑ j ∈ range (n-1), (135/192:ℝ)^j := by rw [mul_sum]
    _ ≤ ((5/12:ℝ)*(135/n)*|kernel d|)*(7/2) := by gcongr
    _ ≤ _ := by
      have h : 0 ≤ |kernel d|/(n:ℝ) := by positivity
      rw [div_eq_mul_inv] at h
      simp only [div_eq_mul_inv]
      nlinarith only [h]

private theorem tail_mass {n : ℕ} (hn : 65≤n) (d : ℕ) :
    |∑ j ∈ range (n-2), relativeWeight n (j+2)*shifted kernel d (j+2)| ≤
      (15000/(n:ℝ)^2)*|kernel d| := by
  have hsum := geom_cap (n-2)
  calc
    _ ≤ ∑ j ∈ range (n-2), |relativeWeight n (j+2)*shifted kernel d (j+2)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range (n-2), ((5/12:ℝ)*(10000/(n:ℝ)^2)*|kernel d|)*(135/192:ℝ)^j := by
      apply sum_le_sum
      intro j hj
      have hj' : j+2<n := by have := mem_range.mp hj; omega
      apply (one_term d hj').trans
      calc
        _ ≤ (5/12:ℝ)*((10000/(n:ℝ)^2)*(135/192:ℝ)^j)*|kernel d| := by
          gcongr
          exact tail_bound hn hj'
        _ = _ := by ring
    _ = ((5/12:ℝ)*(10000/(n:ℝ)^2)*|kernel d|)*∑ j ∈ range (n-2), (135/192:ℝ)^j := by rw [mul_sum]
    _ ≤ ((5/12:ℝ)*(10000/(n:ℝ)^2)*|kernel d|)*(7/2) := by gcongr
    _ ≤ _ := by
      have h : 0 ≤ |kernel d|/(n:ℝ)^2 := by positivity
      rw [div_eq_mul_inv] at h
      simp only [div_eq_mul_inv]
      nlinarith only [h]

private theorem factorial_decay {n d : ℕ} (hn : 66≤n) (hd : d≤2*n+1) (lo : 2≤d)
    {c : ℝ} (h₀ : 0≤c) (h₁ : c≤5/2) :
    c*Real.pi^(2*n+d)/(4^n*((2*n).factorial:ℝ)) ≤ 1/(n:ℝ)^2 := by
  let k := n-1
  have hkn : k+1=n := by dsimp [k]; omega
  have h := Polygon.UniformCoefficientBound.factorial_correction_lt (n:=k) (d:=d-2)
    (by omega) (by omega) h₀ h₁
  have hf : ((2*n).factorial:ℝ) = (2*(n:ℝ))*(2*(n:ℝ)-1)*((2*k).factorial:ℝ) := by
    rw [show 2*n=2*k+1+1 by omega,Nat.factorial_succ,Nat.factorial_succ]
    push_cast
    have eq : (k:ℝ)+1=n := by exact_mod_cast hkn
    rw [←eq]
    ring
  have hr : (66:ℝ)≤n := by exact_mod_cast hn
  have hpos : 0 < 2*(n:ℝ)-1 := by linarith
  have hnpos : (0:ℝ)<n := by linarith
  have hscale : 0 < 4*(2*(n:ℝ))*(2*n-1) := by positivity
  have split : c*Real.pi^(2*n+d)/(4^n*((2*n).factorial:ℝ)) =
      (c*Real.pi^(2*k+(d-2))/(4^k*((2*k).factorial:ℝ))) *
      (Real.pi^4/(4*(2*(n:ℝ))*(2*n-1))) := by
    rw [show 2*n+d=(2*k+(d-2))+4 by omega,pow_add,hf,←hkn,pow_succ (4:ℝ) k]
    field_simp
  rw [split]
  calc
    _ ≤ (1/32:ℝ)*(Real.pi^4/(4*(2*(n:ℝ))*(2*n-1))) :=
      mul_le_mul_of_nonneg_right h.le (div_nonneg (by positivity) hscale.le)
    _ ≤ _ := by
      have pi4 : Real.pi^4 ≤ 100 := by
        calc
          _ = (Real.pi^2)^2 := by ring
          _ ≤ (10:ℝ)^2 := pow_le_pow_left₀ (sq_nonneg _) pi_bound.le _
          _ = _ := by norm_num
      rw [←mul_div_assoc,div_le_div_iff₀ hscale (by positivity)]
      nlinarith [mul_nonneg (show 0 ≤ 100-Real.pi^4 by linarith) (sq_nonneg (n:ℝ)),
        mul_nonneg (show 0≤(n:ℝ) by positivity) (show 0≤(n:ℝ)-1 by linarith)]

private theorem correction_decay {n r : ℕ} (hn : 66 ≤ n) (hr : 1 ≤ r) (top : r ≤ 2 * n + 2)
    :
    |(correction r : ℝ) / (2 * 4 ^ n)| ≤
      leadingScale n r * |kernel (2 * n + 2 - r)| / (n:ℝ)^2 := by
  let d := 2 * n + 2 - r
  let c : ℝ := correction r
  let F : ℝ := (2 * n).factorial
  have hn' : 0 < n := by omega
  have hscale := leadingScale_positive (r := r) hn'
  by_cases low : r = 1 ∨ r = 2
  · have htotal : d + r = 2 * n + 2 := Nat.sub_add_cancel top
    have hdtop : d ≤ 2 * n + 1 := by omega
    have hcases : 0 ≤ c ∧ c ≤ 5 / 2 := by
      rcases low with h | h <;> norm_num [c, correction, h]
    have hd : 27 ≤ d := by rcases low with h | h <;> omega
    have hfactor := factorial_decay hn hdtop (by omega)
      hcases.1 hcases.2
    have hF : 0 < F := by dsimp [F]; positivity
    have hlead : F / (2 * Real.pi ^ (2 * n)) ≤ leadingScale n r := by
      rw [leadingScale_low hn' low, ← mul_one F]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Polygon.FormalCosine.sigma_one_le hn') hF.le) (by positivity)
    have hkernel : 1 / Real.pi ^ d ≤ |kernel d| := by
      apply (div_le_iff₀ (by positivity : 0 < Real.pi ^ d)).mpr
      rw [mul_comm]
      exact (PolygonKernel.normalized_abs_lower d hd).le
    change |c / (2 * 4 ^ n)| ≤ leadingScale n r * |kernel d| / (n:ℝ)^2
    rw [abs_of_nonneg (div_nonneg hcases.1 (by positivity))]
    calc
      c / (2 * 4 ^ n) =
          (c * Real.pi ^ (2 * n + d) / (4 ^ n * F)) *
          (F / (2 * Real.pi ^ (2 * n + d))) := by field_simp
      _ ≤ (1 / (n:ℝ)^2 : ℝ) * (F / (2 * Real.pi ^ (2 * n + d))) :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ = (F / (2 * Real.pi ^ (2 * n)) * (1 / Real.pi ^ d)) / (n:ℝ)^2 := by
        rw [pow_add]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul hlead hkernel (by positivity) hscale.le) (by positivity)
  · rw [correction, if_neg (fun h ↦ low (Or.inl h)), if_neg (fun h ↦ low (Or.inr h))]
    simp only [Rat.cast_zero, zero_div, abs_zero]
    positivity

/-- Uniform in every positive degree r. The scale times g_d approximates the
actual coefficient with relative error at most 201/n. -/
theorem uniform_diagonal_error {n r : ℕ} (hn : 66≤n) (hr : 1≤r) (top : r≤2*n+2) :
    let d := 2*n+2-r
    let A := ((GeneralRealization.geometricEhrhart (n-3)).coeff r:ℝ)
    |A - leadingScale n r*kernel d| ≤
      (201/(n:ℝ))*(leadingScale n r*|kernel d|) := by
  dsimp only
  let d := 2*n+2-r
  let F := leadingScale n r
  let S := ∑ j ∈ range (n-1), relativeWeight n (j+1)*shifted kernel d (j+1)
  let C := (correction r:ℝ)/(2*4^n)
  have e := diagonal_row (by omega : 3≤n) hr top
  change _ = F*(kernel d+S)-C at e
  have pos : 0 < F := leadingScale_positive (by omega)
  have hn' : (66:ℝ) ≤ n := by exact_mod_cast hn
  have cmp : 1/(n:ℝ)^2 ≤ 1/(n:ℝ) := by
    apply one_div_le_one_div_of_le (by linarith)
    nlinarith [mul_nonneg (show 0≤(n:ℝ) by positivity) (show 0≤(n:ℝ)-1 by linarith)]
  rw [e]
  change |F*(kernel d+S)-C-F*kernel d| ≤ _
  rw [show F*(kernel d+S)-C-F*kernel d=F*S-C by ring]
  calc
    _ ≤ |F*S|+|C| := abs_sub _ _
    _ ≤ F*((200/(n:ℝ))*|kernel d|) + (F*|kernel d|)/(n:ℝ)^2 := by
      rw [abs_mul,abs_of_pos pos]
      exact add_le_add (mul_le_mul_of_nonneg_left (mass (by omega) d) pos.le) (correction_decay hn hr top)
    _ ≤ F*((200/(n:ℝ))*|kernel d|) + (F*|kernel d|)*(1/(n:ℝ)) := by
      rw [div_eq_mul_inv (F*|kernel d|)]
      apply add_le_add_right
      simpa only [one_div] using mul_le_mul_of_nonneg_left cmp (mul_nonneg pos.le (abs_nonneg (kernel d)))
    _ = _ := by change _ = (201/(n:ℝ))*(F*|kernel d|); ring

/-- Uniform second-order estimate, including the signed first displaced term. -/
theorem uniform_first_order_error {n r : ℕ} (hn : 66≤n) (hr : 1≤r) (top : r≤2*n+2) :
    let d := 2*n+2-r
    let A := ((GeneralRealization.geometricEhrhart (n-3)).coeff r:ℝ)
    |A - leadingScale n r*(kernel d+relativeWeight n 1*shifted kernel d 1)| ≤
      (15001/(n:ℝ)^2)*(leadingScale n r*|kernel d|) := by
  dsimp only
  let d := 2*n+2-r
  let F := leadingScale n r
  let T := ∑ j ∈ range (n-2), relativeWeight n (j+2)*shifted kernel d (j+2)
  let C := (correction r:ℝ)/(2*4^n)
  have pos : 0 < F := leadingScale_positive (by omega)
  have e := diagonal_row (by omega : 3≤n) hr top
  rw [show n-1=n-2+1 by omega,sum_range_succ'] at e
  rw [e]
  change |F*(kernel d+(T+relativeWeight n 1*shifted kernel d 1))-C-
    F*(kernel d+relativeWeight n 1*shifted kernel d 1)| ≤ _
  rw [show F*(kernel d+(T+relativeWeight n 1*shifted kernel d 1))-C-
    F*(kernel d+relativeWeight n 1*shifted kernel d 1)=F*T-C by ring]
  calc
    _ ≤ |F*T|+|C| := abs_sub _ _
    _ ≤ F*((15000/(n:ℝ)^2)*|kernel d|) + (F*|kernel d|)/(n:ℝ)^2 := by
      rw [abs_mul,abs_of_pos pos]
      exact add_le_add (mul_le_mul_of_nonneg_left (tail_mass (by omega) d) pos.le) (correction_decay hn hr top)
    _ = _ := by change _ = (15001/(n:ℝ)^2)*(F*|kernel d|); ring

/-- The coefficient of the first displaced kernel value in the expansion. -/
theorem first_relative_weight {n : ℕ} (hn : 2≤n) :
    relativeWeight n 1 = Real.pi^2/(24*(2*(n:ℝ)-1))*
      (FormalCosine.sigma (n-1)/FormalCosine.sigma n) := by
  let k := n-1
  have ek : k+1=n := by dsimp [k]; omega
  have eq : (k:ℝ)+1=n := by exact_mod_cast ek
  have fk : (k:ℝ)≠0 := by exact_mod_cast (show k≠0 by omega)
  have p := FormalCosine.c_ratio (b:=n) (a:=k) (by omega) (by omega)
  rw [show n-k=1 by omega,pow_one] at p
  have f : ((2*n).factorial:ℝ) = (2*(n:ℝ))*(2*(n:ℝ)-1)*((2*k).factorial:ℝ) := by
    rw [show 2*n=2*k+1+1 by omega,Nat.factorial_succ,Nat.factorial_succ]
    push_cast
    rw [←eq]; ring
  change ((2*k).factorial:ℝ)/(2*n).factorial*(FormalCosine.c k/FormalCosine.c n)*
    InverseSineBound.b n k = _
  rw [p,f,show InverseSineBound.b n k=(k:ℝ)/3 from ek ▸ InverseSineBound.first_offset k]
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have hnf : (0:ℝ)<(2*k).factorial := by positivity
  field_simp
  ring

#print axioms first_relative_weight
#print axioms uniform_diagonal_error
#print axioms uniform_first_order_error
end PolygonEndpoint
