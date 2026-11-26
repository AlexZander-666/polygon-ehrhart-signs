import Polygon.PoleBound

/-! Uniform majorant for the off-diagonal centered coefficients of a polygon.
The zero-based argument of `majorant` is one less than the positive offset. -/
namespace Polygon.UniformCoefficientBound
open Finset

/-- The initial offset has kernel factor 28. Subsequent factors are 108. -/
noncomputable def majorant (n : ℕ) : ℕ → ℝ
  | 0 => 28*(Real.pi^2/8)/(2*(n:ℝ)-1)
  | j+1 => majorant n j * (108*(Real.pi^2/8)) /
      (((j:ℝ)+2)*(2*(n:ℝ)-2*(j:ℝ)-3))

/-- Factorial and odd-product part of the normalized coefficients. -/
noncomputable def weight (n h : ℕ) : ℝ :=
  (Real.pi^2/8)^h /
   ((h.factorial:ℝ) * ∏ i ∈ range h, (2*(n:ℝ)-2*(i:ℝ)-1))

theorem majorant_eq (n j : ℕ) : majorant n j = 28*108^j*weight n (j+1) := by
  induction j with
  | zero =>
    simp [majorant,weight,div_eq_mul_inv,mul_assoc]
  | succ j ih =>
    rw [majorant, ih]
    simp only [weight, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
      prod_range_succ]
    have h : 2*(n:ℝ)-2*((j:ℝ)+1)-1 = 2*(n:ℝ)-2*(j:ℝ)-3 := by ring
    rw [h]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring_nf

private lemma pi_sq_lt : Real.pi^2 < 10 := by
  calc
    _ < (3.15:ℝ)^2 := by gcongr; exact Real.pi_lt_d2
    _ < 10 := by norm_num

private lemma denominator {n j : ℕ} (hn : 65 ≤ n) (hj : j+2 < n) :
    192 ≤ ((j:ℝ)+2)*(2*(n:ℝ)-2*(j:ℝ)-3) := by
  have hn' : (65:ℝ) ≤ n := by exact_mod_cast hn
  have hj' : (j:ℝ)+3 ≤ n := by exact_mod_cast (show j+3 ≤ n by omega)
  have hj0 : 0 ≤ (j:ℝ) := by positivity
  nlinarith [mul_nonneg (show 0 ≤ (n:ℝ)-j-3 by linarith)
    (show 0 ≤ 2*(j:ℝ)+1 by linarith)]

/-- At offset h=j+1 the finite product is geometrically dominated up through h=n−1. -/
theorem majorant_le (n j : ℕ) (hn : 65 ≤ n) (hj : j+1<n) :
    majorant n j ≤ (35/129:ℝ)*(135/192:ℝ)^j := by
  have hn' : (65:ℝ) ≤ n := by exact_mod_cast hn
  induction j with
  | zero =>
    simp only [majorant,pow_zero,mul_one]
    apply (div_le_iff₀ (by linarith : 0 < 2*(n:ℝ)-1)).2
    linarith [pi_sq_lt]
  | succ j ih =>
    have hd := denominator hn hj
    let D := ((j:ℝ)+2)*(2*(n:ℝ)-2*(j:ℝ)-3)
    have hd' : 192 ≤ D := hd
    have ratio : 108*(Real.pi^2/8)/D ≤ 135/192 := by
      apply (div_le_iff₀ (by linarith : 0<D)).2
      linarith [pi_sq_lt]
    rw [majorant, mul_div_assoc, pow_succ (135/192:ℝ), ←mul_assoc]
    exact mul_le_mul (ih (by omega)) ratio
      (div_nonneg (by positivity) (by linarith)) (by positivity)

/-- The manuscript's complete relative off-diagonal mass is below two fifths. -/
theorem total_lt (n : ℕ) (hn : 65 ≤ n) :
    (5/12:ℝ)*(∑ j ∈ range (n-1), majorant n j) < 2/5 := by
  have s : (∑ j ∈ range (n-1), majorant n j) ≤
      (35/129:ℝ)*(∑ j ∈ range (n-1), (135/192:ℝ)^j) := by
    rw [mul_sum]
    exact sum_le_sum fun j hj ↦ majorant_le n j hn (by have := mem_range.mp hj; omega)
  have h := geom_sum_mul_neg (135/192:ℝ) (n-1)
  have hp : 0 < (135/192:ℝ)^(n-1) := by positivity
  linarith

/-- The explicit factorial and descending odd product with no recurrence in the conclusion. -/
theorem explicit_total_lt (n : ℕ) (hn : 65 ≤ n) :
    (5/12:ℝ)*(∑ j ∈ range (n-1), 28*108^j*
      ((Real.pi^2/8)^(j+1)/(((j+1).factorial:ℝ) *
        ∏ i ∈ range (j+1), (2*(n:ℝ)-2*(i:ℝ)-1)))) < 2/5 := by
  simpa only [majorant_eq,weight] using total_lt n hn


/-- Zero extension handles those offsets h with d−2h negative. -/
def shifted (g : ℕ → ℝ) (d h : ℕ) : ℝ := if 2*h ≤ d then g (d-2*h) else 0

/-- A single strong first step and j subsequent ordinary steps. -/
theorem shifted_bound (g : ℕ → ℝ)
    (first : ∀ t, 27 ≤ t → |g (t-2)| ≤ 28*|g t|)
    (next : ∀ t, 2 ≤ t → |g (t-2)| ≤ 108*|g t|)
    {d : ℕ} (hd : 27 ≤ d) (j : ℕ) :
    |shifted g d (j+1)| ≤ 28*108^j*|g d| := by
  induction j with
  | zero => simpa [shifted, show 2 ≤ d by omega] using first d hd
  | succ j ih =>
    by_cases he : 2*(j+2) ≤ d
    · have he' : 2*(j+1) ≤ d := by omega
      have e : d-2*(j+2) = d-2*(j+1)-2 := by omega
      rw [shifted, if_pos he, e]
      rw [shifted, if_pos he'] at ih
      calc
        _ ≤ 108*|g (d-2*(j+1))| := next _ (by omega)
        _ ≤ 108*(28*108^j*|g d|) := by gcongr
        _ = _ := by rw [pow_succ]; ring
    · rw [shifted,if_neg he,abs_zero]
      positivity

/-- Sum of absolute magnitudes for arbitrary normalized Newton weights satisfying the
sharp arcsine bound. Here p(h) is indexed by the actual positive offset h. -/
theorem off_diagonal_lt {n d : ℕ} (hn : 65 ≤ n) (hd : 27 ≤ d) (g p : ℕ → ℝ)
    (nonzero : g d ≠ 0)
    (first : ∀ t, 27 ≤ t → |g (t-2)| ≤ 28*|g t|)
    (next : ∀ t, 2 ≤ t → |g (t-2)| ≤ 108*|g t|)
    (weights : ∀ h, 1 ≤ h → h<n → |p h| ≤ (5/12:ℝ)*weight n h) :
    (∑ j ∈ range (n-1), |p (j+1)*shifted g d (j+1)|) < (2/5:ℝ)*|g d| := by
  calc
    _ ≤ ∑ j ∈ range (n-1), (5/12:ℝ)*majorant n j*|g d| := by
      apply sum_le_sum
      intro j hj
      have hw := weights (j+1) (by omega) (by have := mem_range.mp hj; omega)
      rw [abs_mul,majorant_eq]
      calc
        _ ≤ ((5/12:ℝ)*weight n (j+1))*(28*108^j*|g d|) :=
          mul_le_mul hw (shifted_bound g first next hd j) (abs_nonneg _) ((abs_nonneg _).trans hw)
        _ = _ := by ring
    _ = (5/12:ℝ)*(∑ j ∈ range (n-1), majorant n j)*|g d| := by
      rw [←sum_mul, ←mul_sum]
    _ < _ := mul_lt_mul_of_pos_right (total_lt n hn) (abs_pos.mpr nonzero)

/-- The low-degree scale is small starting with row 65. -/
theorem low_correction_lt (n : ℕ) (hn : 65 ≤ n) : 10*(25/(n:ℝ))^n < 1/32 := by
  have hr : (65:ℝ) ≤ n := by exact_mod_cast hn
  have half : 25/(n:ℝ) ≤ 1/2 := (div_le_iff₀ (by linarith)).2 (by linarith)
  have h1 := pow_le_pow_left₀ (by positivity : 0 ≤ 25/(n:ℝ)) half n
  have h2 : (1/2:ℝ)^n ≤ (1/2:ℝ)^9 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  norm_num at h2
  linarith

/-- A normalized row with its off-diagonal terms and a signed low-degree correction.
The conclusion certifies strict agreement of signs. -/
theorem sign_of_centered_sum {n d : ℕ} (hn : 65 ≤ n) (hd : 27 ≤ d)
    (g p : ℕ → ℝ) (nonzero : g d ≠ 0)
    (first : ∀ t, 27 ≤ t → |g (t-2)| ≤ 28*|g t|)
    (next : ∀ t, 2 ≤ t → |g (t-2)| ≤ 108*|g t|)
    (weights : ∀ h, 1 ≤ h → h<n → |p h| ≤ (5/12:ℝ)*weight n h)
    {a F correction : ℝ} (scale : 0<F)
    (row : a = F*(g d + ∑ j ∈ range (n-1), p (j+1)*shifted g d (j+1))-correction)
    (small : |correction| ≤ F*|g d|/32) : 0 < a*g d := by
  let t := ∑ j ∈ range (n-1), p (j+1)*shifted g d (j+1)
  have b : |t| < (2/5:ℝ)*|g d| := (abs_sum_le_sum_abs _ _).trans_lt
    (off_diagonal_lt hn hd g p nonzero first next weights)
  have lo := neg_abs_le t
  have hi := le_abs_self t
  have c1 := le_abs_self correction
  have c2 := neg_abs_le correction
  change a = F*(g d+t)-correction at row
  rcases lt_or_gt_of_ne nonzero with neg | pos
  · rw [abs_of_neg neg] at b small
    apply mul_pos_of_neg_of_neg _ neg
    nlinarith [mul_pos scale (show 0 < -(2/5:ℝ)*g d-t by linarith)]
  · rw [abs_of_pos pos] at b small
    apply mul_pos _ pos
    nlinarith [mul_pos scale (show 0 < (2/5:ℝ)*g d+t by linarith)]


/-- The paper's explicit compensation bound, including its factorial denominator.
For the first two ordinary coefficients the numerator constant is 5/2 or 1/2. -/
theorem factorial_correction_lt {n d : ℕ} (hn : 65 ≤ n) (hd : d ≤ 2*n+1)
    {c : ℝ} (hc : 0 ≤ c) (hcap : c ≤ 5/2) :
    c*Real.pi^(2*n+d)/(4^n*((2*n).factorial:ℝ)) < 1/32 := by
  have hfac : (n:ℝ)^n ≤ ((2*n).factorial:ℝ) := by
    exact_mod_cast (calc
      n^n ≤ (n+1)^n := Nat.pow_le_pow_left (by omega) _
      _ ≤ n.factorial*(n+1)^n := Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
      _ ≤ (n+n).factorial := Nat.factorial_mul_pow_le_factorial
      _ = (2*n).factorial := by rw [two_mul])
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hp := Real.pi_pos
  have hpi : Real.pi^4 ≤ 100 := by
    calc
      _ = (Real.pi^2)^2 := by ring
      _ ≤ (10:ℝ)^2 := pow_le_pow_left₀ (sq_nonneg _) pi_sq_lt.le 2
      _ = _ := by norm_num
  have hpow : Real.pi^(2*n+d) ≤ Real.pi^(4*n+1) :=
    pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) (by omega)
  have hnum : c*Real.pi^(2*n+d) ≤ 10*100^n := by
    calc
      _ ≤ c*Real.pi^(4*n+1) := by gcongr
      _ = (c*Real.pi)*(Real.pi^4)^n := by rw [pow_succ,pow_mul]; ring
      _ ≤ _ := mul_le_mul (by nlinarith [mul_nonneg (sub_nonneg.mpr hcap) hp.le,
        Real.pi_lt_d2]) (pow_le_pow_left₀ (by positivity) hpi _) (by positivity) (by norm_num)
  calc
    _ ≤ 10*100^n/(4^n*(n:ℝ)^n) := by gcongr
    _ = 10*(25/(n:ℝ))^n := by
      rw [div_pow]
      have four : (100:ℝ)^n = 4^n*25^n := by rw [← mul_pow]; norm_num
      rw [four]
      field_simp
    _ < _ := low_correction_lt n hn

/-- The factor 1/3 in the arcsine coefficient estimate is present at every positive
offset: the first rising-factorial factor is exactly 1/3 of the ordinary one. -/
theorem rising_third (k j : ℕ) :
    (∏ i ∈ range (j+1), ((k:ℝ)/3+i)) ≤
      (1/3:ℝ)*(∏ i ∈ range (j+1), ((k:ℝ)+i)) := by
  induction j with
  | zero => simp; ring_nf; rfl
  | succ j ih =>
    rw [prod_range_succ, prod_range_succ (fun i : ℕ ↦ (k:ℝ)+i), ←mul_assoc]
    apply mul_le_mul ih (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k])
    · positivity
    · positivity

/-- The ratio of adjacent Taylor coefficients of arcsin(w)/w is bounded by
the corresponding ratio of (1−w²)^(−1/6). -/
theorem arcsine_ratio_le (h : ℕ) :
    (2*(h:ℝ)+1)^2/(2*((h:ℝ)+1)*(2*(h:ℝ)+3)) ≤
      ((h:ℝ)+1/6)/((h:ℝ)+1) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (h:ℝ), Nat.cast_nonneg (α := ℝ) h]

#print axioms rising_third
#print axioms arcsine_ratio_le
#print axioms majorant_eq
#print axioms explicit_total_lt
#print axioms shifted_bound
#print axioms off_diagonal_lt
#print axioms factorial_correction_lt
#print axioms sign_of_centered_sum
end Polygon.UniformCoefficientBound
