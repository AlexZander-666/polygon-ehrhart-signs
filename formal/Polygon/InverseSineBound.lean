import Polygon.FormalCosine
import Polygon.UniformCoefficientBound

/-! A two-index differential recurrence for powers of the true inverse sine.
The same recurrence certifies positivity and the binomial majorant. -/
namespace Polygon.InverseSineBound
open PowerSeries FormalCosine

private abbrev S := PowerSeries ℝ
private noncomputable abbrev A := inverseSine
private noncomputable abbrev B := (cos ℝ).subst A
private noncomputable abbrev deriv := derivative ℝ
private noncomputable def delta (f : S) : S := B * deriv f
private noncomputable def euler (f : S) : S := X * deriv f

private theorem admissible : HasSubst A := HasSubst.substInvOfIsUnit _ _

private theorem sin_deriv : deriv (sin ℝ) = cos ℝ := by
  ext n
  rw [coeff_derivative]
  rcases Nat.even_or_odd' n with ⟨k,rfl | rfl⟩
  · simp [sin,cos,Nat.factorial_succ, (show (2*k+1)/2=k by omega)]
    field_simp
  · simp [sin,cos,(show Even (2*k+1+1) from ⟨k+1,by omega⟩)]

private theorem delta_A : B * deriv A = 1 := by
  have h := congrArg (derivative ℝ) sine_inverse
  rw [derivative_subst admissible,sin_deriv,derivative_X] at h
  simpa [mul_comm] using h

private theorem square_B : B^2 = 1 - X^2 := by
  have h : (cos ℝ)^2+(sin ℝ)^2=1 := by
    simpa [cosAt,sinAt] using square_sum 1
  have h' := congrArg (fun f : S => (substAlgHom admissible) f) h
  simp only [map_add,map_pow,map_one,coe_substAlgHom,sine_inverse] at h'
  exact eq_sub_of_add_eq h'

private theorem dB : B * deriv B = -X := by
  have h := congrArg (derivative ℝ) square_B
  simp only [derivative_pow, Nat.cast_ofNat, Nat.reduceSub, pow_one, map_sub,
    Derivation.map_one_eq_zero, derivative_X, mul_one, zero_sub] at h
  apply mul_left_cancel₀ (show (2:S) ≠ 0 by
    intro e
    have h0 := congrArg (constantCoeff (R:=ℝ)) e
    norm_num [map_ofNat] at h0)
  linear_combination h

private theorem delta_succ (p : ℕ) : delta (A^(p+1)) = (p+1 : ℕ)*A^p := by
  rw [delta, derivative_pow, Nat.add_sub_cancel]
  calc
    _ = ((p+1 : ℕ) : S)*A^p*(B*deriv A) := by ring
    _ = _ := by rw [delta_A,mul_one]

private theorem delta_twice (p : ℕ) :
    delta (delta (A^(p+2))) = C ((p+2:ℝ)*(p+1))*A^p := by
  rw [delta_succ]
  change B * deriv (((p+2 : ℕ) : S) * A^(p+1)) = _
  have cast : ((p+2:ℕ):S) = C (p+2:ℝ) := by norm_num [map_ofNat]
  rw [cast, Derivation.leibniz, derivative_C, smul_zero, add_zero]
  change B*(C (p+2:ℝ)*deriv (A^(p+1))) = _
  rw [mul_left_comm]
  rw [← delta, delta_succ, map_mul]
  simp only [map_add,map_natCast,map_one, map_ofNat, Nat.cast_add,Nat.cast_one]
  ring

private theorem ode (f : S) : delta (delta f) = deriv (deriv f) - euler (euler f) := by
  simp only [delta,euler,Derivation.leibniz,derivative_X,smul_eq_mul,mul_one]
  linear_combination deriv f * dB + deriv (deriv f) * square_B

private theorem coeff_euler (f : S) (n : ℕ) : coeff n (euler f) = (n : ℝ) * coeff n f := by
  cases n with
  | zero => simp [euler,coeff_zero_eq_constantCoeff]
  | succ n =>
    rw [euler, ←pow_one (X:S), coeff_X_pow_mul, coeff_derivative, Nat.cast_succ]
    ring

/-- Differential recurrence in both the coefficient index and the exponent. -/
theorem recurrence (m p : ℕ) :
    ((m:ℝ)+1)*(m+2)*coeff (m+2) (A^(p+2)) =
      (m:ℝ)^2*coeff m (A^(p+2)) + ((p:ℝ)+2)*(p+1)*coeff m (A^p) := by
  have h := congrArg (coeff m) ((ode (A^(p+2))).symm.trans (delta_twice p))
  simp only [map_sub,coeff_derivative,coeff_euler,coeff_C_mul,Nat.cast_succ] at h
  linear_combination h


/-- The coefficients b_{n,k} used in the original numerical trace expansion. -/
noncomputable def b (n k : ℕ) : ℝ := coeff (2*n) (inverseSine^(2*k))

theorem step (n k : ℕ) :
    (2*(n:ℝ)+1)*(2*n+2)*b (n+1) (k+1) =
      (2*(n:ℝ))^2 * b n (k+1) + (2*(k:ℝ)+2)*(2*k+1)*b n k := by
  have h := recurrence (2*n) (2*k)
  simpa only [b, Nat.mul_add, Nat.mul_one, Nat.cast_mul, Nat.cast_ofNat] using h

theorem above {n k : ℕ} (h : n < k) : b n k = 0 := by
  have hdiv : (X : S) ∣ A := X_dvd_iff.mpr (constantCoeff_substInvOfIsUnit _ _)
  exact X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hdiv (2*k)) _ (by omega)

theorem zero_column (n : ℕ) : b (n+1) 0 = 0 := by
  simp [b, coeff_one]

theorem diagonal (n : ℕ) : b n n = 1 := by
  induction n with
  | zero => simp [b]
  | succ n ih =>
    apply mul_left_cancel₀ (show (2*(n:ℝ)+1)*(2*n+2) ≠ 0 by positivity)
    rw [step, above (Nat.lt_succ_self n), ih]
    ring

/-- The first off-diagonal has an exact linear value. -/
theorem first_offset (n : ℕ) : b (n+1) n = (n:ℝ)/3 := by
  induction n with
  | zero => simp [zero_column]
  | succ n ih =>
    apply mul_left_cancel₀ (show (2*((n+1:ℕ):ℝ)+1)*(2*(n+1:ℕ)+2) ≠ 0 by positivity)
    rw [step,diagonal,ih]
    push_cast
    ring

theorem nonneg (n k : ℕ) : 0 ≤ b n k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => rw [diagonal]; norm_num
    | succ k => rw [above (by omega)]
  | succ n ih =>
    cases k with
    | zero => rw [zero_column]
    | succ k =>
      have h := step n k
      have hp : 0 < (2*(n:ℝ)+1)*(2*n+2) := by positivity
      apply (nonneg_of_mul_nonneg_right _ hp)
      rw [h]
      exact add_nonneg (mul_nonneg (sq_nonneg _) (ih (k+1)))
        (mul_nonneg (by positivity) (ih k))

#print axioms diagonal
#print axioms first_offset
#print axioms nonneg


private theorem subpascal {n k : ℕ} (hk : k ≤ n) :
    b (n+1) (k+1) ≤ b n (k+1) + b n k := by
  have pos : 0 < (2*(n:ℝ)+1)*(2*n+2) := by positivity
  apply le_of_mul_le_mul_left _ pos
  rw [step]
  conv_rhs => rw [mul_add]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ (nonneg ..)
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  · apply mul_le_mul_of_nonneg_right _ (nonneg ..)
    have ord : (k:ℝ) ≤ n := by exact_mod_cast hk
    rw [mul_comm (2*(k:ℝ)+2)]
    gcongr

/-- Uniform binomial bound, sharp on the first off-diagonal. -/
theorem upper (n k : ℕ) (hk : k < n) :
    3*b (n+1) (k+1) ≤ (n.choose k : ℝ) := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    by_cases eq : k=n
    · subst k
      rw [first_offset,Nat.choose_succ_self_right]
      push_cast
      linarith
    · have lo : k < n := by omega
      have u := subpascal (n:=n+1) (k:=k) (by omega)
      cases k with
      | zero =>
        rw [zero_column, add_zero] at u
        have bnd := ih 0 lo
        simp only [Nat.choose_zero_right, Nat.cast_one] at bnd ⊢
        linarith
      | succ t =>
        have h1 := ih (t+1) lo
        have h0 := ih t (by omega)
        rw [Nat.choose_succ_succ',Nat.cast_add]
        linarith

/-- Offset form used to dominate the true non-diagonal terms of the trace. -/
theorem trace_weight_bound {n j : ℕ} (hj : 1 ≤ j) (hn : j < n) :
    0 ≤ coeff (2*n) (inverseSine^(2*(n-j))) ∧
    coeff (2*n) (inverseSine^(2*(n-j))) ≤ (1/3:ℝ)*((n-1).choose j : ℝ) := by
  refine ⟨nonneg _ _, ?_⟩
  have h := upper (n-1) (n-j-1) (by omega)
  have hsym := Nat.choose_symm (n:=n-1) (k:=j) (by omega)
  rw [show n-1+1=n by omega,show n-j-1+1=n-j by omega,
    show n-j-1 = n-1-j by omega, hsym] at h
  change b n (n-j) ≤ _
  linarith

#print axioms trace_weight_bound

#print axioms recurrence
end Polygon.InverseSineBound
