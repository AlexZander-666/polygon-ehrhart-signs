import PolygonKernel.SeriesBridge
import Mathlib.Tactic

/-! Width-sum exponentials and their ordinary dilation coefficients. -/
noncomputable section
namespace PolygonEndpoint
open PowerSeries Finset PolygonKernel
open scoped PowerSeries

abbrev ex (a : ℚ) : ℚ⟦X⟧ := rescale a (exp ℚ)

private lemma ex_mul (a b : ℚ) : ex a * ex b = ex (a+b) := exp_mul_exp_eq_exp_add a b

/-- A triangular sum with q consecutive widths and a linear endpoint weight. -/
def tri {R : Type*} [CommRing R] (f : ℕ → R) (q : ℕ) : R :=
  ∑ i ∈ range q, ((q:R)-i)*f i

private lemma tri_step {R : Type*} [CommRing R] (f : ℕ → R) (q : ℕ) :
    tri f (q+1) = tri f q + ∑ i ∈ range (q+1), f i := by
  simp only [tri,sum_range_succ,Nat.cast_succ]
  have split (i : ℕ) : ((q:R)+1-i)*f i = ((q:R)-i)*f i+f i := by ring
  simp only [split,sum_add_distrib]
  ring

private theorem sum_step {R : Type*} [CommRing R] (f : ℕ → R) (q : ℕ) :
    ∑ i ∈ range q, (f (i+1)-f i) = f q-f 0 := by
  induction q with
  | zero => simp
  | succ q ih => rw [sum_range_succ,ih]; ring

theorem weighted_second_diff {R : Type*} [CommRing R] (f : ℕ → R) (q : ℕ) :
    tri (fun i ↦ f (i+2)-2*f (i+1)+f i) q = f (q+1)-(q+1:R)*f 1+q*f 0 := by
  induction q with
  | zero => simp [tri]
  | succ q ih =>
    rw [tri_step,ih]
    have e : ∀ i, f (i+2)-2*f (i+1)+f i = (f (i+2)-f (i+1))-(f (i+1)-f i) :=
      fun _ ↦ by ring
    simp_rw [e]
    rw [sum_step (fun i ↦ f (i+1)-f i)]
    push_cast
    ring

/-- U_q uses the actual inclusive width m=i+1 and multiplicity q+2−m. -/
def U (q : ℕ) : ℚ⟦X⟧ := tri (fun i ↦ ex (2*(i:ℚ)+3)) (q+1)

private lemma sinh_shift (x : ℚ) :
    (4*formalSinh^2)*ex x = ex (x+2)-2*ex x+ex (x-2) := by
  have h : 4*formalSinh^2 = (ex 1-ex (-1))^2 := by
    unfold formalSinh
    rw [mul_pow,←mul_assoc,←map_pow]
    norm_num
    have e : (4 : ℚ⟦X⟧) = C (4:ℚ) := (map_ofNat _ _).symm
    rw [e,←map_mul]
    norm_num [ex]
  rw [h]
  have a : ex 1*ex 1*ex x = ex (x+2) := by rw [ex_mul,ex_mul]; congr 1; ring
  have b : ex (-1)*ex (-1)*ex x = ex (x-2) := by rw [ex_mul,ex_mul]; congr 1; ring
  have c : ex 1*ex (-1) = 1 := by rw [ex_mul]; norm_num [ex]
  linear_combination a+b-2*ex x*c

/-- The cross-multiplied endpoint exponential identity, with no division by sinh. -/
theorem endpoint_exponential (q : ℕ) :
    (4*formalSinh^2)*U q = ex (2*(q:ℚ)+5) + (q+1:ℕ)*ex 1 - (q+2:ℕ)*ex 3 := by
  have h := weighted_second_diff (fun i ↦ ex (2*(i:ℚ)+1)) (q+1)
  rw [U,tri,mul_sum]
  trans tri (fun i ↦ ex (2*((i+2:ℕ):ℚ)+1)-2*ex (2*((i+1:ℕ):ℚ)+1)+ex (2*(i:ℚ)+1)) (q+1)
  · apply sum_congr rfl
    intro i _
    rw [mul_left_comm,sinh_shift]
    push_cast
    rw [show 2*(i:ℚ)+3+2=2*((i:ℚ)+2)+1 by ring,
      show 2*(i:ℚ)+3=2*((i:ℚ)+1)+1 by ring,
      show 2*((i:ℚ)+1)+1-2=2*(i:ℚ)+1 by ring]
  · rw [h]
    push_cast
    ring_nf


private abbrev linearTail := H⁻¹*(ex 1-ex 3)
private abbrev constantTail := H⁻¹*(ex 1-2*ex 3)
private theorem h0 : constantCoeff H = 1 := by
  rw [←coeff_zero_eq_constantCoeff_apply]
  simp [H]

private theorem divided_endpoints (q : ℕ) :
    (4:ℚ⟦X⟧) * (X^2 * U q) = ex (2*(q:ℚ))*F + (q:ℚ⟦X⟧)*linearTail + constantTail := by
  have h := congrArg (fun u : ℚ⟦X⟧ ↦ H⁻¹*u) (endpoint_exponential q)
  rw [formalSinh_sq, ←ex_mul (2*(q:ℚ)) 5] at h
  push_cast at h
  have cancel := PowerSeries.mul_inv_cancel H (by rw [h0]; norm_num)
  unfold linearTail constantTail PolygonKernel.F
  change 4*(X^2*U q) = ex (2*(q:ℚ))*(ex 5*H⁻¹) + _ + _
  calc
    _ = H⁻¹*(4*(X^2*H)*U q) := by linear_combination -4*X^2*U q*cancel
    _ = _ := by convert h using 1; ring

/-- Ordinary polynomial in the dilation variable representing four times the
coefficient of s^h in U; the two endpoint terms have degree at most one. -/
def exponentialPolynomial (h : ℕ) : Polynomial ℚ :=
  (∑ i ∈ range (h+3), Polynomial.C (g (h+2-i)*2^i/(i.factorial:ℚ)) * Polynomial.X^i) +
    Polynomial.C (coeff (h+2) linearTail)*Polynomial.X + Polynomial.C (coeff (h+2) constantTail)

private lemma coeff_ex (a : ℚ) (i : ℕ) : coeff i (ex a) = a^i/i.factorial := by
  simp [ex,coeff_rescale,div_eq_mul_inv]

theorem exponentialPolynomial_eval (h q : ℕ) :
    (exponentialPolynomial h).eval (q:ℚ) = 4 * coeff h (U q) := by
  have a := congrArg (coeff (h+2)) (divided_endpoints q)
  have c4 : (4:ℚ⟦X⟧)=C (4:ℚ) := (map_ofNat _ _).symm
  have cq : (q:ℚ⟦X⟧)=C (q:ℚ) := (map_natCast _ _).symm
  rw [c4,coeff_C_mul,coeff_X_pow_mul,map_add,map_add,cq,coeff_C_mul,coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk] at a
  rw [a]
  simp only [exponentialPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_finsetSum,Polynomial.eval_pow,coeff_ex]
  congr 2
  · apply sum_congr rfl
    intro i _
    unfold g
    rw [mul_pow]
    ring
  · ring

private theorem kernel_polynomial_coeff (h r : ℕ) :
    (∑ i ∈ range (h+3), Polynomial.C (g (h+2-i)*2^i/(i.factorial:ℚ)) *
      Polynomial.X^i).coeff r =
    if r ≤ h+2 then g (h+2-r)*2^r/r.factorial else 0 := by
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow]
  simp [mem_range, show r < h+3 ↔ r≤h+2 by omega]

/-- Every index r≥2 is obtained from the correctly shifted true kernel
coefficient (with zero outside support). -/
theorem exponentialPolynomial_high (h r : ℕ) (hr : 2≤r) :
    (exponentialPolynomial h).coeff r =
    if r ≤ h+2 then g (h+2-r)*2^r/r.factorial else 0 := by
  rw [exponentialPolynomial,Polynomial.coeff_add,Polynomial.coeff_add,kernel_polynomial_coeff]
  simp [Polynomial.coeff_C_mul,Polynomial.coeff_X,Polynomial.coeff_C,
    show r≠0 by omega,show 1≠r by omega]


private theorem H_even : rescale (-1) H = H := by
  ext d
  rw [coeff_rescale]
  rcases Nat.even_or_odd' d with ⟨j,rfl|rfl⟩
  · simp
  · simp [H,hCoeff]

private theorem inv_even : rescale (-1) H⁻¹ = H⁻¹ := by
  have cancel := PowerSeries.mul_inv_cancel H (by rw [h0]; norm_num)
  apply mul_left_cancel₀ (show H≠0 by intro eq; have h := h0; rw [eq,map_zero] at h; norm_num at h)
  have e := congrArg (rescale (-1:ℚ)) cancel
  rwa [map_mul,H_even,map_one,←cancel] at e

private theorem linear_even (k : ℕ) : coeff (2*k+2) linearTail = -4/((2*k).factorial:ℚ) := by
  let oddTail := H⁻¹*(ex (-1)-ex 1)
  have hodd : rescale (-1:ℚ) oddTail = -oddTail := by
    simp only [oddTail,map_mul,inv_even,map_sub,ex,rescale_rescale]
    norm_num
    ring
  have coeffzero : coeff (2*k+2) oddTail=0 := by
    have hh := congrArg (coeff (2*k+2)) hodd
    rw [coeff_rescale,map_neg,show (-1:ℚ)^(2*k+2)=1 by
      rw [pow_add,pow_mul]; norm_num] at hh
    linarith
  have shift := sinh_shift 1
  norm_num only [show (1:ℚ)+2 = 3 by norm_num,show (1:ℚ)-2 = -1 by norm_num] at shift
  rw [formalSinh_sq] at shift
  have equation : linearTail = -(4:ℚ⟦X⟧)*(X^2*ex 1)+oddTail := by
    dsimp only [linearTail,oddTail]
    have can := PowerSeries.mul_inv_cancel H (by rw [h0]; norm_num)
    linear_combination H⁻¹*shift - 4*X^2*ex 1*can
  rw [equation,map_add,coeffzero,add_zero,neg_mul,map_neg,
    show (4:ℚ⟦X⟧)=C (4:ℚ) from (map_ofNat _ _).symm,coeff_C_mul,coeff_X_pow_mul,coeff_ex]
  ring

/-- Multiplicity of the removed constant-one crown summand. -/
def endpointCount : Polynomial ℚ :=
  Polynomial.C (1/2:ℚ) * ((Polynomial.X+1)*(Polynomial.X+2))

/-- The endpoint transform of the true centered power ((2m+1)^(2k)−1). -/
def moment (k : ℕ) : Polynomial ℚ :=
  Polynomial.C (((2*k).factorial:ℚ)/4) * exponentialPolynomial (2*k) - endpointCount

/-- Terms of the endpoint correction for ordinary indices r≥1. -/
def correction (r : ℕ) : ℚ := if r=1 then 5/2 else if r=2 then 1/2 else 0

private theorem endpointCount_eq : endpointCount = Polynomial.C (1/2:ℚ)*Polynomial.X^2 +
    Polynomial.C (3/2:ℚ)*Polynomial.X+1 := by
  unfold endpointCount
  have e : Polynomial.C (3/2:ℚ) = 3*Polynomial.C (1/2:ℚ) := by
    rw [←Polynomial.C_ofNat 3,←map_mul]; norm_num
  rw [e]
  have two : (2:Polynomial ℚ)*Polynomial.C (1/2:ℚ)=1 := by
    rw [←Polynomial.C_ofNat 2,←map_mul]; norm_num
  linear_combination two

/-- Ordinary coefficients for the transform of a single centered width power, including
the exceptional first and second coefficients and the finite support cutoff. -/
theorem moment_coeff (k r : ℕ) (hr : 1≤r) :
    (moment k).coeff r =
      (if r ≤ 2*k+2 then ((2*k).factorial:ℚ)/4 * (g (2*k+2-r)*2^r/r.factorial) else 0)
      - correction r := by
  rw [moment,Polynomial.coeff_sub,Polynomial.coeff_C_mul,endpointCount_eq]
  by_cases h1 : r=1
  · subst r
    rw [exponentialPolynomial,Polynomial.coeff_add,Polynomial.coeff_add,
      kernel_polynomial_coeff,if_pos (by omega),Polynomial.coeff_C_mul,linear_even]
    simp [Polynomial.coeff_C_mul,Polynomial.coeff_X,Polynomial.coeff_one,correction]
    field_simp
    ring
  · have h2 : 2 ≤ r := by omega
    rw [exponentialPolynomial_high _ _ h2]
    by_cases h3 : r=2
    · subst r
      simp [Polynomial.coeff_C_mul,Polynomial.coeff_one,
        correction,show 2≤2*k+2 by omega]
    · simp [Polynomial.coeff_C_mul,Polynomial.coeff_X,Polynomial.coeff_one,
        correction,h1,h3,Ne.symm h1,show r≠0 by omega]

end PolygonEndpoint
