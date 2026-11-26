import Polygon.TraceSeries
import Mathlib.RingTheory.PowerSeries.WellKnown

/-! Formal trigonometric identities for the actual polygon transfer determinant. -/
namespace Polygon.FormalCosine
open PowerSeries
open scoped PowerSeries

noncomputable abbrev cosAt (a : ℝ) := rescale a (cos ℝ)
noncomputable abbrev sinAt (a : ℝ) := rescale a (sin ℝ)

private theorem sin_derivative : derivative ℝ (sin ℝ) = cos ℝ := by
  ext n
  rw [coeff_derivative]
  rcases Nat.even_or_odd' n with ⟨k,rfl | rfl⟩
  · simp [sin,cos,Nat.factorial_succ, (show (2*k+1)/2=k by omega)]
    field_simp
  · simp [sin,cos,(show Even (2*k+1+1) from ⟨k+1,by omega⟩)]

private theorem cos_derivative : derivative ℝ (cos ℝ) = -(sin ℝ) := by
  ext n
  rw [coeff_derivative,map_neg]
  rcases Nat.even_or_odd' n with ⟨k,rfl | rfl⟩
  · simp [sin,cos]
  · simp [sin,cos,(show Even (2*k+1+1) from ⟨k+1,by omega⟩),
      (show (2*k+1+1)/2=k+1 by omega), (show (2*k+1)/2=k by omega),
      Nat.factorial_succ,pow_succ]
    field_simp

private theorem scaled_derivative (a : ℝ) (f : PowerSeries ℝ) :
    derivative ℝ (rescale a f) = C a * rescale a (derivative ℝ f) := by
  ext n
  simp only [coeff_derivative,coeff_rescale,coeff_C_mul,pow_succ]
  ring

private theorem cosAt_derivative (a : ℝ) :
    derivative ℝ (cosAt a) = -C a * sinAt a := by
  rw [cosAt,scaled_derivative,cos_derivative,map_neg]
  ring

private theorem sinAt_derivative (a : ℝ) :
    derivative ℝ (sinAt a) = C a * cosAt a := by
  rw [sinAt,scaled_derivative,sin_derivative]


private lemma at_zero (a : ℝ) :
    constantCoeff (cosAt a) = 1 ∧ constantCoeff (sinAt a) = 0 := by
  simp [←coeff_zero_eq_constantCoeff_apply,coeff_rescale,cos,sin]

private theorem zero_solution (a : ℝ) {f g : PowerSeries ℝ}
    (hf : derivative ℝ f = -C a*g) (hg : derivative ℝ g = C a*f)
    (f0 : constantCoeff f = 0) (g0 : constantCoeff g = 0) : f=0 ∧ g=0 := by
  suffices pair : ∀ n, coeff n f = 0 ∧ coeff n g = 0 by
    exact ⟨PowerSeries.ext (fun n ↦ by simpa using (pair n).1),
      PowerSeries.ext (fun n ↦ by simpa using (pair n).2)⟩
  intro n
  induction n with
  | zero => simpa [coeff_zero_eq_constantCoeff_apply] using And.intro f0 g0
  | succ n ih =>
    have h1 := congrArg (coeff n) hf
    have h2 := congrArg (coeff n) hg
    rw [coeff_derivative,neg_mul,map_neg,coeff_C_mul,ih.2,mul_zero,neg_zero] at h1
    rw [coeff_derivative,coeff_C_mul,ih.1,mul_zero] at h2
    exact ⟨(mul_eq_zero.mp h1).resolve_right (by positivity),
      (mul_eq_zero.mp h2).resolve_right (by positivity)⟩

/-- Angle addition for the existing Mathlib formal sine and cosine. -/
theorem add_angles (a b : ℝ) :
    cosAt (a+b) = cosAt a*cosAt b-sinAt a*sinAt b ∧
    sinAt (a+b) = sinAt a*cosAt b+cosAt a*sinAt b := by
  have h := zero_solution (a+b) (f := cosAt (a+b) - (cosAt a*cosAt b-sinAt a*sinAt b))
    (g := sinAt (a+b) - (sinAt a*cosAt b+cosAt a*sinAt b))
  apply And.imp sub_eq_zero.mp sub_eq_zero.mp
  apply h
  · simp only [map_sub,map_add,Derivation.leibniz,smul_eq_mul,cosAt_derivative,sinAt_derivative]
    ring
  · simp only [map_sub,map_add,Derivation.leibniz,smul_eq_mul,cosAt_derivative,sinAt_derivative]
    ring
  · simp [(at_zero _).1,(at_zero _).2]
  · simp [(at_zero _).1,(at_zero _).2]

private theorem eq_of_diff_eq {f g : PowerSeries ℝ} (h : derivative ℝ f = derivative ℝ g)
    (h0 : constantCoeff f=constantCoeff g) : f=g := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simpa [coeff_zero_eq_constantCoeff_apply] using h0
  | succ n =>
    have h1 := congrArg (coeff n) h
    simp only [coeff_derivative] at h1
    exact mul_right_cancel₀ (by positivity : (n:ℝ)+1 ≠ 0) h1

/-- The formal Pythagorean identity. -/
theorem square_sum (a : ℝ) : cosAt a ^ 2 + sinAt a ^ 2 = 1 := by
  apply eq_of_diff_eq
  · simp only [pow_two,map_add,Derivation.leibniz,smul_eq_mul,cosAt_derivative,sinAt_derivative,
      derivative_one]
    ring
  · simp [(at_zero _).1,(at_zero _).2]

private lemma twoStep (a b : ℝ) :
    cosAt (a+b+b) = 2*cosAt b*cosAt (a+b)-cosAt a := by
  rw [(add_angles (a+b) b).1,(add_angles a b).1,(add_angles a b).2]
  linear_combination -cosAt a * square_sum b


/-- The substitution parameter in the determinant identity; it has constant term zero. -/
noncomputable def parameter : PowerSeries ℝ := 4*(sin ℝ)^2

theorem parameter_zero : constantCoeff parameter = 0 := by
  have h := (at_zero 1).2
  simp [sinAt,rescale_one] at h
  simp [parameter,h]

theorem parameter_hasSubst : HasSubst parameter := HasSubst.of_constantCoeff_zero' parameter_zero

private theorem det_poly (m : ℕ) : (TransferSpectrum.realTransfer m).charpolyRev =
    (BinomialContinuant.positive m).comp (Polynomial.C (-1)*Polynomial.X) := by
  ext i
  rw [Polynomial.comp_C_mul_X_coeff, BinomialContinuant.coefficient]
  exact (BinomialContinuant.reverse_coeff m i).trans (mul_comm ..)

private theorem det_aeval (m : ℕ) : (TraceSeries.detSeries m).subst parameter =
    Polynomial.aeval (-parameter) (BinomialContinuant.positive m) := by
  rw [TraceSeries.detSeries,subst_coe parameter_hasSubst,det_poly,Polynomial.aeval_comp]
  simp

private lemma cos_two : 2*cosAt 2 = 2-parameter := by
  have e := (add_angles 1 1).1
  norm_num [cosAt,sinAt,rescale_one] at e
  have u := square_sum 1
  simp [cosAt,sinAt,rescale_one] at u
  unfold parameter cosAt
  linear_combination 2*e + 2*u

/-- The original reversed characteristic determinant, after substituting
4 sin(θ)², multiplied by cos θ, is cos((2m+1)θ) as formal power series. -/
theorem determinant_cos (m : ℕ) :
    (TraceSeries.detSeries m).subst parameter * cos ℝ = cosAt (2*(m:ℝ)+1) := by
  rw [det_aeval]
  induction m using Nat.twoStepInduction with
  | zero => simp [BinomialContinuant.positive,cosAt,rescale_one]
  | one =>
    have base := twoStep 1 1
    have double := cos_two
    norm_num [cosAt,sinAt,rescale_one] at base double ⊢
    simp only [BinomialContinuant.positive,map_add,map_one,Polynomial.aeval_X]
    linear_combination -base - cos ℝ * double
  | more m a b =>
    rw [BinomialContinuant.positive,map_sub,map_mul,map_add,Polynomial.aeval_C,Polynomial.aeval_X,
      sub_mul,mul_assoc,b,a]
    have step := twoStep (2*(m:ℝ)+1) 2
    push_cast
    change (2-parameter)*cosAt (2*((m:ℝ)+1)+1) - cosAt (2*(m:ℝ)+1) = _
    rw [←cos_two]
    have u : 2*(m:ℝ)+1+2=2*((m:ℝ)+1)+1 := by ring
    have v : 2*((m:ℝ)+1)+1+2=2*((m:ℝ)+2)+1 := by ring
    simpa only [u,v] using step.symm


private theorem normalized_ne_zero {f : PowerSeries ℝ} (h : constantCoeff f = 1) : f ≠ 0 := by
  intro z
  rw [z,map_zero] at h
  exact zero_ne_one h

/-- The formal logarithm of the product of two normalized real series. -/
theorem logOf_mul {f g : PowerSeries ℝ} (hf : constantCoeff f=1) (hg : constantCoeff g=1) :
    logOf (f*g) = logOf f + logOf g := by
  have hm : constantCoeff (f*g)=1 := by rw [map_mul,hf,hg,one_mul]
  apply eq_of_diff_eq
  · apply mul_left_cancel₀ (normalized_ne_zero hm)
    rw [TraceSeries.times_derivative_logOf hm,Derivation.leibniz,map_add]
    simp only [smul_eq_mul]
    linear_combination -g * TraceSeries.times_derivative_logOf hf -
      f * TraceSeries.times_derivative_logOf hg
  · simp [constantCoeff_logOf hf,constantCoeff_logOf hg,constantCoeff_logOf hm]

/-- Substitution at a series of zero constant term commutes with the normalized formal log. -/
theorem logOf_subst {f a : PowerSeries ℝ} (hf : constantCoeff f=1) (ha : HasSubst a) :
    logOf (f.subst a) = (logOf f).subst a := by
  have h : HasSubst (f-1) := HasSubst.of_constantCoeff_zero' (by rw [map_sub,hf,map_one,sub_self])
  have one : (1 : PowerSeries ℝ).subst a = 1 := by rw [← coe_substAlgHom ha,map_one]
  simp only [logOf_eq,subst_comp_subst_apply h ha,subst_sub ha,one]

private lemma cos0 : constantCoeff (cos ℝ)=1 := by
  simpa [cosAt,rescale_one] using (at_zero 1).1

/-- Coefficients of this one universal series are the formal log-secant coefficients. -/
noncomputable def logSec : PowerSeries ℝ := -logOf (cos ℝ)

/-- Formal trace logarithm after the sine substitution, using a single universal log-secant. -/
theorem centered_log (m : ℕ) :
    (-logOf (TraceSeries.detSeries m)).subst parameter =
      rescale (2*(m:ℝ)+1) logSec - logSec := by
  have h := determinant_cos m
  have c := congrArg constantCoeff h
  rw [map_mul,cos0,mul_one,(at_zero _).1] at c
  have l := congrArg logOf h
  rw [logOf_mul c cos0,cosAt,rescale_eq_subst,logOf_subst cos0 (HasSubst.smul_X' _),
    ←rescale_eq_subst,logOf_subst (TraceSeries.constant_det m) parameter_hasSubst] at l
  unfold logSec
  rw [map_neg,←coe_substAlgHom parameter_hasSubst,map_neg]
  rw [coe_substAlgHom]
  linear_combination -l

/-- Centered powers obtained directly from the negative logarithm of the original
matrix determinant; the offset index is the actual coefficient index. -/
theorem centered_coefficient (m j : ℕ) :
    coeff j ((-logOf (TraceSeries.detSeries m)).subst parameter) =
      ((2*(m:ℝ)+1)^j-1)*coeff j logSec := by
  rw [centered_log,map_sub,coeff_rescale]
  ring

/-- The original integer traces after substitution give the centered even powers in the manuscript. -/
theorem trace_centered_even (m k : ℕ) :
    coeff (2*k) ((PowerSeries.mk (fun
      | 0 => (0:ℝ)
      | j+1 => (Cert.traceCount (j+1) m : ℝ)/(j+1 : ℕ))).subst parameter) =
    ((2*(m:ℝ)+1)^(2*k)-1)*coeff (2*k) logSec := by
  exact (congrArg (fun f : PowerSeries ℝ ↦ coeff (2*k) (f.subst parameter))
    (TraceSeries.neg_logDet_trace_series m).symm).trans (centered_coefficient m (2*k))


private lemma sin_first : IsUnit (coeff 1 (sin ℝ)) := by norm_num [sin]
private lemma sin_zero : constantCoeff (sin ℝ) = 0 := by
  simpa [sinAt,rescale_one] using (at_zero 1).2

/-- The unique normalized formal compositional inverse of the conventional sine. -/
noncomputable def inverseSine : PowerSeries ℝ := (sin ℝ).substInvOfIsUnit sin_first

theorem sine_inverse : (sin ℝ).subst inverseSine = X :=
  subst_substInvOfIsUnit_right (sin ℝ) sin_zero sin_first

private lemma inverse_ok : HasSubst inverseSine := HasSubst.substInvOfIsUnit _ _

private lemma parameter_inverse : parameter.subst inverseSine = 4*X^2 := by
  let A : PowerSeries ℝ →ₐ[ℝ] PowerSeries ℝ := substAlgHom inverse_ok
  have ha (q : PowerSeries ℝ) : A q = q.subst inverseSine := congrFun (coe_substAlgHom _) q
  rw [← ha,parameter,map_mul,map_ofNat,map_pow,ha,sine_inverse]

/-- Inverting sine formally gives the trace logarithm directly in powers of 4w². -/
theorem inverse_centered_log (m : ℕ) :
    (-logOf (TraceSeries.detSeries m)).subst (4*X^2 : PowerSeries ℝ) =
      (rescale (2*(m:ℝ)+1) logSec-logSec).subst inverseSine := by
  have h := congrArg (fun f : PowerSeries ℝ ↦ f.subst inverseSine) (centered_log m)
  simpa only [subst_comp_subst_apply parameter_hasSubst inverse_ok,parameter_inverse] using h

private lemma even_substitution (f : PowerSeries ℝ) (n : ℕ) :
    coeff (2*n) (f.subst (4*X^2 : PowerSeries ℝ)) = 4^n*coeff n f := by
  have hx : HasSubst (X^2 : PowerSeries ℝ) := HasSubst.X_pow (by norm_num)
  have hx2 : ((4:ℝ) • (X : PowerSeries ℝ)).subst (X^2 : PowerSeries ℝ) = 4*X^2 := by
    let A : PowerSeries ℝ →ₐ[ℝ] PowerSeries ℝ := substAlgHom hx
    have ha (q : PowerSeries ℝ) : A q = q.subst (X^2 : PowerSeries ℝ) :=
      congrFun (coe_substAlgHom _) q
    rw [←ha,map_smul,ha,subst_X hx]
    rw [Algebra.smul_def]
    norm_num
    exact map_ofNat _ _
  have hs : (rescale 4 f).subst (X^2 : PowerSeries ℝ) = f.subst (4*X^2 : PowerSeries ℝ) := by
    rw [rescale_eq_subst,subst_comp_subst_apply (HasSubst.smul_X' _) hx,hx2]
  rw [←hs,coeff_subst_X_pow (by norm_num : (2:ℕ) ≠ 0)]
  simp [coeff_rescale]

private lemma coeff_subst_finite {a : PowerSeries ℝ} (h0 : constantCoeff a=0)
    (f : PowerSeries ℝ) (j : ℕ) : coeff j (f.subst a) =
      ∑ i ∈ Finset.range (j+1), coeff i f * coeff j (a^i) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' h0)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply Finset.mem_range.mpr
  by_contra! h
  have hlt : (j : ℕ∞) < (i : ℕ∞) := by exact_mod_cast (show j < i by omega)
  have he := coeff_of_lt_order j ((hlt.trans_le (le_order_pow_of_constantCoeff_eq_zero i h0)))
  exact hi (by simp [he])

private lemma rescale_neg_one : rescale (-1) (cos ℝ) = cos ℝ := by
  ext n
  rw [coeff_rescale]
  rcases Nat.even_or_odd' n with ⟨k,rfl|rfl⟩ <;> simp [cos]

theorem logSec_odd (k : ℕ) : coeff (2*k+1) logSec = 0 := by
  have h : rescale (-1) logSec = logSec := by
    rw [logSec,map_neg,rescale_eq_subst,←logOf_subst cos0 (HasSubst.smul_X' _),
      ←rescale_eq_subst,rescale_neg_one]
  have hc := congrArg (coeff (2*k+1)) h
  rw [coeff_rescale] at hc
  rw [show (-1:ℝ)^(2*k+1) = -1 by rw [pow_succ,pow_mul]; norm_num] at hc
  linarith

private theorem skip_odd (f : ℕ → ℝ) (h : ∀ k, f (2*k+1)=0) (n : ℕ) :
    ∑ k ∈ Finset.range (2*n+1), f k = ∑ k ∈ Finset.range (n+1), f (2*k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)+1 = (2*n+1)+1+1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ _ (2*n+1), h,add_zero,ih,Finset.sum_range_succ _ (n+1)]
    congr 1

/-- The finite centered trace expansion, with b_{n,k} defined from the formal inverse sine. -/
theorem trace_centered_sum {n : ℕ} (hn : 0<n) (m : ℕ) :
    4^n*((Cert.traceCount n m : ℝ)/n) =
      ∑ k ∈ Finset.range (n+1), ((2*(m:ℝ)+1)^(2*k)-1)*coeff (2*k) logSec*
        coeff (2*n) (inverseSine^(2*k)) := by
  have r := congrArg (coeff (2*n)) (inverse_centered_log m)
  rw [even_substitution,TraceSeries.coeff_neg_logDet hn,
    coeff_subst_finite (show constantCoeff inverseSine = 0 from constantCoeff_substInvOfIsUnit _ _)] at r
  simp only [map_sub,coeff_rescale] at r
  rw [skip_odd _ (fun k ↦ by rw [logSec_odd,mul_zero,sub_zero,zero_mul])] at r
  convert r using 1
  apply Finset.sum_congr rfl
  intro k _
  ring


/-- The complete crown polynomial in the inclusive width variable is the finite
linear combination of genuine centered powers; it agrees at every real width. -/
theorem crown_centered_polynomial {n : ℕ} (hn : 0 < n) :
    Polynomial.C ((4:ℝ)^n/n) * (WidthSpectrum.crownPolynomial (n-1)).map (Rat.castHom ℝ) =
      ∑ k ∈ Finset.range (n+1), (((2*Polynomial.X+1 : Polynomial ℝ)^(2*k)-1) *
        Polynomial.C (coeff (2*k) logSec * coeff (2*n) (inverseSine^(2*k)))) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℝ))).mono
  rintro _ ⟨m,rfl⟩
  have c : ((WidthSpectrum.crownPolynomial (n-1)).map (Rat.castHom ℝ)).eval (m:ℝ) =
      (Cert.traceCount n m:ℝ) := by
    have h := Polynomial.eval_map_apply (p:=WidthSpectrum.crownPolynomial (n-1))
      (f:=Rat.castHom ℝ) (m:ℚ)
    rw [WidthSpectrum.crown_eval_trace, show n-1+1=n by omega] at h
    exact_mod_cast h
  simp only [Set.mem_ofPred_eq,Polynomial.eval_mul,Polynomial.eval_C,c,Polynomial.eval_finsetSum,
    Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_ofNat,
    Polynomial.eval_X,Polynomial.eval_one]
  simpa only [←mul_assoc,div_mul_eq_mul_div,mul_div_assoc] using trace_centered_sum hn m

#print axioms add_angles
#print axioms determinant_cos
#print axioms centered_log
#print axioms trace_centered_even
#print axioms sine_inverse
#print axioms inverse_centered_log
#print axioms trace_centered_sum
#print axioms crown_centered_polynomial
end Polygon.FormalCosine
