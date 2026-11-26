import Polygon.BinomialTrace
import Polygon.WidthSpectrum
import Mathlib.RingTheory.PowerSeries.Log

/-! The original polygon transfer traces as the logarithmic derivative of det(I−zT). -/
namespace Polygon.TraceSeries
open Finset
open scoped PowerSeries

/-- The unchanged reverse characteristic polynomial, coerced to a formal power series. -/
noncomputable def detSeries (m : ℕ) : PowerSeries ℝ :=
  ((TransferSpectrum.realTransfer m).charpolyRev : Polynomial ℝ)

/-- The constant term is the trace of T itself; the exponent is one less than its power. -/
noncomputable def traces (m : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun j ↦ (Cert.traceCount (j+1) m : ℝ)

theorem coeff_det (m j : ℕ) : PowerSeries.coeff j (detSeries m) =
    (-1:ℝ)^j * (Nat.choose (m+j) (2*j) : ℝ) := by
  rw [detSeries,Polynomial.coeff_coe]
  exact BinomialContinuant.reverse_coeff m j

theorem coeff_traces (m j : ℕ) : PowerSeries.coeff j (traces m) =
    (Cert.traceCount (j+1) m : ℝ) := PowerSeries.coeff_mk _ _

theorem constant_det (m : ℕ) : PowerSeries.constantCoeff (detSeries m) = 1 := by
  rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply,coeff_det]
  simp

private theorem interior (d p : ℕ → ℝ) (n : ℕ) :
    (∑ a ∈ (antidiagonal (n+1)).filter (fun a : ℕ × ℕ ↦ a.1 ∈ Set.Ioo 0 (n+1)),
      d a.1 * p a.2) =
    (∑ a ∈ antidiagonal n, d a.1*p (a.2+1)) - d 0*p (n+1) := by
  rw [sum_filter, Nat.sum_antidiagonal_succ']
  simp only [Set.mem_Ioo, lt_self_iff_false, and_false, if_false, zero_add]
  have s : (∑ a ∈ antidiagonal n, d a.1 * p (a.2+1)) =
      ∑ a ∈ antidiagonal n, ((if 0 < a.1 ∧ a.1 < n+1 then d a.1*p (a.2+1) else 0) +
       (if a=(0,n) then d 0*p (n+1) else 0)) := by
    apply sum_congr rfl
    rintro ⟨i,j⟩ hij
    have := mem_antidiagonal.mp hij
    change i+j=n at this
    by_cases h : i=0
    · subst i
      simp_all
    · simp [h,(show 0 < i by omega), (show i < n+1 by omega)]
  rw [s,sum_add_distrib]
  simp

/-- Every coefficient of the formal differential identity, before division by D. -/
theorem newton_coefficient (m n : ℕ) :
    (∑ a ∈ antidiagonal n, PowerSeries.coeff a.1 (detSeries m) *
      (Cert.traceCount (a.2+1) m : ℝ)) =
    -(PowerSeries.coeff (n+1) (detSeries m) * ((n:ℝ)+1)) := by
  have hw : (Cert.traceCount (n+1) m : ℝ) =
      (-1:ℝ)^(n+1+1)*(n+1 : ℕ)*(Nat.choose (m+(n+1)) (2*(n+1)) : ℝ) -
      ∑ a ∈ (antidiagonal (n+1)).filter (fun a : ℕ × ℕ ↦ a.1 ∈ Set.Ioo 0 (n+1)),
        (-1:ℝ)^a.1*(Nat.choose (m+a.1) (2*a.1) : ℝ)*(Cert.traceCount a.2 m : ℝ) := by
    exact_mod_cast BinomialTrace.trace_integer m (n+1) (by omega)
  have hi := interior (fun j ↦ (-1:ℝ)^j*(Nat.choose (m+j) (2*j):ℝ))
    (fun j ↦ (Cert.traceCount j m:ℝ)) n
  simp only [pow_zero, Nat.add_zero, Nat.mul_zero, Nat.choose_zero_right, Nat.cast_one,
    mul_one, one_mul] at hi
  rw [hi] at hw
  simp only [coeff_det]
  rw [pow_succ (-1:ℝ) (n+1), Nat.cast_succ] at hw
  linarith

/-- D(z) times the shifted integer trace series equals minus its formal derivative. -/
theorem determinant_times_traces (m : ℕ) :
    detSeries m * traces m = -(PowerSeries.derivative ℝ (detSeries m)) := by
  ext n
  rw [PowerSeries.coeff_mul, map_neg, PowerSeries.coeff_derivative]
  simpa only [coeff_traces] using newton_coefficient m n


private theorem log_derivative_unit :
    (1+PowerSeries.X : PowerSeries ℝ) * PowerSeries.derivative ℝ (PowerSeries.log ℝ) = 1 := by
  rw [add_mul,one_mul,PowerSeries.deriv_log]
  ext n
  cases n with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    have hx (f : PowerSeries ℝ) : PowerSeries.coeff (n+1) (PowerSeries.X*f) =
        PowerSeries.coeff n f := by simp
    rw [map_add,hx,PowerSeries.coeff_mk,PowerSeries.coeff_mk]
    simp [pow_succ]

/-- The derivative of Mathlib's formal logarithm after substitution of a unit
series having constant term one. -/
theorem times_derivative_logOf {f : PowerSeries ℝ} (hf : PowerSeries.constantCoeff f = 1) :
    f * PowerSeries.derivative ℝ (PowerSeries.logOf f) = PowerSeries.derivative ℝ f := by
  have subok : PowerSeries.HasSubst (f-1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by rw [map_sub,hf,map_one,sub_self])
  let A : PowerSeries ℝ →ₐ[ℝ] PowerSeries ℝ := PowerSeries.substAlgHom subok
  have ha (q : PowerSeries ℝ) : A q = q.subst (f-1) :=
    congrFun (PowerSeries.coe_substAlgHom subok) q
  have hx : A PowerSeries.X = f-1 := (ha _).trans (PowerSeries.subst_X subok)
  have h := congrArg A log_derivative_unit
  rw [map_mul,map_add,map_one,hx,add_sub_cancel,ha] at h
  rw [PowerSeries.logOf_eq,PowerSeries.derivative_subst subok,map_sub,PowerSeries.derivative_one,
    sub_zero,←mul_assoc]
  rw [h,one_mul]

/-- Formal logarithmic derivative, including the empty-width determinant. -/
theorem derivative_neg_logDet (m : ℕ) :
    PowerSeries.derivative ℝ (-PowerSeries.logOf (detSeries m)) = traces m := by
  have nz : detSeries m ≠ 0 := by
    intro h
    have eqn := constant_det m
    rw [h,map_zero] at eqn
    exact zero_ne_one eqn
  apply mul_left_cancel₀ nz
  rw [map_neg,mul_neg,times_derivative_logOf (constant_det m),determinant_times_traces]

/-- The positive-degree coefficient of minus log det(I−zT) is the original trace divided by k. -/
theorem coeff_neg_logDet {k : ℕ} (hk : 0<k) (m : ℕ) :
    PowerSeries.coeff k (-PowerSeries.logOf (detSeries m)) = (Cert.traceCount k m : ℝ)/k := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have h := congrArg (PowerSeries.coeff n) (derivative_neg_logDet m)
  rw [PowerSeries.coeff_derivative,coeff_traces] at h
  apply (eq_div_iff (by positivity)).2
  simpa only [Nat.cast_succ] using h

/-- The complete formal logarithm is normalized with constant term zero. -/
theorem neg_logDet_trace_series (m : ℕ) : -PowerSeries.logOf (detSeries m) =
    PowerSeries.mk (fun | 0 => 0 | k+1 => (Cert.traceCount (k+1) m : ℝ)/(k+1 : ℕ)) := by
  ext k
  rw [PowerSeries.coeff_mk]
  cases k with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.constantCoeff_logOf (constant_det m)]
  | succ k => exact coeff_neg_logDet (by omega) m

/-- At every positive power, multiply the log coefficient by the side count to
obtain the width difference of the actual polygon-face Ehrhart polynomial. -/
theorem geometric_log_coefficient {n : ℕ} (hn : 3 ≤ n) (m : ℕ) :
    let E := GeneralRealization.geometricEhrhart (n-3)
    (n:ℝ)*PowerSeries.coeff n (-PowerSeries.logOf (detSeries m)) =
      ((E.eval ((m:ℚ)-1) - 2*E.eval ((m:ℚ)-2) + E.eval ((m:ℚ)-3) : ℚ) : ℝ) := by
  dsimp only
  rw [WidthSpectrum.geometric_width_trace hn,coeff_neg_logDet (by omega : 0<n)]
  push_cast
  field_simp [show (n:ℝ) ≠ 0 by exact_mod_cast (by omega : n ≠ 0)]

/-- An empty matrix has determinant one and contributes no positive trace powers. -/
theorem empty_width : detSeries 0 = 1 ∧ traces 0 = 0 := by
  constructor
  · ext n
    cases n with
    | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff_apply,constant_det]
    | succ k =>
      rw [coeff_det, Nat.choose_eq_zero_of_lt (by omega : 0+(k+1)<2*(k+1))]
      simp
  · ext n
    simp [coeff_traces,Cert.traceCount_correct,Matrix.trace]

#print axioms determinant_times_traces
#print axioms derivative_neg_logDet
#print axioms coeff_neg_logDet
#print axioms neg_logDet_trace_series
#print axioms geometric_log_coefficient
#print axioms empty_width
end Polygon.TraceSeries
