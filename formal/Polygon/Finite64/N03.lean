import Polygon.NewtonTraceCache

/-! Exact trace and interpolation inputs for the 3-gon. -/
namespace Polygon.Finite64.N03

open NewtonInterpolant

def numerators : List ℤ := [
  40320,
  150240,
  238848,
  212520,
  115752,
  39480,
  8232,
  960,
  48
]

def traces : List ℕ := [
  1,
  18,
  129,
  571,
  1884,
  5103,
  11998,
  25362,
  49347
]

def scale : ℕ := 40320

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem trace_evaluated : NewtonTraceCache.traceRow 3 9 = traces := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem values_checked : valuesOK 9 scale numerators traces = true := by decide +kernel

private theorem signs_checked : signsOK 3 numerators = true := by decide +kernel

theorem polynomial_eq :
    FaceOrder.ehrhartPolynomial 2 = Small.fromCoeffs (normalized scale numerators) :=
  certify_scaled 2 scale numerators traces (by decide +kernel) (by decide +kernel)
    (NewtonTraceCache.trace_list_certificate 3 9 (by decide) (by decide) trace_evaluated) (valuesOK_sound values_checked)

theorem signs (j : Fin 9) :
    ((FaceOrder.ehrhartPolynomial 2).coeff j.val < 0 ↔ negativeIndex 3 j.val) ∧
      ((FaceOrder.ehrhartPolynomial 2).coeff j.val ≠ 0) :=
  signsOK_sound (by decide +kernel) polynomial_eq signs_checked j

end Polygon.Finite64.N03
