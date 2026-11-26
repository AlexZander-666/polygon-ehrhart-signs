import Polygon.NewtonTraceCache

/-! Exact trace and interpolation inputs for the 4-gon. -/
namespace Polygon.Finite64.N04

open NewtonInterpolant

def numerators : List ℤ := [
  3628800,
  17663040,
  38200608,
  48155200,
  39009520,
  21154560,
  7766304,
  1905600,
  299280,
  27200,
  1088
]

def traces : List ℕ := [
  1,
  47,
  650,
  4726,
  23219,
  87677,
  274132,
  743724,
  1806597,
  4016683,
  8306078
]

def scale : ℕ := 3628800

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem trace_evaluated : NewtonTraceCache.traceRow 4 11 = traces := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem values_checked : valuesOK 11 scale numerators traces = true := by decide +kernel

private theorem signs_checked : signsOK 4 numerators = true := by decide +kernel

theorem polynomial_eq :
    FaceOrder.ehrhartPolynomial 3 = Small.fromCoeffs (normalized scale numerators) :=
  certify_scaled 3 scale numerators traces (by decide +kernel) (by decide +kernel)
    (NewtonTraceCache.trace_list_certificate 4 11 (by decide) (by decide) trace_evaluated) (valuesOK_sound values_checked)

theorem signs (j : Fin 11) :
    ((FaceOrder.ehrhartPolynomial 3).coeff j.val < 0 ↔ negativeIndex 4 j.val) ∧
      ((FaceOrder.ehrhartPolynomial 3).coeff j.val ≠ 0) :=
  signsOK_sound (by decide +kernel) polynomial_eq signs_checked j

end Polygon.Finite64.N04
