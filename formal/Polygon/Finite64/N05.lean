import Polygon.NewtonTraceCache

/-! Exact trace and interpolation inputs for the 5-gon. -/
namespace Polygon.Finite64.N05

open NewtonInterpolant

def numerators : List ℤ := [
  479001600,
  2899324800,
  8009436960,
  13282288800,
  14637733880,
  11233675200,
  6132509680,
  2394136800,
  662886840,
  126984000,
  15991360,
  1190400,
  39680
]

def traces : List ℕ := [
  1,
  123,
  3281,
  39175,
  286555,
  1508401,
  6271378,
  21836366,
  66220705,
  179784715,
  445824731,
  1025102013,
  2211041131
]

def scale : ℕ := 479001600

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem trace_evaluated : NewtonTraceCache.traceRow 5 13 = traces := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem values_checked : valuesOK 13 scale numerators traces = true := by decide +kernel

private theorem signs_checked : signsOK 5 numerators = true := by decide +kernel

theorem polynomial_eq :
    FaceOrder.ehrhartPolynomial 4 = Small.fromCoeffs (normalized scale numerators) :=
  certify_scaled 4 scale numerators traces (by decide +kernel) (by decide +kernel)
    (NewtonTraceCache.trace_list_certificate 5 13 (by decide) (by decide) trace_evaluated) (valuesOK_sound values_checked)

theorem signs (j : Fin 13) :
    ((FaceOrder.ehrhartPolynomial 4).coeff j.val < 0 ↔ negativeIndex 5 j.val) ∧
      ((FaceOrder.ehrhartPolynomial 4).coeff j.val ≠ 0) :=
  signsOK_sound (by decide +kernel) polynomial_eq signs_checked j

end Polygon.Finite64.N05
