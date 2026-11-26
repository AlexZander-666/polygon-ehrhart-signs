import Polygon.NewtonTraceCache

/-! Exact trace and interpolation inputs for the 6-gon. -/
namespace Polygon.Finite64.N06

open NewtonInterpolant

def numerators : List ℤ := [
  87178291200,
  632867074560,
  2128261658112,
  4385257793280,
  6163078067328,
  6218323631520,
  4619256209568,
  2553984713280,
  1052540009664,
  321160039200,
  71388084768,
  11215626240,
  1178731008,
  74296320,
  2122752
]

def traces : List ℕ := [
  1,
  322,
  16565,
  324787,
  3537032,
  25954363,
  143491522,
  641220510,
  2427636903,
  8048123548,
  23932518871,
  64999798097,
  163496233966,
  385058712533,
  856590060388
]

def scale : ℕ := 87178291200

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem trace_evaluated : NewtonTraceCache.traceRow 6 15 = traces := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem values_checked : valuesOK 15 scale numerators traces = true := by decide +kernel

private theorem signs_checked : signsOK 6 numerators = true := by decide +kernel

theorem polynomial_eq :
    FaceOrder.ehrhartPolynomial 5 = Small.fromCoeffs (normalized scale numerators) :=
  certify_scaled 5 scale numerators traces (by decide +kernel) (by decide +kernel)
    (NewtonTraceCache.trace_list_certificate 6 15 (by decide) (by decide) trace_evaluated) (valuesOK_sound values_checked)

theorem signs (j : Fin 15) :
    ((FaceOrder.ehrhartPolynomial 5).coeff j.val < 0 ↔ negativeIndex 6 j.val) ∧
      ((FaceOrder.ehrhartPolynomial 5).coeff j.val ≠ 0) :=
  signsOK_sound (by decide +kernel) polynomial_eq signs_checked j

end Polygon.Finite64.N06
