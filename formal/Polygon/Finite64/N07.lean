import Polygon.NewtonTraceCache

/-! Exact trace and interpolation inputs for the 7-gon. -/
namespace Polygon.Finite64.N07

open NewtonInterpolant

def numerators : List ℤ := [
  20922789888000,
  177030049996800,
  703123779778560,
  1732695702151680,
  2958727455495168,
  3705504475836800,
  3509782959912320,
  2552380331621120,
  1432471245261056,
  619592525552000,
  205191794487680,
  51398526699520,
  9543947305984,
  1270852710400,
  114598973440,
  6263111680,
  156577792
]

def traces : List ℕ := [
  1,
  843,
  83635,
  2692756,
  43659386,
  446592076,
  3283191793,
  18829595163,
  88997960754,
  360282191464,
  1284750752750,
  4121573874993,
  12089958221845,
  32843331797619,
  83477154217934,
  200167338448738,
  455927446140543
]

def scale : ℕ := 20922789888000

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem trace_evaluated : NewtonTraceCache.traceRow 7 17 = traces := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem values_checked : valuesOK 17 scale numerators traces = true := by decide +kernel

private theorem signs_checked : signsOK 7 numerators = true := by decide +kernel

theorem polynomial_eq :
    FaceOrder.ehrhartPolynomial 6 = Small.fromCoeffs (normalized scale numerators) :=
  certify_scaled 6 scale numerators traces (by decide +kernel) (by decide +kernel)
    (NewtonTraceCache.trace_list_certificate 7 17 (by decide) (by decide) trace_evaluated) (valuesOK_sound values_checked)

theorem signs (j : Fin 17) :
    ((FaceOrder.ehrhartPolynomial 6).coeff j.val < 0 ↔ negativeIndex 7 j.val) ∧
      ((FaceOrder.ehrhartPolynomial 6).coeff j.val ≠ 0) :=
  signsOK_sound (by decide +kernel) polynomial_eq signs_checked j

end Polygon.Finite64.N07
