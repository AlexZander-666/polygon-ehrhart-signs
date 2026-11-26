import Polygon.NewtonTraceCache

/-! Exact trace and interpolation inputs for the 8-gon. -/
namespace Polygon.Finite64.N08

open NewtonInterpolant

def numerators : List ℤ := [
  6402373705728000,
  61998801861427200,
  283044836900413440,
  811928460590899200,
  1635154994885713920,
  2446772221201397760,
  2814101233215069184,
  2539816676880537600,
  1818047751504890880,
  1034945843521075200,
  467133522853291008,
  166012584797030400,
  45965615829652480,
  9766557510635520,
  1557206532943872,
  179926260940800,
  14207318814720,
  685352632320,
  15230058496
]

def traces : List ℕ := [
  1,
  2207,
  422266,
  22325254,
  538911123,
  7684444237,
  75121981012,
  552936550828,
  3262699677557,
  16128413992171,
  68968383551598,
  261345398253842,
  894010313416903,
  2801354938451801,
  8135100330495912,
  22102901602775128,
  56627006244276137,
  137694654094923127,
  319532169394352098
]

def scale : ℕ := 6402373705728000

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem trace_evaluated : NewtonTraceCache.traceRow 8 19 = traces := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem values_checked : valuesOK 19 scale numerators traces = true := by decide +kernel

private theorem signs_checked : signsOK 8 numerators = true := by decide +kernel

theorem polynomial_eq :
    FaceOrder.ehrhartPolynomial 7 = Small.fromCoeffs (normalized scale numerators) :=
  certify_scaled 7 scale numerators traces (by decide +kernel) (by decide +kernel)
    (NewtonTraceCache.trace_list_certificate 8 19 (by decide) (by decide) trace_evaluated) (valuesOK_sound values_checked)

theorem signs (j : Fin 19) :
    ((FaceOrder.ehrhartPolynomial 7).coeff j.val < 0 ↔ negativeIndex 8 j.val) ∧
      ((FaceOrder.ehrhartPolynomial 7).coeff j.val ≠ 0) :=
  signsOK_sound (by decide +kernel) polynomial_eq signs_checked j

end Polygon.Finite64.N08
