import Polygon.NewtonTraceCache

/-! Exact trace and interpolation inputs for the 9-gon. -/
namespace Polygon.Finite64.N09

open NewtonInterpolant

def numerators : List ℤ := [
  2432902008176640000,
  26398579449876480000,
  137365302355362201600,
  449034555906532362240,
  1037820614793901876224,
  1806117609426773184000,
  2448749341045693382400,
  2639716352364029114880,
  2294047143272528895744,
  1620916683615777600000,
  933524841963120825600,
  436911070457185758720,
  164996601604929978624,
  49775836168899072000,
  11842633861131571200,
  2184873961739304960,
  305233372059162624,
  31147840272384000,
  2187464796979200,
  94439404339200,
  1888788086784
]

def traces : List ℕ := [
  1,
  5778,
  2131986,
  185095534,
  6652069455,
  132225131448,
  1718849681938,
  16237146130254,
  119611855006038,
  722005671255193,
  3702382563441006,
  16571686299458898,
  66108961363819936,
  238940157097961643,
  792790188752665908,
  2440649644434359884,
  7033176908228349063,
  19110924804311410068,
  49269584621379102130,
  121150218635569655694,
  285412641777626644821
]

def scale : ℕ := 2432902008176640000

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem trace_evaluated : NewtonTraceCache.traceRow 9 21 = traces := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem values_checked : valuesOK 21 scale numerators traces = true := by decide +kernel

private theorem signs_checked : signsOK 9 numerators = true := by decide +kernel

theorem polynomial_eq :
    FaceOrder.ehrhartPolynomial 8 = Small.fromCoeffs (normalized scale numerators) :=
  certify_scaled 8 scale numerators traces (by decide +kernel) (by decide +kernel)
    (NewtonTraceCache.trace_list_certificate 9 21 (by decide) (by decide) trace_evaluated) (valuesOK_sound values_checked)

theorem signs (j : Fin 21) :
    ((FaceOrder.ehrhartPolynomial 8).coeff j.val < 0 ↔ negativeIndex 9 j.val) ∧
      ((FaceOrder.ehrhartPolynomial 8).coeff j.val ≠ 0) :=
  signsOK_sound (by decide +kernel) polynomial_eq signs_checked j

end Polygon.Finite64.N09
