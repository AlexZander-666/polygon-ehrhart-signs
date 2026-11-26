import Polygon.NewtonTraceCache

/-! Exact trace and interpolation inputs for the 10-gon. -/
namespace Polygon.Finite64.N10

open NewtonInterpolant

def numerators : List ℤ := [
  1124000727777607680000,
  13735821105483079680000,
  78030627032139393024000,
  287887245493719188275200,
  758094953218653728747520,
  1502062208084113282252800,
  2335270125925308297707520,
  2926724265533113647078400,
  2997969649596784610513920,
  2529927701585843808128000,
  1768988197435547263493120,
  1027851136754999510553600,
  495497184291079867653120,
  196973395871686474163200,
  63960441131056288107520,
  16765117439468301516800,
  3497041748767449681920,
  570121495286667878400,
  70874376968476139520,
  6475911112523776000,
  409498741461483520,
  15998886812057600,
  290888851128320
]

def traces : List ℕ := [
  1,
  15127,
  10764221,
  1534601035,
  82110068595,
  2275178956601,
  39328626021382,
  476808631729466,
  4385017799542985,
  32321355362370955,
  198752474937000511,
  1050796356524174537,
  4888528457763504511,
  20380280629295676305,
  77259808732346897260,
  269501756310269184916,
  873533348310014790257,
  2652444688121707667951,
  7597019165416739733745,
  20644514215669459763735,
  53493813641683473836571,
  132744583418104661927977,
  316648003630995064543826
]

def scale : ℕ := 1124000727777607680000

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem trace_evaluated : NewtonTraceCache.traceRow 10 23 = traces := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem values_checked : valuesOK 23 scale numerators traces = true := by decide +kernel

private theorem signs_checked : signsOK 10 numerators = true := by decide +kernel

theorem polynomial_eq :
    FaceOrder.ehrhartPolynomial 9 = Small.fromCoeffs (normalized scale numerators) :=
  certify_scaled 9 scale numerators traces (by decide +kernel) (by decide +kernel)
    (NewtonTraceCache.trace_list_certificate 10 23 (by decide) (by decide) trace_evaluated) (valuesOK_sound values_checked)

theorem signs (j : Fin 23) :
    ((FaceOrder.ehrhartPolynomial 9).coeff j.val < 0 ↔ negativeIndex 10 j.val) ∧
      ((FaceOrder.ehrhartPolynomial 9).coeff j.val ≠ 0) :=
  signsOK_sound (by decide +kernel) polynomial_eq signs_checked j

end Polygon.Finite64.N10
