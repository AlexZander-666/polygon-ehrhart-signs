import Polygon.NewtonExecutor

/-! Exact integer interpolation certificates for the original face-poset Ehrhart rows. -/
namespace Polygon.NewtonInterpolant

open Finset Polynomial

def traceRow (n width : ℕ) : List ℕ :=
  (List.range width).map fun i ↦ (NewtonExecutor.trace n (i + 1)).toNat

theorem traceRow_get (n width i : ℕ) (h : i < width) :
    (traceRow n width).getD i 0 = Cert.traceCount n (i + 1) := by
  have h' : i < (traceRow n width).length := by simpa [traceRow] using h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h']
  simp [traceRow, NewtonExecutor.trace_correct]

private theorem sum_list_range {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- Endpoint weights for each allowed interval of labels. This is the first
finite sum over the original lower and upper face labels. -/
def observation (traces : List ℕ) (q : ℕ) : ℕ :=
  ((List.range (q + 1)).map fun i ↦ (q + 1 - i) * traces.getD i 0).sum

theorem observation_eq (traces : List ℕ) (q : ℕ) :
    observation traces q = Small.observation traces q := by
  unfold observation Small.observation
  rw [sum_list_range]
  exact (Fin.sum_univ_eq_sum_range (fun i ↦ (q + 1 - i) * traces.getD i 0) (q + 1)).symm

def hornerInt (x : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: rest => a + x * hornerInt x rest

def normalized (scale : ℕ) (coeffs : List ℤ) : List ℚ :=
  coeffs.map fun (a : ℤ) ↦ (a : ℚ) / scale

theorem horner_normalized (x : ℤ) (scale : ℕ) (coeffs : List ℤ) :
    Small.horner (x : ℚ) (normalized scale coeffs) =
      (hornerInt x coeffs : ℚ) / scale := by
  induction coeffs with
  | nil => simp [normalized, Small.horner, hornerInt]
  | cons a cs ih =>
    simp only [normalized, List.map_cons, Small.horner, hornerInt,
      Int.cast_add, Int.cast_mul] at ih ⊢
    rw [ih]
    ring

theorem normalized_get (scale : ℕ) (coeffs : List ℤ) (j : ℕ) :
    (normalized scale coeffs).getD j 0 = (coeffs.getD j 0 : ℚ) / scale := by
  induction coeffs generalizing j with
  | nil => simp [normalized]
  | cons a cs ih =>
    cases j with
    | zero => rfl
    | succ j =>
      change (normalized scale cs).getD j 0 = (cs.getD j 0 : ℚ) / scale
      exact ih j

/-- Every retained coefficient has an integer numerator and the same positive
denominator. Check integer dilate values against the original face labeling count. -/
theorem certify_scaled (k scale : ℕ) (coeffs : List ℤ) (traces : List ℕ) (hscale : 0 < scale)
    (len : coeffs.length = 2 * (k + 1) + 3)
    (ht : ∀ i : Fin (2 * (k + 1) + 3),
      Cert.traceCount (k + 1) (i.val + 1) = traces.getD i.val 0)
    (hv : ∀ i : Fin (2 * (k + 1) + 3),
      hornerInt (i.val : ℤ) coeffs = (scale : ℤ) * (observation traces i.val : ℤ)) :
    FaceOrder.ehrhartPolynomial k = Small.fromCoeffs (normalized scale coeffs) := by
  apply Small.certify k (normalized scale coeffs) traces (by simpa [normalized] using len) ht
  intro i
  have ns : (scale : ℚ) ≠ 0 := by exact_mod_cast hscale.ne'
  rw [← Int.cast_natCast, horner_normalized, hv, observation_eq]
  push_cast
  field_simp

/-- A materialized list computed by the verified Newton executor gives all actual
matrix traces, with no unproved assumption about its numeric entries. -/
theorem trace_list_certificate (n width : ℕ) {traces : List ℕ}
    (h : traceRow n width = traces) (i : Fin width) :
    Cert.traceCount n (i.val + 1) = traces.getD i.val 0 := by
  rw [← h, traceRow_get _ _ _ i.isLt]

/-- Convert a single list of kernel-checked booleans to a universally quantified
interpolation equality. This keeps closed kernel checks in list form. -/
def valuesOK (size scale : ℕ) (coeffs : List ℤ) (traces : List ℕ) : Bool :=
  (List.range size).all fun q ↦
    decide (hornerInt (q : ℤ) coeffs = (scale : ℤ) * (observation traces q : ℤ))

theorem valuesOK_sound {size scale : ℕ} {coeffs : List ℤ} {traces : List ℕ}
    (h : valuesOK size scale coeffs traces = true) (q : Fin size) :
    hornerInt (q.val : ℤ) coeffs = (scale : ℤ) * (observation traces q.val : ℤ) := by
  unfold valuesOK at h
  exact of_decide_eq_true (List.all_eq_true.mp h q.val (List.mem_range.mpr q.isLt))

def negativeIndex (n j : ℕ) : Prop :=
  0 < j ∧ 27 ≤ 2 * n + 2 - j ∧ ((2 * n + 2 - j) % 4 = 0 ∨ (2 * n + 2 - j) % 4 = 3)

instance (n j : ℕ) : Decidable (negativeIndex n j) := by
  unfold negativeIndex
  infer_instance

def signsOK (n : ℕ) (coeffs : List ℤ) : Bool :=
  (List.range (2 * n + 3)).all fun j ↦
    decide ((coeffs.getD j 0 < 0 ↔ negativeIndex n j) ∧ coeffs.getD j 0 ≠ 0)

theorem signsOK_sound {k scale : ℕ} {coeffs : List ℤ} (hscale : 0 < scale)
    (eq : FaceOrder.ehrhartPolynomial k = Small.fromCoeffs (normalized scale coeffs))
    (h : signsOK (k + 1) coeffs = true) (j : Fin (2 * (k + 1) + 3)) :
    ((FaceOrder.ehrhartPolynomial k).coeff j.val < 0 ↔ negativeIndex (k + 1) j.val) ∧
      ((FaceOrder.ehrhartPolynomial k).coeff j.val ≠ 0) := by
  have ok := of_decide_eq_true (List.all_eq_true.mp h j.val (List.mem_range.mpr j.isLt))
  rw [eq, Small.coeff_fromCoeffs, normalized_get]
  have hs : (0 : ℚ) < scale := by exact_mod_cast hscale
  rw [div_neg_iff, div_ne_zero_iff]
  simp only [not_lt_of_ge hs.le, and_false, false_or, hs, and_true]
  exact ⟨(show ((coeffs.getD j.val 0 : ℤ) : ℚ) < 0 ↔ _ by exact_mod_cast ok.1),
    ⟨by exact_mod_cast ok.2, hs.ne'⟩⟩

#print axioms traceRow_get
#print axioms observation_eq
#print axioms certify_scaled
#print axioms trace_list_certificate
#print axioms valuesOK_sound
#print axioms signsOK_sound

end Polygon.NewtonInterpolant
