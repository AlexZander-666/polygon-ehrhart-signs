import Polygon.GeneralRealization
import Polygon.TransferSpectrum

/-! The second width difference of the full face polynomial extracts the crown trace. -/
namespace Polygon.WidthSpectrum
noncomputable section
open Polynomial Finset

/-- Oriented incidences between a vertex (left) and an edge (right) of the crown. -/
def incidence (k : ℕ) : Fin (k+1) ⊕ Fin (k+1) → Fin (k+1) ⊕ Fin (k+1) → Prop
  | .inl i, .inr e => i = e ∨ i = e+1
  | _, _ => False

/-- Remove the two extrema. A weak labeling of the remaining incidence relation
is exactly a cyclic vertex labeling with one admissible label on each edge. -/
def crownEquiv (k m : ℕ) : Ehrhart.Labels (incidence k) m ≃ Tally.Coloring k m where
  toFun f := ⟨fun i ↦ f.val (.inl i), fun i ↦ ⟨f.val (.inr i),
    max_le (f.property _ _ (Or.inl rfl)) (f.property _ _ (Or.inr rfl))⟩⟩
  invFun f := ⟨Sum.elim f.1 (fun i ↦ (f.2 i).val), by
    rintro (i | i) (e | e) h <;> try contradiction
    rcases h with rfl | rfl
    · exact (le_max_left ..).trans (f.2 i).property
    · exact (le_max_right ..).trans (f.2 e).property⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    cases i <;> rfl
  right_inv f := by cases f; rfl

/-- The integer width variable counts labels, beginning with width zero. -/
def crownPolynomial (k : ℕ) : ℚ[X] :=
  (Ehrhart.orderPolynomial (incidence k)).comp (X - 1)

private theorem eval_minus_one {V : Type*} [Fintype V] [Nonempty V] (r : V → V → Prop) :
    (Ehrhart.orderPolynomial r).eval (-1) = 0 := by
  classical
  simp only [Ehrhart.orderPolynomial, eval_finsetSum, eval_mul, eval_C]
  apply sum_eq_zero
  intro i _
  cases i with
  | zero =>
    have h : IsEmpty (Ehrhart.SurjectiveLabels r 0) := ⟨fun f ↦
      Fin.elim0 (f.val.val (Classical.arbitrary V))⟩
    simp [Fintype.card_eq_zero]
  | succ i =>
    simp [Ehrhart.choosePolynomial, descPochhammer_succ_left]

/-- The crown polynomial counts the original integer transfer trace at every natural width. -/
theorem crown_eval_trace (k m : ℕ) :
    (crownPolynomial k).eval (m : ℚ) = (Cert.traceCount (k+1) m : ℚ) := by
  rw [crownPolynomial, eval_comp, eval_sub, eval_X, eval_one]
  cases m with
  | zero =>
    rw [Nat.cast_zero, zero_sub, eval_minus_one, Cert.traceCount_correct]
    simp [Matrix.trace]
  | succ m =>
    rw [Nat.cast_succ, add_sub_cancel_right, Ehrhart.eval_orderPolynomial,
      Fintype.card_congr (crownEquiv k (m+1)), Tally.card_coloring,
      Cert.traceCount_correct, Tally.trace_pow_cycle]
    rfl


private def triangle (f : ℕ → ℚ) (q : ℕ) : ℚ :=
  ∑ i ∈ range q, ((q : ℚ) - i) * f (i+1)

private theorem triangle_step (f : ℕ → ℚ) (q : ℕ) :
    triangle f (q+1) = triangle f q + ∑ i ∈ range (q+1), f (i+1) := by
  simp only [triangle, sum_range_succ, Nat.cast_add, Nat.cast_one]
  have split (i : ℕ) : ((q : ℚ) + 1 - i) * f (i+1) =
      ((q : ℚ) - i) * f (i+1) + f (i+1) := by ring
  simp only [split, sum_add_distrib]
  ring

private theorem eval_triangle (k q : ℕ) :
    (FaceOrder.ehrhartPolynomial k).eval (q : ℚ) =
      triangle (fun m ↦ (Cert.traceCount (k+1) m : ℚ)) (q+1) := by
  rw [FaceOrder.eval_ehrhartPolynomial, Tally.card_labeling_eq_traceCount,
    Fin.sum_univ_eq_sum_range (fun i ↦ (q+1-i)*Cert.traceCount (k+1) (i+1)), Nat.cast_sum]
  apply sum_congr rfl
  intro i hi
  rw [Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt (mem_range.mp hi))]

/-- For three consecutive nonnegative dilates, the width isolated is the first
dilate plus three. The right side is the actual integer matrix trace. -/
theorem forward_difference (k q : ℕ) :
    let E := FaceOrder.ehrhartPolynomial k
    E.eval ((q : ℚ)+2) - 2*E.eval ((q : ℚ)+1) + E.eval (q : ℚ) =
      (Cert.traceCount (k+1) (q+3) : ℚ) := by
  dsimp only
  rw [← Nat.cast_ofNat (R := ℚ) (n := 2), ← Nat.cast_add, ← Nat.cast_one (R := ℚ),
    ← Nat.cast_add, eval_triangle, eval_triangle, eval_triangle]
  rw [triangle_step _ (q+2), triangle_step _ (q+1)]
  rw [sum_range_succ _ (q+2)]
  ring

/-- A polynomial identity over the rationals. In particular the low widths use
actual evaluations of the full Ehrhart polynomial at negative inputs. -/
theorem difference_polynomial (k : ℕ) :
    let E := FaceOrder.ehrhartPolynomial k
    E.comp (X+2) - 2*E.comp (X+1) + E = (crownPolynomial k).comp (X+3) := by
  dsimp only
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℚ))).mono
  rintro _ ⟨q,rfl⟩
  have ic := crown_eval_trace k (q+3)
  push_cast at ic
  simpa [eval_comp, ←ic] using forward_difference k q


/-- Second backward difference in the inclusive width, valid even for rational widths. -/
theorem width_difference (k : ℕ) (w : ℚ) :
    let E := FaceOrder.ehrhartPolynomial k
    E.eval (w-1) - 2*E.eval (w-2) + E.eval (w-3) = (crownPolynomial k).eval w := by
  have h := congrArg (Polynomial.eval (w-3)) (difference_polynomial k)
  simpa [eval_comp, show w-3+2=w-1 by ring, show w-3+1=w-2 by ring] using h

/-- The entire rational identity in geometric side-count indexing. -/
theorem geometric_width_difference {n : ℕ} (hn : 3 ≤ n) (w : ℚ) :
    let E := GeneralRealization.geometricEhrhart (n-3)
    E.eval (w-1) - 2*E.eval (w-2) + E.eval (w-3) = (crownPolynomial (n-1)).eval w := by
  dsimp only
  rw [GeneralRealization.ehrhart_by_sides hn]
  exact width_difference (n-1) w

/-- At all natural widths the difference is a literal integer crown trace. -/
theorem geometric_width_trace {n : ℕ} (hn : 3 ≤ n) (m : ℕ) :
    let E := GeneralRealization.geometricEhrhart (n-3)
    E.eval ((m : ℚ)-1) - 2*E.eval ((m : ℚ)-2) + E.eval ((m : ℚ)-3) =
      (Cert.traceCount n m : ℚ) := by
  dsimp only
  rw [geometric_width_difference hn, crown_eval_trace, show n-1+1=n by omega]

/-- Spectral form for every polygon size and inclusive integer width, including zero. -/
theorem geometric_width_spectrum {n : ℕ} (hn : 3 ≤ n) (m : ℕ) :
    let E := GeneralRealization.geometricEhrhart (n-3)
    ((E.eval ((m : ℚ)-1) - 2*E.eval ((m : ℚ)-2) + E.eval ((m : ℚ)-3) : ℚ) : ℝ) =
      ∑ j : Fin m, ((TransferSpectrum.parameter j)⁻¹)^n := by
  dsimp only
  rw [geometric_width_trace hn]
  exact_mod_cast TransferSpectrum.traceCount n m

private theorem trace_one (n : ℕ) : Cert.traceCount n 1 = 1 := by
  have h : Cert.transfer 1 = 1 := by
    ext i j
    have hi : i=0 := Subsingleton.elim ..
    have hj : j=0 := Subsingleton.elim ..
    subst i
    subst j
    decide
  rw [Cert.traceCount_correct, h, one_pow]
  simp

/-- Values needed by the empty, one-label and two-label boundary widths. -/
theorem low_inputs (k : ℕ) :
    let E := FaceOrder.ehrhartPolynomial k
    E.eval 0 = 1 ∧ E.eval (-1) = 0 ∧ E.eval (-2) = 0 ∧ E.eval (-3) = 0 := by
  dsimp only
  let E := FaceOrder.ehrhartPolynomial k
  have e0 : E.eval 0 = 1 := by
    simpa [E, triangle, trace_one] using eval_triangle k 0
  let _ : Nonempty (FaceOrder.Face k) := ⟨.bottom⟩
  have e1 : E.eval (-1) = 0 := eval_minus_one (FaceOrder.faceLE (k := k))
  have h1 := (width_difference k 1).trans (crown_eval_trace k 1)
  have h0 := (width_difference k 0).trans (crown_eval_trace k 0)
  have empty : Cert.traceCount (k+1) 0 = 0 := by rw [Cert.traceCount_correct]; simp [Matrix.trace]
  norm_num [trace_one, empty, ← show E = FaceOrder.ehrhartPolynomial k from rfl, e0, e1] at h0 h1
  exact ⟨e0, e1, by linarith, by linarith⟩


/-- The spectrum directly recovers a second difference of three literal lattice
point cardinalities; the smallest dilation may be zero. -/
theorem lattice_count_spectrum {n : ℕ} (hn : 3 ≤ n) (q : ℕ) :
    let counts := fun d ↦ Fintype.card
      (Ehrhart.LatticePoints (fun a b : GeneralRealization.GeometricFace (n-3) ↦ a ≤ b) d)
    (counts (q+2) : ℝ) - 2*(counts (q+1) : ℝ) + counts q =
      ∑ j : Fin (q+3), ((TransferSpectrum.parameter j)⁻¹)^n := by
  dsimp only
  have hs := geometric_width_spectrum hn (q+3)
  have h (d : ℕ) := GeneralRealization.geometricCounts (n-3) d
  push_cast at hs
  have a : (q : ℚ)+3-1 = (q+2 : ℕ) := by push_cast; ring
  have b : (q : ℚ)+3-2 = (q+1 : ℕ) := by push_cast; ring
  have c : (q : ℚ)+3-3 = q := by ring
  simpa only [a,b,c,h,Rat.cast_natCast] using hs

#print axioms crownEquiv
#print axioms crown_eval_trace
#print axioms difference_polynomial
#print axioms geometric_width_difference
#print axioms geometric_width_trace
#print axioms geometric_width_spectrum
#print axioms low_inputs
#print axioms lattice_count_spectrum

end
end Polygon.WidthSpectrum
