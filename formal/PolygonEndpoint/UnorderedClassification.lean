import Polygon.UnorderedExtremes
import PolygonEndpoint.CyclicClassification
import PolygonEndpoint.FixedCodimension
import PolygonEndpoint.FixedDegreeDiagonal
import PolygonEndpoint.UniformApprox

/-! The actual Ehrhart polynomial and its coefficient limits for unordered extreme-point sets. -/
noncomputable section

namespace PolygonEndpoint

open Polygon Filter
open scoped Topology

abbrev PlanarSet := Set (ℝ × ℝ)

/-- Every exposed subset of the given hull, ordered by inclusion. -/
abbrev UnorderedFace (S : PlanarSet) :=
  {F : PlanarSet // IsExposed ℝ (convexHull ℝ S) F}

/-- The chosen incidence isomorphism from the original, unordered point set. -/
def unorderedFaceOrderIso (S : PlanarSet) (hf : S.Finite)
    (he : S = (convexHull ℝ S).extremePoints ℝ)
    (hfull : affineSpan ℝ (convexHull ℝ S) = ⊤) :
    UnorderedFace S ≃o FaceOrder.Face (S.ncard - 1) :=
  (Classical.choice (UnorderedExtremes.faceOrderIso_of_extremes hf he hfull)).symm

@[instance_reducible] def unorderedFaceFintype (S : PlanarSet) (hf : S.Finite)
    (he : S = (convexHull ℝ S).extremePoints ℝ)
    (hfull : affineSpan ℝ (convexHull ℝ S) = ⊤) : Fintype (UnorderedFace S) :=
  Fintype.ofEquiv _ (unorderedFaceOrderIso S hf he hfull).symm.toEquiv

/-- Ehrhart polynomial of the order polytope of the actual complete exposed-face order. -/
def unorderedEhrhart (S : PlanarSet) (hf : S.Finite)
    (he : S = (convexHull ℝ S).extremePoints ℝ)
    (hfull : affineSpan ℝ (convexHull ℝ S) = ⊤) : Polynomial ℚ :=
  letI := unorderedFaceFintype S hf he hfull
  Ehrhart.orderPolynomial (fun a b : UnorderedFace S ↦ a ≤ b)

private theorem three_le_ncard {S : PlanarSet} (hf : S.Finite)
    (hfull : affineSpan ℝ (convexHull ℝ S) = ⊤) : 3 ≤ S.ncard := by
  rw [Set.ncard_eq_toFinset_card S hf]
  exact UnorderedExtremes.card_ge_three hf.toFinset (by simpa only [hf.coe_toFinset] using hfull)

/-- Polynomials on the same number of vertices agree regardless of the coordinates or labeling. -/
theorem unorderedEhrhart_eq_reference (S : PlanarSet) (hf : S.Finite)
    (he : S = (convexHull ℝ S).extremePoints ℝ)
    (hfull : affineSpan ℝ (convexHull ℝ S) = ⊤) :
    unorderedEhrhart S hf he hfull = GeneralRealization.geometricEhrhart (S.ncard - 3) := by
  let _ := unorderedFaceFintype S hf he hfull
  exact PolygonTransport.of_cyclic_incidence (three_le_ncard hf hfull)
    (unorderedFaceOrderIso S hf he hfull)

/-- Strict signs and zero tail at all ordinary coefficient indices. -/
theorem unordered_classification (S : PlanarSet) (hf : S.Finite)
    (he : S = (convexHull ℝ S).extremePoints ℝ)
    (hfull : affineSpan ℝ (convexHull ℝ S) = ⊤) (r : ℕ) :
    let n := S.ncard
    let a := (unorderedEhrhart S hf he hfull).coeff r
    (a < 0 ↔ NewtonInterpolant.negativeIndex n r) ∧
    (0 < a ↔ r ≤ 2 * n + 2 ∧ ¬ NewtonInterpolant.negativeIndex n r) ∧
    (a = 0 ↔ 2 * n + 2 < r) := by
  rw [unorderedEhrhart_eq_reference S hf he hfull]
  simpa only [NewtonInterpolant.negativeIndex] using geometric_classification
    (three_le_ncard hf hfull) r

/-- The exact number of negative coefficients of the actual geometric polynomial. -/
theorem unordered_negative_count (S : PlanarSet) (hf : S.Finite)
    (he : S = (convexHull ℝ S).extremePoints ℝ)
    (hfull : affineSpan ℝ (convexHull ℝ S) = ⊤) :
    let n := S.ncard
    ((Finset.range (2 * n + 3)).filter (fun r ↦ (unorderedEhrhart S hf he hfull).coeff r < 0)).card =
      n - 12 := by
  rw [unorderedEhrhart_eq_reference S hf he hfull]
  exact negative_count (three_le_ncard hf hfull)

/-- Ordinary degree zero is exactly one for each hull. -/
@[simp] theorem unordered_constant (S : PlanarSet) (hf : S.Finite)
    (he : S = (convexHull ℝ S).extremePoints ℝ)
    (hfull : affineSpan ℝ (convexHull ℝ S) = ⊤) :
    (unorderedEhrhart S hf he hfull).coeff 0 = 1 := by
  rw [unorderedEhrhart_eq_reference S hf he hfull]
  exact geometric_constant (three_le_ncard hf hfull)

private theorem diagonal_ne_zero {n r : ℕ} (hn : 0 < n) : FixedDegree.diagonal n r ≠ 0 := by
  have h := (PolygonKernel.kernel_all (2 * n + 2 - r)).1
  have hcast : (PolygonKernel.g (2 * n + 2 - r) : ℝ) ≠ 0 := by exact_mod_cast h
  exact mul_ne_zero (leadingScale_positive hn).ne' hcast

private theorem actual_over_diagonal_limit {r : ℕ} (hr : 1 ≤ r) :
    Tendsto (fun n ↦ geometricCoeff n r / FixedDegree.diagonal n r) atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) _
    (tendsto_const_div_atTop_nhds_zero_nat 201)
  filter_upwards [eventually_ge_atTop (max 66 r)] with n hn
  have hn₆₆ : 66 ≤ n := (le_max_left ..).trans hn
  have htop : r ≤ 2 * n + 2 := by
    have := (le_max_right 66 r).trans hn
    omega
  have hnd := diagonal_ne_zero (r := r) (n := n) (by omega)
  have pos := leadingScale_positive (r := r) (n := n) (by omega)
  have h := uniform_diagonal_error hn₆₆ hr htop
  change ‖geometricCoeff n r / FixedDegree.diagonal n r - 1‖ ≤ (201 / (n : ℝ))
  rw [Real.norm_eq_abs,
    show geometricCoeff n r / FixedDegree.diagonal n r - 1 =
      (geometricCoeff n r - FixedDegree.diagonal n r) / FixedDegree.diagonal n r by
      rw [sub_div, div_self hnd],
    abs_div, div_le_iff₀ (abs_pos.mpr hnd)]
  simpa only [FixedDegree.diagonal, abs_mul, abs_of_pos pos] using h

private theorem actual_from_diagonal_limit {r : ℕ} (hr : 1 ≤ r) (s : ℕ → ℝ)
    (h : Tendsto (fun n ↦ FixedDegree.diagonal n r / s n) atTop (𝓝 1)) :
    Tendsto (fun n ↦ geometricCoeff n r / s n) atTop (𝓝 1) := by
  have hmul := (actual_over_diagonal_limit hr).mul h
  rw [mul_one] at hmul
  apply hmul.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [← mul_div_assoc, div_mul_cancel₀ _ (diagonal_ne_zero (by omega : 0 < n))]

/-- Fixed positive odd degree of the geometric polynomial with the paper's normalization. -/
theorem geometric_ordinary_odd_limit (a : ℕ) :
    Tendsto (fun n ↦ geometricCoeff n (2 * a + 1) /
      (FixedDegree.factorialScale n * FixedDegree.oddPrincipal n a)) atTop (𝓝 1) :=
  actual_from_diagonal_limit (by omega) _ (FixedDegree.odd_diagonal_limit a)

/-- Fixed positive even degree of the geometric polynomial with the paper's normalization. -/
theorem geometric_ordinary_even_limit (a : ℕ) :
    Tendsto (fun n ↦ geometricCoeff n (2 * a + 2) /
      (FixedDegree.factorialScale n * (FixedDegree.evenPrincipal n a * (2 * (n : ℝ)))))
    atTop (𝓝 1) :=
  actual_from_diagonal_limit (by omega) _ (FixedDegree.even_diagonal_limit a)

section Family

variable {ι : Type*} {l : Filter ι} (S : ι → PlanarSet)
  (hf : ∀ i, (S i).Finite) (he : ∀ i, S i = (convexHull ℝ (S i)).extremePoints ℝ)
  (hfull : ∀ i, affineSpan ℝ (convexHull ℝ (S i)) = ⊤)

/-- Ordinary degree zero has the same limit along any unordered family. -/
theorem unordered_ordinary_zero_limit :
    Tendsto (fun i ↦ ((unorderedEhrhart (S i) (hf i) (he i) (hfull i)).coeff 0 : ℝ)) l (𝓝 1) := by
  simpa only [unordered_constant, Rat.cast_one] using (tendsto_const_nhds : Tendsto
    (fun _ : ι ↦ (1 : ℝ)) l (𝓝 1))

/-- Fixed odd degree along any family of unordered hulls with diverging vertex count. -/
theorem unordered_ordinary_odd_limit (hn : Tendsto (fun i ↦ (S i).ncard) l atTop) (a : ℕ) :
    Tendsto (fun i ↦
      let n := (S i).ncard
      ((unorderedEhrhart (S i) (hf i) (he i) (hfull i)).coeff (2 * a + 1) : ℝ) /
        (FixedDegree.factorialScale n * FixedDegree.oddPrincipal n a)) l (𝓝 1) := by
  simpa only [Function.comp_def, geometricCoeff, unorderedEhrhart_eq_reference] using
    (geometric_ordinary_odd_limit a).comp hn

/-- Fixed even degree along any family of unordered hulls with diverging vertex count. -/
theorem unordered_ordinary_even_limit (hn : Tendsto (fun i ↦ (S i).ncard) l atTop) (a : ℕ) :
    Tendsto (fun i ↦
      let n := (S i).ncard
      ((unorderedEhrhart (S i) (hf i) (he i) (hfull i)).coeff (2 * a + 2) : ℝ) /
        (FixedDegree.factorialScale n * (FixedDegree.evenPrincipal n a * (2 * (n : ℝ)))))
    l (𝓝 1) := by
  simpa only [Function.comp_def, geometricCoeff, unorderedEhrhart_eq_reference] using
    (geometric_ordinary_even_limit a).comp hn

/-- Fixed codimension along any family of unordered hulls with diverging vertex count. -/
theorem unordered_fixed_codimension (hn : Tendsto (fun i ↦ (S i).ncard) l atTop) (d : ℕ) :
    Tendsto (fun i ↦
      let D := 2 * (S i).ncard + 2
      let E := unorderedEhrhart (S i) (hf i) (he i) (hfull i)
      (E.coeff (D - d) : ℝ) / ((E.coeff D : ℝ) * (D.descFactorial d : ℝ) / 2 ^ d))
    l (𝓝 (kernel d)) := by
  simpa only [Function.comp_def, unorderedEhrhart_eq_reference] using
    (geometric_fixed_codimension d).comp hn

end Family

#print axioms unorderedFaceOrderIso
#print axioms unorderedEhrhart
#print axioms unorderedEhrhart_eq_reference
#print axioms unordered_classification
#print axioms unordered_negative_count
#print axioms unordered_constant
#print axioms geometric_ordinary_odd_limit
#print axioms geometric_ordinary_even_limit
#print axioms unordered_ordinary_zero_limit
#print axioms unordered_ordinary_odd_limit
#print axioms unordered_ordinary_even_limit
#print axioms unordered_fixed_codimension

end PolygonEndpoint
