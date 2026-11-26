import PolygonEndpoint.UnorderedClassification

/-! Uniform first-offset and fixed ordinary-degree errors for the actual unordered hull. -/
noncomputable section

namespace PolygonEndpoint

open Polygon Filter Asymptotics
open scoped Topology

variable {S : PlanarSet}

/-- For every positive degree the first displaced kernel value has the stated exact
coefficient. The remaining error is uniform in degree, including degrees one and two. -/
theorem unordered_uniform_first_order_error (hf : S.Finite)
    (he : S = (convexHull ℝ S).extremePoints ℝ)
    (hfull : affineSpan ℝ (convexHull ℝ S) = ⊤)
    (hn : 66 ≤ S.ncard) {r : ℕ} (hr : 1 ≤ r) (htop : r ≤ 2 * S.ncard + 2) :
    let n := S.ncard
    let d := 2 * n + 2 - r
    let A := ((unorderedEhrhart S hf he hfull).coeff r : ℝ)
    let q₁ := (Real.pi ^ 2 / (24 * (2 * (n : ℝ) - 1))) *
      (FormalCosine.sigma (n - 1) / FormalCosine.sigma n)
    |A - leadingScale n r * (kernel d + q₁ * UniformCoefficientBound.shifted kernel d 1)| ≤
      (15001 / (n : ℝ) ^ 2) * (leadingScale n r * |kernel d|) := by
  simpa only [unorderedEhrhart_eq_reference S hf he hfull,
    first_relative_weight (by omega : 2 ≤ S.ncard)] using uniform_first_order_error hn hr htop

/-- A single explicit relative-error constant valid for both parities. -/
def ordinaryRateConstant (a : ℕ) : ℝ :=
  201 + 202 * (4 * FixedDegree.tailBudget + 2 * (a : ℝ) + 1)

private theorem normalized_error {n r : ℕ} (hn : 66 ≤ n) (hr : 1 ≤ r)
    (htop : r ≤ 2 * n + 2) (s B : ℝ) (hB : 0 ≤ B)
    (hdiag : |FixedDegree.diagonal n r / s - 1| ≤ B / (n : ℝ)) :
    |geometricCoeff n r / s - 1| ≤ (201 + 202 * B) / (n : ℝ) := by
  let A := geometricCoeff n r
  let D := FixedDegree.diagonal n r
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hscale := leadingScale_positive (n := n) (r := r) (by omega)
  have hg : (PolygonKernel.g (2 * n + 2 - r) : ℝ) ≠ 0 := by
    exact_mod_cast (PolygonKernel.kernel_all (2 * n + 2 - r)).1
  have hd0 : D ≠ 0 := mul_ne_zero hscale.ne' hg
  have hA : |A / D - 1| ≤ 201 / (n : ℝ) := by
    rw [← div_self hd0, ← sub_div, abs_div, div_le_iff₀ (abs_pos.mpr hd0)]
    simpa only [A, D, FixedDegree.diagonal, abs_mul, abs_of_pos hscale] using
      uniform_diagonal_error hn hr htop
  have hB' : B / (n : ℝ) ≤ B := by
    apply (div_le_iff₀ hn0).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn1 hB
  have hs : |D / s| ≤ 1 + B := by
    have e := abs_add_le (D / s - 1) (1 : ℝ)
    rw [sub_add_cancel, abs_one] at e
    have tight := hdiag.trans hB'
    linarith
  have hprod : (A / D) * (D / s) = A / s := by
    rw [← mul_div_assoc, div_mul_cancel₀ _ hd0]
  have e : A / s - 1 = (A / D - 1) * (D / s) + (D / s - 1) := by
    rw [← hprod]
    ring
  change |A / s - 1| ≤ _
  rw [e]
  calc
    _ ≤ |A / D - 1| * |D / s| + |D / s - 1| := by
      rw [← abs_mul]
      exact abs_add_le _ _
    _ ≤ (201 / (n : ℝ)) * (1 + B) + B / (n : ℝ) :=
      add_le_add (mul_le_mul hA hs (abs_nonneg _) (by positivity)) hdiag
    _ = _ := by ring

private theorem tailBudget_nonneg : 0 ≤ FixedDegree.tailBudget := by
  unfold FixedDegree.tailBudget FixedDegree.regularCap
  positivity

/-- Effective O(1/n) relative error at every fixed positive odd degree. -/
theorem unordered_ordinary_odd_rate (hf : S.Finite)
    (he : S = (convexHull ℝ S).extremePoints ℝ)
    (hfull : affineSpan ℝ (convexHull ℝ S) = ⊤) (a : ℕ)
    (hn : max 66 (2 * a + 2) ≤ S.ncard) :
    let n := S.ncard
    let A := ((unorderedEhrhart S hf he hfull).coeff (2 * a + 1) : ℝ)
    |A / (FixedDegree.factorialScale n * FixedDegree.oddPrincipal n a) - 1| ≤
      ordinaryRateConstant a / (n : ℝ) := by
  let n := S.ncard
  have hsmall : 2 * a + 2 ≤ n := (le_max_right ..).trans hn
  have hlarge : 66 ≤ n := (le_max_left ..).trans hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  let B := 4 * FixedDegree.tailBudget + 2 * (a : ℝ) + 1
  have hB : 0 ≤ B := by
    dsimp [B]
    linarith [tailBudget_nonneg, Nat.cast_nonneg (α := ℝ) a]
  have hbound : 4 * FixedDegree.tailBudget / (n : ℝ) ^ 2 ≤ B / (n : ℝ) := by
    calc
      _ ≤ 4 * FixedDegree.tailBudget / (n : ℝ) := by
        apply div_le_div_of_nonneg_left (mul_nonneg (by norm_num) tailBudget_nonneg) hn0
        nlinarith only [mul_nonneg (sub_nonneg.mpr hn1) hn0.le]
      _ ≤ _ := div_le_div_of_nonneg_right
        (by dsimp [B]; linarith [Nat.cast_nonneg (α := ℝ) a]) hn0.le
  rw [unorderedEhrhart_eq_reference S hf he hfull]
  exact normalized_error hlarge (by omega) (by omega) _ B hB
    ((FixedDegree.odd_diagonal_rate hsmall).trans hbound)

/-- Effective O(1/n) relative error at every fixed positive even degree. -/
theorem unordered_ordinary_even_rate (hf : S.Finite)
    (he : S = (convexHull ℝ S).extremePoints ℝ)
    (hfull : affineSpan ℝ (convexHull ℝ S) = ⊤) (a : ℕ)
    (hn : max 66 (2 * a + 2) ≤ S.ncard) :
    let n := S.ncard
    let A := ((unorderedEhrhart S hf he hfull).coeff (2 * a + 2) : ℝ)
    |A / (FixedDegree.factorialScale n * (FixedDegree.evenPrincipal n a * (2 * (n : ℝ)))) - 1| ≤
      ordinaryRateConstant a / (n : ℝ) := by
  let n := S.ncard
  have hsmall : 2 * a + 2 ≤ n := (le_max_right ..).trans hn
  have hlarge : 66 ≤ n := (le_max_left ..).trans hn
  let B := 4 * FixedDegree.tailBudget + 2 * (a : ℝ) + 1
  have hB : 0 ≤ B := by
    dsimp [B]
    linarith [tailBudget_nonneg, Nat.cast_nonneg (α := ℝ) a]
  rw [unorderedEhrhart_eq_reference S hf he hfull]
  exact normalized_error hlarge (by omega) (by omega) _ B hB (FixedDegree.even_diagonal_rate hsmall)

section Family

variable {ι : Type*} {l : Filter ι} (S : ι → PlanarSet)
  (hf : ∀ i, (S i).Finite) (he : ∀ i, S i = (convexHull ℝ (S i)).extremePoints ℝ)
  (hfull : ∀ i, affineSpan ℝ (convexHull ℝ (S i)) = ⊤)

/-- Fixed odd degree along any family with diverging number of sides, in Big-O notation. -/
theorem unordered_ordinary_odd_bigO (hn : Tendsto (fun i ↦ (S i).ncard) l atTop) (a : ℕ) :
    (fun i ↦
      let n := (S i).ncard
      ((unorderedEhrhart (S i) (hf i) (he i) (hfull i)).coeff (2 * a + 1) : ℝ) /
        (FixedDegree.factorialScale n * FixedDegree.oddPrincipal n a) - 1)
      =O[l] (fun i ↦ 1 / ((S i).ncard : ℝ)) := by
  apply IsBigO.of_bound (ordinaryRateConstant a)
  have hlarge := hn.eventually (eventually_ge_atTop (max 66 (2 * a + 2)))
  filter_upwards [hlarge] with i hi
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / ((S i).ncard : ℝ)),
    mul_one_div] using unordered_ordinary_odd_rate (hf i) (he i) (hfull i) a hi

/-- Fixed even degree along any family with diverging number of sides, in Big-O notation. -/
theorem unordered_ordinary_even_bigO (hn : Tendsto (fun i ↦ (S i).ncard) l atTop) (a : ℕ) :
    (fun i ↦
      let n := (S i).ncard
      ((unorderedEhrhart (S i) (hf i) (he i) (hfull i)).coeff (2 * a + 2) : ℝ) /
        (FixedDegree.factorialScale n * (FixedDegree.evenPrincipal n a * (2 * (n : ℝ)))) - 1)
      =O[l] (fun i ↦ 1 / ((S i).ncard : ℝ)) := by
  apply IsBigO.of_bound (ordinaryRateConstant a)
  have hlarge := hn.eventually (eventually_ge_atTop (max 66 (2 * a + 2)))
  filter_upwards [hlarge] with i hi
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / ((S i).ncard : ℝ)),
    mul_one_div] using unordered_ordinary_even_rate (hf i) (he i) (hfull i) a hi

end Family

#print axioms unordered_uniform_first_order_error
#print axioms unordered_ordinary_odd_rate
#print axioms unordered_ordinary_even_rate
#print axioms unordered_ordinary_odd_bigO
#print axioms unordered_ordinary_even_bigO

end PolygonEndpoint
