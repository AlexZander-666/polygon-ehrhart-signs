import PolygonEndpoint.Weight
import Polygon.FormalCosine

/-! Exact centered sums for the ordinary coefficients of the actual full polygon face lattice. -/
noncomputable section
namespace PolygonEndpoint
open Finset PowerSeries Polygon

private lemma count_eval (q : ℕ) :
    ∑ i ∈ range (q+1), ((q:ℚ)+1-i) = endpointCount.eval (q:ℚ) := by
  simp only [endpointCount,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
  induction q with
  | zero => norm_num
  | succ q ih =>
    rw [sum_range_succ]
    push_cast
    have h (i : ℕ) : ((q:ℚ)+1+1-i) = ((q:ℚ)+1-i)+1 := by ring
    simp only [h,sum_add_distrib,sum_const,card_range,nsmul_one]
    rw [ih]
    push_cast
    ring

theorem moment_eval (k q : ℕ) : (moment k).eval (q:ℚ) =
    ∑ i ∈ range (q+1), ((q:ℚ)+1-i)*((2*(i:ℚ)+3)^(2*k)-1) := by
  rw [moment,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,
    exponentialPolynomial_eval,←count_eval]
  have castweight (i : ℕ) : ((q+1:ℕ):PowerSeries ℚ) - i = C ((q:ℚ)+1-i) := by
    rw [map_sub,map_add,map_natCast,map_natCast,map_one]
    push_cast
    rfl
  simp only [U,tri,map_sum,castweight,coeff_C_mul,ex,coeff_rescale,coeff_exp,
    Algebra.algebraMap_self_apply]
  simp_rw [mul_sub,mul_one,sum_sub_distrib]
  congr 1
  rw [←mul_assoc,mul_sum]
  apply sum_congr rfl
  intro i _
  field_simp

private theorem eval_geometric (n q : ℕ) (hn : 3≤n) :
    (GeneralRealization.geometricEhrhart (n-3)).eval (q:ℚ) =
    ∑ i ∈ range (q+1), ((q:ℚ)+1-i)*(Cert.traceCount n (i+1):ℚ) := by
  rw [GeneralRealization.ehrhart_by_sides hn,FaceOrder.eval_ehrhartPolynomial,
    Tally.card_labeling_eq_traceCount, show n-1+1=n by omega,
    Fin.sum_univ_eq_sum_range (fun i ↦ (q+1-i)*Cert.traceCount n (i+1)),Nat.cast_sum]
  apply sum_congr rfl
  intro i hi
  rw [Nat.cast_mul,Nat.cast_sub (le_of_lt (mem_range.mp hi)),Nat.cast_succ]

/-- Finite original-trace coefficients, with the logarithmic and inverse-sine factors in order. -/
abbrev amplit (n k : ℕ) : ℝ := coeff (2*k) FormalCosine.logSec *
  coeff (2*n) (FormalCosine.inverseSine^(2*k))

/-- Polynomial identity in the dilation variable for the actual face-lattice order polytope. -/
theorem geometric_polynomial {n : ℕ} (hn : 3 ≤ n) :
    Polynomial.C ((4:ℝ)^n/n)*(GeneralRealization.geometricEhrhart (n-3)).map (Rat.castHom ℝ) =
    ∑ k ∈ range (n+1), (moment k).map (Rat.castHom ℝ)*Polynomial.C (amplit n k) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℝ))).mono
  rintro _ ⟨q,rfl⟩
  have cast (p : Polynomial ℚ) : (p.map (Rat.castHom ℝ)).eval (q:ℝ) = ((p.eval (q:ℚ) : ℚ) : ℝ) := by
    exact_mod_cast Polynomial.eval_map_apply (p:=p) (f:=Rat.castHom ℝ) (q:ℚ)
  simp only [Set.mem_ofPred_eq,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_finsetSum,
    cast,eval_geometric n q hn,moment_eval]
  push_cast
  rw [mul_sum]
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  have t := FormalCosine.trace_centered_sum (n:=n) (by omega) (i+1)
  push_cast at t
  have v : 2*((i:ℝ)+1)+1 = 2*i+3 := by ring
  rw [v] at t
  rw [show (4:ℝ)^n/n*(((q:ℝ)+1-i)*(Cert.traceCount n (i+1):ℝ)) =
    ((q:ℝ)+1-i)*(4^n*((Cert.traceCount n (i+1):ℝ)/n)) by ring, t,mul_sum]
  apply sum_congr rfl
  intro k _
  unfold amplit
  ring

/-- Coefficient readout with the exact 5/2 and 1/2 endpoint corrections. -/
theorem actual_ordinary_coefficient {n r : ℕ} (hn : 3 ≤ n) (hr : 1 ≤ r) :
    (4:ℝ)^n/n * ((GeneralRealization.geometricEhrhart (n-3)).coeff r : ℝ) =
      ∑ k ∈ range (n+1), (((if r ≤ 2*k+2 then ((2*k).factorial:ℚ)/4 *
        (PolygonKernel.g (2*k+2-r)*2^r/r.factorial) else 0) - correction r : ℚ) : ℝ) *
        amplit n k := by
  have h := congrArg (fun p : Polynomial ℝ ↦ p.coeff r) (geometric_polynomial hn)
  simp only [Polynomial.coeff_C_mul,Polynomial.finsetSum_coeff,Polynomial.coeff_mul_C,
    Polynomial.coeff_map,fun k ↦ moment_coeff k r hr] at h
  rw [show ((GeneralRealization.geometricEhrhart (n-3)).coeff r:ℝ) =
      (Rat.castHom ℝ) ((GeneralRealization.geometricEhrhart (n-3)).coeff r) from rfl,h]
  apply sum_congr rfl
  intro k _
  split_ifs <;> norm_num

end PolygonEndpoint
