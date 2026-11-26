import PolygonEndpoint.Ehrhart

/-! Total mass of the inverse-sine/log-secant coefficients and the exact low-degree correction. -/
noncomputable section
namespace PolygonEndpoint
open PowerSeries Polygon Polygon.FormalCosine Finset
open scoped PowerSeries

private theorem normalizedLog : (logSec.subst inverseSine)+(logSec.subst inverseSine) =
    -logOf (1-(X : PowerSeries ℝ)^2) := by
  have hi : HasSubst inverseSine := HasSubst.substInvOfIsUnit _ _
  have hu : constantCoeff (cos ℝ)=1 := by simp [←coeff_zero_eq_constantCoeff_apply,cos]
  let A : PowerSeries ℝ →ₐ[ℝ] PowerSeries ℝ := substAlgHom hi
  have ha (f : PowerSeries ℝ) : A f = f.subst inverseSine := congrFun (coe_substAlgHom _) f
  have sq : cos ℝ * cos ℝ = 1 - sin ℝ^2 := by
    have e := square_sum 1
    simp [cosAt,sinAt,rescale_one] at e
    linear_combination e
  have sub : A (cos ℝ * cos ℝ) = 1 - (X:PowerSeries ℝ)^2 := by
    rw [sq,map_sub,map_pow,map_one,ha,sine_inverse]
  rw [←sub,ha,logOf_subst (by rw [map_mul,hu,one_mul]) hi,logOf_mul hu hu,logSec,
    ←ha,←ha,map_neg,map_add]
  ring

private theorem log_sq_even {n : ℕ} (hn : 0<n) :
    coeff (2*n) (logOf (1-(X:PowerSeries ℝ)^2)) = -1/(n:ℝ) := by
  have hx : HasSubst ((X:PowerSeries ℝ)^2) := HasSubst.X_pow (by norm_num)
  have hh : ((-1:ℝ) • (X:PowerSeries ℝ)).subst (X^2:PowerSeries ℝ) = -X^2 := by
    rw [neg_one_smul,←coe_substAlgHom hx,map_neg,coe_substAlgHom hx,subst_X hx]
  have hs : (rescale (-1:ℝ) (log ℝ)).subst (X^2:PowerSeries ℝ) =
      (log ℝ).subst (-X^2:PowerSeries ℝ) := by
    rw [rescale_eq_subst,subst_comp_subst_apply (HasSubst.smul_X' _) hx,hh]
  rw [logOf_eq,show (1-(X:PowerSeries ℝ)^2)-1 = -X^2 by ring,←hs,
    coeff_subst_X_pow (by norm_num : (2:ℕ) ≠ 0)]
  simp [coeff_rescale,coeff_log,hn.ne',pow_succ,←mul_div_assoc,←pow_add]

private lemma coeff_subst_finite {a : PowerSeries ℝ} (h0 : constantCoeff a=0)
    (f : PowerSeries ℝ) (j : ℕ) : coeff j (f.subst a) =
      ∑ i ∈ Finset.range (j+1), coeff i f * coeff j (a^i) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' h0)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply Finset.mem_range.mpr
  by_contra! h
  have hlt : (j : ℕ∞) < (i : ℕ∞) := by exact_mod_cast (show j < i by omega)
  have he := coeff_of_lt_order j ((hlt.trans_le (le_order_pow_of_constantCoeff_eq_zero i h0)))
  exact hi (by simp [he])

private theorem skip_odd (f : ℕ → ℝ) (h : ∀ k, f (2*k+1)=0) (n : ℕ) :
    ∑ k ∈ Finset.range (2*n+1), f k = ∑ k ∈ Finset.range (n+1), f (2*k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)+1 = (2*n+1)+1+1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ _ (2*n+1), h,add_zero,ih,Finset.sum_range_succ _ (n+1)]
    congr 1

theorem amplit_sum {n : ℕ} (hn : 0<n) :
    ∑ k ∈ range (n+1), amplit n k = 1/(2*(n:ℝ)) := by
  have e := congrArg (coeff (2*n)) normalizedLog
  rw [map_add,map_neg,log_sq_even hn,coeff_subst_finite
    (show constantCoeff inverseSine=0 from constantCoeff_substInvOfIsUnit _ _),
    skip_odd _ (fun k ↦ by rw [logSec_odd,zero_mul])] at e
  change (∑ k ∈ range (n+1), amplit n k) + (∑ k ∈ range (n+1), amplit n k) = -(-1/(n:ℝ)) at e
  rw [show (1:ℝ)/(2*n) = (1/(n:ℝ))/2 by ring]
  rw [neg_div,neg_neg] at e
  linarith

/-- Exact ordinary Ehrhart coefficient plus its full low-degree endpoint compensation. -/
theorem corrected_coefficient {n r : ℕ} (hn : 3≤n) (hr : 1≤r) :
    ((4:ℝ)^n/n) * (((GeneralRealization.geometricEhrhart (n-3)).coeff r : ℝ) +
      (correction r:ℝ)/(2*4^n)) =
    ∑ k ∈ range (n+1), ((if r≤2*k+2 then ((2*k).factorial:ℚ)/4 *
      (PolygonKernel.g (2*k+2-r)*2^r/r.factorial) else 0 : ℚ) : ℝ)*amplit n k := by
  have h := actual_ordinary_coefficient hn hr
  simp only [Rat.cast_sub,sub_mul,sum_sub_distrib,←mul_sum,amplit_sum (by omega : 0<n)] at h
  rw [mul_add,h]
  have den : (4:ℝ)^n / n * ((correction r:ℝ)/(2*4^n)) =
      (correction r:ℝ)*(1/(2*(n:ℝ))) := by field_simp
  rw [den,sub_add_cancel]

end PolygonEndpoint
