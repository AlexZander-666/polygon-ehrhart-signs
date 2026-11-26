import PolygonKernel.Definition

/-! Identification with the normalized sinh expression in the proof. -/
namespace PolygonKernel

open PowerSeries
open scoped PowerSeries

/-- The odd part of the formal exponential, namely the formal sinh series. -/
noncomputable def formalSinh : ℚ⟦X⟧ :=
  C (1 / 2 : ℚ) * (rescale (1 : ℚ) (exp ℚ) - rescale (-1 : ℚ) (exp ℚ))

private theorem formalSinh_sq_expand :
    formalSinh ^ 2 =
      C (1 / 4 : ℚ) * (rescale (2 : ℚ) (exp ℚ) + rescale (-2 : ℚ) (exp ℚ) - C 2) := by
  have plus :
      rescale (1 : ℚ) (exp ℚ) ^ 2 = rescale (2 : ℚ) (exp ℚ) := by
    rw [pow_two, exp_mul_exp_eq_exp_add]
    norm_num
  have minus :
      rescale (-1 : ℚ) (exp ℚ) ^ 2 = rescale (-2 : ℚ) (exp ℚ) := by
    rw [pow_two, exp_mul_exp_eq_exp_add]
    norm_num
  have cancel :
      rescale (1 : ℚ) (exp ℚ) * rescale (-1 : ℚ) (exp ℚ) = 1 := by
    rw [exp_mul_exp_eq_exp_add]
    simp
  rw [← plus, ← minus, show C (2 : ℚ) = (2 : ℚ⟦X⟧) from map_ofNat (C (R := ℚ)) 2]
  rw [show C (1 / 4 : ℚ) = (C (1 / 2 : ℚ)) ^ 2 by rw [← map_pow]; norm_num]
  unfold formalSinh
  symm
  calc
    _ = C (1 / 2 : ℚ) ^ 2 *
        (rescale (1 : ℚ) (exp ℚ) ^ 2 + rescale (-1 : ℚ) (exp ℚ) ^ 2 -
          2 * (rescale (1 : ℚ) (exp ℚ) * rescale (-1 : ℚ) (exp ℚ))) := by
        rw [cancel, mul_one]
    _ = _ := by ring

/-- The normalized kernel denominator is the square of sinh after
removing its two vanishing factors of the formal variable. -/
theorem formalSinh_sq : formalSinh ^ 2 = X ^ 2 * H := by
  rw [formalSinh_sq_expand]
  ext n
  rw [coeff_X_pow_mul', coeff_C_mul, map_sub, map_add, coeff_rescale, coeff_rescale]
  cases n with
  | zero => norm_num
  | succ n =>
    cases n with
    | zero => norm_num
    | succ d =>
      have hle : 2 ≤ d + 1 + 1 := by omega
      have hsub : d + 1 + 1 - 2 = d := by omega
      rw [if_pos hle, hsub]
      simp only [H, coeff_mk, coeff_exp, Algebra.algebraMap_self_apply]
      rw [show d + 1 + 1 = d + 2 by omega]
      rw [coeff_C, if_neg (by omega : d + 2 ≠ 0), sub_zero]
      unfold hCoeff
      by_cases even : d % 2 = 0
      · have parity : Even (d + 2) := Nat.even_iff.mpr (by omega)
        rw [if_pos even, parity.neg_pow]
        rw [show (2 : ℚ) ^ (d + 2) = 2 ^ (d + 1) * 2 by rw [pow_succ]]
        ring
      · have parity : Odd (d + 2) := Nat.odd_iff.mpr (by omega)
        rw [if_neg even, parity.neg_pow]
        ring

/-- The coefficients used in the finite check come from the normalized formal
expression (e^{5X}(X/\sinh X)^2), written without division by a nonunit. -/
theorem F_mul_formalSinh_sq :
    F * formalSinh ^ 2 = X ^ 2 * rescale (5 : ℚ) (exp ℚ) := by
  rw [formalSinh_sq, ← H_mul_F]
  ring

/-- This cross-multiplied identity uniquely specifies the formal expression. -/
theorem F_eq_of_formalSinh {G : ℚ⟦X⟧}
    (h : G * formalSinh ^ 2 = X ^ 2 * rescale (5 : ℚ) (exp ℚ)) :
    G = F := by
  rw [formalSinh_sq, ← H_mul_F] at h
  have fact : X ^ 2 * (H * G) = X ^ 2 * (H * F) := by
    convert h using 1; ring
  have nz : H ≠ 0 := by
    intro eq
    have c := congrArg (coeff 0) eq
    simp [H] at c
  exact mul_left_cancel₀ nz (X_pow_mul_cancel fact)

#print axioms formalSinh_sq
#print axioms F_mul_formalSinh_sq
#print axioms F_eq_of_formalSinh

end PolygonKernel
