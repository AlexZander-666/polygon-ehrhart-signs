import Polygon.TransferDeterminant

/-! The positive, pairwise distinct spectral parameters of the crown transfer matrix. -/
namespace Polygon.TransferSpectrum
open Polygon.TransferDeterminant

noncomputable def angle {m : ℕ} (j : Fin m) : ℝ :=
  ((j.val : ℝ) + 1/2) * Real.pi / (2*(m:ℝ)+1)

noncomputable def parameter {m : ℕ} (j : Fin m) : ℝ := 4*(Real.sin (angle j))^2

theorem angle_mem {m : ℕ} (j : Fin m) : 0 < angle j ∧ angle j < Real.pi/2 := by
  have hj : (j.val : ℝ) < m := by exact_mod_cast j.isLt
  constructor
  · unfold angle; positivity
  · unfold angle
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith [mul_pos (sub_pos.mpr hj) Real.pi_pos]

theorem positive {m : ℕ} (j : Fin m) : 0 < parameter j := by
  have h := angle_mem j
  have hsin := Real.sin_pos_of_pos_of_lt_pi h.1 (by linarith [Real.pi_pos])
  unfold parameter
  positivity

theorem strictMono (m : ℕ) : StrictMono (@parameter m) := by
  intro i j hij
  have h : angle i < angle j := by
    unfold angle
    exact div_lt_div_of_pos_right
      (mul_lt_mul_of_pos_right (add_lt_add_left (by exact_mod_cast (show i.val < j.val from hij) : (i.val:ℝ)<j.val) _) Real.pi_pos)
      (by positivity)
  have hi := angle_mem i
  have hj := angle_mem j
  have hsin := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos, hi.1]) hj.2.le h
  have hpos := Real.sin_pos_of_pos_of_lt_pi hi.1 (by linarith [Real.pi_pos])
  unfold parameter
  nlinarith [sq_nonneg (Real.sin (angle j)-Real.sin (angle i)),
    mul_pos (sub_pos.mpr hsin) hpos]

theorem characteristic_zero {m : ℕ} (j : Fin m) : characteristic m (parameter j) = 0 := by
  have hp : 0 < 2*(m:ℝ)+1 := by positivity
  have index : (2*(m:ℝ)+1)*angle j = (j.val:ℝ)*Real.pi+Real.pi/2 := by
    unfold angle
    field_simp
  have h := trig_identity m (angle j)
  rw [index, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero] at h
  have bounds := angle_mem j
  exact (mul_eq_zero.mp h).resolve_right
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [bounds.1, Real.pi_pos], bounds.2⟩).ne'

#print axioms characteristic_zero

noncomputable def realTransfer (m : ℕ) := (Cert.transfer m).map (Nat.cast : ℕ → ℝ)

theorem eigen_root {m : ℕ} (j : Fin m) :
    (realTransfer m).charpoly.eval (parameter j)⁻¹ = 0 := by
  let A := realTransfer m
  let z := parameter j
  have hz : z ≠ 0 := (positive j).ne'
  have scalar : Matrix.scalar (Fin m) z⁻¹ = z⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ) := by
    ext i k
    by_cases h : i = k <;> simp [Matrix.scalar_apply, h]
  have factor : Matrix.scalar (Fin m) z⁻¹ - A = z⁻¹ • (1-z • A) := by
    rw [scalar, smul_sub, smul_smul, inv_mul_cancel₀ hz, one_smul]
  change A.charpoly.eval z⁻¹ = 0
  rw [Matrix.eval_charpoly, factor, Matrix.det_smul]
  change _ * characteristic m (parameter j) = 0
  rw [characteristic_zero, mul_zero]

noncomputable def values (m : ℕ) : Finset ℝ :=
  Finset.univ.image fun j : Fin m => (parameter j)⁻¹

theorem roots (m : ℕ) : (realTransfer m).charpoly.roots = (values m).val := by
  apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
  · intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact eigen_root j
  · have inj : Function.Injective (fun j : Fin m => (parameter j)⁻¹) :=
      inv_injective.comp (strictMono m).injective
    simp [values, Finset.card_image_of_injective _ inj, Matrix.charpoly_natDegree_eq_dim]
  · exact (realTransfer m).charpoly_monic.ne_zero

#print axioms roots


private theorem hermitian (m : ℕ) : (realTransfer m).IsHermitian := by
  ext i j
  simp [realTransfer, Cert.transfer, Matrix.conjTranspose_apply, max_comm]

/-- Actual integer crown-label counts equal the sum of the explicit spectral powers. -/
theorem traceCount (n m : ℕ) : (Cert.traceCount n m : ℝ) =
    ∑ j : Fin m, ((parameter j)⁻¹)^n := by
  let A := realTransfer m
  have hA : A.IsHermitian := hermitian m
  have casttrace : (Cert.traceCount n m : ℝ) = (A^n).trace := by
    rw [Cert.traceCount_correct]
    change (((Cert.transfer m ^ n).trace : ℕ) : ℝ) =
      (((Cert.transfer m).map (Nat.castRingHom ℝ)) ^ n).trace
    rw [← Matrix.map_pow]
    simp [Matrix.trace, Matrix.diag]
  have eqeig : (A^n).trace = ∑ j, (hA.eigenvalues j)^n := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul, Matrix.diagonal_pow]
    simp [Matrix.trace, Matrix.diag]
  have r := hA.roots_charpoly_eq_eigenvalues.symm.trans (roots m)
  have sums := congrArg (fun s : Multiset ℝ => (s.map (fun x => x^n)).sum) r
  have inj : Function.Injective (fun j : Fin m => (parameter j)⁻¹) :=
    inv_injective.comp (strictMono m).injective
  rw [casttrace, eqeig]
  unfold values at sums
  rw [Finset.image_val_of_injOn (fun _ _ _ _ h => inj h)] at sums
  simpa [Multiset.map_map, Function.comp_def, List.sum_ofFn] using sums

#print axioms traceCount

end Polygon.TransferSpectrum
