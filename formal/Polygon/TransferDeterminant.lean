import Polygon.TransferFactor

/-! The continuant for the determinant of the crown transfer matrix. -/
namespace Polygon.TransferDeterminant

def band (n : ℕ) (a b : ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  if i.val = j.val then (if i.val = 0 then b else a)
  else if i.val+1 = j.val ∨ j.val+1 = i.val then -1 else 0

private theorem tail_entry {n : ℕ} (a b : ℝ) (i j : Fin n) :
    band (n+1) a b i.succ j.succ = band n a a i j := by
  simp [band, Fin.val_succ]

private theorem tail_submatrix (n : ℕ) (a b : ℝ) :
    (band (n+1) a b).submatrix Fin.succ (0 : Fin (n+1)).succAbove = band n a a := by
  ext i j
  exact tail_entry a b i j

private def minor (n : ℕ) (a b : ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  (band (n+2) a b).submatrix Fin.succ (0 : Fin (n+1)).succ.succAbove

private theorem minor_det (n : ℕ) (a b : ℝ) :
    (minor n a b).det = -(band n a a).det := by
  have drop : (minor n a b).submatrix (0 : Fin (n+1)).succAbove Fin.succ = band n a a := by
    ext i j
    simp only [minor, Matrix.submatrix_apply, Fin.zero_succAbove, Fin.succ_succAbove_succ]
    rw [tail_entry, tail_entry]
  have atZero : minor n a b 0 0 = -1 := by
    simp [minor, Matrix.submatrix_apply, band]
  have beyond (i : Fin n) : minor n a b i.succ 0 = 0 := by
    simp [minor, Matrix.submatrix_apply, band, Fin.val_succ]
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, atZero, drop]
  simp [beyond]

theorem band_succ_succ (n : ℕ) (a b : ℝ) : (band (n+2) a b).det =
    b * (band (n+1) a a).det - (band n a a).det := by
  have atZero : band (n+2) a b 0 0 = b := by simp [band]
  have atOne : band (n+2) a b 0 (0 : Fin (n+1)).succ = -1 := by simp [band]
  have beyond (i : Fin n) : band (n+2) a b 0 i.succ.succ = 0 := by simp [band, Fin.val_succ]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ, atZero, atOne,
    tail_submatrix]
  change _ + (_ * (minor n a b).det + _) = _
  rw [minor_det]
  simp [beyond, sub_eq_add_neg]


private theorem empty_det (a b : ℝ) : (band 0 a b).det = 1 := Matrix.det_isEmpty

private theorem singleton_det (a b : ℝ) : (band 1 a b).det = b := by
  simp [Matrix.det_unique, band]

theorem band_recurrence (n : ℕ) (a b : ℝ) :
    (band (n+2) a b).det = a*(band (n+1) a b).det - (band n a b).det := by
  cases n with
  | zero => simp [band_succ_succ, band, mul_comm]
  | succ n =>
    cases n with
    | zero =>
      rw [band_succ_succ, band_succ_succ 0, band_succ_succ 0, singleton_det,
        empty_det, singleton_det]
      ring
    | succ n =>
      have h1 := band_succ_succ n a a
      have h2 := band_succ_succ (n+1) a a
      rw [band_succ_succ, band_succ_succ (n+1) a b, band_succ_succ n a b, h2, h1]
      ring

open TransferFactor

noncomputable def characteristic (m : ℕ) (z : ℝ) : ℝ :=
    (1 - z • (Cert.transfer m).map (Nat.cast : ℕ → ℝ)).det

theorem characteristic_eq_band (m : ℕ) (z : ℝ) :
    characteristic m z = (band m (2-z) (1-z)).det := by
  let A := (Cert.transfer m).map (Nat.cast : ℕ → ℝ)
  have hdet : A.det = 1 := det_transfer m
  have hu : IsUnit A.det := hdet ▸ isUnit_one
  have prod : A * (A⁻¹-z • 1) = 1 - z • A := by
    rw [mul_sub, Matrix.mul_nonsing_inv A hu, Matrix.mul_smul, mul_one]
  have eqband : A⁻¹-z • 1 = band m (2-z) (1-z) := by
    ext i j
    simp only [A, Matrix.sub_apply, inverse_entry, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, band]
    by_cases eq : i = j
    · subst j
      by_cases hi : i.val = 0 <;> simp [hi, Nat.pos_iff_ne_zero] 
      ring
    · have hne := (Fin.val_inj.not).2 eq
      have noBoth : ¬(i.val+1=j.val ∧ j.val+1=i.val) := by omega
      split_ifs <;> simp_all
  change (1-z • A).det = _
  rw [← prod, Matrix.det_mul, hdet, one_mul, eqband]

theorem recurrence (m : ℕ) (z : ℝ) :
    characteristic (m+2) z = (2-z)*characteristic (m+1) z-characteristic m z := by
  simpa only [characteristic_eq_band] using band_recurrence m (2-z) (1-z)

#print axioms recurrence


private lemma char_zero (z : ℝ) : characteristic 0 z = 1 := by
  rw [characteristic_eq_band, empty_det]

private lemma char_one (z : ℝ) : characteristic 1 z = 1-z := by
  rw [characteristic_eq_band, singleton_det]

private lemma cos_step (x t : ℝ) :
    Real.cos (x+2*t) = (2-4*Real.sin t^2)*Real.cos x - Real.cos (x-2*t) := by
  rw [Real.cos_add, Real.cos_sub, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq t,
    congrArg (fun y : ℝ => y * Real.cos x) (Real.sin_sq_add_cos_sq t)]

/-- A denominator-free form of the transfer determinant valid at every real angle. -/
theorem trig_identity (m : ℕ) (t : ℝ) :
    characteristic m (4 * Real.sin t^2) * Real.cos t =
      Real.cos ((2*(m : ℝ)+1)*t) := by
  induction m using Nat.twoStepInduction with
  | zero => simp [char_zero]
  | one =>
    rw [char_one]
    norm_num only [Nat.cast_one, mul_one, show (2:ℝ)+1 = 3 by norm_num]
    rw [Real.cos_three_mul]
    nlinarith [congrArg (fun y : ℝ => y * Real.cos t) (Real.sin_sq_add_cos_sq t)]
  | more n ih ih' =>
    rw [recurrence, sub_mul, mul_assoc, ih', ih]
    push_cast
    have h := cos_step ((2*((n : ℝ)+1)+1)*t) t
    have hm : (2*((n:ℝ)+1)+1)*t-2*t = (2*(n:ℝ)+1)*t := by ring
    have hp : (2*((n:ℝ)+1)+1)*t+2*t = (2*((n:ℝ)+2)+1)*t := by ring
    rw [hm, hp] at h
    exact h.symm

#print axioms trig_identity

end Polygon.TransferDeterminant
