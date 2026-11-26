import Polygon.Trace

/-! Factorization of the actual transfer matrix used in the polygon counting theorem. -/
namespace Polygon.TransferFactor

def upper (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := fun i j => if i ≤ j then 1 else 0

theorem gram (m : ℕ) :
    (Cert.transfer m).map (Nat.cast : ℕ → ℝ) = upper m * (upper m).transpose := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.map_apply, Matrix.transpose_apply]
  have summand (k : Fin m) : upper m i k * upper m j k =
      (if max i j ≤ k then (1 : ℝ) else 0) := by
    simp only [upper, max_le_iff]
    split_ifs <;> simp_all
  simp_rw [summand]
  rw [Finset.sum_boole]
  have subset : Finset.univ.filter (fun k : Fin m => max i j ≤ k) = Finset.Ici (max i j) := by
    ext k; simp
  rw [subset, Fin.card_Ici]
  rfl

theorem det_upper (m : ℕ) : (upper m).det = 1 := by
  have h : (upper m).IsUpperTriangular := by
    intro i j hji
    exact if_neg (not_le.mpr hji)
  rw [Matrix.det_of_isUpperTriangular h]
  simp [upper]

theorem det_transfer (m : ℕ) : ((Cert.transfer m).map (Nat.cast : ℕ → ℝ)).det = 1 := by
  rw [gram, Matrix.det_mul, Matrix.det_transpose, det_upper, mul_one]

#print axioms gram
#print axioms det_transfer

def shift (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := fun i j =>
  if i.val + 1 = j.val then 1 else 0

private theorem shift_mul_upper (m : ℕ) (i j : Fin m) :
    (shift m * upper m) i j = if i < j then 1 else 0 := by
  rw [Matrix.mul_apply]
  by_cases h : i.val+1 < m
  · let s : Fin m := ⟨i.val+1,h⟩
    have hshift (k : Fin m) : shift m i k = if k = s then 1 else 0 := by
      simp only [shift]
      congr 1
      exact propext ⟨fun e => Fin.ext e.symm, fun e => congrArg Fin.val e.symm⟩
    simp_rw [hshift, ite_mul, one_mul, zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  · have hz (k : Fin m) : shift m i k = 0 := by
      apply if_neg
      have := k.isLt
      omega
    simp_rw [hz, zero_mul]
    simp only [Finset.sum_const_zero]
    rw [if_neg]
    intro hij
    exact h (lt_of_le_of_lt (show i.val+1 ≤ j.val from hij) j.isLt)

theorem difference_mul_upper (m : ℕ) : (1 - shift m) * upper m = 1 := by
  rw [sub_mul, one_mul]
  ext i j
  rw [Matrix.sub_apply, shift_mul_upper, Matrix.one_apply]
  simp only [upper]
  split_ifs <;> simp_all <;> omega

theorem inv_transfer (m : ℕ) : ((Cert.transfer m).map (Nat.cast : ℕ → ℝ))⁻¹ =
    (1-shift m).transpose * (1-shift m) := by
  rw [gram, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv,
      Matrix.inv_eq_left_inv (difference_mul_upper m)]

#print axioms inv_transfer


private theorem shift_gram {m : ℕ} (i j : Fin m) :
    ((shift m).transpose * shift m) i j = if i = j ∧ 0 < i.val then 1 else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  by_cases pos : 0 < i.val
  · let pred : Fin m := ⟨i.val-1, by have := i.isLt; omega⟩
    have hs (k : Fin m) : shift m k i = if k = pred then 1 else 0 := by
      simp only [shift]
      congr 1
      apply propext
      constructor
      · intro e; apply Fin.ext; change k.val = i.val-1; omega
      · rintro rfl; change i.val-1+1 = i.val; omega
    simp_rw [hs, ite_mul, one_mul, zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, shift, pos, and_true]
    have h : pred.val + 1 = i.val := by change i.val-1+1 = i.val; omega
    by_cases e : i = j <;> simp [h, e, Fin.val_inj]
  · have hs (k : Fin m) : shift m k i = 0 := by apply if_neg; omega
    simp_rw [hs, zero_mul]
    simp [pos]

/-- Every entry of the tridiagonal inverse, including the exceptional first diagonal. -/
theorem inverse_entry {m : ℕ} (i j : Fin m) :
    (((Cert.transfer m).map (Nat.cast : ℕ → ℝ))⁻¹) i j =
      (if i = j then 1 else 0) - (if j.val+1 = i.val then 1 else 0) -
      (if i.val+1 = j.val then 1 else 0) +
      (if i = j ∧ 0 < i.val then 1 else 0) := by
  rw [inv_transfer, Matrix.transpose_sub, Matrix.transpose_one, sub_mul, one_mul,
      mul_sub, mul_one]
  simp only [Matrix.sub_apply, Matrix.transpose_apply, Matrix.one_apply, shift_gram, shift]
  ring

#print axioms inverse_entry

end Polygon.TransferFactor
