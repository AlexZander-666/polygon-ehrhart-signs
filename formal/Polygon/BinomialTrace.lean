import Polygon.BinomialContinuant
import Polygon.TransferSpectrum
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-! Newton's recurrence with integer binomial coefficients for the original crown trace. -/
namespace Polygon.BinomialTrace

open Polynomial TransferSpectrum

noncomputable def eig {m : ℕ} (j : Fin m) : ℝ := (parameter j)⁻¹

private theorem root_list (m : ℕ) :
    (realTransfer m).charpoly.roots = Finset.univ.val.map (@eig m) := by
  have inj : Function.Injective (@eig m) := inv_injective.comp (strictMono m).injective
  rw [roots]
  change (Finset.univ.image (@eig m)).val = _
  exact Finset.image_val_of_injOn (fun _ _ _ _ h => inj h)

theorem elementary (m k : ℕ) :
    (Finset.univ.val.map (@eig m)).esymm k = (Nat.choose (m+k) (2*k) : ℝ) := by
  let A := realTransfer m
  have card : A.charpoly.roots.card = m := by simp [A, root_list]
  have deg : A.charpoly.natDegree = m := by simp [Matrix.charpoly_natDegree_eq_dim]
  rw [← root_list]
  change A.charpoly.roots.esymm k = _
  by_cases hk : k ≤ m
  · have v := Polynomial.coeff_eq_esymm_roots_of_card (card.trans deg.symm)
        (k := m-k) (by omega)
    rw [deg, show m-(m-k) = k by omega, A.charpoly_monic.leadingCoeff, one_mul] at v
    have b := BinomialContinuant.reverse_coeff m k
    change A.charpolyRev.coeff k = _ at b
    rw [← Matrix.reverse_charpoly, coeff_reverse, deg, revAt_le hk, v] at b
    exact mul_left_cancel₀ (pow_ne_zero k (by norm_num : (-1:ℝ)≠0)) b
  · rw [Nat.choose_eq_zero_of_lt (by omega), Multiset.esymm,
      Multiset.powersetCard_eq_empty k (by omega)]
    simp

private theorem evaluated_psum (m t : ℕ) :
    MvPolynomial.aeval (@eig m) (MvPolynomial.psum (Fin m) ℝ t) =
      (Cert.traceCount t m : ℝ) := by
  rw [TransferSpectrum.traceCount]
  simp [MvPolynomial.psum, eig]

/-- Newton's identity for the exact crown trace, independent of the numerical eigenvalues. -/
theorem trace_recurrence (m k : ℕ) (hk : 0 < k) :
    (Cert.traceCount k m : ℝ) = (-1 : ℝ)^(k+1)*k*(Nat.choose (m+k) (2*k) : ℝ) -
      ∑ a ∈ (Finset.HasAntidiagonal.antidiagonal k).filter (fun a : ℕ × ℕ => a.1 ∈ Set.Ioo 0 k),
        (-1 : ℝ)^a.1*(Nat.choose (m+a.1) (2*a.1) : ℝ)*(Cert.traceCount a.2 m : ℝ) := by
  have h := congrArg (MvPolynomial.aeval (@eig m))
    (MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin m) ℝ k hk)
  simpa only [map_sub, map_mul, map_neg, map_pow, map_one, map_natCast, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, elementary, evaluated_psum] using h

/-- Integer arithmetic suffices for all entries of the recurrence, including empty width. -/
theorem trace_integer (m k : ℕ) (hk : 0 < k) :
    (Cert.traceCount k m : ℤ) = (-1 : ℤ)^(k+1)*k*(Nat.choose (m+k) (2*k) : ℤ) -
      ∑ a ∈ (Finset.HasAntidiagonal.antidiagonal k).filter (fun a : ℕ × ℕ => a.1 ∈ Set.Ioo 0 k),
        (-1 : ℤ)^a.1*(Nat.choose (m+a.1) (2*a.1) : ℤ)*(Cert.traceCount a.2 m : ℤ) := by
  exact_mod_cast trace_recurrence m k hk

#print axioms trace_integer
#print axioms elementary
#print axioms trace_recurrence
end Polygon.BinomialTrace
