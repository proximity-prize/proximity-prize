import ProximityPrize.SubmissionLower.Part.G068


section Compact_SecondJetWeightedLocal
/-! The weighted independent family in flat coordinates and under contact. -/
namespace ProximityPrize.SubmissionLower.SecondJetWeightedLocal
open SecondJetBasis SecondJetSupport SecondJetLocal SecondJetWeightedBasis
open SecondJetWeightedSupport MvPolynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

theorem flatEquiv_weightedVector (r h a b : ℕ) (e : Fin 3 →₀ ℕ) :
    flatEquiv (K := K) (weightedVector (K := K) r h a b (e 0) (e 1) (e 2) (min a (e 1))) =
      weightedTerm (K := K) r h a b e := by
  simp only [weightedVector, map_mul, map_pow, map_add, map_sub, flatEquiv_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four]
  simp only [Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  simp only [weightedTerm, SecondJetWeightedContact.family, SecondJetWeightedContact.U,
    SecondJetWeightedContact.V, SecondJetWeightedContact.J, map_mul, map_pow, map_add, map_sub]
  ring

theorem weightedTerm_vanishes (m r h a b : ℕ) (e : Fin 3 →₀ ℕ)
    (horder : m ≤ r+2*a+b) :
    Polynomial.X^m ∣ contact (K := K) (weightedTerm (K := K) r h a b e) := by
  apply (pow_dvd_pow Polynomial.X horder).trans
  unfold weightedTerm
  apply SecondJetWeightedContact.family_contact _ _ _ _ _ _ _ _ _ _ _
    (min_le_left _ _) (contact (K := K)).toRingHom Polynomial.X contact_X
  · have hu : (Polynomial.X : Target (K := K))^2 ∣ contact (K := K)
        (Polynomial.C (Polynomial.C SecondJetLocal.v)+Polynomial.X*Polynomial.C Polynomial.X) :=
      ⟨Polynomial.C (MvPolynomial.X 1), contact_u⟩
    simpa only [SecondJetWeightedContact.U, SecondJetWeightedContact.V,
      SecondJetLocal.v, map_sub, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hu
  · have hv : (Polynomial.X : Target (K := K)) ∣
        contact (K := K) (Polynomial.C (Polynomial.C SecondJetLocal.v)) := by
      rw [contact_v]
      exact dvd_mul_right _ _
    simpa only [SecondJetWeightedContact.V, SecondJetLocal.v, map_sub, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hv


end
end ProximityPrize.SubmissionLower.SecondJetWeightedLocal

end Compact_SecondJetWeightedLocal
