import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSecondContactSFreeInterpolation6660Research
import ProximityPrize.SubmissionLower.ContactInterpolation
import ProximityPrize.SubmissionLower.ContactTranslation

 
















namespace ProximityPrize.SubmissionLower
namespace ContactSecondContactLegacyBridge6660Research

open ContactSecondContactSFreeInterpolation6660Research

set_option autoImplicit false

noncomputable section

variable (K : Type*) [Field K]

 
theorem globalCoefficientBox_le_legacy (D w C rCap : Nat) :
    ContactSecondContactSFreeInterpolation6660Research.globalCoefficientBox
        K D w C rCap <=
      ContactInterpolation.globalCoefficientBox K D w C rCap := by
  apply MvPolynomial.restrictSupport_mono
  intro d hd
  change
    d 1 + d 2 + d 3 ≤ C ∧ d 2 ≤ rCap ∧
        d 0 + w * d 1 + (w - 1) * d 2 < D at hd
  change
    d 1 + d 3 ≤ C ∧ d 2 ≤ rCap ∧
      d 0 + w * d 1 + (w - 1) * d 2 < D
  exact ⟨by omega, hd.2.1, hd.2.2⟩

theorem mem_legacy_globalCoefficientBox
    (D w C rCap : Nat) (Q : MvPolynomial (Fin 4) K)
    (hQ : Q ∈
      ContactSecondContactSFreeInterpolation6660Research.globalCoefficientBox
        K D w C rCap) :
    Q ∈ ContactInterpolation.globalCoefficientBox K D w C rCap :=
  globalCoefficientBox_le_legacy K D w C rCap hQ

 
theorem specialization_eq_legacy (P : Polynomial K) (gamma : K) :
    ContactSecondContactSFreeInterpolation6660Research.specialization K P gamma =
      ContactTranslation.specialization K P gamma := by
  rfl

theorem specialization_apply_eq_legacy
    (P : Polynomial K) (gamma : K) (Q : MvPolynomial (Fin 4) K) :
    ContactSecondContactSFreeInterpolation6660Research.specialization K P gamma Q =
      ContactTranslation.specialization K P gamma Q := by
  rfl

end

end ContactSecondContactLegacyBridge6660Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactSecondContactLegacyBridge6660Research.globalCoefficientBox_le_legacy
#print axioms ProximityPrize.SubmissionLower.ContactSecondContactLegacyBridge6660Research.mem_legacy_globalCoefficientBox
#print axioms ProximityPrize.SubmissionLower.ContactSecondContactLegacyBridge6660Research.specialization_apply_eq_legacy
