import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagTranslation6641Research
import ProximityPrize.SubmissionLower.ContactFlagInterpolation6641FrozenResearch
import ProximityPrize.SubmissionLower.ContactTranslation

/-!
# Universal vanishing interpolant at score 66.30

The generic translation theorem turns the frozen order-29 contact equations
into specialization vanishing for every degree-`w` polynomial agreeing on
at least `agreements = 183070` coordinates.
-/

namespace ProximityPrize.SubmissionLower.ContactTranslation6630Research

open ProximityPrize.Benchmark
open ContactFlagInterpolation6641Research ContactFlagInterpolation6641FrozenResearch ContactFlagRankKernel6641Research
open ContactFlagParameters6641Research ContactFlagTranslation6641Research

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

/-- The flag-complete box is a subspace of the legacy rectangular box with
the same total cap.  This adapter lets the downstream factor machinery reuse
all of its established singular and specialization interfaces. -/
theorem flagCoefficientBox_le_rectangular (K : Type*) [Field K]
    (D w L s : ℕ) :
    globalCoefficientBox K D w L s ≤
      ContactInterpolation.globalCoefficientBox K D w L s := by
  apply MvPolynomial.restrictSupport_mono
  intro d hd
  change d 1 + d 2 + d 3 ≤ L ∧ d 2 ≤ s ∧
    d 0 + w * d 1 + (w - 1) * d 2 < D at hd
  change d 1 + d 3 ≤ L ∧ d 2 ≤ s ∧
    d 0 + w * d 1 + (w - 1) * d 2 < D
  exact ⟨by omega, hd.2.1, hd.2.2⟩

theorem exists_frozen_translated_contact_interpolant6630
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
      Q ≠ 0 ∧
      Q ∈ globalCoefficientBox IRSProfile.Field
        weightedCap w seedTotalCap slopeCap ∧
      ∀ (i : IRSProfile.Index) (r : ℕ),
        slopeDifference IRSProfile.Field ^ (multiplicity - r) ∣
          (homogenizedTranslation IRSProfile.Field
            (IRSProfile.domain i) (u0 i) (u1 i) Q).coeff r := by
  obtain ⟨Q, theta, hQ, hcaps, hreconstruct, hequations⟩ :=
    exists_frozen_nonzero_polynomial_and_equations6641 u0 u1
  refine ⟨Q, hQ, hcaps, ?_⟩
  intro i r
  rw [hreconstruct,
    translation_reconstruct_coeff IRSProfile.Field
      weightedCap w seedTotalCap slopeCap]
  exact all_blocks_divisible_of_equations IRSProfile.Field
    weightedCap w seedTotalCap slopeCap multiplicity
    (IRSProfile.domain i) (u0 i) (u1 i) theta (hequations i) r

theorem exists_frozen_universal_vanishing_interpolant6630
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
      Q ≠ 0 ∧
      Q ∈ ContactInterpolation.globalCoefficientBox IRSProfile.Field
        weightedCap w seedTotalCap slopeCap ∧
      Q ∈ globalCoefficientBox IRSProfile.Field
        weightedCap w seedTotalCap slopeCap ∧
      ∀ (gamma : IRSProfile.Field) (P : Polynomial IRSProfile.Field)
        (support : Finset IRSProfile.Index),
        P.natDegree ≤ w → agreements ≤ support.card →
        (∀ i ∈ support,
          P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i) →
        ContactTranslation.specialization IRSProfile.Field P gamma Q = 0 := by
  classical
  obtain ⟨Q, hQ, hcaps, hcontact⟩ :=
    exists_frozen_translated_contact_interpolant6630 u0 u1
  have hrect := flagCoefficientBox_le_rectangular IRSProfile.Field
    weightedCap w seedTotalCap slopeCap hcaps
  refine ⟨Q, hQ, hrect, hcaps, ?_⟩
  intro gamma P support hP hcard hvalues
  have hzero : specialization IRSProfile.Field P gamma Q = 0 := by
    apply specialization_eq_zero_of_contact_and_degree IRSProfile.Field Q P gamma
      IRSProfile.domain u0 u1 support multiplicity
    · intro i hi r
      exact hcontact i r
    · exact hvalues
    · have hdegree := specialization_natDegree_lt IRSProfile.Field
        weightedCap w seedTotalCap slopeCap Q P gamma
        (by norm_num [ContactFlagParameters6641Research.weightedCap,
          ContactFlagParameters6641Research.multiplicity,
          ContactFlagParameters6641Research.agreements,
          ContactFlagParameters6641Research.n,
          ContactFlagParameters6641Research.errors])
        hcaps hP
      have hbound : weightedCap ≤
        ContactFlagParameters6641Research.multiplicity * support.card := by
        rw [ContactFlagParameters6641Research.weightedCap]
        exact Nat.mul_le_mul_left
          ContactFlagParameters6641Research.multiplicity hcard
      exact hdegree.trans_le hbound
  have hspec : ContactFlagTranslation6641Research.specialization
      IRSProfile.Field P gamma =
      ContactTranslation.specialization IRSProfile.Field P gamma := by
    rfl
  rw [← DFunLike.congr_fun hspec Q]
  exact hzero

end

end ProximityPrize.SubmissionLower.ContactTranslation6630Research
