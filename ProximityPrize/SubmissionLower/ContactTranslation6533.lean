import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactTranslation
import ProximityPrize.SubmissionLower.ContactInterpolation6533

/-!
# Actual universal vanishing interpolant at the 65.67 row

This isolated wrapper identifies the new coefficient array with the existing
symbolic translation theorem and derives the universal specialization
vanishing statement at 183,689 agreements.
-/

namespace ProximityPrize.SubmissionLower.ContactTranslation6533

open ProximityPrize.Benchmark
open ContactInterpolation ContactInterpolation6533 ContactRankKernel
open ContactParameters6533 ContactTranslation

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

/-- A genuine nonzero interpolant whose translated coefficient at every
node is divisible by the required order-22 contact power. -/
theorem exists_frozen_translated_contact_interpolant6533
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
      Q ≠ 0 ∧
      Q ∈ globalCoefficientBox IRSProfile.Field
        weightedCap w seedTotalCap slopeCap ∧
      Q ∈ fullTriangleBox IRSProfile.Field seedTotalCap ∧
      ∀ (i : IRSProfile.Index) (r : ℕ),
        slopeDifference IRSProfile.Field ^ (multiplicity - r) ∣
          (homogenizedTranslation IRSProfile.Field
            (IRSProfile.domain i) (u0 i) (u1 i) Q).coeff r := by
  obtain ⟨Q, theta, hQ, hcaps, hfull, hreconstruct, hequations⟩ :=
    exists_frozen_nonzero_polynomial_and_equations6533 u0 u1
  refine ⟨Q, hQ, hcaps, hfull, ?_⟩
  intro i r
  rw [hreconstruct,
    translation_reconstruct_coeff IRSProfile.Field
      weightedCap w seedTotalCap slopeCap]
  exact all_blocks_divisible_of_equations IRSProfile.Field
    weightedCap w seedTotalCap slopeCap multiplicity
    (IRSProfile.domain i) (u0 i) (u1 i) theta (hequations i) r

/-- The same nonzero order-22 interpolant vanishes after specialization for
every degree-`w` polynomial agreeing on at least 183,689 nodes. -/
theorem exists_frozen_universal_vanishing_interpolant6533
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
      Q ≠ 0 ∧
      Q ∈ globalCoefficientBox IRSProfile.Field
        weightedCap w seedTotalCap slopeCap ∧
      Q ∈ fullTriangleBox IRSProfile.Field seedTotalCap ∧
      ∀ (gamma : IRSProfile.Field) (P : Polynomial IRSProfile.Field)
        (support : Finset IRSProfile.Index),
        P.natDegree ≤ w → agreements ≤ support.card →
        (∀ i ∈ support,
          P.eval (IRSProfile.domain i) = u0 i + gamma * u1 i) →
        specialization IRSProfile.Field P gamma Q = 0 := by
  classical
  obtain ⟨Q, hQ, hcaps, hfull, hcontact⟩ :=
    exists_frozen_translated_contact_interpolant6533 u0 u1
  refine ⟨Q, hQ, hcaps, hfull, ?_⟩
  intro gamma P support hP hcard hvalues
  apply specialization_eq_zero_of_contact_and_degree IRSProfile.Field Q P gamma
    IRSProfile.domain u0 u1 support multiplicity
  · intro i hi r
    exact hcontact i r
  · exact hvalues
  · have hdegree := specialization_natDegree_lt IRSProfile.Field
      weightedCap w seedTotalCap slopeCap Q P gamma
      (by norm_num [ContactParameters6533.weightedCap,
        ContactParameters6533.multiplicity,
        ContactParameters6533.agreements, ContactParameters6533.n,
        ContactParameters6533.errors]) hcaps hP
    have hbound : weightedCap ≤
        ContactParameters6533.multiplicity * support.card := by
      rw [weightedCap]
      exact Nat.mul_le_mul_left ContactParameters6533.multiplicity hcard
    exact hdegree.trans_le hbound

end

end ProximityPrize.SubmissionLower.ContactTranslation6533

#print axioms ProximityPrize.SubmissionLower.ContactTranslation6533.exists_frozen_translated_contact_interpolant6533
#print axioms ProximityPrize.SubmissionLower.ContactTranslation6533.exists_frozen_universal_vanishing_interpolant6533
