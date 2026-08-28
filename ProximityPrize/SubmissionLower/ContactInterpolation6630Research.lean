import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactInterpolation
import ProximityPrize.SubmissionLower.ContactParameters6630Research

/-!
# Frozen contact interpolation at the score-66.30 row

This is the numeric `(m,L,s) = (29,601,8)` instantiation of the generic
contact-rank kernel.  Its sole arithmetic input is the exact positive
dimension margin in `ContactParameters6630Research`.
-/

namespace ProximityPrize.SubmissionLower.ContactInterpolation6630Research

open ContactInterpolation ContactRankKernel ContactParameters6630Research
open ProximityPrize.Benchmark

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

abbrev FrozenCoefficientIndex6630 :=
  CoefficientIndex weightedCap w seedTotalCap slopeCap

theorem exists_frozen_nonzero_contact_array6630
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ theta : FrozenCoefficientIndex6630 → IRSProfile.Field, theta ≠ 0 ∧
      ∀ (i : IRSProfile.Index) (r : Fin multiplicity),
        contactJet IRSProfile.Field (multiplicity - r.val)
          ((extractBlock IRSProfile.Field weightedCap w seedTotalCap slopeCap
            (IRSProfile.domain i) (u0 i) (u1 i) r.val theta) :
              Poly IRSProfile.Field) = 0 := by
  apply exists_nonzero_block_equations IRSProfile.Field
    weightedCap w seedTotalCap slopeCap multiplicity
    (fun i : IRSProfile.Index ↦ IRSProfile.domain i) u0 u1
  rw [show Fintype.card IRSProfile.Index = n by
    norm_num [IRSProfile.Index, n]]
  simpa only [totalContactRank, ContactParameters6630Research.localContactRank,
    ContactRankKernel.localRankBound,
    ContactParameters6630Research.contactExponent,
    ContactParameters6630Research.coefficientCount,
    ContactInterpolation.coefficientCount, ContactRankKernel.contactRankBound,
    ContactRankKernel.blockInputCount,
    ContactRankKernel.blockKernelLowerBound] using interpolation_gate

theorem exists_frozen_nonzero_polynomial_and_equations6630
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ (Q : MvPolynomial (Fin 4) IRSProfile.Field)
      (theta : FrozenCoefficientIndex6630 → IRSProfile.Field),
      Q ≠ 0 ∧
      Q ∈ globalCoefficientBox IRSProfile.Field
        weightedCap w seedTotalCap slopeCap ∧
      Q = reconstruct IRSProfile.Field weightedCap w seedTotalCap slopeCap theta ∧
      ∀ (i : IRSProfile.Index) (r : Fin multiplicity),
        contactJet IRSProfile.Field (multiplicity - r.val)
          ((extractBlock IRSProfile.Field weightedCap w seedTotalCap slopeCap
            (IRSProfile.domain i) (u0 i) (u1 i) r.val theta) :
              Poly IRSProfile.Field) = 0 := by
  obtain ⟨theta, htheta, hconstraints⟩ :=
    exists_frozen_nonzero_contact_array6630 u0 u1
  exact ⟨reconstruct IRSProfile.Field weightedCap w seedTotalCap slopeCap theta,
    theta,
    reconstruct_ne_zero IRSProfile.Field weightedCap w seedTotalCap slopeCap
      theta htheta,
    reconstruct_mem_globalCoefficientBox IRSProfile.Field
      weightedCap w seedTotalCap slopeCap theta,
    rfl, hconstraints⟩

end

end ProximityPrize.SubmissionLower.ContactInterpolation6630Research

#print axioms ProximityPrize.SubmissionLower.ContactInterpolation6630Research.exists_frozen_nonzero_contact_array6630
#print axioms ProximityPrize.SubmissionLower.ContactInterpolation6630Research.exists_frozen_nonzero_polynomial_and_equations6630
