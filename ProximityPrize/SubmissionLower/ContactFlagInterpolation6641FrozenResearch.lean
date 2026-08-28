import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagInterpolation6641Research
import ProximityPrize.SubmissionLower.ContactFlagParameters6641Research

/-!
# Frozen contact interpolation at the score-66.30 row

This is the numeric `(m,L,s) = (29,601,8)` instantiation of the generic
contact-rank kernel.  Its sole arithmetic input is the exact positive
dimension margin in `ContactFlagParameters6641Research`.
-/

namespace ProximityPrize.SubmissionLower.ContactFlagInterpolation6641FrozenResearch

open ContactFlagInterpolation6641Research ContactFlagRankKernel6641Research ContactFlagParameters6641Research
open ProximityPrize.Benchmark

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

abbrev FrozenCoefficientIndex6641 :=
  CoefficientIndex weightedCap w seedTotalCap slopeCap

theorem exists_frozen_nonzero_contact_array6641
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ theta : FrozenCoefficientIndex6641 → IRSProfile.Field, theta ≠ 0 ∧
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
  simpa only [totalContactRank, ContactFlagParameters6641Research.localContactRank,
    ContactFlagRankKernel6641Research.localRankBound,
    ContactFlagParameters6641Research.contactExponent,
    ContactFlagParameters6641Research.coefficientCount,
    ContactFlagInterpolation6641Research.coefficientCount, ContactFlagRankKernel6641Research.contactRankBound,
    ContactFlagRankKernel6641Research.blockInputCount,
    ContactFlagRankKernel6641Research.blockKernelLowerBound] using interpolation_gate

theorem exists_frozen_nonzero_polynomial_and_equations6641
    (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    ∃ (Q : MvPolynomial (Fin 4) IRSProfile.Field)
      (theta : FrozenCoefficientIndex6641 → IRSProfile.Field),
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
    exists_frozen_nonzero_contact_array6641 u0 u1
  exact ⟨reconstruct IRSProfile.Field weightedCap w seedTotalCap slopeCap theta,
    theta,
    reconstruct_ne_zero IRSProfile.Field weightedCap w seedTotalCap slopeCap
      theta htheta,
    reconstruct_mem_globalCoefficientBox IRSProfile.Field
      weightedCap w seedTotalCap slopeCap theta,
    rfl, hconstraints⟩

end

end ProximityPrize.SubmissionLower.ContactFlagInterpolation6641FrozenResearch
