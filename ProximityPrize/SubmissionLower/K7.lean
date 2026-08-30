import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Q
import ProximityPrize.SubmissionLower.R
namespace ProximityPrize.SubmissionLower.RCN175
open RCN174 RCN256 RCN223
open ProximityPrize.Benchmark
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
abbrev FrozenCoefficientIndex6600:=
 CoefficientIndex weightedCap w seedTotalCap slopeCap
theorem exists_frozen_nonzero_contact_array6600
   (u0 u1:IRSProfile.Index → IRSProfile.Field):
   ∃ theta:FrozenCoefficientIndex6600 → IRSProfile.Field,theta≠0∧
     ∀ (i:IRSProfile.Index) (r:Fin multiplicity),
       contactJet IRSProfile.Field (multiplicity-r.val)
         ((extractBlock IRSProfile.Field weightedCap w seedTotalCap slopeCap
           (IRSProfile.domain i) (u0 i) (u1 i) r.val theta):
             Poly IRSProfile.Field)=0:=by
 apply exists_nonzero_block_equations IRSProfile.Field
   weightedCap w seedTotalCap slopeCap multiplicity
   (fun i:IRSProfile.Index↦IRSProfile.domain i) u0 u1
 rw [show Fintype.card IRSProfile.Index=n by
   norm_num [IRSProfile.Index,n]]
 simpa only [totalContactRank,RCN223.localContactRank,
   RCN256.localRankBound,
   RCN223.contactExponent,
   RCN223.coefficientCount,
   RCN174.coefficientCount,RCN256.contactRankBound,
   RCN256.blockInputCount,
   RCN256.blockKernelLowerBound] using interpolation_gate
theorem exists_frozen_nonzero_polynomial_and_equations6600
   (u0 u1:IRSProfile.Index → IRSProfile.Field):
   ∃ (Q:MvPolynomial (Fin 4) IRSProfile.Field)
     (theta:FrozenCoefficientIndex6600 → IRSProfile.Field),
     Q≠0∧
     Q∈globalCoefficientBox IRSProfile.Field
       weightedCap w seedTotalCap slopeCap∧
     Q=reconstruct IRSProfile.Field weightedCap w seedTotalCap slopeCap theta∧
     ∀ (i:IRSProfile.Index) (r:Fin multiplicity),
       contactJet IRSProfile.Field (multiplicity-r.val)
         ((extractBlock IRSProfile.Field weightedCap w seedTotalCap slopeCap
           (IRSProfile.domain i) (u0 i) (u1 i) r.val theta):
             Poly IRSProfile.Field)=0:=by
 obtain ⟨theta,htheta,hconstraints⟩:=
   exists_frozen_nonzero_contact_array6600 u0 u1
 exact ⟨reconstruct IRSProfile.Field weightedCap w seedTotalCap slopeCap theta,
   theta,
   reconstruct_ne_zero IRSProfile.Field weightedCap w seedTotalCap slopeCap
     theta htheta,
   reconstruct_mem_globalCoefficientBox IRSProfile.Field
     weightedCap w seedTotalCap slopeCap theta,
   rfl,hconstraints⟩
end
end ProximityPrize.SubmissionLower.RCN175
