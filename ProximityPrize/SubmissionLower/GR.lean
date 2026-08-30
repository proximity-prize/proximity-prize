import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.K
import ProximityPrize.SubmissionLower.K7
namespace ProximityPrize.SubmissionLower.RCN320
open ProximityPrize.Benchmark
open RCN174 RCN175 RCN256
open RCN223 RCN319
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
theorem exists_frozen_translated_contact_interpolant6600
   (u0 u1:IRSProfile.Index → IRSProfile.Field):
   ∃ Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q≠0∧
     Q∈globalCoefficientBox IRSProfile.Field
       weightedCap w seedTotalCap slopeCap∧
     ∀ (i:IRSProfile.Index) (r:ℕ),
       slopeDifference IRSProfile.Field^(multiplicity-r)∣
         (homogenizedTranslation IRSProfile.Field
           (IRSProfile.domain i) (u0 i) (u1 i) Q).coeff r:=by
 obtain ⟨Q,theta,hQ,hcaps,hreconstruct,hequations⟩:=
   exists_frozen_nonzero_polynomial_and_equations6600 u0 u1
 refine ⟨Q,hQ,hcaps,?_⟩
 intro i r
 rw [hreconstruct,
   translation_reconstruct_coeff IRSProfile.Field
     weightedCap w seedTotalCap slopeCap]
 exact all_blocks_divisible_of_equations IRSProfile.Field
   weightedCap w seedTotalCap slopeCap multiplicity
   (IRSProfile.domain i) (u0 i) (u1 i) theta (hequations i) r
theorem exists_frozen_universal_vanishing_interpolant6600
   (u0 u1:IRSProfile.Index → IRSProfile.Field):
   ∃ Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q≠0∧
     Q∈globalCoefficientBox IRSProfile.Field
       weightedCap w seedTotalCap slopeCap∧
     ∀ (gamma:IRSProfile.Field) (P:Polynomial IRSProfile.Field)
       (support:Finset IRSProfile.Index),
       P.natDegree ≤ w → agreements ≤ support.card →
       (∀ i∈support,
         P.eval (IRSProfile.domain i)=u0 i+gamma*u1 i) →
       specialization IRSProfile.Field P gamma Q=0:=by
 classical
 obtain ⟨Q,hQ,hcaps,hcontact⟩:=
   exists_frozen_translated_contact_interpolant6600 u0 u1
 refine ⟨Q,hQ,hcaps,?_⟩
 intro gamma P support hP hcard hvalues
 apply specialization_eq_zero_of_contact_and_degree IRSProfile.Field Q P gamma
   IRSProfile.domain u0 u1 support multiplicity
 · intro i hi r
   exact hcontact i r
 · exact hvalues
 · have hdegree:=specialization_natDegree_lt IRSProfile.Field
     weightedCap w seedTotalCap slopeCap Q P gamma
     (by norm_num [RCN223.weightedCap,
       RCN223.multiplicity,
       RCN223.agreements,
       RCN223.n,
       RCN223.errors])
     hcaps hP
   have hbound:weightedCap ≤
       RCN223.multiplicity*support.card:=by
     rw [RCN223.weightedCap]
     exact Nat.mul_le_mul_left
       RCN223.multiplicity hcard
   exact hdegree.trans_le hbound
end
end ProximityPrize.SubmissionLower.RCN320
