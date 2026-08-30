import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.AB
import ProximityPrize.SubmissionLower.GG
namespace ProximityPrize.SubmissionLower.ContactStackedGCDCover6670Research
open ProximityPrize.Benchmark
open ContactInterpolation ContactTranslation
open ContactRecursiveGCDResearch
open ContactStackedParameters6670Research
open ContactStackedInterpolation6670Research
noncomputable section
abbrev GlobalPoly:=MvPolynomial (Fin 4) IRSProfile.Field
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
local instance:GCDMonoid GlobalPoly:=
 UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
def RecursiveSpecializationBranch
   (P:Polynomial IRSProfile.Field) (gamma:IRSProfile.Field)
   (QA QB QC:GlobalPoly):Prop:=
 let phi:=(specialization IRSProfile.Field P gamma).toRingHom
 (phi (gcd12 QA QB)≠0∧
     phi (quotientA QA QB)=0∧phi (quotientB QA QB)=0)∨
   (phi (gcd12 QA QB)=0∧phi (gcd123 QA QB QC)≠0∧
     phi (middleQuotient QA QB QC)=0∧
     phi (quotientC QA QB QC)=0)∨
   (phi (gcd123 QA QB QC)=0∧phi (gcd12 QA QB)=0)
theorem recursive_branch_of_three_vanishings
   (P:Polynomial IRSProfile.Field) (gamma:IRSProfile.Field)
   (QA QB QC:GlobalPoly)
   (hA:specialization IRSProfile.Field P gamma QA=0)
   (hB:specialization IRSProfile.Field P gamma QB=0)
   (hC:specialization IRSProfile.Field P gamma QC=0):
   RecursiveSpecializationBranch P gamma QA QB QC:=by
 exact recursive_three_branch_cover
   (specialization IRSProfile.Field P gamma).toRingHom QA QB QC hA hB hC
theorem exists_stacked_interpolants_with_recursive_cover
   (u0 u1:IRSProfile.Index → IRSProfile.Field):
   ∃ QA QB QC:GlobalPoly,
     QA≠0∧
     QA∈globalCoefficientBox IRSProfile.Field
       (34*agreements) w 20000 10∧
     QB≠0∧
     QB∈globalCoefficientBox IRSProfile.Field
       (68*agreements) w 900 21∧
     QC≠0∧
     QC∈globalCoefficientBox IRSProfile.Field
       (37*agreements) w 42000 9∧
     QB∈ContactFlagInterpolation6641Research.globalCoefficientBox IRSProfile.Field
       (68*agreements) w 900 21∧
     ∀ (gamma:IRSProfile.Field) (P:Polynomial IRSProfile.Field)
       (support:Finset IRSProfile.Index),
       P.natDegree ≤ w → agreements ≤ support.card →
       (∀ i∈support,
         P.eval (IRSProfile.domain i)=u0 i+gamma*u1 i) →
       RecursiveSpecializationBranch P gamma QA QB QC:=by
 obtain ⟨QA,QB,QC,hQA,hboxA,hQB,hboxB,hQC,hboxC,hflagB,huniversal⟩:=
   exists_stacked_universal_vanishing_interpolants u0 u1
 refine ⟨QA,QB,QC,hQA,hboxA,hQB,hboxB,hQC,hboxC,hflagB,?_⟩
 intro gamma P support hP hcard hvalues
 obtain ⟨hA,hB,hC⟩:=huniversal gamma P support hP hcard hvalues
 exact recursive_branch_of_three_vanishings P gamma QA QB QC hA hB hC
end
end ProximityPrize.SubmissionLower.ContactStackedGCDCover6670Research
