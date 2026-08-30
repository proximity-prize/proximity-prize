import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.BF
import ProximityPrize.SubmissionLower.CC
import ProximityPrize.SubmissionLower.GC
import ProximityPrize.SubmissionLower.DW
import ProximityPrize.SubmissionLower.AG
namespace ProximityPrize.SubmissionLower.ContactStackedResidualCells6656Research
open scoped Classical BigOperators
open ProximityPrize.Benchmark
open ContactInterpolation ContactTranslation ContactFactorCaps
open ContactPrimeSeedIncidence ContactProperCutSeedCount ContactRecursiveGCDResearch
open ContactStackedParameters6656Research
open ContactStackedGCDCover6656Research
open ContactStackedSeedPartition6656Research
open ContactStackedBoxTransport6656Research
open ContactRecursiveResidualStages6656Research
open ContactTightSingularLedgerResearch
open ContactSingularLedger6600Research
open ContactSingularBranch6600Research
open ContactSingularBranchParameterizedResearch
open ContactAsymmetricResidualStageResearch
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 35000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
abbrev StackedPoly:=MvPolynomial (Fin 4) IRSProfile.Field
local instance:GCDMonoid StackedPoly:=
 UniqueFactorizationMonoid.toGCDMonoid StackedPoly
local instance:CharP IRSProfile.Field prime:=by
 simpa [prime,ContactParameters6600Research.prime] using
   ContactFrozenAlignment6600Research.challenge_field_characteristic6600
def firstResidualQ2Stage:UnequalParameters:=
 ⟨262144,131071,182807,65,14,598,34,7,5263⟩
def firstResidualQ2Ceiling:ℕ:=66773536747163
def secondResidualGcd12Ceiling:ℕ:=370003897865012
theorem optimized_residual_cell_values:
   firstResidualQ2Stage.agreement=⟨17039231,3538917,1379653347⟩∧
     firstResidualQ2Stage.mixedCost=⟨77868,362427,931⟩∧
     firstResidualQ2Stage.regularCountCap=9865174615710∧
     firstResidualQ2Stage.regularCountCap+firstResidualQ2.countCap+1=
       firstResidualQ2Ceiling∧
     residualStageTwo.regularCountCap+secondResidualGcd12.countCap+1=
       secondResidualGcd12Ceiling:=by
 norm_num [firstResidualQ2Stage,firstResidualQ2Ceiling,
   secondResidualGcd12Ceiling,firstResidualQ2,secondResidualGcd12,
   UnequalParameters.agreement,UnequalParameters.leftAgreement,
   UnequalParameters.rightAgreement,UnequalParameters.mixedCost,
   UnequalParameters.regularCountCap,UnequalParameters.regularNumerator,
   UnequalParameters.errors,UnequalParameters.gap,
   TightParameters.countCap,TightParameters.tightNumerator,
   TightParameters.coreNumerator,TightParameters.aggregateCost,
   TightParameters.agreement,TightParameters.implicitYCap,
   TightParameters.algebraicCap,TightParameters.kappa,
   TightParameters.errors,TightParameters.gap,residualStageTwo,dot]
variable {K Iota:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem asymmetric_stage_count_lt_of_regular_factors
   (P:UnequalParameters)
   (S:ContactTightSingularLedgerResearch.TightParameters)
   (Q T:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (p:ℕ) [CharP K p]
   (hs:1 ≤ S.s) (hsmall:S.s < p) (hw:1 ≤ S.w)
   (hchar:S.w < p) (hDw:S.w < S.kappa*S.D)
   (hj:1 ≤ S.algebraicCap)
   (hjYSmall:S.implicitYCap < p)
   (hjZSmall:S.algebraicCap < p)
   (hmixedSmall:2*S.implicitYCap*S.algebraicCap < p)
   (hwa:S.w < S.a) (han:S.a ≤ S.n)
   (hbox:Q∈globalCoefficientBox K S.D S.w S.L S.s)
   (hgap:0 < P.gap) (_hgapEq:S.gap=P.gap)
   (hY:(S.D-1)/S.w ≤ P.leftY)
   (hR:S.s ≤ P.leftR) (hZ:S.L ≤ P.leftZ)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=S.n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ S.w)
   (hQsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0)
   (hTsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma T=0)
   (hagreement:∀ gamma∈Gamma,
     S.a ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma S.w S.errors)
   (hregular:∀ F:ContactAsymmetricResidualStageResearch.RegularIndex Q,
     (regularPairSeeds Q T selected Gamma F).card*P.gap ≤
       (P.n-P.w)*dot P.agreement (regularVector P F.1)+
         (P.errors+1)*P.gap*(regularVector P F.1).z):
   Gamma.card < P.regularCountCap+S.countCap+1:=by
 classical
 have hcover:=card_le_regular_sum_add_singular Q T hQ
   S.D S.w S.L S.s p hs hsmall hw hDw hj hjZSmall hbox
   selected Gamma hQsolution hTsolution
 have hregularScaled:=sum_regular_counts_bound P Q T selected Gamma
   (regularVector_budgets P Q hQ S.D S.w S.L S.s (by omega) hbox hY hR hZ)
   hregular
 have hregularCap:
     (∑ F:ContactAsymmetricResidualStageResearch.RegularIndex Q,
       (regularPairSeeds Q T selected Gamma F).card) ≤ P.regularCountCap:=
   P.regular_count_le _ hgap hregularScaled
 have hsingularOld:=
   ContactSingularBranchParameterizedResearch.TightParameters.singularSeeds_count_le_countCap
     S Q hQ hbox hs hsmall hw hchar hDw hj hjYSmall hjZSmall hmixedSmall
     hwa han selected Gamma nodes x u0 u1 hinj hnodes hdegree hagreement
     hnoPencil
 have hsingular:
     (ContactAsymmetricResidualStageResearch.singularSeeds Q selected Gamma).card ≤
       S.countCap:=by
   change (ContactSingularBranch6600Research.singularSeeds Q selected Gamma).card ≤
     S.countCap
   exact hsingularOld
 omega
theorem quotientB_ne_zero
   (QA QB:StackedPoly) (hQB:QB≠0):quotientB QA QB≠0:=by
 intro hz
 apply hQB
 rw [b_eq_gcd12_mul_quotientB QA QB,hz,mul_zero]
theorem middleQuotient_ne_zero
   (QA QB QC:StackedPoly) (hQA:QA≠0):
   middleQuotient QA QB QC≠0:=by
 intro hz
 apply gcd12_ne_zero (B:=QB) hQA
 rw [gcd12_eq_gcd123_mul_middleQuotient QA QB QC,hz,mul_zero]
theorem firstResidualCell_count_lt
   (QA QB QC:StackedPoly) (hQA:QA≠0) (hQB:QB≠0)
   (hboxA:QA∈globalCoefficientBox IRSProfile.Field
     (25*agreements) w 5263 7)
   (hboxB:QB∈globalCoefficientBox IRSProfile.Field
     (47*agreements) w 598 14)
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field)
   (u0 u1:IRSProfile.Index → IRSProfile.Field)
   (hcover:∀ gamma∈Gamma,
     RecursiveSpecializationBranch (selected gamma) gamma QA QB QC)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
   (hagreement:∀ gamma∈Gamma,
     agreements ≤ ((Finset.univ:Finset IRSProfile.Index).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i)=
         u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma w errors):
   (firstResidualSeeds selected Gamma QA QB).card <
     firstResidualQ2Ceiling:=by
 let Delta:=firstResidualSeeds selected Gamma QA QB
 let Q:=quotientB QA QB
 let T:=quotientA QA QB
 have hsub:Delta ⊆ Gamma:=by
   intro gamma hgamma
   exact (Finset.mem_filter.mp hgamma).1
 have hsolutions:=firstResidualSeeds_quotient_vanish selected Gamma
   QA QB QC hcover
 have hQsolution:∀ gamma∈Delta,
     specialization IRSProfile.Field (selected gamma) gamma Q=0:=
   fun gamma hgamma => (hsolutions gamma hgamma).2
 have hTsolution:∀ gamma∈Delta,
     specialization IRSProfile.Field (selected gamma) gamma T=0:=
   fun gamma hgamma => (hsolutions gamma hgamma).1
 have hQ:Q≠0:=quotientB_ne_zero QA QB hQB
 have hQbox:=quotientB_mem_parent_box QA QB hQB hboxB
 have hTbox:=quotientA_mem_parent_box QA QB hQA hboxA
 have hTcaps:=degree_bounds_of_mem_box T (25*agreements) w 5263 7
   (by norm_num [w]) hTbox
 have hrel:IsRelPrime Q T:=
   (firstQuotients_isRelPrime hQA).symm
 have hdegreeDelta:∀ gamma∈Delta,
     (selected gamma).natDegree ≤ firstResidualQ2.w:=by
   intro gamma hgamma
   simpa [firstResidualQ2,w] using hdegree gamma (hsub hgamma)
 have hagreementDelta:∀ gamma∈Delta,
     firstResidualQ2.a ≤
       ((Finset.univ:Finset IRSProfile.Index).filter (fun i =>
         (selected gamma).eval (IRSProfile.domain i)=
           u0 i+gamma*u1 i)).card:=by
   intro gamma hgamma
   simpa [firstResidualQ2,agreements] using hagreement gamma (hsub hgamma)
 have hnoPencilDelta:NoLargeSelectedPencil selected Delta
     firstResidualQ2.w firstResidualQ2.errors:=by
   simpa [firstResidualQ2,TightParameters.errors,errors,n,agreements,w] using
     noLargeSelectedPencil_mono selected Gamma Delta w errors hsub hnoPencil
 have hstage:=asymmetric_stage_count_lt_of_regular_factors
   firstResidualQ2Stage firstResidualQ2 Q T hQ prime
   (by norm_num [firstResidualQ2])
   (by norm_num [firstResidualQ2,prime])
   (by norm_num [firstResidualQ2])
   (by norm_num [firstResidualQ2,prime])
   (by norm_num [firstResidualQ2,TightParameters.kappa])
   (by norm_num [firstResidualQ2,TightParameters.algebraicCap,
     TightParameters.kappa])
   (by norm_num [firstResidualQ2,prime,TightParameters.implicitYCap,
     TightParameters.kappa])
   (by norm_num [firstResidualQ2,prime,TightParameters.algebraicCap,
     TightParameters.kappa])
   (by norm_num [firstResidualQ2,prime,TightParameters.implicitYCap,
     TightParameters.algebraicCap,TightParameters.kappa])
   (by norm_num [firstResidualQ2])
   (by norm_num [firstResidualQ2])
   hQbox
   (by norm_num [firstResidualQ2Stage,UnequalParameters.gap])
   (by norm_num [firstResidualQ2Stage,firstResidualQ2,
     UnequalParameters.gap,TightParameters.gap])
   (by norm_num [firstResidualQ2Stage,firstResidualQ2])
   (by norm_num [firstResidualQ2Stage,firstResidualQ2])
   (by norm_num [firstResidualQ2Stage,firstResidualQ2])
   selected Delta (Finset.univ:Finset IRSProfile.Index) IRSProfile.domain
   u0 u1 IRSProfile.domain.injective.injOn
   (by norm_num [IRSProfile.Index,firstResidualQ2])
   hdegreeDelta hQsolution hTsolution hagreementDelta hnoPencilDelta
   (all_regularPairSeeds_bound firstResidualQ2Stage Q T hQ hrel
     firstResidualQ2.D firstResidualQ2.w firstResidualQ2.L firstResidualQ2.s
     prime hQbox
     (by norm_num [firstResidualQ2])
     (by norm_num [firstResidualQ2Stage,firstResidualQ2])
     (by norm_num [firstResidualQ2Stage,firstResidualQ2])
     (by norm_num [firstResidualQ2Stage,firstResidualQ2])
     (by simpa [firstResidualQ2Stage,agreements,w] using hTcaps.1)
     (by simpa [firstResidualQ2Stage] using hTcaps.2.1)
     (by simpa [firstResidualQ2Stage] using hTcaps.2.2)
     (by norm_num [firstResidualQ2Stage])
     (by norm_num [firstResidualQ2Stage,prime])
     (by norm_num [firstResidualQ2Stage,prime])
     (by norm_num [firstResidualQ2Stage,prime])
     (by norm_num [firstResidualQ2Stage,UnequalParameters.mixedCost,prime])
     (by norm_num [firstResidualQ2Stage,UnequalParameters.mixedCost,prime])
     (by norm_num [firstResidualQ2Stage,UnequalParameters.mixedCost,prime])
     selected Delta (Finset.univ:Finset IRSProfile.Index) IRSProfile.domain
     u0 u1 IRSProfile.domain.injective.injOn
     (by norm_num [IRSProfile.Index,firstResidualQ2Stage])
     (by norm_num [firstResidualQ2Stage])
     (by norm_num [firstResidualQ2Stage,prime])
     (by norm_num [firstResidualQ2Stage])
     (by norm_num [firstResidualQ2Stage])
     (by simpa [firstResidualQ2Stage,firstResidualQ2] using hdegreeDelta)
     (by simpa [firstResidualQ2Stage,firstResidualQ2] using hagreementDelta)
     (by simpa [firstResidualQ2Stage,firstResidualQ2,
       UnequalParameters.errors,TightParameters.errors] using hnoPencilDelta))
 simpa [Delta,firstResidualQ2Ceiling,optimized_residual_cell_values.2.2.2.1]
   using hstage
theorem secondResidualCell_count_lt
   (QA QB QC:StackedPoly) (hQA:QA≠0) (hQB:QB≠0) (hQC:QC≠0)
   (hboxA:QA∈globalCoefficientBox IRSProfile.Field
     (25*agreements) w 5263 7)
   (hboxB:QB∈globalCoefficientBox IRSProfile.Field
     (47*agreements) w 598 14)
   (hboxC:QC∈globalCoefficientBox IRSProfile.Field
     (27*agreements) w 579299 6)
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field)
   (u0 u1:IRSProfile.Index → IRSProfile.Field)
   (hcover:∀ gamma∈Gamma,
     RecursiveSpecializationBranch (selected gamma) gamma QA QB QC)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
   (hagreement:∀ gamma∈Gamma,
     agreements ≤ ((Finset.univ:Finset IRSProfile.Index).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i)=
         u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma w errors):
   (secondResidualSeeds selected Gamma QA QB QC).card <
     secondResidualGcd12Ceiling:=by
 let Delta:=secondResidualSeeds selected Gamma QA QB QC
 let Q:=middleQuotient QA QB QC
 let T:=quotientC QA QB QC
 have hsub:Delta ⊆ Gamma:=by
   intro gamma hgamma
   exact (Finset.mem_filter.mp (Finset.mem_filter.mp hgamma).1).1
 have hsolutions:=secondResidualSeeds_quotient_vanish selected Gamma
   QA QB QC hcover
 have hQsolution:∀ gamma∈Delta,
     specialization IRSProfile.Field (selected gamma) gamma Q=0:=
   fun gamma hgamma => (hsolutions gamma hgamma).1
 have hTsolution:∀ gamma∈Delta,
     specialization IRSProfile.Field (selected gamma) gamma T=0:=
   fun gamma hgamma => (hsolutions gamma hgamma).2
 have hbox12:=gcd12_mem_meet_box QA QB hQA hQB hboxA hboxB
 have hQ:Q≠0:=middleQuotient_ne_zero QA QB QC hQA
 have hQbox:=middleQuotient_mem_parent_box QA QB QC hQA hbox12
 have hTbox:=quotientC_mem_parent_box QA QB QC hQC hboxC
 have hTcaps:=degree_bounds_of_mem_box T (27*agreements) w 579299 6
   (by norm_num [w]) hTbox
 have hrel:IsRelPrime Q T:=secondQuotients_isRelPrime hQA
 have hdegreeDelta:∀ gamma∈Delta,
     (selected gamma).natDegree ≤ secondResidualGcd12.w:=by
   intro gamma hgamma
   simpa [secondResidualGcd12,w] using hdegree gamma (hsub hgamma)
 have hagreementDelta:∀ gamma∈Delta,
     secondResidualGcd12.a ≤
       ((Finset.univ:Finset IRSProfile.Index).filter (fun i =>
         (selected gamma).eval (IRSProfile.domain i)=
           u0 i+gamma*u1 i)).card:=by
   intro gamma hgamma
   simpa [secondResidualGcd12,agreements] using hagreement gamma (hsub hgamma)
 have hnoPencilDelta:NoLargeSelectedPencil selected Delta
     secondResidualGcd12.w secondResidualGcd12.errors:=by
   simpa [secondResidualGcd12,TightParameters.errors,errors,n,agreements,w] using
     noLargeSelectedPencil_mono selected Gamma Delta w errors hsub hnoPencil
 have hstage:=asymmetric_stage_count_lt_of_regular_factors
   residualStageTwo secondResidualGcd12 Q T hQ prime
   (by norm_num [secondResidualGcd12])
   (by norm_num [secondResidualGcd12,prime])
   (by norm_num [secondResidualGcd12])
   (by norm_num [secondResidualGcd12,prime])
   (by norm_num [secondResidualGcd12,TightParameters.kappa])
   (by norm_num [secondResidualGcd12,TightParameters.algebraicCap,
     TightParameters.kappa])
   (by norm_num [secondResidualGcd12,prime,TightParameters.implicitYCap,
     TightParameters.kappa])
   (by norm_num [secondResidualGcd12,prime,TightParameters.algebraicCap,
     TightParameters.kappa])
   (by norm_num [secondResidualGcd12,prime,TightParameters.implicitYCap,
     TightParameters.algebraicCap,TightParameters.kappa])
   (by norm_num [secondResidualGcd12])
   (by norm_num [secondResidualGcd12])
   hQbox
   (by norm_num [residualStageTwo,UnequalParameters.gap])
   (by norm_num [residualStageTwo,secondResidualGcd12,
     UnequalParameters.gap,TightParameters.gap])
   (by norm_num [residualStageTwo,secondResidualGcd12])
   (by norm_num [residualStageTwo,secondResidualGcd12])
   (by norm_num [residualStageTwo,secondResidualGcd12])
   selected Delta (Finset.univ:Finset IRSProfile.Index) IRSProfile.domain
   u0 u1 IRSProfile.domain.injective.injOn
   (by norm_num [IRSProfile.Index,secondResidualGcd12])
   hdegreeDelta hQsolution hTsolution hagreementDelta hnoPencilDelta
   (all_regularPairSeeds_bound residualStageTwo Q T hQ hrel
     secondResidualGcd12.D secondResidualGcd12.w secondResidualGcd12.L
     secondResidualGcd12.s prime hQbox
     (by norm_num [secondResidualGcd12])
     (by norm_num [residualStageTwo,secondResidualGcd12])
     (by norm_num [residualStageTwo,secondResidualGcd12])
     (by norm_num [residualStageTwo,secondResidualGcd12])
     (by simpa [residualStageTwo,agreements,w] using hTcaps.1)
     (by simpa [residualStageTwo] using hTcaps.2.1)
     (by simpa [residualStageTwo] using hTcaps.2.2)
     (by norm_num [residualStageTwo])
     (by norm_num [residualStageTwo,prime])
     (by norm_num [residualStageTwo,prime])
     (by norm_num [residualStageTwo,prime])
     (by norm_num [residualStageTwo,UnequalParameters.mixedCost,prime])
     (by norm_num [residualStageTwo,UnequalParameters.mixedCost,prime])
     (by norm_num [residualStageTwo,UnequalParameters.mixedCost,prime])
     selected Delta (Finset.univ:Finset IRSProfile.Index) IRSProfile.domain
     u0 u1 IRSProfile.domain.injective.injOn
     (by norm_num [IRSProfile.Index,residualStageTwo])
     (by norm_num [residualStageTwo])
     (by norm_num [residualStageTwo,prime])
     (by norm_num [residualStageTwo])
     (by norm_num [residualStageTwo])
     (by simpa [residualStageTwo,secondResidualGcd12] using hdegreeDelta)
     (by simpa [residualStageTwo,secondResidualGcd12] using hagreementDelta)
     (by simpa [residualStageTwo,secondResidualGcd12,
       UnequalParameters.errors,TightParameters.errors] using hnoPencilDelta))
 simpa [Delta,secondResidualGcd12Ceiling,
   optimized_residual_cell_values.2.2.2.2] using hstage
end
end ProximityPrize.SubmissionLower.ContactStackedResidualCells6656Research
