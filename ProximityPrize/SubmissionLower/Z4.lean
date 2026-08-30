import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.AC
import ProximityPrize.SubmissionLower.F1
namespace ProximityPrize.SubmissionLower.ContactGlobalSelectedFamilies6600Research
open scoped Classical BigOperators
open ContactParameters6600Research
open ContactSelectedSeedDecomposition ContactImplicitContactLift
open ContactInterpolation ContactTranslation ContactFactorCaps
open ContactRegularFactorFlag6600Research
open ContactSingularBranch6600Research
open ContactNearPencil6600FactorLedgerResearch
open ContactPrimeSeedIncidence
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
def regularSeeds (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (F:ContactRegularFactorFlag6600Research.RegularIndex Q):Finset K:=
 Gamma.filter (fun gamma↦RegularSolution F.1 (selected gamma) gamma)
theorem regularSeeds_subset (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (F:ContactRegularFactorFlag6600Research.RegularIndex Q):
   regularSeeds Q selected Gamma F ⊆ Gamma:=
 Finset.filter_subset _ _
theorem card_le_regular_sum_add_singular
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) [CharP K prime]
   (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0):
   Gamma.card ≤
     (∑ F:ContactRegularFactorFlag6600Research.RegularIndex Q,
       (regularSeeds Q selected Gamma F).card)+
     (singularSeeds Q selected Gamma).card:=by
 classical
 let regularUnion:=Finset.univ.biUnion (regularSeeds Q selected Gamma)
 have hsub:Gamma ⊆ regularUnion ∪ singularSeeds Q selected Gamma:=by
   intro gamma hgamma
   obtain ⟨F,hF,hreg⟩ | ⟨q,hq,himp⟩ | hexc:=
     solution_three_way Q hQ weightedCap w seedTotalCap slopeCap prime
       (by norm_num [slopeCap]) characteristic_gates.2.2.2
       (by norm_num [w])
       (by norm_num [ContactParameters6600Research.w,
         ContactParameters6600Research.weightedCap,
         ContactParameters6600Research.multiplicity,
         ContactParameters6600Research.agreements,
         ContactParameters6600Research.n,
         ContactParameters6600Research.errors,
         ContactParameters6600Research.slopeCap])
       hbox (selected gamma) gamma (hsolution gamma hgamma)
   · apply Finset.mem_union.mpr
     left
     apply Finset.mem_biUnion.mpr
     exact ⟨⟨F,hF⟩,Finset.mem_univ _,
       Finset.mem_filter.mpr ⟨hgamma,hreg⟩⟩
   · apply Finset.mem_union.mpr
     right
     apply Finset.mem_union.mpr
     left
     apply Finset.mem_biUnion.mpr
     exact ⟨⟨q,hq⟩,Finset.mem_univ _,
       Finset.mem_filter.mpr ⟨hgamma,himp⟩⟩
   · apply Finset.mem_union.mpr
     right
     apply Finset.mem_union.mpr
     right
     exact Finset.mem_filter.mpr ⟨hgamma,hexc⟩
 calc
   Gamma.card ≤ (regularUnion ∪ singularSeeds Q selected Gamma).card:=
     Finset.card_le_card hsub
   _ ≤ regularUnion.card+(singularSeeds Q selected Gamma).card:=
     Finset.card_union_le _ _
   _ ≤ (∑ F:ContactRegularFactorFlag6600Research.RegularIndex Q,
         (regularSeeds Q selected Gamma F).card)+
       (singularSeeds Q selected Gamma).card:=
     Nat.add_le_add_right Finset.card_biUnion_le _
theorem regularSeeds_scaled_rectangular_bound
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hregular:∀ F:ContactRegularFactorFlag6600Research.RegularIndex Q,
     (regularSeeds Q selected Gamma F).card*gap^2 ≤
       factorRegularLedger (regularFlag Q F)):
   (∑ F:ContactRegularFactorFlag6600Research.RegularIndex Q,
     (regularSeeds Q selected Gamma F).card)*gap^2 ≤
       rectangularRegularNumerator:=by
 have hcaps:=regularFlag_budgets Q hQ hbox
 exact sum_factor_counts_rectangular_le
   (fun F:ContactRegularFactorFlag6600Research.RegularIndex Q↦
     (regularSeeds Q selected Gamma F).card)
   (regularFlag Q) hregular hcaps.1 hcaps.2.1 hcaps.2.2
theorem global_scaled_bound_of_regular_factors
   {Iota:Type} [DecidableEq Iota]
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) [CharP K prime]
   (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0)
   (hagreement:∀ gamma∈Gamma,
     agreements ≤ (nodes.filter (fun i↦
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma w errors)
   (hregular:∀ F:ContactRegularFactorFlag6600Research.RegularIndex Q,
     (regularSeeds Q selected Gamma F).card*gap^2 ≤
       factorRegularLedger (regularFlag Q F)):
   Gamma.card*gap^2 ≤ rectangularTotalNumerator:=by
 have hcover:=card_le_regular_sum_add_singular Q hQ hbox selected Gamma
   hsolution
 have hreg:=regularSeeds_scaled_rectangular_bound Q hQ hbox selected Gamma
   hregular
 have hsing:=singularSeeds_scaled_bound Q hQ hbox selected Gamma nodes
   x u0 u1 hinj hnodes hdegree hagreement hnoPencil
 calc
   Gamma.card*gap^2 ≤
       ((∑ F:ContactRegularFactorFlag6600Research.RegularIndex Q,
         (regularSeeds Q selected Gamma F).card)+
         (singularSeeds Q selected Gamma).card)*gap^2:=
     Nat.mul_le_mul_right (gap^2) hcover
   _=(∑ F:ContactRegularFactorFlag6600Research.RegularIndex Q,
         (regularSeeds Q selected Gamma F).card)*gap^2+
       (singularSeeds Q selected Gamma).card*gap^2:=by ring
   _ ≤ rectangularRegularNumerator+retainedSingularContribution:=
     Nat.add_le_add hreg hsing
   _=rectangularTotalNumerator:=rfl
theorem global_count_lt_alignment_of_regular_factors
   {Iota:Type} [DecidableEq Iota]
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) [CharP K prime]
   (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0)
   (hagreement:∀ gamma∈Gamma,
     agreements ≤ (nodes.filter (fun i↦
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma w errors)
   (hregular:∀ F:ContactRegularFactorFlag6600Research.RegularIndex Q,
     (regularSeeds Q selected Gamma F).card*gap^2 ≤
       factorRegularLedger (regularFlag Q F)):
   Gamma.card < alignmentBudget:=by
 have hscaled:=global_scaled_bound_of_regular_factors Q hQ hbox selected
   Gamma nodes x u0 u1 hinj hnodes hdegree hsolution hagreement hnoPencil
   hregular
 have hlt:Gamma.card*gap^2 < alignmentBudget*gap^2:=
   hscaled.trans_lt rectangular_strict_budget
 exact Nat.lt_of_mul_lt_mul_right hlt
end
end ProximityPrize.SubmissionLower.ContactGlobalSelectedFamilies6600Research
