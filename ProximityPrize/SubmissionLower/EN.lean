import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.U
import ProximityPrize.SubmissionLower.Z4
import ProximityPrize.SubmissionLower.AK
namespace ProximityPrize.SubmissionLower.RCN141
open scoped Classical BigOperators
open RCN174 RCN319 RCN286
open RCN167 RCN169
open RCN290
open RCN238
open RCN266
open RCN140
open RCN291
open RCN294
open RCN318
open RCN276
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 35000
def prime6656:ℕ:=2130706433
def meetTightProfile:TightParameters where
 n:=meetProfile.n
 w:=meetProfile.w
 a:=meetProfile.agreements
 D:=meetProfile.weightedCap
 L:=meetProfile.seedTotalCap
 s:=meetProfile.slopeCap
theorem meet_tight_parameter_values:
   meetTightProfile.errors=meetProfile.errors∧
     meetTightProfile.gap=meetProfile.gap∧
     meetTightProfile.implicitYCap=meetProfile.implicitYCap∧
     meetTightProfile.algebraicCap=meetProfile.algebraicCap:=by
 norm_num [meetTightProfile,meetProfile,TightParameters.errors,
   TightParameters.gap,TightParameters.implicitYCap,
   TightParameters.algebraicCap,TightParameters.kappa,
   Profile.errors,Profile.gap,Profile.implicitYCap,
   Profile.implicitWeightedCap,Profile.algebraicCap]
theorem meet_characteristic_gates:
   meetProfile.slopeCap < prime6656∧
     meetProfile.algebraicCap < prime6656∧
     meetProfile.implicitWeightedCap < prime6656:=by
 norm_num [meetProfile,prime6656,Profile.algebraicCap,
   Profile.implicitWeightedCap]
variable {K Iota:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem meet_card_le_regular_sum_add_singular
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) [CharP K prime6656]
   (hbox:Q∈globalCoefficientBox K meetProfile.weightedCap meetProfile.w
     meetProfile.seedTotalCap meetProfile.slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0):
   Gamma.card ≤
     (∑ F:RegularIndex Q,(regularSeeds Q selected Gamma F).card)+
       (singularSeeds Q selected Gamma).card:=by
 classical
 have hdecomp:=selected_seed_decomposition Q hQ
   meetProfile.weightedCap meetProfile.w meetProfile.seedTotalCap
   meetProfile.slopeCap prime6656
   (by norm_num [meetProfile])
   meet_characteristic_gates.1
   (by norm_num [meetProfile])
   (by norm_num [meetProfile])
   (by norm_num [meetProfile,Profile.algebraicCap])
   meet_characteristic_gates.2.1 hbox Gamma selected hsolution
 let regularUnion:=Finset.univ.biUnion (regularSeeds Q selected Gamma)
 have hsub:Gamma ⊆ regularUnion ∪ singularSeeds Q selected Gamma:=by
   intro gamma hgamma
   by_cases hexc:gamma∈
       exceptionalSeeds (singularAuxiliary Q) Gamma selected
   · apply Finset.mem_union.mpr
     right
     apply Finset.mem_union.mpr
     right
     exact hexc
   · obtain ⟨F,hF,hreg⟩ | ⟨q,hq,himp⟩:=
       hdecomp.2.1 gamma hgamma hexc
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
 calc
   Gamma.card ≤ (regularUnion ∪ singularSeeds Q selected Gamma).card:=
     Finset.card_le_card hsub
   _ ≤ regularUnion.card+(singularSeeds Q selected Gamma).card:=
     Finset.card_union_le _ _
   _ ≤ (∑ F:RegularIndex Q,(regularSeeds Q selected Gamma F).card)+
       (singularSeeds Q selected Gamma).card:=
     Nat.add_le_add_right Finset.card_biUnion_le _
def meetImplicitCost (Q:MvPolynomial (Fin 4) K)
   (q:ImplicitIndex Q):RCN223.DegreeVector:=
 ⟨pairYCost q.1,pairRCost q.1,pairZCost q.1⟩
theorem meet_singularSeeds_scaled_bound_of_implicit_pairs
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) [CharP K prime6656]
   (hbox:Q∈globalCoefficientBox K meetProfile.weightedCap meetProfile.w
     meetProfile.seedTotalCap meetProfile.slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0)
   (hpair:∀ q:ImplicitIndex Q,
     (implicitSeeds Q selected Gamma q).card*meetProfile.gap ≤
       (meetProfile.n-meetProfile.w)*
           dot meetTightProfile.agreement (meetImplicitCost Q q)+
         (meetProfile.errors+1)*meetProfile.gap*
           (meetImplicitCost Q q).z):
   (singularSeeds Q selected Gamma).card*meetProfile.gap^2 ≤
     meetProfile.retainedSingularContribution:=by
 classical
 have hdecomp:=selected_seed_decomposition Q hQ
   meetProfile.weightedCap meetProfile.w meetProfile.seedTotalCap
   meetProfile.slopeCap prime6656
   (by norm_num [meetProfile])
   meet_characteristic_gates.1
   (by norm_num [meetProfile])
   (by norm_num [meetProfile])
   (by norm_num [meetProfile,Profile.algebraicCap])
   meet_characteristic_gates.2.1 hbox Gamma selected hsolution
 have hy:(∑ q:ImplicitIndex Q,(meetImplicitCost Q q).y) ≤
     meetTightProfile.algebraicCap:=by
   simpa only [meetImplicitCost,Finset.sum_coe_sort,
     meet_tight_parameter_values.2.2.2,Profile.algebraicCap] using
       hdecomp.2.2.2.1
 have hr:(∑ q:ImplicitIndex Q,(meetImplicitCost Q q).r) ≤
     2*meetTightProfile.implicitYCap*meetTightProfile.algebraicCap:=by
   simpa only [meetImplicitCost,Finset.sum_coe_sort,
     meet_tight_parameter_values.2.2.1,
     meet_tight_parameter_values.2.2.2,Profile.implicitYCap,
     Profile.implicitWeightedCap,Profile.algebraicCap] using
       hdecomp.2.2.2.2.1
 have hz:(∑ q:ImplicitIndex Q,(meetImplicitCost Q q).z) ≤
     meetTightProfile.implicitYCap:=by
   simpa only [meetImplicitCost,Finset.sum_coe_sort,
     meet_tight_parameter_values.2.2.1,Profile.implicitYCap,
     Profile.implicitWeightedCap] using hdecomp.2.2.2.2.2
 have hexc:
     (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card ≤
       2*meetTightProfile.algebraicCap^2:=by
   simpa only [meet_tight_parameter_values.2.2.2,
     Profile.algebraicCap] using hdecomp.1
 have hpair':∀ q:ImplicitIndex Q,
     (implicitSeeds Q selected Gamma q).card*meetTightProfile.gap ≤
       (meetTightProfile.n-meetTightProfile.w)*
           dot meetTightProfile.agreement (meetImplicitCost Q q)+
         (meetTightProfile.errors+1)*meetTightProfile.gap*
           (meetImplicitCost Q q).z:=by
   intro q
   simpa only [meetTightProfile,TightParameters.errors,
     TightParameters.gap,Profile.errors,Profile.gap] using hpair q
 have hsum:=meetTightProfile.with_exceptions_bound
   (fun q:ImplicitIndex Q↦(implicitSeeds Q selected Gamma q).card)
   (meetImplicitCost Q)
   (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card
   hy hr hz hpair' hexc
 have hunion:=singularSeeds_card_le_sum Q selected Gamma
 have hgap:meetTightProfile.gap=meetProfile.gap:=
   meet_tight_parameter_values.2.1
 have htight:meetTightProfile.tightNumerator*meetProfile.gap ≤
     meetProfile.retainedSingularContribution:=by
   norm_num [meetTightProfile,meetProfile,TightParameters.tightNumerator,
     TightParameters.coreNumerator,TightParameters.aggregateCost,
     TightParameters.agreement,TightParameters.implicitYCap,
     TightParameters.algebraicCap,TightParameters.kappa,
     TightParameters.errors,TightParameters.gap,Profile.errors,
     Profile.gap,Profile.retainedSingularContribution,Profile.mixed,
     Profile.liftedSurface,Profile.implicitCut,Profile.liftedLast,
     Profile.liftedAgreement,Profile.unitZ,Profile.algebraicCap,
     Profile.implicitWeightedCap,Profile.implicitYCap,dot]
 calc
   (singularSeeds Q selected Gamma).card*meetProfile.gap^2 ≤
       (((∑ q:ImplicitIndex Q,
         (implicitSeeds Q selected Gamma q).card)+
         (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card)*
           meetProfile.gap)*meetProfile.gap:=by
     calc
       _ ≤ ((∑ q:ImplicitIndex Q,
             (implicitSeeds Q selected Gamma q).card)+
             (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card)*
             meetProfile.gap^2:=
         Nat.mul_le_mul_right _ hunion
       _=(((∑ q:ImplicitIndex Q,
             (implicitSeeds Q selected Gamma q).card)+
             (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card)*
               meetProfile.gap)*meetProfile.gap:=by ring
   _ ≤ meetTightProfile.tightNumerator*meetProfile.gap:=by
     rw [←hgap]
     exact Nat.mul_le_mul_right meetTightProfile.gap hsum
   _ ≤ meetProfile.retainedSingularContribution:=htight
theorem meet_global_count_lt_fixed_cost_of_local_counts
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) [CharP K prime6656]
   (hbox:Q∈globalCoefficientBox K meetProfile.weightedCap meetProfile.w
     meetProfile.seedTotalCap meetProfile.slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0)
   (hregular:∀ F:RegularIndex Q,
     (regularSeeds Q selected Gamma F).card*meetProfile.gap^2 ≤
       meetProfile.factorRegularLedger (regularFlag Q F))
   (hpair:∀ q:ImplicitIndex Q,
     (implicitSeeds Q selected Gamma q).card*meetProfile.gap ≤
       (meetProfile.n-meetProfile.w)*
           dot meetTightProfile.agreement (meetImplicitCost Q q)+
         (meetProfile.errors+1)*meetProfile.gap*
           (meetImplicitCost Q q).z):
   Gamma.card < 95756912943422943:=by
 have hcover:=meet_card_le_regular_sum_add_singular Q hQ hbox selected
   Gamma hsolution
 have hreg:=sum_factor_counts_rectangular_le meetProfile Q hQ
   (by norm_num [meetProfile]) hbox
   (fun F:RegularIndex Q↦(regularSeeds Q selected Gamma F).card)
   hregular
 have hsing:=meet_singularSeeds_scaled_bound_of_implicit_pairs Q hQ hbox
   selected Gamma hsolution hpair
 have hscaled:Gamma.card*meetProfile.gap^2 ≤
     meetProfile.totalNumerator:=by
   calc
     Gamma.card*meetProfile.gap^2 ≤
         ((∑ F:RegularIndex Q,
           (regularSeeds Q selected Gamma F).card)+
           (singularSeeds Q selected Gamma).card)*meetProfile.gap^2:=
       Nat.mul_le_mul_right _ hcover
     _=(∑ F:RegularIndex Q,
           (regularSeeds Q selected Gamma F).card)*meetProfile.gap^2+
         (singularSeeds Q selected Gamma).card*meetProfile.gap^2:=by ring
     _ ≤ meetProfile.regularNumerator+
         meetProfile.retainedSingularContribution:=Nat.add_le_add hreg hsing
     _=meetProfile.totalNumerator:=rfl
 have hstrict:meetProfile.totalNumerator <
     95756912943422943*meetProfile.gap^2:=by
   rw [meet_total_numerator_exact]
   norm_num [meetProfile,Profile.gap]
 exact Nat.lt_of_mul_lt_mul_right (hscaled.trans_lt hstrict)
end
end ProximityPrize.SubmissionLower.RCN141
