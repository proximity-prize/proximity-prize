import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.EN
import ProximityPrize.SubmissionLower.AG
namespace ProximityPrize.SubmissionLower.RCN092
open scoped Classical BigOperators
open RCN174 RCN319 RCN238
open RCN266
open RCN140
open RCN291
open RCN294
open RCN318
open RCN276
open RCN141
open RCN292
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 35000
variable {K Iota:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem meet_tight_scaled_le_retained:
   meetTightProfile.tightNumerator*meetProfile.gap ≤
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
theorem meet_singularSeeds_tight_gap_bound
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   [CharP K prime6656]
   (hbox:Q∈globalCoefficientBox K meetProfile.weightedCap meetProfile.w
     meetProfile.seedTotalCap meetProfile.slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=meetProfile.n)
   (hdegree:∀ gamma∈Gamma,
     (selected gamma).natDegree ≤ meetProfile.w)
   (hagreement:∀ gamma∈Gamma,
     meetProfile.agreements ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma meetProfile.w
     meetProfile.errors):
   (singularSeeds Q selected Gamma).card*meetTightProfile.gap ≤
     meetTightProfile.tightNumerator:=by
 exact
   RCN292.TightParameters.singularSeeds_tight_gap_bound
     meetTightProfile Q hQ hbox
     (by norm_num [meetTightProfile,meetProfile])
     (by norm_num [meetTightProfile,meetProfile,prime6656])
     (by norm_num [meetTightProfile,meetProfile])
     (by norm_num [meetTightProfile,meetProfile,prime6656])
     (by norm_num [meetTightProfile,meetProfile,TightParameters.kappa])
     (by norm_num [meetTightProfile,meetProfile,
       TightParameters.algebraicCap,TightParameters.kappa])
     (by norm_num [meetTightProfile,meetProfile,prime6656,
       TightParameters.implicitYCap,TightParameters.kappa])
     (by norm_num [meetTightProfile,meetProfile,prime6656,
       TightParameters.algebraicCap,TightParameters.kappa])
     (by norm_num [meetTightProfile,meetProfile,prime6656,
       TightParameters.implicitYCap,TightParameters.algebraicCap,
       TightParameters.kappa])
     (by norm_num [meetTightProfile,meetProfile])
     (by norm_num [meetTightProfile,meetProfile])
     selected Gamma nodes x u0 u1 hinj
     (by simpa [meetTightProfile] using hnodes)
     (by simpa [meetTightProfile] using hdegree)
     (by simpa [meetTightProfile] using hagreement)
     (by simpa [meetTightProfile,TightParameters.errors,
       Profile.errors] using hnoPencil)
theorem meet_singularSeeds_scaled_bound
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   [CharP K prime6656]
   (hbox:Q∈globalCoefficientBox K meetProfile.weightedCap meetProfile.w
     meetProfile.seedTotalCap meetProfile.slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=meetProfile.n)
   (hdegree:∀ gamma∈Gamma,
     (selected gamma).natDegree ≤ meetProfile.w)
   (hagreement:∀ gamma∈Gamma,
     meetProfile.agreements ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma meetProfile.w
     meetProfile.errors):
   (singularSeeds Q selected Gamma).card*meetProfile.gap^2 ≤
     meetProfile.retainedSingularContribution:=by
 have hbase:=meet_singularSeeds_tight_gap_bound Q hQ hbox selected Gamma
   nodes x u0 u1 hinj hnodes hdegree hagreement hnoPencil
 have hgap:meetTightProfile.gap=meetProfile.gap:=
   meet_tight_parameter_values.2.1
 have hscaled:
     (singularSeeds Q selected Gamma).card*meetProfile.gap^2 ≤
       meetTightProfile.tightNumerator*meetProfile.gap:=by
   rw [←hgap]
   calc
     (singularSeeds Q selected Gamma).card*meetTightProfile.gap^2=
         ((singularSeeds Q selected Gamma).card*meetTightProfile.gap)*
           meetTightProfile.gap:=by ring
     _ ≤ meetTightProfile.tightNumerator*meetTightProfile.gap:=
       Nat.mul_le_mul_right meetTightProfile.gap hbase
 exact hscaled.trans meet_tight_scaled_le_retained
theorem meet_global_count_lt_fixedCost_of_regular_factors
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   [CharP K prime6656]
   (hbox:Q∈globalCoefficientBox K meetProfile.weightedCap meetProfile.w
     meetProfile.seedTotalCap meetProfile.slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=meetProfile.n)
   (hdegree:∀ gamma∈Gamma,
     (selected gamma).natDegree ≤ meetProfile.w)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0)
   (hagreement:∀ gamma∈Gamma,
     meetProfile.agreements ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma meetProfile.w
     meetProfile.errors)
   (hregular:∀ F:RegularIndex Q,
     (regularSeeds Q selected Gamma F).card*meetProfile.gap^2 ≤
       meetProfile.factorRegularLedger (regularFlag Q F)):
   Gamma.card < meetProfile.fixedCost:=by
 have hcover:=meet_card_le_regular_sum_add_singular Q hQ hbox selected
   Gamma hsolution
 have hreg:=sum_factor_counts_rectangular_le meetProfile Q hQ
   (by norm_num [meetProfile]) hbox
   (fun F:RegularIndex Q => (regularSeeds Q selected Gamma F).card)
   hregular
 have hsing:=meet_singularSeeds_scaled_bound Q hQ hbox selected Gamma
   nodes x u0 u1 hinj hnodes hdegree hagreement hnoPencil
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
     meetProfile.fixedCost*meetProfile.gap^2:=by
   rw [meet_total_numerator_exact,meet_fixed_cost_exact]
   norm_num [meetProfile,Profile.gap]
 exact Nat.lt_of_mul_lt_mul_right (hscaled.trans_lt hstrict)
end
end ProximityPrize.SubmissionLower.RCN092
