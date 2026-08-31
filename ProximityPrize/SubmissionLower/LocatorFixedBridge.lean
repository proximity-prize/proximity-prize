import ProximityPrize.SubmissionLower.LocatorFixedConsumer
import ProximityPrize.SubmissionLower.LocatorSelectedCaps
import ProximityPrize.SubmissionLower.LocatorAuxiliarySelection
import ProximityPrize.SubmissionLower.LocatorQuotientReplacement
import ProximityPrize.SubmissionLower.LocatorCover
namespace ProximityPrize.SubmissionLower.LocatorFixedBridge
open ProximityPrize.Benchmark
open scoped Classical
open RCN180 RCN101 RCN234 RCN156 RCN275 RCN238 RCN243 RCN259 RCN319
open RCN266 RCN130 RCN140
open LocatorSelection LocatorFactorAggregate LocatorFactorReplacement
open LocatorReplacementGrid LocatorReplacementData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
theorem gcd_fixed_count_le
    (u0 u1:I → K) (S:SelectedPair u0 u1)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma∈Gamma,181776 ≤
      ((Finset.univ:Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80368):
    (LocatorCover.fixed
      (fun gamma => (specialization K (selected gamma) gamma).toRingHom)
      Gamma S.QA S.QB).card ≤
      272000000000000000+LocatorArithmetic.fixedSingular.countCap:=by
  classical
  let H:P4:=gcd12 S.QA S.QB
  let phi:K → P4 →+*Polynomial K:=
    fun gamma => (specialization K (selected gamma) gamma).toRingHom
  let Delta:Finset K:=LocatorCover.fixed phi Gamma S.QA S.QB
  have hH:H≠0:=gcd_ne_zero_of_left S.QA_ne
  have hHflagA:H∈RCN100.globalCoefficientBox K 9815904 131071 40000 16:=
    LocatorCaps.full_A_divisor_mem_box u0 u1 H hH S.common_divides_A
  have hHcaps:=(mem_flagGlobalCoefficientBox_iff H
    9815904 131071 40000 16 (by decide)).mp hHflagA
  have hT:wt residualTotalWeights H ≤ 2080:=S.common_total_le
  have hYS:wt residualYSWeights H ≤ 72:=S.common_ys_le
  have hS:wt residualSWeights H ≤ 16:=S.common_slope_le
  have hflag:H∈RCN100.globalCoefficientBox K 9815904 131071 2080 16:=
    (mem_flagGlobalCoefficientBox_iff H 9815904 131071 2080 16 (by decide)).mpr
      ⟨hT,hS,hHcaps.2.2⟩
  have hbox:=flag_box_to_ordinary K 9815904 131071 2080 16 H hflag
  have hsupport:ResidualSupportData LocatorFixedConsumer.wholeSupport H:=
    ⟨hS,hYS,hT⟩
  have hsub:Delta ⊆ Gamma:=by
    intro gamma hg
    have hm:gamma∈Gamma∧(phi gamma) (gcd12 S.QA S.QB)=0:=by
      simpa only [Delta,LocatorCover.fixed,Finset.mem_filter] using hg
    exact hm.1
  have hsolution:∀ gamma∈Delta,specialization K (selected gamma) gamma H=0:=by
    intro gamma hg
    exact LocatorCover.fixed_vanish phi Gamma S.QA S.QB gamma hg
  have hdegreeD:∀ gamma∈Delta,(selected gamma).natDegree ≤ 131071:=
    fun gamma hg => hdegree gamma (hsub hg)
  have hagreementD:∀ gamma∈Delta,181776 ≤
      ((Finset.univ:Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card:=
    fun gamma hg => hagreement gamma (hsub hg)
  have hnoD:NoLargeSelectedPencil selected Delta 131071 80368:=
    noLargeSelectedPencil_mono selected Gamma Delta 131071 80368 hsub hno
  let p:=regularCumulativeFlag H
  have hfcaps (F:RegularIndex H):
      (p F).all ≤ 16∧middle (p F) ≤ 72∧total (p F) ≤ 2080:=by
    have hf:=LocatorFixed.factor_support H hH hsupport F
    have hc:=originalCumulativeFlag_cumulative F.1
    refine ⟨?_,?_,?_⟩
    · simpa only [p,regularCumulativeFlag,hc.1,
        LocatorFixedConsumer.wholeSupport] using hf.s_weight
    · simpa only [p,regularCumulativeFlag,middle,hc.2.1,
        LocatorFixedConsumer.wholeSupport] using hf.ys_weight
    · simpa only [p,regularCumulativeFlag,total,hc.2.2,
        LocatorFixedConsumer.wholeSupport] using hf.total_weight
  have hfpos (F:RegularIndex H):1 ≤ (p F).all:=by
    have hne:(regularCumulativeFlag H F).all≠0:=
      Nat.ne_of_gt (regularCumulativeFlag_positive H F)
    simpa only [p] using Nat.one_le_iff_ne_zero.mpr hne
  let qCost:RegularIndex H → ℕ:=fun F =>
    chosenCost (cellOf (p F) (hfpos F) (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2)
  have hqCost (F:RegularIndex H)
      (hbad:Bad 2080 131072 131073 272000000000000000 (p F)):
      (regularSeeds H selected Delta F).card ≤ qCost F:=by
    dsimp only [qCost]
    have hf:=RCN167.positiveRFactors_spec H F.1 F.2
    have hdiv95:∀ v:RCN180.ConstraintKernel (K:=K)
        17268720 131071 2822 29 95 IRSProfile.domain u0 u1,
        F.1∣RCN100.reconstruct K 17268720 131071 2822 29 v.1:=by
      intro v
      exact hf.2.1.trans
        (LocatorAuxiliarySelection.common_divides_A95_small S 2822 (by decide) v)
    have hdiv72:∀ v:RCN180.ConstraintKernel (K:=K)
        13087872 131071 16540 21 72 IRSProfile.domain u0 u1,
        F.1∣RCN100.reconstruct K 13087872 131071 16540 21 v.1:=by
      intro v
      exact hf.2.1.trans
        (LocatorAuxiliarySelection.common_divides_A72_small S 16540 (by decide) v)
    have hown:=LocatorFixed.regular_factor_count 9815904
      LocatorFixedConsumer.wholeSupport (by decide) (by decide)
      (by decide) (by decide) (by decide)
      H hH hbox hsupport selected Delta u0 u1 hdegreeD hagreementD hnoD F
    exact LocatorQuotientReplacement.regularSeeds_count_le_chosen
      u0 u1 H selected Delta hdegreeD hagreementD hnoD F hf.1.ne_zero
      hdiv95 hdiv72
      (cellOf (p F) (hfpos F) (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2)
      (cellOf_bounds (p F) (hfpos F) (hfcaps F).1
        (hfcaps F).2.1 (hfcaps F).2.2)
      hbad hown
  have hcell (F:RegularIndex H)
      (hbad:Bad 2080 131072 131073 272000000000000000 (p F)):
      cellCost 2080 72 16 131072 131073 (p F) (qCost F) ≤
        272000000000000000:=by
    let c:=cellOf (p F) (hfpos F) (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    have hc:InCell (p F) c:=
      cellOf_bounds (p F) (hfpos F) (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    have hv:Valid c:=valid_of_inCell (p F) c hc
    have hnr:¬ RateFits c:=by
      intro hrate
      have hglobal:=LocatorRateCover.global_rate_of_endpoints
        (p F) 2080 (yhi c) (r c) 272000000000000000
        (by dsimp [c,r];omega) hc.all_eq hc.middle_le_yhi
        (by dsimp [c,yhi];omega) (hfcaps F).2.2 hrate.1 hrate.2
      exact (not_lt_of_ge hglobal) hbad
    exact cellCost_le_of_grid_bound (p F) c (qCost F) hc
      (by simpa only [qCost,c] using chosenCost_with_rest c hv hnr)
  exact LocatorFixedConsumer.fixed_count_le H hH hbox hsupport
    selected Delta u0 u1 hsolution hdegreeD hagreementD hnoD qCost hqCost hcell
end
end ProximityPrize.SubmissionLower.LocatorFixedBridge
