import ProximityPrize.SubmissionLower.LocatorFixedConsumer
import ProximityPrize.SubmissionLower.LocatorSelectedCaps
import ProximityPrize.SubmissionLower.LocatorAuxiliarySelection
import ProximityPrize.SubmissionLower.LocatorQuotientReplacement
import ProximityPrize.SubmissionLower.LocatorHybridQuarticReplacement
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptAll6765
import ProximityPrize.SubmissionLower.LocatorCover
namespace ProximityPrize.SubmissionLower.LocatorFixedBridge
open ProximityPrize.Benchmark
open scoped Classical
open RCN081 RCN095 RCN180 RCN101 RCN234 RCN156 RCN275 RCN238 RCN243 RCN259
open RCN319 RCN266 RCN130 RCN140
open LocatorSelection LocatorFactorAggregate LocatorFactorReplacement
open LocatorReplacementGrid LocatorReplacementData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
private abbrev regularBound:ℕ:=271800583557655343

theorem gcd_fixed_count_le
    (u0 u1:I→K) (S:SelectedPair u0 u1)
    (selected:K→Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement:∀ gamma∈Gamma,181707≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80437):
    (LocatorCover.fixed
      (fun gamma=>(specialization K (selected gamma) gamma).toRingHom)
      Gamma S.QA S.QB).card≤
      regularBound+LocatorArithmetic.fixedSingular.countCap:=by
  classical
  let H:P4:=gcd12 S.QA S.QB
  let phi:K→P4→+*Polynomial K:=
    fun gamma=>(specialization K (selected gamma) gamma).toRingHom
  let Delta:Finset K:=LocatorCover.fixed phi Gamma S.QA S.QB
  have hH:H≠0:=gcd_ne_zero_of_left S.QA_ne
  have hHflagA:H∈RCN100.globalCoefficientBox K 10539006 131071 52091 17:=
    LocatorCaps.full_A_divisor_mem_box u0 u1 H hH S.common_divides_A
  have hHcaps:=(mem_flagGlobalCoefficientBox_iff H
    10539006 131071 52091 17 (by decide)).mp hHflagA
  have hT:wt residualTotalWeights H≤2556:=S.common_total_le
  have hYS:wt residualYSWeights H≤78:=S.common_ys_le
  have hS:wt residualSWeights H≤17:=S.common_slope_le
  have hflag:H∈RCN100.globalCoefficientBox K 10539006 131071 2556 17:=
    (mem_flagGlobalCoefficientBox_iff H 10539006 131071 2556 17 (by decide)).mpr
      ⟨hT,hS,hHcaps.2.2⟩
  have hbox:=flag_box_to_ordinary K 10539006 131071 2556 17 H hflag
  have hsupport:ResidualSupportData LocatorFixedConsumer.wholeSupport H:=
    ⟨hS,hYS,hT⟩
  have hsub:Delta⊆Gamma:=by
    intro gamma hg
    exact (by
      simpa only [Delta,LocatorCover.fixed,Finset.mem_filter] using hg:
        gamma∈Gamma∧phi gamma (gcd12 S.QA S.QB)=0).1
  have hsolution:∀ gamma∈Delta,specialization K (selected gamma) gamma H=0:=
    fun gamma hg=>LocatorCover.fixed_vanish phi Gamma S.QA S.QB gamma hg
  have hdegreeD:∀ gamma∈Delta,(selected gamma).natDegree≤131071:=
    fun gamma hg=>hdegree gamma (hsub hg)
  have hagreementD:∀ gamma∈Delta,181707≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card:=
    fun gamma hg=>hagreement gamma (hsub hg)
  have hnoD:NoLargeSelectedPencil selected Delta 131071 80437:=
    noLargeSelectedPencil_mono selected Gamma Delta 131071 80437 hsub hno
  let p:=regularCumulativeFlag H
  have hfcaps (F:RegularIndex H):
      (p F).all≤17∧middle (p F)≤78∧total (p F)≤2556:=by
    have hf:=LocatorFixed.factor_support H hH hsupport F
    have hc:=originalCumulativeFlag_cumulative F.1
    exact ⟨by simpa only [p,regularCumulativeFlag,hc.1,
        LocatorFixedConsumer.wholeSupport] using hf.s_weight,
      by simpa only [p,regularCumulativeFlag,middle,hc.2.1,
        LocatorFixedConsumer.wholeSupport] using hf.ys_weight,
      by simpa only [p,regularCumulativeFlag,total,hc.2.2,
        LocatorFixedConsumer.wholeSupport] using hf.total_weight⟩
  have hfpos (F:RegularIndex H):1≤(p F).all:=by
    have hp:=regularCumulativeFlag_positive H F
    change 1≤(regularCumulativeFlag H F).all
    omega
  let qCost:RegularIndex H→ℕ:=fun F=>
    chosenCost (cellOf (p F) (hfpos F) (hfcaps F).1
      (hfcaps F).2.1 (hfcaps F).2.2)
  have hqCost (F:RegularIndex H)
      (hbad:Bad 2556 131072 131073 regularBound (p F)):
      (regularSeeds H selected Delta F).card≤qCost F:=by
    let c:=cellOf (p F) (hfpos F) (hfcaps F).1
      (hfcaps F).2.1 (hfcaps F).2.2
    have hc:InCell (p F) c:=cellOf_bounds (p F) (hfpos F)
      (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    have hv:Valid c:=cellOf_valid (p F) (hfpos F)
      (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    have hnone:¬noBadFits c:=by
      intro hn
      have hmono:=paddedCost_mono 131072 131073 (below_cell_cap (p F) c hc)
      have hscaled:=Nat.mul_le_mul_left 2556 hmono
      have hright:=Nat.mul_le_mul_left regularBound hc.tlo_le
      have hle:2556*paddedCost 131072 131073 (p F)≤
          regularBound*total (p F):=(hscaled.trans hn).trans hright
      exact (Nat.not_lt_of_ge hle) hbad
    have routes:ordinaryFits c∨sourceFits c∨sourceFits126 c∨hybridFits c:=
      (receipt c hv).resolve_left hnone
    by_cases ho:ordinaryFits c
    · have hown:=LocatorFixed.regular_factor_count 10539006
        LocatorFixedConsumer.wholeSupport (by decide) (by decide)
        (by decide) (by decide) (by decide)
        H hH hbox hsupport selected Delta u0 u1 hdegreeD hagreementD hnoD F
      have hle:=hown.trans
        (paddedCost_mono 131072 131073 (below_cell_cap (p F) c hc))
      simpa only [qCost,c,chosenCost,if_pos ho] using hle
    · have hf:=RCN167.positiveRFactors_spec H F.1 F.2
      have hHcontact:wt (contactWeights 131071) H<10539006:=by omega
      have hcontact:wt (contactWeights 131071) F.1<10539006:=
        (weightedTotalDegree_le_of_dvd (contactWeights 131071)
          F.1 H hf.2.1 hH).trans_lt hHcontact
      have hsources:=routes.resolve_left ho
      by_cases h93:sourceFits c
      · have hdiv93:∀ L,L≤52091→∀ v:RCN180.ConstraintKernel (K:=K)
            16898751 131071 L 27 93 IRSProfile.domain u0 u1,
            F.1∣RCN100.reconstruct K 16898751 131071 L 27 v.1:=by
          intro L hL v
          exact hf.2.1.trans
            (LocatorAuxiliarySelection.common_divides_A93_small S L hL v)
        have hs:=LocatorQuotientReplacement.regularSeeds_count_le_source93
          u0 u1 H selected Delta hdegreeD hagreementD hnoD F hf.1.ne_zero
          hdiv93 hcontact c hc h93
        simpa only [qCost,c,chosenCost,if_neg ho,if_pos h93] using hs
      · have htail:=hsources.resolve_left h93
        have hdiv126:∀ L,L≤52091→∀ v:RCN180.ConstraintKernel (K:=K)
            22895082 131071 L 39 126 IRSProfile.domain u0 u1,
            F.1∣RCN100.reconstruct K 22895082 131071 L 39 v.1:=by
          intro L hL v
          exact hf.2.1.trans
            (LocatorAuxiliarySelection.common_divides_A126_small S L hL v)
        by_cases h126:sourceFits126 c
        · have hs:=LocatorQuotientReplacement.regularSeeds_count_le_source126
            u0 u1 H selected Delta hdegreeD hagreementD hnoD F hf.1.ne_zero
            hdiv126 hcontact c hc h126
          simpa only [qCost,c,chosenCost,if_neg ho,if_neg h93,if_pos h126] using hs
        · have hhybrid:hybridFits c:=htail.resolve_left h126
          have hs:=LocatorHybridQuarticReplacement.regularSeeds_count_le_hybrid126
            u0 u1 H selected Delta hdegreeD hagreementD hnoD F hf.1.ne_zero
            hdiv126 c hc hhybrid
          simpa only [qCost,c,chosenCost,if_neg ho,if_neg h93,if_neg h126] using hs
  have hcell (F:RegularIndex H)
      (hbad:Bad 2556 131072 131073 regularBound (p F)):
      cellCost 2556 78 17 131072 131073 (p F) (qCost F)≤regularBound:=by
    let c:=cellOf (p F) (hfpos F) (hfcaps F).1
      (hfcaps F).2.1 (hfcaps F).2.2
    have hc:InCell (p F) c:=cellOf_bounds (p F) (hfpos F)
      (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    have hv:Valid c:=cellOf_valid (p F) (hfpos F)
      (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    have hnone:¬noBadFits c:=by
      intro hn
      have hmono:=paddedCost_mono 131072 131073 (below_cell_cap (p F) c hc)
      have hscaled:=Nat.mul_le_mul_left 2556 hmono
      have hright:=Nat.mul_le_mul_left regularBound hc.tlo_le
      exact (Nat.not_lt_of_ge ((hscaled.trans hn).trans hright)) hbad
    exact cellCost_le_of_cell_bound (p F) c (qCost F) hc
      (by simpa only [qCost,c,exactRest] using chosenCost_with_rest c hv hnone)
  exact LocatorFixedConsumer.fixed_count_le H hH hbox hsupport
    selected Delta u0 u1 hsolution hdegreeD hagreementD hnoD qCost hqCost hcell
end
end ProximityPrize.SubmissionLower.LocatorFixedBridge
