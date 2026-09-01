import ProximityPrize.SubmissionLower.LocatorFixedConsumer
import ProximityPrize.SubmissionLower.LocatorSelectedCaps
import ProximityPrize.SubmissionLower.LocatorAuxiliarySelection
import ProximityPrize.SubmissionLower.LocatorQuotientReplacement
import ProximityPrize.SubmissionLower.LocatorCover
namespace ProximityPrize.SubmissionLower.LocatorFixedBridge
open ProximityPrize.Benchmark
open scoped Classical
open RCN095 RCN180 RCN101 RCN234 RCN156 RCN275 RCN238 RCN243 RCN259 RCN319 RCN266 RCN130 RCN140 LocatorSelection LocatorFactorAggregate LocatorFactorReplacement LocatorReplacementGrid LocatorReplacementData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
private abbrev regularBound:ℕ:=271696879461797498
theorem gcd_fixed_count_le
    (u0 u1:I → K) (S:SelectedPair u0 u1)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181717 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80427) :
    (LocatorCover.fixed
      (fun gamma=> (specialization K (selected gamma) gamma).toRingHom)
      Gamma S.QA S.QB).card ≤
      regularBound + LocatorArithmetic.fixedSingular.countCap:=by
  classical
  let H:P4:=gcd12 S.QA S.QB
  let phi:K → P4 →+* Polynomial K:=
    fun gamma=> (specialization K (selected gamma) gamma).toRingHom
  let Delta:Finset K:=LocatorCover.fixed phi Gamma S.QA S.QB
  have hH:H ≠ 0:=gcd_ne_zero_of_left S.QA_ne
  have hHflagA:H ∈ RCN100.globalCoefficientBox K 10539586 131071 52091 17:=
    LocatorCaps.full_A_divisor_mem_box u0 u1 H hH S.common_divides_A
  have hHcapsA:=(mem_flagGlobalCoefficientBox_iff H
    10539586 131071 52091 17 (by decide)).mp hHflagA
  have hT:wt residualTotalWeights H ≤ 2450:=S.common_total_le
  have hYS:wt residualYSWeights H ≤ 77:=S.common_ys_le
  have hS:wt residualSWeights H ≤ 17:=hHcapsA.2.1
  have hflag:H ∈ RCN100.globalCoefficientBox K 10539586 131071 2450 17:=
    (mem_flagGlobalCoefficientBox_iff H 10539586 131071 2450 17 (by decide)).mpr
      ⟨hT,hS,hHcapsA.2.2⟩
  have hbox:=flag_box_to_ordinary K 10539586 131071 2450 17 H hflag
  have hsupport:ResidualSupportData LocatorFixedConsumer.wholeSupport H:=
    ⟨hS,hYS,hT⟩
  have hsub:Delta ⊆ Gamma:=by
    intro gamma hg
    have hm:gamma ∈ Gamma ∧ (phi gamma) (gcd12 S.QA S.QB) =0:=by
      simpa only [Delta,LocatorCover.fixed,Finset.mem_filter] using hg
    exact hm.1
  have hsolution:∀ gamma ∈ Delta,specialization K (selected gamma) gamma H=0:=by
    intro gamma hg
    exact LocatorCover.fixed_vanish phi Gamma S.QA S.QB gamma hg
  have hdegreeD:∀ gamma ∈ Delta, (selected gamma).natDegree ≤ 131071:=
    fun gamma hg=> hdegree gamma (hsub hg)
  have hagreementD:∀ gamma ∈ Delta,181717 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card:=
    fun gamma hg=> hagreement gamma (hsub hg)
  have hnoD:NoLargeSelectedPencil selected Delta 131071 80427:=
    noLargeSelectedPencil_mono selected Gamma Delta 131071 80427 hsub hno
  let p:=regularCumulativeFlag H
  have hfcaps (F:RegularIndex H) :
      (p F).all ≤ 17 ∧ middle (p F) ≤ 77 ∧ total (p F) ≤ 2450:=by
    have hf:=LocatorFixed.factor_support H hH hsupport F
    have hc:=originalCumulativeFlag_cumulative F.1
    refine ⟨?_, ?_, ?_⟩
    · simpa only [p,regularCumulativeFlag,hc.1,
        LocatorFixedConsumer.wholeSupport] using hf.s_weight
    · simpa only [p,regularCumulativeFlag,middle,hc.2.1,
        LocatorFixedConsumer.wholeSupport] using hf.ys_weight
    · simpa only [p,regularCumulativeFlag,total,hc.2.2,
        LocatorFixedConsumer.wholeSupport] using hf.total_weight
  have hfpos (F:RegularIndex H):1 ≤ (p F).all:=by
    have hne:(regularCumulativeFlag H F).all ≠ 0:=
      Nat.ne_of_gt (regularCumulativeFlag_positive H F)
    simpa only [p] using Nat.one_le_iff_ne_zero.mpr hne
  let qCost:RegularIndex H → ℕ:=fun F=>
    let c:=cellOf (p F) (hfpos F) (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    chosenCost c
  have hqCost (F:RegularIndex H)
      (hbad:Bad 2450 131072 131073 regularBound (p F)) :
      (regularSeeds H selected Delta F).card ≤ qCost F:=by
    let c:=cellOf (p F) (hfpos F) (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    have hc:InCell (p F) c:=
      cellOf_bounds (p F) (hfpos F) (hfcaps F).1
        (hfcaps F).2.1 (hfcaps F).2.2
    have hown:=LocatorFixed.regular_factor_count 10539586
      LocatorFixedConsumer.wholeSupport (by decide) (by decide)
      (by decide) (by decide) (by decide)
      H hH hbox hsupport selected Delta u0 u1 hdegreeD hagreementD hnoD F
    have hf:=RCN167.positiveRFactors_spec H F.1 F.2
    have hdiv72 (L:ℕ) (hL:L ≤ 52091) : ∀ v:RCN180.ConstraintKernel (K:=K)
        13083624 131071 L 21 72 IRSProfile.domain u0 u1,
        F.1 ∣ RCN100.reconstruct K 13083624 131071 L 21 v.1:=by
      intro v
      exact hf.2.1.trans
        (LocatorAuxiliarySelection.common_divides_A72_small S L hL v)
    have hdiv126 (L:ℕ) (hL:L ≤ 52091) : ∀ v:RCN180.ConstraintKernel (K:=K)
        22896342 131071 L 39 126 IRSProfile.domain u0 u1,
        F.1 ∣ RCN100.reconstruct K 22896342 131071 L 39 v.1:=by
      intro v
      exact hf.2.1.trans
        (LocatorAuxiliarySelection.common_divides_A126_small S L hL v)
    have h:=LocatorQuotientReplacement.regularSeeds_count_le_chosen
      u0 u1 H selected Delta hdegreeD hagreementD hnoD F hf.1.ne_zero
      hdiv72 hdiv126 c hc hbad hown
    simpa only [qCost,c] using h
  have hcell (F:RegularIndex H)
      (hbad:Bad 2450 131072 131073 regularBound (p F)) :
      cellCost 2450 77 17 131072 131073 (p F) (qCost F) ≤
        regularBound:=by
    let c:=cellOf (p F) (hfpos F) (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    have hc:InCell (p F) c:=
      cellOf_bounds (p F) (hfpos F) (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    have hv:Valid c:=valid_of_inCell (p F) c hc
    have hnr:¬ RateFits c:=by
      intro hrate
      have hrpos:1 ≤ r c:=by
        simpa only [hc.all_eq] using hfpos F
      have hglobal:=LocatorRateCover.global_rate_of_endpoints
        (p F) 2450 (yhi c) (r c) regularBound
        hrpos hc.all_eq hc.middle_le_yhi
        ((yhi_le_77 c).trans (by decide))
        (hc.total_le_thi.trans (thi_le_2450 c)) hrate.1 hrate.2
      exact (not_lt_of_ge hglobal) hbad
    exact cellCost_le_of_grid_bound (p F) c (qCost F) hc
      (by simpa only [qCost,c] using chosenCost_with_rest c hv hnr)
  exact LocatorFixedConsumer.fixed_count_le H hH hbox hsupport
    selected Delta u0 u1 hsolution hdegreeD hagreementD hnoD qCost hqCost hcell
end
end ProximityPrize.SubmissionLower.LocatorFixedBridge
