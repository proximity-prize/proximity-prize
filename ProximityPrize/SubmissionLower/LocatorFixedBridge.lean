import ProximityPrize.SubmissionLower.LocatorFixedConsumer
import ProximityPrize.SubmissionLower.LocatorFixedOwnBound
import ProximityPrize.SubmissionLower.LocatorSelectedCaps
import ProximityPrize.SubmissionLower.LocatorAuxiliarySelection
import ProximityPrize.SubmissionLower.LocatorQuotientReplacement
import ProximityPrize.SubmissionLower.LocatorCover
namespace ProximityPrize.SubmissionLower.LocatorFixedBridge
open ProximityPrize.Benchmark
open scoped Classical
open RCN095 RCN180 RCN101 RCN234 RCN156 RCN275 RCN238 RCN243 RCN259 RCN319 RCN266 RCN130 RCN140 LocatorSelection LocatorFactorAggregate LocatorFactorReplacement LocatorReplacementGridData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
private abbrev regularBound:ℕ:=266501969061169804
theorem gcd_fixed_count_le
    (u0 u1:I → K) (S:SelectedPair u0 u1)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181579 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80565) :
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
  have hHflagA:H ∈ RCN100.globalCoefficientBox K 12347372 131071 130000 20:=
    LocatorCaps.full_A_divisor_mem_box u0 u1 H hH S.common_divides_A
  have hHcapsA:=(mem_flagGlobalCoefficientBox_iff H
    12347372 131071 130000 20 (by decide)).mp hHflagA
  have hT:wt residualTotalWeights H ≤ 3319:=S.common_total_le
  have hYS:wt residualYSWeights H ≤ 92:=S.common_ys_le
  have hS:wt residualSWeights H ≤ 20:=S.common_slope_le
  have hflag:H ∈ RCN100.globalCoefficientBox K 12347372 131071 3319 20:=
    (mem_flagGlobalCoefficientBox_iff H 12347372 131071 3319 20 (by decide)).mpr
      ⟨hT,hS,hHcapsA.2.2⟩
  have hbox:=flag_box_to_ordinary K 12347372 131071 3319 20 H hflag
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
  have hagreementD:∀ gamma ∈ Delta,181579 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card:=
    fun gamma hg=> hagreement gamma (hsub hg)
  have hnoD:NoLargeSelectedPencil selected Delta 131071 80565:=
    noLargeSelectedPencil_mono selected Gamma Delta 131071 80565 hsub hno
  let p:=regularCumulativeFlag H
  have hfcaps (F:RegularIndex H) :
      (p F).all ≤ 20 ∧ middle (p F) ≤ 92 ∧ total (p F) ≤ 3319:=by
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
  have hown (F:RegularIndex H) :
      LocatorHybridCost.OwnBound (regularSeeds H selected Delta F).card (p F):=
    LocatorFixedOwnBound.regular_factor_own_bound 12347372
      LocatorFixedConsumer.wholeSupport (by decide) (by decide)
      (by decide) (by decide) (by decide)
      H hH hbox hsupport selected Delta u0 u1 hdegreeD hagreementD hnoD F
      LocatorHybridRealize.realization
  have hqCost (F:RegularIndex H)
      (_hbad:BadCost 3319 LocatorHybridCost.ordinaryCostOf regularBound (p F)) :
      (regularSeeds H selected Delta F).card ≤ qCost F:=by
    let c:=cellOf (p F) (hfpos F) (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    have hc:InCell (p F) c:=
      cellOf_bounds (p F) (hfpos F) (hfcaps F).1
        (hfcaps F).2.1 (hfcaps F).2.2
    have hv:Valid c:=valid_of_inCell (p F) c
      (hfcaps F).2.1 (hfcaps F).2.2 hc
    have hf:=RCN167.positiveRFactors_spec H F.1 F.2
    have hdivA : ∀ v:RCN180.ConstraintKernel (K:=K)
        12347372 131071 130000 20 68 IRSProfile.domain u0 u1,
        F.1 ∣ RCN100.reconstruct K 12347372 131071 130000 20 v.1:=by
      intro v
      exact hf.2.1.trans
        (LocatorAuxiliarySelection.common_divides_A61_small S 130000 (by decide) v)
    have hdivAux : ∀ v:RCN180.ConstraintKernel (K:=K)
        13073688 131071 130000 21 72 IRSProfile.domain u0 u1,
        F.1 ∣ RCN100.reconstruct K 13073688 131071 130000 21 v.1:=by
      intro v
      exact hf.2.1.trans
        (LocatorAuxiliarySelection.common_divides_A72_small S 130000 (by decide) v)
    have hdivC : ∀ v:RCN180.ConstraintKernel (K:=K)
        54473700 131071 200000 87 300 IRSProfile.domain u0 u1,
        F.1 ∣ RCN100.reconstruct K 54473700 131071 200000 87 v.1:=by
      intro v
      exact hf.2.1.trans
        (LocatorAuxiliarySelection.common_divides_A150_small S 200000 (by decide) v)
    have h:=LocatorQuotientReplacement.regularSeeds_count_le_chosen
      u0 u1 H selected Delta hdegreeD hagreementD hnoD F hf.1.ne_zero
      hdivA hdivAux hdivC c hc hv (hown F)
    simpa only [qCost,c] using h
  have hqRate (F:RegularIndex H)
      (_hbad:BadCost 3319 LocatorHybridCost.ordinaryCostOf regularBound (p F)) :
      3319 * qCost F ≤ regularBound * total (p F):=by
    let c:=cellOf (p F) (hfpos F) (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    have hc:InCell (p F) c:=
      cellOf_bounds (p F) (hfpos F) (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    have hv:Valid c:=valid_of_inCell (p F) c
      (hfcaps F).2.1 (hfcaps F).2.2 hc
    have hrate:=chosenCost_rate c hv
    have hfactorT:(box c).factorT ≤ total (p F):=by
      unfold Box.factorT
      exact max_le hc.tlo_le (hc.ylo_le.trans (middle_le_total (p F)))
    have hrate' : 3319 * qCost F ≤ regularBound * (box c).factorT := by
      simpa only [qCost,c] using hrate
    exact hrate'.trans (Nat.mul_le_mul_left regularBound hfactorT)
  exact LocatorFixedConsumer.fixed_count_le H hH hbox hsupport
    selected Delta u0 u1 hsolution hdegreeD hagreementD hnoD hown qCost hqCost hqRate
end
end ProximityPrize.SubmissionLower.LocatorFixedBridge
