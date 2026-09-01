import ProximityPrize.SubmissionLower.LocatorFixedConsumer
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
private abbrev regularBound:ℕ:=268872673633727229
theorem gcd_fixed_count_le
    (u0 u1:I → K) (S:SelectedPair u0 u1)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181628 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80516) :
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
  have hHflagA:H ∈ RCN100.globalCoefficientBox K 11624192 131071 169536 19:=
    LocatorCaps.full_A_divisor_mem_box u0 u1 H hH S.common_divides_A
  have hHcapsA:=(mem_flagGlobalCoefficientBox_iff H
    11624192 131071 169536 19 (by decide)).mp hHflagA
  have hT:wt residualTotalWeights H ≤ 2916:=S.common_total_le
  have hYS:wt residualYSWeights H ≤ 85:=S.common_ys_le
  have hS:wt residualSWeights H ≤ 19:=S.common_slope_le
  have hflag:H ∈ RCN100.globalCoefficientBox K 11624192 131071 2916 19:=
    (mem_flagGlobalCoefficientBox_iff H 11624192 131071 2916 19 (by decide)).mpr
      ⟨hT,hS,hHcapsA.2.2⟩
  have hbox:=flag_box_to_ordinary K 11624192 131071 2916 19 H hflag
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
  have hagreementD:∀ gamma ∈ Delta,181628 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card:=
    fun gamma hg=> hagreement gamma (hsub hg)
  have hnoD:NoLargeSelectedPencil selected Delta 131071 80516:=
    noLargeSelectedPencil_mono selected Gamma Delta 131071 80516 hsub hno
  let p:=regularCumulativeFlag H
  have hfcaps (F:RegularIndex H) :
      (p F).all ≤ 19 ∧ middle (p F) ≤ 85 ∧ total (p F) ≤ 2916:=by
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
      (hbad:Bad 2916 131072 131073 regularBound (p F)) :
      (regularSeeds H selected Delta F).card ≤ qCost F:=by
    let c:=cellOf (p F) (hfpos F) (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    have hc:InCell (p F) c:=
      cellOf_bounds (p F) (hfpos F) (hfcaps F).1
        (hfcaps F).2.1 (hfcaps F).2.2
    have hv:Valid c:=valid_of_inCell (p F) c
      (hfcaps F).2.1 (hfcaps F).2.2 hc
    have hown:=LocatorFixed.regular_factor_count 11624192
      LocatorFixedConsumer.wholeSupport (by decide) (by decide)
      (by decide) (by decide) (by decide)
      H hH hbox hsupport selected Delta u0 u1 hdegreeD hagreementD hnoD F
    have hf:=RCN167.positiveRFactors_spec H F.1 F.2
    have hdivA : ∀ v:RCN180.ConstraintKernel (K:=K)
        11624192 131071 169536 19 64 IRSProfile.domain u0 u1,
        F.1 ∣ RCN100.reconstruct K 11624192 131071 169536 19 v.1:=by
      intro v
      exact hf.2.1.trans
        (LocatorAuxiliarySelection.common_divides_A61_small S 169536 (by decide) v)
    have hdivAux : ∀ v:RCN180.ConstraintKernel (K:=K)
        13077216 131071 169536 21 72 IRSProfile.domain u0 u1,
        F.1 ∣ RCN100.reconstruct K 13077216 131071 169536 21 v.1:=by
      intro v
      exact hf.2.1.trans
        (LocatorAuxiliarySelection.common_divides_A72_small S 169536 (by decide) v)
    have hdivC : ∀ v:RCN180.ConstraintKernel (K:=K)
        39050020 131071 169536 63 215 IRSProfile.domain u0 u1,
        F.1 ∣ RCN100.reconstruct K 39050020 131071 169536 63 v.1:=by
      intro v
      exact hf.2.1.trans
        (LocatorAuxiliarySelection.common_divides_A150_small S 169536 (by decide) v)
    have h:=LocatorQuotientReplacement.regularSeeds_count_le_chosen
      u0 u1 H selected Delta hdegreeD hagreementD hnoD F hf.1.ne_zero
      hdivA hdivAux hdivC c hc hv hown
    simpa only [qCost,c] using h
  have hqRate (F:RegularIndex H)
      (_hbad:Bad 2916 131072 131073 regularBound (p F)) :
      2916 * qCost F ≤ regularBound * total (p F):=by
    let c:=cellOf (p F) (hfpos F) (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    have hc:InCell (p F) c:=
      cellOf_bounds (p F) (hfpos F) (hfcaps F).1 (hfcaps F).2.1 (hfcaps F).2.2
    have hv:Valid c:=valid_of_inCell (p F) c
      (hfcaps F).2.1 (hfcaps F).2.2 hc
    have hrate:=chosenCost_rate c hv
    have hfactorT:(box c).factorT ≤ total (p F):=by
      unfold Box.factorT
      exact max_le hc.tlo_le (hc.ylo_le.trans (middle_le_total (p F)))
    have hrate' : 2916 * qCost F ≤ regularBound * (box c).factorT := by
      simpa only [qCost,c] using hrate
    exact hrate'.trans (Nat.mul_le_mul_left regularBound hfactorT)
  exact LocatorFixedConsumer.fixed_count_le H hH hbox hsupport
    selected Delta u0 u1 hsolution hdegreeD hagreementD hnoD qCost hqCost hqRate
end
end ProximityPrize.SubmissionLower.LocatorFixedBridge
