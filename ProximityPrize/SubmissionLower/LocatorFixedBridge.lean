import ProximityPrize.SubmissionLower.LocatorFixedConsumer
import ProximityPrize.SubmissionLower.LocatorFixedOwnBoundC2
import ProximityPrize.SubmissionLower.LocatorSelectedCaps
import ProximityPrize.SubmissionLower.LocatorQuotientReplacement
import ProximityPrize.SubmissionLower.LocatorPairGrid
import ProximityPrize.SubmissionLower.LocatorCover
namespace ProximityPrize.SubmissionLower.LocatorFixedBridge
open ProximityPrize.Benchmark
open scoped Classical
open RCN095 RCN100 RCN180 RCN101 RCN234 RCN156 RCN275 RCN238 RCN243 RCN259 RCN319 RCN266 RCN130 RCN140 LocatorSelection LocatorFactorAggregate LocatorFactorReplacement LocatorReplacementGridData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
/-! Row 6786.  The common divisor `H` of the selected pair divides every B and
total-cap reconstruction, so it lies in the B box (slope `24`, ys `113`) with
total at most `3808`.  Each regular factor is charged by one of two grids:
if it divides every A reconstruction it lies in the narrow box (slope `22`,
ys `99`) and the adaptive receipt grid applies; otherwise the generic
divisor-or-helper switch counts it by a direct coprime pair with an A
reconstruction, and the wide coarse pair grid certifies that rate. -/
theorem gcd_fixed_count_le
    (u0 u1:I → K) (S:SelectedPair u0 u1)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181530 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80614) :
    (LocatorCover.fixed
      (fun gamma=> (specialization K (selected gamma) gamma).toRingHom)
      Gamma S.QA S.QB).card ≤
      bound + LocatorArithmetic.fixedSingular.countCap:=by
  classical
  let H:P4:=gcd12 S.QA S.QB
  let phi:K → P4 →+* Polynomial K:=
    fun gamma=> (specialization K (selected gamma) gamma).toRingHom
  let Delta:Finset K:=LocatorCover.fixed phi Gamma S.QA S.QB
  have hH:H ≠ 0:=gcd_ne_zero_of_left S.QA_ne
  have hHflagB:H ∈ RCN100.globalCoefficientBox K 14885460 131071 9600 24:=
    LocatorCaps.full_B_divisor_mem_box u0 u1 H hH S.common_divides_B
  have hHcapsB:=(mem_flagGlobalCoefficientBox_iff H
    14885460 131071 9600 24 (by decide)).mp hHflagB
  have hT:wt residualTotalWeights H ≤ 3808:=S.common_total_le
  have hYS:wt residualYSWeights H ≤ 113:=S.common_ys_le
  have hS:wt residualSWeights H ≤ 24:=S.common_slope_le
  have hflag:H ∈ RCN100.globalCoefficientBox K 14885460 131071 3808 24:=
    (mem_flagGlobalCoefficientBox_iff H 14885460 131071 3808 24 (by decide)).mpr
      ⟨hT,hS,hHcapsB.2.2⟩
  have hbox:=flag_box_to_ordinary K 14885460 131071 3808 24 H hflag
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
  have hagreementD:∀ gamma ∈ Delta,181530 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i) =u0 i + gamma * u1 i)).card:=
    fun gamma hg=> hagreement gamma (hsub hg)
  have hnoD:NoLargeSelectedPencil selected Delta 131071 80614:=
    noLargeSelectedPencil_mono selected Gamma Delta 131071 80614 hsub hno
  let p:=regularCumulativeFlag H
  have hfcaps (F:RegularIndex H) :
      (p F).all ≤ 24 ∧ middle (p F) ≤ 113 ∧ total (p F) ≤ 3808:=by
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
  have hown (F:RegularIndex H) :
      LocatorHybridCostC2.OwnBoundC2 (regularSeeds H selected Delta F).card (p F):=
    LocatorFixedOwnBoundC2.regular_factor_own_bound 14885460
      LocatorFixedConsumer.wholeSupport (by decide) (by decide)
      (by decide) (by decide) (by decide)
      H hH hbox hsupport selected Delta u0 u1 hdegreeD hagreementD hnoD F
      LocatorHybridRealizeC2.realizationC2
  have hrepl (F:RegularIndex H)
      (_hbad:BadCostW capSum LocatorHybridCostC2.ordinaryCostOfC2 bound
        LocatorFixedConsumer.wgt (p F)) :
      ∃ q:ℕ, (regularSeeds H selected Delta F).card ≤ q ∧
        capSum * q ≤ bound * LocatorFixedConsumer.wgt (p F):=by
    have hf:=RCN167.positiveRFactors_spec H F.1 F.2
    have hF:F.1 ≠ 0:=hf.1.ne_zero
    have hc:=originalCumulativeFlag_cumulative F.1
    have hall:wt residualSWeights F.1=(p F).all:=by
      simp only [p,regularCumulativeFlag,hc.1]
    have hmid:wt residualYSWeights F.1=middle (p F):=by
      simp only [p,regularCumulativeFlag,middle,hc.2.1]
    have htot:wt residualTotalWeights F.1=total (p F):=by
      simp only [p,regularCumulativeFlag,total,hc.2.2]
    by_cases hA:∀ v:ConstraintKernel (K:=K) 13614750 131071 130000 22 75
        IRSProfile.domain u0 u1,
        F.1 ∣ reconstruct K 13614750 131071 130000 22 v.1
    · have hys:middle (p F) ≤ 99:=by
        have h:=LocatorCaps.common_A_ys_le u0 u1 F.1 hF hA
        simpa only [p,regularCumulativeFlag,middle,hc.2.1] using h
      have hsl:(p F).all ≤ 22:=by
        have h:=LocatorCaps.common_A_slope_le u0 u1 F.1 hF hA
        simpa only [p,regularCumulativeFlag,hc.1] using h
      let c:=cellOf (p F) (hfpos F) hsl hys (hfcaps F).2.2
      have hcell:InCell (p F) c:=cellOf_bounds (p F) (hfpos F) hsl hys (hfcaps F).2.2
      have hv:Valid c:=valid_of_inCell (p F) c hys (hfcaps F).2.2 hcell
      refine ⟨chosenCost c, ?_, ?_⟩
      · exact LocatorQuotientReplacement.regularSeeds_count_le_chosen
          u0 u1 H selected Delta hdegreeD hagreementD hnoD F hF c hcell hv (hown F)
      · have hrate:=chosenCost_rate c hv
        have hfactorT:(box c).factorT ≤ total (p F):=by
          unfold Box.factorT
          exact max_le hcell.tlo_le (hcell.ylo_le.trans (middle_le_total (p F)))
        have hweight:(box c).weight ≤ LocatorFixedConsumer.wgt (p F):=by
          unfold Box.weight LocatorFixedConsumer.wgt
          exact Nat.add_le_add
            (Nat.add_le_add hfactorT (Nat.mul_le_mul_left wY hcell.ylo_le))
            (Nat.mul_le_mul_left wS (le_of_eq hcell.all_eq.symm))
        exact hrate.trans (Nat.mul_le_mul_left bound hweight)
    · let e:=LocatorPairGrid.extCellOf (p F) (hfpos F) (hfcaps F).1
        (hfcaps F).2.1 (hfcaps F).2.2
      have hb:=LocatorPairGrid.extCellOf_bounds (p F) (hfpos F) (hfcaps F).1
        (hfcaps F).2.1 (hfcaps F).2.2
      have hpair:=LocatorPairGrid.ext_pair_fits (p F) (hfpos F) (hfcaps F).1
        (hfcaps F).2.1 (hfcaps F).2.2
      let b:=LocatorPairGrid.extBox e
      have hFY:F.1.degreeOf 1 ≤ b.factorY:=by
        apply (LocatorQuotientReplacement.degreeY_le_ysWeight F.1).trans
        rw [hmid]
        exact le_min hb.2.2.1 ((middle_le_total (p F)).trans hb.2.2.2.2)
      have hFR:F.1.degreeOf 2 ≤ b.r:=by
        rw [← LocatorContact.slope_weight_eq_degreeR,hall]
        exact hb.1.le
      have hFZ:F.1.degreeOf 3 ≤ b.thi:=by
        apply (LocatorQuotientReplacement.degreeZ_le_totalWeight F.1).trans
        rw [htot]
        exact hb.2.2.2.2
      have hgates:LocatorHelperFactorSwitchGenericC2.HelperPairGates
          103 22 130000 b.factorY b.r b.thi:=by
        simpa only [LocatorHelperFactorSwitchGenericC2.HelperPairGates,
          LocatorHelperFactorSwitchGenericC2.helperPair,
          LocatorReplacementGridData.helperPair,LocatorPairGrid.PairFits,
          PairGates,sourceA] using hpair.1
      rcases LocatorHelperFactorSwitchGenericC2.divisor_or_helper_count
          13614750 130000 22 75 103 (by decide) (by decide)
          LocatorHelperArithmeticGeneric.sourceA_shape
          selected Delta hdegreeD hagreementD hnoD F b.factorY b.r b.thi
          hFY hFR hFZ hgates with hdiv | hcount
      · exact absurd hdiv hA
      · refine ⟨(helperPair sourceA b).regularCountCap, ?_, ?_⟩
        · simpa only [LocatorHelperFactorSwitchGenericC2.helperPair,
            LocatorReplacementGridData.helperPair,sourceA] using hcount
        · have hfactorT:b.factorT ≤ total (p F):=by
            unfold Box.factorT
            exact max_le hb.2.2.2.1 (hb.2.1.trans (middle_le_total (p F)))
          have hweight:b.weight ≤ LocatorFixedConsumer.wgt (p F):=by
            unfold Box.weight LocatorFixedConsumer.wgt
            exact Nat.add_le_add
              (Nat.add_le_add hfactorT (Nat.mul_le_mul_left wY hb.2.1))
              (Nat.mul_le_mul_left wS (le_of_eq hb.1.symm))
          exact hpair.2.trans (Nat.mul_le_mul_left bound hweight)
  let qCost:RegularIndex H → ℕ:=fun F=>
    if h:BadCostW capSum LocatorHybridCostC2.ordinaryCostOfC2 bound
        LocatorFixedConsumer.wgt (p F) then
      Classical.choose (hrepl F h) else 0
  have hqCost (F:RegularIndex H)
      (hbad:BadCostW capSum LocatorHybridCostC2.ordinaryCostOfC2 bound
        LocatorFixedConsumer.wgt (p F)) :
      (regularSeeds H selected Delta F).card ≤ qCost F:=by
    simp only [qCost,dif_pos hbad]
    exact (Classical.choose_spec (hrepl F hbad)).1
  have hqRate (F:RegularIndex H)
      (hbad:BadCostW capSum LocatorHybridCostC2.ordinaryCostOfC2 bound
        LocatorFixedConsumer.wgt (p F)) :
      capSum * qCost F ≤ bound * LocatorFixedConsumer.wgt (p F):=by
    simp only [qCost,dif_pos hbad]
    exact (Classical.choose_spec (hrepl F hbad)).2
  exact LocatorFixedConsumer.fixed_count_le H hH hbox hsupport
    selected Delta u0 u1 hsolution hdegreeD hagreementD hnoD hown qCost hqCost hqRate
end
end ProximityPrize.SubmissionLower.LocatorFixedBridge
