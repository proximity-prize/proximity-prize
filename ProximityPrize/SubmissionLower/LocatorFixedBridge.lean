import ProximityPrize.SubmissionLower.LocatorFixed
import ProximityPrize.SubmissionLower.LocatorSelectedCaps
import ProximityPrize.SubmissionLower.LocatorCover


namespace ProximityPrize.SubmissionLower.LocatorFixedBridge
open ProximityPrize.Benchmark
open scoped Classical
open RCN180 RCN101 RCN234 RCN156 RCN275 RCN238 RCN243 RCN259 RCN319
open RCN266 RCN130
open LocatorSelection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4

theorem gcd_fixed_count_le
    (u0 u1:I → K) (S:SelectedPair u0 u1)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree≤131071)
    (hagreement:∀ gamma∈Gamma,181953≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80191):
    (LocatorCover.fixed
      (fun gamma=>(specialization K (selected gamma) gamma).toRingHom)
      Gamma S.QA S.QB).card≤
      271263904445294429+LocatorArithmetic.fixedSingular.countCap:=by
  classical
  let H:P4:=gcd12 S.QA S.QB
  let phi:K → P4 →+*Polynomial K:=
    fun gamma=>(specialization K (selected gamma) gamma).toRingHom
  let Delta:Finset K:=LocatorCover.fixed phi Gamma S.QA S.QB
  have hH:H≠0:=gcd_ne_zero_of_left S.QA_ne
  have hHflagC:H∈RCN100.globalCoefficientBox K 8187885 131071 24496 13:=
    S.common_C_flag
  have hHcaps:=(mem_flagGlobalCoefficientBox_iff H
    8187885 131071 24496 13 (by decide)).mp hHflagC
  have hT:wt residualTotalWeights H≤1469:=S.common_total_le
  have hY:wt residualYSWeights H≤60:=S.common_ys_le
  have hS:wt residualSWeights H≤13:=S.common_slope_le
  have hflag:H∈RCN100.globalCoefficientBox K 8187885 131071 1469 13:=
    (mem_flagGlobalCoefficientBox_iff H 8187885 131071 1469 13 (by decide)).mpr
      ⟨hT,hS,hHcaps.2.2⟩
  have hbox:=flag_box_to_ordinary K 8187885 131071 1469 13 H hflag
  have hsupport:ResidualSupportData LocatorFixed.wholeSupport H:=
    ⟨hS,hY,hT⟩
  have hsub:Delta ⊆ Gamma:=by
    intro gamma hg
    have hm:gamma∈Gamma ∧ (phi gamma) (gcd12 S.QA S.QB)=0:=by
      simpa only [Delta,LocatorCover.fixed,Finset.mem_filter] using hg
    exact hm.1
  have hsolution:∀ gamma∈Delta,specialization K (selected gamma) gamma H=0:=by
    intro gamma hg
    exact LocatorCover.fixed_vanish phi Gamma S.QA S.QB gamma hg
  have hdegreeD:∀ gamma∈Delta,(selected gamma).natDegree≤131071:=
    fun gamma hg=>hdegree gamma (hsub hg)
  have hagreementD:∀ gamma∈Delta,181953≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card:=
    fun gamma hg=>hagreement gamma (hsub hg)
  have hnoD:NoLargeSelectedPencil selected Delta 131071 80191:=
    noLargeSelectedPencil_mono selected Gamma Delta 131071 80191 hsub hno
  have h10 (R:RegularIndex H) (hs:(regularCumulativeFlag H R).all=10):
      LocatorFactorAggregate.middle (regularCumulativeFlag H R)≤56:=by
    have hf:=RCN167.positiveRFactors_spec H R.1 R.2
    have hc:=originalCumulativeFlag_cumulative R.1
    have hR:R.1.degreeOf (2:Fin 4)=10:=by
      rw [← LocatorContact.slope_weight_eq_degreeR,← hc.1]
      exact hs
    have hy:=S.factor_r10_ys_le R.1 hf.1 hf.2.1 hR
    simpa only [LocatorFactorAggregate.middle,regularCumulativeFlag,hc.2.1] using hy
  have h11 (R:RegularIndex H) (hs:(regularCumulativeFlag H R).all=11):
      LocatorFactorAggregate.middle (regularCumulativeFlag H R)≤52:=by
    have hf:=RCN167.positiveRFactors_spec H R.1 R.2
    have hc:=originalCumulativeFlag_cumulative R.1
    have hR:R.1.degreeOf (2:Fin 4)=11:=by
      rw [← LocatorContact.slope_weight_eq_degreeR,← hc.1]
      exact hs
    have hy:=S.factor_r11_ys_le R.1 hf.1 hf.2.1 hR
    simpa only [LocatorFactorAggregate.middle,regularCumulativeFlag,hc.2.1] using hy
  have h12 (R:RegularIndex H) (hs:(regularCumulativeFlag H R).all=12):
      LocatorFactorAggregate.middle (regularCumulativeFlag H R)≤48:=by
    have hf:=RCN167.positiveRFactors_spec H R.1 R.2
    have hc:=originalCumulativeFlag_cumulative R.1
    have hR:R.1.degreeOf (2:Fin 4)=12:=by
      rw [← LocatorContact.slope_weight_eq_degreeR,← hc.1]
      exact hs
    have hy:=S.factor_r12_ys_le R.1 hf.1 hf.2.1 hR
    simpa only [LocatorFactorAggregate.middle,regularCumulativeFlag,hc.2.1] using hy
  have h13 (R:RegularIndex H) (hs:(regularCumulativeFlag H R).all=13):
      LocatorFactorAggregate.middle (regularCumulativeFlag H R)≤44:=by
    have hf:=RCN167.positiveRFactors_spec H R.1 R.2
    have hc:=originalCumulativeFlag_cumulative R.1
    have hR:R.1.degreeOf (2:Fin 4)=13:=by
      rw [← LocatorContact.slope_weight_eq_degreeR,← hc.1]
      exact hs
    have hy:=S.factor_r13_ys_le R.1 hf.1 hf.2.1 hR
    simpa only [LocatorFactorAggregate.middle,regularCumulativeFlag,hc.2.1] using hy
  have ht9 (R:RegularIndex H) (hs:(regularCumulativeFlag H R).all=9)
      (hy:60≤LocatorFactorAggregate.middle (regularCumulativeFlag H R)):
      LocatorFactorAggregate.total (regularCumulativeFlag H R)≤1252:=by
    have hf:=RCN167.positiveRFactors_spec H R.1 R.2
    have hc:=originalCumulativeFlag_cumulative R.1
    have hR:R.1.degreeOf (2:Fin 4)=9:=by
      rw [← LocatorContact.slope_weight_eq_degreeR,← hc.1]; exact hs
    have hY:60≤wt residualYSWeights R.1:=by
      simpa only [LocatorFactorAggregate.middle,regularCumulativeFlag,hc.2.1] using hy
    have ht:=S.factor_r9_ys60_total_le R.1 hf.1 hf.2.1 hR hY
    simpa only [LocatorFactorAggregate.total,regularCumulativeFlag,hc.2.2] using ht
  have ht10 (R:RegularIndex H) (hs:(regularCumulativeFlag H R).all=10)
      (hy:40≤LocatorFactorAggregate.middle (regularCumulativeFlag H R)):
      LocatorFactorAggregate.total (regularCumulativeFlag H R)≤1406:=by
    have hf:=RCN167.positiveRFactors_spec H R.1 R.2
    have hc:=originalCumulativeFlag_cumulative R.1
    have hR:R.1.degreeOf (2:Fin 4)=10:=by
      rw [← LocatorContact.slope_weight_eq_degreeR,← hc.1]; exact hs
    have hY:40≤wt residualYSWeights R.1:=by
      simpa only [LocatorFactorAggregate.middle,regularCumulativeFlag,hc.2.1] using hy
    have ht:=S.factor_r10_ys40_total_le R.1 hf.1 hf.2.1 hR hY
    simpa only [LocatorFactorAggregate.total,regularCumulativeFlag,hc.2.2] using ht
  have ht11 (R:RegularIndex H) (hs:(regularCumulativeFlag H R).all=11)
      (hy:36≤LocatorFactorAggregate.middle (regularCumulativeFlag H R)):
      LocatorFactorAggregate.total (regularCumulativeFlag H R)≤1407:=by
    have hf:=RCN167.positiveRFactors_spec H R.1 R.2
    have hc:=originalCumulativeFlag_cumulative R.1
    have hR:R.1.degreeOf (2:Fin 4)=11:=by
      rw [← LocatorContact.slope_weight_eq_degreeR,← hc.1]; exact hs
    have hY:36≤wt residualYSWeights R.1:=by
      simpa only [LocatorFactorAggregate.middle,regularCumulativeFlag,hc.2.1] using hy
    have ht:=S.factor_r11_ys36_total_le R.1 hf.1 hf.2.1 hR hY
    simpa only [LocatorFactorAggregate.total,regularCumulativeFlag,hc.2.2] using ht
  have ht12 (R:RegularIndex H) (hs:(regularCumulativeFlag H R).all=12)
      (hy:32≤LocatorFactorAggregate.middle (regularCumulativeFlag H R)):
      LocatorFactorAggregate.total (regularCumulativeFlag H R)≤1405:=by
    have hf:=RCN167.positiveRFactors_spec H R.1 R.2
    have hc:=originalCumulativeFlag_cumulative R.1
    have hR:R.1.degreeOf (2:Fin 4)=12:=by
      rw [← LocatorContact.slope_weight_eq_degreeR,← hc.1]; exact hs
    have hY:32≤wt residualYSWeights R.1:=by
      simpa only [LocatorFactorAggregate.middle,regularCumulativeFlag,hc.2.1] using hy
    have ht:=S.factor_r12_ys32_total_le R.1 hf.1 hf.2.1 hR hY
    simpa only [LocatorFactorAggregate.total,regularCumulativeFlag,hc.2.2] using ht
  have ht13 (R:RegularIndex H) (hs:(regularCumulativeFlag H R).all=13)
      (hy:27≤LocatorFactorAggregate.middle (regularCumulativeFlag H R)):
      LocatorFactorAggregate.total (regularCumulativeFlag H R)≤1408:=by
    have hf:=RCN167.positiveRFactors_spec H R.1 R.2
    have hc:=originalCumulativeFlag_cumulative R.1
    have hR:R.1.degreeOf (2:Fin 4)=13:=by
      rw [← LocatorContact.slope_weight_eq_degreeR,← hc.1]; exact hs
    have hY:27≤wt residualYSWeights R.1:=by
      simpa only [LocatorFactorAggregate.middle,regularCumulativeFlag,hc.2.1] using hy
    have ht:=S.factor_r13_ys27_total_le R.1 hf.1 hf.2.1 hR hY
    simpa only [LocatorFactorAggregate.total,regularCumulativeFlag,hc.2.2] using ht
  exact LocatorFixed.fixed_count_le H hH hbox hsupport
    selected Delta u0 u1 hsolution hdegreeD hagreementD hnoD h10 h11 h12 h13
    ht9 ht10 ht11 ht12 ht13

end
end ProximityPrize.SubmissionLower.LocatorFixedBridge
