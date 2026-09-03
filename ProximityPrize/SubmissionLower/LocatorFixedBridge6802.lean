import ProximityPrize.SubmissionLower.LocatorFixedConsumer6802
import ProximityPrize.SubmissionLower.LocatorFixedOwnBoundC2

namespace ProximityPrize.SubmissionLower.LocatorFixedBridge6802

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN095 RCN100 RCN101 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN243 RCN259 RCN260 RCN266 RCN275 RCN319
open LocatorSelection6802 LocatorFactorAggregate LocatorBatchProductRoute

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4

/-- Exact direct helper charge for one factor exiting at the A source. -/
def initialAHelperCap (p:FlagDegree):ℕ:=
  (LocatorGenericHelperFactorSwitch6802.helperPair
    130000 132 29 (middle p) p.all (total p)).regularCountCap

/-- Linear reconstruction of the independent A source. -/
def initialAMap (u0 u1:I → K):LocatorCaps6802.AKernel u0 u1 →ₗ[K] P4:=
  kernelReconstructLinear (K:=K) 17411808 131071 130000 29 96
    IRSProfile.domain u0 u1

/-- Factors universal on the current A source. -/
def initialAUniversalFactors (u0 u1:I → K) (H:P4):
    Finset (RegularIndex H):=
  universalFactors H (Finset.univ:Finset (RegularIndex H))
    (initialAMap u0 u1)

@[simp] theorem mem_initialAUniversalFactors
    (u0 u1:I → K) (H:P4) (F:RegularIndex H):
    F ∈ initialAUniversalFactors u0 u1 H ↔
      ∀ v:LocatorCaps6802.AKernel u0 u1,
        F.1 ∣ reconstruct K 17411808 131071 130000 29 v.1:=by
  simp only [initialAUniversalFactors,mem_universalFactors,Finset.mem_univ,
    true_and,initialAMap,kernelReconstructLinear_apply]

/-- The universal A factors divide every A row jointly. -/
theorem initialAUniversalProduct_dvd
    (u0 u1:I → K) (H:P4):
    ∀ v:LocatorCaps6802.AKernel u0 u1,
      regularProduct H (initialAUniversalFactors u0 u1 H) ∣
        reconstruct K 17411808 131071 130000 29 v.1:=by
  intro v
  have h:=universalProduct_dvd H
    (Finset.univ:Finset (RegularIndex H)) (initialAMap u0 u1) v
  simpa only [initialAUniversalFactors,initialAMap,
    kernelReconstructLinear_apply] using h

/-- The same universal product divides the selected carrier. -/
theorem initialAUniversalProduct_dvd_carrier
    (u0 u1:I → K) (H:P4):
    regularProduct H (initialAUniversalFactors u0 u1 H) ∣ H:=
  regularProduct_dvd_carrier H (initialAUniversalFactors u0 u1 H)

private theorem degreeY_le_ysWeight (Q:P4):
    Q.degreeOf (1:Fin 4) ≤ wt residualYSWeights Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*0 ≤ wt residualYSWeights Q at h
  omega

private theorem degreeZ_le_totalWeight (Q:P4):
    Q.degreeOf (3:Fin 4) ≤ wt residualTotalWeights Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*1 ≤ wt residualTotalWeights Q at h
  omega

private theorem initialA_helper_gates (p:FlagDegree)
    (hr:1 ≤ p.all) (hs:p.all ≤ 32)
    (hy:middle p ≤ 149) (ht:total p ≤ 6403):
    LocatorGenericHelperFactorSwitch6802.HelperPairGates
      130000 132 29 (middle p) p.all (total p):=by
  unfold LocatorGenericHelperFactorSwitch6802.HelperPairGates
  change 1 ≤ p.all ∧ middle p < 2130706433 ∧ p.all < 2130706433 ∧
    total p < 2130706433 ∧
    p.all*130000+total p*29 < 2130706433 ∧
    middle p*130000+total p*132 < 2130706433 ∧
    middle p*29+p.all*132 < 2130706433
  omega

/-- Every factor outside the A-universal set gets the direct coprime A
helper, with no minimum against its ordinary cost. -/
theorem initialA_nonuniversal_count
    (u0 u1:I → K) (H:P4) (hH:H ≠ 0)
    (hwide:ResidualSupportData LocatorFixedConsumer6802.wideSupport H)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181373 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80771)
    (F:RegularIndex H) (hFU:F ∉ initialAUniversalFactors u0 u1 H):
    (regularSeeds H selected Gamma F).card ≤
      initialAHelperCap (regularCumulativeFlag H F):=by
  have hFsupport:=LocatorFixed6802.factor_support H hH hwide F
  have hc:=originalCumulativeFlag_cumulative F.1
  have hs:(regularCumulativeFlag H F).all ≤ 32:=by
    simpa only [regularCumulativeFlag,hc.1,LocatorFixedConsumer6802.wideSupport]
      using hFsupport.s_weight
  have hy:middle (regularCumulativeFlag H F) ≤ 149:=by
    simpa only [regularCumulativeFlag,middle,hc.2.1,
      LocatorFixedConsumer6802.wideSupport] using hFsupport.ys_weight
  have ht:total (regularCumulativeFlag H F) ≤ 6403:=by
    simpa only [regularCumulativeFlag,total,hc.2.2,
      LocatorFixedConsumer6802.wideSupport] using hFsupport.total_weight
  have hr:1 ≤ (regularCumulativeFlag H F).all:=
    Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (regularCumulativeFlag_positive H F))
  have hFY:F.1.degreeOf 1 ≤ middle (regularCumulativeFlag H F):=by
    rw [regularCumulativeFlag,middle,hc.2.1]
    exact degreeY_le_ysWeight F.1
  have hFR:F.1.degreeOf 2 ≤ (regularCumulativeFlag H F).all:=by
    rw [regularCumulativeFlag,originalCumulativeFlag_all]
  have hFZ:F.1.degreeOf 3 ≤ total (regularCumulativeFlag H F):=by
    rw [regularCumulativeFlag,total,hc.2.2]
    exact degreeZ_le_totalWeight F.1
  rcases LocatorGenericHelperFactorSwitch6802.divisor_or_helper_count
      17411808 130000 29 96 132 (by decide) (by decide) (by decide)
      selected Gamma hdegree hagreement hno F
      (middle (regularCumulativeFlag H F)) (regularCumulativeFlag H F).all
      (total (regularCumulativeFlag H F)) hFY hFR hFZ
      (initialA_helper_gates (regularCumulativeFlag H F) hr hs hy ht) with
    hdiv | hcount
  · exact False.elim (hFU ((mem_initialAUniversalFactors u0 u1 H F).2 hdiv))
  · simpa only [initialAHelperCap] using hcount

/-- An A-universal factor has a narrow own-bound even though the whole
selected gcd is wide. -/
theorem initialA_universal_ownBound
    (u0 u1:I → K) (H:P4) (hH:H ≠ 0)
    (hTotal:wt residualTotalWeights H ≤ 6403)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181373 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80771)
    (F:RegularIndex H) (hFU:F ∈ initialAUniversalFactors u0 u1 H):
    LocatorHybridCostC2.OwnBoundC2 (regularSeeds H selected Gamma F).card
      (regularCumulativeFlag H F):=by
  have hF:=RCN167.positiveRFactors_spec H F.1 F.2
  have hdivA:∀ v:LocatorCaps6802.AKernel u0 u1,
      F.1 ∣ reconstruct K 17411808 131071 130000 29 v.1:=
    (mem_initialAUniversalFactors u0 u1 H F).1 hFU
  have hAflag:=LocatorCaps6802.full_A_divisor_mem_box u0 u1 F.1
    hF.1.ne_zero hdivA
  have hAcaps:=(mem_flagGlobalCoefficientBox_iff F.1
    17411808 131071 130000 29 (by decide)).mp hAflag
  have hFt:wt residualTotalWeights F.1 ≤ 6403:=
    (weightedTotalDegree_le_of_dvd residualTotalWeights F.1 H hF.2.1 hH).trans
      hTotal
  have hFy:wt residualYSWeights F.1 ≤ 132:=
    LocatorCaps6802.common_A_ys_le u0 u1 F.1 hF.1.ne_zero hdivA
  have hFs:wt residualSWeights F.1 ≤ 29:=
    LocatorCaps6802.common_A_slope_le u0 u1 F.1 hF.1.ne_zero hdivA
  have hFflag:F.1 ∈ globalCoefficientBox K 17411808 131071 6403 29:=
    (mem_flagGlobalCoefficientBox_iff F.1
      17411808 131071 6403 29 (by decide)).mpr ⟨hFt,hFs,hAcaps.2.2⟩
  have hFbox:=flag_box_to_ordinary K 17411808 131071 6403 29 F.1 hFflag
  have hFsupport:ResidualSupportData LocatorFixedConsumer6802.wholeSupport F.1:=
    ⟨hFs,hFy,hFt⟩
  let Fself:=LocatorCoprimeQuotient.regularIndexSelf H F
  have hown:=LocatorFixedOwnBoundC2.regular_factor_own_bound 17411808
    LocatorFixedConsumer6802.wholeSupport (by decide) (by decide)
    (by decide) (by decide) (by decide)
    F.1 hF.1.ne_zero hFbox hFsupport selected Gamma u0 u1
    hdegree hagreement hno Fself LocatorHybridRealizeC2.realizationC2
  simpa only [RCN140.regularSeeds,regularCumulativeFlag,Fself,
    LocatorCoprimeQuotient.regularIndexSelf_val] using hown

/-! ## Wide selected-gcd bridge with a replaceable numerical receipt -/

/-- Algebraic bridge to the phase-potential certificate.  `hphase` bounds
the A-universal child; `hledger` combines it with the exact direct-A charges
of all factors that exit at this first split. -/
theorem gcd_fixed_count_le_of_initial_phase
    (u0 u1:I → K) (S:LocatorSelection6802.SelectedPair u0 u1)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181373 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80771)
    (phaseCap:ℕ)
    (hphase:
      let H:P4:=gcd12 S.QA S.QB
      let phi:K → P4 →+* Polynomial K:=
        fun gamma=>(specialization K (selected gamma) gamma).toRingHom
      let Delta:=LocatorCover.fixed phi Gamma S.QA S.QB
      let U:=initialAUniversalFactors u0 u1 H
      (∑ F ∈ U,(regularSeeds H selected Delta F).card) ≤ phaseCap)
    (hledger:
      let H:P4:=gcd12 S.QA S.QB
      let U:=initialAUniversalFactors u0 u1 H
      phaseCap+(∑ F ∈ (Finset.univ:Finset (RegularIndex H)) \ U,
        initialAHelperCap (regularCumulativeFlag H F)) ≤
          LocatorFixedConsumer6802.initialRegularCap):
    (LocatorCover.fixed
      (fun gamma=>(specialization K (selected gamma) gamma).toRingHom)
      Gamma S.QA S.QB).card ≤
      LocatorFixedConsumer6802.initialRegularCap+
        LocatorArithmetic6802.fixedSingularCap:=by
  classical
  let H:P4:=gcd12 S.QA S.QB
  let phi:K → P4 →+* Polynomial K:=
    fun gamma=>(specialization K (selected gamma) gamma).toRingHom
  let Delta:Finset K:=LocatorCover.fixed phi Gamma S.QA S.QB
  let U:=initialAUniversalFactors u0 u1 H
  have hH:H ≠ 0:=gcd_ne_zero_of_left S.QA_ne
  have hBflag:H ∈ globalCoefficientBox K 19588284 131071 15200 32:=
    LocatorCaps6802.full_B_divisor_mem_box u0 u1 H hH S.common_divides_B
  have hBcaps:=(mem_flagGlobalCoefficientBox_iff H
    19588284 131071 15200 32 (by decide)).mp hBflag
  have hT:wt residualTotalWeights H ≤ 6403:=S.common_total_le
  have hYS:wt residualYSWeights H ≤ 149:=S.common_ys_le
  have hS:wt residualSWeights H ≤ 32:=S.common_slope_le
  have hflag:H ∈ globalCoefficientBox K 19588284 131071 6403 32:=
    (mem_flagGlobalCoefficientBox_iff H
      19588284 131071 6403 32 (by decide)).mpr ⟨hT,hS,hBcaps.2.2⟩
  have hbox:=flag_box_to_ordinary K 19588284 131071 6403 32 H hflag
  have hwide:ResidualSupportData LocatorFixedConsumer6802.wideSupport H:=
    ⟨hS,hYS,hT⟩
  have hsub:Delta ⊆ Gamma:=by
    intro gamma hg
    have hm:gamma ∈ Gamma ∧ (phi gamma) (gcd12 S.QA S.QB)=0:=by
      simpa only [Delta,LocatorCover.fixed,Finset.mem_filter] using hg
    exact hm.1
  have hsolution:∀ gamma ∈ Delta,
      specialization K (selected gamma) gamma H=0:=by
    intro gamma hg
    exact LocatorCover.fixed_vanish phi Gamma S.QA S.QB gamma hg
  have hdegreeD:∀ gamma ∈ Delta,(selected gamma).natDegree ≤ 131071:=
    fun gamma hg=>hdegree gamma (hsub hg)
  have hagreementD:∀ gamma ∈ Delta,181373 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card:=
    fun gamma hg=>hagreement gamma (hsub hg)
  have hnoD:NoLargeSelectedPencil selected Delta 131071 80771:=
    noLargeSelectedPencil_mono selected Gamma Delta 131071 80771 hsub hno
  have hN:∀ F ∈ (Finset.univ:Finset (RegularIndex H)) \ U,
      (regularSeeds H selected Delta F).card ≤
        initialAHelperCap (regularCumulativeFlag H F):=by
    intro F hFN
    apply initialA_nonuniversal_count u0 u1 H hH hwide selected Delta
      hdegreeD hagreementD hnoD F
    exact (Finset.mem_sdiff.mp hFN).2
  have hreg:(∑ F:RegularIndex H,
      (regularSeeds H selected Delta F).card) ≤
        LocatorFixedConsumer6802.initialRegularCap:=by
    apply LocatorFixedConsumer6802.initial_A_regularSeeds_sum_le H selected Delta
      U phaseCap (fun F => initialAHelperCap (regularCumulativeFlag H F))
    · simpa only [H,phi,Delta,U] using hphase
    · exact hN
    · simpa only [H,U] using hledger
  exact LocatorFixedConsumer6802.wide_fixed_count_le H hH hbox selected Delta u0 u1
    hsolution hdegreeD hagreementD hnoD hreg

end
end ProximityPrize.SubmissionLower.LocatorFixedBridge6802
