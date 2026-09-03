import ProximityPrize.SubmissionLower.LocatorFixedConsumer
import ProximityPrize.SubmissionLower.LocatorFixedOwnBound
import ProximityPrize.SubmissionLower.LocatorSelectedCaps
import ProximityPrize.SubmissionLower.LocatorBatchProductRoute
import ProximityPrize.SubmissionLower.LocatorGenericHelperFactorSwitch
import ProximityPrize.SubmissionLower.LocatorCover

/-!
# Initial A-source bridge for the wide selected gcd

The selected TCap/B pair only puts its gcd in the wide box
`(total,ys,slope)=(5964,153,33)`.  Split its regular factors on the independent
A kernel.  Nonuniversal factors get the direct `pairCost(F,A)` bound;
universal factors inherit A's narrow `(ys,slope)=(127,28)` caps.
-/

namespace ProximityPrize.SubmissionLower.LocatorFixedBridge

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN095 RCN100 RCN101 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN243 RCN259 RCN260 RCN266 RCN275 RCN319
open LocatorSelection LocatorFactorAggregate LocatorBatchProductRoute

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4

/-- Exact direct helper charge for one factor exiting at the A source. -/
def initialAHelperCap (p:FlagDegree):ℕ:=
  (LocatorGenericHelperFactorSwitch.helperPair
    130000 127 28 (middle p) p.all (total p)).regularCountCap

/-- Linear reconstruction of the independent A source. -/
def initialAMap (u0 u1:I → K):LocatorCaps.AKernel u0 u1 →ₗ[K] P4:=
  kernelReconstructLinear (K:=K) 16688064 131071 130000 28 92
    IRSProfile.domain u0 u1

/-- Factors universal on the current A source. -/
def initialAUniversalFactors (u0 u1:I → K) (H:P4):
    Finset (RegularIndex H):=
  universalFactors H (Finset.univ:Finset (RegularIndex H))
    (initialAMap u0 u1)

@[simp] theorem mem_initialAUniversalFactors
    (u0 u1:I → K) (H:P4) (F:RegularIndex H):
    F ∈ initialAUniversalFactors u0 u1 H ↔
      ∀ v:LocatorCaps.AKernel u0 u1,
        F.1 ∣ reconstruct K 16688064 131071 130000 28 v.1:=by
  simp only [initialAUniversalFactors,mem_universalFactors,Finset.mem_univ,
    true_and,initialAMap,kernelReconstructLinear_apply]

/-- The universal A factors divide every A row jointly. -/
theorem initialAUniversalProduct_dvd
    (u0 u1:I → K) (H:P4):
    ∀ v:LocatorCaps.AKernel u0 u1,
      regularProduct H (initialAUniversalFactors u0 u1 H) ∣
        reconstruct K 16688064 131071 130000 28 v.1:=by
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
    (hr:1 ≤ p.all) (hs:p.all ≤ 33)
    (hy:middle p ≤ 153) (ht:total p ≤ 5964):
    LocatorGenericHelperFactorSwitch.HelperPairGates
      130000 127 28 (middle p) p.all (total p):=by
  unfold LocatorGenericHelperFactorSwitch.HelperPairGates
  change 1 ≤ p.all ∧ middle p < 2130706433 ∧ p.all < 2130706433 ∧
    total p < 2130706433 ∧
    p.all*130000+total p*28 < 2130706433 ∧
    middle p*130000+total p*127 < 2130706433 ∧
    middle p*28+p.all*127 < 2130706433
  omega

/-- Every factor outside the A-universal set gets the direct coprime A
helper, with no minimum against its ordinary cost. -/
theorem initialA_nonuniversal_count
    (u0 u1:I → K) (H:P4) (hH:H ≠ 0)
    (hwide:ResidualSupportData LocatorFixedConsumer.wideSupport H)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181392 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80752)
    (F:RegularIndex H) (hFU:F ∉ initialAUniversalFactors u0 u1 H):
    (regularSeeds H selected Gamma F).card ≤
      initialAHelperCap (regularCumulativeFlag H F):=by
  have hFsupport:=LocatorFixed.factor_support H hH hwide F
  have hc:=originalCumulativeFlag_cumulative F.1
  have hs:(regularCumulativeFlag H F).all ≤ 33:=by
    simpa only [regularCumulativeFlag,hc.1,LocatorFixedConsumer.wideSupport]
      using hFsupport.s_weight
  have hy:middle (regularCumulativeFlag H F) ≤ 153:=by
    simpa only [regularCumulativeFlag,middle,hc.2.1,
      LocatorFixedConsumer.wideSupport] using hFsupport.ys_weight
  have ht:total (regularCumulativeFlag H F) ≤ 5964:=by
    simpa only [regularCumulativeFlag,total,hc.2.2,
      LocatorFixedConsumer.wideSupport] using hFsupport.total_weight
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
  rcases LocatorGenericHelperFactorSwitch.divisor_or_helper_count
      16688064 130000 28 92 127 (by decide) (by decide) (by decide)
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
    (hTotal:wt residualTotalWeights H ≤ 5964)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181392 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80752)
    (F:RegularIndex H) (hFU:F ∈ initialAUniversalFactors u0 u1 H):
    LocatorHybridCost.OwnBound (regularSeeds H selected Gamma F).card
      (regularCumulativeFlag H F):=by
  have hF:=RCN167.positiveRFactors_spec H F.1 F.2
  have hdivA:∀ v:LocatorCaps.AKernel u0 u1,
      F.1 ∣ reconstruct K 16688064 131071 130000 28 v.1:=
    (mem_initialAUniversalFactors u0 u1 H F).1 hFU
  have hAflag:=LocatorCaps.full_A_divisor_mem_box u0 u1 F.1
    hF.1.ne_zero hdivA
  have hAcaps:=(mem_flagGlobalCoefficientBox_iff F.1
    16688064 131071 130000 28 (by decide)).mp hAflag
  have hFt:wt residualTotalWeights F.1 ≤ 5964:=
    (weightedTotalDegree_le_of_dvd residualTotalWeights F.1 H hF.2.1 hH).trans
      hTotal
  have hFy:wt residualYSWeights F.1 ≤ 127:=
    LocatorCaps.common_A_ys_le u0 u1 F.1 hF.1.ne_zero hdivA
  have hFs:wt residualSWeights F.1 ≤ 28:=
    LocatorCaps.common_A_slope_le u0 u1 F.1 hF.1.ne_zero hdivA
  have hFflag:F.1 ∈ globalCoefficientBox K 16688064 131071 5964 28:=
    (mem_flagGlobalCoefficientBox_iff F.1
      16688064 131071 5964 28 (by decide)).mpr ⟨hFt,hFs,hAcaps.2.2⟩
  have hFbox:=flag_box_to_ordinary K 16688064 131071 5964 28 F.1 hFflag
  have hFsupport:ResidualSupportData LocatorFixedConsumer.wholeSupport F.1:=
    ⟨hFs,hFy,hFt⟩
  let Fself:=LocatorCoprimeQuotient.regularIndexSelf H F
  have hown:=LocatorFixedOwnBound.regular_factor_own_bound 16688064
    LocatorFixedConsumer.wholeSupport (by decide) (by decide)
    (by decide) (by decide) (by decide)
    F.1 hF.1.ne_zero hFbox hFsupport selected Gamma u0 u1
    hdegree hagreement hno Fself LocatorHybridRealize.realization
  simpa only [RCN140.regularSeeds,regularCumulativeFlag,Fself,
    LocatorCoprimeQuotient.regularIndexSelf_val] using hown

/-! ## Wide selected-gcd bridge with a replaceable numerical receipt -/

/-- Algebraic bridge to the phase-potential certificate.  `hphase` bounds
the A-universal child; `hledger` combines it with the exact direct-A charges
of all factors that exit at this first split. -/
theorem gcd_fixed_count_le_of_initial_phase
    (u0 u1:I → K) (S:SelectedPair u0 u1)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181392 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80752)
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
          LocatorFixedConsumer.initialRegularCap):
    (LocatorCover.fixed
      (fun gamma=>(specialization K (selected gamma) gamma).toRingHom)
      Gamma S.QA S.QB).card ≤
      LocatorFixedConsumer.initialRegularCap+
        LocatorArithmetic.fixedSingularCap:=by
  classical
  let H:P4:=gcd12 S.QA S.QB
  let phi:K → P4 →+* Polynomial K:=
    fun gamma=>(specialization K (selected gamma) gamma).toRingHom
  let Delta:Finset K:=LocatorCover.fixed phi Gamma S.QA S.QB
  let U:=initialAUniversalFactors u0 u1 H
  have hH:H ≠ 0:=gcd_ne_zero_of_left S.QA_ne
  have hBflag:H ∈ globalCoefficientBox K 20134512 131071 10381 33:=
    LocatorCaps.full_B_divisor_mem_box u0 u1 H hH S.common_divides_B
  have hBcaps:=(mem_flagGlobalCoefficientBox_iff H
    20134512 131071 10381 33 (by decide)).mp hBflag
  have hT:wt residualTotalWeights H ≤ 5964:=S.common_total_le
  have hYS:wt residualYSWeights H ≤ 153:=S.common_ys_le
  have hS:wt residualSWeights H ≤ 33:=S.common_slope_le
  have hflag:H ∈ globalCoefficientBox K 20134512 131071 5964 33:=
    (mem_flagGlobalCoefficientBox_iff H
      20134512 131071 5964 33 (by decide)).mpr ⟨hT,hS,hBcaps.2.2⟩
  have hbox:=flag_box_to_ordinary K 20134512 131071 5964 33 H hflag
  have hwide:ResidualSupportData LocatorFixedConsumer.wideSupport H:=
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
  have hagreementD:∀ gamma ∈ Delta,181392 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card:=
    fun gamma hg=>hagreement gamma (hsub hg)
  have hnoD:NoLargeSelectedPencil selected Delta 131071 80752:=
    noLargeSelectedPencil_mono selected Gamma Delta 131071 80752 hsub hno
  have hN:∀ F ∈ (Finset.univ:Finset (RegularIndex H)) \ U,
      (regularSeeds H selected Delta F).card ≤
        initialAHelperCap (regularCumulativeFlag H F):=by
    intro F hFN
    apply initialA_nonuniversal_count u0 u1 H hH hwide selected Delta
      hdegreeD hagreementD hnoD F
    exact (Finset.mem_sdiff.mp hFN).2
  have hreg:(∑ F:RegularIndex H,
      (regularSeeds H selected Delta F).card) ≤
        LocatorFixedConsumer.initialRegularCap:=by
    apply LocatorFixedConsumer.initial_A_regularSeeds_sum_le H selected Delta
      U phaseCap (fun F => initialAHelperCap (regularCumulativeFlag H F))
    · simpa only [H,phi,Delta,U] using hphase
    · exact hN
    · simpa only [H,U] using hledger
  exact LocatorFixedConsumer.wide_fixed_count_le H hH hbox selected Delta u0 u1
    hsolution hdegreeD hagreementD hnoD hreg

end
end ProximityPrize.SubmissionLower.LocatorFixedBridge
