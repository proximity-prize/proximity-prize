import ProximityPrize.SubmissionLower.HigherInitialArithmetic6810
import ProximityPrize.SubmissionLower.HigherAffineRateBridge6810
import ProximityPrize.SubmissionLower.HigherSelection6810
import ProximityPrize.SubmissionLower.HigherRouting6810
import ProximityPrize.SubmissionLower.HigherOrdinary6810
import ProximityPrize.SubmissionLower.HigherSingletonGeometry6810
import ProximityPrize.SubmissionLower.LowerGeometry

section InitialGeometry
namespace ProximityPrize.SubmissionLower.Lower80850.InitialSupports
open RCN130 RCN238 RCN275
-- Raw cumulative support caps for the common carrier and its A-universal factors.
def wideSupport : ResidualSupportParameters := ⟨37, 164, 8865, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
def wholeSupport : ResidualSupportParameters := ⟨34, 156, 8865, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
end ProximityPrize.SubmissionLower.Lower80850.InitialSupports
namespace ProximityPrize.SubmissionLower.Lower80850.InitialBridge

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN095 RCN100 RCN101 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN243 RCN259 RCN260 RCN266 RCN275 RCN319
open Selection LocatorFactorAggregate LocatorBatchProductRoute

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4

/-- Exact direct helper charge for one factor exiting at the A source. -/
def initialAHelperCap (p:FlagDegree):ℕ:=
  AsymmetricHelper.leftRegularCountCap (Lower80850.FactorSwitch.helperPair
    157823 156 34 (middle p) p.all (total p))

/-- Linear reconstruction of the independent A source. -/
def initialAMap (u0 u1:I → K):Caps.AKernel u0 u1 →ₗ[K] P4:=
  kernelReconstructLinear (K:=K) 20486222 131071 157823 34 113
    IRSProfile.domain u0 u1

/-- Factors universal on the current A source. -/
def initialAUniversalFactors (u0 u1:I → K) (H:P4):
    Finset (RegularIndex H):=
  universalFactors H (Finset.univ:Finset (RegularIndex H))
    (initialAMap u0 u1)

@[simp] theorem mem_initialAUniversalFactors
    (u0 u1:I → K) (H:P4) (F:RegularIndex H):
    F ∈ initialAUniversalFactors u0 u1 H ↔
      ∀ v:Caps.AKernel u0 u1,
        F.1 ∣ reconstruct K 20486222 131071 157823 34 v.1:=by
  simp only [initialAUniversalFactors,mem_universalFactors,Finset.mem_univ,
    true_and,initialAMap,kernelReconstructLinear_apply]

/-- The universal A factors divide every A row jointly. -/
theorem initialAUniversalProduct_dvd
    (u0 u1:I → K) (H:P4):
    ∀ v:Caps.AKernel u0 u1,
      regularProduct H (initialAUniversalFactors u0 u1 H) ∣
        reconstruct K 20486222 131071 157823 34 v.1:=by
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
    (hr:1 ≤ p.all) (hs:p.all ≤ 37)
    (hy:middle p ≤ 164) (ht:total p ≤ 8865):
    Lower80850.FactorSwitch.HelperPairGates
      157823 156 34 (middle p) p.all (total p):=by
  unfold Lower80850.FactorSwitch.HelperPairGates
  change 1 ≤ p.all ∧ middle p < 2130706433 ∧ p.all < 2130706433 ∧
    total p < 2130706433 ∧
    p.all*157823+total p*34 < 2130706433 ∧
    middle p*157823+total p*156 < 2130706433 ∧
    middle p*34+p.all*156 < 2130706433
  omega

/-- Every factor outside the A-universal set gets the direct coprime A
helper, with no minimum against its ordinary cost. -/
theorem initialA_nonuniversal_count
    (u0 u1:I → K) (H:P4) (hH:H ≠ 0)
    (hwide:ResidualSupportData InitialSupports.wideSupport H)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181294 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80850)
    (F:RegularIndex H) (hFU:F ∉ initialAUniversalFactors u0 u1 H):
    (regularSeeds H selected Gamma F).card ≤
      initialAHelperCap (regularCumulativeFlag H F):=by
  have hFsupport:=HigherOrdinary6810.factor_support H hH hwide F
  have hc:=originalCumulativeFlag_cumulative F.1
  have hs:(regularCumulativeFlag H F).all ≤ 37:=by
    simpa only [regularCumulativeFlag,hc.1,InitialSupports.wideSupport]
      using hFsupport.s_weight
  have hy:middle (regularCumulativeFlag H F) ≤ 164:=by
    simpa only [regularCumulativeFlag,middle,hc.2.1,
      InitialSupports.wideSupport] using hFsupport.ys_weight
  have ht:total (regularCumulativeFlag H F) ≤ 8865:=by
    simpa only [regularCumulativeFlag,total,hc.2.2,
      InitialSupports.wideSupport] using hFsupport.total_weight
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
  rcases Lower80850.FactorSwitch.divisor_or_helper_count
      20486222 157823 34 113 156 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      selected Gamma hdegree hagreement hno F
      (middle (regularCumulativeFlag H F)) (regularCumulativeFlag H F).all
      (total (regularCumulativeFlag H F)) hFY hFR hFZ
      (initialA_helper_gates (regularCumulativeFlag H F) hr hs hy ht) with
    hdiv | hcount
  · exact False.elim (hFU ((mem_initialAUniversalFactors u0 u1 H F).2 hdiv))
  · simpa only [initialAHelperCap] using hcount


theorem initialA_universal_singleBound
    (hreceipt : HigherAffineRateBridge6810.Receipt)
    (hthreshold : PhaseSemantics.ThresholdReceiptSound)
    (u0 u1:I → K) (H:P4) (hH:H ≠ 0)
    (hTotal:wt residualTotalWeights H ≤ 8865)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181294 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80850)
    (F:RegularIndex H) (hFU:F ∈ initialAUniversalFactors u0 u1 H):
    (regularSeeds H selected Gamma F).card ≤
      HigherAffineSingleton6810.cap
        (HigherAffineRateData6810.rate (regularCumulativeFlag H F).all (regularCumulativeFlag H F).yz)
        (regularCumulativeFlag H F).all (regularCumulativeFlag H F).zOnly:=by
  have hF:=RCN167.positiveRFactors_spec H F.1 F.2
  have hdivA:∀ v:Caps.AKernel u0 u1,
      F.1 ∣ reconstruct K 20486222 131071 157823 34 v.1:=
    (mem_initialAUniversalFactors u0 u1 H F).1 hFU
  have hAflag:=Caps.full_A_divisor_mem_box u0 u1 F.1
    hF.1.ne_zero hdivA
  have hAcaps:=(mem_flagGlobalCoefficientBox_iff F.1
    20486222 131071 157823 34 (by decide +kernel)).mp hAflag
  have hFt:wt residualTotalWeights F.1 ≤ 8865:=
    (weightedTotalDegree_le_of_dvd residualTotalWeights F.1 H hF.2.1 hH).trans
      hTotal
  have hFy:wt residualYSWeights F.1 ≤ 156:=
    Caps.common_A_ys_le u0 u1 F.1 hF.1.ne_zero hdivA
  have hFs:wt residualSWeights F.1 ≤ 34:=
    Caps.common_A_slope_le u0 u1 F.1 hF.1.ne_zero hdivA
  have hFflag:F.1 ∈ globalCoefficientBox K 20486222 131071 8865 34:=
    (mem_flagGlobalCoefficientBox_iff F.1
      20486222 131071 8865 34 (by decide +kernel)).mpr ⟨hFt,hFs,hAcaps.2.2⟩
  have hFbox:=flag_box_to_ordinary K 20486222 131071 8865 34 F.1 hFflag
  have hFsupport:ResidualSupportData InitialSupports.wholeSupport F.1:=
    ⟨hFs,hFy,hFt⟩
  let Fself:=LocatorCoprimeQuotient.regularIndexSelf H F
  have hc := originalCumulativeFlag_cumulative F.1
  have hr : 1 ≤ (regularCumulativeFlag H F).all := regularCumulativeFlag_positive H F
  have hs : (regularCumulativeFlag H F).all ≤ 34 := by
    simpa only [regularCumulativeFlag,hc.1] using hFs
  have hy : middle (regularCumulativeFlag H F) ≤ 156 := by
    simpa only [regularCumulativeFlag,middle,hc.2.1] using hFy
  have ht : total (regularCumulativeFlag H F) ≤ 8865 := by
    simpa only [regularCumulativeFlag,total,hc.2.2] using hFt
  have hy' : (regularCumulativeFlag H F).all+(regularCumulativeFlag H F).yz ≤ 156 := by
    simpa only [middle,Nat.add_comm] using hy
  have ht' : (regularCumulativeFlag H F).all+(regularCumulativeFlag H F).yz+
      (regularCumulativeFlag H F).zOnly ≤ 8865 := by
    simpa only [total,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ht
  have hbound := HigherSingletonGeometry6810.factor_count_le_affine 20486222
    InitialSupports.wholeSupport (by decide +kernel) (by decide +kernel)
    F.1 hF.1.ne_zero hFbox selected Gamma u0 u1 hdegree hagreement hno Fself
    hs hy ht hreceipt hthreshold
  simpa only [RCN140.regularSeeds,regularCumulativeFlag,Fself,
    LocatorCoprimeQuotient.regularIndexSelf_val] using hbound

end
end ProximityPrize.SubmissionLower.Lower80850.InitialBridge


namespace ProximityPrize.SubmissionLower.Lower80850.Initial
open RCN095 RCN260 LocatorFactorAggregate Lower80850.InitialBridge Lower80850.FactorSwitch
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem initialA_majorant (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 37)
    (hy : middle p ≤ 164) (ht : total p ≤ 8865) :
    InitialBridge.initialAHelperCap p ≤ initialAPotential.eval p := by
  change AsymmetricHelper.leftRegularCountCap
      (helperPair 157823 156 34 (middle p) p.all (total p)) ≤
    7710297192*total p+4147246020192*middle p+18653809146957*p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _
    42991289 9568183 2323888831 7710297192 4147246020192 18653809146957
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1+2*131071*middle p ≤ 42991289
    omega
  · change 131071*(2*p.all-1) ≤ 9568183
    omega
  · change 2*131071*total p+1 ≤ 2323888831
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]
end ProximityPrize.SubmissionLower.Lower80850.Initial


end InitialGeometry
