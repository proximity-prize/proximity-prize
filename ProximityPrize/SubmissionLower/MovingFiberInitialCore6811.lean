import ProximityPrize.SubmissionLower.MovingFiberInitialArithmetic6811
import ProximityPrize.SubmissionLower.MovingFiberSelection6811
import ProximityPrize.SubmissionLower.MovingFiberRouting6811
import ProximityPrize.SubmissionLower.MovingFiberOrdinary6811
import ProximityPrize.SubmissionLower.LowerGeometry

section InitialGeometry
namespace ProximityPrize.SubmissionLower.Lower80860.InitialSupports
open RCN130 RCN238 RCN275
-- Raw cumulative support caps for the common carrier and its A-universal factors.
def wideSupport : ResidualSupportParameters := ⟨40, 185, 9678, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
def wholeSupport : ResidualSupportParameters := ⟨35, 163, 9678, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
end ProximityPrize.SubmissionLower.Lower80860.InitialSupports
namespace ProximityPrize.SubmissionLower.Lower80860.InitialBridge

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
  AsymmetricHelper.leftRegularCountCap (Lower80860.FactorSwitch.helperPair
    380088 163 35 (middle p) p.all (total p))

/-- Linear reconstruction of the independent A source. -/
def initialAMap (u0 u1:I → K):Caps.AKernel u0 u1 →ₗ[K] P4:=
  kernelReconstructLinear (K:=K) 21390450 131071 380088 35 118
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
        F.1 ∣ reconstruct K 21390450 131071 380088 35 v.1:=by
  simp only [initialAUniversalFactors,mem_universalFactors,Finset.mem_univ,
    true_and,initialAMap,kernelReconstructLinear_apply]

/-- The universal A factors divide every A row jointly. -/
theorem initialAUniversalProduct_dvd
    (u0 u1:I → K) (H:P4):
    ∀ v:Caps.AKernel u0 u1,
      regularProduct H (initialAUniversalFactors u0 u1 H) ∣
        reconstruct K 21390450 131071 380088 35 v.1:=by
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
    (hr:1 ≤ p.all) (hs:p.all ≤ 40)
    (hy:middle p ≤ 185) (ht:total p ≤ 9678):
    Lower80860.FactorSwitch.HelperPairGates
      380088 163 35 (middle p) p.all (total p):=by
  unfold Lower80860.FactorSwitch.HelperPairGates
  change 1 ≤ p.all ∧ middle p < 2130706433 ∧ p.all < 2130706433 ∧
    total p < 2130706433 ∧
    p.all*380088+total p*35 < 2130706433 ∧
    middle p*380088+total p*163 < 2130706433 ∧
    middle p*35+p.all*163 < 2130706433
  omega

/-- Every factor outside the A-universal set gets the direct coprime A
helper, with no minimum against its ordinary cost. -/
theorem initialA_nonuniversal_count
    (u0 u1:I → K) (H:P4) (hH:H ≠ 0)
    (hwide:ResidualSupportData InitialSupports.wideSupport H)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181275 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80869)
    (F:RegularIndex H) (hFU:F ∉ initialAUniversalFactors u0 u1 H):
    (regularSeeds H selected Gamma F).card ≤
      initialAHelperCap (regularCumulativeFlag H F):=by
  have hFsupport:=MovingFiberOrdinary6811.factor_support H hH hwide F
  have hc:=originalCumulativeFlag_cumulative F.1
  have hs:(regularCumulativeFlag H F).all ≤ 40:=by
    simpa only [regularCumulativeFlag,hc.1,InitialSupports.wideSupport]
      using hFsupport.s_weight
  have hy:middle (regularCumulativeFlag H F) ≤ 185:=by
    simpa only [regularCumulativeFlag,middle,hc.2.1,
      InitialSupports.wideSupport] using hFsupport.ys_weight
  have ht:total (regularCumulativeFlag H F) ≤ 9678:=by
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
  rcases Lower80860.FactorSwitch.divisor_or_helper_count
      21390450 380088 35 118 163 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      selected Gamma hdegree hagreement hno F
      (middle (regularCumulativeFlag H F)) (regularCumulativeFlag H F).all
      (total (regularCumulativeFlag H F)) hFY hFR hFZ
      (initialA_helper_gates (regularCumulativeFlag H F) hr hs hy ht) with
    hdiv | hcount
  · exact False.elim (hFU ((mem_initialAUniversalFactors u0 u1 H F).2 hdiv))
  · simpa only [initialAHelperCap] using hcount



end
end ProximityPrize.SubmissionLower.Lower80860.InitialBridge


namespace ProximityPrize.SubmissionLower.Lower80860.Initial
open RCN095 RCN260 LocatorFactorAggregate Lower80860.InitialBridge Lower80860.FactorSwitch
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem initialA_majorant (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 40)
    (hy : middle p ≤ 185) (ht : total p ≤ 9678) :
    InitialBridge.initialAHelperCap p ≤ initialAPotential.eval p := by
  change AsymmetricHelper.leftRegularCountCap
      (helperPair 380088 163 35 (middle p) p.all (total p)) ≤
    8838030555*total p+10507113500843*middle p+49204411286684*p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _
    48496271 10354609 2537010277 8838030555 10507113500843 49204411286684
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1+2*131071*middle p ≤ 48496271
    omega
  · change 131071*(2*p.all-1) ≤ 10354609
    omega
  · change 2*131071*total p+1 ≤ 2537010277
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]
end ProximityPrize.SubmissionLower.Lower80860.Initial


end InitialGeometry
