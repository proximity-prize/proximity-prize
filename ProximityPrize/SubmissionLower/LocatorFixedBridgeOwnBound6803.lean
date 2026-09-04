import ProximityPrize.SubmissionLower.LocatorFixedBridge6803
import ProximityPrize.SubmissionLower.LocatorCapsA6803
import ProximityPrize.SubmissionLower.LocatorFixedOwnBoundC26803

/-! The narrow own-bound half of the retuned initial-A bridge. -/

namespace ProximityPrize.SubmissionLower.LocatorFixedBridge6803

open ProximityPrize.Benchmark
open scoped Classical
open RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN174
  RCN180 RCN234 RCN238 RCN243 RCN266 RCN275
open LocatorFactorAggregate

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

/-- An A-universal factor has the narrow 68.03 own-bound even though the
whole selected gcd has the wide support. -/
theorem initialA_universal_ownBound
    (u0 u1 : I → K) (H : P4) (hH : H ≠ 0)
    (hTotal : wt residualTotalWeights H ≤ 6676)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181363 ≤
      ((Finset.univ : Finset I).filter fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80781)
    (F : RegularIndex H) (hFU : F ∈ initialAUniversalFactors u0 u1 H) :
    LocatorHybridCost.OwnBound (regularSeeds H selected Gamma F).card
      (regularCumulativeFlag H F) := by
  have hF := RCN167.positiveRFactors_spec H F.1 F.2
  have hdivA : ∀ v : AKernel u0 u1,
      F.1 ∣ reconstruct K 17773574 131071 130000 29 v.1 :=
    (mem_initialAUniversalFactors u0 u1 H F).1 hFU
  have hAflag := LocatorCapsA6803.full_A_divisor_mem_box u0 u1 F.1
    hF.1.ne_zero hdivA
  have hAcaps := (mem_flagGlobalCoefficientBox_iff F.1
    17773574 131071 130000 29 (by decide)).mp hAflag
  have hFt : wt residualTotalWeights F.1 ≤ 6676 :=
    (RCN081.weightedTotalDegree_le_of_dvd residualTotalWeights F.1 H
      hF.2.1 hH).trans hTotal
  have hFy : wt residualYSWeights F.1 ≤ 135 :=
    LocatorCapsA6803.common_A_ys_le u0 u1 F.1 hF.1.ne_zero hdivA
  have hFs : wt residualSWeights F.1 ≤ 29 :=
    LocatorCapsA6803.common_A_slope_le u0 u1 F.1 hF.1.ne_zero hdivA
  have hFflag : F.1 ∈
      RCN100.globalCoefficientBox K 17773574 131071 6676 29 :=
    (mem_flagGlobalCoefficientBox_iff F.1
      17773574 131071 6676 29 (by decide)).mpr
        ⟨hFt, hFs, hAcaps.2.2⟩
  have hFbox := RCN101.flag_box_to_ordinary K 17773574 131071 6676 29 F.1
    hFflag
  have hFsupport : ResidualSupportData narrowSupport F.1 :=
    ⟨hFs, hFy, hFt⟩
  let Fself := LocatorCoprimeQuotient.regularIndexSelf H F
  have hown := LocatorFixedOwnBoundC26803.regular_factor_own_bound
    (D := 17773574) (P := narrowSupport)
    (hDlow := by decide) (hDhigh := by decide)
    (hS := by decide) (hY := by decide) (hT := by decide)
    (Q := F.1) (hQ := hF.1.ne_zero) (hbox := hFbox)
    (HQ := hFsupport) (selected := selected) (Gamma := Gamma)
    (u0 := u0) (u1 := u1) (hdegree := by exact hdegree)
    (hagreement := by exact hagreement) (hno := by exact hno) (R := Fself)
    (hreal := LocatorHybridRealizeC26803.realizationC2)
  simpa only [RCN140.regularSeeds, regularCumulativeFlag, Fself,
    LocatorCoprimeQuotient.regularIndexSelf_val] using hown

end

end ProximityPrize.SubmissionLower.LocatorFixedBridge6803
