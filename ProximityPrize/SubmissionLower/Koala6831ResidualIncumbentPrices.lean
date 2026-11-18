import ProximityPrize.SubmissionLower.MergedInfra6815_14
import ProximityPrize.SubmissionLower.MergedInfra6815_6
import ProximityPrize.SubmissionLower.BoundaryTailGates
import ProximityPrize.SubmissionLower.LowerGeometry
import ProximityPrize.SubmissionLower.MergedInfra6815_10
import ProximityPrize.SubmissionLower.MergedInfra6815_10
import ProximityPrize.SubmissionLower.MergedInfra6815_18
import ProximityPrize.SubmissionLower.MergedInfra6815_10
import ProximityPrize.SubmissionLower.MergedInfra6815_10
import ProximityPrize.SubmissionLower.HFreeDir6813
import ProximityPrize.SubmissionLower.Koala6831ResidualPrices

namespace ProximityPrize.SubmissionLower.Koala6831Residual

open RCN095 RCN146 LocatorHybridCells

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem firstTail_eq_cellFirstTail (f : Envelope)
    (hr : 3 ≤ f.slope) (hy : f.slope + 2 ≤ f.middle) :
    firstTail f = cellFirstTail f.total f.middle f.slope := by
  unfold cellFirstTail cellSupport
  rw [Lower80788.FixedStage.tail_support_formula]
  change (⟨262144 * (f.total-f.middle), 1+262144*(f.middle-f.slope),
      262144*(f.slope-1)⟩ : FlagDegree) = _
  apply flag_ext <;> simp only [cellA, cellB, cellS, RCN327.w] <;> omega

theorem normalTail_zero_eq_cellNormal (f : Envelope) :
    normalTail 0 f = BoundaryTailProvider.cellNormal f.total f.middle f.slope := by
  simp only [normalTail, BoundaryTailProvider.cellNormal, BoundaryTailAlgebra.normalFlag,
    Nat.add_zero, Nat.sub_zero]
  apply flag_ext
  · exact congrArg (· * (f.total-f.middle)) (by decide)
  · exact congrArg₂ (fun a b : ℕ => a * (f.middle-f.slope) - b) (by decide) (by decide)
  · exact congrArg (· * (f.slope-1)) (by decide)

theorem movingFiber_eq_cellMovingFiber (f : Envelope)
    (hr : 3 ≤ f.slope) (hy : f.slope + 2 ≤ f.middle) :
    movingFiber f = cellMovingFiber f.total f.middle f.slope := by
  apply flag_ext <;>
    simp only [movingFiber, cellMovingFiber, RCN206.fiberFlag, cellA, cellB, cellS] <;>
    omega

theorem ordinaryMovingTail_eq_cellMovingCut (f : Envelope)
    (hr : 3 ≤ f.slope) (hy : f.slope + 2 ≤ f.middle) :
    ordinaryMovingTail f = cellMovingCut f.total f.middle f.slope := by
  change (⟨131074*(f.total-f.middle), 131074*(f.middle-f.slope),
      131074*f.slope-1⟩ : FlagDegree) = _
  apply flag_ext <;>
    simp only [cellMovingCut, cellRational, cellDirection,
      cellA, cellB, cellS, RCN206.directionFlag, RCN327.w, add_zOnly, add_yz, add_all] <;>
    omega

theorem rawChargeWithCorrections_original_eq_incumbent (f : Envelope) (left : FlagDegree)
    (hr : 3 ≤ f.slope) (hy : f.slope + 2 ≤ f.middle) :
    rawChargeWithCorrections TailCorrections.original f left =
      MovingFiberOrdinaryHigh6815.bound left f.total f.middle f.slope := by
  change flagMixed left (firstTail f) (normalTail 0 f) +
    65539 * flagMixed left (movingFiber f) (ordinaryMovingTail f) = _
  rw [firstTail_eq_cellFirstTail f hr hy, normalTail_zero_eq_cellNormal f,
    movingFiber_eq_cellMovingFiber f hr hy, ordinaryMovingTail_eq_cellMovingCut f hr hy]
  rfl

theorem identityRaw_eq_identityGraph (f : Envelope)
    (hr : 3 ≤ f.slope) (hy : f.slope + 2 ≤ f.middle) :
    identityRaw f = identityGraph f := by
  apply flag_ext <;> simp only [identityRaw, identityGraph] <;> omega

theorem identityCurveDegree_eq_identityGraph (f : Envelope) (left : FlagDegree)
    (hr : 3 ≤ f.slope) (hy : f.slope + 2 ≤ f.middle) :
    identityCurveDegree left (cellA f.total f.middle) (cellB f.middle f.slope) (cellS f.slope)
        RCN327.w =
      left.zOnly * (identityGraph f).zOnly + left.yz * (identityGraph f).yz +
        left.all * (identityGraph f).all := by
  have hz : 393219 + 262146 * cellS f.slope = (identityGraph f).zOnly := by
    simp only [identityGraph, cellS]
    omega
  have hv : 786438 + 524292 * cellS f.slope = (identityGraph f).yz := by
    simp only [identityGraph, cellS]
    omega
  have ha : 1048586 + 262146 * cellA f.total f.middle + 524292 * cellB f.middle f.slope +
      524292 * cellS f.slope = (identityGraph f).all := by
    simp only [identityGraph, cellA, cellB, cellS]
    omega
  change identityCurveDegree left (cellA f.total f.middle) (cellB f.middle f.slope)
    (cellS f.slope) Lower80788.HybridIdentityC2.w = _
  rw [Lower80788.HybridIdentityC2.identityDegree_linear, hz, hv, ha]

theorem identityCurveDegree_eq_identityRaw (f : Envelope) (left : FlagDegree)
    (hr : 3 ≤ f.slope) (hy : f.slope + 2 ≤ f.middle) :
    identityCurveDegree left (cellA f.total f.middle) (cellB f.middle f.slope) (cellS f.slope)
        RCN327.w =
      left.zOnly * (identityRaw f).zOnly + left.yz * (identityRaw f).yz +
        left.all * (identityRaw f).all := by
  rw [identityRaw_eq_identityGraph f hr hy]
  exact identityCurveDegree_eq_identityGraph f left hr hy

theorem incumbent_raw_identity_absorbed (f : Envelope) (left : FlagDegree)
    (hr : 3 ≤ f.slope) (hy : f.slope + 2 ≤ f.middle)
    (hgate : rawGatesWithCorrections TailCorrections.original f = true) :
    131073 * 81067 *
        identityCurveDegree left (cellA f.total f.middle) (cellB f.middle f.slope)
          (cellS f.slope) RCN327.w ≤
      50007 * MovingFiberOrdinaryHigh6815.bound left f.total f.middle f.slope := by
  simp only [rawGatesWithCorrections, Bool.and_eq_true] at hgate
  have haxis := List.all_eq_true.mp hgate.2
  have hZ := of_decide_eq_true (haxis (0 : Fin 3) (by simp))
  have hYZ := of_decide_eq_true (haxis (1 : Fin 3) (by simp))
  have hFull := of_decide_eq_true (haxis (2 : Fin 3) (by simp))
  let price := rawChargeWithCorrections TailCorrections.original f
  change 131073 * 81067 * (identityRaw f).zOnly ≤ 50007 * price unitZFlag at hZ
  change 131073 * 81067 * (identityRaw f).yz ≤ 50007 * price unitYZFlag at hYZ
  change 131073 * 81067 * (identityRaw f).all ≤ 50007 * price unitAllFlag at hFull
  have hlin : price left =
      left.zOnly * price unitZFlag + left.yz * price unitYZFlag +
        left.all * price unitAllFlag := by
    simp only [price, rawChargeWithCorrections, flagMixed, unitZFlag, unitYZFlag, unitAllFlag]
    ring
  rw [identityCurveDegree_eq_identityRaw f left hr hy,
    ← rawChargeWithCorrections_original_eq_incumbent f left hr hy]
  change 131073 * 81067 * _ ≤ 50007 * price left
  calc
    _ = left.zOnly * (131073*81067*(identityRaw f).zOnly) +
        left.yz * (131073*81067*(identityRaw f).yz) +
        left.all * (131073*81067*(identityRaw f).all) := by ring
    _ ≤ left.zOnly * (50007*price unitZFlag) + left.yz * (50007*price unitYZFlag) +
        left.all * (50007*price unitAllFlag) :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hZ) (Nat.mul_le_mul_left _ hYZ))
        (Nat.mul_le_mul_left _ hFull)
    _ = 50007 * price left := by rw [hlin]; ring

theorem rawGates_of_jetGates_small (cuts : TailCorrections) (f : Envelope)
    (cfg : Fin 3 → JetProfile) (hgate : jetGatesWithCorrections cuts f cfg = true) :
    rawGatesWithCorrections cuts ((⟨f.slope, f.middle, jetSourceCap cfg⟩ : Envelope).pad 0) =
      true := by
  simp only [jetGatesWithCorrections, Bool.and_eq_true] at hgate
  tauto

end ProximityPrize.SubmissionLower.Koala6831Residual

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
