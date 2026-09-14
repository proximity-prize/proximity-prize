import ProximityPrize.SubmissionLower.AffineSingleBridge6808
import ProximityPrize.SubmissionLower.BoundaryTailSelection6808
import ProximityPrize.SubmissionLower.BoundaryTailRouting6808
import ProximityPrize.SubmissionLower.BoundaryTailOrdinary6808
import ProximityPrize.SubmissionLower.AffineSingletonGeometry6808
import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.Lower80840.Initial
open scoped BigOperators
open RCN095 LocatorFactorAggregate
open LocatorPhase6800Oracle (Potential rawFlag rawFlag_all rawFlag_middle rawFlag_total
  sumFlag sumFlag_all sumFlag_middle sumFlag_total)
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def initialAPotential : Potential := ⟨8020669608, 6658181645698, 30779966292966⟩
def initialAComplement (p : FlagDegree) : ℕ :=
    let t := 8483 - total p
    let y := 178 - middle p
    let r := 39 - p.all
  let nr := min t (min y r)
  let t' := t - nr
  let y' := y - nr
  let nv := min t' y'
  initialAPotential.eval (rawFlag nr nv (t' - nv))

/-- The greedy complement is maximal for the A potential among all raw flags
that can be added to `p` inside the wide box. -/
theorem initialAPotential_le_complement (p n : FlagDegree)
    (ht : total p + total n ≤ 8483)
    (hy : middle p + middle n ≤ 178)
    (hr : p.all + n.all ≤ 39) :
    initialAPotential.eval n ≤ initialAComplement p := by
  have hnpY : n.all ≤ middle n := by simp [middle]
  have hnpT : middle n ≤ total n := by simp [middle, total]
  have hppY : p.all ≤ middle p := by simp [middle]
  have hppT : middle p ≤ total p := by simp [middle, total]
  simp only [initialAComplement, Potential.eval, initialAPotential,
    rawFlag_total, rawFlag_middle, rawFlag_all]
  simp only [Nat.min_def]
  split_ifs <;> omega
theorem sum_initialAPotential_eval {ι : Type} [DecidableEq ι] (s : Finset ι)
    (p : ι → FlagDegree) :
    (∑ i ∈ s, initialAPotential.eval (p i)) =
      initialAPotential.eval (sumFlag s p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sumFlag, Potential.eval, total, middle]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, ih]
      simp [sumFlag, Potential.eval, total, middle, hi]
      ring

/-- Aggregate direct-A helper ledger for the factors that leave the initial
split.  The exact greedy complement avoids the seven-trillion loss of three
independent cumulative-coordinate remainders. -/
theorem initialA_helpers_sum_le_complement
    {ι : Type} [DecidableEq ι] (s : Finset ι) (p : ι → FlagDegree)
    (helper : ι → ℕ)
    (universal : FlagDegree)
    (hhelper : ∀ i ∈ s, helper i ≤ initialAPotential.eval (p i))
    (ht : total universal + ∑ i ∈ s, total (p i) ≤ 8483)
    (hy : middle universal + ∑ i ∈ s, middle (p i) ≤ 178)
    (hr : universal.all + ∑ i ∈ s, (p i).all ≤ 39) :
    (∑ i ∈ s, helper i) ≤ initialAComplement universal := by
  calc
    (∑ i ∈ s, helper i) ≤ ∑ i ∈ s, initialAPotential.eval (p i) :=
      Finset.sum_le_sum (fun i hi => hhelper i hi)
    _ = initialAPotential.eval (sumFlag s p) := sum_initialAPotential_eval s p
    _ ≤ initialAComplement universal := by
      apply initialAPotential_le_complement
      · simpa only [sumFlag_total] using ht
      · simpa only [sumFlag_middle] using hy
      · simpa only [sumFlag_all] using hr


end ProximityPrize.SubmissionLower.Lower80840.Initial

section InitialGeometry
namespace ProximityPrize.SubmissionLower.Lower80840.InitialSupports
open RCN130 RCN238 RCN275
-- Raw cumulative support caps for the common carrier and its A-universal factors.
def wideSupport : ResidualSupportParameters := ⟨39, 178, 8483, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
def wholeSupport : ResidualSupportParameters := ⟨33, 152, 8483, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
end ProximityPrize.SubmissionLower.Lower80840.InitialSupports
namespace ProximityPrize.SubmissionLower.Lower80840.InitialBridge

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
  AsymmetricHelper.leftRegularCountCap (Lower80840.FactorSwitch.helperPair
    245562 152 33 (middle p) p.all (total p))

/-- Linear reconstruction of the independent A source. -/
def initialAMap (u0 u1:I → K):Caps.AKernel u0 u1 →ₗ[K] P4:=
  kernelReconstructLinear (K:=K) 19943440 131071 245562 33 110
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
        F.1 ∣ reconstruct K 19943440 131071 245562 33 v.1:=by
  simp only [initialAUniversalFactors,mem_universalFactors,Finset.mem_univ,
    true_and,initialAMap,kernelReconstructLinear_apply]

/-- The universal A factors divide every A row jointly. -/
theorem initialAUniversalProduct_dvd
    (u0 u1:I → K) (H:P4):
    ∀ v:Caps.AKernel u0 u1,
      regularProduct H (initialAUniversalFactors u0 u1 H) ∣
        reconstruct K 19943440 131071 245562 33 v.1:=by
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
    (hr:1 ≤ p.all) (hs:p.all ≤ 39)
    (hy:middle p ≤ 178) (ht:total p ≤ 8483):
    Lower80840.FactorSwitch.HelperPairGates
      245562 152 33 (middle p) p.all (total p):=by
  unfold Lower80840.FactorSwitch.HelperPairGates
  change 1 ≤ p.all ∧ middle p < 2130706433 ∧ p.all < 2130706433 ∧
    total p < 2130706433 ∧
    p.all*245562+total p*33 < 2130706433 ∧
    middle p*245562+total p*152 < 2130706433 ∧
    middle p*33+p.all*152 < 2130706433
  omega

/-- Every factor outside the A-universal set gets the direct coprime A
helper, with no minimum against its ordinary cost. -/
theorem initialA_nonuniversal_count
    (u0 u1:I → K) (H:P4) (hH:H ≠ 0)
    (hwide:ResidualSupportData InitialSupports.wideSupport H)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181304 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80840)
    (F:RegularIndex H) (hFU:F ∉ initialAUniversalFactors u0 u1 H):
    (regularSeeds H selected Gamma F).card ≤
      initialAHelperCap (regularCumulativeFlag H F):=by
  have hFsupport:=BoundaryTailOrdinary6808.factor_support H hH hwide F
  have hc:=originalCumulativeFlag_cumulative F.1
  have hs:(regularCumulativeFlag H F).all ≤ 39:=by
    simpa only [regularCumulativeFlag,hc.1,InitialSupports.wideSupport]
      using hFsupport.s_weight
  have hy:middle (regularCumulativeFlag H F) ≤ 178:=by
    simpa only [regularCumulativeFlag,middle,hc.2.1,
      InitialSupports.wideSupport] using hFsupport.ys_weight
  have ht:total (regularCumulativeFlag H F) ≤ 8483:=by
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
  rcases Lower80840.FactorSwitch.divisor_or_helper_count
      19943440 245562 33 110 152 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      selected Gamma hdegree hagreement hno F
      (middle (regularCumulativeFlag H F)) (regularCumulativeFlag H F).all
      (total (regularCumulativeFlag H F)) hFY hFR hFZ
      (initialA_helper_gates (regularCumulativeFlag H F) hr hs hy ht) with
    hdiv | hcount
  · exact False.elim (hFU ((mem_initialAUniversalFactors u0 u1 H F).2 hdiv))
  · simpa only [initialAHelperCap] using hcount


theorem initialA_universal_singleBound
    (hreceipt : AffineSingleBridge6808.Receipt)
    (hthreshold : PhaseSemantics.ThresholdReceiptSound)
    (u0 u1:I → K) (H:P4) (hH:H ≠ 0)
    (hTotal:wt residualTotalWeights H ≤ 8483)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181304 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80840)
    (F:RegularIndex H) (hFU:F ∈ initialAUniversalFactors u0 u1 H):
    (regularSeeds H selected Gamma F).card ≤
      AffineSingleton6808.cap
        (AffineRateData6808.rate (regularCumulativeFlag H F).all (regularCumulativeFlag H F).yz)
        (regularCumulativeFlag H F).all (regularCumulativeFlag H F).zOnly:=by
  have hF:=RCN167.positiveRFactors_spec H F.1 F.2
  have hdivA:∀ v:Caps.AKernel u0 u1,
      F.1 ∣ reconstruct K 19943440 131071 245562 33 v.1:=
    (mem_initialAUniversalFactors u0 u1 H F).1 hFU
  have hAflag:=Caps.full_A_divisor_mem_box u0 u1 F.1
    hF.1.ne_zero hdivA
  have hAcaps:=(mem_flagGlobalCoefficientBox_iff F.1
    19943440 131071 245562 33 (by decide +kernel)).mp hAflag
  have hFt:wt residualTotalWeights F.1 ≤ 8483:=
    (weightedTotalDegree_le_of_dvd residualTotalWeights F.1 H hF.2.1 hH).trans
      hTotal
  have hFy:wt residualYSWeights F.1 ≤ 152:=
    Caps.common_A_ys_le u0 u1 F.1 hF.1.ne_zero hdivA
  have hFs:wt residualSWeights F.1 ≤ 33:=
    Caps.common_A_slope_le u0 u1 F.1 hF.1.ne_zero hdivA
  have hFflag:F.1 ∈ globalCoefficientBox K 19943440 131071 8483 33:=
    (mem_flagGlobalCoefficientBox_iff F.1
      19943440 131071 8483 33 (by decide +kernel)).mpr ⟨hFt,hFs,hAcaps.2.2⟩
  have hFbox:=flag_box_to_ordinary K 19943440 131071 8483 33 F.1 hFflag
  have hFsupport:ResidualSupportData InitialSupports.wholeSupport F.1:=
    ⟨hFs,hFy,hFt⟩
  let Fself:=LocatorCoprimeQuotient.regularIndexSelf H F
  have hc := originalCumulativeFlag_cumulative F.1
  have hr : 1 ≤ (regularCumulativeFlag H F).all := regularCumulativeFlag_positive H F
  have hs : (regularCumulativeFlag H F).all ≤ 33 := by
    simpa only [regularCumulativeFlag,hc.1] using hFs
  have hy : middle (regularCumulativeFlag H F) ≤ 152 := by
    simpa only [regularCumulativeFlag,middle,hc.2.1] using hFy
  have ht : total (regularCumulativeFlag H F) ≤ 8483 := by
    simpa only [regularCumulativeFlag,total,hc.2.2] using hFt
  have hy' : (regularCumulativeFlag H F).all+(regularCumulativeFlag H F).yz ≤ 152 := by
    simpa only [middle,Nat.add_comm] using hy
  have ht' : (regularCumulativeFlag H F).all+(regularCumulativeFlag H F).yz+
      (regularCumulativeFlag H F).zOnly ≤ 8483 := by
    simpa only [total,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ht
  apply AffineSingleBridge6808.count_le_affine _ _ _ _ hr hs hy' ht'
    (hreceipt.single _ _ hr hs hy') (hthreshold _ _ hr hs hy')
  · intro hSafe
    have hSafeSelf : BoundaryTailGates6808.Safe (regularCumulativeFlag F.1 Fself).all
        (middle (regularCumulativeFlag F.1 Fself)) := by
      simpa only [middle,Nat.add_comm,regularCumulativeFlag,Fself,
        LocatorCoprimeQuotient.regularIndexSelf_val] using hSafe
    have hraw := BoundaryTailOrdinary6808.regular_factor_count_raw 19943440
      InitialSupports.wholeSupport (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      F.1 hF.1.ne_zero hFbox hFsupport selected Gamma u0 u1
      hdegree hagreement hno Fself hSafeSelf
    simpa only [BoundaryTailShape6808.cost,LocatorPhase6800Oracle.rawFlag,
      RCN140.regularSeeds,regularCumulativeFlag,Fself,
      LocatorCoprimeQuotient.regularIndexSelf_val] using hraw
  · intro ha
    simp only [AffineSingleton6808.Active,if_neg (by decide : ¬(1:ℕ)=0),if_pos] at ha
    have hroot := AffineSingletonGeometry6808.root_count 19943440
      InitialSupports.wholeSupport (by decide +kernel) (by decide +kernel)
      F.1 hF.1.ne_zero hFbox selected Gamma u0 u1 hdegree hagreement hno Fself
      ha.2.1 (by simpa only [middle,Nat.add_comm,regularCumulativeFlag,Fself,
        LocatorCoprimeQuotient.regularIndexSelf_val] using ha.2.2.2.2.2.1)
      (by simpa only [total,Nat.add_comm,Nat.add_assoc,Nat.add_left_comm,
        regularCumulativeFlag,Fself,LocatorCoprimeQuotient.regularIndexSelf_val]
        using ha.2.2.2.2.2.2)
      ⟨ha.1,ha.2.2.1,ha.2.2.2.1,ha.2.2.2.2.1⟩
    simpa only [RCN140.regularSeeds,regularCumulativeFlag,Fself,
      LocatorCoprimeQuotient.regularIndexSelf_val] using hroot
  · intro j hj hroute
    have hout := AffineSingletonGeometry6808.source_count (TenPhase.sound j) u0 u1
      (TenPhase.kernel u0 u1 j) H selected Gamma hdegree hagreement hno F hs hy ht hroute
    rw [PhaseSemantics.potential_eq j hj] at hout
    exact hout

end
end ProximityPrize.SubmissionLower.Lower80840.InitialBridge


namespace ProximityPrize.SubmissionLower.Lower80840.Initial
open RCN095 RCN260 LocatorFactorAggregate Lower80840.InitialBridge Lower80840.FactorSwitch
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem initialA_majorant (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 39)
    (hy : middle p ≤ 178) (ht : total p ≤ 8483) :
    InitialBridge.initialAHelperCap p ≤ initialAPotential.eval p := by
  change AsymmetricHelper.leftRegularCountCap
      (helperPair 245562 152 33 (middle p) p.all (total p)) ≤
    8020669608*total p+6658181645698*middle p+30779966292966*p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _
    46661277 10092467 2223750587 8020669608 6658181645698 30779966292966
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1+2*131071*middle p ≤ 46661277
    omega
  · change 131071*(2*p.all-1) ≤ 10092467
    omega
  · change 2*131071*total p+1 ≤ 2223750587
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]
end ProximityPrize.SubmissionLower.Lower80840.Initial


end InitialGeometry
