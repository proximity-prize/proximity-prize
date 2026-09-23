import ProximityPrize.SubmissionLower.MovingFiberInitialCore6811
import ProximityPrize.SubmissionLower.MovingFiberReceiptBridge6811

namespace ProximityPrize.SubmissionLower.Lower80860.InitialBridge
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN095 RCN100 RCN101 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN243 RCN259 RCN260 RCN266 RCN275 RCN319
open Selection LocatorFactorAggregate LocatorBatchProductRoute
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : GCDMonoid P4 := UniqueFactorizationMonoid.toGCDMonoid P4

theorem initialA_universal_singleBound
    (hreceipt : ReceiptData.Receipt)
    (u0 u1:I → K) (H:P4) (hH:H ≠ 0)
    (hTotal:wt residualTotalWeights H ≤ 10169)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181265 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80879)
    (F:RegularIndex H) (hFU:F ∈ initialAUniversalFactors u0 u1 H):
    ∀ j : Fin 8, (regularSeeds H selected Gamma F).card ≤
      MovingFiberReceiptTypes6811.sheetSlope j.val*(regularCumulativeFlag H F).zOnly+
      MovingFiberReceiptTypes6811.sheetOwn j.val (regularCumulativeFlag H F).all (regularCumulativeFlag H F).yz :=by
  have hF:=RCN167.positiveRFactors_spec H F.1 F.2
  have hdivA:∀ v:Caps.AKernel u0 u1,
      F.1 ∣ reconstruct K 22476860 131071 202144 36 v.1:=
    (mem_initialAUniversalFactors u0 u1 H F).1 hFU
  have hAflag:=Caps.full_A_divisor_mem_box u0 u1 F.1
    hF.1.ne_zero hdivA
  have hAcaps:=(mem_flagGlobalCoefficientBox_iff F.1
    22476860 131071 202144 36 (by decide +kernel)).mp hAflag
  have hFt:wt residualTotalWeights F.1 ≤ 10169:=
    (weightedTotalDegree_le_of_dvd residualTotalWeights F.1 H hF.2.1 hH).trans
      hTotal
  have hFy:wt residualYSWeights F.1 ≤ 171:=
    Caps.common_A_ys_le u0 u1 F.1 hF.1.ne_zero hdivA
  have hFs:wt residualSWeights F.1 ≤ 36:=
    Caps.common_A_slope_le u0 u1 F.1 hF.1.ne_zero hdivA
  have hFflag:F.1 ∈ globalCoefficientBox K 22476860 131071 10169 36:=
    (mem_flagGlobalCoefficientBox_iff F.1
      22476860 131071 10169 36 (by decide +kernel)).mpr ⟨hFt,hFs,hAcaps.2.2⟩
  have hFbox:=flag_box_to_ordinary K 22476860 131071 10169 36 F.1 hFflag
  have hFsupport:ResidualSupportData InitialSupports.wholeSupport F.1:=
    ⟨hFs,hFy,hFt⟩
  let Fself:=LocatorCoprimeQuotient.regularIndexSelf H F
  have hc := originalCumulativeFlag_cumulative F.1
  have hr : 1 ≤ (regularCumulativeFlag H F).all := regularCumulativeFlag_positive H F
  have hs : (regularCumulativeFlag H F).all ≤ 36 := by
    simpa only [regularCumulativeFlag,hc.1] using hFs
  have hy : middle (regularCumulativeFlag H F) ≤ 171 := by
    simpa only [regularCumulativeFlag,middle,hc.2.1] using hFy
  have ht : total (regularCumulativeFlag H F) ≤ 10169 := by
    simpa only [regularCumulativeFlag,total,hc.2.2] using hFt
  have hy' : (regularCumulativeFlag H F).all+(regularCumulativeFlag H F).yz ≤ 171 := by
    simpa only [middle,Nat.add_comm] using hy
  have ht' : (regularCumulativeFlag H F).all+(regularCumulativeFlag H F).yz+
      (regularCumulativeFlag H F).zOnly ≤ 10169 := by
    simpa only [total,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ht
  have hAt := hreceipt _ _ hr hs hy'
  intro j
  have hbound := MovingFiberSingletonGeometry6811.factor_count_of_cover 22476860
    InitialSupports.wholeSupport (by decide +kernel) (by decide +kernel)
    F.1 hF.1.ne_zero hFbox selected Gamma u0 u1 hdegree hagreement hno Fself hs hy ht
    (ReceiptData.lookup (regularCumulativeFlag H F).all (regularCumulativeFlag H F).yz).carrier
    (MovingFiberReceiptTypes6811.sheetSlope j.val)
    (MovingFiberReceiptTypes6811.sheetOwn j.val (regularCumulativeFlag H F).all (regularCumulativeFlag H F).yz)
    (ReceiptData.lookup (regularCumulativeFlag H F).all (regularCumulativeFlag H F).yz).threshold
    (ReceiptData.lookup (regularCumulativeFlag H F).all (regularCumulativeFlag H F).yz).singletons
    hAt.single.1 (by simpa only [Nat.sub_sub,regularCumulativeFlag,Fself,
      LocatorCoprimeQuotient.regularIndexSelf_val] using hAt.single.2 j)
    (fun k hk => ReceiptBridge.threshold_at hreceipt _ _ hr hs hy' k (List.mem_range.mpr (by omega)))
  simpa only [MovingFiberSingleCore6811.cap,RCN140.regularSeeds,regularCumulativeFlag,Fself,
    LocatorCoprimeQuotient.regularIndexSelf_val] using hbound

#print axioms initialA_universal_singleBound
end
end ProximityPrize.SubmissionLower.Lower80860.InitialBridge
