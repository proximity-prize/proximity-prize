import ProximityPrize.SubmissionLower.Koala6844ReceiptsFirstJetIndex
import ProximityPrize.SubmissionLower.Koala6844ReceiptsFirstJetRank
import ProximityPrize.SubmissionLower.Koala6844VirtualShortSource
import ProximityPrize.SubmissionLower.Koala6844VirtualShortRankReceipts

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

open scoped BigOperators
open Koala6844VirtualShort (NormalizedIndex AuxiliaryIndex card_normalizedIndex normalizedRankBudget
  seedlessRankBudget ordinaryRankBound_eq seedlessRankBudget_eq_auxiliaryRankSlice)

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxRecDepth 2048

private theorem exact_window_sum (n : Nat) (f : Nat → Int) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i.val := by
  rw [Fin.sum_univ_eq_sum_range]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.map_append,List.sum_append,Finset.sum_range_succ,ih]
    simp

private theorem shiftedSlopeColumnCap_le (cut B U j : Nat) (hB : B < degree)
    (hcap : slopeColumnCap cut B ≤ U) (hj : j ≤ U) :
    slopeColumnCap (cut-(degree+poleWidth)*j) B ≤ U-j := by
  unfold slopeColumnCap degree poleWidth at *
  omega

private theorem rankSlope_zero (B : Nat) : firstJetRankSlopeTwelve 0 B = 0 := by
  simp [firstJetRankSlopeTwelve, firstJetRankTwelve]

theorem firstJetGapTwelve_exact (f : FirstJetShape) (room : Nat) (hB : f.s < degree)
    (hM : f.m+f.s ≤ (firstJetFlag f room).y) (hL : (firstJetFlag f room).y ≤ f.L)
    (hq : f.q ≤ (firstJetFlag f room).y) :
    let D := fun _ : Nat => firstJetCutoff f room
    let U := (firstJetFlag f room).y
    firstJetGapTwelve f room =
      12*((Fintype.card (NormalizedIndex D degree (degree+poleWidth) f.L f.s 0 U f.q) : Int) -
        (nodes : Int)*(normalizedRankBudget D degree f.m f.L f.s 0 U f.q : Int)) := by
  dsimp only
  let cut := firstJetCutoff f room
  let U := (firstJetFlag f room).y
  let D : Nat → Nat := fun _ => cut
  let src : SourceShape := ⟨f.m,f.s,0,U,f.L,0,1,f.q⟩
  let A := Fintype.card (SecondJetRelaxedGlobalIndex.Index D degree f.L f.s 0 U)
  let R := SecondJetRelaxedGlobalMap.rankBound f.m f.L f.s 0 U (fun _ => (cut+f.s-1)/degree)
  let col (j : Nat) := Fintype.card
    (AuxiliaryIndex (fun _ => cut-(degree+poleWidth)*j) degree f.s 0 (U-j))
  let rank (j : Nat) := seedlessRankBudget (f.m-j) f.s 0 (U-j)
  change firstJetGapTwelve f room =
    12*((Fintype.card (NormalizedIndex D degree (degree+poleWidth) f.L f.s 0 U f.q) : Int) -
      (nodes : Int)*(normalizedRankBudget D degree f.m f.L f.s 0 U f.q : Int))
  rw [card_normalizedIndex,normalizedRankBudget]
  change firstJetGapTwelve f room =
    12*((((A+∑ j : Fin f.q, col (j.val+1)) : Nat) : Int) -
      (nodes : Int)*(((R+∑ j : Fin f.q, rank (j.val+1)) : Nat) : Int))
  have hcap : slopeColumnCap cut f.s ≤ U := le_rfl
  have hOrdCol : (A : Int) = firstJetAffineColumns cut f.s false*f.L+firstJetAffineColumns cut f.s true :=
    ordinaryFirstJetIndex_card cut f.L f.s U hB hL hcap
  have hOrdRank : 12*(R : Int) = firstJetRankTwelve f.m f.s f.L := by
    have hC (h : Nat) (_ : h ≤ src.s) : U ≤ (cut+f.s-1)/degree := le_rfl
    change 12*(SecondJetRelaxedGlobalMap.rankBound src.m src.L src.B src.s src.U
      (fun _ => (cut+f.s-1)/degree) : Int) = _
    rw [ordinaryRankBound_eq src _ (by simp [src]) (by simp [src]) hL hC]
    exact ordinaryFirstJetRankTwelve_eq src rfl hM hL
  have hAux (j : Fin f.q) : firstJetAuxContribution f room j.val =
      12*(col (j.val+1) : Int) - (nodes : Int)*(12*(rank (j.val+1) : Int)) := by
    have hj : j.val+1 ≤ U := (Nat.succ_le_of_lt j.isLt).trans hq
    have hA : (col (j.val+1) : Int) =
        firstJetAffineColumns (firstJetCutoff f room-(degree+poleWidth)*(j.val+1)) f.s false :=
      auxiliaryFirstJetIndex_card _ f.s _ hB (shiftedSlopeColumnCap_le cut f.s U _ hB hcap hj)
    have hR : 12*(rank (j.val+1) : Int) = firstJetRankSlopeTwelve (f.m-(j.val+1)) f.s := by
      change 12*(seedlessRankBudget (src.m-(j.val+1)) src.B src.s (src.U-(j.val+1)) : Int) = _
      rw [seedlessRankBudget_eq_auxiliaryRankSlice src _ (by simp [src]) hj]
      exact auxiliaryFirstJetRankTwelve_eq src _ rfl hj hM
    simp only [firstJetAuxContribution]
    rw [Nat.mul_comm (j.val+1) (degree+poleWidth), ← hA,hR]
    split_ifs with h
    · rfl
    · have hz : f.m-(j.val+1)=0 := by omega
      rw [hz,rankSlope_zero,mul_zero]

  have hsum : ((List.range f.q).map (firstJetAuxContribution f room)).sum =
      ∑ j : Fin f.q, (12*(col (j.val+1) : Int) - (nodes : Int)*(12*(rank (j.val+1) : Int))) := by
    rw [exact_window_sum]
    exact Finset.sum_congr rfl fun j _ => hAux j
  unfold firstJetGapTwelve
  change 12*(firstJetAffineColumns cut f.s false*f.L+firstJetAffineColumns cut f.s true)-
    (nodes : Int)*firstJetRankTwelve f.m f.s f.L +
    ((List.range f.q).map (firstJetAuxContribution f room)).sum = _
  rw [← hOrdCol,← hOrdRank,hsum]
  push_cast
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem firstJetGap_exact (f : FirstJetShape) (room : Nat) (hB : f.s < degree)
    (hM : f.m+f.s ≤ (firstJetFlag f room).y) (hL : (firstJetFlag f room).y ≤ f.L)
    (hq : f.q ≤ (firstJetFlag f room).y) :
    let D := fun _ : Nat => firstJetCutoff f room
    let U := (firstJetFlag f room).y
    firstJetGap f room = Fintype.card (NormalizedIndex D degree (degree+poleWidth) f.L f.s 0 U f.q) -
      nodes*normalizedRankBudget D degree f.m f.L f.s 0 U f.q := by
  dsimp only
  unfold firstJetGap
  rw [firstJetGapTwelve_exact f room hB hM hL hq]
  simp only [Int.mul_ediv_cancel_left _ (by decide : (12 : Int) ≠ 0), ← Nat.cast_mul]
  omega

end ProximityPrize.SubmissionLower.Koala6844Receipts
