import ProximityPrize.SubmissionLower.Koala6844ReceiptsFirstJetColumns
import ProximityPrize.SubmissionLower.Koala6844VirtualShortBasis

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

open scoped BigOperators
open SecondJetRelaxedGlobalIndex (Index budget yCount card_index)
open Koala6844VirtualShort (AuxiliaryIndex card_auxiliaryIndex)

set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem ordinaryFirstJetIndex_card (cut L B U : Nat) (hB : B < degree) (hUL : U ≤ L)
    (hcap : slopeColumnCap cut B ≤ U) :
    (Fintype.card (Index (fun _ => cut) degree L B 0 U) : Int) =
      firstJetAffineColumns cut B false*(L : Int)+firstJetAffineColumns cut B true := by
  rw [card_index, Fin.sum_univ_one]
  simp only [Fin.val_zero, Nat.mul_zero, Nat.sub_zero]
  rw [Fin.sum_univ_eq_sum_range (fun r : Nat =>
    ∑ y : Fin (yCount (fun _ => cut) degree U 0 r),
      (budget (fun _ => cut) degree 0 r - degree*y.val) * (L+1-r-y.val))]
  push_cast
  have hsum : (∑ r ∈ Finset.range (B+1), ∑ y : Fin (yCount (fun _ => cut) degree U 0 r),
      ((budget (fun _ => cut) degree 0 r-degree*y.val : Nat) : Int)*((L+1-r-y.val : Nat) : Int)) =
      ∑ r ∈ Finset.range (B+1), firstJetColumnRow cut U L r true := by
    apply Finset.sum_congr rfl
    intro r _
    unfold firstJetColumnRow
    rw [Fin.sum_univ_eq_sum_range (fun y : Nat =>
      ((budget (fun _ => cut) degree 0 r-degree*y : Nat) : Int)*((L+1-r-y : Nat) : Int))]
    simp only [ite_true]
  rw [hsum]
  exact firstJetColumnRows_eq cut B U L true hB hcap hUL

theorem auxiliaryFirstJetIndex_card (cut B U : Nat) (hB : B < degree)
    (hcap : slopeColumnCap cut B ≤ U) :
    (Fintype.card (AuxiliaryIndex (fun _ => cut) degree B 0 U) : Int) =
      firstJetAffineColumns cut B false := by
  rw [card_auxiliaryIndex, Fin.sum_univ_one]
  simp only [Fin.val_zero, Nat.mul_zero, Nat.sub_zero]
  rw [Fin.sum_univ_eq_sum_range (fun r : Nat =>
    ∑ y : Fin (yCount (fun _ => cut) degree U 0 r),
      (budget (fun _ => cut) degree 0 r - degree*y.val))]
  push_cast
  have hsum : (∑ r ∈ Finset.range (B+1), ∑ y : Fin (yCount (fun _ => cut) degree U 0 r),
      ((budget (fun _ => cut) degree 0 r-degree*y.val : Nat) : Int)) =
      ∑ r ∈ Finset.range (B+1), firstJetColumnRow cut U U r false := by
    apply Finset.sum_congr rfl
    intro r _
    unfold firstJetColumnRow
    rw [Fin.sum_univ_eq_sum_range (fun y : Nat =>
      ((budget (fun _ => cut) degree 0 r-degree*y : Nat) : Int))]
    simp
  rw [hsum]
  exact firstJetColumnRows_eq cut B U U false hB hcap le_rfl

end ProximityPrize.SubmissionLower.Koala6844Receipts
