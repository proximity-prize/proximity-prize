/- Apache-2.0. Original retuned 68.36 gate checks at rank 12. -/
import ProximityPrize.SubmissionLower.Night6836EndCore
namespace Koala6836.FastEnd
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def part12_0 : List Nat := [0,1,2,3]
private theorem paidpart12_0 : part12_0.all (fun k => checkEnd 12 (k+12))=true := by decide +kernel
private def part12_1 : List Nat := [4,5,6,7]
private theorem paidpart12_1 : part12_1.all (fun k => checkEnd 12 (k+12))=true := by decide +kernel
private def part12_2 : List Nat := [8,9,10,11]
private theorem paidpart12_2 : part12_2.all (fun k => checkEnd 12 (k+12))=true := by decide +kernel
private def part12_3 : List Nat := [12,13,14,15]
private theorem paidpart12_3 : part12_3.all (fun k => checkEnd 12 (k+12))=true := by decide +kernel
private def part12_4 : List Nat := [16,17,18,19]
private theorem paidpart12_4 : part12_4.all (fun k => checkEnd 12 (k+12))=true := by decide +kernel
private def part12_5 : List Nat := [20,21,22,23]
private theorem paidpart12_5 : part12_5.all (fun k => checkEnd 12 (k+12))=true := by decide +kernel
private def part12_6 : List Nat := [24,25,26,27]
private theorem paidpart12_6 : part12_6.all (fun k => checkEnd 12 (k+12))=true := by decide +kernel
private def part12_7 : List Nat := [28,29,30,31]
private theorem paidpart12_7 : part12_7.all (fun k => checkEnd 12 (k+12))=true := by decide +kernel
private def part12_8 : List Nat := [32,33,34,35]
private theorem paidpart12_8 : part12_8.all (fun k => checkEnd 12 (k+12))=true := by decide +kernel
private def part12_9 : List Nat := [36,37,38,39]
private theorem paidpart12_9 : part12_9.all (fun k => checkEnd 12 (k+12))=true := by decide +kernel
private def part12_10 : List Nat := [40,41,42,43]
private theorem paidpart12_10 : part12_10.all (fun k => checkEnd 12 (k+12))=true := by decide +kernel
private def part12_11 : List Nat := [44,45,46,47]
private theorem paidpart12_11 : part12_11.all (fun k => checkEnd 12 (k+12))=true := by decide +kernel
private def part12_12 : List Nat := [48,49,50]
private theorem paidpart12_12 : part12_12.all (fun k => checkEnd 12 (k+12))=true := by decide +kernel
theorem rank12 : checkedRank 12 = true := by
  unfold checkedRank
  have parts : List.range (maxY 12+2-12) = part12_0 ++ part12_1 ++ part12_2 ++ part12_3 ++ part12_4 ++ part12_5 ++ part12_6 ++ part12_7 ++ part12_8 ++ part12_9 ++ part12_10 ++ part12_11 ++ part12_12 := by decide +kernel
  rw [parts]
  simp only [List.all_append,paidpart12_0,paidpart12_1,paidpart12_2,paidpart12_3,paidpart12_4,paidpart12_5,paidpart12_6,paidpart12_7,paidpart12_8,paidpart12_9,paidpart12_10,paidpart12_11,paidpart12_12, Bool.true_and]
#print axioms rank12
end Koala6836.FastEnd
