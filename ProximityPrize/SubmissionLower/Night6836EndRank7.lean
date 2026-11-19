/- Apache-2.0. Original retuned 68.36 gate checks at rank 7. -/
import ProximityPrize.SubmissionLower.Night6836EndCore
namespace Koala6836.FastEnd
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def part7_0 : List Nat := [0,1,2,3]
private theorem paidpart7_0 : part7_0.all (fun k => checkEnd 7 (k+7))=true := by decide +kernel
private def part7_1 : List Nat := [4,5,6,7]
private theorem paidpart7_1 : part7_1.all (fun k => checkEnd 7 (k+7))=true := by decide +kernel
private def part7_2 : List Nat := [8,9,10,11]
private theorem paidpart7_2 : part7_2.all (fun k => checkEnd 7 (k+7))=true := by decide +kernel
private def part7_3 : List Nat := [12,13,14,15]
private theorem paidpart7_3 : part7_3.all (fun k => checkEnd 7 (k+7))=true := by decide +kernel
private def part7_4 : List Nat := [16,17,18,19]
private theorem paidpart7_4 : part7_4.all (fun k => checkEnd 7 (k+7))=true := by decide +kernel
private def part7_5 : List Nat := [20,21,22,23]
private theorem paidpart7_5 : part7_5.all (fun k => checkEnd 7 (k+7))=true := by decide +kernel
private def part7_6 : List Nat := [24,25,26,27]
private theorem paidpart7_6 : part7_6.all (fun k => checkEnd 7 (k+7))=true := by decide +kernel
private def part7_7 : List Nat := [28,29,30,31]
private theorem paidpart7_7 : part7_7.all (fun k => checkEnd 7 (k+7))=true := by decide +kernel
private def part7_8 : List Nat := [32,33,34,35]
private theorem paidpart7_8 : part7_8.all (fun k => checkEnd 7 (k+7))=true := by decide +kernel
private def part7_9 : List Nat := [36,37,38,39]
private theorem paidpart7_9 : part7_9.all (fun k => checkEnd 7 (k+7))=true := by decide +kernel
private def part7_10 : List Nat := [40,41,42,43]
private theorem paidpart7_10 : part7_10.all (fun k => checkEnd 7 (k+7))=true := by decide +kernel
private def part7_11 : List Nat := [44,45,46,47]
private theorem paidpart7_11 : part7_11.all (fun k => checkEnd 7 (k+7))=true := by decide +kernel
private def part7_12 : List Nat := [48,49,50,51]
private theorem paidpart7_12 : part7_12.all (fun k => checkEnd 7 (k+7))=true := by decide +kernel
private def part7_13 : List Nat := [52,53,54,55]
private theorem paidpart7_13 : part7_13.all (fun k => checkEnd 7 (k+7))=true := by decide +kernel
private def part7_14 : List Nat := [56,57,58,59]
private theorem paidpart7_14 : part7_14.all (fun k => checkEnd 7 (k+7))=true := by decide +kernel
private def part7_15 : List Nat := [60,61,62,63]
private theorem paidpart7_15 : part7_15.all (fun k => checkEnd 7 (k+7))=true := by decide +kernel
private def part7_16 : List Nat := [64]
private theorem paidpart7_16 : part7_16.all (fun k => checkEnd 7 (k+7))=true := by decide +kernel
theorem rank7 : checkedRank 7 = true := by
  unfold checkedRank
  have parts : List.range (maxY 7+2-7) = part7_0 ++ part7_1 ++ part7_2 ++ part7_3 ++ part7_4 ++ part7_5 ++ part7_6 ++ part7_7 ++ part7_8 ++ part7_9 ++ part7_10 ++ part7_11 ++ part7_12 ++ part7_13 ++ part7_14 ++ part7_15 ++ part7_16 := by decide +kernel
  rw [parts]
  simp only [List.all_append,paidpart7_0,paidpart7_1,paidpart7_2,paidpart7_3,paidpart7_4,paidpart7_5,paidpart7_6,paidpart7_7,paidpart7_8,paidpart7_9,paidpart7_10,paidpart7_11,paidpart7_12,paidpart7_13,paidpart7_14,paidpart7_15,paidpart7_16, Bool.true_and]
#print axioms rank7
end Koala6836.FastEnd
