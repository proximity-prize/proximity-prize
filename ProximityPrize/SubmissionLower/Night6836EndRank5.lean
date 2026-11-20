/- Apache-2.0. Original retuned 68.36 gate checks at rank 5. -/
import ProximityPrize.SubmissionLower.Night6836EndCore
namespace Koala6836.FastEnd
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def part5_0 : List Nat := [0,1,2,3]
private theorem paidpart5_0 : part5_0.all (fun k => checkEnd 5 (k+5))=true := by decide +kernel
private def part5_1 : List Nat := [4,5,6,7]
private theorem paidpart5_1 : part5_1.all (fun k => checkEnd 5 (k+5))=true := by decide +kernel
private def part5_2 : List Nat := [8,9,10,11]
private theorem paidpart5_2 : part5_2.all (fun k => checkEnd 5 (k+5))=true := by decide +kernel
private def part5_3 : List Nat := [12,13,14,15]
private theorem paidpart5_3 : part5_3.all (fun k => checkEnd 5 (k+5))=true := by decide +kernel
private def part5_4 : List Nat := [16,17,18,19]
private theorem paidpart5_4 : part5_4.all (fun k => checkEnd 5 (k+5))=true := by decide +kernel
private def part5_5 : List Nat := [20,21,22,23]
private theorem paidpart5_5 : part5_5.all (fun k => checkEnd 5 (k+5))=true := by decide +kernel
private def part5_6 : List Nat := [24,25,26,27]
private theorem paidpart5_6 : part5_6.all (fun k => checkEnd 5 (k+5))=true := by decide +kernel
private def part5_7 : List Nat := [28,29,30,31]
private theorem paidpart5_7 : part5_7.all (fun k => checkEnd 5 (k+5))=true := by decide +kernel
private def part5_8 : List Nat := [32,33,34,35]
private theorem paidpart5_8 : part5_8.all (fun k => checkEnd 5 (k+5))=true := by decide +kernel
private def part5_9 : List Nat := [36,37,38,39]
private theorem paidpart5_9 : part5_9.all (fun k => checkEnd 5 (k+5))=true := by decide +kernel
private def part5_10 : List Nat := [40,41,42,43]
private theorem paidpart5_10 : part5_10.all (fun k => checkEnd 5 (k+5))=true := by decide +kernel
private def part5_11 : List Nat := [44,45,46,47]
private theorem paidpart5_11 : part5_11.all (fun k => checkEnd 5 (k+5))=true := by decide +kernel
private def part5_12 : List Nat := [48,49,50,51]
private theorem paidpart5_12 : part5_12.all (fun k => checkEnd 5 (k+5))=true := by decide +kernel
private def part5_13 : List Nat := [52,53,54,55]
private theorem paidpart5_13 : part5_13.all (fun k => checkEnd 5 (k+5))=true := by decide +kernel
private def part5_14 : List Nat := [56,57,58,59]
private theorem paidpart5_14 : part5_14.all (fun k => checkEnd 5 (k+5))=true := by decide +kernel
private def part5_15 : List Nat := [60,61,62,63]
private theorem paidpart5_15 : part5_15.all (fun k => checkEnd 5 (k+5))=true := by decide +kernel
private def part5_16 : List Nat := [64,65,66,67]
private theorem paidpart5_16 : part5_16.all (fun k => checkEnd 5 (k+5))=true := by decide +kernel
private def part5_17 : List Nat := [68]
private theorem paidpart5_17 : part5_17.all (fun k => checkEnd 5 (k+5))=true := by decide +kernel
theorem rank5 : checkedRank 5 = true := by
  unfold checkedRank
  have parts : List.range (maxY 5+2-5) = part5_0 ++ part5_1 ++ part5_2 ++ part5_3 ++ part5_4 ++ part5_5 ++ part5_6 ++ part5_7 ++ part5_8 ++ part5_9 ++ part5_10 ++ part5_11 ++ part5_12 ++ part5_13 ++ part5_14 ++ part5_15 ++ part5_16 ++ part5_17 := by decide +kernel
  rw [parts]
  simp only [List.all_append,paidpart5_0,paidpart5_1,paidpart5_2,paidpart5_3,paidpart5_4,paidpart5_5,paidpart5_6,paidpart5_7,paidpart5_8,paidpart5_9,paidpart5_10,paidpart5_11,paidpart5_12,paidpart5_13,paidpart5_14,paidpart5_15,paidpart5_16,paidpart5_17, Bool.true_and]
#print axioms rank5
end Koala6836.FastEnd
