/- Apache-2.0. Original retuned 68.36 gate checks at rank 3. -/
import ProximityPrize.SubmissionLower.Night6836EndCore
namespace Koala6836.FastEnd
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def part3_0 : List Nat := [0,1,2,3]
private theorem paidpart3_0 : part3_0.all (fun k => checkEnd 3 (k+3))=true := by decide +kernel
private def part3_1 : List Nat := [4,5,6,7]
private theorem paidpart3_1 : part3_1.all (fun k => checkEnd 3 (k+3))=true := by decide +kernel
private def part3_2 : List Nat := [8,9,10,11]
private theorem paidpart3_2 : part3_2.all (fun k => checkEnd 3 (k+3))=true := by decide +kernel
private def part3_3 : List Nat := [12,13,14,15]
private theorem paidpart3_3 : part3_3.all (fun k => checkEnd 3 (k+3))=true := by decide +kernel
private def part3_4 : List Nat := [16,17,18,19]
private theorem paidpart3_4 : part3_4.all (fun k => checkEnd 3 (k+3))=true := by decide +kernel
private def part3_5 : List Nat := [20,21,22,23]
private theorem paidpart3_5 : part3_5.all (fun k => checkEnd 3 (k+3))=true := by decide +kernel
private def part3_6 : List Nat := [24,25,26,27]
private theorem paidpart3_6 : part3_6.all (fun k => checkEnd 3 (k+3))=true := by decide +kernel
private def part3_7 : List Nat := [28,29,30,31]
private theorem paidpart3_7 : part3_7.all (fun k => checkEnd 3 (k+3))=true := by decide +kernel
private def part3_8 : List Nat := [32,33,34,35]
private theorem paidpart3_8 : part3_8.all (fun k => checkEnd 3 (k+3))=true := by decide +kernel
private def part3_9 : List Nat := [36,37,38,39]
private theorem paidpart3_9 : part3_9.all (fun k => checkEnd 3 (k+3))=true := by decide +kernel
private def part3_10 : List Nat := [40,41,42,43]
private theorem paidpart3_10 : part3_10.all (fun k => checkEnd 3 (k+3))=true := by decide +kernel
private def part3_11 : List Nat := [44,45,46,47]
private theorem paidpart3_11 : part3_11.all (fun k => checkEnd 3 (k+3))=true := by decide +kernel
private def part3_12 : List Nat := [48,49,50,51]
private theorem paidpart3_12 : part3_12.all (fun k => checkEnd 3 (k+3))=true := by decide +kernel
private def part3_13 : List Nat := [52,53,54,55]
private theorem paidpart3_13 : part3_13.all (fun k => checkEnd 3 (k+3))=true := by decide +kernel
private def part3_14 : List Nat := [56,57,58,59]
private theorem paidpart3_14 : part3_14.all (fun k => checkEnd 3 (k+3))=true := by decide +kernel
private def part3_15 : List Nat := [60,61,62,63]
private theorem paidpart3_15 : part3_15.all (fun k => checkEnd 3 (k+3))=true := by decide +kernel
private def part3_16 : List Nat := [64,65,66,67]
private theorem paidpart3_16 : part3_16.all (fun k => checkEnd 3 (k+3))=true := by decide +kernel
private def part3_17 : List Nat := [68,69,70,71]
private theorem paidpart3_17 : part3_17.all (fun k => checkEnd 3 (k+3))=true := by decide +kernel
private def part3_18 : List Nat := [72,73]
private theorem paidpart3_18 : part3_18.all (fun k => checkEnd 3 (k+3))=true := by decide +kernel
theorem rank3 : checkedRank 3 = true := by
  unfold checkedRank
  have parts : List.range (maxY 3+2-3) = part3_0 ++ part3_1 ++ part3_2 ++ part3_3 ++ part3_4 ++ part3_5 ++ part3_6 ++ part3_7 ++ part3_8 ++ part3_9 ++ part3_10 ++ part3_11 ++ part3_12 ++ part3_13 ++ part3_14 ++ part3_15 ++ part3_16 ++ part3_17 ++ part3_18 := by decide +kernel
  rw [parts]
  simp only [List.all_append,paidpart3_0,paidpart3_1,paidpart3_2,paidpart3_3,paidpart3_4,paidpart3_5,paidpart3_6,paidpart3_7,paidpart3_8,paidpart3_9,paidpart3_10,paidpart3_11,paidpart3_12,paidpart3_13,paidpart3_14,paidpart3_15,paidpart3_16,paidpart3_17,paidpart3_18, Bool.true_and]
#print axioms rank3
end Koala6836.FastEnd
