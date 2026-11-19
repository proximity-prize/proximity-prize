/- Apache-2.0. Original retuned 68.36 gate checks at rank 8. -/
import ProximityPrize.SubmissionLower.Night6836EndCore
namespace Koala6836.FastEnd
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def part8_0 : List Nat := [0,1,2,3]
private theorem paidpart8_0 : part8_0.all (fun k => checkEnd 8 (k+8))=true := by decide +kernel
private def part8_1 : List Nat := [4,5,6,7]
private theorem paidpart8_1 : part8_1.all (fun k => checkEnd 8 (k+8))=true := by decide +kernel
private def part8_2 : List Nat := [8,9,10,11]
private theorem paidpart8_2 : part8_2.all (fun k => checkEnd 8 (k+8))=true := by decide +kernel
private def part8_3 : List Nat := [12,13,14,15]
private theorem paidpart8_3 : part8_3.all (fun k => checkEnd 8 (k+8))=true := by decide +kernel
private def part8_4 : List Nat := [16,17,18,19]
private theorem paidpart8_4 : part8_4.all (fun k => checkEnd 8 (k+8))=true := by decide +kernel
private def part8_5 : List Nat := [20,21,22,23]
private theorem paidpart8_5 : part8_5.all (fun k => checkEnd 8 (k+8))=true := by decide +kernel
private def part8_6 : List Nat := [24,25,26,27]
private theorem paidpart8_6 : part8_6.all (fun k => checkEnd 8 (k+8))=true := by decide +kernel
private def part8_7 : List Nat := [28,29,30,31]
private theorem paidpart8_7 : part8_7.all (fun k => checkEnd 8 (k+8))=true := by decide +kernel
private def part8_8 : List Nat := [32,33,34,35]
private theorem paidpart8_8 : part8_8.all (fun k => checkEnd 8 (k+8))=true := by decide +kernel
private def part8_9 : List Nat := [36,37,38,39]
private theorem paidpart8_9 : part8_9.all (fun k => checkEnd 8 (k+8))=true := by decide +kernel
private def part8_10 : List Nat := [40,41,42,43]
private theorem paidpart8_10 : part8_10.all (fun k => checkEnd 8 (k+8))=true := by decide +kernel
private def part8_11 : List Nat := [44,45,46,47]
private theorem paidpart8_11 : part8_11.all (fun k => checkEnd 8 (k+8))=true := by decide +kernel
private def part8_12 : List Nat := [48,49,50,51]
private theorem paidpart8_12 : part8_12.all (fun k => checkEnd 8 (k+8))=true := by decide +kernel
private def part8_13 : List Nat := [52,53,54,55]
private theorem paidpart8_13 : part8_13.all (fun k => checkEnd 8 (k+8))=true := by decide +kernel
private def part8_14 : List Nat := [56,57,58,59]
private theorem paidpart8_14 : part8_14.all (fun k => checkEnd 8 (k+8))=true := by decide +kernel
private def part8_15 : List Nat := [60,61]
private theorem paidpart8_15 : part8_15.all (fun k => checkEnd 8 (k+8))=true := by decide +kernel
theorem rank8 : checkedRank 8 = true := by
  unfold checkedRank
  have parts : List.range (maxY 8+2-8) = part8_0 ++ part8_1 ++ part8_2 ++ part8_3 ++ part8_4 ++ part8_5 ++ part8_6 ++ part8_7 ++ part8_8 ++ part8_9 ++ part8_10 ++ part8_11 ++ part8_12 ++ part8_13 ++ part8_14 ++ part8_15 := by decide +kernel
  rw [parts]
  simp only [List.all_append,paidpart8_0,paidpart8_1,paidpart8_2,paidpart8_3,paidpart8_4,paidpart8_5,paidpart8_6,paidpart8_7,paidpart8_8,paidpart8_9,paidpart8_10,paidpart8_11,paidpart8_12,paidpart8_13,paidpart8_14,paidpart8_15, Bool.true_and]
#print axioms rank8
end Koala6836.FastEnd
