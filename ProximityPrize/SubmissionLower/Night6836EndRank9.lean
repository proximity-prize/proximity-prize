/- Apache-2.0. Original retuned 68.36 gate checks at rank 9. -/
import ProximityPrize.SubmissionLower.Night6836EndCore
namespace Koala6836.FastEnd
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def part9_0 : List Nat := [0,1,2,3]
private theorem paidpart9_0 : part9_0.all (fun k => checkEnd 9 (k+9))=true := by decide +kernel
private def part9_1 : List Nat := [4,5,6,7]
private theorem paidpart9_1 : part9_1.all (fun k => checkEnd 9 (k+9))=true := by decide +kernel
private def part9_2 : List Nat := [8,9,10,11]
private theorem paidpart9_2 : part9_2.all (fun k => checkEnd 9 (k+9))=true := by decide +kernel
private def part9_3 : List Nat := [12,13,14,15]
private theorem paidpart9_3 : part9_3.all (fun k => checkEnd 9 (k+9))=true := by decide +kernel
private def part9_4 : List Nat := [16,17,18,19]
private theorem paidpart9_4 : part9_4.all (fun k => checkEnd 9 (k+9))=true := by decide +kernel
private def part9_5 : List Nat := [20,21,22,23]
private theorem paidpart9_5 : part9_5.all (fun k => checkEnd 9 (k+9))=true := by decide +kernel
private def part9_6 : List Nat := [24,25,26,27]
private theorem paidpart9_6 : part9_6.all (fun k => checkEnd 9 (k+9))=true := by decide +kernel
private def part9_7 : List Nat := [28,29,30,31]
private theorem paidpart9_7 : part9_7.all (fun k => checkEnd 9 (k+9))=true := by decide +kernel
private def part9_8 : List Nat := [32,33,34,35]
private theorem paidpart9_8 : part9_8.all (fun k => checkEnd 9 (k+9))=true := by decide +kernel
private def part9_9 : List Nat := [36,37,38,39]
private theorem paidpart9_9 : part9_9.all (fun k => checkEnd 9 (k+9))=true := by decide +kernel
private def part9_10 : List Nat := [40,41,42,43]
private theorem paidpart9_10 : part9_10.all (fun k => checkEnd 9 (k+9))=true := by decide +kernel
private def part9_11 : List Nat := [44,45,46,47]
private theorem paidpart9_11 : part9_11.all (fun k => checkEnd 9 (k+9))=true := by decide +kernel
private def part9_12 : List Nat := [48,49,50,51]
private theorem paidpart9_12 : part9_12.all (fun k => checkEnd 9 (k+9))=true := by decide +kernel
private def part9_13 : List Nat := [52,53,54,55]
private theorem paidpart9_13 : part9_13.all (fun k => checkEnd 9 (k+9))=true := by decide +kernel
private def part9_14 : List Nat := [56,57,58,59]
private theorem paidpart9_14 : part9_14.all (fun k => checkEnd 9 (k+9))=true := by decide +kernel
theorem rank9 : checkedRank 9 = true := by
  unfold checkedRank
  have parts : List.range (maxY 9+2-9) = part9_0 ++ part9_1 ++ part9_2 ++ part9_3 ++ part9_4 ++ part9_5 ++ part9_6 ++ part9_7 ++ part9_8 ++ part9_9 ++ part9_10 ++ part9_11 ++ part9_12 ++ part9_13 ++ part9_14 := by decide +kernel
  rw [parts]
  simp only [List.all_append,paidpart9_0,paidpart9_1,paidpart9_2,paidpart9_3,paidpart9_4,paidpart9_5,paidpart9_6,paidpart9_7,paidpart9_8,paidpart9_9,paidpart9_10,paidpart9_11,paidpart9_12,paidpart9_13,paidpart9_14, Bool.true_and]
#print axioms rank9
end Koala6836.FastEnd
