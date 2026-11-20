/- Apache-2.0. Original retuned 68.36 gate checks at rank 6. -/
import ProximityPrize.SubmissionLower.Night6836EndCore
namespace Koala6836.FastEnd
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def part6_0 : List Nat := [0,1,2,3]
private theorem paidpart6_0 : part6_0.all (fun k => checkEnd 6 (k+6))=true := by decide +kernel
private def part6_1 : List Nat := [4,5,6,7]
private theorem paidpart6_1 : part6_1.all (fun k => checkEnd 6 (k+6))=true := by decide +kernel
private def part6_2 : List Nat := [8,9,10,11]
private theorem paidpart6_2 : part6_2.all (fun k => checkEnd 6 (k+6))=true := by decide +kernel
private def part6_3 : List Nat := [12,13,14,15]
private theorem paidpart6_3 : part6_3.all (fun k => checkEnd 6 (k+6))=true := by decide +kernel
private def part6_4 : List Nat := [16,17,18,19]
private theorem paidpart6_4 : part6_4.all (fun k => checkEnd 6 (k+6))=true := by decide +kernel
private def part6_5 : List Nat := [20,21,22,23]
private theorem paidpart6_5 : part6_5.all (fun k => checkEnd 6 (k+6))=true := by decide +kernel
private def part6_6 : List Nat := [24,25,26,27]
private theorem paidpart6_6 : part6_6.all (fun k => checkEnd 6 (k+6))=true := by decide +kernel
private def part6_7 : List Nat := [28,29,30,31]
private theorem paidpart6_7 : part6_7.all (fun k => checkEnd 6 (k+6))=true := by decide +kernel
private def part6_8 : List Nat := [32,33,34,35]
private theorem paidpart6_8 : part6_8.all (fun k => checkEnd 6 (k+6))=true := by decide +kernel
private def part6_9 : List Nat := [36,37,38,39]
private theorem paidpart6_9 : part6_9.all (fun k => checkEnd 6 (k+6))=true := by decide +kernel
private def part6_10 : List Nat := [40,41,42,43]
private theorem paidpart6_10 : part6_10.all (fun k => checkEnd 6 (k+6))=true := by decide +kernel
private def part6_11 : List Nat := [44,45,46,47]
private theorem paidpart6_11 : part6_11.all (fun k => checkEnd 6 (k+6))=true := by decide +kernel
private def part6_12 : List Nat := [48,49,50,51]
private theorem paidpart6_12 : part6_12.all (fun k => checkEnd 6 (k+6))=true := by decide +kernel
private def part6_13 : List Nat := [52,53,54,55]
private theorem paidpart6_13 : part6_13.all (fun k => checkEnd 6 (k+6))=true := by decide +kernel
private def part6_14 : List Nat := [56,57,58,59]
private theorem paidpart6_14 : part6_14.all (fun k => checkEnd 6 (k+6))=true := by decide +kernel
private def part6_15 : List Nat := [60,61,62,63]
private theorem paidpart6_15 : part6_15.all (fun k => checkEnd 6 (k+6))=true := by decide +kernel
private def part6_16 : List Nat := [64,65,66]
private theorem paidpart6_16 : part6_16.all (fun k => checkEnd 6 (k+6))=true := by decide +kernel
theorem rank6 : checkedRank 6 = true := by
  unfold checkedRank
  have parts : List.range (maxY 6+2-6) = part6_0 ++ part6_1 ++ part6_2 ++ part6_3 ++ part6_4 ++ part6_5 ++ part6_6 ++ part6_7 ++ part6_8 ++ part6_9 ++ part6_10 ++ part6_11 ++ part6_12 ++ part6_13 ++ part6_14 ++ part6_15 ++ part6_16 := by decide +kernel
  rw [parts]
  simp only [List.all_append,paidpart6_0,paidpart6_1,paidpart6_2,paidpart6_3,paidpart6_4,paidpart6_5,paidpart6_6,paidpart6_7,paidpart6_8,paidpart6_9,paidpart6_10,paidpart6_11,paidpart6_12,paidpart6_13,paidpart6_14,paidpart6_15,paidpart6_16, Bool.true_and]
#print axioms rank6
end Koala6836.FastEnd
