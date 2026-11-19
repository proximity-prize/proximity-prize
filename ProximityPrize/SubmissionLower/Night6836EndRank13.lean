/- Apache-2.0. Original retuned 68.36 gate checks at rank 13. -/
import ProximityPrize.SubmissionLower.Night6836EndCore
namespace Koala6836.FastEnd
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def part13_0 : List Nat := [0,1,2,3]
private theorem paidpart13_0 : part13_0.all (fun k => checkEnd 13 (k+13))=true := by decide +kernel
private def part13_1 : List Nat := [4,5,6,7]
private theorem paidpart13_1 : part13_1.all (fun k => checkEnd 13 (k+13))=true := by decide +kernel
private def part13_2 : List Nat := [8,9,10,11]
private theorem paidpart13_2 : part13_2.all (fun k => checkEnd 13 (k+13))=true := by decide +kernel
private def part13_3 : List Nat := [12,13,14,15]
private theorem paidpart13_3 : part13_3.all (fun k => checkEnd 13 (k+13))=true := by decide +kernel
private def part13_4 : List Nat := [16,17,18,19]
private theorem paidpart13_4 : part13_4.all (fun k => checkEnd 13 (k+13))=true := by decide +kernel
private def part13_5 : List Nat := [20,21,22,23]
private theorem paidpart13_5 : part13_5.all (fun k => checkEnd 13 (k+13))=true := by decide +kernel
private def part13_6 : List Nat := [24,25,26,27]
private theorem paidpart13_6 : part13_6.all (fun k => checkEnd 13 (k+13))=true := by decide +kernel
private def part13_7 : List Nat := [28,29,30,31]
private theorem paidpart13_7 : part13_7.all (fun k => checkEnd 13 (k+13))=true := by decide +kernel
private def part13_8 : List Nat := [32,33,34,35]
private theorem paidpart13_8 : part13_8.all (fun k => checkEnd 13 (k+13))=true := by decide +kernel
private def part13_9 : List Nat := [36,37,38,39]
private theorem paidpart13_9 : part13_9.all (fun k => checkEnd 13 (k+13))=true := by decide +kernel
private def part13_10 : List Nat := [40,41,42,43]
private theorem paidpart13_10 : part13_10.all (fun k => checkEnd 13 (k+13))=true := by decide +kernel
private def part13_11 : List Nat := [44,45,46]
private theorem paidpart13_11 : part13_11.all (fun k => checkEnd 13 (k+13))=true := by decide +kernel
theorem rank13 : checkedRank 13 = true := by
  unfold checkedRank
  have parts : List.range (maxY 13+2-13) = part13_0 ++ part13_1 ++ part13_2 ++ part13_3 ++ part13_4 ++ part13_5 ++ part13_6 ++ part13_7 ++ part13_8 ++ part13_9 ++ part13_10 ++ part13_11 := by decide +kernel
  rw [parts]
  simp only [List.all_append,paidpart13_0,paidpart13_1,paidpart13_2,paidpart13_3,paidpart13_4,paidpart13_5,paidpart13_6,paidpart13_7,paidpart13_8,paidpart13_9,paidpart13_10,paidpart13_11, Bool.true_and]
#print axioms rank13
end Koala6836.FastEnd
