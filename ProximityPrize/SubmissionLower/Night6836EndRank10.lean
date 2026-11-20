/- Apache-2.0. Original retuned 68.36 gate checks at rank 10. -/
import ProximityPrize.SubmissionLower.Night6836EndCore
namespace Koala6836.FastEnd
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def part10_0 : List Nat := [0,1,2,3]
private theorem paidpart10_0 : part10_0.all (fun k => checkEnd 10 (k+10))=true := by decide +kernel
private def part10_1 : List Nat := [4,5,6,7]
private theorem paidpart10_1 : part10_1.all (fun k => checkEnd 10 (k+10))=true := by decide +kernel
private def part10_2 : List Nat := [8,9,10,11]
private theorem paidpart10_2 : part10_2.all (fun k => checkEnd 10 (k+10))=true := by decide +kernel
private def part10_3 : List Nat := [12,13,14,15]
private theorem paidpart10_3 : part10_3.all (fun k => checkEnd 10 (k+10))=true := by decide +kernel
private def part10_4 : List Nat := [16,17,18,19]
private theorem paidpart10_4 : part10_4.all (fun k => checkEnd 10 (k+10))=true := by decide +kernel
private def part10_5 : List Nat := [20,21,22,23]
private theorem paidpart10_5 : part10_5.all (fun k => checkEnd 10 (k+10))=true := by decide +kernel
private def part10_6 : List Nat := [24,25,26,27]
private theorem paidpart10_6 : part10_6.all (fun k => checkEnd 10 (k+10))=true := by decide +kernel
private def part10_7 : List Nat := [28,29,30,31]
private theorem paidpart10_7 : part10_7.all (fun k => checkEnd 10 (k+10))=true := by decide +kernel
private def part10_8 : List Nat := [32,33,34,35]
private theorem paidpart10_8 : part10_8.all (fun k => checkEnd 10 (k+10))=true := by decide +kernel
private def part10_9 : List Nat := [36,37,38,39]
private theorem paidpart10_9 : part10_9.all (fun k => checkEnd 10 (k+10))=true := by decide +kernel
private def part10_10 : List Nat := [40,41,42,43]
private theorem paidpart10_10 : part10_10.all (fun k => checkEnd 10 (k+10))=true := by decide +kernel
private def part10_11 : List Nat := [44,45,46,47]
private theorem paidpart10_11 : part10_11.all (fun k => checkEnd 10 (k+10))=true := by decide +kernel
private def part10_12 : List Nat := [48,49,50,51]
private theorem paidpart10_12 : part10_12.all (fun k => checkEnd 10 (k+10))=true := by decide +kernel
private def part10_13 : List Nat := [52,53,54,55]
private theorem paidpart10_13 : part10_13.all (fun k => checkEnd 10 (k+10))=true := by decide +kernel
private def part10_14 : List Nat := [56]
private theorem paidpart10_14 : part10_14.all (fun k => checkEnd 10 (k+10))=true := by decide +kernel
theorem rank10 : checkedRank 10 = true := by
  unfold checkedRank
  have parts : List.range (maxY 10+2-10) = part10_0 ++ part10_1 ++ part10_2 ++ part10_3 ++ part10_4 ++ part10_5 ++ part10_6 ++ part10_7 ++ part10_8 ++ part10_9 ++ part10_10 ++ part10_11 ++ part10_12 ++ part10_13 ++ part10_14 := by decide +kernel
  rw [parts]
  simp only [List.all_append,paidpart10_0,paidpart10_1,paidpart10_2,paidpart10_3,paidpart10_4,paidpart10_5,paidpart10_6,paidpart10_7,paidpart10_8,paidpart10_9,paidpart10_10,paidpart10_11,paidpart10_12,paidpart10_13,paidpart10_14, Bool.true_and]
#print axioms rank10
end Koala6836.FastEnd
