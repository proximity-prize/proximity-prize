/- Apache-2.0. Original retuned 68.36 gate checks at rank 11. -/
import ProximityPrize.SubmissionLower.Night6836EndCore
namespace Koala6836.FastEnd
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def part11_0 : List Nat := [0,1,2,3]
private theorem paidpart11_0 : part11_0.all (fun k => checkEnd 11 (k+11))=true := by decide +kernel
private def part11_1 : List Nat := [4,5,6,7]
private theorem paidpart11_1 : part11_1.all (fun k => checkEnd 11 (k+11))=true := by decide +kernel
private def part11_2 : List Nat := [8,9,10,11]
private theorem paidpart11_2 : part11_2.all (fun k => checkEnd 11 (k+11))=true := by decide +kernel
private def part11_3 : List Nat := [12,13,14,15]
private theorem paidpart11_3 : part11_3.all (fun k => checkEnd 11 (k+11))=true := by decide +kernel
private def part11_4 : List Nat := [16,17,18,19]
private theorem paidpart11_4 : part11_4.all (fun k => checkEnd 11 (k+11))=true := by decide +kernel
private def part11_5 : List Nat := [20,21,22,23]
private theorem paidpart11_5 : part11_5.all (fun k => checkEnd 11 (k+11))=true := by decide +kernel
private def part11_6 : List Nat := [24,25,26,27]
private theorem paidpart11_6 : part11_6.all (fun k => checkEnd 11 (k+11))=true := by decide +kernel
private def part11_7 : List Nat := [28,29,30,31]
private theorem paidpart11_7 : part11_7.all (fun k => checkEnd 11 (k+11))=true := by decide +kernel
private def part11_8 : List Nat := [32,33,34,35]
private theorem paidpart11_8 : part11_8.all (fun k => checkEnd 11 (k+11))=true := by decide +kernel
private def part11_9 : List Nat := [36,37,38,39]
private theorem paidpart11_9 : part11_9.all (fun k => checkEnd 11 (k+11))=true := by decide +kernel
private def part11_10 : List Nat := [40,41,42,43]
private theorem paidpart11_10 : part11_10.all (fun k => checkEnd 11 (k+11))=true := by decide +kernel
private def part11_11 : List Nat := [44,45,46,47]
private theorem paidpart11_11 : part11_11.all (fun k => checkEnd 11 (k+11))=true := by decide +kernel
private def part11_12 : List Nat := [48,49,50,51]
private theorem paidpart11_12 : part11_12.all (fun k => checkEnd 11 (k+11))=true := by decide +kernel
private def part11_13 : List Nat := [52,53]
private theorem paidpart11_13 : part11_13.all (fun k => checkEnd 11 (k+11))=true := by decide +kernel
theorem rank11 : checkedRank 11 = true := by
  unfold checkedRank
  have parts : List.range (maxY 11+2-11) = part11_0 ++ part11_1 ++ part11_2 ++ part11_3 ++ part11_4 ++ part11_5 ++ part11_6 ++ part11_7 ++ part11_8 ++ part11_9 ++ part11_10 ++ part11_11 ++ part11_12 ++ part11_13 := by decide +kernel
  rw [parts]
  simp only [List.all_append,paidpart11_0,paidpart11_1,paidpart11_2,paidpart11_3,paidpart11_4,paidpart11_5,paidpart11_6,paidpart11_7,paidpart11_8,paidpart11_9,paidpart11_10,paidpart11_11,paidpart11_12,paidpart11_13, Bool.true_and]
#print axioms rank11
end Koala6836.FastEnd
