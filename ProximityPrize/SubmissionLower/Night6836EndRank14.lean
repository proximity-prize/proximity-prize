/- Apache-2.0. Original retuned 68.36 gate checks at rank 14. -/
import ProximityPrize.SubmissionLower.Night6836EndCore
namespace Koala6836.FastEnd
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def part14_0 : List Nat := [0,1,2,3]
private theorem paidpart14_0 : part14_0.all (fun k => checkEnd 14 (k+14))=true := by decide +kernel
private def part14_1 : List Nat := [4,5,6,7]
private theorem paidpart14_1 : part14_1.all (fun k => checkEnd 14 (k+14))=true := by decide +kernel
private def part14_2 : List Nat := [8,9,10,11]
private theorem paidpart14_2 : part14_2.all (fun k => checkEnd 14 (k+14))=true := by decide +kernel
private def part14_3 : List Nat := [12,13,14,15]
private theorem paidpart14_3 : part14_3.all (fun k => checkEnd 14 (k+14))=true := by decide +kernel
private def part14_4 : List Nat := [16,17,18,19]
private theorem paidpart14_4 : part14_4.all (fun k => checkEnd 14 (k+14))=true := by decide +kernel
private def part14_5 : List Nat := [20,21,22,23]
private theorem paidpart14_5 : part14_5.all (fun k => checkEnd 14 (k+14))=true := by decide +kernel
private def part14_6 : List Nat := [24,25,26,27]
private theorem paidpart14_6 : part14_6.all (fun k => checkEnd 14 (k+14))=true := by decide +kernel
private def part14_7 : List Nat := [28,29,30,31]
private theorem paidpart14_7 : part14_7.all (fun k => checkEnd 14 (k+14))=true := by decide +kernel
private def part14_8 : List Nat := [32,33,34,35]
private theorem paidpart14_8 : part14_8.all (fun k => checkEnd 14 (k+14))=true := by decide +kernel
private def part14_9 : List Nat := [36,37,38,39]
private theorem paidpart14_9 : part14_9.all (fun k => checkEnd 14 (k+14))=true := by decide +kernel
private def part14_10 : List Nat := [40,41]
private theorem paidpart14_10 : part14_10.all (fun k => checkEnd 14 (k+14))=true := by decide +kernel
theorem rank14 : checkedRank 14 = true := by
  unfold checkedRank
  have parts : List.range (maxY 14+2-14) = part14_0 ++ part14_1 ++ part14_2 ++ part14_3 ++ part14_4 ++ part14_5 ++ part14_6 ++ part14_7 ++ part14_8 ++ part14_9 ++ part14_10 := by decide +kernel
  rw [parts]
  simp only [List.all_append,paidpart14_0,paidpart14_1,paidpart14_2,paidpart14_3,paidpart14_4,paidpart14_5,paidpart14_6,paidpart14_7,paidpart14_8,paidpart14_9,paidpart14_10, Bool.true_and]
#print axioms rank14
end Koala6836.FastEnd
