/- Apache-2.0. Original retuned 68.36 gate checks at rank 15. -/
import ProximityPrize.SubmissionLower.Night6836EndCore
namespace Koala6836.FastEnd
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def part15_0 : List Nat := [0,1,2,3]
private theorem paidpart15_0 : part15_0.all (fun k => checkEnd 15 (k+15))=true := by decide +kernel
private def part15_1 : List Nat := [4,5,6,7]
private theorem paidpart15_1 : part15_1.all (fun k => checkEnd 15 (k+15))=true := by decide +kernel
private def part15_2 : List Nat := [8,9,10,11]
private theorem paidpart15_2 : part15_2.all (fun k => checkEnd 15 (k+15))=true := by decide +kernel
private def part15_3 : List Nat := [12,13,14,15]
private theorem paidpart15_3 : part15_3.all (fun k => checkEnd 15 (k+15))=true := by decide +kernel
private def part15_4 : List Nat := [16,17,18,19]
private theorem paidpart15_4 : part15_4.all (fun k => checkEnd 15 (k+15))=true := by decide +kernel
private def part15_5 : List Nat := [20,21,22,23]
private theorem paidpart15_5 : part15_5.all (fun k => checkEnd 15 (k+15))=true := by decide +kernel
private def part15_6 : List Nat := [24,25,26,27]
private theorem paidpart15_6 : part15_6.all (fun k => checkEnd 15 (k+15))=true := by decide +kernel
private def part15_7 : List Nat := [28,29,30,31]
private theorem paidpart15_7 : part15_7.all (fun k => checkEnd 15 (k+15))=true := by decide +kernel
private def part15_8 : List Nat := [32,33,34,35]
private theorem paidpart15_8 : part15_8.all (fun k => checkEnd 15 (k+15))=true := by decide +kernel
theorem rank15 : checkedRank 15 = true := by
  unfold checkedRank
  have parts : List.range (maxY 15+2-15) = part15_0 ++ part15_1 ++ part15_2 ++ part15_3 ++ part15_4 ++ part15_5 ++ part15_6 ++ part15_7 ++ part15_8 := by decide +kernel
  rw [parts]
  simp only [List.all_append,paidpart15_0,paidpart15_1,paidpart15_2,paidpart15_3,paidpart15_4,paidpart15_5,paidpart15_6,paidpart15_7,paidpart15_8, Bool.true_and]
#print axioms rank15
end Koala6836.FastEnd
