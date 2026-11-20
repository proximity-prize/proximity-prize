/- Apache-2.0. Original retuned 68.36 gate checks at rank 16. -/
import ProximityPrize.SubmissionLower.Night6836EndCore
namespace Koala6836.FastEnd
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def part16_0 : List Nat := [0,1,2,3]
private theorem paidpart16_0 : part16_0.all (fun k => checkEnd 16 (k+16))=true := by decide +kernel
private def part16_1 : List Nat := [4,5,6,7]
private theorem paidpart16_1 : part16_1.all (fun k => checkEnd 16 (k+16))=true := by decide +kernel
private def part16_2 : List Nat := [8,9,10,11]
private theorem paidpart16_2 : part16_2.all (fun k => checkEnd 16 (k+16))=true := by decide +kernel
private def part16_3 : List Nat := [12,13,14,15]
private theorem paidpart16_3 : part16_3.all (fun k => checkEnd 16 (k+16))=true := by decide +kernel
private def part16_4 : List Nat := [16,17,18,19]
private theorem paidpart16_4 : part16_4.all (fun k => checkEnd 16 (k+16))=true := by decide +kernel
private def part16_5 : List Nat := [20,21,22,23]
private theorem paidpart16_5 : part16_5.all (fun k => checkEnd 16 (k+16))=true := by decide +kernel
private def part16_6 : List Nat := [24,25,26,27]
private theorem paidpart16_6 : part16_6.all (fun k => checkEnd 16 (k+16))=true := by decide +kernel
theorem rank16 : checkedRank 16 = true := by
  unfold checkedRank
  have parts : List.range (maxY 16+2-16) = part16_0 ++ part16_1 ++ part16_2 ++ part16_3 ++ part16_4 ++ part16_5 ++ part16_6 := by decide +kernel
  rw [parts]
  simp only [List.all_append,paidpart16_0,paidpart16_1,paidpart16_2,paidpart16_3,paidpart16_4,paidpart16_5,paidpart16_6, Bool.true_and]
#print axioms rank16
end Koala6836.FastEnd
