/- Apache-2.0. Original retuned 68.36 gate checks at rank 17. -/
import ProximityPrize.SubmissionLower.Night6836EndCore
namespace Koala6836.FastEnd
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def part17_0 : List Nat := [0,1,2,3]
private theorem paidpart17_0 : part17_0.all (fun k => checkEnd 17 (k+17))=true := by decide +kernel
private def part17_1 : List Nat := [4,5,6,7]
private theorem paidpart17_1 : part17_1.all (fun k => checkEnd 17 (k+17))=true := by decide +kernel
private def part17_2 : List Nat := [8,9,10,11]
private theorem paidpart17_2 : part17_2.all (fun k => checkEnd 17 (k+17))=true := by decide +kernel
private def part17_3 : List Nat := [12,13,14,15]
private theorem paidpart17_3 : part17_3.all (fun k => checkEnd 17 (k+17))=true := by decide +kernel
private def part17_4 : List Nat := [16,17,18,19]
private theorem paidpart17_4 : part17_4.all (fun k => checkEnd 17 (k+17))=true := by decide +kernel
theorem rank17 : checkedRank 17 = true := by
  unfold checkedRank
  have parts : List.range (maxY 17+2-17) = part17_0 ++ part17_1 ++ part17_2 ++ part17_3 ++ part17_4 := by decide +kernel
  rw [parts]
  simp only [List.all_append,paidpart17_0,paidpart17_1,paidpart17_2,paidpart17_3,paidpart17_4, Bool.true_and]
#print axioms rank17
end Koala6836.FastEnd
