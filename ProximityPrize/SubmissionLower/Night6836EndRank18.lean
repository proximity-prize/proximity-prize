/- Apache-2.0. Original retuned 68.36 gate checks at rank 18. -/
import ProximityPrize.SubmissionLower.Night6836EndCore
namespace Koala6836.FastEnd
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def part18_0 : List Nat := [0,1,2,3]
private theorem paidpart18_0 : part18_0.all (fun k => checkEnd 18 (k+18))=true := by decide +kernel
private def part18_1 : List Nat := [4,5,6,7]
private theorem paidpart18_1 : part18_1.all (fun k => checkEnd 18 (k+18))=true := by decide +kernel
private def part18_2 : List Nat := [8,9]
private theorem paidpart18_2 : part18_2.all (fun k => checkEnd 18 (k+18))=true := by decide +kernel
theorem rank18 : checkedRank 18 = true := by
  unfold checkedRank
  have parts : List.range (maxY 18+2-18) = part18_0 ++ part18_1 ++ part18_2 := by decide +kernel
  rw [parts]
  simp only [List.all_append,paidpart18_0,paidpart18_1,paidpart18_2, Bool.true_and]
#print axioms rank18
end Koala6836.FastEnd
