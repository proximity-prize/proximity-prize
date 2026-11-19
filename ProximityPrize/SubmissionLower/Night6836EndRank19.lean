/- Apache-2.0. Original retuned 68.36 gate checks at rank 19. -/
import ProximityPrize.SubmissionLower.Night6836EndCore
namespace Koala6836.FastEnd
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def part19_0 : List Nat := [0]
private theorem paidpart19_0 : part19_0.all (fun k => checkEnd 19 (k+19))=true := by decide +kernel
theorem rank19 : checkedRank 19 = true := by
  unfold checkedRank
  have parts : List.range (maxY 19+2-19) = part19_0 := by decide +kernel
  rw [parts]
  exact paidpart19_0
#print axioms rank19
end Koala6836.FastEnd
