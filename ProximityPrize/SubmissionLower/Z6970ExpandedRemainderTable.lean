import ProximityPrize.SubmissionLower.Z6970ExpandedRemainderCompute

set_option Elab.async false
set_option autoImplicit false

namespace ExpandedTaper6970
open scoped BigOperators

def remainderChunk (lo n : ℕ) : ℕ :=
  TaperBudget.sumRange (fun q => remainderRow (lo+q)) n

theorem remainderChunk_add (lo a b : ℕ) :
    remainderChunk lo (a+b) = remainderChunk lo a + remainderChunk (lo+a) b := by
  simp only [remainderChunk, TaperBudget.sumRange_eq, Finset.sum_range_add, Nat.add_assoc]

theorem remainderChunk_plateau : remainderChunk 1679 (3514-1679) = 0 := by
  rw [remainderChunk, TaperBudget.sumRange_eq]
  apply Finset.sum_eq_zero
  intro q hq
  have hq' := Finset.mem_range.mp hq
  have h : 1679 ≤ 1679+q ∧ 1679+q < 3514 := by omega
  simp [remainderRow,h]

end ExpandedTaper6970
