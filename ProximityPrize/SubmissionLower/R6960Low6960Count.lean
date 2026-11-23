import ProximityPrize.SubmissionLower.R6960Low6960CountCore
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0
import ProximityPrize.SubmissionLower.R6960Low6960Tiles1
import ProximityPrize.SubmissionLower.R6960Low6960Tiles2
import ProximityPrize.SubmissionLower.R6960Low6960Tiles3
import ProximityPrize.SubmissionLower.R6960Low6960Tiles4
import ProximityPrize.SubmissionLower.R6960Low6960Tiles5
import ProximityPrize.SubmissionLower.R6960Low6960Tiles6
import ProximityPrize.SubmissionLower.R6960Low6960Tiles7
import ProximityPrize.SubmissionLower.R6960Low6960Tiles8
import ProximityPrize.SubmissionLower.R6960Low6960Tiles9
import ProximityPrize.SubmissionLower.R6960Low6960Tiles10
import ProximityPrize.SubmissionLower.R6960Low6960Tiles11
import ProximityPrize.SubmissionLower.R6960Low6960Tiles12
import ProximityPrize.SubmissionLower.R6960Low6960Tiles13
import ProximityPrize.SubmissionLower.R6960Low6960Tiles14

set_option Elab.async false

namespace Lower6960.Low
open Low6960Allocation (Band Receipt)

private theorem certified (k : Band) : Nonempty (Receipt k) := by
  fin_cases k
  · exact ⟨Low6960Allocation.Group0.receipt⟩
  · exact ⟨Low6960Allocation.Group1.receipt⟩
  · exact ⟨Low6960Allocation.Group2.receipt⟩
  · exact ⟨Low6960Allocation.Group3.receipt⟩
  · exact ⟨Low6960Allocation.Group4.receipt⟩
  · exact ⟨Low6960Allocation.Group5.receipt⟩
  · exact ⟨Low6960Allocation.Group6.receipt⟩
  · exact ⟨Low6960Allocation.Group7.receipt⟩
  · exact ⟨Low6960Allocation.Group8.receipt⟩
  · exact ⟨Low6960Allocation.Group9.receipt⟩
  · exact ⟨Low6960Allocation.Group10.receipt⟩
  · exact ⟨Low6960Allocation.Group11.receipt⟩
  · exact ⟨Low6960Allocation.Group12.receipt⟩
  · exact ⟨Low6960Allocation.Group13.receipt⟩
  · exact ⟨Low6960Allocation.Group14.receipt⟩

private noncomputable def receipts (k : Band) : Receipt k := Classical.choice (certified k)

/-- The 69.60 count for the actual family at every positive height through 2338. -/
theorem count {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt 179827 M Γ) (lo : 1≤M.overhead) (hi : M.overhead≤2338) :
    Γ.card≤266695718139456639 :=
  count_with_receipts receipts M F lo hi

#print axioms count
end Lower6960.Low
