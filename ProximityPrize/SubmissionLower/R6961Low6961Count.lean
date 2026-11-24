import ProximityPrize.SubmissionLower.R6961Low6961CountCore
import ProximityPrize.SubmissionLower.R6961Low6961Tiles0
import ProximityPrize.SubmissionLower.R6961Low6961Tiles1
import ProximityPrize.SubmissionLower.R6961Low6961Tiles2
import ProximityPrize.SubmissionLower.R6961Low6961Tiles3
import ProximityPrize.SubmissionLower.R6961Low6961Tiles4
import ProximityPrize.SubmissionLower.R6961Low6961Tiles5
import ProximityPrize.SubmissionLower.R6961Low6961Tiles6
import ProximityPrize.SubmissionLower.R6961Low6961Tiles7
import ProximityPrize.SubmissionLower.R6961Low6961Tiles8
import ProximityPrize.SubmissionLower.R6961Low6961Tiles9
import ProximityPrize.SubmissionLower.R6961Low6961Tiles10
import ProximityPrize.SubmissionLower.R6961Low6961Tiles11
import ProximityPrize.SubmissionLower.R6961Low6961Tiles12
import ProximityPrize.SubmissionLower.R6961Low6961Tiles13
import ProximityPrize.SubmissionLower.R6961Low6961Tiles14
import ProximityPrize.SubmissionLower.R6961Low6961Tiles15

set_option Elab.async false

namespace Lower6961.Low
open Low6961Allocation (Band Receipt)

private theorem certified (k : Band) : Nonempty (Receipt k) := by
  fin_cases k
  · exact ⟨Low6961Allocation.Group0.receipt⟩
  · exact ⟨Low6961Allocation.Group1.receipt⟩
  · exact ⟨Low6961Allocation.Group2.receipt⟩
  · exact ⟨Low6961Allocation.Group3.receipt⟩
  · exact ⟨Low6961Allocation.Group4.receipt⟩
  · exact ⟨Low6961Allocation.Group5.receipt⟩
  · exact ⟨Low6961Allocation.Group6.receipt⟩
  · exact ⟨Low6961Allocation.Group7.receipt⟩
  · exact ⟨Low6961Allocation.Group8.receipt⟩
  · exact ⟨Low6961Allocation.Group9.receipt⟩
  · exact ⟨Low6961Allocation.Group10.receipt⟩
  · exact ⟨Low6961Allocation.Group11.receipt⟩
  · exact ⟨Low6961Allocation.Group12.receipt⟩
  · exact ⟨Low6961Allocation.Group13.receipt⟩
  · exact ⟨Low6961Allocation.Group14.receipt⟩
  · exact ⟨Low6961Allocation.Group15.receipt⟩

private noncomputable def receipts (k : Band) : Receipt k := Classical.choice (certified k)

/-- The 69.60 count for the actual family at every positive height through 2326. -/
theorem count {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt 179818 M Γ) (lo : 1≤M.overhead) (hi : M.overhead≤2326) :
    Γ.card≤265959947636540641 :=
  count_with_receipts receipts M F lo hi

#print axioms count
end Lower6961.Low
