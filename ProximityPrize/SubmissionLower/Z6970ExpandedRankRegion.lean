import ProximityPrize.SubmissionLower.Z6970ExpandedRankBudget

set_option Elab.async false
set_option autoImplicit false

namespace ExpandedTaper6970

def plateau (i : BlockIndex) : Prop := 1679 ≤ i.1.val ∧ i.1.val < 3514

instance (i : BlockIndex) : Decidable (plateau i) := by
  unfold plateau
  infer_instance

end ExpandedTaper6970
