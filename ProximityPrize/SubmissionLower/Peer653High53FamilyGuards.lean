import ProximityPrize.SubmissionLower.Peer653High53FamilyInventory

-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229Family.lean.

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

section
namespace Peer653High53
open Peer653High53 (Band agreement p)
theorem grades_checked (b : Band) :
    AllGrades (start b) (finish b) (terminal b).shape.U (retainedCap b) 1 (grades b) := by
  cases b <;>
    repeat' refine And.intro (GradeOK.mk (by decide) (by decide) (by decide) (by decide +kernel)) ?_
  all_goals trivial
theorem grade_checked (b : Band) (i : Fin (grades b).length) :
    GradeOK (start b) (finish b) (terminal b).shape.U (retainedCap b) (i.val+1) ((grades b).get i) :=
  get_grade _ _ (grades_checked b) i
theorem terminal_guards (b : Band) :
    0 < (start b) ∧ (finish b) ≤ heightCap ∧ 0 < (terminal b).shape.m * agreement ∧
    (terminal b).shape.m * agreement < p ∧
    (terminal b).shape.B * (131071-(start b)) ≤ (terminal b).shape.m*agreement := by
  cases b <;> decide +kernel
end Peer653High53
end
