import ProximityPrize.SubmissionLower.R6960Front6960List
import ProximityPrize.SubmissionLower.R6960Front6960HighCount
import ProximityPrize.SubmissionLower.R6960Front6960Rank2
import ProximityPrize.SubmissionLower.R6960Front6960Rank3
import ProximityPrize.SubmissionLower.R6960Front6960Rank4
import ProximityPrize.SubmissionLower.R6960Front6960Rank5
import ProximityPrize.SubmissionLower.R6960Low6960Count

set_option Elab.async false
namespace Lower6960
open ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower.Front6960Radius (p q)

theorem low_front_count : Front6960.c6 := by
  intro _ _ M _ F lo hi
  exact Low.count M F lo hi

/-- The 69.60 claim at the greatest allowed radius in its error cell follows
from the uniform positive-height count above the verified low endpoint. -/
theorem protocol_claim
    (high : ∀ {u deleted Γ} (M : P1.ModelAt 33561 u deleted) (_F : P1.FamilyAt 179827 M Γ),
      2339 ≤ M.overhead → M.overhead ≤ 33561 → Γ.card ≤ 266695718139456639) :
    ProtocolClaim 6960 p q := by
  apply ProximityPrize.SubmissionLower.Front6960Radius.extend
  apply Front6960.of_children Front6960ListBank.scalar_list
    Front6960_1.proof Front6960_2.proof
    (Front6960_3.of_children Front6960_3_1.proof Front6960_3_2.proof)
    (Front6960_4.of_children Front6960_4_1.proof Front6960_4_2.proof)
    Front6960_5.proof low_front_count
  intro _ _ M _ F lo hi
  exact high M F lo hi

/-- All numerical and front-end parts of the claim are closed. The one
remaining input is the bound for the actual simple marked sheets. -/
theorem protocol_claim_of_retained (retained : RetainedCount) : ProtocolClaim 6960 p q :=
  protocol_claim (fun M F lo hi => high_count_of_retained retained M F lo hi)

#print axioms protocol_claim_of_retained
#print axioms low_front_count
#print axioms protocol_claim
end Lower6960
