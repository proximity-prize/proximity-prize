/- Bome2017, joint projection accounting for 68.36 after Lucieno and BitWonka. -/
/- Apache-2.0. Adapted from the accepted Bome2017 68.32 proof and the 69.69 genuine reduction, after Lucieno and BitWonka. -/
import ProximityPrize.SubmissionLower.KB36ScalarMethod
import Mathlib.Data.Nat.Choose.Bounds
namespace ProximityPrize.SubmissionLower.JointProtocol6836
open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem
open scoped NNReal
noncomputable section
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
local instance projectionFieldEq : DecidableEq IRSProfile.Field := Classical.decEq _
local instance projectionIndexEq : DecidableEq IRSProfile.Index := Classical.decEq _
/-- The projected-support (joint agreement) predicate is itself sufficient at the
new score and seed budget. This interface can use direct recovery of both words. -/
theorem word_list : IntermediateScalar.Words 181039 87312511777 := by
  intro u L code close
  exact IntermediateScalar.words_6842 u L code (fun c z => (show 180980≤181039 by decide).trans (close c z))

theorem protocol_of_projected (hgiven : AffineLineGivenSetsBound IRSProfile.baseCode (radius : ℝ) mcaBudget) :
    ProtocolClaim 6836 332210175 1073741824 where
  admissible := radius_admissible
  reduction := by
    change certifiedGammaError IRSProfile.code radius ≤ reductionTarget
    have proj : 15*(87312511777+1).choose 2 < Fintype.card IRSProfile.Field := by
      have lePow := Nat.mul_le_mul_left 15 (Nat.choose_le_pow (87312511777+1) 2)
      have small : 15 * ((87312511777+1 : ℕ)^2) < (2130706433 : ℕ)^6 := by decide +kernel
      exact lePow.trans_lt (small.trans_eq RCN284.field_cardinality.symm)
    have capacity : 2^(128:ℕ)*(mcaBudget+87312511777) ≤ Fintype.card IRSProfile.Field := by
      exact Koala6836.ProtocolInt.capacity.trans_eq RCN284.field_cardinality.symm
    simpa [reductionTarget,ProximityGap.prizeThreshold] using reduction_of_bounds hgiven _ word_list proj capacity
  score := score_target_le
#print axioms protocol_of_projected

end
end ProximityPrize.SubmissionLower.JointProtocol6836
