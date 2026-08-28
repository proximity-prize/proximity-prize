import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactGlobalSelectedCount
import ProximityPrize.SubmissionLower.ContactFrozenAlignment6454

/-!
# Unconditional alignment at 77324 errors with seed budget 10^17

Model label: gpt-5.

The actual global selected-family theorem, freshly compiled against the
conservative 6454 parameter instance, supplies the exact interpolation
count. The new frontend constructs the nonzero interpolant on the
caller's original supports and applies the unchanged generic stock-code
bridge. No geometric, selected-count, or alignment premise remains.

This module proves alignment only. It is not a new ProtocolClaim, complete
candidate source-policy approval, independent benchmark, or submission.
-/

namespace ProximityPrize.SubmissionLower.ContactAlignment6454

open ProximityPrize.Benchmark
open ContactAlignmentParameters ContactAlignmentBridge ContactFrozenAlignment6454
open ContactGlobalSelectedCount

noncomputable section

theorem interpolant_selected_count6454 : InterpolantSelectedCount6454 := by
  classical
  letI : CharP IRSProfile.Field prime := challenge_field_characteristic
  intro Q hQ hbox selected seeds u₀ u₁ hdegree hsolution hagreement hnoPencil
  exact global_selected_count IRSProfile.Field Q hQ hbox selected seeds
    (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain u₀ u₁
    IRSProfile.domain.injective.injOn
    (by norm_num [IRSProfile.Index, n]) hdegree hsolution hagreement hnoPencil

theorem selected_no_large_pencil_bound6454 : SelectedNoLargePencilBound6454 :=
  selected_count_of_interpolant_count interpolant_selected_count6454

/-- The exact unmodified stock alignment predicate, with no remaining
counting, interpolation, or geometric hypothesis. -/
theorem alignment6454 :
    AffineLineAlignmentBound IRSProfile.baseCode 77324 100000000000000000 :=
  alignment_of_interpolant_count interpolant_selected_count6454

#print axioms interpolant_selected_count6454
#print axioms selected_no_large_pencil_bound6454
#print axioms alignment6454

end
end ProximityPrize.SubmissionLower.ContactAlignment6454
