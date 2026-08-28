import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactGlobalSelectedCount6533
import ProximityPrize.SubmissionLower.ContactFrozenAlignment6533

/-!
# Unconditional alignment at 78,455 errors with the maximal safe seed budget

The constructed order-22 interpolant and the unconditional characteristic-free
global-shear selected-count theorem are connected here to the unchanged stock
alignment interface.  No geometric, counting, or alignment premise remains.
-/

namespace ProximityPrize.SubmissionLower.ContactAlignment6533

open ProximityPrize.Benchmark
open ContactParameters6533 ContactFrozenAlignment6533
open ContactGlobalSelectedCount6533

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

theorem interpolant_selected_count6533 : InterpolantSelectedCount6533 := by
  classical
  letI : CharP IRSProfile.Field prime := challenge_field_characteristic6533
  intro Q hQ hbox hfull selected seeds u0 u1 hdegree hsolution hagreement hnoPencil
  exact global_selected_count6533 IRSProfile.Field Q hQ hbox hfull selected seeds
    (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by norm_num [IRSProfile.Index, n]) hdegree hsolution hagreement hnoPencil

/-- The exact stock-code alignment predicate at the 65.67 radius. -/
theorem alignment6533 :
    AffineLineAlignmentBound IRSProfile.baseCode errors alignmentBudget :=
  alignment_of_interpolant_count6533 interpolant_selected_count6533

end
end ProximityPrize.SubmissionLower.ContactAlignment6533

#print axioms ProximityPrize.SubmissionLower.ContactAlignment6533.interpolant_selected_count6533
#print axioms ProximityPrize.SubmissionLower.ContactAlignment6533.alignment6533
