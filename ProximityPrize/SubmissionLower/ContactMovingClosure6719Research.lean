import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingFixedSelected6719Research
import ProximityPrize.SubmissionLower.ContactMovingStackedSelectedBound6719Research

namespace ProximityPrize.SubmissionLower.ContactMovingClosure6719Research

open ProximityPrize.Benchmark
open ContactMovingFixedProfile6719Research ContactMovingFixedSelected6719Research
open ContactMovingStackedSelectedBound6719Research

noncomputable section
set_option maxRecDepth 20000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

/-- .
 -/
theorem fixedCellCountProvider6719 : FixedCellCountProvider6719 := by
  intro Q hQ hbox Hsupport selected Δ u0 u1 hsolution hdegree hagreement hnoPencil
  letI : CharP IRSProfile.Field prime := by
    simpa [prime, ContactParameters6600Research.prime] using
      ContactFrozenAlignment6600Research.challenge_field_characteristic6600
  exact fixed_selected_count_le Q hQ hbox Hsupport selected Δ
    (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by norm_num [IRSProfile.Index, fixedProfile])
    hdegree hsolution hagreement hnoPencil

theorem protocolClaim6719 : ProtocolClaim 6719 319823 1048576 :=
  protocolClaim6719_of_fixedProvider fixedCellCountProvider6719

end

end ProximityPrize.SubmissionLower.ContactMovingClosure6719Research
