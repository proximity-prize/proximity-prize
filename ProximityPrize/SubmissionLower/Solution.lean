import ProximityPrize.SubmissionLower.ContactMovingFixedSelected
import ProximityPrize.SubmissionLower.ContactMovingStackedSelectedBound
import ProximityPrize.SubmissionLower.ContactMovingProtocol

namespace ProximityPrize.SubmissionLower.ContactMovingClosure

open ProximityPrize.Benchmark
open ContactMovingFixedProfile
open ContactMovingFixedSelected
open ContactMovingStackedSelectedBound

noncomputable section
set_option maxRecDepth 30000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

theorem fixedCellCountProvider6732 : FixedCellCountProvider6732 := by
  intro Q hQ hbox Hsupport selected Δ u0 u1 hsolution hdegree hagreement hnoPencil
  letI : CharP IRSProfile.Field ContactMovingParameters.prime := by
    simpa [ContactParameters.prime, ContactMovingParameters.prime] using
      ContactMovingStackedResidualCells.challenge_field_characteristic6600
  have h := fixed_selected_count_le Q hQ hbox Hsupport selected Δ
    (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by norm_num [IRSProfile.Index, fixedProfile])
    hdegree hsolution hagreement hnoPencil
  simpa [ContactMovingParameters.fixedCost] using h

theorem alignmentBound6732 :
    AffineLineAlignmentBound IRSProfile.baseCode 80082 274980727111395087 := by
  have h := ContactAlignmentBridge.alignmentBound_of_selected_count
    IRSProfile.domain 131071 80082 274980727111395087
    (selectedNoLargePencilBound6732_of_fixedProvider fixedCellCountProvider6732)
  simpa [IRSProfile.baseCode, IRSProfile.baseDimension] using h

end
end ProximityPrize.SubmissionLower.ContactMovingClosure

namespace ProximityPrize.Benchmark

theorem candidate : ProtocolClaim 6732 10250623 33554432 :=
  ProximityPrize.SubmissionLower.ContactMovingProtocol.protocolClaim6732_of_alignment
    ProximityPrize.SubmissionLower.ContactMovingClosure.alignmentBound6732

end ProximityPrize.Benchmark
