import ProximityPrize.SubmissionLower.ContactTwoTailFixedSelected6733Research
import ProximityPrize.SubmissionLower.ContactMovingProtocol6733Research
namespace ProximityPrize.SubmissionLower.ContactTwoTailClosure6733Research
open ProximityPrize.Benchmark
open ContactTwoTailFixedSelected6733Research
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
theorem alignmentBound6733_of_proper
    (proper:ProperStageProvider6733):
    AffineLineAlignmentBound IRSProfile.baseCode 80102 274980727208431873:=by
  have h:=ContactAlignmentBridge.alignmentBound_of_selected_count
    IRSProfile.domain 131071 80102 274980727208431873
    (ContactTwoTailStackedSelectedBound6733Research.selectedNoLargePencilBound6733_of_fixedProvider
        (fixedCellCountProvider_of_proper proper))
  simpa [IRSProfile.baseCode,IRSProfile.baseDimension] using h
theorem protocolClaim6733_of_proper
    (proper:ProperStageProvider6733):
    ProtocolClaim 6734 10253183 33554432:=
  ContactMovingProtocol6733Research.protocolClaim6733_of_alignment
    (alignmentBound6733_of_proper proper)
end
end ProximityPrize.SubmissionLower.ContactTwoTailClosure6733Research
