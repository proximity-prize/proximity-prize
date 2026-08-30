import ProximityPrize.SubmissionLower.RFreeScaledJetBridge

set_option autoImplicit true

section
namespace ProximityPrize.SubmissionLower.ContactTwoTailClosure6735Research
open ProximityPrize.Benchmark
open ContactTwoTailFixedSelected6735Research
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
theorem alignmentBound6733_of_proper
    (proper:ProperStageProvider6733):
    AffineLineAlignmentBound IRSProfile.baseCode 80161 274980727143946195:=by
  have h:=ContactAlignmentBridge.alignmentBound_of_selected_count
    IRSProfile.domain 131071 80161 274980727143946195
    (ContactTwoTailStackedSelectedBound6735Research.selectedNoLargePencilBound6735_of_fixedProvider
        (fixedCellCountProvider_of_proper proper))
  simpa [IRSProfile.baseCode,IRSProfile.baseDimension] using h
theorem protocolClaim6733_of_proper
    (proper:ProperStageProvider6733):
    ProtocolClaim 6740 10260735 33554432:=
  ContactMovingProtocol6735Research.protocolClaim6735_of_alignment
    (alignmentBound6733_of_proper proper)
end
end ProximityPrize.SubmissionLower.ContactTwoTailClosure6735Research
end
section
namespace ProximityPrize.SubmissionLower.ContactTwoTailUnconditional6735Research
open ProximityPrize.Benchmark
open ContactTwoTailFixedSelected6735Research
open ContactProperStageActiveProvider6735Research
open ContactProperStageActiveFixedPowers6735Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem properStageProvider6733:ProperStageProvider6733:=
  properStageProvider6733_of_activeFixedPowers activeStageFixedPowerProvider6733
theorem protocolClaim6733:ProtocolClaim 6740 10260735 33554432:=
  ContactTwoTailClosure6735Research.protocolClaim6733_of_proper properStageProvider6733
end
end ProximityPrize.SubmissionLower.ContactTwoTailUnconditional6735Research
end
