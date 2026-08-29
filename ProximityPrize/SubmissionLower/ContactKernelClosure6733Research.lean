import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactKernelSelectedBound6733Research
import ProximityPrize.SubmissionLower.ContactKernelProtocol6733Research
namespace ProximityPrize.SubmissionLower.ContactKernelClosure6733Research
open ProximityPrize.Benchmark
open ContactKernelArithmetic6733Research
open ContactKernelSelectedBound6733Research
noncomputable section
local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
theorem alignmentBound6733 :
    AffineLineAlignmentBound IRSProfile.baseCode errors budget := by
  have h := ContactAlignmentBridge.alignmentBound_of_selected_count
    IRSProfile.domain w errors budget selectedNoLargePencilBound6733
  simpa [IRSProfile.baseCode,IRSProfile.baseDimension,w] using h
theorem protocolClaim6733 : ProtocolClaim 6733 10251903 33554432 :=
  ContactKernelProtocol6733Research.protocolClaim6733_of_alignment
    alignmentBound6733
#print axioms protocolClaim6733
end
end ProximityPrize.SubmissionLower.ContactKernelClosure6733Research
