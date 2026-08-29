import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingFixedSelected6732Research
import ProximityPrize.SubmissionLower.ContactMovingStackedSelectedBound6732Research
import ProximityPrize.SubmissionLower.ContactMovingProtocol6732Research

/-! Premise-free assembly of the fixed cell, stacked residual cells, and protocol. -/
namespace ProximityPrize.SubmissionLower.ContactMovingClosure6732Research

open ProximityPrize.Benchmark
open ContactMovingFixedProfile6732Research
open ContactMovingFixedSelected6732Research
open ContactMovingStackedSelectedBound6732Research

noncomputable section
set_option maxRecDepth 30000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _

theorem fixedCellCountProvider6732 : FixedCellCountProvider6732 := by
  intro Q hQ hbox Hsupport selected Δ u0 u1 hsolution hdegree hagreement hnoPencil
  letI : CharP IRSProfile.Field prime := by
    simpa [prime, ContactParameters6600Research.prime] using
      ContactFrozenAlignment6600Research.challenge_field_characteristic6600
  have h := fixed_selected_count_le Q hQ hbox Hsupport selected Δ
    (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by norm_num [IRSProfile.Index, fixedProfile])
    hdegree hsolution hagreement hnoPencil
  simpa [ContactMovingParameters6732Research.fixedCost] using h

theorem alignmentBound6732 :
    AffineLineAlignmentBound IRSProfile.baseCode 80082 274980727111395087 := by
  have h := ContactAlignmentBridge.alignmentBound_of_selected_count
    IRSProfile.domain 131071 80082 274980727111395087
    (selectedNoLargePencilBound6732_of_fixedProvider fixedCellCountProvider6732)
  simpa [IRSProfile.baseCode, IRSProfile.baseDimension] using h

theorem protocolClaim6732 : ProtocolClaim 6732 10250623 33554432 :=
  ContactMovingProtocol6732Research.protocolClaim6732_of_alignment alignmentBound6732

#print axioms protocolClaim6732

end
end ProximityPrize.SubmissionLower.ContactMovingClosure6732Research
