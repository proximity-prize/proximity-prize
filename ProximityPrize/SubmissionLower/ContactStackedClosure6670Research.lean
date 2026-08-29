import ProximityPrize.SubmissionLower.ContactStackedSelectedBound6670Research
import ProximityPrize.SubmissionLower.ContactFixedSelectedCell6670Research
import ProximityPrize.SubmissionLower.ContactSeedlessProtocolResearch

/-!
# Premise-free stacked 67.40 closure

This module supplies the sole fixed-cell premise of the selected-family
composition from the completed sharp-YZ fixed-meet theorem.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedClosure6670Research

open ProximityPrize.Benchmark
open ContactAlignmentBridge
open ContactFixedMeetProfile6670Research
open ContactFixedSelectedCell6670Research
open ContactStackedSelectedBound6670Research
open ContactSeedlessProtocolResearch

noncomputable section

abbrev GlobalPoly := MvPolynomial (Fin 4) IRSProfile.Field

theorem selectedNoLargePencilBound6670 :
    SelectedNoLargePencilBound
      IRSProfile.domain 131071 80162 274980727111395087 :=
  selectedNoLargePencilBound_of_fixedCellCountProvider6670
    fixedCell_count_lt_fixedCost

theorem protocolClaim6740 : ProtocolClaim 6740 320651 1048576 := by
  have halign :
      AffineLineAlignmentBound
        IRSProfile.baseCode
        ContactScore6630Research.errors6630
        ContactSeedlessProtocolResearch.mcaBudget := by
    change AffineLineAlignmentBound IRSProfile.baseCode 80162 274980727111395087
    apply affineLineAlignmentBound_of_selectedNoLargePencilBound
      IRSProfile.domain 131071 80162 274980727111395087
      IRSProfile.baseNttDomain.primitive.injOn_rootsOfUnity
      (by norm_num [IRSProfile.domain_card_eq_n, ContactFixedMeetProfile6670Research.fixedProfile])
      (by norm_num [ContactFixedMeetProfile6670Research.fixedProfile])
      (by norm_num [ContactFixedMeetProfile6670Research.fixedProfile])
    exact selectedNoLargePencilBound6670
  exact protocolClaim6740_of_alignment halign

theorem protocolClaim6750 : ProtocolClaim 6740 320651 1048576 :=
  protocolClaim6740

end

end ProximityPrize.SubmissionLower.ContactStackedClosure6670Research
