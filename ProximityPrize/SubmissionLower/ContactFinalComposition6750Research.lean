import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSelectedInterpolationProvider6750Research
import ProximityPrize.SubmissionLower.ContactOldCoreHighTEquationProvider6750Research
import ProximityPrize.SubmissionLower.ContactLegacyCanonicalAnchoredZero6750Research

 







namespace ProximityPrize.SubmissionLower
namespace ContactFinalComposition6750Research

open ProximityPrize.Benchmark
open ContactSelectedCount6750Research
open ContactSelectedCountHighTRepair6750Research
open ContactSelectedInterpolationProvider6750Research
open ContactOldCoreHighTEquationProvider6750Research
open ContactLegacyOldGCountProvider6750Research
open ContactLegacyCanonicalAnchoredZero6750Research

set_option autoImplicit false

 

theorem semanticSelectedCount6750_of_ledgers
    (hardLedger : LegacyOldGLedger6750)
    (directLedger : DirectOldGLedger6750) : SemanticSelectedCount6750 :=
  semanticSelectedCount6750_of_highT_split
    closedSelectedInterpolantsProvider6750
    highTOldGEquationProvider6750
    (legacyOldGCountProvider6750_of_receipts
      canonicalZeroCountProvider6750_closed hardLedger directLedger)

 
theorem selectedNoLargePencilBound6750_of_ledgers
    (hardLedger : LegacyOldGLedger6750)
    (directLedger : DirectOldGLedger6750) :
    ContactMovingProtocol6750Research.SelectedNoLargePencilBound6750 :=
  selectedNoLargePencilBound6750_of_semantic
    (semanticSelectedCount6750_of_ledgers hardLedger directLedger)

 

theorem protocolClaim6750_of_ledgers
    (hardLedger : LegacyOldGLedger6750)
    (directLedger : DirectOldGLedger6750) :
    ProtocolClaim 6751 10274687 33554432 :=
  ContactMovingProtocol6750Research.protocolClaim6750_of_selected_count
    (selectedNoLargePencilBound6750_of_ledgers hardLedger directLedger)

end ContactFinalComposition6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactFinalComposition6750Research.semanticSelectedCount6750_of_ledgers
#print axioms ProximityPrize.SubmissionLower.ContactFinalComposition6750Research.protocolClaim6750_of_ledgers
