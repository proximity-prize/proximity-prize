import ProximityPrize.SubmissionLower.Koala6844ReceiptsTerminalFlagReference
import ProximityPrize.SubmissionLower.Koala6844ReceiptsTerminalTape00
import ProximityPrize.SubmissionLower.Koala6844ReceiptsTerminalTape01
import ProximityPrize.SubmissionLower.Koala6844ReceiptsTerminalTape02
import ProximityPrize.SubmissionLower.Koala6844ReceiptsTerminalTape03
import ProximityPrize.SubmissionLower.Koala6844ReceiptsTerminalTape04
import ProximityPrize.SubmissionLower.Koala6844ReceiptsTerminalTape05
import ProximityPrize.SubmissionLower.Koala6844ReceiptsTerminalTape06
import ProximityPrize.SubmissionLower.Koala6844ReceiptsTerminalTape07
import ProximityPrize.SubmissionLower.Koala6844ReceiptsTerminalTape08

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def checkedTerminalTapes : List TerminalCoveredSlope :=
  terminalTapeGroup00 ++
  terminalTapeGroup01 ++
  terminalTapeGroup02 ++
  terminalTapeGroup03 ++
  terminalTapeGroup04 ++
  terminalTapeGroup05 ++
  terminalTapeGroup06 ++
  terminalTapeGroup07 ++
  terminalTapeGroup08

theorem checkedTerminalTapes_slopes :
    checkedTerminalTapes.map TerminalCoveredSlope.slope = (List.range afterRooms.r).map (·+1) := by
  decide +kernel

theorem coveredTerminalFlags_eq_reference :
    coveredTerminalFlags checkedTerminalTapes = terminalFlagReference := by
  decide +kernel


end ProximityPrize.SubmissionLower.Koala6844Receipts

