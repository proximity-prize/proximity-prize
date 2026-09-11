import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
import ProximityPrize.SubmissionLower.BoundaryTailPrefixChecked
import ProximityPrize.SubmissionLower.BoundaryTailRunsChecked
import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked
import ProximityPrize.SubmissionLower.BoundaryTailLedgerChecked
import ProximityPrize.SubmissionLower.BoundaryTailClosure

namespace ProximityPrize.SubmissionLower.Lower80811.Claim

open ProximityPrize.Benchmark
open Lower80811
open scoped Classical BigOperators

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem protocolClaim : ProtocolClaim 6806 338950094847 1099511627776 := by
  exact Closure.protocolClaim6806
    BoundaryTailBaseChecked.phaseReceipt
    PhaseChecked.prefixReceipt
    ThresholdCompressed.thresholdReceipt
    PhaseChecked.runsReceipt
    LedgerChecked.ledgerReceipt

end ProximityPrize.SubmissionLower.Lower80811.Claim
