import ProximityPrize.SubmissionLower.LowerRunsChecked
import ProximityPrize.SubmissionLower.LowerAuxChecks

section Compact_ClaimCompressed80791
/-! Unconditional exact-radius lower-bound certificate at error 80791. -/
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.CompressedClaim
open ProximityPrize.Benchmark
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem prefixReceipt : PhaseSemantics.PrefixReceiptSound := by
  intro r v hr hR hY
  exact PrefixChecked.checked r (List.mem_range.mpr (by omega)) hr
    v (List.mem_range.mpr (by omega))

theorem thresholdReceipt : PhaseSemantics.ThresholdReceiptSound := by
  intro r v hr hR hY
  exact ThresholdCompressed.checked r (List.mem_range.mpr (by omega)) hr
    v (List.mem_range.mpr (by omega))

theorem runReceipt : PhaseSemantics.RunReceiptSound := by
  intro r v hr hR hY
  exact RunsChecked.checked r (List.mem_range.mpr (by omega)) hr
    v (List.mem_range.mpr (by omega))

theorem ledgerReceipt : Assembly.LedgerReceiptSound := LedgerChecked.checked

theorem protocolClaim : ProtocolClaim 6804 10341375 33554432 :=
  Closure.protocolClaim6804 prefixReceipt thresholdReceipt runReceipt ledgerReceipt

end ProximityPrize.SubmissionLower.Lower80791.CompressedClaim

end Compact_ClaimCompressed80791
