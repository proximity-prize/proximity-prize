import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_terminal_029_s00 :
    FastFits (subunitLiteralBox 8 38 1056 1063 ⟨0, by decide⟩) := by
  decide +kernel

private theorem receipt_terminal_029_s01 :
    FastFits (subunitLiteralBox 8 38 1056 1063 ⟨1, by decide⟩) := by
  decide +kernel

private theorem receipt_terminal_029_s02 :
    FastFits (subunitLiteralBox 8 38 1056 1063 ⟨2, by decide⟩) := by
  decide +kernel

private theorem receipt_terminal_029_s03 :
    FastFits (subunitLiteralBox 8 38 1056 1063 ⟨3, by decide⟩) := by
  decide +kernel

theorem receipt_hard_unit_029 (si : Fin 4) :
    FastFits (subunitLiteralBox 8 38 1056 1063 si) := by
  fin_cases si
  · exact receipt_terminal_029_s00
  · exact receipt_terminal_029_s01
  · exact receipt_terminal_029_s02
  · exact receipt_terminal_029_s03

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
