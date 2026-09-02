import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_terminal_051_s00 :
    FastFits (subunitLiteralBox 8 38 1224 1231 ⟨0, by decide⟩) := by
  decide +kernel

private theorem receipt_terminal_051_s01 :
    FastFits (subunitLiteralBox 8 38 1224 1231 ⟨1, by decide⟩) := by
  decide +kernel

private theorem receipt_terminal_051_s02 :
    FastFits (subunitLiteralBox 8 38 1224 1231 ⟨2, by decide⟩) := by
  decide +kernel

private theorem receipt_terminal_051_s03 :
    FastFits (subunitLiteralBox 8 38 1224 1231 ⟨3, by decide⟩) := by
  decide +kernel

theorem receipt_hard_unit_051 (si : Fin 4) :
    FastFits (subunitLiteralBox 8 38 1224 1231 si) := by
  fin_cases si
  · exact receipt_terminal_051_s00
  · exact receipt_terminal_051_s01
  · exact receipt_terminal_051_s02
  · exact receipt_terminal_051_s03

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
