import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_terminal_023_s00 :
    FastFits (subunitLiteralBox 8 38 1008 1015 ⟨0, by decide⟩) := by
  decide +kernel

private theorem receipt_terminal_023_s01 :
    FastFits (subunitLiteralBox 8 38 1008 1015 ⟨1, by decide⟩) := by
  decide +kernel

private theorem receipt_terminal_023_s02 :
    FastFits (subunitLiteralBox 8 38 1008 1015 ⟨2, by decide⟩) := by
  decide +kernel

private theorem receipt_terminal_023_s03 :
    FastFits (subunitLiteralBox 8 38 1008 1015 ⟨3, by decide⟩) := by
  decide +kernel

theorem receipt_hard_unit_023 (si : Fin 4) :
    FastFits (subunitLiteralBox 8 38 1008 1015 si) := by
  fin_cases si
  · exact receipt_terminal_023_s00
  · exact receipt_terminal_023_s01
  · exact receipt_terminal_023_s02
  · exact receipt_terminal_023_s03

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
