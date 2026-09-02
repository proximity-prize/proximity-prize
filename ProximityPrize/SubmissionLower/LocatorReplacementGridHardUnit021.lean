import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_terminal_021_s00 :
    FastFits (subunitLiteralBox 8 38 992 999 ⟨0, by decide⟩) := by
  decide +kernel

private theorem receipt_terminal_021_s01 :
    FastFits (subunitLiteralBox 8 38 992 999 ⟨1, by decide⟩) := by
  decide +kernel

private theorem receipt_terminal_021_s02 :
    FastFits (subunitLiteralBox 8 38 992 999 ⟨2, by decide⟩) := by
  decide +kernel

private theorem receipt_terminal_021_s03 :
    FastFits (subunitLiteralBox 8 38 992 999 ⟨3, by decide⟩) := by
  decide +kernel

theorem receipt_hard_unit_021 (si : Fin 4) :
    FastFits (subunitLiteralBox 8 38 992 999 si) := by
  fin_cases si
  · exact receipt_terminal_021_s00
  · exact receipt_terminal_021_s01
  · exact receipt_terminal_021_s02
  · exact receipt_terminal_021_s03

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
