import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_terminal_020_s00 :
    FastFits (subunitLiteralBox 8 38 984 991 ⟨0, by decide⟩) := by
  decide +kernel

private theorem receipt_terminal_020_s01 :
    FastFits (subunitLiteralBox 8 38 984 991 ⟨1, by decide⟩) := by
  decide +kernel

private theorem receipt_terminal_020_s02 :
    FastFits (subunitLiteralBox 8 38 984 991 ⟨2, by decide⟩) := by
  decide +kernel

private theorem receipt_terminal_020_s03 :
    FastFits (subunitLiteralBox 8 38 984 991 ⟨3, by decide⟩) := by
  decide +kernel

theorem receipt_hard_unit_020 (si : Fin 4) :
    FastFits (subunitLiteralBox 8 38 984 991 si) := by
  fin_cases si
  · exact receipt_terminal_020_s00
  · exact receipt_terminal_020_s01
  · exact receipt_terminal_020_s02
  · exact receipt_terminal_020_s03

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
