import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

private theorem receipt_terminal_011_s00 :
    FastFits (subunitLiteralBox 8 38 912 919 ⟨0, by decide⟩) := by
  decide +kernel

private theorem receipt_terminal_011_s01 :
    FastFits (subunitLiteralBox 8 38 912 919 ⟨1, by decide⟩) := by
  decide +kernel

private theorem receipt_terminal_011_s02 :
    FastFits (subunitLiteralBox 8 38 912 919 ⟨2, by decide⟩) := by
  decide +kernel

private theorem receipt_terminal_011_s03 :
    FastFits (subunitLiteralBox 8 38 912 919 ⟨3, by decide⟩) := by
  decide +kernel

theorem receipt_hard_unit_011 (si : Fin 4) :
    FastFits (subunitLiteralBox 8 38 912 919 si) := by
  fin_cases si
  · exact receipt_terminal_011_s00
  · exact receipt_terminal_011_s01
  · exact receipt_terminal_011_s02
  · exact receipt_terminal_011_s03

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
