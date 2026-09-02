import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R11Y00T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R11Y00Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R11TailBand

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_6783_r11_y00_full : FixedYReceipt 11 ⟨0, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r11_y00_t00_01 ct (by omega) h1
  · exact receipt_6783_r11_y00_t01_28 ct (by omega) hhi

theorem receipt_6783_r11_band_00_01 : RowBandReceipt 11 0 1 :=
  fixedYReceipt_to_rowBand 11 ⟨0, by decide⟩ receipt_6783_r11_y00_full

private theorem receipt_6783_r11_fast : FastRowReceipt 11 := by
  intro cy
  by_cases h1 : cy.val < 1
  · exact receipt_6783_r11_band_00_01 cy (by omega) h1
  · exact receipt_6783_r11_band_01_24 cy (by omega) (by omega)

theorem receipt_row_11_6783 : RowReceipt 11 :=
  fastRowReceipt_to_rowReceipt 11 receipt_6783_r11_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
