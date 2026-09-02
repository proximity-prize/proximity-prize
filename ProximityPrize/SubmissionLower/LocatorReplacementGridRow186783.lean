import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R18Y00T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R18Y00Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R18TailBand

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_6783_r18_y00_full : FixedYReceipt 18 ⟨0, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r18_y00_t00_01 ct (by omega) h1
  · exact receipt_6783_r18_y00_t01_28 ct (by omega) hhi

theorem receipt_6783_r18_band_00_01 : RowBandReceipt 18 0 1 :=
  fixedYReceipt_to_rowBand 18 ⟨0, by decide⟩ receipt_6783_r18_y00_full

private theorem receipt_6783_r18_fast : FastRowReceipt 18 := by
  intro cy
  by_cases h1 : cy.val < 1
  · exact receipt_6783_r18_band_00_01 cy (by omega) h1
  · exact receipt_6783_r18_band_01_24 cy (by omega) (by omega)

theorem receipt_row_18_6783 : RowReceipt 18 :=
  fastRowReceipt_to_rowReceipt 18 receipt_6783_r18_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
