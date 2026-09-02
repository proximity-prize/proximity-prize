import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R01Y00T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R01Y00Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R01Y01T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R01Y01Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R01Y02T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R01Y02Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R01Y03T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R01Y03Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R01TailBand

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_6783_r01_y00_full : FixedYReceipt 1 ⟨0, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r01_y00_t00_01 ct (by omega) h1
  · exact receipt_6783_r01_y00_t01_28 ct (by omega) hhi

theorem receipt_6783_r01_band_00_01 : RowBandReceipt 1 0 1 :=
  fixedYReceipt_to_rowBand 1 ⟨0, by decide⟩ receipt_6783_r01_y00_full

theorem receipt_6783_r01_y01_full : FixedYReceipt 1 ⟨1, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r01_y01_t00_01 ct (by omega) h1
  · exact receipt_6783_r01_y01_t01_28 ct (by omega) hhi

theorem receipt_6783_r01_band_01_02 : RowBandReceipt 1 1 2 :=
  fixedYReceipt_to_rowBand 1 ⟨1, by decide⟩ receipt_6783_r01_y01_full

theorem receipt_6783_r01_y02_full : FixedYReceipt 1 ⟨2, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r01_y02_t00_01 ct (by omega) h1
  · exact receipt_6783_r01_y02_t01_28 ct (by omega) hhi

theorem receipt_6783_r01_band_02_03 : RowBandReceipt 1 2 3 :=
  fixedYReceipt_to_rowBand 1 ⟨2, by decide⟩ receipt_6783_r01_y02_full

theorem receipt_6783_r01_y03_full : FixedYReceipt 1 ⟨3, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r01_y03_t00_01 ct (by omega) h1
  · exact receipt_6783_r01_y03_t01_28 ct (by omega) hhi

theorem receipt_6783_r01_band_03_04 : RowBandReceipt 1 3 4 :=
  fixedYReceipt_to_rowBand 1 ⟨3, by decide⟩ receipt_6783_r01_y03_full

private theorem receipt_6783_r01_fast : FastRowReceipt 1 := by
  intro cy
  by_cases h1 : cy.val < 1
  · exact receipt_6783_r01_band_00_01 cy (by omega) h1
  by_cases h2 : cy.val < 2
  · exact receipt_6783_r01_band_01_02 cy (by omega) h2
  by_cases h3 : cy.val < 3
  · exact receipt_6783_r01_band_02_03 cy (by omega) h3
  by_cases h4 : cy.val < 4
  · exact receipt_6783_r01_band_03_04 cy (by omega) h4
  · exact receipt_6783_r01_band_04_24 cy (by omega) (by omega)

theorem receipt_row_01_6783 : RowReceipt 1 :=
  fastRowReceipt_to_rowReceipt 1 receipt_6783_r01_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
