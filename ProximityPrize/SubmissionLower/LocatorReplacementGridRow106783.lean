import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R10Y00T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R10Y00Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R10Y01T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R10Y01T01
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R10Y01Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R10Y02T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R10Y02T01
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R10Y02T02
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R10Y02Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R10Y03T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R10Y03T01
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R10Y03T02
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R10Y03T03
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R10Y03T04
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R10Y03T05
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R10Y03Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R10TailBand

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_6783_r10_y00_full : FixedYReceipt 10 ⟨0, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r10_y00_t00_01 ct (by omega) h1
  · exact receipt_6783_r10_y00_t01_28 ct (by omega) hhi

theorem receipt_6783_r10_band_00_01 : RowBandReceipt 10 0 1 :=
  fixedYReceipt_to_rowBand 10 ⟨0, by decide⟩ receipt_6783_r10_y00_full

theorem receipt_6783_r10_y01_full : FixedYReceipt 10 ⟨1, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r10_y01_t00_01 ct (by omega) h1
  by_cases h2 : ct.val < 2
  · exact receipt_6783_r10_y01_t01_02 ct (by omega) h2
  · exact receipt_6783_r10_y01_t02_28 ct (by omega) hhi

theorem receipt_6783_r10_band_01_02 : RowBandReceipt 10 1 2 :=
  fixedYReceipt_to_rowBand 10 ⟨1, by decide⟩ receipt_6783_r10_y01_full

theorem receipt_6783_r10_y02_full : FixedYReceipt 10 ⟨2, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r10_y02_t00_01 ct (by omega) h1
  by_cases h2 : ct.val < 2
  · exact receipt_6783_r10_y02_t01_02 ct (by omega) h2
  by_cases h3 : ct.val < 3
  · exact receipt_6783_r10_y02_t02_03 ct (by omega) h3
  · exact receipt_6783_r10_y02_t03_28 ct (by omega) hhi

theorem receipt_6783_r10_band_02_03 : RowBandReceipt 10 2 3 :=
  fixedYReceipt_to_rowBand 10 ⟨2, by decide⟩ receipt_6783_r10_y02_full

theorem receipt_6783_r10_y03_full : FixedYReceipt 10 ⟨3, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r10_y03_t00_01 ct (by omega) h1
  by_cases h2 : ct.val < 2
  · exact receipt_6783_r10_y03_t01_02 ct (by omega) h2
  by_cases h3 : ct.val < 3
  · exact receipt_6783_r10_y03_t02_03 ct (by omega) h3
  by_cases h4 : ct.val < 4
  · exact receipt_6783_r10_y03_t03_04 ct (by omega) h4
  by_cases h5 : ct.val < 5
  · exact receipt_6783_r10_y03_t04_05 ct (by omega) h5
  by_cases h6 : ct.val < 6
  · exact receipt_6783_r10_y03_t05_06 ct (by omega) h6
  · exact receipt_6783_r10_y03_t06_28 ct (by omega) hhi

theorem receipt_6783_r10_band_03_04 : RowBandReceipt 10 3 4 :=
  fixedYReceipt_to_rowBand 10 ⟨3, by decide⟩ receipt_6783_r10_y03_full

private theorem receipt_6783_r10_fast : FastRowReceipt 10 := by
  intro cy
  by_cases h1 : cy.val < 1
  · exact receipt_6783_r10_band_00_01 cy (by omega) h1
  by_cases h2 : cy.val < 2
  · exact receipt_6783_r10_band_01_02 cy (by omega) h2
  by_cases h3 : cy.val < 3
  · exact receipt_6783_r10_band_02_03 cy (by omega) h3
  by_cases h4 : cy.val < 4
  · exact receipt_6783_r10_band_03_04 cy (by omega) h4
  · exact receipt_6783_r10_band_04_24 cy (by omega) (by omega)

theorem receipt_row_10_6783 : RowReceipt 10 :=
  fastRowReceipt_to_rowReceipt 10 receipt_6783_r10_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
