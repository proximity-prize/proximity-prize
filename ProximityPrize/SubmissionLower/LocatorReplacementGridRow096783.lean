import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y00T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y00Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y01T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y01Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y02T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y02T01
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y02Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y03T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y03T01
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y03T02
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y03T03
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y03Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y04T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y04T01
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y04T02
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y04T03
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y04T04
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y04T05
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y04T06
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y04T07
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y04T08
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y04T09
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y04T10
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y04Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y05T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09Y05Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R09TailBand

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_6783_r09_y00_full : FixedYReceipt 9 ⟨0, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r09_y00_t00_01 ct (by omega) h1
  · exact receipt_6783_r09_y00_t01_28 ct (by omega) hhi

theorem receipt_6783_r09_band_00_01 : RowBandReceipt 9 0 1 :=
  fixedYReceipt_to_rowBand 9 ⟨0, by decide⟩ receipt_6783_r09_y00_full

theorem receipt_6783_r09_y01_full : FixedYReceipt 9 ⟨1, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r09_y01_t00_01 ct (by omega) h1
  · exact receipt_6783_r09_y01_t01_28 ct (by omega) hhi

theorem receipt_6783_r09_band_01_02 : RowBandReceipt 9 1 2 :=
  fixedYReceipt_to_rowBand 9 ⟨1, by decide⟩ receipt_6783_r09_y01_full

theorem receipt_6783_r09_y02_full : FixedYReceipt 9 ⟨2, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r09_y02_t00_01 ct (by omega) h1
  by_cases h2 : ct.val < 2
  · exact receipt_6783_r09_y02_t01_02 ct (by omega) h2
  · exact receipt_6783_r09_y02_t02_28 ct (by omega) hhi

theorem receipt_6783_r09_band_02_03 : RowBandReceipt 9 2 3 :=
  fixedYReceipt_to_rowBand 9 ⟨2, by decide⟩ receipt_6783_r09_y02_full

theorem receipt_6783_r09_y03_full : FixedYReceipt 9 ⟨3, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r09_y03_t00_01 ct (by omega) h1
  by_cases h2 : ct.val < 2
  · exact receipt_6783_r09_y03_t01_02 ct (by omega) h2
  by_cases h3 : ct.val < 3
  · exact receipt_6783_r09_y03_t02_03 ct (by omega) h3
  by_cases h4 : ct.val < 4
  · exact receipt_6783_r09_y03_t03_04 ct (by omega) h4
  · exact receipt_6783_r09_y03_t04_28 ct (by omega) hhi

theorem receipt_6783_r09_band_03_04 : RowBandReceipt 9 3 4 :=
  fixedYReceipt_to_rowBand 9 ⟨3, by decide⟩ receipt_6783_r09_y03_full

theorem receipt_6783_r09_y04_full : FixedYReceipt 9 ⟨4, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r09_y04_t00_01 ct (by omega) h1
  by_cases h2 : ct.val < 2
  · exact receipt_6783_r09_y04_t01_02 ct (by omega) h2
  by_cases h3 : ct.val < 3
  · exact receipt_6783_r09_y04_t02_03 ct (by omega) h3
  by_cases h4 : ct.val < 4
  · exact receipt_6783_r09_y04_t03_04 ct (by omega) h4
  by_cases h5 : ct.val < 5
  · exact receipt_6783_r09_y04_t04_05 ct (by omega) h5
  by_cases h6 : ct.val < 6
  · exact receipt_6783_r09_y04_t05_06 ct (by omega) h6
  by_cases h7 : ct.val < 7
  · exact receipt_6783_r09_y04_t06_07 ct (by omega) h7
  by_cases h8 : ct.val < 8
  · exact receipt_6783_r09_y04_t07_08 ct (by omega) h8
  by_cases h9 : ct.val < 9
  · exact receipt_6783_r09_y04_t08_09 ct (by omega) h9
  by_cases h10 : ct.val < 10
  · exact receipt_6783_r09_y04_t09_10 ct (by omega) h10
  by_cases h11 : ct.val < 11
  · exact receipt_6783_r09_y04_t10_11 ct (by omega) h11
  · exact receipt_6783_r09_y04_t11_28 ct (by omega) hhi

theorem receipt_6783_r09_band_04_05 : RowBandReceipt 9 4 5 :=
  fixedYReceipt_to_rowBand 9 ⟨4, by decide⟩ receipt_6783_r09_y04_full

theorem receipt_6783_r09_y05_full : FixedYReceipt 9 ⟨5, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r09_y05_t00_01 ct (by omega) h1
  · exact receipt_6783_r09_y05_t01_28 ct (by omega) hhi

theorem receipt_6783_r09_band_05_06 : RowBandReceipt 9 5 6 :=
  fixedYReceipt_to_rowBand 9 ⟨5, by decide⟩ receipt_6783_r09_y05_full

private theorem receipt_6783_r09_fast : FastRowReceipt 9 := by
  intro cy
  by_cases h1 : cy.val < 1
  · exact receipt_6783_r09_band_00_01 cy (by omega) h1
  by_cases h2 : cy.val < 2
  · exact receipt_6783_r09_band_01_02 cy (by omega) h2
  by_cases h3 : cy.val < 3
  · exact receipt_6783_r09_band_02_03 cy (by omega) h3
  by_cases h4 : cy.val < 4
  · exact receipt_6783_r09_band_03_04 cy (by omega) h4
  by_cases h5 : cy.val < 5
  · exact receipt_6783_r09_band_04_05 cy (by omega) h5
  by_cases h6 : cy.val < 6
  · exact receipt_6783_r09_band_05_06 cy (by omega) h6
  · exact receipt_6783_r09_band_06_24 cy (by omega) (by omega)

theorem receipt_row_09_6783 : RowReceipt 9 :=
  fastRowReceipt_to_rowReceipt 9 receipt_6783_r09_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
