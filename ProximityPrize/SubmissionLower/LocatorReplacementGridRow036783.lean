import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y00T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y00Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y01T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y01Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y02T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y02Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y03T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y03Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y04T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y04Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y05T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y05Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y06T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y06Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y07T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y07Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y08T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y08T01
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y08Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y09T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y09T01
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y09Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y10T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y10T01
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03Y10Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R03TailBand

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_6783_r03_y00_full : FixedYReceipt 3 ⟨0, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r03_y00_t00_01 ct (by omega) h1
  · exact receipt_6783_r03_y00_t01_28 ct (by omega) hhi

theorem receipt_6783_r03_band_00_01 : RowBandReceipt 3 0 1 :=
  fixedYReceipt_to_rowBand 3 ⟨0, by decide⟩ receipt_6783_r03_y00_full

theorem receipt_6783_r03_y01_full : FixedYReceipt 3 ⟨1, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r03_y01_t00_01 ct (by omega) h1
  · exact receipt_6783_r03_y01_t01_28 ct (by omega) hhi

theorem receipt_6783_r03_band_01_02 : RowBandReceipt 3 1 2 :=
  fixedYReceipt_to_rowBand 3 ⟨1, by decide⟩ receipt_6783_r03_y01_full

theorem receipt_6783_r03_y02_full : FixedYReceipt 3 ⟨2, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r03_y02_t00_01 ct (by omega) h1
  · exact receipt_6783_r03_y02_t01_28 ct (by omega) hhi

theorem receipt_6783_r03_band_02_03 : RowBandReceipt 3 2 3 :=
  fixedYReceipt_to_rowBand 3 ⟨2, by decide⟩ receipt_6783_r03_y02_full

theorem receipt_6783_r03_y03_full : FixedYReceipt 3 ⟨3, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r03_y03_t00_01 ct (by omega) h1
  · exact receipt_6783_r03_y03_t01_28 ct (by omega) hhi

theorem receipt_6783_r03_band_03_04 : RowBandReceipt 3 3 4 :=
  fixedYReceipt_to_rowBand 3 ⟨3, by decide⟩ receipt_6783_r03_y03_full

theorem receipt_6783_r03_y04_full : FixedYReceipt 3 ⟨4, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r03_y04_t00_01 ct (by omega) h1
  · exact receipt_6783_r03_y04_t01_28 ct (by omega) hhi

theorem receipt_6783_r03_band_04_05 : RowBandReceipt 3 4 5 :=
  fixedYReceipt_to_rowBand 3 ⟨4, by decide⟩ receipt_6783_r03_y04_full

theorem receipt_6783_r03_y05_full : FixedYReceipt 3 ⟨5, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r03_y05_t00_01 ct (by omega) h1
  · exact receipt_6783_r03_y05_t01_28 ct (by omega) hhi

theorem receipt_6783_r03_band_05_06 : RowBandReceipt 3 5 6 :=
  fixedYReceipt_to_rowBand 3 ⟨5, by decide⟩ receipt_6783_r03_y05_full

theorem receipt_6783_r03_y06_full : FixedYReceipt 3 ⟨6, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r03_y06_t00_01 ct (by omega) h1
  · exact receipt_6783_r03_y06_t01_28 ct (by omega) hhi

theorem receipt_6783_r03_band_06_07 : RowBandReceipt 3 6 7 :=
  fixedYReceipt_to_rowBand 3 ⟨6, by decide⟩ receipt_6783_r03_y06_full

theorem receipt_6783_r03_y07_full : FixedYReceipt 3 ⟨7, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r03_y07_t00_01 ct (by omega) h1
  · exact receipt_6783_r03_y07_t01_28 ct (by omega) hhi

theorem receipt_6783_r03_band_07_08 : RowBandReceipt 3 7 8 :=
  fixedYReceipt_to_rowBand 3 ⟨7, by decide⟩ receipt_6783_r03_y07_full

theorem receipt_6783_r03_y08_full : FixedYReceipt 3 ⟨8, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r03_y08_t00_01 ct (by omega) h1
  by_cases h2 : ct.val < 2
  · exact receipt_6783_r03_y08_t01_02 ct (by omega) h2
  · exact receipt_6783_r03_y08_t02_28 ct (by omega) hhi

theorem receipt_6783_r03_band_08_09 : RowBandReceipt 3 8 9 :=
  fixedYReceipt_to_rowBand 3 ⟨8, by decide⟩ receipt_6783_r03_y08_full

theorem receipt_6783_r03_y09_full : FixedYReceipt 3 ⟨9, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r03_y09_t00_01 ct (by omega) h1
  by_cases h2 : ct.val < 2
  · exact receipt_6783_r03_y09_t01_02 ct (by omega) h2
  · exact receipt_6783_r03_y09_t02_28 ct (by omega) hhi

theorem receipt_6783_r03_band_09_10 : RowBandReceipt 3 9 10 :=
  fixedYReceipt_to_rowBand 3 ⟨9, by decide⟩ receipt_6783_r03_y09_full

theorem receipt_6783_r03_y10_full : FixedYReceipt 3 ⟨10, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r03_y10_t00_01 ct (by omega) h1
  by_cases h2 : ct.val < 2
  · exact receipt_6783_r03_y10_t01_02 ct (by omega) h2
  · exact receipt_6783_r03_y10_t02_28 ct (by omega) hhi

theorem receipt_6783_r03_band_10_11 : RowBandReceipt 3 10 11 :=
  fixedYReceipt_to_rowBand 3 ⟨10, by decide⟩ receipt_6783_r03_y10_full

private theorem receipt_6783_r03_fast : FastRowReceipt 3 := by
  intro cy
  by_cases h1 : cy.val < 1
  · exact receipt_6783_r03_band_00_01 cy (by omega) h1
  by_cases h2 : cy.val < 2
  · exact receipt_6783_r03_band_01_02 cy (by omega) h2
  by_cases h3 : cy.val < 3
  · exact receipt_6783_r03_band_02_03 cy (by omega) h3
  by_cases h4 : cy.val < 4
  · exact receipt_6783_r03_band_03_04 cy (by omega) h4
  by_cases h5 : cy.val < 5
  · exact receipt_6783_r03_band_04_05 cy (by omega) h5
  by_cases h6 : cy.val < 6
  · exact receipt_6783_r03_band_05_06 cy (by omega) h6
  by_cases h7 : cy.val < 7
  · exact receipt_6783_r03_band_06_07 cy (by omega) h7
  by_cases h8 : cy.val < 8
  · exact receipt_6783_r03_band_07_08 cy (by omega) h8
  by_cases h9 : cy.val < 9
  · exact receipt_6783_r03_band_08_09 cy (by omega) h9
  by_cases h10 : cy.val < 10
  · exact receipt_6783_r03_band_09_10 cy (by omega) h10
  by_cases h11 : cy.val < 11
  · exact receipt_6783_r03_band_10_11 cy (by omega) h11
  · exact receipt_6783_r03_band_11_24 cy (by omega) (by omega)

theorem receipt_row_03_6783 : RowReceipt 3 :=
  fastRowReceipt_to_rowReceipt 3 receipt_6783_r03_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
