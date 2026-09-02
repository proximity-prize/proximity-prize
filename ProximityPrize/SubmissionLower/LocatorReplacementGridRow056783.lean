import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y00T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y00Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y01T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y01Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y02T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y02Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y03T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y03Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y04T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y04Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y05T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y05T01
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y05Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y06T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y06T01
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y06T02
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y06Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y07T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y07T01
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y07T02
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y07T03
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y07Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y08T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y08T01
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y08T02
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y08T03
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y08T04
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y08T05
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y08T06
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y08T07
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y08Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y09T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y09T01
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y09T02
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y09T03
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y09T04
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y09T05
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y09T06
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y09T07
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y09T08
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y09T09
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y09T10
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y09T11
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y09T12
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y09T13
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y09T14
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y09T15
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y09T16
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05Y09Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R05TailBand

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_6783_r05_y00_full : FixedYReceipt 5 ⟨0, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r05_y00_t00_01 ct (by omega) h1
  · exact receipt_6783_r05_y00_t01_28 ct (by omega) hhi

theorem receipt_6783_r05_band_00_01 : RowBandReceipt 5 0 1 :=
  fixedYReceipt_to_rowBand 5 ⟨0, by decide⟩ receipt_6783_r05_y00_full

theorem receipt_6783_r05_y01_full : FixedYReceipt 5 ⟨1, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r05_y01_t00_01 ct (by omega) h1
  · exact receipt_6783_r05_y01_t01_28 ct (by omega) hhi

theorem receipt_6783_r05_band_01_02 : RowBandReceipt 5 1 2 :=
  fixedYReceipt_to_rowBand 5 ⟨1, by decide⟩ receipt_6783_r05_y01_full

theorem receipt_6783_r05_y02_full : FixedYReceipt 5 ⟨2, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r05_y02_t00_01 ct (by omega) h1
  · exact receipt_6783_r05_y02_t01_28 ct (by omega) hhi

theorem receipt_6783_r05_band_02_03 : RowBandReceipt 5 2 3 :=
  fixedYReceipt_to_rowBand 5 ⟨2, by decide⟩ receipt_6783_r05_y02_full

theorem receipt_6783_r05_y03_full : FixedYReceipt 5 ⟨3, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r05_y03_t00_01 ct (by omega) h1
  · exact receipt_6783_r05_y03_t01_28 ct (by omega) hhi

theorem receipt_6783_r05_band_03_04 : RowBandReceipt 5 3 4 :=
  fixedYReceipt_to_rowBand 5 ⟨3, by decide⟩ receipt_6783_r05_y03_full

theorem receipt_6783_r05_y04_full : FixedYReceipt 5 ⟨4, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r05_y04_t00_01 ct (by omega) h1
  · exact receipt_6783_r05_y04_t01_28 ct (by omega) hhi

theorem receipt_6783_r05_band_04_05 : RowBandReceipt 5 4 5 :=
  fixedYReceipt_to_rowBand 5 ⟨4, by decide⟩ receipt_6783_r05_y04_full

theorem receipt_6783_r05_y05_full : FixedYReceipt 5 ⟨5, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r05_y05_t00_01 ct (by omega) h1
  by_cases h2 : ct.val < 2
  · exact receipt_6783_r05_y05_t01_02 ct (by omega) h2
  · exact receipt_6783_r05_y05_t02_28 ct (by omega) hhi

theorem receipt_6783_r05_band_05_06 : RowBandReceipt 5 5 6 :=
  fixedYReceipt_to_rowBand 5 ⟨5, by decide⟩ receipt_6783_r05_y05_full

theorem receipt_6783_r05_y06_full : FixedYReceipt 5 ⟨6, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r05_y06_t00_01 ct (by omega) h1
  by_cases h2 : ct.val < 2
  · exact receipt_6783_r05_y06_t01_02 ct (by omega) h2
  by_cases h3 : ct.val < 3
  · exact receipt_6783_r05_y06_t02_03 ct (by omega) h3
  · exact receipt_6783_r05_y06_t03_28 ct (by omega) hhi

theorem receipt_6783_r05_band_06_07 : RowBandReceipt 5 6 7 :=
  fixedYReceipt_to_rowBand 5 ⟨6, by decide⟩ receipt_6783_r05_y06_full

theorem receipt_6783_r05_y07_full : FixedYReceipt 5 ⟨7, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r05_y07_t00_01 ct (by omega) h1
  by_cases h2 : ct.val < 2
  · exact receipt_6783_r05_y07_t01_02 ct (by omega) h2
  by_cases h3 : ct.val < 3
  · exact receipt_6783_r05_y07_t02_03 ct (by omega) h3
  by_cases h4 : ct.val < 4
  · exact receipt_6783_r05_y07_t03_04 ct (by omega) h4
  · exact receipt_6783_r05_y07_t04_28 ct (by omega) hhi

theorem receipt_6783_r05_band_07_08 : RowBandReceipt 5 7 8 :=
  fixedYReceipt_to_rowBand 5 ⟨7, by decide⟩ receipt_6783_r05_y07_full

theorem receipt_6783_r05_y08_full : FixedYReceipt 5 ⟨8, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r05_y08_t00_01 ct (by omega) h1
  by_cases h2 : ct.val < 2
  · exact receipt_6783_r05_y08_t01_02 ct (by omega) h2
  by_cases h3 : ct.val < 3
  · exact receipt_6783_r05_y08_t02_03 ct (by omega) h3
  by_cases h4 : ct.val < 4
  · exact receipt_6783_r05_y08_t03_04 ct (by omega) h4
  by_cases h5 : ct.val < 5
  · exact receipt_6783_r05_y08_t04_05 ct (by omega) h5
  by_cases h6 : ct.val < 6
  · exact receipt_6783_r05_y08_t05_06 ct (by omega) h6
  by_cases h7 : ct.val < 7
  · exact receipt_6783_r05_y08_t06_07 ct (by omega) h7
  by_cases h8 : ct.val < 8
  · exact receipt_6783_r05_y08_t07_08 ct (by omega) h8
  · exact receipt_6783_r05_y08_t08_28 ct (by omega) hhi

theorem receipt_6783_r05_band_08_09 : RowBandReceipt 5 8 9 :=
  fixedYReceipt_to_rowBand 5 ⟨8, by decide⟩ receipt_6783_r05_y08_full

theorem receipt_6783_r05_y09_full : FixedYReceipt 5 ⟨9, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r05_y09_t00_01 ct (by omega) h1
  by_cases h2 : ct.val < 2
  · exact receipt_6783_r05_y09_t01_02 ct (by omega) h2
  by_cases h3 : ct.val < 3
  · exact receipt_6783_r05_y09_t02_03 ct (by omega) h3
  by_cases h4 : ct.val < 4
  · exact receipt_6783_r05_y09_t03_04 ct (by omega) h4
  by_cases h5 : ct.val < 5
  · exact receipt_6783_r05_y09_t04_05 ct (by omega) h5
  by_cases h6 : ct.val < 6
  · exact receipt_6783_r05_y09_t05_06 ct (by omega) h6
  by_cases h7 : ct.val < 7
  · exact receipt_6783_r05_y09_t06_07 ct (by omega) h7
  by_cases h8 : ct.val < 8
  · exact receipt_6783_r05_y09_t07_08 ct (by omega) h8
  by_cases h9 : ct.val < 9
  · exact receipt_6783_r05_y09_t08_09 ct (by omega) h9
  by_cases h10 : ct.val < 10
  · exact receipt_6783_r05_y09_t09_10 ct (by omega) h10
  by_cases h11 : ct.val < 11
  · exact receipt_6783_r05_y09_t10_11 ct (by omega) h11
  by_cases h12 : ct.val < 12
  · exact receipt_6783_r05_y09_t11_12 ct (by omega) h12
  by_cases h13 : ct.val < 13
  · exact receipt_6783_r05_y09_t12_13 ct (by omega) h13
  by_cases h14 : ct.val < 14
  · exact receipt_6783_r05_y09_t13_14 ct (by omega) h14
  by_cases h15 : ct.val < 15
  · exact receipt_6783_r05_y09_t14_15 ct (by omega) h15
  by_cases h16 : ct.val < 16
  · exact receipt_6783_r05_y09_t15_16 ct (by omega) h16
  by_cases h17 : ct.val < 17
  · exact receipt_6783_r05_y09_t16_17 ct (by omega) h17
  · exact receipt_6783_r05_y09_t17_28 ct (by omega) hhi

theorem receipt_6783_r05_band_09_10 : RowBandReceipt 5 9 10 :=
  fixedYReceipt_to_rowBand 5 ⟨9, by decide⟩ receipt_6783_r05_y09_full

private theorem receipt_6783_r05_fast : FastRowReceipt 5 := by
  intro cy
  by_cases h1 : cy.val < 1
  · exact receipt_6783_r05_band_00_01 cy (by omega) h1
  by_cases h2 : cy.val < 2
  · exact receipt_6783_r05_band_01_02 cy (by omega) h2
  by_cases h3 : cy.val < 3
  · exact receipt_6783_r05_band_02_03 cy (by omega) h3
  by_cases h4 : cy.val < 4
  · exact receipt_6783_r05_band_03_04 cy (by omega) h4
  by_cases h5 : cy.val < 5
  · exact receipt_6783_r05_band_04_05 cy (by omega) h5
  by_cases h6 : cy.val < 6
  · exact receipt_6783_r05_band_05_06 cy (by omega) h6
  by_cases h7 : cy.val < 7
  · exact receipt_6783_r05_band_06_07 cy (by omega) h7
  by_cases h8 : cy.val < 8
  · exact receipt_6783_r05_band_07_08 cy (by omega) h8
  by_cases h9 : cy.val < 9
  · exact receipt_6783_r05_band_08_09 cy (by omega) h9
  by_cases h10 : cy.val < 10
  · exact receipt_6783_r05_band_09_10 cy (by omega) h10
  · exact receipt_6783_r05_band_10_24 cy (by omega) (by omega)

theorem receipt_row_05_6783 : RowReceipt 5 :=
  fastRowReceipt_to_rowReceipt 5 receipt_6783_r05_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
