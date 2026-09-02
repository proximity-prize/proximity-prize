import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y00T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y00Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y01T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y01Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y02T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y02Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y03T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y03T01
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y03Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y04T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y04T01
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y04T02
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y04Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y05T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y05T01
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y05T02
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y05T03
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y05T04
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y05Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T01
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T02
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T03
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T04
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T05
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T06
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T07
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T08
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T09
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T10
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T11
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T12
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T13
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T14
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T15
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T16
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T17
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T18
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T19
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T20
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T21
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T22
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T23
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T24
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T25
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06T26
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y06Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y07T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y07T01
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y07Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y08T00
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07Y08Tail
import ProximityPrize.SubmissionLower.LocatorReplacementGrid6783R07TailBand

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem receipt_6783_r07_y00_full : FixedYReceipt 7 ⟨0, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r07_y00_t00_01 ct (by omega) h1
  · exact receipt_6783_r07_y00_t01_28 ct (by omega) hhi

theorem receipt_6783_r07_band_00_01 : RowBandReceipt 7 0 1 :=
  fixedYReceipt_to_rowBand 7 ⟨0, by decide⟩ receipt_6783_r07_y00_full

theorem receipt_6783_r07_y01_full : FixedYReceipt 7 ⟨1, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r07_y01_t00_01 ct (by omega) h1
  · exact receipt_6783_r07_y01_t01_28 ct (by omega) hhi

theorem receipt_6783_r07_band_01_02 : RowBandReceipt 7 1 2 :=
  fixedYReceipt_to_rowBand 7 ⟨1, by decide⟩ receipt_6783_r07_y01_full

theorem receipt_6783_r07_y02_full : FixedYReceipt 7 ⟨2, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r07_y02_t00_01 ct (by omega) h1
  · exact receipt_6783_r07_y02_t01_28 ct (by omega) hhi

theorem receipt_6783_r07_band_02_03 : RowBandReceipt 7 2 3 :=
  fixedYReceipt_to_rowBand 7 ⟨2, by decide⟩ receipt_6783_r07_y02_full

theorem receipt_6783_r07_y03_full : FixedYReceipt 7 ⟨3, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r07_y03_t00_01 ct (by omega) h1
  by_cases h2 : ct.val < 2
  · exact receipt_6783_r07_y03_t01_02 ct (by omega) h2
  · exact receipt_6783_r07_y03_t02_28 ct (by omega) hhi

theorem receipt_6783_r07_band_03_04 : RowBandReceipt 7 3 4 :=
  fixedYReceipt_to_rowBand 7 ⟨3, by decide⟩ receipt_6783_r07_y03_full

theorem receipt_6783_r07_y04_full : FixedYReceipt 7 ⟨4, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r07_y04_t00_01 ct (by omega) h1
  by_cases h2 : ct.val < 2
  · exact receipt_6783_r07_y04_t01_02 ct (by omega) h2
  by_cases h3 : ct.val < 3
  · exact receipt_6783_r07_y04_t02_03 ct (by omega) h3
  · exact receipt_6783_r07_y04_t03_28 ct (by omega) hhi

theorem receipt_6783_r07_band_04_05 : RowBandReceipt 7 4 5 :=
  fixedYReceipt_to_rowBand 7 ⟨4, by decide⟩ receipt_6783_r07_y04_full

theorem receipt_6783_r07_y05_full : FixedYReceipt 7 ⟨5, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r07_y05_t00_01 ct (by omega) h1
  by_cases h2 : ct.val < 2
  · exact receipt_6783_r07_y05_t01_02 ct (by omega) h2
  by_cases h3 : ct.val < 3
  · exact receipt_6783_r07_y05_t02_03 ct (by omega) h3
  by_cases h4 : ct.val < 4
  · exact receipt_6783_r07_y05_t03_04 ct (by omega) h4
  by_cases h5 : ct.val < 5
  · exact receipt_6783_r07_y05_t04_05 ct (by omega) h5
  · exact receipt_6783_r07_y05_t05_28 ct (by omega) hhi

theorem receipt_6783_r07_band_05_06 : RowBandReceipt 7 5 6 :=
  fixedYReceipt_to_rowBand 7 ⟨5, by decide⟩ receipt_6783_r07_y05_full

theorem receipt_6783_r07_y06_full : FixedYReceipt 7 ⟨6, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r07_y06_t00_01 ct (by omega) h1
  by_cases h2 : ct.val < 2
  · exact receipt_6783_r07_y06_t01_02 ct (by omega) h2
  by_cases h3 : ct.val < 3
  · exact receipt_6783_r07_y06_t02_03 ct (by omega) h3
  by_cases h4 : ct.val < 4
  · exact receipt_6783_r07_y06_t03_04 ct (by omega) h4
  by_cases h5 : ct.val < 5
  · exact receipt_6783_r07_y06_t04_05 ct (by omega) h5
  by_cases h6 : ct.val < 6
  · exact receipt_6783_r07_y06_t05_06 ct (by omega) h6
  by_cases h7 : ct.val < 7
  · exact receipt_6783_r07_y06_t06_07 ct (by omega) h7
  by_cases h8 : ct.val < 8
  · exact receipt_6783_r07_y06_t07_08 ct (by omega) h8
  by_cases h9 : ct.val < 9
  · exact receipt_6783_r07_y06_t08_09 ct (by omega) h9
  by_cases h10 : ct.val < 10
  · exact receipt_6783_r07_y06_t09_10 ct (by omega) h10
  by_cases h11 : ct.val < 11
  · exact receipt_6783_r07_y06_t10_11 ct (by omega) h11
  by_cases h12 : ct.val < 12
  · exact receipt_6783_r07_y06_t11_12 ct (by omega) h12
  by_cases h13 : ct.val < 13
  · exact receipt_6783_r07_y06_t12_13 ct (by omega) h13
  by_cases h14 : ct.val < 14
  · exact receipt_6783_r07_y06_t13_14 ct (by omega) h14
  by_cases h15 : ct.val < 15
  · exact receipt_6783_r07_y06_t14_15 ct (by omega) h15
  by_cases h16 : ct.val < 16
  · exact receipt_6783_r07_y06_t15_16 ct (by omega) h16
  by_cases h17 : ct.val < 17
  · exact receipt_6783_r07_y06_t16_17 ct (by omega) h17
  by_cases h18 : ct.val < 18
  · exact receipt_6783_r07_y06_t17_18 ct (by omega) h18
  by_cases h19 : ct.val < 19
  · exact receipt_6783_r07_y06_t18_19 ct (by omega) h19
  by_cases h20 : ct.val < 20
  · exact receipt_6783_r07_y06_t19_20 ct (by omega) h20
  by_cases h21 : ct.val < 21
  · exact receipt_6783_r07_y06_t20_21 ct (by omega) h21
  by_cases h22 : ct.val < 22
  · exact receipt_6783_r07_y06_t21_22 ct (by omega) h22
  by_cases h23 : ct.val < 23
  · exact receipt_6783_r07_y06_t22_23 ct (by omega) h23
  by_cases h24 : ct.val < 24
  · exact receipt_6783_r07_y06_t23_24 ct (by omega) h24
  by_cases h25 : ct.val < 25
  · exact receipt_6783_r07_y06_t24_25 ct (by omega) h25
  by_cases h26 : ct.val < 26
  · exact receipt_6783_r07_y06_t25_26 ct (by omega) h26
  by_cases h27 : ct.val < 27
  · exact receipt_6783_r07_y06_t26_27 ct (by omega) h27
  · exact receipt_6783_r07_y06_t27_28 ct (by omega) hhi

theorem receipt_6783_r07_band_06_07 : RowBandReceipt 7 6 7 :=
  fixedYReceipt_to_rowBand 7 ⟨6, by decide⟩ receipt_6783_r07_y06_full

theorem receipt_6783_r07_y07_full : FixedYReceipt 7 ⟨7, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r07_y07_t00_01 ct (by omega) h1
  by_cases h2 : ct.val < 2
  · exact receipt_6783_r07_y07_t01_02 ct (by omega) h2
  · exact receipt_6783_r07_y07_t02_28 ct (by omega) hhi

theorem receipt_6783_r07_band_07_08 : RowBandReceipt 7 7 8 :=
  fixedYReceipt_to_rowBand 7 ⟨7, by decide⟩ receipt_6783_r07_y07_full

theorem receipt_6783_r07_y08_full : FixedYReceipt 7 ⟨8, by decide⟩ 0 28 := by
  intro ct hlo hhi
  by_cases h1 : ct.val < 1
  · exact receipt_6783_r07_y08_t00_01 ct (by omega) h1
  · exact receipt_6783_r07_y08_t01_28 ct (by omega) hhi

theorem receipt_6783_r07_band_08_09 : RowBandReceipt 7 8 9 :=
  fixedYReceipt_to_rowBand 7 ⟨8, by decide⟩ receipt_6783_r07_y08_full

private theorem receipt_6783_r07_fast : FastRowReceipt 7 := by
  intro cy
  by_cases h1 : cy.val < 1
  · exact receipt_6783_r07_band_00_01 cy (by omega) h1
  by_cases h2 : cy.val < 2
  · exact receipt_6783_r07_band_01_02 cy (by omega) h2
  by_cases h3 : cy.val < 3
  · exact receipt_6783_r07_band_02_03 cy (by omega) h3
  by_cases h4 : cy.val < 4
  · exact receipt_6783_r07_band_03_04 cy (by omega) h4
  by_cases h5 : cy.val < 5
  · exact receipt_6783_r07_band_04_05 cy (by omega) h5
  by_cases h6 : cy.val < 6
  · exact receipt_6783_r07_band_05_06 cy (by omega) h6
  by_cases h7 : cy.val < 7
  · exact receipt_6783_r07_band_06_07 cy (by omega) h7
  by_cases h8 : cy.val < 8
  · exact receipt_6783_r07_band_07_08 cy (by omega) h8
  by_cases h9 : cy.val < 9
  · exact receipt_6783_r07_band_08_09 cy (by omega) h9
  · exact receipt_6783_r07_band_09_24 cy (by omega) (by omega)

theorem receipt_row_07_6783 : RowReceipt 7 :=
  fastRowReceipt_to_rowReceipt 7 receipt_6783_r07_fast

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
