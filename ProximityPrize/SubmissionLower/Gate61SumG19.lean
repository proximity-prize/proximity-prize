import ProximityPrize.SubmissionLower.Gate61DatG19
set_option maxRecDepth 100000
namespace Gate61DatG19
open Gate61Cell
theorem S0 : psum lv 0 10 = 4067128132739 := by decide +kernel
theorem P0 : psum lv 0 10 = 4067128132739 := S0
theorem S1 : psum lv 10 10 = 4042288933228 := by decide +kernel
theorem P1 : psum lv 0 20 = 8109417065967 := by
  have h : psum lv 0 20 = psum lv 0 10 + psum lv 10 10 := psum_add lv 0 10 10
  rw [h, P0, S1]; rfl
theorem S2 : psum lv 20 10 = 3901207051180 := by decide +kernel
theorem P2 : psum lv 0 30 = 12010624117147 := by
  have h : psum lv 0 30 = psum lv 0 20 + psum lv 20 10 := psum_add lv 0 20 10
  rw [h, P1, S2]; rfl
theorem S3 : psum lv 30 10 = 3466015313940 := by decide +kernel
theorem P3 : psum lv 0 40 = 15476639431087 := by
  have h : psum lv 0 40 = psum lv 0 30 + psum lv 30 10 := psum_add lv 0 30 10
  rw [h, P2, S3]; rfl
theorem S4 : psum lv 40 10 = 2509861302740 := by decide +kernel
theorem P4 : psum lv 0 50 = 17986500733827 := by
  have h : psum lv 0 50 = psum lv 0 40 + psum lv 40 10 := psum_add lv 0 40 10
  rw [h, P3, S4]; rfl
theorem S5 : psum lv 50 10 = 1139098904769 := by decide +kernel
theorem P5 : psum lv 0 60 = 19125599638596 := by
  have h : psum lv 0 60 = psum lv 0 50 + psum lv 50 10 := psum_add lv 0 50 10
  rw [h, P4, S5]; rfl
theorem S6 : psum lv 60 10 = 261813792925 := by decide +kernel
theorem P6 : psum lv 0 70 = 19387413431521 := by
  have h : psum lv 0 70 = psum lv 0 60 + psum lv 60 10 := psum_add lv 0 60 10
  rw [h, P5, S6]; rfl
theorem S7 : psum lv 70 10 = 33364666878 := by decide +kernel
theorem P7 : psum lv 0 80 = 19420778098399 := by
  have h : psum lv 0 80 = psum lv 0 70 + psum lv 70 10 := psum_add lv 0 70 10
  rw [h, P6, S7]; rfl
theorem S8 : psum lv 80 10 = 100325111 := by decide +kernel
theorem P8 : psum lv 0 90 = 19420878423510 := by
  have h : psum lv 0 90 = psum lv 0 80 + psum lv 80 10 := psum_add lv 0 80 10
  rw [h, P7, S8]; rfl
theorem S9 : psum lv 90 10 = 0 := by decide +kernel
theorem P9 : psum lv 0 100 = 19420878423510 := by
  have h : psum lv 0 100 = psum lv 0 90 + psum lv 90 10 := psum_add lv 0 90 10
  rw [h, P8, S9]; rfl
theorem S10 : psum lv 100 10 = 0 := by decide +kernel
theorem P10 : psum lv 0 110 = 19420878423510 := by
  have h : psum lv 0 110 = psum lv 0 100 + psum lv 100 10 := psum_add lv 0 100 10
  rw [h, P9, S10]; rfl
theorem S11 : psum lv 110 10 = 0 := by decide +kernel
theorem P11 : psum lv 0 120 = 19420878423510 := by
  have h : psum lv 0 120 = psum lv 0 110 + psum lv 110 10 := psum_add lv 0 110 10
  rw [h, P10, S11]; rfl
theorem S12 : psum lv 120 10 = 0 := by decide +kernel
theorem P12 : psum lv 0 130 = 19420878423510 := by
  have h : psum lv 0 130 = psum lv 0 120 + psum lv 120 10 := psum_add lv 0 120 10
  rw [h, P11, S12]; rfl
theorem S13 : psum lv 130 10 = 0 := by decide +kernel
theorem P13 : psum lv 0 140 = 19420878423510 := by
  have h : psum lv 0 140 = psum lv 0 130 + psum lv 130 10 := psum_add lv 0 130 10
  rw [h, P12, S13]; rfl
theorem S14 : psum lv 140 10 = 0 := by decide +kernel
theorem P14 : psum lv 0 150 = 19420878423510 := by
  have h : psum lv 0 150 = psum lv 0 140 + psum lv 140 10 := psum_add lv 0 140 10
  rw [h, P13, S14]; rfl
theorem S15 : psum lv 150 10 = 0 := by decide +kernel
theorem P15 : psum lv 0 160 = 19420878423510 := by
  have h : psum lv 0 160 = psum lv 0 150 + psum lv 150 10 := psum_add lv 0 150 10
  rw [h, P14, S15]; rfl
theorem S16 : psum lv 160 10 = 0 := by decide +kernel
theorem P16 : psum lv 0 170 = 19420878423510 := by
  have h : psum lv 0 170 = psum lv 0 160 + psum lv 160 10 := psum_add lv 0 160 10
  rw [h, P15, S16]; rfl
theorem S17 : psum lv 170 10 = 0 := by decide +kernel
theorem P17 : psum lv 0 180 = 19420878423510 := by
  have h : psum lv 0 180 = psum lv 0 170 + psum lv 170 10 := psum_add lv 0 170 10
  rw [h, P16, S17]; rfl
theorem S18 : psum lv 180 10 = 0 := by decide +kernel
theorem P18 : psum lv 0 190 = 19420878423510 := by
  have h : psum lv 0 190 = psum lv 0 180 + psum lv 180 10 := psum_add lv 0 180 10
  rw [h, P17, S18]; rfl
theorem S19 : psum lv 190 10 = 0 := by decide +kernel
theorem P19 : psum lv 0 200 = 19420878423510 := by
  have h : psum lv 0 200 = psum lv 0 190 + psum lv 190 10 := psum_add lv 0 190 10
  rw [h, P18, S19]; rfl
theorem S20 : psum lv 200 10 = 0 := by decide +kernel
theorem P20 : psum lv 0 210 = 19420878423510 := by
  have h : psum lv 0 210 = psum lv 0 200 + psum lv 200 10 := psum_add lv 0 200 10
  rw [h, P19, S20]; rfl
theorem S21 : psum lv 210 10 = 0 := by decide +kernel
theorem P21 : psum lv 0 220 = 19420878423510 := by
  have h : psum lv 0 220 = psum lv 0 210 + psum lv 210 10 := psum_add lv 0 210 10
  rw [h, P20, S21]; rfl
theorem S22 : psum lv 220 10 = 0 := by decide +kernel
theorem P22 : psum lv 0 230 = 19420878423510 := by
  have h : psum lv 0 230 = psum lv 0 220 + psum lv 220 10 := psum_add lv 0 220 10
  rw [h, P21, S22]; rfl
theorem S23 : psum lv 230 7 = 0 := by decide +kernel
theorem P23 : psum lv 0 237 = 19420878423510 := by
  have h : psum lv 0 237 = psum lv 0 230 + psum lv 230 7 := psum_add lv 0 230 7
  rw [h, P22, S23]; rfl
theorem sumLt : (∑ i ∈ Finset.range n, lsum lv i) < Low6960Prices.layerNeed := by
  rw [← psum_eq]
  have h := P23
  have e : n = 237 := rfl
  rw [e, h]; decide
end Gate61DatG19
