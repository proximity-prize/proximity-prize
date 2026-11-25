import ProximityPrize.SubmissionLower.Gate61DatRJa
set_option Elab.async false
set_option maxRecDepth 100000
namespace Gate61DatRJa
open Gate61Cell
theorem S0 : psum lv 0 10 = 4067226680502 := by decide +kernel
theorem P0 : psum lv 0 10 = 4067226680502 := S0
theorem S1 : psum lv 10 10 = 4045714063787 := by decide +kernel
theorem P1 : psum lv 0 20 = 8112940744289 := by
  have h : psum lv 0 20 = psum lv 0 10 + psum lv 10 10 := psum_add lv 0 10 10
  rw [h, P0, S1]; rfl
theorem S2 : psum lv 20 10 = 3923157684039 := by decide +kernel
theorem P2 : psum lv 0 30 = 12036098428328 := by
  have h : psum lv 0 30 = psum lv 0 20 + psum lv 20 10 := psum_add lv 0 20 10
  rw [h, P1, S2]; rfl
theorem S3 : psum lv 30 10 = 3545690543476 := by decide +kernel
theorem P3 : psum lv 0 40 = 15581788971804 := by
  have h : psum lv 0 40 = psum lv 0 30 + psum lv 30 10 := psum_add lv 0 30 10
  rw [h, P2, S3]; rfl
theorem S4 : psum lv 40 10 = 2690212321942 := by decide +kernel
theorem P4 : psum lv 0 50 = 18272001293746 := by
  have h : psum lv 0 50 = psum lv 0 40 + psum lv 40 10 := psum_add lv 0 40 10
  rw [h, P3, S4]; rfl
theorem S5 : psum lv 50 10 = 1248821810628 := by decide +kernel
theorem P5 : psum lv 0 60 = 19520823104374 := by
  have h : psum lv 0 60 = psum lv 0 50 + psum lv 50 10 := psum_add lv 0 50 10
  rw [h, P4, S5]; rfl
theorem S6 : psum lv 60 10 = 224514053650 := by decide +kernel
theorem P6 : psum lv 0 70 = 19745337158024 := by
  have h : psum lv 0 70 = psum lv 0 60 + psum lv 60 10 := psum_add lv 0 60 10
  rw [h, P5, S6]; rfl
theorem S7 : psum lv 70 10 = 18556894216 := by decide +kernel
theorem P7 : psum lv 0 80 = 19763894052240 := by
  have h : psum lv 0 80 = psum lv 0 70 + psum lv 70 10 := psum_add lv 0 70 10
  rw [h, P6, S7]; rfl
theorem S8 : psum lv 80 10 = 2119039262 := by decide +kernel
theorem P8 : psum lv 0 90 = 19766013091502 := by
  have h : psum lv 0 90 = psum lv 0 80 + psum lv 80 10 := psum_add lv 0 80 10
  rw [h, P7, S8]; rfl
theorem S9 : psum lv 90 10 = 0 := by decide +kernel
theorem P9 : psum lv 0 100 = 19766013091502 := by
  have h : psum lv 0 100 = psum lv 0 90 + psum lv 90 10 := psum_add lv 0 90 10
  rw [h, P8, S9]; rfl
theorem S10 : psum lv 100 10 = 0 := by decide +kernel
theorem P10 : psum lv 0 110 = 19766013091502 := by
  have h : psum lv 0 110 = psum lv 0 100 + psum lv 100 10 := psum_add lv 0 100 10
  rw [h, P9, S10]; rfl
theorem S11 : psum lv 110 10 = 0 := by decide +kernel
theorem P11 : psum lv 0 120 = 19766013091502 := by
  have h : psum lv 0 120 = psum lv 0 110 + psum lv 110 10 := psum_add lv 0 110 10
  rw [h, P10, S11]; rfl
theorem S12 : psum lv 120 10 = 0 := by decide +kernel
theorem P12 : psum lv 0 130 = 19766013091502 := by
  have h : psum lv 0 130 = psum lv 0 120 + psum lv 120 10 := psum_add lv 0 120 10
  rw [h, P11, S12]; rfl
theorem S13 : psum lv 130 10 = 0 := by decide +kernel
theorem P13 : psum lv 0 140 = 19766013091502 := by
  have h : psum lv 0 140 = psum lv 0 130 + psum lv 130 10 := psum_add lv 0 130 10
  rw [h, P12, S13]; rfl
theorem S14 : psum lv 140 10 = 0 := by decide +kernel
theorem P14 : psum lv 0 150 = 19766013091502 := by
  have h : psum lv 0 150 = psum lv 0 140 + psum lv 140 10 := psum_add lv 0 140 10
  rw [h, P13, S14]; rfl
theorem S15 : psum lv 150 10 = 0 := by decide +kernel
theorem P15 : psum lv 0 160 = 19766013091502 := by
  have h : psum lv 0 160 = psum lv 0 150 + psum lv 150 10 := psum_add lv 0 150 10
  rw [h, P14, S15]; rfl
theorem S16 : psum lv 160 10 = 0 := by decide +kernel
theorem P16 : psum lv 0 170 = 19766013091502 := by
  have h : psum lv 0 170 = psum lv 0 160 + psum lv 160 10 := psum_add lv 0 160 10
  rw [h, P15, S16]; rfl
theorem S17 : psum lv 170 10 = 0 := by decide +kernel
theorem P17 : psum lv 0 180 = 19766013091502 := by
  have h : psum lv 0 180 = psum lv 0 170 + psum lv 170 10 := psum_add lv 0 170 10
  rw [h, P16, S17]; rfl
theorem S18 : psum lv 180 10 = 0 := by decide +kernel
theorem P18 : psum lv 0 190 = 19766013091502 := by
  have h : psum lv 0 190 = psum lv 0 180 + psum lv 180 10 := psum_add lv 0 180 10
  rw [h, P17, S18]; rfl
theorem S19 : psum lv 190 10 = 0 := by decide +kernel
theorem P19 : psum lv 0 200 = 19766013091502 := by
  have h : psum lv 0 200 = psum lv 0 190 + psum lv 190 10 := psum_add lv 0 190 10
  rw [h, P18, S19]; rfl
theorem S20 : psum lv 200 10 = 0 := by decide +kernel
theorem P20 : psum lv 0 210 = 19766013091502 := by
  have h : psum lv 0 210 = psum lv 0 200 + psum lv 200 10 := psum_add lv 0 200 10
  rw [h, P19, S20]; rfl
theorem S21 : psum lv 210 7 = 0 := by decide +kernel
theorem P21 : psum lv 0 217 = 19766013091502 := by
  have h : psum lv 0 217 = psum lv 0 210 + psum lv 210 7 := psum_add lv 0 210 7
  rw [h, P20, S21]; rfl
theorem sumLt : (∑ i ∈ Finset.range n, lsum lv i) < Low6960Prices.layerNeed := by
  rw [← psum_eq]
  have h := P21
  have e : n = 217 := rfl
  rw [e, h]; decide
end Gate61DatRJa
