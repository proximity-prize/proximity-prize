import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m26_0 : availableMass (start (.two7 ⟨5, by decide⟩)) ⟨1,3,0⟩ 44 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨5, by decide⟩)) ⟨1,3,0⟩ 44 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 209 [4474327638891, 3741565535995, 3099406695387, 2527553535826, 1913813118672, 1386284423384, 969900020576, 649712364648, 411506582000, 241800471032, 127844502144, 57621817736, 19848232208, 3972231960, 175183237, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m26_1 : availableMass (start (.two7 ⟨5, by decide⟩)) ⟨2,6,0⟩ 99 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨5, by decide⟩)) ⟨2,6,0⟩ 99 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 225 [4474327638891, 3741565535995, 3099406695387, 2540522162763, 2057855627659, 1644623423451, 1294314527355, 1000690560427, 708536149496, 400897270099, 198690480731, 80564931931, 22705414099, 2769727043, 13686805, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m26_2 : availableMass (start (.two7 ⟨5, by decide⟩)) ⟨5,15,0⟩ 140 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨5, by decide⟩)) ⟨5,15,0⟩ 140 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 215 [4474327638891, 3741565535995, 3099406695387, 2540522162763, 2057855627659, 1644623423451, 1294314527355, 1000690560427, 757785787563, 559907117499, 401634102811, 265164787900, 80469726110, 7398812478, 3266418, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m26_3 : availableMass (start (.two7 ⟨5, by decide⟩)) ⟨11,33,0⟩ 147 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨5, by decide⟩)) ⟨11,33,0⟩ 147 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 188 [4474327638891, 3741565535995, 3099406695387, 2540522162763, 2057855627659, 1644623423451, 1294314527355, 1000690560427, 757785787563, 559907117499, 401634102811, 277818939915, 111103863017, 1557730249, 0, 0] (by decide +kernel) (by decide)

theorem checked26 (q : Threshold) (hq : q ∈ thresholds (.two7 ⟨5, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two7 ⟨5, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨by decide, m26_0⟩
  · exact ⟨by decide, m26_1⟩
  · exact ⟨by decide, m26_2⟩
  · exact ⟨by decide, m26_3⟩

end Low53At2389PriceMass
