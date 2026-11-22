import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m21_0 : availableMass (start (.two7 ⟨0, by decide⟩)) ⟨1,3,0⟩ 39 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨0, by decide⟩)) ⟨1,3,0⟩ 39 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 204 [4518321774336, 3849816668780, 3250457160752, 2652921551098, 2013174724021, 1481762954305, 1052741762669, 715392883513, 458901283237, 272355160241, 144745944925, 64968299689, 21820118933, 4002529057, 123024466, 0, 0] (by decide +kernel) (by decide)

private theorem m21_1 : availableMass (start (.two7 ⟨0, by decide⟩)) ⟨3,9,0⟩ 74 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨0, by decide⟩)) ⟨3,9,0⟩ 74 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 177 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1321504582056, 735357081548, 352906039340, 133333310604, 31734119660, 2297721164, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m21_2 : availableMass (start (.two7 ⟨0, by decide⟩)) ⟨5,14,0⟩ 84 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨0, by decide⟩)) ⟨5,14,0⟩ 84 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 162 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 893535209814, 353318188890, 92395819686, 8795411130, 4859790, 0, 0] (by decide +kernel) (by decide)

private theorem m21_3 : availableMass (start (.two7 ⟨0, by decide⟩)) ⟨9,27,0⟩ 98 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨0, by decide⟩)) ⟨9,27,0⟩ 98 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 146 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 622024203035, 93126860535, 1138221359, 0, 0] (by decide +kernel) (by decide)

private theorem m21_4 : availableMass (start (.two7 ⟨0, by decide⟩)) ⟨68,25,0⟩ 97 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨0, by decide⟩)) ⟨68,25,0⟩ 97 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 148 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 546288398668, 69818679948, 985494780, 0, 0] (by decide +kernel) (by decide)

private theorem m21_5 : availableMass (start (.two7 ⟨0, by decide⟩)) ⟨69,28,0⟩ 99 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨0, by decide⟩)) ⟨69,28,0⟩ 99 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 146 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 631042435770, 77653442572, 734009095, 0, 0] (by decide +kernel) (by decide)

private theorem m21_6 : availableMass (start (.two7 ⟨0, by decide⟩)) ⟨70,42,0⟩ 103 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨0, by decide⟩)) ⟨70,42,0⟩ 103 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 136 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1160590952492, 769455428817, 78158836886, 8459776, 0] (by decide +kernel) (by decide)

theorem checked21 (q : Threshold) (hq : q ∈ thresholds (.two7 ⟨0, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two7 ⟨0, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, m21_0⟩
  · exact ⟨by decide, m21_1⟩
  · exact ⟨by decide, m21_2⟩
  · exact ⟨by decide, m21_3⟩
  · exact ⟨by decide, m21_4⟩
  · exact ⟨by decide, m21_5⟩
  · exact ⟨by decide, m21_6⟩

end Low53At2389PriceMass
