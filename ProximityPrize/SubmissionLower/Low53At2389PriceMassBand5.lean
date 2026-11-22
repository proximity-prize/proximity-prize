import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m5_0 : availableMass (start .one7) ⟨1,3,0⟩ 65 < layerNeed := by
  rw [mass_eq (start .one7) ⟨1,3,0⟩ 65 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 230 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1799933049774, 1318413678867, 923331819887, 616006720427, 385607449287, 221206307267, 111778827167, 46203773787, 13263143927, 1642166387, 8048187, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m5_1 : availableMass (start .one7) ⟨4,12,0⟩ 84 < layerNeed := by
  rw [mass_eq (start .one7) ⟨4,12,0⟩ 84 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 170 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 928341895573, 411044183701, 134134749533, 22845213805, 523215286, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m5_2 : availableMass (start .one7) ⟨9,25,0⟩ 92 < layerNeed := by
  rw [mass_eq (start .one7) ⟨9,25,0⟩ 92 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 143 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1099318556262, 363120455104, 38669547968, 62177136, 0] (by decide +kernel) (by decide)

private theorem m5_3 : availableMass (start .one7) ⟨9,27,0⟩ 95 < layerNeed := by
  rw [mass_eq (start .one7) ⟨9,27,0⟩ 95 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 143 [4518321774336, 3849816668780, 3250457160752, 2716533600588, 2244324484544, 1830096454796, 1470104299440, 1153763873808, 467121157493, 53305608465, 144132253, 0] (by decide +kernel) (by decide)

theorem checked5 (q : Threshold) (hq : q ∈ thresholds .one7) :
    0 < q.j ∧ availableMass (start .one7) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨by decide, m5_0⟩
  · exact ⟨by decide, m5_1⟩
  · exact ⟨by decide, m5_2⟩
  · exact ⟨by decide, m5_3⟩

end Low53At2389PriceMass
