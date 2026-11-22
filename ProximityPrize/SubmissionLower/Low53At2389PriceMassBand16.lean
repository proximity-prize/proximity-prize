import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m16_0 : availableMass (start (.two6 ⟨10, by decide⟩)) ⟨1,3,0⟩ 38 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨10, by decide⟩)) ⟨1,3,0⟩ 38 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 221 [4487981692249, 3778312455973, 3156060990097, 2541559321098, 1919897966052, 1416599826264, 1017198744444, 706836417552, 471727817172, 299161189512, 177498055404, 96173210304, 45694724292, 17643942072, 4675482972, 517240944, 1698968, 0, 0] (by decide +kernel) (by decide)

private theorem m16_1 : availableMass (start (.two6 ⟨10, by decide⟩)) ⟨2,6,0⟩ 87 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨10, by decide⟩)) ⟨2,6,0⟩ 87 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 224 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1045344549967, 658549788534, 384527658438, 203411310102, 93000947814, 33533338806, 7681813254, 556264278, 1653, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m16_2 : availableMass (start (.two6 ⟨10, by decide⟩)) ⟨7,21,0⟩ 112 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨10, by decide⟩)) ⟨7,21,0⟩ 112 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 173 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 863589734713, 556261385317, 157089245079, 17717188503, 58105421, 0, 0] (by decide +kernel) (by decide)

private theorem m16_3 : availableMass (start (.two6 ⟨10, by decide⟩)) ⟨64,39,0⟩ 114 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨10, by decide⟩)) ⟨64,39,0⟩ 114 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 150 [4487981692249, 3778312455973, 3156060990097, 2613764138653, 2144290189897, 1740838876309, 1396941374593, 1106460305677, 863589734713, 540520018904, 54107365863, 58561738, 0] (by decide +kernel) (by decide)

theorem checked16 (q : Threshold) (hq : q ∈ thresholds (.two6 ⟨10, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two6 ⟨10, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨by decide, m16_0⟩
  · exact ⟨by decide, m16_1⟩
  · exact ⟨by decide, m16_2⟩
  · exact ⟨by decide, m16_3⟩

end Low53At2389PriceMass
