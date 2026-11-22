import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m12_0 : availableMass (start (.two6 ⟨6, by decide⟩)) ⟨1,3,0⟩ 28 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨6, by decide⟩)) ⟨1,3,0⟩ 28 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 211 [4523726644349, 3868209364793, 3228208392019, 2525050842306, 1930861442166, 1443096224826, 1049435626830, 738149629938, 498097761126, 318729092586, 190082241726, 102785371170, 48056188758, 17701947546, 4119445806, 295027026, 0, 0] (by decide +kernel) (by decide)

private theorem m12_1 : availableMass (start (.two6 ⟨6, by decide⟩)) ⟨2,6,0⟩ 64 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨6, by decide⟩)) ⟨2,6,0⟩ 64 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 201 [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1839597698615, 1257496750664, 809568001160, 486424926152, 265590033416, 125875775816, 47384551304, 11508702920, 930518792, 56308, 0, 0] (by decide +kernel) (by decide)

private theorem m12_2 : availableMass (start (.two6 ⟨6, by decide⟩)) ⟨6,18,0⟩ 87 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨6, by decide⟩)) ⟨6,18,0⟩ 87 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 155 [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1569766246853, 1073080663214, 416946793508, 103933194020, 8931774500, 1533254, 0] (by decide +kernel) (by decide)

private theorem m12_3 : availableMass (start (.two6 ⟨6, by decide⟩)) ⟨12,36,0⟩ 94 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨6, by decide⟩)) ⟨12,36,0⟩ 94 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 133 [4523726644349, 3868209364793, 3284829680405, 2768300471057, 2313522733613, 1915585581929, 1569766246853, 1244611721864, 403814261837, 24149304641, 0, 0] (by decide +kernel) (by decide)

theorem checked12 (q : Threshold) (hq : q ∈ thresholds (.two6 ⟨6, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two6 ⟨6, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨by decide, m12_0⟩
  · exact ⟨by decide, m12_1⟩
  · exact ⟨by decide, m12_2⟩
  · exact ⟨by decide, m12_3⟩

end Low53At2389PriceMass
