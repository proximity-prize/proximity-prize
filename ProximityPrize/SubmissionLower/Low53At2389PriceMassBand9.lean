import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m9_0 : availableMass (start (.two6 ⟨3, by decide⟩)) ⟨1,3,0⟩ 25 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨3, by decide⟩)) ⟨1,3,0⟩ 25 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 208 [4550535358424, 3935632046408, 3273588754989, 2579265606237, 1993236165645, 1505513856381, 1106338849773, 786178065309, 535725170637, 345900581565, 207851462061, 112951724253, 52802028429, 19229783037, 4289144685, 261018141, 0, 0] (by decide +kernel) (by decide)

private theorem m9_1 : availableMass (start (.two6 ⟨3, by decide⟩)) ⟨2,6,0⟩ 57 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨3, by decide⟩)) ⟨2,6,0⟩ 57 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 194 [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2425107043454, 1789262967002, 1212543919994, 776904958490, 461711688890, 246759699290, 112274559482, 38911820954, 7757016890, 326411551, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m9_2 : availableMass (start (.two6 ⟨3, by decide⟩)) ⟨6,18,0⟩ 79 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨3, by decide⟩)) ⟨6,18,0⟩ 79 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 147 [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2046645611144, 1613188306409, 776025089642, 252313743674, 42970187018, 1001257452, 0, 0] (by decide +kernel) (by decide)

private theorem m9_3 : availableMass (start (.two6 ⟨3, by decide⟩)) ⟨12,36,0⟩ 85 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨3, by decide⟩)) ⟨12,36,0⟩ 85 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 124 [4550535358424, 3935632046408, 3381406198136, 2884202720360, 2440447141400, 2046645611144, 1699384901048, 837577132502, 97005320078, 298282698, 0] (by decide +kernel) (by decide)

theorem checked9 (q : Threshold) (hq : q ∈ thresholds (.two6 ⟨3, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two6 ⟨3, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨by decide, m9_0⟩
  · exact ⟨by decide, m9_1⟩
  · exact ⟨by decide, m9_2⟩
  · exact ⟨by decide, m9_3⟩

end Low53At2389PriceMass
