import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m17_0 : availableMass (start (.two6 ⟨11, by decide⟩)) ⟨1,3,0⟩ 42 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨11, by decide⟩)) ⟨1,3,0⟩ 42 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 225 [4479045454224, 3755838228768, 3123868817520, 2548308617988, 1934582804220, 1423333604928, 1019129498796, 706262716992, 470219697660, 297681085920, 176521733868, 95810700576, 45811252092, 17980861440, 4971208620, 628180608, 4896645, 0, 0] (by decide +kernel) (by decide)

private theorem m17_1 : availableMass (start (.two6 ⟨11, by decide⟩)) ⟨2,6,0⟩ 96 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨11, by decide⟩)) ⟨2,6,0⟩ 96 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 233 [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 1065192863040, 741008224078, 441710405422, 241177643278, 116115032302, 45950884558, 12836729518, 1647314062, 13462739, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m17_2 : availableMass (start (.two6 ⟨11, by decide⟩)) ⟨8,24,0⟩ 112 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨11, by decide⟩)) ⟨8,24,0⟩ 112 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 167 [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 1065192863040, 825354534672, 515311359960, 121536503308, 8083767052, 0, 0] (by decide +kernel) (by decide)

private theorem m17_3 : availableMass (start (.two6 ⟨11, by decide⟩)) ⟨13,39,0⟩ 125 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨11, by decide⟩)) ⟨13,39,0⟩ 125 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 161 [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 1065192863040, 825354534672, 628416662688, 363663748024, 30334412214, 1868, 0] (by decide +kernel) (by decide)

private theorem m17_4 : availableMass (start (.two6 ⟨11, by decide⟩)) ⟨63,37,0⟩ 121 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨11, by decide⟩)) ⟨63,37,0⟩ 121 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 159 [4479045454224, 3755838228768, 3123868817520, 2575130055552, 2101982053968, 1697152199904, 1353735156528, 1065192863040, 825354534672, 628416662688, 227848384720, 7084643960, 0, 0] (by decide +kernel) (by decide)

theorem checked17 (q : Threshold) (hq : q ∈ thresholds (.two6 ⟨11, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two6 ⟨11, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, m17_0⟩
  · exact ⟨by decide, m17_1⟩
  · exact ⟨by decide, m17_2⟩
  · exact ⟨by decide, m17_3⟩
  · exact ⟨by decide, m17_4⟩

end Low53At2389PriceMass
