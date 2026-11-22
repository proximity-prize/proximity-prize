import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m10_0 : availableMass (start (.two6 ⟨4, by decide⟩)) ⟨1,3,0⟩ 25 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨4, by decide⟩)) ⟨1,3,0⟩ 25 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 208 [4541599120399, 3913157819203, 3242521237365, 2544858423909, 1958865886557, 1473594208605, 1078441653861, 763154166645, 517825371789, 332896574637, 199156761045, 107742597381, 50138430525, 18176287869, 4035877317, 244587285, 0, 0] (by decide +kernel) (by decide)

private theorem m10_1 : availableMass (start (.two6 ⟨4, by decide⟩)) ⟨2,6,0⟩ 57 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨4, by decide⟩)) ⟨2,6,0⟩ 57 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 194 [4541599120399, 3913157819203, 3349214025559, 2845568637259, 2383095319224, 1751266525062, 1181965856214, 754186977318, 446334754422, 237530689734, 107612921622, 37136224614, 7372009398, 309029715, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m10_2 : availableMass (start (.two6 ⟨4, by decide⟩)) ⟨6,18,0⟩ 78 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨4, by decide⟩)) ⟨6,18,0⟩ 78 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 146 [4541599120399, 3913157819203, 3349214025559, 2845568637259, 2398139005471, 2002958934739, 1539522341125, 710564204536, 224110093048, 35647259128, 635462086, 0, 0] (by decide +kernel) (by decide)

private theorem m10_3 : availableMass (start (.two6 ⟨4, by decide⟩)) ⟨12,35,0⟩ 87 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨4, by decide⟩)) ⟨12,35,0⟩ 87 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 127 [4541599120399, 3913157819203, 3349214025559, 2845568637259, 2398139005471, 2002958934739, 1656178682983, 980300366201, 151029721477, 1952684200, 0] (by decide +kernel) (by decide)

theorem checked10 (q : Threshold) (hq : q ∈ thresholds (.two6 ⟨4, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two6 ⟨4, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨by decide, m10_0⟩
  · exact ⟨by decide, m10_1⟩
  · exact ⟨by decide, m10_2⟩
  · exact ⟨by decide, m10_3⟩

end Low53At2389PriceMass
