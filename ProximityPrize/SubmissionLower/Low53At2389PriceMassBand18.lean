import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m18_0 : availableMass (start (.two6 ⟨12, by decide⟩)) ⟨1,3,0⟩ 47 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨12, by decide⟩)) ⟨1,3,0⟩ 47 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 230 [4470109216199, 3733364001563, 3091676644943, 2535258742611, 1961253078942, 1439246797698, 1027917535566, 710661448578, 472189832094, 298529120802, 177020888718, 96321849186, 46403854878, 18553897794, 5374109262, 781759938, 12726064, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m18_1 : availableMass (start (.two6 ⟨12, by decide⟩)) ⟨2,6,0⟩ 107 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨12, by decide⟩)) ⟨2,6,0⟩ 107 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 244 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 786114201381, 519321065186, 292918296242, 148419672194, 64104647762, 21262549538, 4192575986, 203816008, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m18_2 : availableMass (start (.two6 ⟨12, by decide⟩)) ⟨7,21,0⟩ 135 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨12, by decide⟩)) ⟨7,21,0⟩ 135 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 196 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 593978154299, 438772460399, 245023514335, 47486960799, 1879248302, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m18_3 : availableMass (start (.two6 ⟨12, by decide⟩)) ⟨13,39,0⟩ 137 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨12, by decide⟩)) ⟨13,39,0⟩ 137 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 173 [4470109216199, 3733364001563, 3091676644943, 2536495972451, 2059673918039, 1653465523499, 1310528938463, 1023925420403, 787119334631, 593978154299, 438772460399, 241296608597, 15132139160, 0, 0] (by decide +kernel) (by decide)

theorem checked18 (q : Threshold) (hq : q ∈ thresholds (.two6 ⟨12, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two6 ⟨12, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨by decide, m18_0⟩
  · exact ⟨by decide, m18_1⟩
  · exact ⟨by decide, m18_2⟩
  · exact ⟨by decide, m18_3⟩

end Low53At2389PriceMass
