import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m27_0 : availableMass (start (.two7 ⟨6, by decide⟩)) ⟨1,3,0⟩ 163 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨6, by decide⟩)) ⟨1,3,0⟩ 163 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 328 [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 729785446298, 536305911102, 382525865162, 263028840638, 172727913114, 104890483415, 48279439685, 16338216105, 3175350125, 129561835, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m27_1 : availableMass (start (.two7 ⟨6, by decide⟩)) ⟨3,9,0⟩ 233 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨6, by decide⟩)) ⟨3,9,0⟩ 233 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 336 [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 729785446298, 536305911102, 382525865162, 263028840638, 172727913114, 106865701598, 61014368522, 31075619742, 13280704538, 4190415614, 695089098, 15842094, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m27_2 : availableMass (start (.two7 ⟨6, by decide⟩)) ⟨7,21,0⟩ 281 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨6, by decide⟩)) ⟨7,21,0⟩ 281 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 339 [4465528811802, 3719915309438, 3069196602314, 2505319875198, 2020561856282, 1607528817182, 1259156572938, 968710482014, 729785446298, 536305911102, 382525865162, 263028840638, 172727913114, 106865701598, 61014368522, 31075619742, 13280704538, 4190415614, 695089098, 16053050, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

theorem checked27 (q : Threshold) (hq : q ∈ thresholds (.two7 ⟨6, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two7 ⟨6, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨by decide, m27_0⟩
  · exact ⟨by decide, m27_1⟩
  · exact ⟨by decide, m27_2⟩

end Low53At2389PriceMass
