import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m24_0 : availableMass (start (.two7 ⟨3, by decide⟩)) ⟨1,3,0⟩ 38 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨3, by decide⟩)) ⟨1,3,0⟩ 38 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 203 [4491925293069, 3784865989109, 3159826881533, 2536287708676, 1899401475488, 1380980184320, 968918547552, 650004277184, 411425981216, 240773163648, 126036224480, 55606459712, 18276061344, 3238117376, 90310153, 0, 0] (by decide +kernel) (by decide)

private theorem m24_1 : availableMass (start (.two7 ⟨3, by decide⟩)) ⟨2,6,0⟩ 86 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨3, by decide⟩)) ⟨2,6,0⟩ 86 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 212 [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 986200575352, 588275990238, 315641141290, 144701281374, 50929810938, 10544227966, 506364456, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m24_2 : availableMass (start (.two7 ⟨3, by decide⟩)) ⟨6,18,0⟩ 116 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨3, by decide⟩)) ⟨6,18,0⟩ 116 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 182 [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 1064650717253, 813786470093, 579747567033, 202064904473, 27224257121, 220057246, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m24_3 : availableMass (start (.two7 ⟨3, by decide⟩)) ⟨12,36,0⟩ 119 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨3, by decide⟩)) ⟨12,36,0⟩ 119 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 157 [4491925293069, 3784865989109, 3159826881533, 2610926737893, 2132443170413, 1718812635989, 1364630436189, 1064650717253, 813786470093, 601620714435, 152922411032, 1554900477, 0, 0] (by decide +kernel) (by decide)

theorem checked24 (q : Threshold) (hq : q ∈ thresholds (.two7 ⟨3, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two7 ⟨3, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨by decide, m24_0⟩
  · exact ⟨by decide, m24_1⟩
  · exact ⟨by decide, m24_2⟩
  · exact ⟨by decide, m24_3⟩

end Low53At2389PriceMass
