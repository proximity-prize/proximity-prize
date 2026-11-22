import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m15_0 : availableMass (start (.two6 ⟨9, by decide⟩)) ⟨1,3,0⟩ 35 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨9, by decide⟩)) ⟨1,3,0⟩ 35 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 218 [4496917930274, 3800786683178, 3186758143074, 2531571870189, 1917345333837, 1419304154205, 1022448100701, 712729285005, 477052161069, 303273525117, 180202515645, 97600613421, 46181641485, 17611765149, 4509491997, 445671885, 564927, 0, 0] (by decide +kernel) (by decide)

private theorem m15_1 : availableMass (start (.two6 ⟨9, by decide⟩)) ⟨2,6,0⟩ 79 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨9, by decide⟩)) ⟨2,6,0⟩ 79 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 216 [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1415218021940, 954132778316, 589859297372, 337129543532, 172464973436, 74536952204, 24166753436, 4325559212, 136684518, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m15_2 : availableMass (start (.two6 ⟨9, by decide⟩)) ⟨7,21,0⟩ 103 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨9, by decide⟩)) ⟨7,21,0⟩ 103 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 164 [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1440147592658, 1147727748314, 843348621397, 313231843635, 57115363299, 1859927549, 0, 0] (by decide +kernel) (by decide)

private theorem m15_3 : availableMass (start (.two6 ⟨9, by decide⟩)) ⟨13,38,0⟩ 109 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨9, by decide⟩)) ⟨13,38,0⟩ 109 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 146 [4496917930274, 3800786683178, 3188253162674, 2652398221754, 2186598325826, 1784525552714, 1440147592658, 1147727748314, 901824934754, 380507335012, 21487750992, 0, 0] (by decide +kernel) (by decide)

theorem checked15 (q : Threshold) (hq : q ∈ thresholds (.two6 ⟨9, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two6 ⟨9, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨by decide, m15_0⟩
  · exact ⟨by decide, m15_1⟩
  · exact ⟨by decide, m15_2⟩
  · exact ⟨by decide, m15_3⟩

end Low53At2389PriceMass
