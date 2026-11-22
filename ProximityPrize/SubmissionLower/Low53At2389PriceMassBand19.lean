import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m19_0 : availableMass (start (.two6 ⟨13, by decide⟩)) ⟨1,3,0⟩ 54 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨13, by decide⟩)) ⟨1,3,0⟩ 54 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 237 [4461172978174, 3710889774358, 3059484472366, 2497861889350, 1995380945828, 1474809540552, 1051629688908, 726096233448, 482062185756, 304816629096, 181084718412, 99027680328, 48242813148, 19763486856, 6059143116, 1035295272, 33755095, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m19_1 : availableMass (start (.two6 ⟨13, by decide⟩)) ⟨2,6,0⟩ 122 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨13, by decide⟩)) ⟨2,6,0⟩ 122 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 259 [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 748884134590, 559539645910, 375238778132, 201311328504, 95027537640, 36974521560, 10284705480, 1387040952, 17364606, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m19_2 : availableMass (start (.two6 ⟨13, by decide⟩)) ⟨6,18,0⟩ 159 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨13, by decide⟩)) ⟨6,18,0⟩ 159 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 227 [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 748884134590, 559539645910, 408601906414, 290487250438, 200050951966, 102425127217, 16422612118, 350649492, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m19_3 : availableMass (start (.two6 ⟨13, by decide⟩)) ⟨12,35,0⟩ 173 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨13, by decide⟩)) ⟨12,35,0⟩ 173 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 213 [4461172978174, 3710889774358, 3059484472366, 2497861889350, 2017365782110, 1609778847094, 1267322720398, 982657977766, 748884134590, 559539645910, 408601906414, 290487250438, 200050951966, 132587224630, 61805091729, 1606144150, 0, 0] (by decide +kernel) (by decide)

theorem checked19 (q : Threshold) (hq : q ∈ thresholds (.two6 ⟨13, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two6 ⟨13, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨by decide, m19_0⟩
  · exact ⟨by decide, m19_1⟩
  · exact ⟨by decide, m19_2⟩
  · exact ⟨by decide, m19_3⟩

end Low53At2389PriceMass
