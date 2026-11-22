import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m25_0 : availableMass (start (.two7 ⟨4, by decide⟩)) ⟨1,3,0⟩ 38 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨4, by decide⟩)) ⟨1,3,0⟩ 38 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 203 [4483126465980, 3763215762552, 3129616788460, 2502175061577, 1866309226357, 1351332386105, 944125034653, 630644580001, 397415214149, 231527913097, 120640436845, 52977329393, 17329918741, 3056316889, 84881542, 0, 0] (by decide +kernel) (by decide)

private theorem m25_1 : availableMass (start (.two7 ⟨4, by decide⟩)) ⟨2,6,0⟩ 86 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨4, by decide⟩)) ⟨2,6,0⟩ 86 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 212 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 956682942221, 568177511623, 303502390143, 138508850871, 48528658735, 10002132135, 478365477, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m25_2 : availableMass (start (.two7 ⟨4, by decide⟩)) ⟨5,15,0⟩ 122 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨4, by decide⟩)) ⟨5,15,0⟩ 122 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 197 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 583508323896, 328362534945, 83632160749, 7428750873, 1966136, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m25_3 : availableMass (start (.two7 ⟨4, by decide⟩)) ⟨11,33,0⟩ 128 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨4, by decide⟩)) ⟨11,33,0⟩ 128 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 169 [4483126465980, 3763215762552, 3129616788460, 2575724450328, 2095149399036, 1681718029720, 1329472481772, 1032670638840, 785786128828, 583508323896, 385107069168, 53392565308, 39941822, 0, 0] (by decide +kernel) (by decide)

theorem checked25 (q : Threshold) (hq : q ∈ thresholds (.two7 ⟨4, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two7 ⟨4, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨by decide, m25_0⟩
  · exact ⟨by decide, m25_1⟩
  · exact ⟨by decide, m25_2⟩
  · exact ⟨by decide, m25_3⟩

end Low53At2389PriceMass
