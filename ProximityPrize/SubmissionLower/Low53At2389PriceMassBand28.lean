import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m28_0 : availableMass (start (.two7 ⟨7, by decide⟩)) ⟨1,3,0⟩ 206 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨7, by decide⟩)) ⟨1,3,0⟩ 206 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 371 [4456729984713, 3698265082881, 3038986509241, 2470117587633, 1983268084905, 1570434210913, 1223998618521, 936730403601, 701785105033, 512704704705, 363417627513, 248238741361, 161869357161, 99397228833, 56296553305, 28427970513, 12038563401, 3175341328, 157894210, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m28_1 : availableMass (start (.two7 ⟨7, by decide⟩)) ⟨3,9,0⟩ 290 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨7, by decide⟩)) ⟨3,9,0⟩ 290 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 393 [4456729984713, 3698265082881, 3038986509241, 2470117587633, 1983268084905, 1570434210913, 1223998618521, 936730403601, 701785105033, 512704704705, 363417627513, 248238741361, 161869357161, 99397228833, 56296553305, 28427970513, 12038563401, 3761857921, 617823033, 14133535, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m28_2 : availableMass (start (.two7 ⟨7, by decide⟩)) ⟨8,24,0⟩ 293 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨7, by decide⟩)) ⟨8,24,0⟩ 293 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 346 [4456729984713, 3698265082881, 3038986509241, 2470117587633, 1983268084905, 1570434210913, 1223998618521, 936730403601, 701785105033, 512704704705, 363417627513, 248238741361, 161869357161, 99397228833, 56296553305, 28427970513, 12038563401, 3761857921, 617823033, 14133535, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

theorem checked28 (q : Threshold) (hq : q ∈ thresholds (.two7 ⟨7, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two7 ⟨7, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨by decide, m28_0⟩
  · exact ⟨by decide, m28_1⟩
  · exact ⟨by decide, m28_2⟩

end Low53At2389PriceMass
