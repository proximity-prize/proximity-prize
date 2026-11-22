import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m6_0 : availableMass (start (.two6 ⟨0, by decide⟩)) ⟨1,3,0⟩ 26 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨0, by decide⟩)) ⟨1,3,0⟩ 26 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 209 [4577344072499, 4003054728023, 3385449412992, 2700137567964, 2111365856064, 1613859096612, 1200386962632, 863583078252, 595945018704, 389834310324, 237476430552, 130960807932, 62240822112, 23133803844, 5321034984, 347748492, 0, 0] (by decide +kernel) (by decide)

private theorem m6_1 : availableMass (start (.two6 ⟨0, by decide⟩)) ⟨3,9,0⟩ 50 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨0, by decide⟩)) ⟨3,9,0⟩ 50 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 160 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2347603381233, 1508946054683, 894038912843, 472926382403, 210087695363, 68952323723, 11899979483, 286775522, 0, 0] (by decide +kernel) (by decide)

private theorem m6_2 : availableMass (start (.two6 ⟨0, by decide⟩)) ⟨5,15,0⟩ 56 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨0, by decide⟩)) ⟨5,15,0⟩ 56 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 134 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2501099975999, 1482065102579, 689728307819, 245907921299, 51262603691, 2420053359, 0, 0] (by decide +kernel) (by decide)

private theorem m6_3 : availableMass (start (.two6 ⟨0, by decide⟩)) ⟨7,19,0⟩ 57 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨0, by decide⟩)) ⟨7,19,0⟩ 57 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 123 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2516914901691, 1397837518085, 537008633261, 131816952237, 10384795013, 140517, 0] (by decide +kernel) (by decide)

private theorem m6_4 : availableMass (start (.two6 ⟨0, by decide⟩)) ⟨8,24,0⟩ 72 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨0, by decide⟩)) ⟨8,24,0⟩ 72 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 127 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1237704963515, 357133160015, 43995538115, 198724905, 0] (by decide +kernel) (by decide)

private theorem m6_5 : availableMass (start (.two6 ⟨0, by decide⟩)) ⟨69,37,0⟩ 76 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨0, by decide⟩)) ⟨69,37,0⟩ 76 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 114 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1367631731231, 203511717259, 3485672986, 0] (by decide +kernel) (by decide)

private theorem m6_6 : availableMass (start (.two6 ⟨0, by decide⟩)) ⟨69,39,0⟩ 81 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨0, by decide⟩)) ⟨69,39,0⟩ 81 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 117 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1739221821012, 449325374010, 18214925810, 0] (by decide +kernel) (by decide)

theorem checked6 (q : Threshold) (hq : q ∈ thresholds (.two6 ⟨0, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two6 ⟨0, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, m6_0⟩
  · exact ⟨by decide, m6_1⟩
  · exact ⟨by decide, m6_2⟩
  · exact ⟨by decide, m6_3⟩
  · exact ⟨by decide, m6_4⟩
  · exact ⟨by decide, m6_5⟩
  · exact ⟨by decide, m6_6⟩

end Low53At2389PriceMass
