import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m8_0 : availableMass (start (.two6 ⟨2, by decide⟩)) ⟨1,3,0⟩ 25 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨2, by decide⟩)) ⟨1,3,0⟩ 25 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 208 [4559471596449, 3958106273613, 3304656272613, 2613672788565, 2027606444733, 1537433504157, 1134236045685, 809201963973, 553624969485, 358904588493, 216546163077, 118160851125, 55465626333, 20283278205, 4542412053, 277448997, 0, 0] (by decide +kernel) (by decide)

private theorem m8_1 : availableMass (start (.two6 ⟨2, by decide⟩)) ⟨2,6,0⟩ 26 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨2, by decide⟩)) ⟨2,6,0⟩ 26 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 163 [4559471596449, 3958106273613, 3234819001780, 2359678310740, 1657198973620, 1110865787668, 700718445172, 406939965652, 209856695860, 89938309780, 27797808628, 4191520852, 58674686, 0] (by decide +kernel) (by decide)

private theorem m8_2 : availableMass (start (.two6 ⟨2, by decide⟩)) ⟨3,9,0⟩ 49 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨2, by decide⟩)) ⟨3,9,0⟩ 49 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 159 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2228567171880, 1414575256404, 828233043888, 432010059132, 188445810936, 60149792100, 9801479424, 191245932, 0, 0] (by decide +kernel) (by decide)

private theorem m8_3 : availableMass (start (.two6 ⟨2, by decide⟩)) ⟨5,15,0⟩ 55 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨2, by decide⟩)) ⟨5,15,0⟩ 55 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 133 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2387358775913, 1367075566135, 624256213303, 216318662047, 42652763119, 1695347490, 0, 0] (by decide +kernel) (by decide)

private theorem m8_4 : availableMass (start (.two6 ⟨2, by decide⟩)) ⟨7,19,0⟩ 56 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨2, by decide⟩)) ⟨7,19,0⟩ 56 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 122 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2402227118368, 1274101147760, 476519436460, 111375141160, 7680861860, 0, 0] (by decide +kernel) (by decide)

private theorem m8_5 : availableMass (start (.two6 ⟨2, by decide⟩)) ⟨7,21,0⟩ 77 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨2, by decide⟩)) ⟨7,21,0⟩ 77 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 138 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1554639259477, 621880125693, 149402048829, 11118038397, 3221, 0] (by decide +kernel) (by decide)

private theorem m8_6 : availableMass (start (.two6 ⟨2, by decide⟩)) ⟨13,38,0⟩ 82 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨2, by decide⟩)) ⟨13,38,0⟩ 82 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 119 [4559471596449, 3958106273613, 3413598370713, 2922836803461, 2482755277329, 2090332287549, 1705499476979, 574586865770, 37887211082, 0] (by decide +kernel) (by decide)

theorem checked8 (q : Threshold) (hq : q ∈ thresholds (.two6 ⟨2, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two6 ⟨2, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, m8_0⟩
  · exact ⟨by decide, m8_1⟩
  · exact ⟨by decide, m8_2⟩
  · exact ⟨by decide, m8_3⟩
  · exact ⟨by decide, m8_4⟩
  · exact ⟨by decide, m8_5⟩
  · exact ⟨by decide, m8_6⟩

end Low53At2389PriceMass
