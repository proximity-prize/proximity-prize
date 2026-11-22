import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m7_0 : availableMass (start (.two6 ⟨1, by decide⟩)) ⟨1,3,0⟩ 26 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨1, by decide⟩)) ⟨1,3,0⟩ 26 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 209 [4568407834474, 3980580500818, 3354203059164, 2665499620824, 2076745021956, 1581684566184, 1172243499588, 840331951704, 577844935524, 376662347496, 228648967524, 125654458968, 59513368644, 22045126824, 5054047236, 329327064, 0, 0] (by decide +kernel) (by decide)

private theorem m7_1 : availableMass (start (.two6 ⟨1, by decide⟩)) ⟨3,9,0⟩ 49 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨1, by decide⟩)) ⟨3,9,0⟩ 49 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 159 [4568407834474, 3980580500818, 3445790543290, 2961470886562, 2266292923387, 1443818465899, 848452360291, 444167620963, 194447374315, 62284858747, 10183424659, 199290442, 0, 0] (by decide +kernel) (by decide)

private theorem m7_2 : availableMass (start (.two6 ⟨1, by decide⟩)) ⟨5,15,0⟩ 56 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨1, by decide⟩)) ⟨5,15,0⟩ 56 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 134 [4568407834474, 3980580500818, 3445790543290, 2961470886562, 2459994343402, 1452720658986, 673771575150, 239424148602, 49754073294, 2342307482, 0, 0] (by decide +kernel) (by decide)

private theorem m7_3 : availableMass (start (.two6 ⟨1, by decide⟩)) ⟨7,19,0⟩ 57 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨1, by decide⟩)) ⟨7,19,0⟩ 57 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 123 [4568407834474, 3980580500818, 3445790543290, 2961470886562, 2475523523288, 1370189824827, 524602888267, 128353123707, 10082331147, 136048, 0] (by decide +kernel) (by decide)

private theorem m7_4 : availableMass (start (.two6 ⟨1, by decide⟩)) ⟨8,24,0⟩ 72 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨1, by decide⟩)) ⟨8,24,0⟩ 72 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 127 [4568407834474, 3980580500818, 3445790543290, 2961470886562, 2525063413258, 2134018963954, 1208917287822, 347715840486, 42710729790, 192424602, 0] (by decide +kernel) (by decide)

private theorem m7_5 : availableMass (start (.two6 ⟨1, by decide⟩)) ⟨13,38,0⟩ 82 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨1, by decide⟩)) ⟨13,38,0⟩ 82 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 119 [4568407834474, 3980580500818, 3445790543290, 2961470886562, 2525063413258, 2134018963954, 1747708674346, 590631222944, 39055385856, 0] (by decide +kernel) (by decide)

private theorem m7_6 : availableMass (start (.two6 ⟨1, by decide⟩)) ⟨67,21,0⟩ 78 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨1, by decide⟩)) ⟨67,21,0⟩ 78 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 139 [4568407834474, 3980580500818, 3445790543290, 2961470886562, 2525063413258, 2134018963954, 1597043779190, 543555361608, 101036212620, 5830606752, 308268, 0] (by decide +kernel) (by decide)

theorem checked7 (q : Threshold) (hq : q ∈ thresholds (.two6 ⟨1, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two6 ⟨1, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, m7_0⟩
  · exact ⟨by decide, m7_1⟩
  · exact ⟨by decide, m7_2⟩
  · exact ⟨by decide, m7_3⟩
  · exact ⟨by decide, m7_4⟩
  · exact ⟨by decide, m7_5⟩
  · exact ⟨by decide, m7_6⟩

end Low53At2389PriceMass
