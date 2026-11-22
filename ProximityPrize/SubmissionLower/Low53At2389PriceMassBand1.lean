import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m1_0 : availableMass (start .one3) ⟨2,5,0⟩ 3 < layerNeed := by
  rw [mass_eq (start .one3) ⟨2,5,0⟩ 3 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 209 [4583084299747, 3833064805960, 3160055470728, 2569940874696, 2057525884936, 1617558745416, 1244731077000, 933677877448, 678977521416, 475151760456, 316665723016, 197927914440, 113290216968, 57047889736, 23439568776, 6647267016, 796374280, 3161993] (by decide +kernel) (by decide)

private theorem m1_1 : availableMass (start .one3) ⟨2,6,0⟩ 10 < layerNeed := by
  rw [mass_eq (start .one3) ⟨2,6,0⟩ 10 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 193 [4727530820122, 4040037260832, 3265619205324, 2595368352504, 2022303798372, 1539308590032, 1139129725692, 814378154664, 557528777364, 360920445312, 216755961132, 117102078552, 53889502404, 18912888624, 3830844252, 166228894, 0] (by decide +kernel) (by decide)

private theorem m1_2 : availableMass (start .one3) ⟨3,9,0⟩ 23 < layerNeed := by
  rw [mass_eq (start .one3) ⟨3,9,0⟩ 23 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 160 [4740005313959, 4433739636828, 3653605056914, 2712160195586, 1945726192754, 1337437713122, 869999439698, 525686073794, 286342335026, 133382961314, 47792708882, 10126352258, 508826329, 0] (by decide +kernel) (by decide)

private theorem m1_3 : availableMass (start .one3) ⟨4,12,0⟩ 26 < layerNeed := by
  rw [mass_eq (start .one3) ⟨4,12,0⟩ 26 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 136 [4740005313959, 4439709210263, 3747889761194, 2585305558964, 1684023272264, 1018898791364, 555706052264, 259169230964, 92962743464, 19711245764, 989921470, 0] (by decide +kernel) (by decide)

private theorem m1_4 : availableMass (start .one3) ⟨5,15,0⟩ 40 < layerNeed := by
  rw [mass_eq (start .one3) ⟨5,15,0⟩ 40 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 131 [4740005313959, 4439709210263, 4152103344383, 3562210255827, 2284933848087, 1322519562723, 675224994639, 282803997531, 82833642759, 10714219347, 66353552] (by decide +kernel) (by decide)

private theorem m1_5 : availableMass (start .one3) ⟨6,18,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .one3) ⟨6,18,0⟩ 43 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 121 [4740005313959, 4439709210263, 4152103344383, 3718266552593, 2346389605559, 1235453952431, 543771305111, 174976883759, 28673150519, 556310504, 0] (by decide +kernel) (by decide)

private theorem m1_6 : availableMass (start .one3) ⟨7,20,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .one3) ⟨7,20,0⟩ 47 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 118 [4740005313959, 4439709210263, 4152103344383, 3864865238591, 2667928246251, 1356073213771, 563320265979, 162172412859, 20002667851, 92904891] (by decide +kernel) (by decide)

private theorem m1_7 : availableMass (start .one3) ⟨8,24,0⟩ 49 < layerNeed := by
  rw [mass_eq (start .one3) ⟨8,24,0⟩ 49 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 110 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2786297300517, 1257395782413, 422858453709, 76752635493, 2211709670, 0] (by decide +kernel) (by decide)

private theorem m1_8 : availableMass (start .one3) ⟨11,33,0⟩ 50 < layerNeed := by
  rw [mass_eq (start .one3) ⟨11,33,0⟩ 50 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 95 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2696417850675, 885444335094, 148162021158, 3070914490] (by decide +kernel) (by decide)

private theorem m1_9 : availableMass (start .one3) ⟨66,4,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .one3) ⟨66,4,0⟩ 1 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 236 [4074394190516, 2559977024008, 1392434410420, 523402165692, 43868253843, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m1_10 : availableMass (start .one3) ⟨67,15,0⟩ 49 < layerNeed := by
  rw [mass_eq (start .one3) ⟨67,15,0⟩ 49 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 140 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2779940605881, 1285514333013, 485898634065, 125911129773, 10241306207, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m1_11 : availableMass (start .one3) ⟨69,22,0⟩ 50 < layerNeed := by
  rw [mass_eq (start .one3) ⟨69,22,0⟩ 50 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 116 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2747498233766, 1039284071473, 285556819193, 43275915913, 1471349521, 0] (by decide +kernel) (by decide)

private theorem m1_12 : availableMass (start .one3) ⟨69,31,0⟩ 51 < layerNeed := by
  rw [mass_eq (start .one3) ⟨69,31,0⟩ 51 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 99 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2735827566091, 801698737251, 128348822583, 4638350487, 0] (by decide +kernel) (by decide)

private theorem m1_13 : availableMass (start .one3) ⟨71,40,0⟩ 53 < layerNeed := by
  rw [mass_eq (start .one3) ⟨71,40,0⟩ 53 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 91 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2943362148010, 728759511874, 62468033910, 94035648] (by decide +kernel) (by decide)

private theorem m1_14 : availableMass (start .one3) ⟨70,42,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one3) ⟨70,42,0⟩ 55 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 91 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3226528425316, 912396526977, 83047074177, 174513099] (by decide +kernel) (by decide)

private theorem m1_15 : availableMass (start .one3) ⟨72,41,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one3) ⟨72,41,0⟩ 57 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 94 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3453544405103, 1216169313452, 145128428028, 1509315092] (by decide +kernel) (by decide)

private theorem m1_16 : availableMass (start .one3) ⟨100,39,0⟩ 52 < layerNeed := by
  rw [mass_eq (start .one3) ⟨100,39,0⟩ 52 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 91 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 2725328422137, 560688479978, 36557643506, 27131192] (by decide +kernel) (by decide)

private theorem m1_17 : availableMass (start .one3) ⟨100,40,0⟩ 54 < layerNeed := by
  rw [mass_eq (start .one3) ⟨100,40,0⟩ 54 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 92 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3061784881275, 740274950469, 56938739733, 119257909] (by decide +kernel) (by decide)

private theorem m1_18 : availableMass (start .one3) ⟨115,44,0⟩ 58 < layerNeed := by
  rw [mass_eq (start .one3) ⟨115,44,0⟩ 58 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 93 [4740005313959, 4439709210263, 4152103344383, 3876938262239, 3517616412649, 1172382730201, 94599892273, 293443019] (by decide +kernel) (by decide)

theorem checked1 (q : Threshold) (hq : q ∈ thresholds .one3) :
    0 < q.j ∧ availableMass (start .one3) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, m1_0⟩
  · exact ⟨by decide, m1_1⟩
  · exact ⟨by decide, m1_2⟩
  · exact ⟨by decide, m1_3⟩
  · exact ⟨by decide, m1_4⟩
  · exact ⟨by decide, m1_5⟩
  · exact ⟨by decide, m1_6⟩
  · exact ⟨by decide, m1_7⟩
  · exact ⟨by decide, m1_8⟩
  · exact ⟨by decide, m1_9⟩
  · exact ⟨by decide, m1_10⟩
  · exact ⟨by decide, m1_11⟩
  · exact ⟨by decide, m1_12⟩
  · exact ⟨by decide, m1_13⟩
  · exact ⟨by decide, m1_14⟩
  · exact ⟨by decide, m1_15⟩
  · exact ⟨by decide, m1_16⟩
  · exact ⟨by decide, m1_17⟩
  · exact ⟨by decide, m1_18⟩

end Low53At2389PriceMass
