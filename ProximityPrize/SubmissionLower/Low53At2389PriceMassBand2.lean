import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m2_0 : availableMass (start .one4) ⟨2,4,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .one4) ⟨2,4,0⟩ 1 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 207 [4493720335568, 3730708851152, 3059893912272, 2475203870672, 1970595389648, 1540053444048, 1177591320272, 877250616272, 633101241552, 439241417168, 289797675728, 178924861392, 100806129872, 49652948432, 19705095888, 5230662608, 526050512, 542036] (by decide +kernel) (by decide)

private theorem m2_1 : availableMass (start .one4) ⟨2,5,0⟩ 3 < layerNeed := by
  rw [mass_eq (start .one4) ⟨2,5,0⟩ 3 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 186 [4524229271836, 3684712069209, 2947617937929, 2315891461737, 1781459146425, 1336232381241, 972107438889, 680965475529, 454672530777, 285079527705, 164022272841, 83321456169, 34782651129, 10196314617, 1337786985, 9248562] (by decide +kernel) (by decide)

private theorem m2_2 : availableMass (start .one4) ⟨2,6,0⟩ 22 < layerNeed := by
  rw [mass_eq (start .one4) ⟨2,6,0⟩ 22 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 187 [4679106249028, 4263074300183, 3529677448163, 2745781921575, 2086692805067, 1541900921039, 1100800323891, 752688300023, 486765367835, 292135277727, 157805012099, 72684785351, 25588043883, 5231466095, 235246722, 0] (by decide +kernel) (by decide)

private theorem m2_3 : availableMass (start .one4) ⟨3,9,0⟩ 24 < layerNeed := by
  rw [mass_eq (start .one4) ⟨3,9,0⟩ 24 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 150 [4679106249028, 4274622143268, 3481139225859, 2498607702283, 1719443668851, 1120852567803, 679690571107, 372464580459, 175332227283, 64101872731, 14232607683, 834252747, 0] (by decide +kernel) (by decide)

private theorem m2_4 : availableMass (start .one4) ⟨4,12,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .one4) ⟨4,12,0⟩ 43 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 146 [4679106249028, 4274622143268, 3894297784836, 3437423401626, 2389652993944, 1488279288280, 846690744344, 421904233048, 170030655640, 46274943704, 4936059160, 8296344, 0] (by decide +kernel) (by decide)

private theorem m2_5 : availableMass (start .one4) ⟨6,17,0⟩ 49 < layerNeed := by
  rw [mass_eq (start .one4) ⟨6,17,0⟩ 49 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 127 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2646510692640, 1432849478676, 660852452040, 232488995964, 47232024432, 2061662142, 0] (by decide +kernel) (by decide)

private theorem m2_6 : availableMass (start .one4) ⟨8,24,0⟩ 50 < layerNeed := by
  rw [mass_eq (start .one4) ⟨8,24,0⟩ 50 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 108 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2567980650652, 1100167886564, 332522895492, 46497284900, 434381502] (by decide +kernel) (by decide)

private theorem m2_7 : availableMass (start .one4) ⟨67,15,0⟩ 51 < layerNeed := by
  rw [mass_eq (start .one4) ⟨67,15,0⟩ 51 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 137 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2679633916912, 1218015146003, 440335188251, 107970140307, 9032496842, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m2_8 : availableMass (start .one4) ⟨69,27,0⟩ 58 < layerNeed := by
  rw [mass_eq (start .one4) ⟨69,27,0⟩ 58 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 111 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3148456950328, 1495738883835, 368968506691, 43524655107, 584638755, 0] (by decide +kernel) (by decide)

private theorem m2_9 : availableMass (start .one4) ⟨69,30,0⟩ 60 < layerNeed := by
  rw [mass_eq (start .one4) ⟨69,30,0⟩ 60 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 108 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3203080394436, 1711134843018, 395520139482, 39127267690, 206507711] (by decide +kernel) (by decide)

private theorem m2_10 : availableMass (start .one4) ⟨70,33,0⟩ 61 < layerNeed := by
  rw [mass_eq (start .one4) ⟨70,33,0⟩ 61 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 105 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3203080394436, 1814606811986, 379450123654, 28501861306, 18574756] (by decide +kernel) (by decide)

private theorem m2_11 : availableMass (start .one4) ⟨99,46,0⟩ 63 < layerNeed := by
  rw [mass_eq (start .one4) ⟨99,46,0⟩ 63 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 96 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3203080394436, 1908351058410, 223955427144, 2280664997] (by decide +kernel) (by decide)

private theorem m2_12 : availableMass (start .one4) ⟨100,45,0⟩ 64 < layerNeed := by
  rw [mass_eq (start .one4) ⟨100,45,0⟩ 64 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 97 [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3203080394436, 2091225758196, 290015261925, 4981604753, 0] (by decide +kernel) (by decide)

theorem checked2 (q : Threshold) (hq : q ∈ thresholds .one4) :
    0 < q.j ∧ availableMass (start .one4) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, m2_0⟩
  · exact ⟨by decide, m2_1⟩
  · exact ⟨by decide, m2_2⟩
  · exact ⟨by decide, m2_3⟩
  · exact ⟨by decide, m2_4⟩
  · exact ⟨by decide, m2_5⟩
  · exact ⟨by decide, m2_6⟩
  · exact ⟨by decide, m2_7⟩
  · exact ⟨by decide, m2_8⟩
  · exact ⟨by decide, m2_9⟩
  · exact ⟨by decide, m2_10⟩
  · exact ⟨by decide, m2_11⟩
  · exact ⟨by decide, m2_12⟩

end Low53At2389PriceMass
