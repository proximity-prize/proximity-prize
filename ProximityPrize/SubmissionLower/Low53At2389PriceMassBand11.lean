import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m11_0 : availableMass (start (.two6 ⟨5, by decide⟩)) ⟨1,3,0⟩ 26 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨5, by decide⟩)) ⟨1,3,0⟩ 26 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 209 [4532662882374, 3890683591998, 3229217643852, 2526947832264, 1938261685524, 1452986444472, 1059669647412, 747327445512, 505444602804, 323974496184, 193339115412, 104429063112, 48603554772, 17690418744, 3986096244, 255641352, 0, 0] (by decide +kernel) (by decide)

private theorem m11_1 : availableMass (start (.two6 ⟨5, by decide⟩)) ⟨2,6,0⟩ 60 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨5, by decide⟩)) ⟨2,6,0⟩ 60 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 197 [4532662882374, 3890683591998, 3317021852982, 2806934554158, 2355830869542, 1790144400214, 1210296662038, 774969167062, 461525419414, 248332213846, 114759635734, 41181061078, 8973156502, 515879254, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m11_2 : availableMass (start (.two6 ⟨5, by decide⟩)) ⟨6,18,0⟩ 83 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨5, by decide⟩)) ⟨6,18,0⟩ 83 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 151 [4532662882374, 3890683591998, 3317021852982, 2806934554158, 2355830869542, 1959272258334, 1607405364003, 913793991042, 324106800978, 68261227554, 3467185557, 0, 0] (by decide +kernel) (by decide)

private theorem m11_3 : availableMass (start (.two6 ⟨5, by decide⟩)) ⟨12,35,0⟩ 91 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨5, by decide⟩)) ⟨12,35,0⟩ 91 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 131 [4532662882374, 3890683591998, 3317021852982, 2806934554158, 2355830869542, 1959272258334, 1612972464918, 1183713850440, 282470106830, 11167105642, 0] (by decide +kernel) (by decide)

theorem checked11 (q : Threshold) (hq : q ∈ thresholds (.two6 ⟨5, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two6 ⟨5, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨by decide, m11_0⟩
  · exact ⟨by decide, m11_1⟩
  · exact ⟨by decide, m11_2⟩
  · exact ⟨by decide, m11_3⟩

end Low53At2389PriceMass
