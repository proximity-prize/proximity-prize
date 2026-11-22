import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m13_0 : availableMass (start (.two6 ⟨7, by decide⟩)) ⟨1,3,0⟩ 30 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨7, by decide⟩)) ⟨1,3,0⟩ 30 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 213 [4514790406324, 3845735137588, 3220116474026, 2522500455024, 1922700425652, 1432400872896, 1038405053844, 728226703152, 490090033044, 312929733312, 186390971316, 100829391984, 47311117812, 17612748864, 4221362772, 334514736, 14781, 0] (by decide +kernel) (by decide)

private theorem m13_1 : availableMass (start (.two6 ⟨7, by decide⟩)) ⟨2,6,0⟩ 68 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨7, by decide⟩)) ⟨2,6,0⟩ 68 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 205 [4514790406324, 3845735137588, 3252637507828, 2729666387956, 2271214597684, 1851383274190, 1303613845314, 843179548866, 510580328514, 282422741442, 136889944386, 53741693634, 14314345026, 1520853954, 3043734, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m13_2 : availableMass (start (.two6 ⟨7, by decide⟩)) ⟨6,18,0⟩ 93 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨7, by decide⟩)) ⟨6,18,0⟩ 93 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 161 [4514790406324, 3845735137588, 3252637507828, 2729666387956, 2271214597684, 1871898905524, 1526560028788, 1203743794828, 590501955388, 178659046876, 26168886652, 339417866, 0, 0] (by decide +kernel) (by decide)

private theorem m13_3 : availableMass (start (.two6 ⟨7, by decide⟩)) ⟨13,38,0⟩ 95 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨7, by decide⟩)) ⟨13,38,0⟩ 95 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 132 [4514790406324, 3845735137588, 3252637507828, 2729666387956, 2271214597684, 1871898905524, 1526560028788, 1220973646207, 424384605608, 23770799217, 0] (by decide +kernel) (by decide)

private theorem m13_4 : availableMass (start (.two6 ⟨7, by decide⟩)) ⟨67,36,0⟩ 100 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨7, by decide⟩)) ⟨67,36,0⟩ 100 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 139 [4514790406324, 3845735137588, 3252637507828, 2729666387956, 2271214597684, 1871898905524, 1526560028788, 1230262633588, 712174564486, 75818097813, 313138476, 0] (by decide +kernel) (by decide)

theorem checked13 (q : Threshold) (hq : q ∈ thresholds (.two6 ⟨7, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two6 ⟨7, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, m13_0⟩
  · exact ⟨by decide, m13_1⟩
  · exact ⟨by decide, m13_2⟩
  · exact ⟨by decide, m13_3⟩
  · exact ⟨by decide, m13_4⟩

end Low53At2389PriceMass
