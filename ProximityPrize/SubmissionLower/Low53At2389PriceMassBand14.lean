import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m14_0 : availableMass (start (.two6 ⟨8, by decide⟩)) ⟨1,3,0⟩ 32 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨8, by decide⟩)) ⟨1,3,0⟩ 32 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 215 [4505854168299, 3823260910383, 3205206599754, 2519285310636, 1913765017272, 1420885070916, 1026561471504, 717541628892, 481404362856, 306559903092, 182249889216, 98547370764, 46356807192, 17414067876, 4286432112, 372589116, 103554, 0] (by decide +kernel) (by decide)

private theorem m14_1 : availableMass (start (.two6 ⟨8, by decide⟩)) ⟨2,6,0⟩ 73 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨8, by decide⟩)) ⟨2,6,0⟩ 73 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 210 [4505854168299, 3823260910383, 3220445335251, 2691032304855, 2228906461755, 1828212229119, 1369307969638, 891116715382, 544858869382, 306099626902, 152267437222, 62654003638, 18414283462, 2566488022, 27874529, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m14_2 : availableMass (start (.two6 ⟨8, by decide⟩)) ⟨7,21,0⟩ 96 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨8, by decide⟩)) ⟨7,21,0⟩ 96 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 157 [4505854168299, 3823260910383, 3220445335251, 2691032304855, 2228906461755, 1828212229119, 1483353810723, 1188995190951, 640085420085, 172244353965, 18658510269, 42091695, 0, 0] (by decide +kernel) (by decide)

private theorem m14_3 : availableMass (start (.two6 ⟨8, by decide⟩)) ⟨13,38,0⟩ 101 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨8, by decide⟩)) ⟨13,38,0⟩ 101 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 138 [4505854168299, 3823260910383, 3220445335251, 2691032304855, 2228906461755, 1828212229119, 1483353810723, 1188995190951, 753066989821, 103628408554, 488424714, 0] (by decide +kernel) (by decide)

theorem checked14 (q : Threshold) (hq : q ∈ thresholds (.two6 ⟨8, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two6 ⟨8, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨by decide, m14_0⟩
  · exact ⟨by decide, m14_1⟩
  · exact ⟨by decide, m14_2⟩
  · exact ⟨by decide, m14_3⟩

end Low53At2389PriceMass
