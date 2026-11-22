import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m4_0 : availableMass (start .one6) ⟨1,3,0⟩ 23 < layerNeed := by
  rw [mass_eq (start .one6) ⟨1,3,0⟩ 23 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 206 [4577344072499, 4001228654631, 3326080128474, 2647413430734, 2066519969994, 1576294130766, 1169494248666, 838742610414, 576525453834, 375192967854, 226959292506, 123902518926, 57964689354, 20951797134, 4533786714, 244567502, 0, 0] (by decide +kernel) (by decide)

private theorem m4_1 : availableMass (start .one6) ⟨3,9,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .one6) ⟨3,9,0⟩ 44 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 154 [4577344072499, 4003054728023, 3477982715867, 2955329592714, 2073190233524, 1302054153224, 748952614724, 379099682024, 156659659124, 44747090024, 5426758724, 22914708, 0] (by decide +kernel) (by decide)

private theorem m4_2 : availableMass (start .one6) ⟨5,15,0⟩ 50 < layerNeed := by
  rw [mass_eq (start .one6) ⟨5,15,0⟩ 50 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 128 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2212409481437, 1153001880239, 496285694519, 153069811439, 22572620951, 274547437, 0] (by decide +kernel) (by decide)

private theorem m4_3 : availableMass (start .one6) ⟨6,18,0⟩ 72 < layerNeed := by
  rw [mass_eq (start .one6) ⟨6,18,0⟩ 72 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 140 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1366145661992, 544805823848, 144231497384, 14092322792, 9979604, 0] (by decide +kernel) (by decide)

private theorem m4_4 : availableMass (start .one6) ⟨12,36,0⟩ 78 < layerNeed := by
  rw [mass_eq (start .one6) ⟨12,36,0⟩ 78 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 117 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1586427316016, 370480887179, 15674609119, 0] (by decide +kernel) (by decide)

private theorem m4_5 : availableMass (start .one6) ⟨70,35,0⟩ 80 < layerNeed := by
  rw [mass_eq (start .one6) ⟨70,35,0⟩ 80 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 120 [4577344072499, 4003054728023, 3477982715867, 3000104969663, 2567371549187, 2177705640359, 1693627658044, 432786580189, 23775174061, 0] (by decide +kernel) (by decide)

theorem checked4 (q : Threshold) (hq : q ∈ thresholds .one6) :
    0 < q.j ∧ availableMass (start .one6) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, m4_0⟩
  · exact ⟨by decide, m4_1⟩
  · exact ⟨by decide, m4_2⟩
  · exact ⟨by decide, m4_3⟩
  · exact ⟨by decide, m4_4⟩
  · exact ⟨by decide, m4_5⟩

end Low53At2389PriceMass
