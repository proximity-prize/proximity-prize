import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m20_0 : availableMass (start (.two6 ⟨14, by decide⟩)) ⟨1,3,0⟩ 237 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨14, by decide⟩)) ⟨1,3,0⟩ 237 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 420 [4452236740149, 3688415547153, 3027292299789, 2459227806249, 1975057646181, 1566092170689, 1224116502333, 941390535129, 710648934549, 525101137521, 378431352429, 264798559113, 178836508869, 115653724449, 70833500061, 40433901369, 20987765493, 9502701009, 3461087949, 814784949, 36616209, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m20_1 : availableMass (start (.two6 ⟨14, by decide⟩)) ⟨8,24,0⟩ 298 < layerNeed := by
  rw [mass_eq (start (.two6 ⟨14, by decide⟩)) ⟨8,24,0⟩ 298 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 353 [4452236740149, 3688415547153, 3027292299789, 2459227806249, 1975057646181, 1566092170689, 1224116502333, 941390535129, 710648934549, 525101137521, 378431352429, 264798559113, 178836508869, 115653724449, 70833500061, 40433901369, 20987765493, 9502701009, 3461087949, 820143351, 46422905, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide)

theorem checked20 (q : Threshold) (hq : q ∈ thresholds (.two6 ⟨14, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two6 ⟨14, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨by decide, m20_0⟩
  · exact ⟨by decide, m20_1⟩

end Low53At2389PriceMass
