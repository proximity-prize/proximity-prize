import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m23_0 : availableMass (start (.two7 ⟨2, by decide⟩)) ⟨1,3,0⟩ 39 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨2, by decide⟩)) ⟨1,3,0⟩ 39 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 204 [4500724120158, 3806516215666, 3190036974606, 2584310124800, 1946501683179, 1421982153935, 1002699534611, 676268730807, 430539656123, 253597232159, 133761388515, 59587062791, 19864200587, 3617755503, 110488324, 0, 0] (by decide +kernel) (by decide)

private theorem m23_1 : availableMass (start (.two7 ⟨2, by decide⟩)) ⟨2,6,0⟩ 87 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨2, by decide⟩)) ⟨2,6,0⟩ 87 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 213 [4500724120158, 3806516215666, 3190036974606, 2646129025458, 2169736941790, 1755907242258, 1399788390606, 1030502539518, 621324612553, 336362261257, 156012616601, 55885457977, 11970206377, 635972655, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m23_2 : availableMass (start (.two7 ⟨2, by decide⟩)) ⟨7,21,0⟩ 105 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨2, by decide⟩)) ⟨7,21,0⟩ 105 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 163 [4500724120158, 3806516215666, 3190036974606, 2646129025458, 2169736941790, 1755907242258, 1399788390606, 1096630795666, 817261337620, 303516049724, 41713844604, 366231926, 0, 0] (by decide +kernel) (by decide)

private theorem m23_3 : availableMass (start (.two7 ⟨2, by decide⟩)) ⟨67,36,0⟩ 110 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨2, by decide⟩)) ⟨67,36,0⟩ 110 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 148 [4500724120158, 3806516215666, 3190036974606, 2646129025458, 2169736941790, 1755907242258, 1399788390606, 1096630795666, 841786811358, 356610830407, 13454647761, 0, 0] (by decide +kernel) (by decide)

theorem checked23 (q : Threshold) (hq : q ∈ thresholds (.two7 ⟨2, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two7 ⟨2, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨by decide, m23_0⟩
  · exact ⟨by decide, m23_1⟩
  · exact ⟨by decide, m23_2⟩
  · exact ⟨by decide, m23_3⟩

end Low53At2389PriceMass
