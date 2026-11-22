import ProximityPrize.SubmissionLower.Low53At2389PriceMassBase

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Low53At2389PriceMass
open K1_13_8_2 (Threshold)
open Low53At2389Price (layerNeed)
open Low53At2389PriceCaps (Band start thresholds)
open Low53At2389PriceLayer (availableMass)
private theorem m22_0 : availableMass (start (.two7 ⟨1, by decide⟩)) ⟨1,3,0⟩ 39 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨1, by decide⟩)) ⟨1,3,0⟩ 39 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 204 [4509522947247, 3828166442223, 3220247067679, 2618615837949, 1979838203600, 1451872554120, 1027720648640, 695830807160, 444720469680, 262976196200, 139253666720, 62277681240, 20842159760, 3810142280, 116756395, 0, 0] (by decide +kernel) (by decide)

private theorem m22_1 : availableMass (start (.two7 ⟨1, by decide⟩)) ⟨2,6,0⟩ 88 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨1, by decide⟩)) ⟨2,6,0⟩ 88 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 214 [4509522947247, 3828166442223, 3220247067679, 2681331313023, 2207030713167, 1793001848527, 1434946345023, 1074144350593, 655427511164, 357879799528, 167867499148, 61157794664, 13533056380, 790840264, 0, 0, 0, 0] (by decide +kernel) (by decide)

private theorem m22_2 : availableMass (start (.two7 ⟨1, by decide⟩)) ⟨8,24,0⟩ 104 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨1, by decide⟩)) ⟨8,24,0⟩ 104 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 157 [4509522947247, 3828166442223, 3220247067679, 2681331313023, 2207030713167, 1793001848527, 1434946345023, 1128610874079, 822364818201, 251888892669, 21106436229, 1664518, 0, 0] (by decide +kernel) (by decide)

private theorem m22_3 : availableMass (start (.two7 ⟨1, by decide⟩)) ⟨67,21,0⟩ 106 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨1, by decide⟩)) ⟨67,21,0⟩ 106 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 164 [4509522947247, 3828166442223, 3220247067679, 2681331313023, 2207030713167, 1793001848527, 1434946345023, 1128610874079, 853727166201, 298504369334, 33938499542, 314585871, 0, 0] (by decide +kernel) (by decide)

private theorem m22_4 : availableMass (start (.two7 ⟨1, by decide⟩)) ⟨68,39,0⟩ 109 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨1, by decide⟩)) ⟨68,39,0⟩ 109 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 144 [4509522947247, 3828166442223, 3220247067679, 2681331313023, 2207030713167, 1793001848527, 1434946345023, 1128610874079, 869787152623, 307832122803, 6400728715, 0] (by decide +kernel) (by decide)

private theorem m22_5 : availableMass (start (.two7 ⟨1, by decide⟩)) ⟨98,39,0⟩ 110 < layerNeed := by
  rw [mass_eq (start (.two7 ⟨1, by decide⟩)) ⟨98,39,0⟩ 110 (Low53At2389PriceCaps.start_or_index _) (by decide)]
  exact Low53At2389PriceLayer.sumBelow_lt _ 145 [4509522947247, 3828166442223, 3220247067679, 2681331313023, 2207030713167, 1793001848527, 1434946345023, 1128610874079, 869787152623, 348019917907, 8397854266, 0, 0] (by decide +kernel) (by decide)

theorem checked22 (q : Threshold) (hq : q ∈ thresholds (.two7 ⟨1, by decide⟩)) :
    0 < q.j ∧ availableMass (start (.two7 ⟨1, by decide⟩)) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  simp only [thresholds, Low53At2389PriceThresholds.thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, m22_0⟩
  · exact ⟨by decide, m22_1⟩
  · exact ⟨by decide, m22_2⟩
  · exact ⟨by decide, m22_3⟩
  · exact ⟨by decide, m22_4⟩
  · exact ⟨by decide, m22_5⟩

end Low53At2389PriceMass
