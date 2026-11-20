import ProximityPrize.SubmissionLower.AnchorReceipts
import ProximityPrize.SubmissionLower.Fast070

namespace SoundnessAnchor
open K1_13 K1_13_1_1
open private rank_block_le_budget totalBudget_eq_sum from ProximityPrize.SubmissionLower.Fast070

/-- The local map has at least 1,057 fewer independent conditions than the published bound. -/
theorem rank_local (x y : Geom) :
    Module.finrank Geom (LinearMap.range (K1_13_1.anchorLocal x y)) ≤ 9198569 := by
  let ranks (s : Fin 121) (r : Fin 138) :=
    Module.finrank Geom (LinearMap.range (blockMap s (offset r)))
  have h : ∑ s : Fin 121, ∑ r : Fin 138, (ranks s r + improvement s r) ≤
      ∑ s : Fin 121, ∑ r : Fin 138, blockBudget s (offset r) := by
    apply Finset.sum_le_sum
    intro s _
    apply Finset.sum_le_sum
    intro r _
    exact rank_plus_gain s r (rank_block_le_budget K1_13_1_1_1.proof K1_13_1_1_2.proof
      K1_13_1_1_3.proof s (offset r) (Nat.le_of_lt_succ s.isLt) (by unfold offset; omega))
  simp only [Finset.sum_add_distrib] at h
  rw [gain_total, ← totalBudget_eq_sum, totalBudget_eq] at h
  have hlocal : Module.finrank Geom (LinearMap.range (K1_13_1.anchorLocal x y)) ≤
      ∑ s : Fin 121, ∑ r : Fin 138, ranks s r :=
    (rank_local_le_origin x y).trans rank_origin_le_blocks
  omega

/-- The order-90 anchor column count at 180,130 agreements and physical degree 133,542
    strictly exceeds the tightened global rank bound. -/
theorem anchor_room :
    262144 * 9198569 < 90 * 180130 * 356770 - 133542 * 25254303 + 12338027 := by decide

end SoundnessAnchor
