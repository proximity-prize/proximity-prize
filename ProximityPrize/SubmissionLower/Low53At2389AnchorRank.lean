import ProximityPrize.SubmissionLower.Low53At2389AnchorRankBlocks
import ProximityPrize.SubmissionLower.Low53At2389AnchorRankReceipt

namespace Low53At2389AnchorRank
open K1_13 (Geom InBox Row shape extend atJet)
open K1 (I K node)
open Low53At2389AnchorSpace (cap anchorLocal)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators Polynomial

theorem origin_rank : Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) ≤ 14010071 := by
  apply Low53At2389AnchorRankBlocks.origin_le_blocks.trans
  calc
    _ ≤ ∑ s : Fin 130, Low53At2389AnchorRankCore.gradeFee s (Low53At2389AnchorRankReceipt.rows (cap s)) := by
      apply Finset.sum_le_sum
      intro s _
      let d : Fin 54 := ⟨cap s,Nat.lt_succ_of_le (Low53At2389AnchorSpace.cap_le_index s)⟩
      exact Low53At2389AnchorRankCore.grade_bound s d (Low53At2389AnchorRankReceipt.rows d)
        (Low53At2389AnchorRankReceipt.rows_good d) (Low53At2389AnchorRankReceipt.rows_sorted d) (Low53At2389AnchorRankReceipt.rows_cover d)
    _ = _ := Low53At2389AnchorRankReceipt.total_fees

#print axioms origin_rank
end Low53At2389AnchorRank
