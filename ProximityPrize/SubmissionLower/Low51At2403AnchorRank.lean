import ProximityPrize.SubmissionLower.Low51At2403AnchorRankBlocks
import ProximityPrize.SubmissionLower.Low51At2403AnchorRankReceipt

namespace Low51At2403AnchorRank
open K1_13 (Geom InBox Row shape extend atJet)
open K1 (I K node)
open Low51At2403AnchorSpace (cap anchorLocal)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators Polynomial

theorem origin_rank : Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) ≤ 13654979 := by
  apply Low51At2403AnchorRankBlocks.origin_le_blocks.trans
  calc
    _ ≤ ∑ s : Fin 128, Low51At2403AnchorRankCore.gradeFee s (Low51EdgeRankReceipt.rows (cap s)) := by
      apply Finset.sum_le_sum
      intro s _
      let d : Fin 54 := ⟨cap s,Nat.lt_succ_of_le (Low51At2403AnchorSpace.cap_le_index s)⟩
      exact Low51At2403AnchorRankCore.grade_bound s d (Low51EdgeRankReceipt.rows d)
        (Low51EdgeRankReceipt.rows_good d) (Low51EdgeRankReceipt.rows_sorted d) (Low51EdgeRankReceipt.rows_cover d)
    _ = _ := Low51At2403AnchorRankReceipt.total_fees

#print axioms origin_rank
end Low51At2403AnchorRank
