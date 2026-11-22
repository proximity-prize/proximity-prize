import ProximityPrize.SubmissionLower.Cutter53AnchorRankBlocks
import ProximityPrize.SubmissionLower.Cutter53AnchorRankReceipt

namespace Cutter53AnchorRank
open K1_13 (Geom InBox Row shape extend atJet)
open K1 (I K node)
open Cutter53AnchorSpace (cap anchorLocal)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators Polynomial

theorem origin_rank : Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) ≤ 14013601 := by
  apply Cutter53AnchorRankBlocks.origin_le_blocks.trans
  calc
    _ ≤ ∑ s : Fin 130, Cutter53AnchorRankCore.gradeFee s (Low51EdgeRankReceipt.rows (cap s)) := by
      apply Finset.sum_le_sum
      intro s _
      let d : Fin 54 := ⟨cap s,Nat.lt_succ_of_le (Cutter53AnchorSpace.cap_le_index s)⟩
      exact Cutter53AnchorRankCore.grade_bound s d (Low51EdgeRankReceipt.rows d)
        (Low51EdgeRankReceipt.rows_good d) (Low51EdgeRankReceipt.rows_sorted d) (Low51EdgeRankReceipt.rows_cover d)
    _ = _ := Cutter53AnchorRankReceipt.total_fees

end Cutter53AnchorRank
