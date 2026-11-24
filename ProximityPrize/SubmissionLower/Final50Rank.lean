import ProximityPrize.SubmissionLower.Final50RankBlocks
import ProximityPrize.SubmissionLower.Final50RankReceipt

set_option Elab.async false

namespace Final50Rank
open K1_13 (Geom InBox Row shape extend atJet)
open K1 (I K node)
open Final50AnchorSpace (cap anchorLocal)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators Polynomial

theorem origin_rank : Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) ≤ 16564024 := by
  apply Final50RankBlocks.origin_le_blocks.trans
  calc
    _ ≤ ∑ s : Fin 133, Final50RankCore.gradeFee s (Final50RankReceipt.rows (cap s)) := by
      apply Finset.sum_le_sum
      intro s _
      let d : Fin 56 := ⟨cap s,Nat.lt_succ_of_le (Final50AnchorSpace.cap_le_index s)⟩
      exact Final50RankCore.grade_bound s d (Final50RankReceipt.rows d)
        (Final50RankReceipt.rows_good d) (Final50RankReceipt.rows_sorted d) (Final50RankReceipt.rows_cover d)
    _ = _ := Final50RankReceipt.total_fees

#print axioms origin_rank
end Final50Rank
