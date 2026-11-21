import ProximityPrize.SubmissionLower.Low48BlockGeometry
import ProximityPrize.SubmissionLower.Low48Receipt

namespace Low48Rank
open K1_13 (Geom InBox Row shape extend atJet)
open K1 (I K node)
open Low48AnchorSpace (cap anchorLocal)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators Polynomial

theorem origin_rank : Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) ≤ 10803644 := by
  apply Low48BlockGeometry.origin_le_blocks.trans
  calc
    _ ≤ ∑ s : Fin 123, Low48RankCore.gradeFee s (Low48Receipt.rows (cap s)) := by
      apply Finset.sum_le_sum
      intro s _
      let d : Fin 51 := ⟨cap s,Nat.lt_succ_of_le (Low48AnchorSpace.cap_le_index s)⟩
      exact Low48RankCore.grade_bound s d (Low48Receipt.rows d)
        (Low48Receipt.rows_good d) (Low48Receipt.rows_sorted d) (Low48Receipt.rows_cover d)
    _ = _ := Low48Receipt.total_fees

#print axioms origin_rank
end Low48Rank
