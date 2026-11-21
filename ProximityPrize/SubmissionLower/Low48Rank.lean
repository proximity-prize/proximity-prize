import ProximityPrize.SubmissionLower.Low48BlockGeometry
import ProximityPrize.SubmissionLower.Low48Anchor
import ProximityPrize.SubmissionLower.Low48Receipt

namespace Low48Rank
open K1_13 (Geom InBox Row shape extend atJet)
open K1 (I K node)
open Low48AnchorSpace (cap anchorLocal)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators Polynomial

theorem origin_rank : Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) ≤ 10053422 := by
  apply Low48BlockGeometry.origin_le_blocks.trans
  calc
    _ ≤ ∑ s : Fin 122, Low48RankCore.gradeFee s (Low48Receipt.rows (cap s)) := by
      apply Finset.sum_le_sum
      intro s _
      let d : Fin 50 := ⟨cap s,Nat.lt_succ_of_le (Low48AnchorSpace.cap_le_index s)⟩
      exact Low48RankCore.grade_bound s d (Low48Receipt.rows d)
        (Low48Receipt.rows_good d) (Low48Receipt.rows_sorted d) (Low48Receipt.rows_cover d)
    _ = _ := Low48Receipt.total_fees

theorem exists_anchor (w : I → K) :
    ∃ P : Row 4, P ≠ 0 ∧ InBox (shape P) ⟨121,49,13⟩ ∧
      differentialWeightedDegree 133412 ((MvPolynomial.optionEquivRight Geom (Fin 4)).symm P) <
        90 * 179925 ∧
      ∀ (S : K[X]) (T : Finset I), S.natDegree ≤ 133412 → 179925 ≤ T.card →
        (∀ i ∈ T, S.eval (node i) = w i) → atJet P (extend S) = 0 :=
  Low48Anchor.exists_anchor origin_rank w

#print axioms origin_rank
#print axioms exists_anchor
end Low48Rank
