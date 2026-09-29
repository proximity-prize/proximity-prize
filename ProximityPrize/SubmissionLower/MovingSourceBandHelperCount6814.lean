import ProximityPrize.SubmissionLower.MovingSourceBandWiden6814

/-! A single generous proper-helper envelope covers all five bands and
all four eligible Z sources, as well as the L=1700 avoidance source. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandHelperCount6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
open RCN135 RCN136 RCN156 RCN234 RCN319
open MovingSourceBandGeometry6814 MovingSourceBandLeading6814
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}

theorem helper_receipt : Gates 3578 57 13 341 1521 89277 ∧
    AsymmetricHelper.leftRegularCountCap (pair 3578 57 13 341 1521 89277)<270000000000000000 := by
  unfold Gates
  decide +kernel

theorem packet_helper_count (P : Packet x t y r) (Q : MvPolynomial (Fin 4) K)
    (hrel : IsRelPrime P.F Q)
    (hw : wt residualSWeights Q≤341 ∧ wt residualYSWeights Q≤1521 ∧ wt residualTotalWeights Q≤89277)
    (hzero : ∀ gamma∈P.seeds, specialization K (P.selected gamma) gamma Q=0) :
    P.seeds.card<270000000000000000 := by
  let PP := P.widen 3578 57 13 P.thigh P.yhigh P.rhigh
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact (proper_cut_count PP Q 341 1521 89277 hrel hw helper_receipt.1 hzero).trans_lt helper_receipt.2

#print axioms packet_helper_count
end
end ProximityPrize.SubmissionLower.MovingSourceBandHelperCount6814
