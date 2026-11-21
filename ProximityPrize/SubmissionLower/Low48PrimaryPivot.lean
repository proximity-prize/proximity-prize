import ProximityPrize.SubmissionLower.Low48PrimaryPivotFinish
import ProximityPrize.SubmissionLower.Low48PrimaryPivotRaw
import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee2
import ProximityPrize.SubmissionLower.Low48PrimaryPivotFee3

set_option Elab.async false

namespace Low48PrimaryPivot
open K1_13 (Geom)
open K1_13_2 K1_13_2_3

theorem origin_rank : Module.finrank Geom (LinearMap.range (nodeMap 0 0)) ≤ 343964087710797 := by
  apply origin_rank_of_receipts
  · rw [rawWindow_w2, rawWindow_w3]
  · have h2 := debit_le_fee w2 (by decide)
    have h3 := debit_le_fee w3 (by decide)
    rw [fee_eq_compute, feeCompute_affine, affineFeeWindow2] at h2
    rw [fee_eq_compute, feeCompute_affine, affineFeeWindow3] at h3
    omega

#print axioms origin_rank
end Low48PrimaryPivot
