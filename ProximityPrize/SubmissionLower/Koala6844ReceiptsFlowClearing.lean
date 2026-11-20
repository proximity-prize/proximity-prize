import ProximityPrize.SubmissionLower.Koala6844ReceiptsClearing
import ProximityPrize.SubmissionLower.Koala6844NormalizationPrelude

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

open Koala6844Moving

noncomputable section
set_option autoImplicit false

variable {K : Type*} [CommRing K]

theorem flow_iterate_clearedForm (B : FlowData K) (q n : ℕ) {P : P4 K}
    (hP : ClearedForm B.A B.numerator q P) :
    ClearedForm B.A B.numerator q ((B.flow : P4 K → P4 K)^[n] P) := by
  let g := (liftX B.d0)^2 * B.A * liftX B.a1
  have ha : B.flow B.A = B.A * g := by
    rw [FlowData.A, FlowData.flow_affine]
    unfold FlowData.denominator g
    rw [← FlowData.A]
    ring
  have hb : B.flow B.numerator = B.numerator * g := by
    simp only [FlowData.numerator, FlowData.C, map_add, RCN347.leibniz_product,
      FlowData.flow_liftX, FlowData.flow_Y, FlowData.flow_affine, zero_mul, zero_add]
    simp only [g, FlowData.yCoefficient, FlowData.denominator, FlowData.minor,
      FlowData.A, affine]
    ring
  exact ClearedForm.iterate B.flow B.A B.numerator g ha hb q n hP

end
end ProximityPrize.SubmissionLower.Koala6844Receipts
