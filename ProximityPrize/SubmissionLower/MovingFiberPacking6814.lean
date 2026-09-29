import ProximityPrize.SubmissionLower.MovingFiberPackingSound6814S0
import ProximityPrize.SubmissionLower.MovingFiberPackingSound6814S1
import ProximityPrize.SubmissionLower.MovingFiberPackingSound6814S2
import ProximityPrize.SubmissionLower.MovingFiberPackingSound6814S3
import ProximityPrize.SubmissionLower.MovingFiberPackingSound6814S4
import ProximityPrize.SubmissionLower.MovingFiberPackingSound6814S5
import ProximityPrize.SubmissionLower.MovingFiberPackingSound6814S6
import ProximityPrize.SubmissionLower.MovingFiberPackingSound6814S7
import ProximityPrize.SubmissionLower.MovingFiberReceiptTypes6814

namespace ProximityPrize.SubmissionLower.MovingFiberPacking6814
open MovingFiberReceiptTypes6814
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
theorem sheet_bellman (j : Fin 8) : AffineFactorAggregate6808.BellmanRows 37 175
    (sheetOwn j.val) (sheetPacked j.val) := by
  fin_cases j
  · simpa only [sheetOwn,sheetPacked] using MovingFiberPackingSound6814.S0.bellman
  · simpa only [sheetOwn,sheetPacked] using MovingFiberPackingSound6814.S1.bellman
  · simpa only [sheetOwn,sheetPacked] using MovingFiberPackingSound6814.S2.bellman
  · simpa only [sheetOwn,sheetPacked] using MovingFiberPackingSound6814.S3.bellman
  · simpa only [sheetOwn,sheetPacked] using MovingFiberPackingSound6814.S4.bellman
  · simpa only [sheetOwn,sheetPacked] using MovingFiberPackingSound6814.S5.bellman
  · simpa only [sheetOwn,sheetPacked] using MovingFiberPackingSound6814.S6.bellman
  · simpa only [sheetOwn,sheetPacked] using MovingFiberPackingSound6814.S7.bellman

#print axioms sheet_bellman
end ProximityPrize.SubmissionLower.MovingFiberPacking6814
