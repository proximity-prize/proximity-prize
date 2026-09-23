import ProximityPrize.SubmissionLower.MovingFiberPackingSound6811S0
import ProximityPrize.SubmissionLower.MovingFiberPackingSound6811S1
import ProximityPrize.SubmissionLower.MovingFiberPackingSound6811S2
import ProximityPrize.SubmissionLower.MovingFiberPackingSound6811S3
import ProximityPrize.SubmissionLower.MovingFiberPackingSound6811S4
import ProximityPrize.SubmissionLower.MovingFiberPackingSound6811S5
import ProximityPrize.SubmissionLower.MovingFiberPackingSound6811S6
import ProximityPrize.SubmissionLower.MovingFiberPackingSound6811S7
import ProximityPrize.SubmissionLower.MovingFiberReceiptTypes6811

namespace ProximityPrize.SubmissionLower.MovingFiberPacking6811
open MovingFiberReceiptTypes6811
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
theorem sheet_bellman (j : Fin 8) : AffineFactorAggregate6808.BellmanRows 36 171
    (sheetOwn j.val) (sheetPacked j.val) := by
  fin_cases j
  · simpa only [sheetOwn,sheetPacked] using MovingFiberPackingSound6811.S0.bellman
  · simpa only [sheetOwn,sheetPacked] using MovingFiberPackingSound6811.S1.bellman
  · simpa only [sheetOwn,sheetPacked] using MovingFiberPackingSound6811.S2.bellman
  · simpa only [sheetOwn,sheetPacked] using MovingFiberPackingSound6811.S3.bellman
  · simpa only [sheetOwn,sheetPacked] using MovingFiberPackingSound6811.S4.bellman
  · simpa only [sheetOwn,sheetPacked] using MovingFiberPackingSound6811.S5.bellman
  · simpa only [sheetOwn,sheetPacked] using MovingFiberPackingSound6811.S6.bellman
  · simpa only [sheetOwn,sheetPacked] using MovingFiberPackingSound6811.S7.bellman

#print axioms sheet_bellman
end ProximityPrize.SubmissionLower.MovingFiberPacking6811
