/- Apache-2.0. Checked split inequalities in one physical excess at a time. -/
import ProximityPrize.SubmissionLower.Night6836TileStep
namespace Koala6836.Fast
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false
private theorem cell0 : (dataOK 13 63 && checks 13 63 && rounded 13 63)=true := by decide +kernel
theorem receiptR13B63 : block 13 63 1=true := by
  have h0 : block 13 63 0=true := rfl
  have h1 := appendCell 13 63 0 h0 cell0
  exact h1
end Koala6836.Fast
