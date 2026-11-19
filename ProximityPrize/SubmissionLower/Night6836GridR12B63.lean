/- Apache-2.0. Checked split inequalities in one physical excess at a time. -/
import ProximityPrize.SubmissionLower.Night6836TileStep
namespace Koala6836.Fast
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false
private theorem cell0 : (dataOK 12 63 && checks 12 63 && rounded 12 63)=true := by decide +kernel
private theorem cell1 : (dataOK 12 64 && checks 12 64 && rounded 12 64)=true := by decide +kernel
theorem receiptR12B63 : block 12 63 2=true := by
  have h0 : block 12 63 0=true := rfl
  have h1 := appendCell 12 63 0 h0 cell0
  have h2 := appendCell 12 63 1 h1 cell1
  exact h2
end Koala6836.Fast
