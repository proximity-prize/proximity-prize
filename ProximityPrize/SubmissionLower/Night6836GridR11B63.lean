/- Apache-2.0. Checked split inequalities in one physical excess at a time. -/
import ProximityPrize.SubmissionLower.Night6836TileStep
namespace Koala6836.Fast
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false
private theorem cell0 : (dataOK 11 63 && checks 11 63 && rounded 11 63)=true := by decide +kernel
private theorem cell1 : (dataOK 11 64 && checks 11 64 && rounded 11 64)=true := by decide +kernel
private theorem cell2 : (dataOK 11 65 && checks 11 65 && rounded 11 65)=true := by decide +kernel
theorem receiptR11B63 : block 11 63 3=true := by
  have h0 : block 11 63 0=true := rfl
  have h1 := appendCell 11 63 0 h0 cell0
  have h2 := appendCell 11 63 1 h1 cell1
  have h3 := appendCell 11 63 2 h2 cell2
  exact h3
end Koala6836.Fast
