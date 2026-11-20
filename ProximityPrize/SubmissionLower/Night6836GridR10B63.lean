/- Apache-2.0. Checked split inequalities in one physical excess at a time. -/
import ProximityPrize.SubmissionLower.Night6836TileStep
namespace Koala6836.Fast
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false
private theorem cell0 : (dataOK 10 63 && checks 10 63 && rounded 10 63)=true := by decide +kernel
private theorem cell1 : (dataOK 10 64 && checks 10 64 && rounded 10 64)=true := by decide +kernel
private theorem cell2 : (dataOK 10 65 && checks 10 65 && rounded 10 65)=true := by decide +kernel
private theorem cell3 : (dataOK 10 66 && checks 10 66 && rounded 10 66)=true := by decide +kernel
theorem receiptR10B63 : block 10 63 4=true := by
  have h0 : block 10 63 0=true := rfl
  have h1 := appendCell 10 63 0 h0 cell0
  have h2 := appendCell 10 63 1 h1 cell1
  have h3 := appendCell 10 63 2 h2 cell2
  have h4 := appendCell 10 63 3 h3 cell3
  exact h4
end Koala6836.Fast
