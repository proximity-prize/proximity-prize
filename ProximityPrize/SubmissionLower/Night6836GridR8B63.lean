/- Apache-2.0. Checked split inequalities in one physical excess at a time. -/
import ProximityPrize.SubmissionLower.Night6836TileStep
namespace Koala6836.Fast
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false
private theorem cell0 : (dataOK 8 63 && checks 8 63 && rounded 8 63)=true := by decide +kernel
private theorem cell1 : (dataOK 8 64 && checks 8 64 && rounded 8 64)=true := by decide +kernel
private theorem cell2 : (dataOK 8 65 && checks 8 65 && rounded 8 65)=true := by decide +kernel
private theorem cell3 : (dataOK 8 66 && checks 8 66 && rounded 8 66)=true := by decide +kernel
private theorem cell4 : (dataOK 8 67 && checks 8 67 && rounded 8 67)=true := by decide +kernel
private theorem cell5 : (dataOK 8 68 && checks 8 68 && rounded 8 68)=true := by decide +kernel
theorem receiptR8B63 : block 8 63 6=true := by
  have h0 : block 8 63 0=true := rfl
  have h1 := appendCell 8 63 0 h0 cell0
  have h2 := appendCell 8 63 1 h1 cell1
  have h3 := appendCell 8 63 2 h2 cell2
  have h4 := appendCell 8 63 3 h3 cell3
  have h5 := appendCell 8 63 4 h4 cell4
  have h6 := appendCell 8 63 5 h5 cell5
  exact h6
end Koala6836.Fast
