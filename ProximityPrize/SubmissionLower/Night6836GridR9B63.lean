/- Apache-2.0. Checked split inequalities in one physical excess at a time. -/
import ProximityPrize.SubmissionLower.Night6836TileStep
namespace Koala6836.Fast
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false
private theorem cell0 : (dataOK 9 63 && checks 9 63 && rounded 9 63)=true := by decide +kernel
private theorem cell1 : (dataOK 9 64 && checks 9 64 && rounded 9 64)=true := by decide +kernel
private theorem cell2 : (dataOK 9 65 && checks 9 65 && rounded 9 65)=true := by decide +kernel
private theorem cell3 : (dataOK 9 66 && checks 9 66 && rounded 9 66)=true := by decide +kernel
private theorem cell4 : (dataOK 9 67 && checks 9 67 && rounded 9 67)=true := by decide +kernel
theorem receiptR9B63 : block 9 63 5=true := by
  have h0 : block 9 63 0=true := rfl
  have h1 := appendCell 9 63 0 h0 cell0
  have h2 := appendCell 9 63 1 h1 cell1
  have h3 := appendCell 9 63 2 h2 cell2
  have h4 := appendCell 9 63 3 h3 cell3
  have h5 := appendCell 9 63 4 h4 cell4
  exact h5
end Koala6836.Fast
