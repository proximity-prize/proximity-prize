/- Apache-2.0. Checked split inequalities in one physical excess at a time. -/
import ProximityPrize.SubmissionLower.Night6836TileStep
namespace Koala6836.Fast
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false
private theorem cell0 : (dataOK 17 54 && checks 17 54 && rounded 17 54)=true := by decide +kernel
private theorem cell1 : (dataOK 17 55 && checks 17 55 && rounded 17 55)=true := by decide +kernel
private theorem cell2 : (dataOK 17 56 && checks 17 56 && rounded 17 56)=true := by decide +kernel
private theorem cell3 : (dataOK 17 57 && checks 17 57 && rounded 17 57)=true := by decide +kernel
private theorem cell4 : (dataOK 17 58 && checks 17 58 && rounded 17 58)=true := by decide +kernel
private theorem cell5 : (dataOK 17 59 && checks 17 59 && rounded 17 59)=true := by decide +kernel
theorem receiptR17B54 : block 17 54 6=true := by
  have h0 : block 17 54 0=true := rfl
  have h1 := appendCell 17 54 0 h0 cell0
  have h2 := appendCell 17 54 1 h1 cell1
  have h3 := appendCell 17 54 2 h2 cell2
  have h4 := appendCell 17 54 3 h3 cell3
  have h5 := appendCell 17 54 4 h4 cell4
  have h6 := appendCell 17 54 5 h5 cell5
  exact h6
end Koala6836.Fast
