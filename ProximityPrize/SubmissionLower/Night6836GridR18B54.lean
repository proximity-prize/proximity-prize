/- Apache-2.0. Checked split inequalities in one physical excess at a time. -/
import ProximityPrize.SubmissionLower.Night6836TileStep
namespace Koala6836.Fast
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false
private theorem cell0 : (dataOK 18 54 && checks 18 54 && rounded 18 54)=true := by decide +kernel
private theorem cell1 : (dataOK 18 55 && checks 18 55 && rounded 18 55)=true := by decide +kernel
private theorem cell2 : (dataOK 18 56 && checks 18 56 && rounded 18 56)=true := by decide +kernel
private theorem cell3 : (dataOK 18 57 && checks 18 57 && rounded 18 57)=true := by decide +kernel
private theorem cell4 : (dataOK 18 58 && checks 18 58 && rounded 18 58)=true := by decide +kernel
theorem receiptR18B54 : block 18 54 5=true := by
  have h0 : block 18 54 0=true := rfl
  have h1 := appendCell 18 54 0 h0 cell0
  have h2 := appendCell 18 54 1 h1 cell1
  have h3 := appendCell 18 54 2 h2 cell2
  have h4 := appendCell 18 54 3 h3 cell3
  have h5 := appendCell 18 54 4 h4 cell4
  exact h5
end Koala6836.Fast
