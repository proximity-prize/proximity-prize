/- Apache-2.0. Checked split inequalities in one physical excess at a time. -/
import ProximityPrize.SubmissionLower.Night6836TileStep
namespace Koala6836.Fast
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false
private theorem cell0 : (dataOK 12 54 && checks 12 54 && rounded 12 54)=true := by decide +kernel
private theorem cell1 : (dataOK 12 55 && checks 12 55 && rounded 12 55)=true := by decide +kernel
private theorem cell2 : (dataOK 12 56 && checks 12 56 && rounded 12 56)=true := by decide +kernel
private theorem cell3 : (dataOK 12 57 && checks 12 57 && rounded 12 57)=true := by decide +kernel
private theorem cell4 : (dataOK 12 58 && checks 12 58 && rounded 12 58)=true := by decide +kernel
private theorem cell5 : (dataOK 12 59 && checks 12 59 && rounded 12 59)=true := by decide +kernel
private theorem cell6 : (dataOK 12 60 && checks 12 60 && rounded 12 60)=true := by decide +kernel
private theorem cell7 : (dataOK 12 61 && checks 12 61 && rounded 12 61)=true := by decide +kernel
private theorem cell8 : (dataOK 12 62 && checks 12 62 && rounded 12 62)=true := by decide +kernel
theorem receiptR12B54 : block 12 54 9=true := by
  have h0 : block 12 54 0=true := rfl
  have h1 := appendCell 12 54 0 h0 cell0
  have h2 := appendCell 12 54 1 h1 cell1
  have h3 := appendCell 12 54 2 h2 cell2
  have h4 := appendCell 12 54 3 h3 cell3
  have h5 := appendCell 12 54 4 h4 cell4
  have h6 := appendCell 12 54 5 h5 cell5
  have h7 := appendCell 12 54 6 h6 cell6
  have h8 := appendCell 12 54 7 h7 cell7
  have h9 := appendCell 12 54 8 h8 cell8
  exact h9
end Koala6836.Fast
