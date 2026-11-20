/- Apache-2.0. Checked split inequalities in one physical excess at a time. -/
import ProximityPrize.SubmissionLower.Night6836TileStep
namespace Koala6836.Fast
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false
private theorem cell0 : (dataOK 10 54 && checks 10 54 && rounded 10 54)=true := by decide +kernel
private theorem cell1 : (dataOK 10 55 && checks 10 55 && rounded 10 55)=true := by decide +kernel
private theorem cell2 : (dataOK 10 56 && checks 10 56 && rounded 10 56)=true := by decide +kernel
private theorem cell3 : (dataOK 10 57 && checks 10 57 && rounded 10 57)=true := by decide +kernel
private theorem cell4 : (dataOK 10 58 && checks 10 58 && rounded 10 58)=true := by decide +kernel
private theorem cell5 : (dataOK 10 59 && checks 10 59 && rounded 10 59)=true := by decide +kernel
private theorem cell6 : (dataOK 10 60 && checks 10 60 && rounded 10 60)=true := by decide +kernel
private theorem cell7 : (dataOK 10 61 && checks 10 61 && rounded 10 61)=true := by decide +kernel
private theorem cell8 : (dataOK 10 62 && checks 10 62 && rounded 10 62)=true := by decide +kernel
theorem receiptR10B54 : block 10 54 9=true := by
  have h0 : block 10 54 0=true := rfl
  have h1 := appendCell 10 54 0 h0 cell0
  have h2 := appendCell 10 54 1 h1 cell1
  have h3 := appendCell 10 54 2 h2 cell2
  have h4 := appendCell 10 54 3 h3 cell3
  have h5 := appendCell 10 54 4 h4 cell4
  have h6 := appendCell 10 54 5 h5 cell5
  have h7 := appendCell 10 54 6 h6 cell6
  have h8 := appendCell 10 54 7 h7 cell7
  have h9 := appendCell 10 54 8 h8 cell8
  exact h9
end Koala6836.Fast
