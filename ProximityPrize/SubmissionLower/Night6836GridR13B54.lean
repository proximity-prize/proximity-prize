/- Apache-2.0. Checked split inequalities in one physical excess at a time. -/
import ProximityPrize.SubmissionLower.Night6836TileStep
namespace Koala6836.Fast
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false
private theorem cell0 : (dataOK 13 54 && checks 13 54 && rounded 13 54)=true := by decide +kernel
private theorem cell1 : (dataOK 13 55 && checks 13 55 && rounded 13 55)=true := by decide +kernel
private theorem cell2 : (dataOK 13 56 && checks 13 56 && rounded 13 56)=true := by decide +kernel
private theorem cell3 : (dataOK 13 57 && checks 13 57 && rounded 13 57)=true := by decide +kernel
private theorem cell4 : (dataOK 13 58 && checks 13 58 && rounded 13 58)=true := by decide +kernel
private theorem cell5 : (dataOK 13 59 && checks 13 59 && rounded 13 59)=true := by decide +kernel
private theorem cell6 : (dataOK 13 60 && checks 13 60 && rounded 13 60)=true := by decide +kernel
private theorem cell7 : (dataOK 13 61 && checks 13 61 && rounded 13 61)=true := by decide +kernel
private theorem cell8 : (dataOK 13 62 && checks 13 62 && rounded 13 62)=true := by decide +kernel
theorem receiptR13B54 : block 13 54 9=true := by
  have h0 : block 13 54 0=true := rfl
  have h1 := appendCell 13 54 0 h0 cell0
  have h2 := appendCell 13 54 1 h1 cell1
  have h3 := appendCell 13 54 2 h2 cell2
  have h4 := appendCell 13 54 3 h3 cell3
  have h5 := appendCell 13 54 4 h4 cell4
  have h6 := appendCell 13 54 5 h5 cell5
  have h7 := appendCell 13 54 6 h6 cell6
  have h8 := appendCell 13 54 7 h7 cell7
  have h9 := appendCell 13 54 8 h8 cell8
  exact h9
end Koala6836.Fast
