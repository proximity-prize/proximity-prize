/- Apache-2.0. Checked split inequalities in one physical excess at a time. -/
import ProximityPrize.SubmissionLower.Night6836TileStep
namespace Koala6836.Fast
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false
private theorem cell0 : (dataOK 11 54 && checks 11 54 && rounded 11 54)=true := by decide +kernel
private theorem cell1 : (dataOK 11 55 && checks 11 55 && rounded 11 55)=true := by decide +kernel
private theorem cell2 : (dataOK 11 56 && checks 11 56 && rounded 11 56)=true := by decide +kernel
private theorem cell3 : (dataOK 11 57 && checks 11 57 && rounded 11 57)=true := by decide +kernel
private theorem cell4 : (dataOK 11 58 && checks 11 58 && rounded 11 58)=true := by decide +kernel
private theorem cell5 : (dataOK 11 59 && checks 11 59 && rounded 11 59)=true := by decide +kernel
private theorem cell6 : (dataOK 11 60 && checks 11 60 && rounded 11 60)=true := by decide +kernel
private theorem cell7 : (dataOK 11 61 && checks 11 61 && rounded 11 61)=true := by decide +kernel
private theorem cell8 : (dataOK 11 62 && checks 11 62 && rounded 11 62)=true := by decide +kernel
theorem receiptR11B54 : block 11 54 9=true := by
  have h0 : block 11 54 0=true := rfl
  have h1 := appendCell 11 54 0 h0 cell0
  have h2 := appendCell 11 54 1 h1 cell1
  have h3 := appendCell 11 54 2 h2 cell2
  have h4 := appendCell 11 54 3 h3 cell3
  have h5 := appendCell 11 54 4 h4 cell4
  have h6 := appendCell 11 54 5 h5 cell5
  have h7 := appendCell 11 54 6 h6 cell6
  have h8 := appendCell 11 54 7 h7 cell7
  have h9 := appendCell 11 54 8 h8 cell8
  exact h9
end Koala6836.Fast
