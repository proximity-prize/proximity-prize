/- Apache-2.0. Checked split inequalities in one physical excess at a time. -/
import ProximityPrize.SubmissionLower.Night6836TileStep
namespace Koala6836.Fast
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false
private theorem cell0 : (dataOK 15 54 && checks 15 54 && rounded 15 54)=true := by decide +kernel
private theorem cell1 : (dataOK 15 55 && checks 15 55 && rounded 15 55)=true := by decide +kernel
private theorem cell2 : (dataOK 15 56 && checks 15 56 && rounded 15 56)=true := by decide +kernel
private theorem cell3 : (dataOK 15 57 && checks 15 57 && rounded 15 57)=true := by decide +kernel
private theorem cell4 : (dataOK 15 58 && checks 15 58 && rounded 15 58)=true := by decide +kernel
private theorem cell5 : (dataOK 15 59 && checks 15 59 && rounded 15 59)=true := by decide +kernel
private theorem cell6 : (dataOK 15 60 && checks 15 60 && rounded 15 60)=true := by decide +kernel
private theorem cell7 : (dataOK 15 61 && checks 15 61 && rounded 15 61)=true := by decide +kernel
theorem receiptR15B54 : block 15 54 8=true := by
  have h0 : block 15 54 0=true := rfl
  have h1 := appendCell 15 54 0 h0 cell0
  have h2 := appendCell 15 54 1 h1 cell1
  have h3 := appendCell 15 54 2 h2 cell2
  have h4 := appendCell 15 54 3 h3 cell3
  have h5 := appendCell 15 54 4 h4 cell4
  have h6 := appendCell 15 54 5 h5 cell5
  have h7 := appendCell 15 54 6 h6 cell6
  have h8 := appendCell 15 54 7 h7 cell7
  exact h8
end Koala6836.Fast
