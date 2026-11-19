/- Apache-2.0. Checked split inequalities in one physical excess at a time. -/
import ProximityPrize.SubmissionLower.Night6836TileStep
namespace Koala6836.Fast
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false
private theorem cell0 : (dataOK 16 54 && checks 16 54 && rounded 16 54)=true := by decide +kernel
private theorem cell1 : (dataOK 16 55 && checks 16 55 && rounded 16 55)=true := by decide +kernel
private theorem cell2 : (dataOK 16 56 && checks 16 56 && rounded 16 56)=true := by decide +kernel
private theorem cell3 : (dataOK 16 57 && checks 16 57 && rounded 16 57)=true := by decide +kernel
private theorem cell4 : (dataOK 16 58 && checks 16 58 && rounded 16 58)=true := by decide +kernel
private theorem cell5 : (dataOK 16 59 && checks 16 59 && rounded 16 59)=true := by decide +kernel
private theorem cell6 : (dataOK 16 60 && checks 16 60 && rounded 16 60)=true := by decide +kernel
theorem receiptR16B54 : block 16 54 7=true := by
  have h0 : block 16 54 0=true := rfl
  have h1 := appendCell 16 54 0 h0 cell0
  have h2 := appendCell 16 54 1 h1 cell1
  have h3 := appendCell 16 54 2 h2 cell2
  have h4 := appendCell 16 54 3 h3 cell3
  have h5 := appendCell 16 54 4 h4 cell4
  have h6 := appendCell 16 54 5 h5 cell5
  have h7 := appendCell 16 54 6 h6 cell6
  exact h7
end Koala6836.Fast
