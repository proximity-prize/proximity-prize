/- Apache-2.0. Checked split inequalities in one physical excess at a time. -/
import ProximityPrize.SubmissionLower.Night6836TileStep
namespace Koala6836.Fast
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false
private theorem cell0 : (dataOK 18 45 && checks 18 45 && rounded 18 45)=true := by decide +kernel
private theorem cell1 : (dataOK 18 46 && checks 18 46 && rounded 18 46)=true := by decide +kernel
private theorem cell2 : (dataOK 18 47 && checks 18 47 && rounded 18 47)=true := by decide +kernel
private theorem cell3 : (dataOK 18 48 && checks 18 48 && rounded 18 48)=true := by decide +kernel
private theorem cell4 : (dataOK 18 49 && checks 18 49 && rounded 18 49)=true := by decide +kernel
private theorem cell5 : (dataOK 18 50 && checks 18 50 && rounded 18 50)=true := by decide +kernel
private theorem cell6 : (dataOK 18 51 && checks 18 51 && rounded 18 51)=true := by decide +kernel
private theorem cell7 : (dataOK 18 52 && checks 18 52 && rounded 18 52)=true := by decide +kernel
private theorem cell8 : (dataOK 18 53 && checks 18 53 && rounded 18 53)=true := by decide +kernel
theorem receiptR18B45 : block 18 45 9=true := by
  have h0 : block 18 45 0=true := rfl
  have h1 := appendCell 18 45 0 h0 cell0
  have h2 := appendCell 18 45 1 h1 cell1
  have h3 := appendCell 18 45 2 h2 cell2
  have h4 := appendCell 18 45 3 h3 cell3
  have h5 := appendCell 18 45 4 h4 cell4
  have h6 := appendCell 18 45 5 h5 cell5
  have h7 := appendCell 18 45 6 h6 cell6
  have h8 := appendCell 18 45 7 h7 cell7
  have h9 := appendCell 18 45 8 h8 cell8
  exact h9
end Koala6836.Fast
