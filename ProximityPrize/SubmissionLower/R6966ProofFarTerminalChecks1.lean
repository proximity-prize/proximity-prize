import ProximityPrize.SubmissionLower.R6966ProofFarTerminalChecks0

set_option Elab.async false

namespace Lower6960.FarTerminalReceipts
open FarTerminalArithmetic
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 0

theorem receipt9 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 9 (witness 9) := by
  apply checks_of_runs _ _ _ _ _ _ 1418 51 183530981820998035284010776000 183532043582479166203453140000 183530978159658809396976000000 183531023495342524931491296000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt10 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 10 (witness 10) := by
  apply checks_of_runs _ _ _ _ _ _ 1418 51 183887984883423336136308172800 183889048650836728678357616640 183887898599264574398631091200 183887943934948289933146387200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt11 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 11 (witness 11) := by
  apply checks_of_runs _ _ _ _ _ _ 1419 51 184676798315579779767989203200 184677866431433771911279632000 184676749906431339876735360000 184676795242115055411250656000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt12 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 12 (witness 12) := by
  apply checks_of_runs _ _ _ _ _ _ 1420 51 185441176198281703469479822080 185442248530922765386081472640 185441155963577116568161459200 185441201299260832102676755200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt13 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 13 (witness 13) := by
  apply checks_of_runs _ _ _ _ _ _ 1421 51 186181194999851087535747141120 186182271418471864274463989760 186181192176240920161887820800 186181237511924635696403116800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt14 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 14 (witness 14) := by
  apply checks_of_runs _ _ _ _ _ _ 1422 51 187115878169038543056984540000 187116959809314099856945332000 187115748175138859025586560000 187115793510822574560101856000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt15 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 15 (witness 15) := by
  apply checks_of_runs _ _ _ _ _ _ 1423 51 187588449505181608803007862400 187589533706623483945358682240 187588445053621415304596659200 187588490389305130839111955200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt16 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 16 (witness 16) := by
  apply checks_of_runs _ _ _ _ _ _ 1424 51 188255826416524744159124544000 188256914316398842898976720000 188255800892758882723977600000 188255846228442598258492896000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

end Lower6960.FarTerminalReceipts
