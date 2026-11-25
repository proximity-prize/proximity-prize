import ProximityPrize.SubmissionLower.R6966ProofFarTerminalChecks0

set_option Elab.async false

namespace Lower6960.FarTerminalReceipts
open FarTerminalArithmetic
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 0

theorem receipt33 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 33 (witness 33) := by
  apply checks_of_runs _ _ _ _ _ _ 1467 53 224842734146003429600620560000 224844024374716655428107840000 224842692547515233806473600000 224842737883198949340988896000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt34 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 34 (witness 34) := by
  apply checks_of_runs _ _ _ _ _ _ 1481 53 240038284306440410344459445760 240039658548686236057490914560 240038281334781965639453875200 240038326670465681173969171200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt35 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 35 (witness 35) := by
  apply checks_of_runs _ _ _ _ _ _ 1509 54 389331936946422291243409735680 389334136706231438341837946880 389331907732458345966282316800 389331953068142061500797612800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt36 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 36 (witness 36) := by
  apply checks_of_runs _ _ _ _ _ _ 1504 54 487834323211238725388074629600 487837067574013909266066384960 487834255336428463279253068800 487834300672112178813768364800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt37 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 37 (witness 37) := by
  apply checks_of_runs _ _ _ _ _ _ 1499 54 525380217392425391837573513760 525383169253821106902065246400 525380181323120319420114508800 525380226658804034954629804800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt38 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 38 (witness 38) := by
  apply checks_of_runs _ _ _ _ _ _ 1495 54 539670235573122208279459810560 539673266340944005098115509120 539670228235096130845877836800 539670273570779846380393132800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt39 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 39 (witness 39) := by
  apply checks_of_runs _ _ _ _ _ _ 1491 54 543692443285428821961190181280 543695496218797354329064141440 543692398971547875548957875200 543692444307231591083473171200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt40 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 40 (witness 40) := by
  apply checks_of_runs _ _ _ _ _ _ 1487 53 543818846193582690602927136000 543821904000531397408348656000 543808501163128991753066880000 543808546498812707287582176000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

end Lower6960.FarTerminalReceipts
