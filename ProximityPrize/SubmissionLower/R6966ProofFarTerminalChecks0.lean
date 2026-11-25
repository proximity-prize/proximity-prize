import ProximityPrize.SubmissionLower.R6966ProofFarTerminalArithmetic
import ProximityPrize.SubmissionLower.R6960TerminalReceipts

set_option Elab.async false

-- merged module R6966ProofFarTerminalData
section Merged_R6966ProofFarTerminalData

namespace Lower6960.FarTerminalReceipts
open FarTerminalArithmetic
abbrev terminalBank := TerminalReceipts.terminalBank
theorem bank_checked : P3_7_1.BankOK terminalBank := TerminalReceipts.bank_checked
def witness : ℕ → RectArgs
  | 1 => ⟨![680470, 68308], ![0, 823]⟩
  | 2 => ⟨![680802, 67976], ![0, 819]⟩
  | 3 => ⟨![680319, 68459], ![0, 815]⟩
  | 4 => ⟨![679844, 68934], ![0, 811]⟩
  | 5 => ⟨![680269, 68509], ![0, 806]⟩
  | 6 => ⟨![679807, 68971], ![0, 802]⟩
  | 7 => ⟨![679440, 69338], ![0, 797]⟩
  | 8 => ⟨![678995, 69783], ![0, 793]⟩
  | 9 => ⟨![679154, 69624], ![0, 788]⟩
  | 10 => ⟨![679003, 69775], ![0, 784]⟩
  | 11 => ⟨![678669, 70109], ![0, 779]⟩
  | 12 => ⟨![678345, 70433], ![0, 774]⟩
  | 13 => ⟨![678031, 70747], ![0, 769]⟩
  | 14 => ⟨![677634, 71144], ![0, 765]⟩
  | 15 => ⟨![677433, 71345], ![0, 759]⟩
  | 16 => ⟨![677149, 71629], ![0, 754]⟩
  | 17 => ⟨![676875, 71903], ![0, 749]⟩
  | 18 => ⟨![676611, 72167], ![0, 744]⟩
  | 19 => ⟨![675717, 73061], ![0, 738]⟩
  | 20 => ⟨![675579, 73199], ![0, 732]⟩
  | 21 => ⟨![675352, 73426], ![0, 727]⟩
  | 22 => ⟨![674516, 74262], ![0, 721]⟩
  | 23 => ⟨![673704, 75074], ![0, 715]⟩
  | 24 => ⟨![673731, 75047], ![0, 708]⟩
  | 25 => ⟨![672963, 75815], ![0, 702]⟩
  | 26 => ⟨![672329, 76449], ![0, 695]⟩
  | 27 => ⟨![671035, 77743], ![0, 688]⟩
  | 28 => ⟨![670579, 78199], ![0, 680]⟩
  | 29 => ⟨![669365, 79413], ![0, 673]⟩
  | 30 => ⟨![667771, 81007], ![0, 664]⟩
  | 31 => ⟨![666123, 82655], ![0, 656]⟩
  | 32 => ⟨![664153, 84625], ![0, 646]⟩
  | 33 => ⟨![661149, 87629], ![0, 635]⟩
  | 34 => ⟨![654235, 94543], ![0, 622]⟩
  | 35 => ⟨![573951, 174827], ![0, 592]⟩
  | 36 => ⟨![494516, 254262], ![0, 508]⟩
  | 37 => ⟨![443316, 305462], ![0, 383]⟩
  | 38 => ⟨![407052, 341726], ![0, 227]⟩
  | 39 => ⟨![379860, 368918], ![0, 46]⟩
  | 40 => ⟨![374389, 374389], ![0, 0]⟩
  | _ => ⟨![0,0],![0,0]⟩

end Lower6960.FarTerminalReceipts

end Merged_R6966ProofFarTerminalData

-- merged module R6966ProofFarTerminalChecks0
section Merged_R6966ProofFarTerminalChecks0

namespace Lower6960.FarTerminalReceipts
open FarTerminalArithmetic
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 0

theorem receipt1 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 1 (witness 1) := by
  apply checks_of_runs _ _ _ _ _ _ 1412 50 180412899927299063958263774400 180413944470901341724549497120 180412845330367654282235059200 180412890666051369816750355200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt2 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 2 (witness 2) := by
  apply checks_of_runs _ _ _ _ _ _ 1412 50 179624148923764908830073297600 179625189101261548620983323680 179624081639472251272373836800 179624126975155966806889132800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt3 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 3 (witness 3) := by
  apply checks_of_runs _ _ _ _ _ _ 1413 50 180771399896070524688668160000 180772446433691845348503552000 180771307363295542910540160000 180771352698979258445055456000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt4 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 4 (witness 4) := by
  apply checks_of_runs _ _ _ _ _ _ 1414 51 181897887856203700931941624800 181898940640263443590499892000 181897766331853970271000960000 181897811667537685805516256000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt5 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 5 (witness 5) := by
  apply checks_of_runs _ _ _ _ _ _ 1414 51 180889994258730211235016412800 180891041421152928878309232000 180889964417887077565618560000 180890009753570793100133856000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt6 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 6 (witness 6) := by
  apply checks_of_runs _ _ _ _ _ _ 1415 51 181985515137681012345411256320 181986568382065970835996917760 181985438075161575518578252800 181985483410845291053093548800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt7 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 7 (witness 7) := by
  apply checks_of_runs _ _ _ _ _ _ 1416 51 182854474811844173935609178880 182855532834706608620254355040 182854471873877331127405747200 182854517209561046661921043200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt8 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 8 (witness 8) := by
  apply checks_of_runs _ _ _ _ _ _ 1417 51 183906866762123034008115561600 183907930632983651567640061440 183906803357486441904573619200 183906848693170157439088915200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

end Lower6960.FarTerminalReceipts

end Merged_R6966ProofFarTerminalChecks0
