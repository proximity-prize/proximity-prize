import ProximityPrize.SubmissionLower.R6966ProofFarTerminalChecks0

set_option Elab.async false

namespace Lower6960.FarTerminalReceipts
open FarTerminalArithmetic
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 0

theorem receipt17 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 17 (witness 17) := by
  apply checks_of_runs _ _ _ _ _ _ 1425 51 188899126660985270228068164480 188900218131665553034323863040 188899065236255928786455731200 188899110571939644320971027200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt18 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 18 (witness 18) := by
  apply checks_of_runs _ _ _ _ _ _ 1426 51 189518414975080604791405931520 189519509889684603275738434560 189518301852994313673451084800 189518347188678029207966380800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt19 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 19 (witness 19) := by
  apply checks_of_runs _ _ _ _ _ _ 1428 51 191611294297429304809014048000 191612400766926136891893970560 191611246589989666561402444800 191611291925673382095917740800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt20 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 20 (witness 20) := by
  apply checks_of_runs _ _ _ _ _ _ 1429 51 191933766627102546879654950400 191934874856600125143598080000 191933766180978266102716800000 191933811516661981637232096000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt21 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 21 (witness 21) := by
  apply checks_of_runs _ _ _ _ _ _ 1430 51 192464075817939744299252913120 192465187020766103424490006560 192463966152090689742251596800 192464011487774405276766892800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt22 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 22 (witness 22) := by
  apply checks_of_runs _ _ _ _ _ _ 1432 51 194413256288069754779764300800 194414378273459307284936196960 194413149841064056409237068800 194413195176747771943752364800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt23 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 23 (witness 23) := by
  apply checks_of_runs _ _ _ _ _ _ 1434 51 196301310976855441750386708000 196302443414560388961515460000 196301185471739870075836800000 196301230807423585610352096000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt24 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 24 (witness 24) := by
  apply checks_of_runs _ _ _ _ _ _ 1435 51 196238520131432706525594677760 196239652175902224686974479360 196238488174836376580335180800 196238533510520092114850476800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

end Lower6960.FarTerminalReceipts
