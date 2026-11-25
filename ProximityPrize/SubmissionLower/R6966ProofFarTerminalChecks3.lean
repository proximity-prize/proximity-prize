import ProximityPrize.SubmissionLower.R6966ProofFarTerminalChecks0

set_option Elab.async false

namespace Lower6960.FarTerminalReceipts
open FarTerminalArithmetic
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 0

theorem receipt25 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 25 (witness 25) := by
  apply checks_of_runs _ _ _ _ _ _ 1437 51 198019782579747292934860696320 198020924508486417675826544640 198019670526089895246138547200 198019715861773610780653843200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt26 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 26 (witness 26) := by
  apply checks_of_runs _ _ _ _ _ _ 1439 51 199486709589604012323002424000 199487859617909473277258160000 199486625847594863188924800000 199486671183278578723440096000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt27 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 27 (witness 27) := by
  apply checks_of_runs _ _ _ _ _ _ 1442 52 202471115510858051306650429440 202472282053908505725907138560 202471018373346410839510195200 202471063709030126374025491200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt28 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 28 (witness 28) := by
  apply checks_of_runs _ _ _ _ _ _ 1444 52 203519620537104357537198336000 203520792837734990529840000000 203519610033136774831036800000 203519655368820490365552096000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt29 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 29 (witness 29) := by
  apply checks_of_runs _ _ _ _ _ _ 1447 52 206303519728923458449433423040 206304707473397978275195263360 206303391397621704451263667200 206303436733305419985778963200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt30 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 30 (witness 30) := by
  apply checks_of_runs _ _ _ _ _ _ 1451 52 209941193985626654125852677120 209942401804231764374722068480 209941175897928454509897292800 209941221233612170044412588800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt31 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 31 (witness 31) := by
  apply checks_of_runs _ _ _ _ _ _ 1455 52 213681618545643969543374837760 213682847099830188534045757440 213681473592389770433629363200 213681518928073485968144659200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipt32 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2500 32 (witness 32) := by
  apply checks_of_runs _ _ _ _ _ _ 1460 52 218125020649363989093697570560 218126273749142828662299623040 218124935277024228554673331200 218124980612707944089188627200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

end Lower6960.FarTerminalReceipts
