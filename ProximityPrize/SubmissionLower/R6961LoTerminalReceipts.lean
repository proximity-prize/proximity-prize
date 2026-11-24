import ProximityPrize.SubmissionLower.R6961TerminalArithmetic
import ProximityPrize.SubmissionLower.R6961LoTerminalBank

set_option Elab.async false
set_option maxHeartbeats 9000000
set_option maxRecDepth 18000
namespace Lower6961.Lo.TerminalReceipts
open Lower6961.TerminalArithmetic

def terminalBank : P1_7.Bank := ⟨⟨4500,6285,1329,1004000⟩,2693670660997120,42024370842405⟩

theorem bank_checked : P3_7_1.BankOK terminalBank :=
  P3_7_1.checked terminalBank rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) Lower6961.Lo.TerminalBank.moment_6285_1329

def witness : ℕ → RectArgs
  | 0 => ⟨![903600, 100400], ![1692, 1692]⟩
  | 1 => ⟨![839344, 114456], ![0, 1800]⟩
  | 2 => ⟨![839344, 114456], ![0, 1793]⟩
  | 3 => ⟨![839344, 114456], ![0, 1786]⟩
  | 4 => ⟨![839344, 114456], ![0, 1779]⟩
  | 5 => ⟨![839344, 114456], ![0, 1772]⟩
  | 6 => ⟨![839344, 114456], ![0, 1765]⟩
  | 7 => ⟨![839344, 114456], ![0, 1757]⟩
  | 8 => ⟨![839344, 114456], ![0, 1750]⟩
  | 9 => ⟨![839344, 114456], ![0, 1743]⟩
  | 10 => ⟨![839344, 114456], ![0, 1735]⟩
  | 11 => ⟨![839344, 114456], ![0, 1728]⟩
  | 12 => ⟨![839344, 114456], ![0, 1721]⟩
  | 13 => ⟨![839344, 114456], ![0, 1713]⟩
  | 14 => ⟨![839344, 114456], ![0, 1705]⟩
  | 15 => ⟨![839344, 114456], ![0, 1698]⟩
  | 16 => ⟨![839344, 114456], ![0, 1690]⟩
  | 17 => ⟨![839344, 114456], ![0, 1682]⟩
  | 18 => ⟨![839344, 114456], ![0, 1674]⟩
  | 19 => ⟨![839344, 114456], ![0, 1666]⟩
  | 20 => ⟨![839344, 114456], ![0, 1658]⟩
  | 21 => ⟨![839344, 114456], ![0, 1650]⟩
  | 22 => ⟨![839344, 114456], ![0, 1641]⟩
  | 23 => ⟨![839344, 114456], ![0, 1633]⟩
  | 24 => ⟨![839344, 114456], ![0, 1625]⟩
  | 25 => ⟨![839344, 114456], ![0, 1616]⟩
  | 26 => ⟨![839344, 114456], ![0, 1607]⟩
  | 27 => ⟨![839344, 114456], ![0, 1598]⟩
  | 28 => ⟨![839344, 114456], ![0, 1590]⟩
  | 29 => ⟨![839344, 114456], ![0, 1581]⟩
  | 30 => ⟨![839344, 114456], ![0, 1571]⟩
  | 31 => ⟨![839344, 114456], ![0, 1562]⟩
  | 32 => ⟨![883520, 120480], ![0, 1551]⟩
  | 33 => ⟨![883520, 120480], ![0, 1541]⟩
  | 34 => ⟨![883520, 120480], ![0, 1531]⟩
  | 35 => ⟨![883520, 120480], ![0, 1520]⟩
  | 36 => ⟨![883520, 120480], ![0, 1509]⟩
  | 37 => ⟨![883520, 120480], ![0, 1498]⟩
  | 38 => ⟨![883520, 120480], ![0, 1487]⟩
  | 39 => ⟨![883520, 120480], ![0, 1476]⟩
  | 40 => ⟨![883520, 120480], ![0, 1464]⟩
  | 41 => ⟨![883520, 120480], ![0, 1452]⟩
  | 42 => ⟨![883520, 120480], ![0, 1440]⟩
  | 43 => ⟨![883520, 120480], ![0, 1427]⟩
  | 44 => ⟨![883520, 120480], ![0, 1414]⟩
  | 45 => ⟨![883520, 120480], ![0, 1401]⟩
  | 46 => ⟨![883520, 120480], ![0, 1388]⟩
  | 47 => ⟨![883520, 120480], ![0, 1374]⟩
  | 48 => ⟨![883520, 120480], ![0, 1360]⟩
  | 49 => ⟨![883520, 120480], ![0, 1345]⟩
  | 50 => ⟨![823280, 180720], ![0, 1328]⟩
  | 51 => ⟨![823280, 180720], ![0, 1284]⟩
  | 52 => ⟨![742960, 261040], ![0, 1194]⟩
  | 53 => ⟨![642560, 361440], ![0, 1059]⟩
  | 54 => ⟨![642560, 361440], ![0, 904]⟩
  | 55 => ⟨![522080, 481920], ![0, 731]⟩
  | 56 => ⟨![522080, 481920], ![0, 498]⟩
  | 57 => ⟨![522080, 481920], ![0, 256]⟩
  | 58 => ⟨![502000, 502000], ![0, 0]⟩
  | _ => ⟨![0, 0], ![0, 0]⟩

private theorem check0 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 1 (witness 0) := by
  apply checks_of_runs _ _ _ _ _ _ 1389 52 352043450119961771102994877920 352045510112972407901589954720 352043377587105657787540785600 352043438344381077091019712000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check1 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 1 (witness 1) := by
  apply checks_of_runs _ _ _ _ _ _ 1393 53 372774778161049179647461641600 372776952856769693477908790400 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check2 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 2 (witness 2) := by
  apply checks_of_runs _ _ _ _ _ _ 1393 53 372774773334776368206359966400 372776948024442445457140658400 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check3 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 3 (witness 3) := by
  apply checks_of_runs _ _ _ _ _ _ 1394 53 372774771262956827296142395200 372776945947709711714261092800 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check4 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 4 (witness 4) := by
  apply checks_of_runs _ _ _ _ _ _ 1394 53 372774766493579360679881424000 372776941172177963178566983200 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check5 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 5 (witness 5) := by
  apply checks_of_runs _ _ _ _ _ _ 1394 53 372774771092071691236576612800 372776945768541740134339113600 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check6 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 6 (witness 6) := by
  apply checks_of_runs _ _ _ _ _ _ 1394 53 372774785058433818966227961600 372776959736801042581577484000 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check7 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 7 (witness 7) := by
  apply checks_of_runs _ _ _ _ _ _ 1395 53 372774716311273415470031500800 372776890955336379769754296800 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check8 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 8 (witness 8) := by
  apply checks_of_runs _ _ _ _ _ _ 1395 53 372774732530164661990735769600 372776907176966560500103435200 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check9 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 9 (witness 9) := by
  apply checks_of_runs _ _ _ _ _ _ 1395 53 372774758559448624882246598400 372776933213205354772024413600 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check10 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 10 (witness 10) := by
  apply checks_of_runs _ _ _ _ _ _ 1395 53 372774711610685494509281625600 372776886239431206372291223200 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check11 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 11 (witness 11) := by
  apply checks_of_runs _ _ _ _ _ _ 1396 53 372774743063526302344948190400 372776917701444078216632659200 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check12 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 12 (witness 12) := by
  apply checks_of_runs _ _ _ _ _ _ 1396 53 372774782826289839785817643200 372776957476936063480823378400 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check13 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 13 (witness 13) := by
  apply checks_of_runs _ _ _ _ _ _ 1396 53 372774749830581173347102334400 372776924462066043718659775200 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check14 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 14 (witness 14) := by
  apply checks_of_runs _ _ _ _ _ _ 1397 53 372774720833905176433657857600 372776895447885636384794738400 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check15 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 15 (witness 15) := by
  apply checks_of_runs _ _ _ _ _ _ 1397 53 372774776870097143784248198400 372776951503669238058955406400 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check16 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 16 (witness 16) := by
  apply checks_of_runs _ _ _ _ _ _ 1397 53 372774760550936754221549145600 372776935172365328703871406400 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check17 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 17 (witness 17) := by
  apply checks_of_runs _ _ _ _ _ _ 1398 53 372774753812582858132957620800 372776928425962675037011742400 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check18 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 18 (witness 18) := by
  apply checks_of_runs _ _ _ _ _ _ 1398 53 372774744287603146248968520000 372776918891608229813528126400 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check19 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 19 (witness 19) := by
  apply checks_of_runs _ _ _ _ _ _ 1398 53 372774747586765561253907163200 372776922186906930871704926400 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check20 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 20 (witness 20) := by
  apply checks_of_runs _ _ _ _ _ _ 1399 53 372774761975824848474762470400 372776936576852993204585966400 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check21 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 21 (witness 21) := by
  apply checks_of_runs _ _ _ _ _ _ 1399 53 372774773831097644079794697600 372776948431785809639890344000 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check22 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 22 (witness 22) := by
  apply checks_of_runs _ _ _ _ _ _ 1399 53 372774716400125586364722403200 372776890970019520329750568800 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check23 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 23 (witness 23) := by
  apply checks_of_runs _ _ _ _ _ _ 1400 53 372774751498431857182854542400 372776926077933438983681541600 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check24 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 24 (witness 24) := by
  apply checks_of_runs _ _ _ _ _ _ 1400 53 372774788049195259471372449600 372776962638814080021970495200 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check25 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 25 (witness 25) := by
  apply checks_of_runs _ _ _ _ _ _ 1400 53 372774756398201193919800715200 372776930967929624912569248000 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check26 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 26 (witness 26) := by
  apply checks_of_runs _ _ _ _ _ _ 1401 53 372774730379207220507959380800 372776904931365665295635584800 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check27 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 27 (witness 27) := by
  apply checks_of_runs _ _ _ _ _ _ 1401 53 372774712794494108766822086400 372776887332629689913511019200 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check28 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 28 (witness 28) := by
  apply checks_of_runs _ _ _ _ _ _ 1401 53 372774793093519523163640185600 372776967660415038612142680000 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check29 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 29 (witness 29) := by
  apply checks_of_runs _ _ _ _ _ _ 1402 53 372774791014984145378353651200 372776965574346985482340754400 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check30 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 30 (witness 30) := by
  apply checks_of_runs _ _ _ _ _ _ 1402 53 372774723921963491746446691200 372776898445109663804177018400 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check31 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 31 (witness 31) := by
  apply checks_of_runs _ _ _ _ _ _ 1403 53 372774745645634782967537404800 372776920171351028840081390400 372774641857847447999818564800 372774699577265147847524851200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check32 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 32 (witness 32) := by
  apply checks_of_runs _ _ _ _ _ _ 1407 53 413039128200033940297264897920 413041534354362570784923584160 413039048427457734125839665600 413039109184733153429318592000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check33 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 33 (witness 33) := by
  apply checks_of_runs _ _ _ _ _ _ 1408 53 413039155587479871167313241920 413041561744627193725281656160 413039048427457734125839665600 413039109184733153429318592000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check34 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 34 (witness 34) := by
  apply checks_of_runs _ _ _ _ _ _ 1408 53 413039196243618678275230854720 413041602409141604793682534560 413039048427457734125839665600 413039109184733153429318592000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check35 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 35 (witness 35) := by
  apply checks_of_runs _ _ _ _ _ _ 1409 53 413039162042355995618078471040 413041568183058767565031344000 413039048427457734125839665600 413039109184733153429318592000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check36 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 36 (witness 36) := by
  apply checks_of_runs _ _ _ _ _ _ 1409 53 413039146138602492967718823360 413041552262211564365464510560 413039048427457734125839665600 413039109184733153429318592000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check37 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 37 (witness 37) := by
  apply checks_of_runs _ _ _ _ _ _ 1410 53 413039145953367400239787740480 413041552066450410833906481600 413039048427457734125839665600 413039109184733153429318592000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check38 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 38 (witness 38) := by
  apply checks_of_runs _ _ _ _ _ _ 1411 53 413039170110834194980804992000 413041576223772396301654542240 413039048427457734125839665600 413039109184733153429318592000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check39 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 39 (witness 39) := by
  apply checks_of_runs _ _ _ _ _ _ 1411 53 413039208001281881811574101120 413041614119726570587826795520 413039048427457734125839665600 413039109184733153429318592000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check40 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 40 (witness 40) := by
  apply checks_of_runs _ _ _ _ _ _ 1412 53 413039179768368359315816919360 413041585862797687726363906560 413039048427457734125839665600 413039109184733153429318592000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check41 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 41 (witness 41) := by
  apply checks_of_runs _ _ _ _ _ _ 1412 53 413039176512481932620226840000 413041582593468556403122085760 413039048427457734125839665600 413039109184733153429318592000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check42 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 42 (witness 42) := by
  apply checks_of_runs _ _ _ _ _ _ 1413 53 413039192676522147997314791040 413041598752130886740366655360 413039048427457734125839665600 413039109184733153429318592000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check43 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 43 (witness 43) := by
  apply checks_of_runs _ _ _ _ _ _ 1414 53 413039147454382077794089267200 413041553497015851403489762080 413039048427457734125839665600 413039109184733153429318592000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check44 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 44 (witness 44) := by
  apply checks_of_runs _ _ _ _ _ _ 1415 53 413039131367202723544727938560 413041537389157050700036002240 413039048427457734125839665600 413039109184733153429318592000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check45 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 45 (witness 45) := by
  apply checks_of_runs _ _ _ _ _ _ 1415 53 413039145506821523937055221120 413041551520848277075267425120 413039048427457734125839665600 413039109184733153429318592000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check46 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 46 (witness 46) := by
  apply checks_of_runs _ _ _ _ _ _ 1416 53 413039187945842633862459497280 413041593963778088058351308160 413039048427457734125839665600 413039109184733153429318592000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check47 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 47 (witness 47) := by
  apply checks_of_runs _ _ _ _ _ _ 1417 53 413039178323737955361284232960 413041584321830273947821614880 413039048427457734125839665600 413039109184733153429318592000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check48 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 48 (witness 48) := by
  apply checks_of_runs _ _ _ _ _ _ 1418 54 413039205850196580048657519840 413041611844093131183449759040 413039048427457734125839665600 413039109184733153429318592000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check49 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 49 (witness 49) := by
  apply checks_of_runs _ _ _ _ _ _ 1419 54 413039188448483078947049771040 413041594417365577460863786560 413039048427457734125839665600 413039109184733153429318592000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check50 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 50 (witness 50) := by
  apply checks_of_runs _ _ _ _ _ _ 1455 55 577258296212720919485734234560 577261633859344204333639549920 577258162228405631959721265600 577258222985681051263200192000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check51 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 51 (witness 51) := by
  apply checks_of_runs _ _ _ _ _ _ 1453 55 577258313293903549959231579360 577261650892497663439191225600 577258162228405631959721265600 577258222985681051263200192000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check52 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 52 (witness 52) := by
  apply checks_of_runs _ _ _ _ _ _ 1450 55 752425313984788487954900971680 752429645190276265109823063840 752425216949416722982528305600 752425277706692142286007232000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check53 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 53 (witness 53) := by
  apply checks_of_runs _ _ _ _ _ _ 1448 55 901004493106576474103871252000 901009667080134287526061487520 901004415150274344832230705600 901004475907549764135709632000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check54 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 54 (witness 54) := by
  apply checks_of_runs _ _ _ _ _ _ 1446 55 901004499379389468083965260480 901009673277240200680098561600 901004415150274344832230705600 901004475907549764135709632000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check55 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 55 (witness 55) := by
  apply checks_of_runs _ _ _ _ _ _ 1444 54 976076083458774651206166102720 976081683122234313539979324960 976076010030707669556290865600 976076070787983088859769792000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check56 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 56 (witness 56) := by
  apply checks_of_runs _ _ _ _ _ _ 1442 54 976076108964514554021698107680 976081708561621875644567011680 976076010030707669556290865600 976076070787983088859769792000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check57 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 57 (witness 57) := by
  apply checks_of_runs _ _ _ _ _ _ 1440 54 976076124612349224812293048320 976081724138843364402337985280 976076010030707669556290865600 976076070787983088859769792000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check58 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2327 58 (witness 58) := by
  apply checks_of_runs _ _ _ _ _ _ 1438 54 977640144567894797130578972160 977645752891385630219111882880 977640001590716697154708785600 977640062347992116458187712000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipts (i : Fin 59) : BlockChecks terminalBank.shape terminalBank.nodeRows
    terminalBank.poleMoment 2327 (max 1 i.val) (witness i.val) := by
  fin_cases i
  · exact check0
  · exact check1
  · exact check2
  · exact check3
  · exact check4
  · exact check5
  · exact check6
  · exact check7
  · exact check8
  · exact check9
  · exact check10
  · exact check11
  · exact check12
  · exact check13
  · exact check14
  · exact check15
  · exact check16
  · exact check17
  · exact check18
  · exact check19
  · exact check20
  · exact check21
  · exact check22
  · exact check23
  · exact check24
  · exact check25
  · exact check26
  · exact check27
  · exact check28
  · exact check29
  · exact check30
  · exact check31
  · exact check32
  · exact check33
  · exact check34
  · exact check35
  · exact check36
  · exact check37
  · exact check38
  · exact check39
  · exact check40
  · exact check41
  · exact check42
  · exact check43
  · exact check44
  · exact check45
  · exact check46
  · exact check47
  · exact check48
  · exact check49
  · exact check50
  · exact check51
  · exact check52
  · exact check53
  · exact check54
  · exact check55
  · exact check56
  · exact check57
  · exact check58

theorem positive {h : ℕ} (lo : 2327≤h) (hi : h≤2449) (i : Fin 59) :
    KoalaRect.rectDebit h terminalBank.nodeRows terminalBank.poleMoment (witness i.val).U <
      KoalaRect.rectGain 179818 h terminalBank.shape (max 1 i.val) (witness i.val).U
        (witness i.val).order :=
  strict_of_checks lo (by omega) (by decide) (by decide) (by omega) (receipts i)

end Lower6961.Lo.TerminalReceipts
