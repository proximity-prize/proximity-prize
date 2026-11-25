import ProximityPrize.SubmissionLower.R6961TerminalArithmetic
import ProximityPrize.SubmissionLower.R6961TerminalBank

set_option Elab.async false
set_option maxHeartbeats 9000000
set_option maxRecDepth 18000
namespace Lower6961.Hi.TerminalReceipts
open Lower6961.TerminalArithmetic

def terminalBank : P1_7.Bank := ⟨⟨4500,6286,1329,850000⟩,2693670660997120,42045879552530⟩

theorem bank_checked : P3_7_1.BankOK terminalBank :=
  P3_7_1.checked terminalBank rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) Lower6961.TerminalBank.moment_6286_1329

def witness : ℕ → RectArgs
  | 0 => ⟨![782000, 68000], ![575, 575]⟩
  | 1 => ⟨![765000, 85000], ![0, 647]⟩
  | 2 => ⟨![765000, 85000], ![0, 641]⟩
  | 3 => ⟨![765000, 85000], ![0, 636]⟩
  | 4 => ⟨![765000, 85000], ![0, 631]⟩
  | 5 => ⟨![765000, 85000], ![0, 625]⟩
  | 6 => ⟨![765000, 85000], ![0, 620]⟩
  | 7 => ⟨![765000, 85000], ![0, 614]⟩
  | 8 => ⟨![765000, 85000], ![0, 608]⟩
  | 9 => ⟨![765000, 85000], ![0, 602]⟩
  | 10 => ⟨![765000, 85000], ![0, 596]⟩
  | 11 => ⟨![765000, 85000], ![0, 590]⟩
  | 12 => ⟨![765000, 85000], ![0, 584]⟩
  | 13 => ⟨![765000, 85000], ![0, 577]⟩
  | 14 => ⟨![765000, 85000], ![0, 571]⟩
  | 15 => ⟨![765000, 85000], ![0, 564]⟩
  | 16 => ⟨![765000, 85000], ![0, 557]⟩
  | 17 => ⟨![765000, 85000], ![0, 550]⟩
  | 18 => ⟨![765000, 85000], ![0, 542]⟩
  | 19 => ⟨![765000, 85000], ![0, 534]⟩
  | 20 => ⟨![765000, 85000], ![0, 526]⟩
  | 21 => ⟨![765000, 85000], ![0, 518]⟩
  | 22 => ⟨![765000, 85000], ![0, 509]⟩
  | 23 => ⟨![765000, 85000], ![0, 500]⟩
  | 24 => ⟨![765000, 85000], ![0, 490]⟩
  | 25 => ⟨![765000, 85000], ![0, 480]⟩
  | 26 => ⟨![765000, 85000], ![0, 469]⟩
  | 27 => ⟨![765000, 85000], ![0, 457]⟩
  | 28 => ⟨![765000, 85000], ![0, 443]⟩
  | 29 => ⟨![697000, 153000], ![0, 421]⟩
  | 30 => ⟨![561000, 289000], ![0, 314]⟩
  | 31 => ⟨![561000, 289000], ![0, 177]⟩
  | 32 => ⟨![561000, 289000], ![0, 30]⟩
  | 33 => ⟨![595000, 255000], ![0, 1]⟩
  | 34 => ⟨![663000, 187000], ![0, 1]⟩
  | 35 => ⟨![663000, 187000], ![0, 1]⟩
  | 36 => ⟨![697000, 153000], ![0, 1]⟩
  | 37 => ⟨![697000, 153000], ![0, 1]⟩
  | 38 => ⟨![731000, 119000], ![0, 1]⟩
  | 39 => ⟨![731000, 119000], ![0, 1]⟩
  | 40 => ⟨![731000, 119000], ![0, 1]⟩
  | 41 => ⟨![731000, 119000], ![0, 1]⟩
  | 42 => ⟨![731000, 119000], ![0, 1]⟩
  | 43 => ⟨![731000, 119000], ![0, 1]⟩
  | 44 => ⟨![765000, 85000], ![0, 1]⟩
  | 45 => ⟨![765000, 85000], ![0, 1]⟩
  | 46 => ⟨![765000, 85000], ![0, 1]⟩
  | 47 => ⟨![765000, 85000], ![0, 1]⟩
  | 48 => ⟨![425000, 425000], ![0, 0]⟩
  | _ => ⟨![0, 0], ![0, 0]⟩

private theorem check0 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 1 (witness 0) := by
  apply checks_of_runs _ _ _ _ _ _ 1448 52 206393066207569165528702892160 206394242733173859646048208640 206393013276669107806167532800 206393064740946772235998819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check1 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 1 (witness 1) := by
  apply checks_of_runs _ _ _ _ _ _ 1461 52 252354227112836712165164973120 252355654241290400321096298720 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check2 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 2 (witness 2) := by
  apply checks_of_runs _ _ _ _ _ _ 1462 52 252353948014261777919700366720 252355375015301674852854755040 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check3 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 3 (witness 3) := by
  apply checks_of_runs _ _ _ _ _ _ 1463 52 252354040583292903125387664000 252355467610676887692219298080 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check4 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 4 (witness 4) := by
  apply checks_of_runs _ _ _ _ _ _ 1464 52 252354164205532049580752579520 252355591271755193205030006240 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check5 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 5 (witness 5) := by
  apply checks_of_runs _ _ _ _ _ _ 1466 52 252353981180966115224476189440 252355408158312682509668721120 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check6 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 6 (witness 6) := by
  apply checks_of_runs _ _ _ _ _ _ 1467 52 252354170745625409759155737600 252355597788305035657572429600 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check7 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 7 (witness 7) := by
  apply checks_of_runs _ _ _ _ _ _ 1468 53 252354055213691961387730606080 252355482194504840143824120480 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check8 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 8 (witness 8) := by
  apply checks_of_runs _ _ _ _ _ _ 1469 53 252353981094862903828013005920 252355408030439341146036630720 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check9 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 9 (witness 9) := by
  apply checks_of_runs _ _ _ _ _ _ 1471 53 252353947339241347923742749120 252355374245747156130022479840 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check10 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 10 (witness 10) := by
  apply checks_of_runs _ _ _ _ _ _ 1472 53 252353956733121307180857117120 252355383627851739495193544160 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check11 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 11 (witness 11) := by
  apply checks_of_runs _ _ _ _ _ _ 1474 53 252354014842248011806307540640 252355441744785698020605680640 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check12 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 12 (witness 12) := by
  apply checks_of_runs _ _ _ _ _ _ 1475 53 252354119362268960336834655360 252355546291199660244087190560 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check13 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 13 (witness 13) := by
  apply checks_of_runs _ _ _ _ _ _ 1477 53 252353942039266124547936421440 252355368876428153060491790880 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check14 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 14 (witness 14) := by
  apply checks_of_runs _ _ _ _ _ _ 1478 53 252354158843065968212092163520 252355585751721076999145064480 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check15 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 15 (witness 15) := by
  apply checks_of_runs _ _ _ _ _ _ 1480 53 252354100801488455700702250560 252355527666145501170759675360 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check16 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 16 (witness 16) := by
  apply checks_of_runs _ _ _ _ _ _ 1482 53 252354110648212822843568384640 252355537496070804160383130080 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check17 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 17 (witness 17) := by
  apply checks_of_runs _ _ _ _ _ _ 1484 53 252354193379169478517230467840 252355620239444648600025697440 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check18 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 18 (witness 18) := by
  apply checks_of_runs _ _ _ _ _ _ 1486 53 252354027512857394684803728960 252355454280363553585024992480 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check19 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 19 (witness 19) := by
  apply checks_of_runs _ _ _ _ _ _ 1489 53 252353950948912554181957776480 252355377659352526501714224000 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check20 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 20 (witness 20) := by
  apply checks_of_runs _ _ _ _ _ _ 1491 53 252353972423054436663940993440 252355399115665829040311446080 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check21 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 21 (witness 21) := by
  apply checks_of_runs _ _ _ _ _ _ 1494 54 252354102722322088904252615520 252355529440732074336341238240 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check22 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 22 (witness 22) := by
  apply checks_of_runs _ _ _ _ _ _ 1496 54 252354035791015674950915078400 252355462450271571322825365600 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check23 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 23 (witness 23) := by
  apply checks_of_runs _ _ _ _ _ _ 1500 54 252354108062773177436242235520 252355534718543106558596945280 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check24 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 24 (witness 24) := by
  apply checks_of_runs _ _ _ _ _ _ 1503 54 252354030379533188061427311840 252355456965511768288250244960 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check25 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 25 (witness 25) := by
  apply checks_of_runs _ _ _ _ _ _ 1507 54 252354140743398737290628335200 252355567334782964180437219680 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check26 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 26 (witness 26) := by
  apply checks_of_runs _ _ _ _ _ _ 1511 54 252354172509356188599767033280 252355599068133347186190537600 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check27 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 27 (witness 27) := by
  apply checks_of_runs _ _ _ _ _ _ 1515 54 252354185670967385251092530400 252355612182966444391941553920 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check28 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 28 (witness 28) := by
  apply checks_of_runs _ _ _ _ _ _ 1521 55 252353985803531654854784666400 252355412170922020648969093920 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check29 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 29 (witness 29) := by
  apply checks_of_runs _ _ _ _ _ _ 1546 56 413777761194597267979377637920 413780065825275586051489863360 413777639998572977758167532800 413777691462850642187998819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check30 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 30 (witness 30) := by
  apply checks_of_runs _ _ _ _ _ _ 1539 55 629009380331720010707786573760 629012855847747159881837075520 629009252596440777924567532800 629009304060718442354398819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check31 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 31 (witness 31) := by
  apply checks_of_runs _ _ _ _ _ _ 1532 55 629009393932670159448252067680 629012869282160440585888010400 629009252596440777924567532800 629009304060718442354398819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check32 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 32 (witness 32) := by
  apply checks_of_runs _ _ _ _ _ _ 1526 55 629009330726892756423450235680 629012805887612862158520571200 629009252596440777924567532800 629009304060718442354398819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check33 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 33 (witness 33) := by
  apply checks_of_runs _ _ _ _ _ _ 1520 55 588662388415817030818065039840 588665647735765098047592420960 588653325234340565393367532800 588653376698618229823198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check34 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 34 (witness 34) := by
  apply checks_of_runs _ _ _ _ _ _ 1514 54 481038218610628072975804535040 481040888826057909256273825440 481037518935406665310167532800 481037570399684329739998819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check35 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 35 (witness 35) := by
  apply checks_of_runs _ _ _ _ _ _ 1509 54 481053592637854983658776096000 481056269326487848972294488000 481037518935406665310167532800 481037570399684329739998819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check36 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 36 (witness 36) := by
  apply checks_of_runs _ _ _ _ _ _ 1504 54 413786348537398570583524539360 413788656138937708198129198560 413777639998572977758167532800 413777691462850642187998819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check37 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 37 (witness 37) := by
  apply checks_of_runs _ _ _ _ _ _ 1499 54 413798162979547798200025083360 413800475556913915022621081280 413777639998572977758167532800 413777691462850642187998819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check38 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 38 (witness 38) := by
  apply checks_of_runs _ _ _ _ _ _ 1495 54 337552444795510677328467004800 337554335067816650558958961920 337549777203494798532567532800 337549828667772462962398819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check39 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 39 (witness 39) := by
  apply checks_of_runs _ _ _ _ _ _ 1491 53 337561106294975948752783315680 337563000214546098654003519360 337549777203494798532567532800 337549828667772462962398819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check40 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 40 (witness 40) := by
  apply checks_of_runs _ _ _ _ _ _ 1487 53 337569335279019171900300098880 337571232662725994613021304320 337549777203494798532567532800 337549828667772462962398819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check41 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 41 (witness 41) := by
  apply checks_of_runs _ _ _ _ _ _ 1483 53 337577163372399045548847107520 337579064053569144786056764320 337549777203494798532567532800 337549828667772462962398819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check42 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 42 (witness 42) := by
  apply checks_of_runs _ _ _ _ _ _ 1479 53 337584619164635906097012022080 337586522989780577296311533280 337549777203494798532567532800 337549828667772462962398819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check43 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 43 (witness 43) := by
  apply checks_of_runs _ _ _ _ _ _ 1476 53 337591728622515292882392247200 337593635440612864555490245440 337549777203494798532567532800 337549828667772462962398819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check44 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 44 (witness 44) := by
  apply checks_of_runs _ _ _ _ _ _ 1472 53 252358558532640215638841652480 252359986050871490177663762880 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check45 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 45 (witness 45) := by
  apply checks_of_runs _ _ _ _ _ _ 1469 53 252363405072615514949710226880 252364834631885605914959763840 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check46 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 46 (witness 46) := by
  apply checks_of_runs _ _ _ _ _ _ 1466 52 252368041178343443258011299840 252369472689938911042888920000 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check47 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 47 (witness 47) := by
  apply checks_of_runs _ _ _ _ _ _ 1463 52 252372480231743109327671159040 252373913613080539442230972320 252353930550172127633367532800 252353982014449792063198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check48 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 48 (witness 48) := by
  apply checks_of_runs _ _ _ _ _ _ 1460 52 701040363034543054796888517600 701044349482962700955111327040 700753123462396711313367532800 700753174926674375743198819200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipts (i : Fin 49) : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 (max 1 i.val) (witness i.val) := by
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

theorem positive {h : ℕ} (lo : 2450≤h) (hi : h≤33599) (i : Fin 49) :
    KoalaRect.rectDebit h terminalBank.nodeRows terminalBank.poleMoment (witness i.val).U <
      KoalaRect.rectGain 179808 h terminalBank.shape (max 1 i.val) (witness i.val).U
        (witness i.val).order :=
  strict_of_checks lo (by omega) (by decide) (by decide) (by omega) (receipts i)

end Lower6961.Hi.TerminalReceipts
