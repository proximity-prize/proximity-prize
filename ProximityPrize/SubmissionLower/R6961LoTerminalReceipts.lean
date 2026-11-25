import ProximityPrize.SubmissionLower.R6961TerminalArithmetic
import ProximityPrize.SubmissionLower.R6961LoTerminalBank

set_option Elab.async false
set_option maxHeartbeats 9000000
set_option maxRecDepth 18000
namespace Lower6961.Lo.TerminalReceipts
open Lower6961.TerminalArithmetic

def terminalBank : P1_7.Bank := ⟨⟨4500,6285,1329,1232000⟩,2693670660997120,42024370842405⟩

theorem bank_checked : P3_7_1.BankOK terminalBank :=
  P3_7_1.checked terminalBank rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) Lower6961.Lo.TerminalBank.moment_6285_1329

def witness : ℕ → RectArgs
  | 0 => ⟨![1133440, 98560], ![1746, 1746]⟩
  | 1 => ⟨![1084160, 147840], ![0, 2002]⟩
  | 2 => ⟨![1084160, 147840], ![0, 1993]⟩
  | 3 => ⟨![1084160, 147840], ![0, 1984]⟩
  | 4 => ⟨![1084160, 147840], ![0, 1975]⟩
  | 5 => ⟨![1084160, 147840], ![0, 1966]⟩
  | 6 => ⟨![1084160, 147840], ![0, 1957]⟩
  | 7 => ⟨![1084160, 147840], ![0, 1947]⟩
  | 8 => ⟨![1084160, 147840], ![0, 1938]⟩
  | 9 => ⟨![1084160, 147840], ![0, 1928]⟩
  | 10 => ⟨![1084160, 147840], ![0, 1919]⟩
  | 11 => ⟨![1084160, 147840], ![0, 1909]⟩
  | 12 => ⟨![1084160, 147840], ![0, 1899]⟩
  | 13 => ⟨![1084160, 147840], ![0, 1889]⟩
  | 14 => ⟨![1084160, 147840], ![0, 1879]⟩
  | 15 => ⟨![1084160, 147840], ![0, 1869]⟩
  | 16 => ⟨![1084160, 147840], ![0, 1859]⟩
  | 17 => ⟨![1084160, 147840], ![0, 1848]⟩
  | 18 => ⟨![1084160, 147840], ![0, 1838]⟩
  | 19 => ⟨![1084160, 147840], ![0, 1827]⟩
  | 20 => ⟨![1084160, 147840], ![0, 1816]⟩
  | 21 => ⟨![1084160, 147840], ![0, 1805]⟩
  | 22 => ⟨![1084160, 147840], ![0, 1794]⟩
  | 23 => ⟨![1084160, 147840], ![0, 1782]⟩
  | 24 => ⟨![1084160, 147840], ![0, 1771]⟩
  | 25 => ⟨![1084160, 147840], ![0, 1759]⟩
  | 26 => ⟨![1084160, 147840], ![0, 1748]⟩
  | 27 => ⟨![1084160, 147840], ![0, 1735]⟩
  | 28 => ⟨![1084160, 147840], ![0, 1723]⟩
  | 29 => ⟨![1084160, 147840], ![0, 1711]⟩
  | 30 => ⟨![1084160, 147840], ![0, 1698]⟩
  | 31 => ⟨![1084160, 147840], ![0, 1685]⟩
  | 32 => ⟨![1084160, 147840], ![0, 1672]⟩
  | 33 => ⟨![1084160, 147840], ![0, 1659]⟩
  | 34 => ⟨![1084160, 147840], ![0, 1645]⟩
  | 35 => ⟨![1084160, 147840], ![0, 1631]⟩
  | 36 => ⟨![1084160, 147840], ![0, 1617]⟩
  | 37 => ⟨![1084160, 147840], ![0, 1602]⟩
  | 38 => ⟨![1084160, 147840], ![0, 1587]⟩
  | 39 => ⟨![1084160, 147840], ![0, 1571]⟩
  | 40 => ⟨![1084160, 147840], ![0, 1556]⟩
  | 41 => ⟨![1084160, 147840], ![0, 1539]⟩
  | 42 => ⟨![1084160, 147840], ![0, 1522]⟩
  | 43 => ⟨![1084160, 147840], ![0, 1505]⟩
  | 44 => ⟨![1084160, 147840], ![0, 1487]⟩
  | 45 => ⟨![1084160, 147840], ![0, 1468]⟩
  | 46 => ⟨![1084160, 147840], ![0, 1449]⟩
  | 47 => ⟨![1084160, 147840], ![0, 1428]⟩
  | 48 => ⟨![1084160, 147840], ![0, 1407]⟩
  | 49 => ⟨![1084160, 147840], ![0, 1384]⟩
  | 50 => ⟨![1084160, 147840], ![0, 1360]⟩
  | 51 => ⟨![1034880, 197120], ![0, 1328]⟩
  | 52 => ⟨![887040, 344960], ![0, 1228]⟩
  | 53 => ⟨![788480, 443520], ![0, 1065]⟩
  | 54 => ⟨![739200, 492800], ![0, 854]⟩
  | 55 => ⟨![689920, 542080], ![0, 605]⟩
  | 56 => ⟨![640640, 591360], ![0, 323]⟩
  | 57 => ⟨![640640, 591360], ![0, 15]⟩
  | 58 => ⟨![616000, 616000], ![0, 0]⟩
  | _ => ⟨![0, 0], ![0, 0]⟩

private theorem check0 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 1 (witness 0) := by
  apply checks_of_runs _ _ _ _ _ _ 1386 51 433497259587366593833101207840 433499799420879127651377116640 433497173469100598839578307200 433497248023817453121466833600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check1 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 1 (witness 1) := by
  apply checks_of_runs _ _ _ _ _ _ 1403 52 621896133532939556204643780960 621899744668279051099296618720 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check2 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 2 (witness 2) := by
  apply checks_of_runs _ _ _ _ _ _ 1404 52 621896121400440261086560368000 621899732521572422795652153600 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check3 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 3 (witness 3) := by
  apply checks_of_runs _ _ _ _ _ _ 1404 52 621896116924892948870292425280 621899728034969099744168811840 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check4 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 4 (witness 4) := by
  apply checks_of_runs _ _ _ _ _ _ 1404 52 621896136618776470340839522560 621899747728099010564362750080 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check5 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 5 (witness 5) := by
  apply checks_of_runs _ _ _ _ _ _ 1405 52 621896160598272651040153813440 621899771708525059770229872000 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check6 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 6 (witness 6) := by
  apply checks_of_runs _ _ _ _ _ _ 1405 52 621896195083638076507666350720 621899806199194477448876154240 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check7 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 7 (witness 7) := by
  apply checks_of_runs _ _ _ _ _ _ 1405 52 621896109137276106004716049920 621899720205757615655028627840 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check8 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 8 (witness 8) := by
  apply checks_of_runs _ _ _ _ _ _ 1406 52 621896168465256613251966870240 621899779549428799487036860320 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check9 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 9 (witness 9) := by
  apply checks_of_runs _ _ _ _ _ _ 1406 52 621896101072011248955537817440 621899712116738420456071113120 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check10 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 10 (witness 10) := by
  apply checks_of_runs _ _ _ _ _ _ 1407 52 621896204063507490088644460320 621899815142460642317817599520 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check11 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 11 (witness 11) := by
  apply checks_of_runs _ _ _ _ _ _ 1407 52 621896157811664826364740978720 621899768859902451806291557920 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check12 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 12 (witness 12) := by
  apply checks_of_runs _ _ _ _ _ _ 1407 52 621896141791460842937330937120 621899752821869403091811596320 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check13 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 13 (witness 13) := by
  apply checks_of_runs _ _ _ _ _ _ 1408 52 621896133733876915581493126080 621899744749671137102516629440 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check14 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 14 (witness 14) := by
  apply checks_of_runs _ _ _ _ _ _ 1408 52 621896144339583883775997276480 621899755348618109034646827840 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check15 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 15 (witness 15) := by
  apply checks_of_runs _ _ _ _ _ _ 1409 52 621896178199796574316686362880 621899789211915396761293453440 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check16 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 16 (witness 16) := by
  apply checks_of_runs _ _ _ _ _ _ 1409 52 621896218454765665763460089280 621899829472480751433949007040 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check17 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 17 (witness 17) := by
  apply checks_of_runs _ _ _ _ _ _ 1410 52 621896146772442376305008566080 621899757746882990653019676480 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check18 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 18 (witness 18) := by
  apply checks_of_runs _ _ _ _ _ _ 1410 52 621896221545066824616246804480 621899832539531581474846942080 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check19 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 19 (witness 19) := by
  apply checks_of_runs _ _ _ _ _ _ 1410 52 621896185756240940955183714720 621899796722417372743887270240 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check20 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 20 (witness 20) := by
  apply checks_of_runs _ _ _ _ _ _ 1411 52 621896158387453436335583523360 621899769328664748507896076000 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check21 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 21 (witness 21) := by
  apply checks_of_runs _ _ _ _ _ _ 1411 52 621896163924411486433919437920 621899774854631889483234126240 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check22 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 22 (witness 22) := by
  apply checks_of_runs _ _ _ _ _ _ 1412 52 621896181066548037692937573120 621899791990462709718290075520 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check23 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 23 (witness 23) := by
  apply checks_of_runs _ _ _ _ _ _ 1412 52 621896088375166135159226856960 621899699244654400504338942720 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check24 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 24 (witness 24) := by
  apply checks_of_runs _ _ _ _ _ _ 1413 52 621896151433199369647637059200 621899762315590918866183010560 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check25 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 25 (witness 25) := by
  apply checks_of_runs _ _ _ _ _ _ 1414 52 621896108083512405760265482080 621899718932123992939189422240 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check26 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 26 (witness 26) := by
  apply checks_of_runs _ _ _ _ _ _ 1414 52 621896223250673924467475545920 621899834134047715061219476800 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check27 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 27 (witness 27) := by
  apply checks_of_runs _ _ _ _ _ _ 1415 52 621896086330647441234567703200 621899697138593550833976824160 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check28 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 28 (witness 28) := by
  apply checks_of_runs _ _ _ _ _ _ 1415 52 621896120231335194192567403680 621899731037736411881375645280 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check29 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 29 (witness 29) := by
  apply checks_of_runs _ _ _ _ _ _ 1416 52 621896181851427440906729626560 621899792667851316348902328000 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check30 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 30 (witness 30) := by
  apply checks_of_runs _ _ _ _ _ _ 1417 52 621896139225656328979647879840 621899750006142324328372007520 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check31 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 31 (witness 31) := by
  apply checks_of_runs _ _ _ _ _ _ 1417 52 621896122760693979259523779200 621899733516030712598549541120 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check32 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 32 (witness 32) := by
  apply checks_of_runs _ _ _ _ _ _ 1418 52 621896143775232245005814045760 621899754521144010619573869120 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check33 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 33 (witness 33) := by
  apply checks_of_runs _ _ _ _ _ _ 1419 52 621896206135686804322351958880 621899816889573110268571969440 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check34 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 34 (witness 34) := by
  apply checks_of_runs _ _ _ _ _ _ 1419 52 621896163985739098416600188640 621899774701248611246078818080 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check35 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 35 (witness 35) := by
  apply checks_of_runs _ _ _ _ _ _ 1420 52 621896161994592856456057839360 621899772688468451066408438400 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check36 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 36 (witness 36) := by
  apply checks_of_runs _ _ _ _ _ _ 1421 52 621896206565097544292784936000 621899817256864180780860778560 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check37 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 37 (witness 37) := by
  apply checks_of_runs _ _ _ _ _ _ 1422 53 621896161281917976605318263200 621899771931381092224235397120 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check38 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 38 (witness 38) := by
  apply checks_of_runs _ _ _ _ _ _ 1423 53 621896167562928487391086516800 621899778191645338239185903520 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check39 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 39 (witness 39) := by
  apply checks_of_runs _ _ _ _ _ _ 1424 53 621896091571362924863355294720 621899702142199771138216355520 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check40 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 40 (witness 40) := by
  apply checks_of_runs _ _ _ _ _ _ 1425 53 621896210342698308686477321760 621899820939805678223777772000 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check41 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 41 (witness 41) := by
  apply checks_of_runs _ _ _ _ _ _ 1426 53 621896121347389437222562337280 621899731878346213064279376480 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check42 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 42 (witness 42) := by
  apply checks_of_runs _ _ _ _ _ _ 1427 53 621896102273951155682790033600 621899712767931087389827187520 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check43 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 43 (witness 43) := by
  apply checks_of_runs _ _ _ _ _ _ 1428 53 621896158099867676717303539200 621899768588147730866262168000 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check44 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 44 (witness 44) := by
  apply checks_of_runs _ _ _ _ _ _ 1429 53 621896165053844710917088356480 621899775513126002919626645760 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check45 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 45 (witness 45) := by
  apply checks_of_runs _ _ _ _ _ _ 1430 53 621896135168747622339547354080 621899745580733230500737215680 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check46 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 46 (witness 46) := by
  apply checks_of_runs _ _ _ _ _ _ 1432 53 621896206396900629952666097280 621899816803823700917724942720 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check47 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 47 (witness 47) := by
  apply checks_of_runs _ _ _ _ _ _ 1433 53 621896138114322713671164189600 621899748451783132251680803680 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check48 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 48 (witness 48) := by
  apply checks_of_runs _ _ _ _ _ _ 1435 53 621896199821272113092445879360 621899810143626413607009459840 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check49 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 49 (witness 49) := by
  apply checks_of_runs _ _ _ _ _ _ 1436 53 621896164313043292391135757600 621899774573996366440729794720 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check50 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 50 (witness 50) := by
  apply checks_of_runs _ _ _ _ _ _ 1438 53 621896173726953342725619976800 621899783943453930470927810400 621896081865724644929408707200 621896156420441499211297233600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check51 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 51 (witness 51) := by
  apply checks_of_runs _ _ _ _ _ _ 1453 54 791455152749577719003254247040 791459726182195850479132270560 791455099422686286410256067200 791455173977403140692144593600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check52 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 52 (witness 52) := by
  apply checks_of_runs _ _ _ _ _ _ 1450 54 1187092872347349028795053226560 1187099693323113690920072760480 1187092807055596783198899907200 1187092881610313637480788433600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check53 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 53 (witness 53) := by
  apply checks_of_runs _ _ _ _ _ _ 1448 53 1356651827010136811118974254560 1356659611095779242354104992640 1356651824612558424679747267200 1356651899167275278961635793600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check54 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 54 (witness 54) := by
  apply checks_of_runs _ _ _ _ _ _ 1446 53 1413171500064656115734301677760 1413179605107650863184577727680 1413171497131545638506696387200 1413171571686262492788584913600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check55 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 55 (witness 55) := by
  apply checks_of_runs _ _ _ _ _ _ 1444 53 1450851298126573583932350880320 1450859617103340269957858413920 1450851278810870447724662467200 1450851353365587302006550993600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check56 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 56 (witness 56) := by
  apply checks_of_runs _ _ _ _ _ _ 1442 53 1469691191790269867786257131840 1469699617664397370475813526720 1469691169650532852333645507200 1469691244205249706615534033600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check57 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 57 (witness 57) := by
  apply checks_of_runs _ _ _ _ _ _ 1440 53 1469691179189314330068262029600 1469699604934792742076310951200 1469691169650532852333645507200 1469691244205249706615534033600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check58 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 58 (witness 58) := by
  apply checks_of_runs _ _ _ _ _ _ 1438 53 1472061876291031759426003754880 1472070322337881873798316365920 1472046156005490652909768387200 1472046230560207507191656913600
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipts (i : Fin 59) : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2346 (max 1 i.val) (witness i.val) := by
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

theorem positive {h : ℕ} (lo : 2346≤h) (hi : h≤2449) (i : Fin 59) :
    KoalaRect.rectDebit h terminalBank.nodeRows terminalBank.poleMoment (witness i.val).U <
      KoalaRect.rectGain 179808 h terminalBank.shape (max 1 i.val) (witness i.val).U
        (witness i.val).order :=
  strict_of_checks lo (by omega) (by decide) (by decide) (by omega) (receipts i)

end Lower6961.Lo.TerminalReceipts
