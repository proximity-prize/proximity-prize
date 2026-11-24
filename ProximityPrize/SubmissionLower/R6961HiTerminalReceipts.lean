import ProximityPrize.SubmissionLower.R6961TerminalArithmetic
import ProximityPrize.SubmissionLower.R6961TerminalBank

set_option Elab.async false
set_option maxHeartbeats 9000000
set_option maxRecDepth 18000
namespace Lower6961.Hi.TerminalReceipts
open Lower6961.TerminalArithmetic

def terminalBank : P1_7.Bank := ⟨⟨4500,6286,1329,748778⟩,2693670660997120,42045879552530⟩

theorem bank_checked : P3_7_1.BankOK terminalBank :=
  P3_7_1.checked terminalBank rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) Lower6961.TerminalBank.moment_6286_1329

def witness : ℕ → RectArgs
  | 0 => ⟨![655181, 93597], ![1200, 1201]⟩
  | 1 => ⟨![668256, 80522], ![0, 1167]⟩
  | 2 => ⟨![667369, 81409], ![0, 1163]⟩
  | 3 => ⟨![667719, 81059], ![0, 1158]⟩
  | 4 => ⟨![666916, 81862], ![0, 1153]⟩
  | 5 => ⟨![667271, 81507], ![0, 1148]⟩
  | 6 => ⟨![666555, 82223], ![0, 1142]⟩
  | 7 => ⟨![666915, 81863], ![0, 1137]⟩
  | 8 => ⟨![666143, 82635], ![0, 1132]⟩
  | 9 => ⟨![666508, 82270], ![0, 1127]⟩
  | 10 => ⟨![665825, 82953], ![0, 1121]⟩
  | 11 => ⟨![666195, 82583], ![0, 1116]⟩
  | 12 => ⟨![665529, 83249], ![0, 1110]⟩
  | 13 => ⟨![664941, 83837], ![0, 1105]⟩
  | 14 => ⟨![665255, 83523], ![0, 1099]⟩
  | 15 => ⟨![664618, 84160], ![0, 1093]⟩
  | 16 => ⟨![665003, 83775], ![0, 1088]⟩
  | 17 => ⟨![664383, 84395], ![0, 1082]⟩
  | 18 => ⟨![663775, 85003], ![0, 1076]⟩
  | 19 => ⟨![663179, 85599], ![0, 1070]⟩
  | 20 => ⟨![663739, 85039], ![0, 1063]⟩
  | 21 => ⟨![663162, 85616], ![0, 1057]⟩
  | 22 => ⟨![662679, 86099], ![0, 1050]⟩
  | 23 => ⟨![662127, 86651], ![0, 1044]⟩
  | 24 => ⟨![661671, 87107], ![0, 1037]⟩
  | 25 => ⟨![661229, 87549], ![0, 1030]⟩
  | 26 => ⟨![660801, 87977], ![0, 1023]⟩
  | 27 => ⟨![660387, 88391], ![0, 1016]⟩
  | 28 => ⟨![660075, 88703], ![0, 1008]⟩
  | 29 => ⟨![658689, 90089], ![0, 1001]⟩
  | 30 => ⟨![658416, 90362], ![0, 993]⟩
  | 31 => ⟨![658159, 90619], ![0, 985]⟩
  | 32 => ⟨![656941, 91837], ![0, 977]⟩
  | 33 => ⟨![655851, 92927], ![0, 968]⟩
  | 34 => ⟨![654797, 93981], ![0, 959]⟩
  | 35 => ⟨![653879, 94899], ![0, 949]⟩
  | 36 => ⟨![652736, 96042], ![0, 939]⟩
  | 37 => ⟨![651234, 97544], ![0, 929]⟩
  | 38 => ⟨![648717, 100061], ![0, 918]⟩
  | 39 => ⟨![646343, 102435], ![0, 905]⟩
  | 40 => ⟨![641859, 106919], ![0, 891]⟩
  | 41 => ⟨![630789, 117989], ![0, 874]⟩
  | 42 => ⟨![560874, 187904], ![0, 836]⟩
  | 43 => ⟨![505414, 243364], ![0, 758]⟩
  | 44 => ⟨![465387, 283391], ![0, 650]⟩
  | 45 => ⟨![434812, 313966], ![0, 517]⟩
  | 46 => ⟨![410697, 338081], ![0, 364]⟩
  | 47 => ⟨![390926, 357852], ![0, 191]⟩
  | 48 => ⟨![374389, 374389], ![0, 0]⟩
  | _ => ⟨![0, 0], ![0, 0]⟩

private theorem check0 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 1 (witness 0) := by
  apply checks_of_runs _ _ _ _ _ _ 1407 50 238107470752235236359540712320 238108854526549756324615848960 237978794940965878509075340800 237978840276649594043590636800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check1 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 1 (witness 1) := by
  apply checks_of_runs _ _ _ _ _ _ 1398 50 208940757817527506536050733920 208941975077689631851815607200 208834141300985949214473100800 208834186636669664748988396800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check2 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 2 (witness 2) := by
  apply checks_of_runs _ _ _ _ _ _ 1399 50 210960953277536241258391440000 210962181896057319608570342400 210853230459044303460576960000 210853275794728018995092256000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check3 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 3 (witness 3) := by
  apply checks_of_runs _ _ _ _ _ _ 1399 50 210164561285472099113178240000 210165785432737376535227750400 210057250132238695861268160000 210057295467922411395783456000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check4 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 4 (witness 4) := by
  apply checks_of_runs _ _ _ _ _ _ 1400 50 211990286628900183848462693280 211991521012051675735327445280 211882045445279073523989388800 211882090780962789058504684800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check5 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 5 (witness 5) := by
  apply checks_of_runs _ _ _ _ _ _ 1400 50 211183769752222718698185415680 211184999611663389703486663680 211075934651949824987102092800 211075979987633540521617388800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check6 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 6 (witness 6) := by
  apply checks_of_runs _ _ _ _ _ _ 1401 50 212809364617359167467128380160 212810603558715853827502291200 212700778047509309385499123200 212700823383193024920014419200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check7 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 7 (witness 7) := by
  apply checks_of_runs _ _ _ _ _ _ 1401 50 211992500348328705918641343360 211993734712108447919355408000 211884314799024842345177587200 211884360134708557879692883200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check8 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 8 (witness 8) := by
  apply checks_of_runs _ _ _ _ _ _ 1402 50 213743037825356315816632135680 213744282010699382335136010240 213633941142412649746293235200 213633986478096365280808531200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check9 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 9 (witness 9) := by
  apply checks_of_runs _ _ _ _ _ _ 1402 50 212915998927840060352449565280 212917238482892954057856375840 212807297661300345714401779200 212807342996984061248917075200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check10 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 10 (witness 10) := by
  apply checks_of_runs _ _ _ _ _ _ 1403 50 214462732309344073278599662080 214463980512485076402050716800 214353297649765631762522611200 214353342985449347297037907200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check11 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 11 (witness 11) := by
  apply checks_of_runs _ _ _ _ _ _ 1403 50 213625280139594008938712801280 213626523658202116281906508800 213516235888806900572774899200 213516281224490616107290195200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check12 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 12 (witness 12) := by
  apply checks_of_runs _ _ _ _ _ _ 1404 50 215131953503944301942046960000 215133205451346570024181872000 215022182390511042801643200000 215022227726194758336158496000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check13 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 13 (witness 13) := by
  apply checks_of_runs _ _ _ _ _ _ 1405 50 216459392170759275899677510080 216460651578052688382836600640 216348896675236100523162508800 216348942010919816057677804800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check14 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 14 (witness 14) := by
  apply checks_of_runs _ _ _ _ _ _ 1405 50 215750854906656308103953329920 215752110326401526751215704320 215640746920472978594095603200 215640792256156694128610899200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check15 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 15 (witness 15) := by
  apply checks_of_runs _ _ _ _ _ _ 1406 50 217187363328981990239829368160 217188626791082939001518781600 217076545631341444554449395200 217076590967025160088964691200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check16 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 16 (witness 16) := by
  apply checks_of_runs _ _ _ _ _ _ 1406 50 216319578674715498870278184960 216320837296411778476948070400 216209131531191311539003891200 216209176866875027073519187200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check17 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 17 (witness 17) := by
  apply checks_of_runs _ _ _ _ _ _ 1407 50 217716597166089469432503214080 217717863616285035735850352640 217605441032324496248955379200 217605486368008211783470675200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check18 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 18 (witness 18) := by
  apply checks_of_runs _ _ _ _ _ _ 1408 50 219083685036059431324879073280 219084959149124437645095628800 218971829119078879337275891200 218971874454762594871791187200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check19 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 19 (witness 19) := by
  apply checks_of_runs _ _ _ _ _ _ 1409 50 220421013649539702745062240000 220422295261403971190943264000 220308465593557133170257600000 220308510929240848704772896000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check20 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 20 (witness 20) := by
  apply checks_of_runs _ _ _ _ _ _ 1409 50 219164481387444607033784688000 219165755920648674215586076800 219052643748759960405094080000 219052689084443675939609376000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check21 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 21 (witness 21) := by
  apply checks_of_runs _ _ _ _ _ _ 1410 50 220459082348912244080147261280 220460364150627627922945704480 220346550708712421871319948800 220346596044396137405835244800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check22 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 22 (witness 22) := by
  apply checks_of_runs _ _ _ _ _ _ 1411 50 221540714843656056191320320000 221542002685968635088028800000 221427679288391850137169600000 221427724624075565671684896000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check23 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 23 (witness 23) := by
  apply checks_of_runs _ _ _ _ _ _ 1412 50 222774759524194623205240043520 222776054303928751490952591360 222661038723017743581576076800 222661084058701459116091372800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check24 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 24 (witness 24) := by
  apply checks_of_runs _ _ _ _ _ _ 1413 50 223792333912324554324149157120 223793634382663587355680019200 223678117942587160928713612800 223678163278270876463228908800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check25 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 25 (witness 25) := by
  apply checks_of_runs _ _ _ _ _ _ 1414 50 224777139586410822210847440000 224778445568921191279567536000 224662431453949213467422400000 224662476789632929001937696000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check26 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 26 (witness 26) := by
  apply checks_of_runs _ _ _ _ _ _ 1415 50 225729321927884646111143038080 225730633245473117654507450880 225614123272374095359245196800 225614168608057810893760492800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check27 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 27 (witness 27) := by
  apply checks_of_runs _ _ _ _ _ _ 1416 50 226649021729384811978740874240 226650338206262693755041254400 226533332851562356606761868800 226533378187246072141277164800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check28 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 28 (witness 28) := by
  apply checks_of_runs _ _ _ _ _ _ 1417 50 227341177047219572025376020480 227342497375215595749098096640 227225191891273945240461811200 227225237226957660774977107200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check29 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 29 (witness 29) := by
  apply checks_of_runs _ _ _ _ _ _ 1419 50 230407121202072334830902592000 230408458736600306088912585600 230289513947040177046630080000 230289559282723892581145376000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check30 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 30 (witness 30) := by
  apply checks_of_runs _ _ _ _ _ _ 1420 50 231009236652448149287471909280 231010577550081438332699371680 230891335759272803863624588800 230891381094956519398139884800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check31 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 31 (witness 31) := by
  apply checks_of_runs _ _ _ _ _ _ 1421 50 231575554652286095979979968000 231576898720483196308411200000 231457357620434235283680960000 231457402956117950818196256000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check32 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 32 (witness 32) := by
  apply checks_of_runs _ _ _ _ _ _ 1423 50 234252536350241396020430517120 234253895433461209246366483200 234132936194597177187892108800 234132981530280892722407404800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check33 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 33 (witness 33) := by
  apply checks_of_runs _ _ _ _ _ _ 1425 51 236638364820578142970245350400 236639737256980498130424176640 236517579191192359070333836800 236517624526876074604849132800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check34 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 34 (witness 34) := by
  apply checks_of_runs _ _ _ _ _ _ 1427 51 238936659474617808256943470080 238938044786806822065412957440 238814697923595106256157580800 238814743259278821790672876800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check35 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 35 (witness 35) := by
  apply checks_of_runs _ _ _ _ _ _ 1429 51 240931316722914646550912736000 240932713183529711301836236800 240808392307552622561668800000 240808437643236338096184096000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check36 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 36 (witness 36) := by
  apply checks_of_runs _ _ _ _ _ _ 1432 51 243405778375472074134521192640 243407188691834068927812765600 243281599695433479676492684800 243281645031117195211007980800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check37 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 37 (witness 37) := by
  apply checks_of_runs _ _ _ _ _ _ 1434 51 246642079736921082757938345600 246643508202976782876553005600 246516196255610022359674560000 246516241591293737894189856000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check38 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 38 (witness 38) := by
  apply checks_of_runs _ _ _ _ _ _ 1438 51 252026042351522889079907020800 252027500990905042745185468800 251897383927492021180431244800 251897429263175736714946540800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check39 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 39 (witness 39) := by
  apply checks_of_runs _ _ _ _ _ _ 1443 51 257058958199638624046181204480 257060444997133894852072696320 256927807944451170967904755200 256927853280134886502420051200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check40 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 40 (witness 40) := by
  apply checks_of_runs _ _ _ _ _ _ 1449 51 266445882632005472033611142400 266447422000783486880628710400 266309968424458761892474560000 266310013760142477426989856000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check41 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 41 (witness 41) := by
  apply checks_of_runs _ _ _ _ _ _ 1464 52 288951936236062687552795574400 288953601661073919081562704000 288804561322932489536614080000 288804606658616205071129376000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check42 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 42 (witness 42) := by
  apply checks_of_runs _ _ _ _ _ _ 1479 53 409120215427706105248706340000 409122553907778811714201140000 408911561930182851407851200000 408911607265866566942366496000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check43 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 43 (witness 43) := by
  apply checks_of_runs _ _ _ _ _ _ 1476 52 477458699287824837067909500000 477461420454571586538814044000 477215266865710025393254080000 477215312201393740927769376000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check44 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 44 (witness 44) := by
  apply checks_of_runs _ _ _ _ _ _ 1472 52 511947573439301279078533701120 511950487698461653144032280320 511686593366888643233577868800 511686638702572358768093164800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check45 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 45 (witness 45) := by
  apply checks_of_runs _ _ _ _ _ _ 1469 52 529914753447983378305091110080 529917768254506932122383761120 529644659386422266821868428800 529644704722105982356383724800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check46 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 46 (witness 46) := by
  apply checks_of_runs _ _ _ _ _ _ 1466 52 538967554989856210493084782080 538970620451655391864963799040 538692812307513275770469260800 538692857643196991304984556800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check47 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 47 (witness 47) := by
  apply checks_of_runs _ _ _ _ _ _ 1463 52 543022256609777708508087997920 543025344714221648897110465920 542745466303308318262950796800 542745511638992033797466092800
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check48 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2450 48 (witness 48) := by
  apply checks_of_runs _ _ _ _ _ _ 1460 52 544083525404653286543950800000 544086619380169223072543712000 543806234378943215027302080000 543806279714626930561817376000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipts (i : Fin 49) : BlockChecks terminalBank.shape terminalBank.nodeRows
    terminalBank.poleMoment 2450 (max 1 i.val) (witness i.val) := by
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

theorem positive {h : ℕ} (lo : 2450≤h) (hi : h≤33579) (i : Fin 49) :
    KoalaRect.rectDebit h terminalBank.nodeRows terminalBank.poleMoment (witness i.val).U <
      KoalaRect.rectGain 179818 h terminalBank.shape (max 1 i.val) (witness i.val).U
        (witness i.val).order :=
  strict_of_checks lo (by omega) (by decide) (by decide) (by omega) (receipts i)

end Lower6961.Hi.TerminalReceipts
