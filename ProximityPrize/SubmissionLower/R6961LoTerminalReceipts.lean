import ProximityPrize.SubmissionLower.R6961TerminalArithmetic
import ProximityPrize.SubmissionLower.R6961LoTerminalBank

set_option Elab.async false
set_option maxHeartbeats 9000000
set_option maxRecDepth 18000
namespace Lower6961.Lo.TerminalReceipts
open Lower6961.TerminalArithmetic

def terminalBank : P1_7.Bank := ⟨⟨4500,6285,1329,1126356⟩,2693670660997120,42024370842405⟩

theorem bank_checked : P3_7_1.BankOK terminalBank :=
  P3_7_1.checked terminalBank rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide +kernel) (by decide) Lower6961.Lo.TerminalBank.moment_6285_1329

def witness : ℕ → RectArgs
  | 0 => ⟨![1013720, 112636], ![1762, 1762]⟩
  | 1 => ⟨![1025053, 101303], ![0, 1809]⟩
  | 2 => ⟨![1025389, 100967], ![0, 1803]⟩
  | 3 => ⟨![1025725, 100631], ![0, 1797]⟩
  | 4 => ⟨![1024270, 102086], ![0, 1791]⟩
  | 5 => ⟨![1024612, 101744], ![0, 1785]⟩
  | 6 => ⟨![1025011, 101345], ![0, 1778]⟩
  | 7 => ⟨![1023581, 102775], ![0, 1772]⟩
  | 8 => ⟨![1023929, 102427], ![0, 1766]⟩
  | 9 => ⟨![1024335, 102021], ![0, 1759]⟩
  | 10 => ⟨![1022930, 103426], ![0, 1753]⟩
  | 11 => ⟨![1023343, 103013], ![0, 1746]⟩
  | 12 => ⟨![1023756, 102600], ![0, 1739]⟩
  | 13 => ⟨![1022377, 103979], ![0, 1733]⟩
  | 14 => ⟨![1022797, 103559], ![0, 1726]⟩
  | 15 => ⟨![1023217, 103139], ![0, 1719]⟩
  | 16 => ⟨![1021925, 104431], ![0, 1712]⟩
  | 17 => ⟨![1022352, 104004], ![0, 1705]⟩
  | 18 => ⟨![1021081, 105275], ![0, 1698]⟩
  | 19 => ⟨![1021515, 104841], ![0, 1691]⟩
  | 20 => ⟨![1022011, 104345], ![0, 1683]⟩
  | 21 => ⟨![1020769, 105587], ![0, 1676]⟩
  | 22 => ⟨![1021273, 105083], ![0, 1668]⟩
  | 23 => ⟨![1020053, 106303], ![0, 1661]⟩
  | 24 => ⟨![1020565, 105791], ![0, 1653]⟩
  | 25 => ⟨![1019432, 106924], ![0, 1645]⟩
  | 26 => ⟨![1019952, 106404], ![0, 1637]⟩
  | 27 => ⟨![1018843, 107513], ![0, 1629]⟩
  | 28 => ⟨![1017750, 108606], ![0, 1621]⟩
  | 29 => ⟨![1018286, 108070], ![0, 1613]⟩
  | 30 => ⟨![1017285, 109071], ![0, 1604]⟩
  | 31 => ⟨![1017829, 108527], ![0, 1596]⟩
  | 32 => ⟨![1016854, 109502], ![0, 1587]⟩
  | 33 => ⟨![1015897, 110459], ![0, 1578]⟩
  | 34 => ⟨![1014958, 111398], ![0, 1569]⟩
  | 35 => ⟨![1015597, 110759], ![0, 1560]⟩
  | 36 => ⟨![1014757, 111599], ![0, 1550]⟩
  | 37 => ⟨![1013937, 112419], ![0, 1540]⟩
  | 38 => ⟨![1013137, 113219], ![0, 1530]⟩
  | 39 => ⟨![1012357, 113999], ![0, 1520]⟩
  | 40 => ⟨![1011673, 114683], ![0, 1509]⟩
  | 41 => ⟨![1011011, 115345], ![0, 1498]⟩
  | 42 => ⟨![1008884, 117472], ![0, 1487]⟩
  | 43 => ⟨![1008277, 118079], ![0, 1476]⟩
  | 44 => ⟨![1006391, 119965], ![0, 1463]⟩
  | 45 => ⟨![1005924, 120432], ![0, 1451]⟩
  | 46 => ⟨![1004212, 122144], ![0, 1437]⟩
  | 47 => ⟨![1001133, 125223], ![0, 1423]⟩
  | 48 => ⟨![999637, 126719], ![0, 1408]⟩
  | 49 => ⟨![995509, 130847], ![0, 1392]⟩
  | 50 => ⟨![989057, 137299], ![0, 1373]⟩
  | 51 => ⟨![967057, 159299], ![0, 1350]⟩
  | 52 => ⟨![844968, 281388], ![0, 1282]⟩
  | 53 => ⟨![762228, 364128], ![0, 1156]⟩
  | 54 => ⟨![701859, 424497], ![0, 986]⟩
  | 55 => ⟨![655418, 470938], ![0, 780]⟩
  | 56 => ⟨![618425, 507931], ![0, 544]⟩
  | 57 => ⟨![588086, 538270], ![0, 281]⟩
  | 58 => ⟨![563178, 563178], ![0, 0]⟩
  | _ => ⟨![0, 0], ![0, 0]⟩

private theorem check0 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 1 (witness 0) := by
  apply checks_of_runs _ _ _ _ _ _ 1393 52 443062344100715178107613492960 443064932290931360689376176320 443062249213863883216415846400 443062317375524145582255672000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check1 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 1 (witness 1) := by
  apply checks_of_runs _ _ _ _ _ _ 1385 52 402952942666811042646408469440 402955302707673630281820515520 402952934189259010039717785600 402953002350919272405557611200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check2 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 2 (witness 2) := by
  apply checks_of_runs _ _ _ _ _ _ 1385 52 401748584221676460941596756800 401750937413107279393170254400 401748567718918358787216076800 401748635880578621153055902400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check3 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 3 (witness 3) := by
  apply checks_of_runs _ _ _ _ _ _ 1385 52 400543346659028155795234226880 400545692994651847342457135040 400543325427206029013838950400 400543393588866291379678776000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check4 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 4 (witness 4) := by
  apply checks_of_runs _ _ _ _ _ _ 1386 52 405756175511006177515546625280 405758551495770719460790166880 405756139605553605694352486400 405756207767213868060192312000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check5 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 5 (witness 5) := by
  apply checks_of_runs _ _ _ _ _ _ 1386 52 404532396712095275540918534400 404534765743949204859073874400 404532336054226047990813388800 404532404215886310356653214400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check6 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 6 (witness 6) := by
  apply checks_of_runs _ _ _ _ _ _ 1386 52 403103418566040783310802503680 403105779441892608673132558080 403103418416861395300281446400 403103486578521657666121272000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check7 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 7 (witness 7) := by
  apply checks_of_runs _ _ _ _ _ _ 1387 52 408218906821846895221340759040 408221296796320131424573324800 408218883171590423346572390400 408218951333250685712412216000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check8 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 8 (witness 8) := by
  apply checks_of_runs _ _ _ _ _ _ 1387 52 406975526323804434122719372800 406977909240780645568378848000 406975461379795805450326732800 406975529541456067816166558400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check9 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 9 (witness 9) := by
  apply checks_of_runs _ _ _ _ _ _ 1387 52 405523635180468520580460656640 405526009817608185325963392000 405523615202680189572770918400 405523683364340451938610744000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check10 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 10 (witness 10) := by
  apply checks_of_runs _ _ _ _ _ _ 1388 52 410542475074515502159540881600 410544878266186472740426447680 410542416825046741302275174400 410542484986707003668115000000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check11 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 11 (witness 11) := by
  apply checks_of_runs _ _ _ _ _ _ 1388 52 409068761373099432259629004800 409071156169050723747556362240 409068728359103877853585305600 409068796520764140219425131200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check12 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 12 (witness 12) := by
  apply checks_of_runs _ _ _ _ _ _ 1388 52 407593719914692234217351601600 407596106305485352952964348480 407593716657833404625742950400 407593784819493666991582776000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check13 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 13 (witness 13) := by
  apply checks_of_runs _ _ _ _ _ _ 1389 52 412513650570760328697989676480 412516064961513164980530518400 412513588610162767050101452800 412513656771823029415941278400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check14 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 14 (witness 14) := by
  apply checks_of_runs _ _ _ _ _ _ 1389 52 411016764890358229187985240960 411019170760017815484952108800 411016712789696034918945484800 411016780951356297284785310400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check15 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 15 (witness 15) := by
  apply checks_of_runs _ _ _ _ _ _ 1389 52 409518506000171504902527051840 409520903338950289583886403200 409518468498336055098921676800 409518536659996317464761502400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check16 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 16 (witness 16) := by
  apply checks_of_runs _ _ _ _ _ _ 1390 52 414123020945101499740894126080 414125444464516185416865285120 414122983272643097658027110400 414123051434303360023866936000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check17 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 17 (witness 17) := by
  apply checks_of_runs _ _ _ _ _ _ 1390 52 412602687911997119210687481600 412605102783178218138377882400 412602645208777035741188812800 412602713370437298107028638400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check18 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 18 (witness 18) := by
  apply checks_of_runs _ _ _ _ _ _ 1391 52 417123941765609426048006273280 417126382345679753978482855680 417123893319653859949964390400 417123961481314122315804216000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check19 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 19 (witness 19) := by
  apply checks_of_runs _ _ _ _ _ _ 1391 52 415581534920090518480384462080 415583966734693357945389338880 415581461537586116462013542400 415581529699246378827853368000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check20 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 20 (witness 20) := by
  apply checks_of_runs _ _ _ _ _ _ 1391 52 413816900123721569182299060480 413819321870406402642253351680 413816893105660517062175846400 413816961267320779428015672000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check21 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 21 (witness 21) := by
  apply checks_of_runs _ _ _ _ _ _ 1392 52 418231883494963358146102003200 418234330360334791036561536000 418231835468991118163628748800 418231903630651380529468574400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check22 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 22 (witness 22) := by
  apply checks_of_runs _ _ _ _ _ _ 1392 52 416441707871346242724386142720 416444144531388798993898982400 416441707414199113551290265600 416441775575859375917130091200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check23 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 23 (witness 23) := by
  apply checks_of_runs _ _ _ _ _ _ 1393 52 420771621962532825624705912000 420774083263143282280256288640 420771565611754958839717785600 420771633773415221205557611200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check24 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 24 (witness 24) := by
  apply checks_of_runs _ _ _ _ _ _ 1393 52 418955878590466256814230712000 418958329548243487639669418880 418955850874989544207969382400 418955919036649806573809208000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check25 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 25 (witness 25) := by
  apply checks_of_runs _ _ _ _ _ _ 1394 52 422971114921894299816922003200 422973588701007271186927164000 422971099836789281627624140800 422971167998449543993463966400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check26 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 26 (witness 26) := by
  apply checks_of_runs _ _ _ _ _ _ 1394 52 421129508566011905685586302720 421131971862952306260395810400 421129503560671145422279372800 421129571722331407788119198400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check27 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 27 (witness 27) := by
  apply checks_of_runs _ _ _ _ _ _ 1395 52 425054543002859570009831792640 425057028617051500409426453760 425054528080571108667793305600 425054596242231371033633131200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check28 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 28 (witness 28) := by
  apply checks_of_runs _ _ _ _ _ _ 1396 52 428913614545506124678744793280 428916122101602108916824530880 428913589006363644249402470400 428913657168023906615242296000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check29 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 29 (witness 29) := by
  apply checks_of_runs _ _ _ _ _ _ 1396 52 427022349063998728705289945280 427024845874132028715611897280 427022288998532343573146726400 427022357160192605938986552000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check30 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 30 (witness 30) := by
  apply checks_of_runs _ _ _ _ _ _ 1397 52 430552568249458871313968144640 430555085105555061045171417600 430552556848496633911602278400 430552625010156896277442104000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check31 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 31 (witness 31) := by
  apply checks_of_runs _ _ _ _ _ _ 1397 52 428635038215603788742190124800 428637544184005590271932864000 428634974007308269731762892800 428635042168968532097602718400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check32 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 32 (witness 32) := by
  apply checks_of_runs _ _ _ _ _ _ 1398 52 432070237058319996546862368000 432072762545709357675642093600 432070188249158379281371852800 432070256410818641647211678400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check33 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 33 (witness 33) := by
  apply checks_of_runs _ _ _ _ _ _ 1399 52 435434855474536155784513019520 435437400083505155748877420800 435434811386199120994685644800 435434879547859383360525470400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check34 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 34 (witness 34) := by
  apply checks_of_runs _ _ _ _ _ _ 1400 52 438729297495554011637629160640 438731860832315485938004296960 438729244324546261618106265600 438729312486206523983946091200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check35 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 35 (witness 35) := by
  apply checks_of_runs _ _ _ _ _ _ 1400 52 436488174594609187623568819200 436490725194224861994494668800 436488089453692681034191564800 436488157615352943400031390400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check36 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 36 (witness 36) := by
  apply checks_of_runs _ _ _ _ _ _ 1401 53 439433598854438845856180784000 439436166175599873715344528000 439433553621678691132166860800 439433621783338953498006686400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check37 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 37 (witness 37) := by
  apply checks_of_runs _ _ _ _ _ _ 1402 53 442303632445153838797916755200 442306216066762894603467110400 442303607751141540122120908800 442303675912801802487960734400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check38 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 38 (witness 38) := by
  apply checks_of_runs _ _ _ _ _ _ 1403 53 445098659986577555080746422400 445101259490959043016467136000 445098633524439208651969228800 445098701686099471017809054400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check39 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 39 (witness 39) := by
  apply checks_of_runs _ _ _ _ _ _ 1404 53 447819056744515338290612428800 447821671717343490948840960000 447819003314603872963580620800 447819071476264135329420446400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check40 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 40 (witness 40) := by
  apply checks_of_runs _ _ _ _ _ _ 1405 53 450200687745212362751654543040 450203316231156788288963597760 450200674138265025134829465600 450200742299925287500669291200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check41 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 41 (witness 41) := by
  apply checks_of_runs _ _ _ _ _ _ 1406 53 452502288649128374402179311360 452504930205038582168303569920 452502285225474575524588646400 452502353387134837890428472000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check42 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 42 (witness 42) := by
  apply checks_of_runs _ _ _ _ _ _ 1408 53 459874358515774634241014683200 459877041981783179359622208000 459874330450461713996239564800 459874398612121976362079390400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check43 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 43 (witness 43) := by
  apply checks_of_runs _ _ _ _ _ _ 1409 53 461971812872252900889210435840 461974508278943022925094649600 461971716259515345066316492800 461971784421175607432156318400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check44 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 44 (witness 44) := by
  apply checks_of_runs _ _ _ _ _ _ 1411 53 468470243341868459869465263360 468472975640918990933755576320 468470232452846696863001702400 468470300614506959228841528000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check45 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 45 (witness 45) := by
  apply checks_of_runs _ _ _ _ _ _ 1412 53 470075174249701876054232688000 470077915687392621789020016000 470075093710272312588161740800 470075161871932574954001566400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check46 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 46 (witness 46) := by
  apply checks_of_runs _ _ _ _ _ _ 1414 53 475943984152771530047421581280 475946758907829323022222518400 475943969494657135446905548800 475944037656317397812745374400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check47 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 47 (witness 47) := by
  apply checks_of_runs _ _ _ _ _ _ 1417 53 486441837041576392838028438720 486444671455717101716876312640 486441813553759983806291865600 486441881715420246172131691200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check48 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 48 (witness 48) := by
  apply checks_of_runs _ _ _ _ _ _ 1419 53 491515907965265593617538129920 491518771204819893434472038400 491515874554445453710119628800 491515942716105716075959454400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check49 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 49 (witness 49) := by
  apply checks_of_runs _ _ _ _ _ _ 1423 53 505427052662750662990625203200 505429994965773241289380608000 505426975119294532157493964800 505427043280954794523333790400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check50 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 50 (witness 50) := by
  apply checks_of_runs _ _ _ _ _ _ 1429 54 526905054819470621232428434560 526908119136854959864584141120 526905028506362352895054540800 526905096668022615260894366400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check51 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 51 (witness 51) := by
  apply checks_of_runs _ _ _ _ _ _ 1447 54 597712915213249149072413568000 597716381869119594687225456000 597712831147142250942747340800 597712899308802513308587166400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check52 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 52 (witness 52) := by
  apply checks_of_runs _ _ _ _ _ _ 1450 54 922424674492259415265613198400 922429986017196066519794719680 922424607547955030897041305600 922424675709615293262881131200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check53 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 53 (witness 53) := by
  apply checks_of_runs _ _ _ _ _ _ 1448 54 1076744982292376158954665888480 1076751170526954613075360597440 1076744919725236086726565785600 1076744987886896349092405611200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check54 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 54 (witness 54) := by
  apply checks_of_runs _ _ _ _ _ _ 1446 54 1155829565791227331148106009600 1155836203248621437799391872000 1155829514923094409100710604800 1155829583084754671466550430400
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check55 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 55 (witness 55) := by
  apply checks_of_runs _ _ _ _ _ _ 1444 54 1197427493054533459118036328000 1197434366738610905998936287360 1197427469885204571415748505600 1197427538046864833781588331200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check56 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 56 (witness 56) := by
  apply checks_of_runs _ _ _ _ _ _ 1442 54 1218590646626198759490930551040 1218597640454027390653973318400 1218590618535241937925598310400 1218590686696902200291438136000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check57 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 57 (witness 57) := by
  apply checks_of_runs _ _ _ _ _ _ 1440 54 1228023414157212345455863665120 1228030461493069115026777314240 1228023380356035639903939686400 1228023448517695902269779512000
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

private theorem check58 : BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment
    2368 58 (witness 58) := by
  apply checks_of_runs _ _ _ _ _ _ 1438 54 1230430208336644044460083402240 1230437269357162698695941087200 1230429873907363606519717785600 1230429942069023868885557611200
  · decide +kernel
  · decide
  · decide
  · decide +kernel
  · decide +kernel
  · apply P0_10_5.Row.eq_of_check; decide +kernel
  all_goals decide +kernel

theorem receipts (i : Fin 59) : BlockChecks terminalBank.shape terminalBank.nodeRows
    terminalBank.poleMoment 2368 (max 1 i.val) (witness i.val) := by
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

theorem positive {h : ℕ} (lo : 2368≤h) (hi : h≤2401) (i : Fin 59) :
    KoalaRect.rectDebit h terminalBank.nodeRows terminalBank.poleMoment (witness i.val).U <
      KoalaRect.rectGain 179798 h terminalBank.shape (max 1 i.val) (witness i.val).U
        (witness i.val).order :=
  strict_of_checks lo (by omega) (by decide) (by decide) (by omega) (receipts i)

end Lower6961.Lo.TerminalReceipts
