import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass0

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group0
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top15
private abbrev P := PaidBatch orders 15

private def priceBatch0 : P :=
  ⟨unpack [56676168765, 26192033033, 13089100041, 4398506249, 70052105, 2943260], by decide +kernel⟩
private def priceBatch1 : P :=
  ⟨unpack [2943264, 70050085, 19719461, 2943268, 2943272, 2942252], by decide +kernel⟩
private def priceBatch2 : P :=
  ⟨unpack [2943276, 2942256, 276534789427620808869341490, 2942260, 279889220426130061999794486, 2941240], by decide +kernel⟩
private def priceBatch3 : P :=
  ⟨unpack [2942264, 209464916361150284268628282, 4398502205, 53205309, 19717437, 2941244], by decide +kernel⟩
private def priceBatch4 : P :=
  ⟨unpack [276596587316170958763255102, 211950336074427340048623934, 2941248, 279837857446316074167231810, 214435755787704396902361410, 2940228], by decide +kernel⟩
private def priceBatch5 : P :=
  ⟨unpack [2941252, 209315465066501732198835526, 216921175500981452682357062, 2940232, 2941256, 211716555065651718110635338], by decide +kernel⟩
private def priceBatch6 : P :=
  ⟨unpack [219406595214258509536094538, 19716429, 2940236, 279256117377815325589692750, 214117645064801704022435150, 221892014927535565316090190], by decide +kernel⟩
private def priceBatch7 : P :=
  ⟨unpack [2940240, 208772290400607241958646098, 216518735063951689934234962, 224377434640812622169827666, 2939220, 2940244], by decide +kernel⟩
private def priceBatch8 : P :=
  ⟨unpack [211090254440261077229691222, 218919825063101675846034774, 226862854354089677949823318, 53203289, 2872664, 2939224], by decide +kernel⟩
private def priceBatch9 : P :=
  ⟨unpack [278160853964590559387245914, 213408218479914911426994522, 221320915062251661757834586, 229348274067366734803560794, 2872668, 2939228], by decide +kernel⟩
private def priceBatch10 : P :=
  ⟨unpack [281180617713425325944003934, 215726182519568746698039646, 223722005061401647669634398, 231833693780643790583556446, 2872672, 2939232], by decide +kernel⟩
private def priceBatch11 : P :=
  ⟨unpack [210084073621880066609569122, 218044146559222580895342946, 226123095060551633581434210, 234319113493920847437293922, 2938212, 2939236], by decide +kernel⟩
private def priceBatch12 : P :=
  ⟨unpack [212320115456668669393558886, 220362110598876416166388070, 228524185059701619493234022, 236804533207197903217289574, 2871656, 2938216], by decide +kernel⟩
private def priceBatch13 : P :=
  ⟨unpack [279480339186493074115975530, 214556157291457272177548650, 222680074638530250363691370, 230925275058851605405033834, 59752, 2871660], by decide +kernel⟩
private def priceBatch14 : P :=
  ⟨unpack [2938220, 208710652034133340822755694, 216792199126245874961538414, 224998038678184085634736494, 233326365058001591316833646, 59756], by decide +kernel⟩
private def priceBatch15 : P :=
  ⟨unpack [13156201841, 4398499185, 36425073, 2871664, 2938224, 210865975418687631420873074], by decide +kernel⟩
private def priceBatch16 : P :=
  ⟨unpack [219028240961034477745528178, 227316002717837919832039794, 235727455057151577228633458, 59760, 2871668, 2938228], by decide +kernel⟩
private def priceBatch17 : P :=
  ⟨unpack [213021298803241920945248630, 221264282795823080529517942, 229633966757491755103084918, 58740, 59764, 2871672], by decide +kernel⟩
private def priceBatch18 : P :=
  ⟨unpack [280106527762649919622272378, 215176622187796211543366010, 223500324630611683313507706, 231951930797145589300388218, 58744, 59768], by decide +kernel⟩
private def priceBatch19 : P :=
  ⟨unpack [2870652, 2871676, 209058437789596446712714622, 217331945572350501067741566, 225736366465400286097497470, 234269894836799424571433342], by decide +kernel⟩
private def priceBatch20 : P :=
  ⟨unpack [58748, 59772, 2870656, 2937216, 211134246478547343278658946, 219487268956904791665858946], by decide +kernel⟩
private def priceBatch21 : P :=
  ⟨unpack [227972408300188888881487234, 236587858876453258768736642, 58752, 59776, 2870660, 2937220], by decide +kernel⟩
private def priceBatch22 : P :=
  ⟨unpack [213210055167498239844603270, 221642592341459081190234502, 230208450134977491665476998, 57732, 58756, 59780], by decide +kernel⟩
private def priceBatch23 : P :=
  ⟨unpack [2870664, 2937224, 215285863856449136410547594, 223797915726013371788351882, 232444491969766094449466762, 57736], by decide +kernel⟩
private def priceBatch24 : P :=
  ⟨unpack [58760, 59784, 69977485, 2869644, 2870668, 208907639740998192676524430], by decide +kernel⟩
private def priceBatch25 : P :=
  ⟨unpack [217361672545400032976491918, 225953239110567661312727438, 234680533804554697233456526, 57740, 58764, 59788], by decide +kernel⟩
private def priceBatch26 : P :=
  ⟨unpack [2869648, 2870672, 210905137488976614437736850, 219437481234350929542436242, 228108562495121951910844818, 236916575639343300017446290], by decide +kernel⟩
private def priceBatch27 : P :=
  ⟨unpack [57744, 58768, 59792, 2869652, 276769678967363506585456022, 212902635236955037272691094], by decide +kernel⟩
private def priceBatch28 : P :=
  ⟨unpack [221513289923301826108380566, 230263885879676241435220374, 56724, 57748, 58772, 59796], by decide +kernel⟩
private def priceBatch29 : P :=
  ⟨unpack [2869656, 2936216, 214900132984933459033903514, 223589098612252722674324890, 232419209264230532033337754, 56728], by decide +kernel⟩
private def priceBatch30 : P :=
  ⟨unpack [57752, 58776, 59800, 2869660, 281961703783135057156033950, 216897630732911881868857758], by decide +kernel⟩
private def priceBatch31 : P :=
  ⟨unpack [225664907301203619240269214, 234574532648784821557713310, 56732, 57756, 58780, 59804], by decide +kernel⟩
private def priceBatch32 : P :=
  ⟨unpack [2868640, 2869664, 210194899137492852857949602, 218895128480890303630070178, 227740715990154515806213538, 236729856033339112155830690], by decide +kernel⟩
private def priceBatch33 : P :=
  ⟨unpack [56736, 57760, 58784, 59808, 2868644, 2869668], by decide +kernel⟩
private def priceBatch34 : P :=
  ⟨unpack [212115289699129720115613094, 220892626228868726465024422, 229816524679105412372157862, 55716, 56740, 57764], by decide +kernel⟩
private def priceBatch35 : P :=
  ⟨unpack [58788, 59812, 2868648, 278042004610453138064525738, 214035680260766587373276586, 222890123976847148226236842], by decide +kernel⟩
private def priceBatch36 : P :=
  ⟨unpack [231892333368056308938102186, 55720, 56744, 57768, 58792, 59816], by decide +kernel⟩
private def priceBatch37 : P :=
  ⟨unpack [2868652, 207175294981687237738744238, 215956070822403454630940078, 224887621724825571061191086, 233968142057007205504046510, 55724], by decide +kernel⟩
private def priceBatch38 : P :=
  ⟨unpack [56748, 57772, 58796, 59820, 2868656, 209019782111613469720299954], by decide +kernel⟩
private def priceBatch39 : P :=
  ⟨unpack [217876461384040321888603570, 226885119472803992822403506, 236043950745958102069990834, 55728, 56752, 57776], by decide +kernel⟩
private def priceBatch40 : P :=
  ⟨unpack [58800, 59824, 4465604021, 69975477, 2867636, 2868660], by decide +kernel⟩
private def priceBatch41 : P :=
  ⟨unpack [210864269241539700628179382, 219796851945677189146267062, 228882617220782415657357750, 238119759434908998635935158, 55732, 56756], by decide +kernel⟩
private def priceBatch42 : P :=
  ⟨unpack [57780, 58804, 59828, 2867640, 2868664, 212708756371465932609735098], by decide +kernel⟩
private def priceBatch43 : P :=
  ⟨unpack [221717242507314056403930554, 230880114968760837418570170, 54712, 55736, 56760, 57784], by decide +kernel⟩
private def priceBatch44 : P :=
  ⟨unpack [58808, 59832, 2867644, 278505465045681136800089534, 214553243501392163517548990, 223637633068950923661594046], by decide +kernel⟩
private def priceBatch45 : P :=
  ⟨unpack [232877612716739260253524414, 54716, 55740, 56764, 57788, 58812], by decide +kernel⟩
private def priceBatch46 : P :=
  ⟨unpack [59836, 2867648, 207396037098855871911019970, 216397730631318395499104706, 225558023630587790919257538, 234875110464717682014736834], by decide +kernel⟩
private def priceBatch47 : P :=
  ⟨unpack [54720, 55744, 56768, 57792, 58816, 59840], by decide +kernel⟩
private def priceBatch48 : P :=
  ⟨unpack [2867652, 209165824551702386770167238, 218242217761244626406918598, 227478414192224658176921030, 236872608212696104849691078, 54724], by decide +kernel⟩
private def priceBatch49 : P :=
  ⟨unpack [55748, 56772, 57796, 58820, 59844, 261726127374253206656499146], by decide +kernel⟩
private def priceBatch50 : P :=
  ⟨unpack [2867656, 210935612004548901629380042, 220086704891170858388474314, 229398804753861525434584522, 238870105960674526610903498, 54728], by decide +kernel⟩
private def priceBatch51 : P :=
  ⟨unpack [55752, 56776, 57800, 58824, 59848, 263924070336752265900834254], by decide +kernel⟩
private def priceBatch52 : P :=
  ⟨unpack [2867660, 212705399457395416488527310, 221931192021097089296288206, 231319195315498392692248014, 53708, 54732], by decide +kernel⟩
private def priceBatch53 : P :=
  ⟨unpack [55756, 56780, 57804, 58828, 59852, 266122013299251325145169362], by decide +kernel⟩
private def priceBatch54 : P :=
  ⟨unpack [278186544727846099123683794, 214475186910241931347674578, 223775679151023321277843922, 233239585877135259949911506, 53712, 54736], by decide +kernel⟩
private def priceBatch55 : P :=
  ⟨unpack [55760, 56784, 57808, 58832, 59856, 268319956261750384389504470], by decide +kernel⟩
private def priceBatch56 : P :=
  ⟨unpack [207036206317135189722776022, 216244974363088446206821846, 225620166280949552185657814, 235159976438772127207574998, 53716, 54740], by decide +kernel⟩
private def priceBatch57 : P :=
  ⟨unpack [55764, 56788, 57812, 58836, 59860, 270517899224249443633839578], by decide +kernel⟩
private def priceBatch58 : P :=
  ⟨unpack [208732497847532906686955994, 218014761815934961065969114, 227464653410875784167213530, 237080367000408994465238490, 53720, 54744], by decide +kernel⟩
private def priceBatch59 : P :=
  ⟨unpack [55768, 56792, 57816, 58840, 59864, 48604], by decide +kernel⟩
private def priceBatch60 : P :=
  ⟨unpack [210428789377930624724877790, 219784549268781475925116382, 229309140540802015075027422, 239000757562045861722901982, 53724, 54748], by decide +kernel⟩
private def priceBatch61 : P :=
  ⟨unpack [55772, 56796, 57820, 58844, 59868, 86750689], by decide +kernel⟩
private def priceBatch62 : P :=
  ⟨unpack [262692869268177385427810786, 48608, 212125080908328341689123298, 221554336721627990784263650, 231153627670728247056583138, 52704], by decide +kernel⟩
private def priceBatch63 : P :=
  ⟨unpack [53728, 54752, 55776, 56800, 57824, 58848], by decide +kernel⟩
private def priceBatch64 : P :=
  ⟨unpack [59872, 264795307665511371166693862, 48612, 213821372438726059727045094, 223324124174474505643410918, 232998114800654477964397030], by decide +kernel⟩
private def priceBatch65 : P :=
  ⟨unpack [52708, 53732, 54756, 55780, 56804, 57828], by decide +kernel⟩
private def priceBatch66 : P :=
  ⟨unpack [58852, 59876, 266897746062845356905576938, 48616, 215517663969123776691225066, 225093911627321020502558186], by decide +kernel⟩
private def priceBatch67 : P :=
  ⟨unpack [234842601930580709945952746, 52712, 53736, 54760, 55784, 56808], by decide +kernel⟩
private def priceBatch68 : P :=
  ⟨unpack [57832, 58856, 59880, 269000184460179342644460014, 48620, 217213955499521494729146862], by decide +kernel⟩
private def priceBatch69 : P :=
  ⟨unpack [226863699080167535361705454, 236687089060506940853766638, 52716, 53740, 54764, 55788], by decide +kernel⟩
private def priceBatch70 : P :=
  ⟨unpack [56812, 57836, 58860, 59884, 47600, 48624], by decide +kernel⟩
private def priceBatch71 : P :=
  ⟨unpack [218910247029919211693326834, 228633486533014050220852722, 238531576190433172835322354, 52720, 53744, 54768], by decide +kernel⟩
private def priceBatch72 : P :=
  ⟨unpack [55792, 56816, 57840, 58864, 59888, 47604], by decide +kernel⟩
private def priceBatch73 : P :=
  ⟨unpack [48628, 220606538560316929731248630, 230403273985860565079999990, 51700, 52724, 53748], by decide +kernel⟩
private def priceBatch74 : P :=
  ⟨unpack [54772, 55796, 56820, 57844, 58868, 59892], by decide +kernel⟩
private def priceBatch75 : P :=
  ⟨unpack [262767547281321974240622074, 47608, 48632, 222302830090714646695428602, 232173061438707079939147258, 51704], by decide +kernel⟩
private def priceBatch76 : P :=
  ⟨unpack [52728, 53752, 54776, 55800, 56824, 57848], by decide +kernel⟩
private def priceBatch77 : P :=
  ⟨unpack [58872, 59896, 264776175405212006292895230, 47612, 48636, 223999121621112364733350398], by decide +kernel⟩
private def priceBatch78 : P :=
  ⟨unpack [233942848891553594798294526, 51708, 52732, 53756, 54780, 55804], by decide +kernel⟩
private def priceBatch79 : P :=
  ⟨unpack [56828, 57852, 58876, 59900, 266784803529102038345168386, 47616], by decide +kernel⟩
private def priceBatch80 : P :=
  ⟨unpack [48640, 225695413151510081697530370, 235712636344400109657441794, 51712, 52736, 53760], by decide +kernel⟩
private def priceBatch81 : P :=
  ⟨unpack [54784, 55808, 56832, 57856, 58880, 59904], by decide +kernel⟩
private def priceBatch82 : P :=
  ⟨unpack [268793431652992070397441542, 47620, 48644, 227391704681907799735452166, 237482423797246624516589062, 51716], by decide +kernel⟩
private def priceBatch83 : P :=
  ⟨unpack [52740, 53764, 54788, 55812, 56836, 57860], by decide +kernel⟩
private def priceBatch84 : P :=
  ⟨unpack [58884, 59908, 46600, 47624, 48648, 229087996212305516699632138], by decide +kernel⟩
private def priceBatch85 : P :=
  ⟨unpack [239252211250093139375736330, 51720, 52744, 53768, 54792, 55816], by decide +kernel⟩
private def priceBatch86 : P :=
  ⟨unpack [56840, 57864, 58888, 59912, 46604, 47628], by decide +kernel⟩
private def priceBatch87 : P :=
  ⟨unpack [48652, 230784287742703234737553934, 50700, 51724, 52748, 53772], by decide +kernel⟩
private def priceBatch88 : P :=
  ⟨unpack [54796, 55820, 56844, 57868, 58892, 59916], by decide +kernel⟩
private def priceBatch89 : P :=
  ⟨unpack [46608, 47632, 48656, 232480579273100951701733906, 50704, 51728], by decide +kernel⟩
private def priceBatch90 : P :=
  ⟨unpack [52752, 53776, 54800, 55824, 56848, 57872], by decide +kernel⟩
private def priceBatch91 : P :=
  ⟨unpack [58896, 59920, 46612, 47636, 48660, 234176870803498669605437974], by decide +kernel⟩
private def priceBatch92 : P :=
  ⟨unpack [50708, 51732, 52756, 53780, 54804, 55828], by decide +kernel⟩
private def priceBatch93 : P :=
  ⟨unpack [56852, 57876, 58900, 59924, 46616, 47640], by decide +kernel⟩
private def priceBatch94 : P :=
  ⟨unpack [48664, 235873162333896386569617946, 50712, 51736, 52760, 53784], by decide +kernel⟩
private def priceBatch95 : P :=
  ⟨unpack [54808, 55832, 56856, 57880, 58904, 59928], by decide +kernel⟩
private def priceBatch96 : P :=
  ⟨unpack [46620, 47644, 48668, 237569453864294104607539742, 50716, 51740], by decide +kernel⟩
private def priceBatch97 : P :=
  ⟨unpack [52764, 53788, 54812, 55836, 56860, 57884], by decide +kernel⟩
private def priceBatch98 : P :=
  ⟨unpack [58908, 59932, 46624, 47648, 48672, 239265745394691821571719714], by decide +kernel⟩
private def priceBatch99 : P :=
  ⟨unpack [50720, 51744, 52768, 53792, 54816, 55840], by decide +kernel⟩
private def priceBatch100 : P :=
  ⟨unpack [56864, 57888, 58912, 59936, 46628, 47652], by decide +kernel⟩
private def priceBatch101 : P :=
  ⟨unpack [48676, 49700, 50724, 51748, 52772, 53796], by decide +kernel⟩
private def priceBatch102 : P :=
  ⟨unpack [54820, 55844, 56868, 57892, 58916, 59940], by decide +kernel⟩
private def priceBatch103 : P :=
  ⟨unpack [46632, 47656, 48680, 49704, 50728, 51752], by decide +kernel⟩
private def priceBatch104 : P :=
  ⟨unpack [52776, 53800, 54824, 55848, 56872, 57896], by decide +kernel⟩
private def priceBatch105 : P :=
  ⟨unpack [58920, 59944, 46636, 47660, 48684, 49708], by decide +kernel⟩
private def priceBatch106 : P :=
  ⟨unpack [50732, 51756, 52780, 53804, 54828, 55852], by decide +kernel⟩
private def priceBatch107 : P :=
  ⟨unpack [56876, 57900, 58924, 59948, 46640, 47664], by decide +kernel⟩
private def priceBatch108 : P :=
  ⟨unpack [48688, 49712, 50736, 51760, 52784, 53808], by decide +kernel⟩
private def priceBatch109 : P :=
  ⟨unpack [54832, 55856, 56880, 57904, 58928, 59952], by decide +kernel⟩
private def priceBatch110 : P :=
  ⟨unpack [46644, 47668, 48692, 49716, 50740, 51764], by decide +kernel⟩
private def priceBatch111 : P :=
  ⟨unpack [52788, 53812, 54836, 55860, 56884, 57908], by decide +kernel⟩
private def priceBatch112 : P :=
  ⟨unpack [58932, 59956, 46648, 47672, 48696, 49720], by decide +kernel⟩
private def priceBatch113 : P :=
  ⟨unpack [50744, 51768, 52792, 53816, 54840, 55864], by decide +kernel⟩
private def priceBatch114 : P :=
  ⟨unpack [56888, 57912, 58936, 59960], by decide +kernel⟩
private def batches : List P := [priceBatch0, priceBatch1, priceBatch2, priceBatch3, priceBatch4, priceBatch5, priceBatch6, priceBatch7, priceBatch8, priceBatch9, priceBatch10, priceBatch11, priceBatch12, priceBatch13, priceBatch14, priceBatch15, priceBatch16, priceBatch17, priceBatch18, priceBatch19, priceBatch20, priceBatch21, priceBatch22, priceBatch23, priceBatch24, priceBatch25, priceBatch26, priceBatch27, priceBatch28, priceBatch29, priceBatch30, priceBatch31, priceBatch32, priceBatch33, priceBatch34, priceBatch35, priceBatch36, priceBatch37, priceBatch38, priceBatch39, priceBatch40, priceBatch41, priceBatch42, priceBatch43, priceBatch44, priceBatch45, priceBatch46, priceBatch47, priceBatch48, priceBatch49, priceBatch50, priceBatch51, priceBatch52, priceBatch53, priceBatch54, priceBatch55, priceBatch56, priceBatch57, priceBatch58, priceBatch59, priceBatch60, priceBatch61, priceBatch62, priceBatch63, priceBatch64, priceBatch65, priceBatch66, priceBatch67, priceBatch68, priceBatch69, priceBatch70, priceBatch71, priceBatch72, priceBatch73, priceBatch74, priceBatch75, priceBatch76, priceBatch77, priceBatch78, priceBatch79, priceBatch80, priceBatch81, priceBatch82, priceBatch83, priceBatch84, priceBatch85, priceBatch86, priceBatch87, priceBatch88, priceBatch89, priceBatch90, priceBatch91, priceBatch92, priceBatch93, priceBatch94, priceBatch95, priceBatch96, priceBatch97, priceBatch98, priceBatch99, priceBatch100, priceBatch101, priceBatch102, priceBatch103, priceBatch104, priceBatch105, priceBatch106, priceBatch107, priceBatch108, priceBatch109, priceBatch110, priceBatch111, priceBatch112, priceBatch113, priceBatch114]
private theorem i45 : checks (tilesOf batches) 142 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 142 53 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=15)
    (hb : a.b≤142) (hj : a.j≤58) :
    Covered orders a ∨ Low6966Gate.Gated ((0 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i45 (i53)) a ha ht hb hj
end Top15

end Low6966Allocation.Group0
