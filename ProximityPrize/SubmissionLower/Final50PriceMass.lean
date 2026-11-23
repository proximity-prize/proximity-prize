import ProximityPrize.SubmissionLower.Final50PriceCaps
import ProximityPrize.SubmissionLower.Final50PriceReceipt

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
set_option linter.defProp false

namespace Final50PriceMass
open Final50PriceCaps (Band start thresholds order)
open Final50Price (layerNeed)
open Final50PriceLayer (availableMass)
open Final50PriceReceipt (Prefix makePrefix emptyPrefix checks paid)
open K1_13 (Shape)
open K1_13_8 (zeroShape)
open K1_13_8_2 (Threshold)

private def prefix_1_3 := makePrefix 1 3 [
  (1, 406784167900), (7, 2802234295898), (12, 4740005313959), (14, 5500464954418),
  (21, 8097241733583), (27, 10244213165881), (28, 10595085671051), (32, 11978966526952),
  (35, 12996488967471), (37, 13665236045035), (41, 14979943747666), (42, 15303914876236),
  (47, 16895888601464), (49, 17519797586832), (50, 17829019945420), (51, 18136430168795),
  (52, 18442035208545), (53, 18745842002439), (54, 19047857477634), (55, 19348088547454)]
private def prefix_2_3 := makePrefix 2 3 [
  (8, 3189620679212), (13, 5110396157981), (18, 6976529923482), (21, 8070431119335),
  (27, 10201307048886), (29, 10894980286737), (36, 13258720397232), (37, 13588366553051),
  (42, 15207016320090), (44, 15840824144420), (46, 16466928178932), (48, 17085392943192),
  (49, 17391780678962), (50, 17696282656250), (51, 17998906854750), (52, 18299661237000),
  (53, 18598553745231), (54, 18895592304540), (55, 19190784819740)]
private def prefix_2_4 := makePrefix 2 4 [
  (11, 4304968480160), (16, 6147714193778), (23, 8612364335756), (31, 11270104078806),
  (38, 13461753832634), (39, 13764933543634), (42, 14659894833234), (44, 15244518946796),
  (45, 15533265224864), (48, 16385396929616), (49, 16664781571364), (50, 16941858050582),
  (51, 17216639192470), (52, 17489137784502), (53, 17759366579862), (54, 18027338294022),
  (55, 18293065604750), (56, 18556561155544), (57, 18817837552212), (58, 19076907362880),
  (59, 19333783121424), (60, 19588477324052)]
private def prefix_2_5 := makePrefix 2 5 [
  (28, 10041766029535), (32, 11268842645056), (40, 13580319888561), (47, 15453278628092),
  (48, 15709855592464), (51, 16463518109079), (54, 17193469075143), (56, 17667176336760),
  (57, 17900206960224), (58, 18130713211985), (59, 18358713237292), (60, 18584225120910),
  (61, 18807266880435), (62, 19027856472931), (63, 19246011791687), (64, 19461750665969),
  (65, 19675090861219), (66, 19886050082250)]
private def prefix_2_6 := makePrefix 2 6 [
  (16, 5973033758156), (41, 13363863064666), (44, 14108719861995), (49, 15288354322332),
  (50, 15515243736970), (51, 15739180107745), (52, 15960188712065), (56, 16815447493922),
  (57, 17022192906542), (59, 17427373656031), (60, 17625858035239), (61, 17821637610149),
  (62, 18014736648519), (64, 18392989678768), (65, 18578191697936), (66, 18760809234926),
  (67, 18940866048621), (68, 19118385795805), (69, 19293392031055), (70, 19465908206633),
  (71, 19635957672378), (72, 19803563675598), (73, 19968749360962), (74, 20131537770392)]
private def prefix_3_7 := makePrefix 3 7 [
  (21, 7464511923332), (44, 13485056606072), (63, 17073628995194), (71, 18271515053300),
  (72, 18409550143796), (74, 18678157174562), (76, 18937013837898), (79, 19307536852454),
  (81, 19543052753812), (82, 19657447694002), (83, 19769638791534), (84, 19879654443236),
  (85, 19987522861476), (86, 20093272080751), (87, 20196929951002), (88, 20298524140798),
  (89, 20398082137462), (90, 20495631246850)]
private def prefix_3_8 := makePrefix 3 8 [
  (112, 20170776390249), (122, 20508292555657), (124, 20562972496999), (126, 20613823188077),
  (128, 20661026761728), (129, 20683316609516), (130, 20704761009344), (131, 20725381505270),
  (132, 20745199370170), (133, 20764235602091), (134, 20782510927443), (135, 20800045800771)]
private def prefix_4_6 := makePrefix 4 6 [
  (20, 7261453319955), (45, 14166489194055), (55, 16352644172370), (56, 16555077612150),
  (59, 17145497957877), (61, 17525315236275), (62, 17711165342649), (65, 18252799068660),
  (66, 18428125483350), (67, 18600886145919), (68, 18771106839471), (69, 18938813204817),
  (70, 19104030740655), (71, 19266784803750), (72, 19427100609114), (73, 19585003230186),
  (74, 19740517599012), (75, 19893668506425), (76, 20044480602225), (77, 20192978395359)]
private def prefix_7_7 := makePrefix 7 7 [
  (63, 16503531333586), (80, 18650466043892), (87, 19341973528666), (88, 19432648213118),
  (92, 19776255791976), (94, 19937008185735), (95, 20014720536660), (96, 20090694016688),
  (97, 20164956071864), (98, 20237533895560), (99, 20308454423480), (100, 20377744337378),
  (101, 20445430066082), (102, 20511537786199), (103, 20576093420154), (104, 20639122642872)]
private def prefix_10_7 := makePrefix 10 7 [
  (91, 19019630296686), (105, 19924280461962), (108, 20080315587441), (111, 20224562833952),
  (114, 20357678133226), (115, 20399686134916), (116, 20440550590296), (117, 20480294076058),
  (118, 20518938888877), (119, 20556507047098), (120, 20593020292146), (121, 20628500087675),
  (122, 20662967626067), (123, 20696443825043), (124, 20728949331621), (125, 20760504523796)]
private def prefix_12_6 := makePrefix 12 6 [
  (49, 14231786780232), (78, 18659227730429), (83, 19213570159051), (86, 19521416200739),
  (88, 19716818077198), (90, 19904622155616), (91, 19995744695381), (92, 20085050849821),
  (93, 20172567740995), (94, 20258322221625), (95, 20342340876428), (96, 20424650023448),
  (97, 20505275715388)]
private def prefix_14_6 := makePrefix 14 6 [
  (63, 16340174244996), (81, 18556636777740), (89, 19313778276342), (94, 19726297034427),
  (95, 19803602382940), (97, 19953235925744), (99, 20096412675537), (100, 20165645929825),
  (101, 20233343814275), (102, 20299531999829), (103, 20364235869786), (104, 20427480521422),
  (105, 20489290767610), (106, 20549691138440), (107, 20608705882839), (108, 20666358970191)]
private def prefix_17_6 := makePrefix 17 6 [
  (110, 19826794758254), (123, 20323216631812), (130, 20522823751482), (133, 20596138932446),
  (135, 20641299424164), (136, 20662816234024), (138, 20703806090738), (140, 20742178703596),
  (141, 20760422994286), (142, 20778059806286), (143, 20795104224180), (144, 20811571083600)]

private def bandPrefix (k : Band) : Prefix (start k).b (start k).j :=
  match k with
  | .empty => emptyPrefix
  | .one3 => prefix_1_3
  | .one3wide => prefix_2_3
  | .one4 => prefix_2_4
  | .one5 => prefix_2_5
  | .one6 => prefix_2_6
  | .one7 => prefix_3_7
  | .two6thin => prefix_2_6
  | .two6thinwide => prefix_4_6
  | .two6wide => prefix_12_6
  | .two6wider => prefix_14_6
  | .two6last => prefix_17_6
  | .two7 => prefix_3_7
  | .two7wide => prefix_7_7
  | .two7last => prefix_10_7
  | .one8 => prefix_3_8
  | .two8 => prefix_3_8

private theorem zero_start (k : Band) : (start k).j = 0 → (start k).b = 0 := by
  cases k <;> decide

private abbrev Good (k : Band) (q : Threshold) :=
  0 < q.j ∧ availableMass (start k) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed

private theorem m (k : Band) (b j l : Nat) (values : List Nat)
    (h : checks (start k) (bandPrefix k) b j l values = true := by decide +kernel) :
    Good k ⟨b,j,l+1⟩ :=
  paid (start k) (bandPrefix k) b j l values (zero_start k) h

private theorem reuse {k k' : Band} {q : Threshold}
    (hb : (start k).b = (start k').b) (hj : (start k).j = (start k').j)
    (h : Good k q) : Good k' q := by
  simp only [Good, Final50PriceLayer.availableMass, K1_13_8.availableMass, hb, hj] at h ⊢
  exact h

private def c0 := m .empty 3 9 4 [13162283972232, 4664214325320, 950638101000, 41055630116]
private def c1 := m .empty 4 12 16 [11502834761168, 2440957634000, 119049499366]
private def c2 := m .empty 5 13 19 [10956594882620, 1895768111548, 45397232414]
private def c3 := m .empty 5 15 23 [10062462797192, 1144379434952, 2862164571]
private def c4 := m .empty 7 19 29 [8423760436644, 351695919772]
private def c5 := m .empty 7 21 31 [7766435870108, 182695620452]
private def c6 := m .empty 9 26 35 [6351666616976, 21548405975]
private def c7 := m .empty 10 8 3 [13108615439376, 4807001444880, 1193038430224, 120012402192, 290015932]
private def c8 := m .empty 10 28 36 [5890479083280, 6400499360]
private def c9 := m .empty 10 30 37 [5502750935684, 1223255306]
private def c10 := m .empty 11 8 4 [13018810760152, 4690713864920, 1139255925208, 111696185560, 261959991]
private def c11 := m .empty 11 31 38 [5307668670608, 378953452]
private def c12 := m .empty 12 34 39 [4822953964396]
private def c13 := m .empty 12 36 40 [4553230993758]
private def c14 := m .empty 14 40 41 [4070774019454]
private def c15 := m .empty 15 44 42 [3686120718746]
private def c16 := m .empty 17 7 1 [12993069124480, 4723746444608, 1227646986496, 166143657664, 4183187020]
private def c17 := m .empty 17 11 18 [11051346456628, 2263863342388, 153012379700, 15772144]
private def c18 := m .empty 17 13 22 [10188764038028, 1461455280652, 28730055650]
private def c19 := m .empty 17 49 43 [3287586454507]
private def c20 := m .empty 19 55 44 [2907784576405]
private def c21 := m .empty 23 6 5 [12911515346984, 4513377543080, 979251201858, 35066811233]
private def c22 := m .empty 23 9 15 [11481133702872, 2774574231960, 319441667160, 4566844138]
private def c23 := m .empty 25 4 1 [13717887854864, 5489103090192, 1128815389209, 3487974072]
private def c24 := m .empty 26 6 8 [12604805184260, 4001972123972, 602205273188, 359753742]
private def c25 := m .empty 30 8 14 [11312521854896, 2481249845680, 146504206191]
private def c26 := m .empty 33 3 8 [13261134125980, 3971265958900, 90735338189]
private def c27 := m .empty 37 26 37 [5650040261952, 12421504891]
private def c28 := m .empty 40 5 18 [11570155337112, 1871072483243, 17324900]
private def c29 := m .empty 43 36 41 [4142932396569]
private def c30 := m .empty 43 43 42 [3513647946966]
private def c31 := m .empty 44 12 26 [8759469471888, 575701193896]
private def c32 := m .empty 50 4 22 [10818421469264, 759045721064]
private def c33 := m .empty 51 13 30 [8013243311684, 282437719616]
private def c34 := m .empty 51 39 42 [3759114915248]
private def c35 := m .empty 51 45 43 [3297860370891]
private def c36 := m .empty 52 18 33 [6762830696988, 108674146028]
private def c37 := m .empty 52 24 36 [5601129329952, 18257410584]
private def c38 := m .empty 53 51 44 [2918228306280]
private def c39 := m .empty 54 33 39 [4307978722828, 1822157]
private def c40 := m .empty 56 33 40 [4276472346644, 1690051]
private def c41 := m .empty 56 35 41 [4068236006708]
private def c42 := m .empty 57 15 32 [7172555333944, 116008334930]
private def c43 := m .empty 57 31 40 [4486688242088, 126203692]
private def c44 := m .empty 58 30 39 [4588546683716, 373046954]
private def c45 := m .empty 59 30 40 [4569500761800, 355334280]
private def c46 := m .empty 60 18 34 [6404517783036, 51384973929]
private def c47 := m .empty 61 50 44 [2918570610648]
private def c48 := m .empty 62 21 35 [5787282280728, 22330921577]
private def c49 := m .empty 64 19 35 [6049936575480, 25160770821]
private def c50 := m .empty 65 33 41 [4134693653816, 1095574]
private def c51 := m .empty 65 43 43 [3309623331842]
private def c52 := m .empty 66 49 44 [2937758522851]
private def c53 := m .empty 68 6 30 [8318365501620, 22298776518]
private def c54 := m .empty 69 28 39 [4604839382208, 776687389]
private def c55 := m .empty 69 42 43 [3339565299928]
private def c56 := m .empty 71 37 42 [3689721917685]
private def c57 := m .empty 73 48 44 [2940973869878]
private def c58 := m .empty 77 56 45 [2537326498359]
private def c59 := m .empty 80 36 42 [3653221167666]
private def c60 := m .empty 81 47 44 [2933861850970]
private def c61 := m .empty 83 41 43 [3266271031956]
private def c62 := m .empty 84 55 45 [2539593509005]
private def c63 := m .empty 86 35 42 [3648141221730]
private def c64 := m .empty 86 46 44 [2947459622113]
private def c65 := m .empty 89 40 43 [3266870256379]
private def c66 := m .empty 90 39 43 [3319351497245]
private def c67 := m .empty 91 33 42 [3725186474633]
private def c68 := m .empty 91 54 45 [2540150820000]
private def c69 := m .empty 92 31 41 [3862631887091]
private def c70 := m .empty 93 30 41 [3923368491440]
private def c71 := m .empty 93 45 44 [2942249965965]
private def c72 := m .empty 96 9 35 [5793236144582]
private def c73 := m .empty 97 32 42 [3702032151389]
private def c74 := m .empty 97 38 43 [3301364984218]
private def c75 := m .empty 98 24 40 [4301482455343]
private def c76 := m .empty 98 53 45 [2538798547496]
private def c77 := m .empty 99 44 44 [2942163978002]
private def c78 := m .empty 100 17 38 [4843773644608]
private def c79 := m .empty 101 12 38 [5258958809652]
private def c80 := m .empty 101 27 41 [3994288825009]
private def c81 := m .empty 102 26 41 [4047513306737]
private def c82 := m .empty 103 30 42 [3738795734126]
private def c83 := m .empty 104 37 43 [3276392161969]
private def c84 := m .empty 105 43 44 [2938669486162]
private def c85 := m .empty 105 52 45 [2535312893643]
private def c86 := m .empty 109 25 41 [3962270392258]
private def c87 := m .empty 110 42 44 [2941000289340]
private def c88 := m .empty 111 51 45 [2536033167864]
private def c89 := m .empty 113 35 43 [3272895503051]
private def c90 := m .empty 116 33 43 [3340597498107]
private def c91 := m .empty 116 41 44 [2929759174118]
private def c92 := m .empty 117 21 40 [4039229771238]
private def c93 := m .empty 117 50 45 [2534622614832]
private def c94 := m .empty 119 40 44 [2945856526765]
private def c95 := m .empty 121 22 41 [3882210534857]
private def c96 := m .empty 122 49 45 [2537955210403]
private def c97 := m .empty 124 39 44 [2937965584728]
private def c98 := m .empty 127 31 43 [3278857441293]
private def c99 := m .empty 127 48 45 [2539202539342]
private def c100 := m .empty 129 38 44 [2926571935486]
private def c101 := m .empty 132 23 42 [3592589920913]
private def c102 := m .empty 132 47 45 [2538162544469]
private def c103 := m .empty 133 6 35 [4488092061005]
private def c104 := m .empty 133 18 41 [3829126166937]
private def c105 := m .empty 133 21 42 [3673917706255]
private def c106 := m .empty 133 28 43 [3328728319428]
private def c107 := m .empty 133 37 44 [2923572454175]
private def c108 := m .empty 134 7 40 [4399438149636]
private def c109 := m .empty 134 14 41 [4016267755704]
private def c110 := m .empty 135 3 39 [4591789398629]
private def c111 := m .empty 137 46 45 [2534728266860]
private def c112 := m .one3 2 6 7 [12610301800980, 4388515765140, 858165333780, 32141819590]
private def c113 := m .one3 3 9 12 [10652111575280, 2147171612912, 88131256382]
private def c114 := m .one3 4 12 27 [8385841404080, 796997901680, 387059280]
private def c115 := m .one3 5 15 37 [6798316071180, 263161211734]
private def c116 := m .one3 6 18 41 [5767114929620, 77472928618]
private def c117 := m .one3 10 28 47 [3719518800992]
private def c118 := m .one3 12 34 49 [3043621920204]
private def c119 := m .one3 12 36 50 [2861780481878]
private def c120 := m .one3 13 38 51 [2691082414273]
private def c121 := m .one3 15 43 52 [2361820302744]
private def c122 := m .one3 17 50 53 [2015625546265]
private def c123 := m .one3 23 5 1 [11781244204928, 3153961755520, 435042520960, 6649223548]
private def c124 := m .one3 23 6 14 [10465071117000, 2377529355912, 237011804232, 1837211429]
private def c125 := m .one3 40 13 28 [6467137835712, 223677873856, 299]
private def c126 := m .one3 58 34 51 [2640765757506]
private def c127 := m .one3 58 41 52 [2240190557572]
private def c128 := m .one3 58 48 53 [1934815346651]
private def c129 := m .one3 60 9 28 [6386591290592, 73477412271]
private def c130 := m .one3 67 6 32 [6364824821344, 16662613747]
private def c131 := m .one3 67 37 52 [2385220037722]
private def c132 := m .one3 67 44 53 [2048165091246]
private def c133 := m .one3 67 51 54 [1785451386348]
private def c134 := m .one3 68 4 21 [7103362967741, 13226055557]
private def c135 := m .one3 68 33 51 [2623844860592]
private def c136 := m .one3 68 43 53 [2083919629727]
private def c137 := m .one3 69 9 35 [5627283614305, 7359457472]
private def c138 := m .one3 70 28 49 [2988524313976]
private def c139 := m .one3 75 25 49 [3161860344688, 16787647]
private def c140 := m .one3 75 32 51 [2626248754248]
private def c141 := m .one3 97 48 54 [1766140703876]
private def c142 := m .one3 100 12 47 [3736476464893]
private def c143 := m .one3 100 28 51 [2614865669255]
private def c144 := m .one3 100 35 52 [2255180611801]
private def c145 := m .one3 100 42 53 [1962441588940]
private def c146 := m .one3 100 47 54 [1784215427010]
private def c147 := m .one3 102 3 42 [4506322173514]
private def c148 := m .one3 104 41 53 [1977013448916]
private def c149 := m .one3 106 10 47 [3715291848313]
private def c150 := m .one3 106 16 49 [3271543028897]
private def c151 := m .one3 106 40 53 [2001859325907]
private def c152 := m .one3 106 46 54 [1789402486596]
private def c153 := m .one3 109 23 50 [2790864646486]
private def c154 := m .one3 109 25 51 [2667031840622]
private def c155 := m .one3 110 31 52 [2351851672810]
private def c156 := m .one3 110 37 53 [2088866568478]
private def c157 := m .one3 111 30 52 [2387226334030]
private def c158 := m .one3 111 45 54 [1797790991397]
private def c159 := m .one3 121 44 54 [1781982478901]
private def c160 := m .one3 125 43 54 [1791964847936]
private def c161 := m .one3 130 42 54 [1795892416131]
private def c162 := m .one3 132 12 50 [2954791981287]
private def c163 := m .one3 132 19 51 [2634275807206]
private def c164 := m .one3 132 36 53 [1978619505871]
private def c165 := m .one3 133 6 49 [3229670811795]
private def c166 := m .one3 133 26 52 [2330235678545]
private def c167 := m .one3 133 53 55 [1498007135246]
private def c168 := m .one3 134 18 51 [2646970658447]
private def c169 := m .one3 134 25 52 [2356786204873]
private def c170 := m .one3 134 33 53 [2061119070100]
private def c171 := m .one3 135 41 54 [1798241917281]
private def c172 := m .one3 136 32 53 [2078318808989]
private def c173 := m .one3wide 2 6 8 [12422434548492, 4251715434252, 815511296268, 29554035381]
private def c174 := m .one3wide 3 9 13 [10478782279320, 2075027195544, 82917051403]
private def c175 := m .one3wide 4 12 29 [8152546065832, 754464793960, 306022308]
private def c176 := m .one3wide 7 21 42 [4953318348064, 16802389574]
private def c177 := m .one3wide 10 28 44 [3746236774436]
private def c178 := m .one3wide 10 30 49 [3376146258203]
private def c179 := m .one3wide 11 32 50 [3146120193503]
private def c180 := m .one3wide 12 36 51 [2788351721079]
private def c181 := m .one3wide 14 40 52 [2491212060663]
private def c182 := m .one3wide 15 45 53 [2201918370505]
private def c183 := m .one3wide 17 51 54 [1925414740107]
private def c184 := m .one3wide 21 5 18 [10642940054920, 2821562421896, 390780688264, 8456080532]
private def c185 := m .one3wide 42 12 36 [6143902097228, 213335233152]
private def c186 := m .one3wide 60 37 52 [2381389365592]
private def c187 := m .one3wide 63 4 21 [7353111465640, 41187156392]
private def c188 := m .one3wide 66 28 49 [2967908718904]
private def c189 := m .one3wide 67 36 52 [2387459610468]
private def c190 := m .one3wide 67 42 53 [2087444920137]
private def c191 := m .one3wide 67 50 54 [1781075901871]
private def c192 := m .one3wide 68 33 51 [2568194477372]
private def c193 := m .one3wide 68 47 54 [1876425711641]
private def c194 := m .one3wide 69 21 48 [3560512372256, 663118061]
private def c195 := m .one3wide 69 28 50 [2911260934908]
private def c196 := m .one3wide 69 35 52 [2426850314083]
private def c197 := m .one3wide 69 46 54 [1907407206240]
private def c198 := m .one3wide 70 9 37 [5351624334856, 2040493885]
private def c199 := m .one3wide 72 39 53 [2190581673924]
private def c200 := m .one3wide 88 10 46 [4172728911937]
private def c201 := m .one3wide 90 53 55 [1602596627035]
private def c202 := m .one3wide 93 44 54 [1870039587323]
private def c203 := m .one3wide 93 51 55 [1645351363962]
private def c204 := m .one3wide 95 19 49 [3198029867188]
private def c205 := m .one3wide 95 43 54 [1894345440089]
private def c206 := m .one3wide 98 18 49 [3206607013299]
private def c207 := m .one3wide 99 28 52 [2539972269861]
private def c208 := m .one3wide 99 35 53 [2192503426342]
private def c209 := m .one3wide 99 41 54 [1943498457692]
private def c210 := m .one3wide 100 15 49 [3363704788382]
private def c211 := m .one3wide 102 3 27 [4799983755146]
private def c212 := m .one3wide 102 50 55 [1640270348773]
private def c213 := m .one3wide 103 6 46 [3986488165225]
private def c214 := m .one3wide 106 19 50 [2975003788902]
private def c215 := m .one3wide 106 49 55 [1652196964881]
private def c216 := m .one3wide 107 40 54 [1935019022594]
private def c217 := m .one3wide 108 26 52 [2538566625465]
private def c218 := m .one3wide 109 23 51 [2693403729762]
private def c219 := m .one3wide 110 34 53 [2152542359932]
private def c220 := m .one3wide 110 39 54 [1952371006542]
private def c221 := m .one3wide 112 48 55 [1655908822640]
private def c222 := m .one3wide 118 33 53 [2129074858904]
private def c223 := m .one3wide 118 38 54 [1938529022846]
private def c224 := m .one3wide 119 47 55 [1654431469605]
private def c225 := m .one3wide 125 46 55 [1655551312291]
private def c226 := m .one3wide 127 9 48 [3128695240017]
private def c227 := m .one3wide 127 28 53 [2234472876386]
private def c228 := m .one3wide 130 37 54 [1895618065811]
private def c229 := m .one3wide 131 15 50 [2748062952948]
private def c230 := m .one3wide 131 22 52 [2432066831900]
private def c231 := m .one3wide 131 45 55 [1655204465348]
private def c232 := m .one3wide 132 12 51 [2837651774784]
private def c233 := m .one3wide 132 35 54 [1943221334334]
private def c234 := m .one4 2 6 16 [10920213775692, 3054940436108, 349357572044, 1008453560]
private def c235 := m .one4 3 7 23 [9746558395124, 2166722856564, 128485125885]
private def c236 := m .one4 3 9 31 [8255210647332, 1145020912420, 10216098653]
private def c237 := m .one4 4 12 39 [6606419217120, 391185252272]
private def c238 := m .one4 5 14 42 [5816635186896, 180124447614]
private def c239 := m .one4 5 15 44 [5444549465540, 116667217981]
private def c240 := m .one4 6 16 45 [5129233336096, 73839684984]
private def c241 := m .one4 7 19 48 [4347996661392, 14368795594]
private def c242 := m .one4 7 21 49 [3966085642120, 3357417758]
private def c243 := m .one4 8 22 50 [3759422515668, 1215114290]
private def c244 := m .one4 8 23 51 [3580411502160, 326272144]
private def c245 := m .one4 9 26 52 [3174394266552]
private def c246 := m .one4 9 27 53 [3036580145344]
private def c247 := m .one4 10 29 54 [2810241796619]
private def c248 := m .one4 11 33 55 [2466912521922]
private def c249 := m .one4 13 37 56 [2185561354096]
private def c250 := m .one4 14 40 57 [2005131214492]
private def c251 := m .one4 15 45 58 [1769900934518]
private def c252 := m .one4 21 5 11 [10471412172816, 2437354920528, 258311974032, 2795895384]
private def c253 := m .one4 61 4 38 [6069046667124, 51153324522]
private def c254 := m .one4 66 28 54 [2433294270410]
private def c255 := m .one4 66 40 58 [1766043976006]
private def c256 := m .one4 67 33 56 [2100189284086]
private def c257 := m .one4 67 51 59 [1414370693232]
private def c258 := m .one4 68 50 59 [1436708629707]
private def c259 := m .one4 69 18 52 [3237588420784, 808731408]
private def c260 := m .one4 69 25 54 [2603538896980, 51654]
private def c261 := m .one4 69 32 56 [2137377172710]
private def c262 := m .one4 69 39 57 [1810292874952]
private def c263 := m .one4 72 36 57 [1914942423044]
private def c264 := m .one4 75 11 50 [3876740233645, 17422405]
private def c265 := m .one4 89 6 50 [3894634061946]
private def c266 := m .one4 98 44 59 [1501626040120]
private def c267 := m .one4 99 9 52 [3300470489115]
private def c268 := m .one4 99 28 56 [2114107572097]
private def c269 := m .one4 99 35 57 [1812408573834]
private def c270 := m .one4 100 15 53 [2862723943612]
private def c271 := m .one4 102 3 38 [4101658850039]
private def c272 := m .one4 105 13 53 [2888137042904]
private def c273 := m .one4 106 18 55 [2545804201596]
private def c274 := m .one4 107 43 59 [1496388149082]
private def c275 := m .one4 108 25 56 [2167228564678]
private def c276 := m .one4 109 24 56 [2200949347805]
private def c277 := m .one4 109 38 58 [1645771987376]
private def c278 := m .one4 110 29 57 [1966277289296]
private def c279 := m .one4 111 28 57 [1997122029767]
private def c280 := m .one4 111 34 58 [1762047072307]
private def c281 := m .one4 114 52 60 [1257207500922]
private def c282 := m .one4 116 42 59 [1489150148466]
private def c283 := m .one4 122 51 60 [1256242718157]
private def c284 := m .one4 124 32 58 [1749819095588]
private def c285 := m .one4 124 41 59 [1483576552410]
private def c286 := m .one4 129 39 59 [1512818295819]
private def c287 := m .one4 129 50 60 [1256938613086]
private def c288 := m .one4 131 9 54 [2592856979508]
private def c289 := m .one4 131 16 56 [2274591642429]
private def c290 := m .one4 133 30 58 [1752367974554]
private def c291 := m .one5 2 6 28 [8812230754960, 1852324982096, 88876376616]
private def c292 := m .one5 3 9 40 [6563988168232, 598108117800, 184681099]
private def c293 := m .one5 4 12 47 [5158053383788, 171296849096]
private def c294 := m .one5 5 15 51 [4222404748592, 39590954109]
private def c295 := m .one5 6 18 54 [3529023075100, 5278270391]
private def c296 := m .one5 7 21 56 [3023606205952, 142224992]
private def c297 := m .one5 8 24 58 [2621008689047]
private def c298 := m .one5 9 26 59 [2406618926870]
private def c299 := m .one5 10 28 60 [2219051169510]
private def c300 := m .one5 11 31 61 [1995362279916]
private def c301 := m .one5 12 34 62 [1806525466436]
private def c302 := m .one5 13 39 63 [1567703265219]
private def c303 := m .one5 15 44 64 [1375187822934]
private def c304 := m .one5 19 5 32 [7903268771392, 1454506300864, 81688360256, 3287787]
private def c305 := m .one5 57 4 48 [5046782285928, 82502110848]
private def c306 := m .one5 66 27 61 [1917314369250]
private def c307 := m .one5 67 37 63 [1462719569068]
private def c308 := m .one5 68 15 57 [2856430919600, 1160779595]
private def c309 := m .one5 68 22 60 [2216200247232, 354058]
private def c310 := m .one5 68 33 62 [1619929176645]
private def c311 := m .one5 68 36 63 [1491593646485]
private def c312 := m .one5 68 43 64 [1270698031602]
private def c313 := m .one5 68 50 65 [1098959184726]
private def c314 := m .one5 69 18 58 [2554014112084, 241972777]
private def c315 := m .one5 69 25 61 [2002511055600]
private def c316 := m .one5 69 32 62 [1653988120423]
private def c317 := m .one5 71 33 63 [1584148058232]
private def c318 := m .one5 71 47 65 [1153784348893]
private def c319 := m .one5 92 21 61 [2030540593462]
private def c320 := m .one5 92 31 63 [1563775886439]
private def c321 := m .one5 99 9 58 [2693310915237]
private def c322 := m .one5 99 18 60 [2136893028343]
private def c323 := m .one5 101 27 62 [1682432663038]
private def c324 := m .one5 102 3 56 [3068342120892]
private def c325 := m .one5 103 6 57 [2824740643902]
private def c326 := m .one5 103 45 65 [1124185056745]
private def c327 := m .one5 104 44 65 [1141801679299]
private def c328 := m .one5 106 19 61 [1990841847754]
private def c329 := m .one5 106 43 65 [1157348830806]
private def c330 := m .one5 108 26 62 [1675810909041]
private def c331 := m .one5 108 42 64 [1190251739012]
private def c332 := m .one5 109 24 62 [1741155840763]
private def c333 := m .one5 109 41 64 [1209142301611]
private def c334 := m .one5 110 29 63 [1542248048562]
private def c335 := m .one5 111 40 64 [1225567245288]
private def c336 := m .one5 113 35 64 [1338500533766]
private def c337 := m .one5 113 42 65 [1160125481842]
private def c338 := m .one5 115 33 64 [1383016299893]
private def c339 := m .one5 119 41 65 [1164664436645]
private def c340 := m .one5 120 11 59 [2221225000427]
private def c341 := m .one5 126 40 65 [1165530189640]
private def c342 := m .one5 126 51 66 [959701281337]
private def c343 := m .one5 131 9 60 [2126325495266]
private def c344 := m .one5 131 12 61 [1994669973599]
private def c345 := m .one5 131 19 62 [1740545921917]
private def c346 := m .one5 131 26 63 [1514725526778]
private def c347 := m .one5 133 39 65 [1165164855321]
private def c348 := m .one5 134 31 64 [1352730256815]
private def c349 := m .one5 134 50 66 [959845681782]
private def c350 := m .one5 135 30 64 [1372048501515]
private def c351 := m .one6 1 3 16 [10763873764872, 3493053605832, 578632315272, 11563070792]
private def c352 := m .one6 2 6 41 [6510918838760, 900730293992, 7700892101]
private def c353 := m .one6 3 9 52 [4657988033192, 223773624498]
private def c354 := m .one6 4 12 56 [3717203860596, 51447813385]
private def c355 := m .one6 5 13 59 [3339688808368, 25266909994]
private def c356 := m .one6 6 16 62 [2734664190292, 2265181937]
private def c357 := m .one6 7 20 65 [2177655907016]
private def c358 := m .one6 8 23 67 [1870280118569]
private def c359 := m .one6 9 27 68 [1603167985132]
private def c360 := m .one6 10 30 69 [1434243803979]
private def c361 := m .one6 11 31 70 [1364311404509]
private def c362 := m .one6 13 38 71 [1112801918286]
private def c363 := m .one6 14 41 72 [1016251359190]
private def c364 := m .one6 16 48 73 [857293164178]
private def c365 := m .one6 32 3 44 [5917847149476, 765313908516, 8723335855]
private def c366 := m .one6 38 21 67 [1835972748944]
private def c367 := m .one6 38 28 69 [1422975139879]
private def c368 := m .one6 38 35 71 [1140428973354]
private def c369 := m .one6 45 3 51 [4820007143064, 274867653418]
private def c370 := m .one6 59 3 56 [3960011822256, 46232717045]
private def c371 := m .one6 66 39 72 [966970577442]
private def c372 := m .one6 66 46 73 [824468302960]
private def c373 := m .one6 67 30 71 [1209204138655]
private def c374 := m .one6 67 37 72 [1007486113711]
private def c375 := m .one6 67 44 73 [855283714428]
private def c376 := m .one6 68 12 62 [2426174957388, 1182236359]
private def c377 := m .one6 68 15 66 [2045404321928, 259802578]
private def c378 := m .one6 68 19 67 [1765146131072, 225318]
private def c379 := m .one6 68 22 68 [1583067911752]
private def c380 := m .one6 68 26 69 [1388980123776]
private def c381 := m .one6 68 29 70 [1260491347386]
private def c382 := m .one6 68 36 72 [1027824278094]
private def c383 := m .one6 68 43 73 [870704827244]
private def c384 := m .one6 69 18 67 [1814231123240, 5688342]
private def c385 := m .one6 95 26 70 [1258818178820]
private def c386 := m .one6 99 6 60 [2399442927945]
private def c387 := m .one6 99 15 68 [1689877631227]
private def c388 := m .one6 99 20 69 [1464378454707]
private def c389 := m .one6 99 28 71 [1165342539394]
private def c390 := m .one6 112 31 72 [1033464576991]
private def c391 := m .one6 114 26 71 [1164267445446]
private def c392 := m .one6 114 38 73 [877700442756]
private def c393 := m .one6 116 50 74 [694004050502]
private def c394 := m .one6 117 49 74 [704340923372]
private def c395 := m .one6 128 48 74 [702634783620]
private def c396 := m .one6 130 47 74 [711721238531]
private def c397 := m .one6 131 6 68 [1709707966471]
private def c398 := m .one6 131 23 70 [1188227266677]
private def c399 := m .one6 132 12 69 [1492222662017]
private def c400 := m .one6 132 37 73 [858903820442]
private def c401 := m .one6 133 3 67 [1811661486513]
private def c402 := m .one6 133 10 69 [1542150096301]
private def c403 := m .one7 1 3 21 [9077032166204, 2297583275516, 198375301308, 32734497]
private def c404 := m .one7 2 6 63 [3511563105296, 203722249683]
private def c405 := m .one7 3 9 72 [2397003087088, 28205668024]
private def c406 := m .one7 4 12 76 [1838279976596, 1955090945]
private def c407 := m .one7 5 15 79 [1465075891620, 1059812]
private def c408 := m .one7 6 18 82 [1186355348749]
private def c409 := m .one7 7 21 83 [1026077507981]
private def c410 := m .one7 8 24 84 [897484111721]
private def c411 := m .one7 9 26 85 [817181260840]
private def c412 := m .one7 10 28 86 [746679554245]
private def c413 := m .one7 11 32 87 [647567585704]
private def c414 := m .one7 13 39 88 [527172281663]
private def c415 := m .one7 16 47 89 [429666231268]
private def c416 := m .one7 34 22 84 [902566104709]
private def c417 := m .one7 37 18 83 [1057884095975]
private def c418 := m .one7 37 25 85 [793311646380]
private def c419 := m .one7 37 46 89 [426449666339]
private def c420 := m .one7 66 26 86 [702163948861]
private def c421 := m .one7 66 38 88 [496121055870]
private def c422 := m .one7 66 45 89 [417872709045]
private def c423 := m .one7 67 9 79 [1475050349744, 348443239]
private def c424 := m .one7 67 12 81 [1252601080560, 52272779]
private def c425 := m .one7 67 16 83 [1031034746022]
private def c426 := m .one7 67 23 85 [783126096725]
private def c427 := m .one7 67 29 87 [629804537418]
private def c428 := m .one7 68 15 83 [1063927815832]
private def c429 := m .one7 69 21 85 [827114440384]
private def c430 := m .one7 69 24 86 [737431526142]
private def c431 := m .one7 69 28 87 [643672151684]
private def c432 := m .one7 69 35 88 [527843728694]
private def c433 := m .one7 69 42 89 [441666639326]
private def c434 := m .one7 70 34 88 [539211998613]
private def c435 := m .one7 90 3 74 [1717180989942]
private def c436 := m .one7 98 6 81 [1280000109729]
private def c437 := m .one7 98 15 84 [919993508058]
private def c438 := m .one7 98 17 85 [847969131276]
private def c439 := m .one7 98 26 87 [633287455685]
private def c440 := m .one7 99 12 83 [1022561805725]
private def c441 := m .one7 99 22 86 [718358412745]
private def c442 := m .one7 99 40 89 [438486907443]
private def c443 := m .one7 105 10 82 [1072787665570]
private def c444 := m .one7 112 33 88 [508334948295]
private def c445 := m .one7 130 6 83 [1005403415313]
private def c446 := m .one7 130 12 85 [839850242192]
private def c447 := m .one7 130 17 86 [731534993047]
private def c448 := m .one7 130 22 87 [636999319464]
private def c449 := m .one7 130 29 88 [532274341271]
private def c450 := m .one7 130 36 89 [449131492482]
private def c451 := m .one7 131 49 90 [344660274536]
private def c452 := reuse (k' := .two6thin) rfl rfl c351
private def c453 := reuse (k' := .two6thin) rfl rfl c352
private def c454 := m .two6thin 3 8 49 [5153697254120, 359013352168]
private def c455 := reuse (k' := .two6thin) rfl rfl c353
private def c456 := m .two6thin 4 12 57 [3651932216340, 48733123410]
private def c457 := reuse (k' := .two6thin) rfl rfl c355
private def c458 := m .two6thin 5 15 61 [2926993020140, 5931606237]
private def c459 := reuse (k' := .two6thin) rfl rfl c356
private def c460 := m .two6thin 6 18 64 [2414290527392, 120508632]
private def c461 := m .two6thin 7 19 65 [2265911438440, 5645982]
private def c462 := m .two6thin 7 21 66 [2056180168181]
private def c463 := m .two6thin 10 28 69 [1521274784035]
private def c464 := reuse (k' := .two6thin) rfl rfl c361
private def c465 := m .two6thin 12 35 71 [1200183265770]
private def c466 := reuse (k' := .two6thin) rfl rfl c363
private def c467 := reuse (k' := .two6thin) rfl rfl c364
private def c468 := reuse (k' := .two6thin) rfl rfl c371
private def c469 := reuse (k' := .two6thin) rfl rfl c372
private def c470 := reuse (k' := .two6thin) rfl rfl c373
private def c471 := reuse (k' := .two6thin) rfl rfl c374
private def c472 := reuse (k' := .two6thin) rfl rfl c375
private def c473 := reuse (k' := .two6thin) rfl rfl c377
private def c474 := reuse (k' := .two6thin) rfl rfl c379
private def c475 := reuse (k' := .two6thin) rfl rfl c382
private def c476 := reuse (k' := .two6thin) rfl rfl c383
private def c477 := reuse (k' := .two6thin) rfl rfl c384
private def c478 := m .two6thin 69 25 69 [1423057514028]
private def c479 := m .two6thin 86 41 73 [876408647931]
private def c480 := m .two6thin 92 29 71 [1161167854176]
private def c481 := m .two6thin 99 6 65 [2223239774855]
private def c482 := reuse (k' := .two6thin) rfl rfl c387
private def c483 := m .two6thin 102 3 50 [2899452762634]
private def c484 := m .two6thin 104 10 66 [1919963376328]
private def c485 := m .two6thin 106 49 74 [717368462105]
private def c486 := m .two6thin 109 24 70 [1260043062753]
private def c487 := m .two6thin 110 31 72 [1038973838377]
private def c488 := m .two6thin 111 40 73 [850489450442]
private def c489 := reuse (k' := .two6thin) rfl rfl c392
private def c490 := m .two6thin 117 48 74 [716150957456]
private def c491 := m .two6thin 127 47 74 [715548353180]
private def c492 := m .two6thin 128 37 73 [866859096170]
private def c493 := reuse (k' := .two6thin) rfl rfl c397
private def c494 := m .two6thin 131 12 69 [1500158347094]
private def c495 := m .two6thin 131 19 70 [1285963992144]
private def c496 := m .two6thin 132 21 71 [1210229229558]
private def c497 := m .two6thin 132 28 72 [1036555149076]
private def c498 := m .two6thinwide 1 3 20 [9961264891536, 3066845928144, 465857319696, 7045157340]
private def c499 := m .two6thinwide 2 6 45 [5886915837544, 752130814312, 4706634932]
private def c500 := m .two6thinwide 3 9 55 [4237449159564, 185748949370]
private def c501 := m .two6thinwide 4 11 59 [3541787353440, 65910155129]
private def c502 := m .two6thinwide 4 12 61 [3245418555036, 36335024364]
private def c503 := m .two6thinwide 5 13 62 [3018260222300, 19394787681]
private def c504 := m .two6thinwide 5 15 65 [2590487396356, 3806755129]
private def c505 := m .two6thinwide 6 18 67 [2173975472496, 52560564]
private def c506 := m .two6thinwide 7 19 68 [2038887363736, 757005]
private def c507 := m .two6thinwide 7 21 69 [1849454787054]
private def c508 := m .two6thinwide 8 22 70 [1742142017582]
private def c509 := m .two6thinwide 9 25 71 [1535642019241]
private def c510 := m .two6thinwide 9 27 72 [1411810584588]
private def c511 := m .two6thinwide 10 30 73 [1262164160169]
private def c512 := m .two6thinwide 12 34 74 [1104350073700]
private def c513 := m .two6thinwide 14 40 75 [931706134020]
private def c514 := m .two6thinwide 16 46 76 [799319364256]
private def c515 := m .two6thinwide 45 45 76 [777885859218]
private def c516 := m .two6thinwide 47 3 56 [4119400651080, 139873341412]
private def c517 := m .two6thinwide 50 33 74 [1043993007838]
private def c518 := m .two6thinwide 52 31 74 [1091976157109]
private def c519 := m .two6thinwide 71 44 76 [758107661892]
private def c520 := m .two6thinwide 72 43 76 [771494877110]
private def c521 := m .two6thinwide 75 41 76 [797963551776]
private def c522 := m .two6thinwide 76 30 74 [1053727791468]
private def c523 := m .two6thinwide 79 38 75 [858521743104]
private def c524 := m .two6thinwide 81 37 75 [872837326656]
private def c525 := m .two6thinwide 82 50 77 [653451232700]
private def c526 := m .two6thinwide 83 8 66 [2155662338405]
private def c527 := m .two6thinwide 84 36 75 [885492375915]
private def c528 := m .two6thinwide 84 40 76 [799655287194]
private def c529 := m .two6thinwide 85 35 75 [902435312982]
private def c530 := m .two6thinwide 87 34 75 [917708183130]
private def c531 := m .two6thinwide 89 33 75 [933284588947]
private def c532 := m .two6thinwide 91 32 75 [949149558341]
private def c533 := m .two6thinwide 91 39 76 [804007447477]
private def c534 := m .two6thinwide 92 3 65 [2321168862769]
private def c535 := m .two6thinwide 92 49 77 [653936885252]
private def c536 := m .two6thinwide 95 6 66 [2072871919415]
private def c537 := m .two6thinwide 97 29 74 [1017921951961]
private def c538 := m .two6thinwide 99 28 74 [1034888728156]
private def c539 := m .two6thinwide 101 38 76 [802569923589]
private def c540 := m .two6thinwide 102 48 77 [653960476268]
private def c541 := m .two6thinwide 103 27 74 [1045342556314]
private def c542 := m .two6thinwide 103 31 75 [939707730040]
private def c543 := m .two6thinwide 104 9 69 [1724422868949]
private def c544 := m .two6thinwide 104 26 74 [1065478066442]
private def c545 := m .two6thinwide 105 12 70 [1573276271598]
private def c546 := m .two6thinwide 106 15 71 [1435488211883]
private def c547 := m .two6thinwide 106 25 73 [1102994904200]
private def c548 := m .two6thinwide 107 18 72 [1310318560266]
private def c549 := m .two6thinwide 109 24 73 [1115660427895]
private def c550 := m .two6thinwide 110 37 76 [801892511990]
private def c551 := m .two6thinwide 112 47 77 [653467891070]
private def c552 := m .two6thinwide 118 36 76 [802090618175]
private def c553 := m .two6thinwide 119 29 75 [935356911967]
private def c554 := m .two6thinwide 121 46 77 [653628859073]
private def c555 := m .two6thinwide 126 35 76 [801266348048]
private def c556 := m .two6thinwide 128 28 75 [927346784218]
private def c557 := m .two6thinwide 130 45 77 [653244000976]
private def c558 := m .two6thinwide 131 27 75 [935926607350]
private def c559 := m .two6wide 1 3 49 [5358104168160, 1143922387872, 82937803872, 13915806]
private def c560 := m .two6wide 3 9 78 [2099932129216, 42579085810]
private def c561 := m .two6wide 4 12 83 [1585341559428, 5121111724]
private def c562 := m .two6wide 5 15 86 [1268379363540, 136682844]
private def c563 := m .two6wide 6 17 88 [1100234266388]
private def c564 := m .two6wide 7 21 90 [890992733334]
private def c565 := m .two6wide 8 24 92 [760088382075]
private def c566 := m .two6wide 9 27 93 [671417760970]
private def c567 := m .two6wide 12 36 95 [495102701660]
private def c568 := m .two6wide 17 50 96 [353708066542]
private def c569 := m .two6wide 62 30 95 [499020358545]
private def c570 := m .two6wide 63 40 96 [390479679612]
private def c571 := m .two6wide 64 18 92 [726656135814]
private def c572 := m .two6wide 64 25 93 [589323155680]
private def c573 := m .two6wide 64 39 96 [397413432348]
private def c574 := m .two6wide 67 36 96 [419397713310]
private def c575 := m .two6wide 85 44 97 [334658701174]
private def c576 := m .two6wide 92 12 92 [704515913433]
private def c577 := m .two6wide 92 15 93 [646266370681]
private def c578 := m .two6wide 92 43 97 [334985994357]
private def c579 := m .two6wide 97 42 97 [336713251226]
private def c580 := m .two6wide 98 3 90 [841044998565]
private def c581 := m .two6wide 100 41 97 [340020982585]
private def c582 := m .two6wide 101 6 91 [759644819882]
private def c583 := m .two6wide 103 34 96 [392316235456]
private def c584 := m .two6wide 104 9 92 [687457939292]
private def c585 := m .two6wide 106 13 93 [616140644642]
private def c586 := m .two6wide 106 40 97 [340492347886]
private def c587 := m .two6wide 107 16 94 [565894806703]
private def c588 := m .two6wide 108 33 96 [392970848186]
private def c589 := m .two6wide 110 27 95 [445780193376]
private def c590 := m .two6wide 110 29 96 [419101010332]
private def c591 := m .two6wide 117 39 97 [335802782236]
private def c592 := m .two6wide 119 28 96 [411665776170]
private def c593 := m .two6wide 121 12 94 [558023383084]
private def c594 := m .two6wide 121 19 95 [486114187118]
private def c595 := m .two6wide 121 38 97 [337366821008]
private def c596 := m .two6wide 124 37 97 [339746447363]
private def c597 := m .two6wider 1 3 63 [3805959029928, 665276014824, 29633788202]
private def c598 := m .two6wider 2 6 81 [2132644629800, 117874286120, 1327]
private def c599 := m .two6wider 3 9 89 [1467856219676, 18693071514]
private def c600 := m .two6wider 4 12 94 [1090691075964, 1437930957]
private def c601 := m .two6wider 5 13 95 [1004278211440, 417611912]
private def c602 := m .two6wider 5 15 97 [865575170492, 4095308]
private def c603 := m .two6wider 6 18 99 [717374696280]
private def c604 := m .two6wider 7 20 100 [642934553621]
private def c605 := m .two6wider 8 24 102 [526258786451]
private def c606 := m .two6wider 9 27 103 [463806908259]
private def c607 := m .two6wider 11 31 104 [399464704741]
private def c608 := m .two6wider 12 36 105 [340339480642]
private def c609 := m .two6wider 14 41 106 [292984220662]
private def c610 := m .two6wider 17 50 107 [235308681116]
private def c611 := m .two6wider 61 9 100 [664697129650]
private def c612 := m .two6wider 65 44 107 [236831872940]
private def c613 := m .two6wider 70 39 106 [264645335207]
private def c614 := m .two6wider 72 38 106 [268293575202]
private def c615 := m .two6wider 74 36 106 [277372199370]
private def c616 := m .two6wider 75 35 106 [282054313144]
private def c617 := m .two6wider 75 43 107 [235167545026]
private def c618 := m .two6wider 78 33 106 [290696084939]
private def c619 := m .two6wider 79 42 107 [236947096204]
private def c620 := m .two6wider 80 32 106 [294539416199]
private def c621 := m .two6wider 82 30 105 [313469931745]
private def c622 := m .two6wider 83 29 105 [318610241394]
private def c623 := m .two6wider 83 31 106 [297233223761]
private def c624 := m .two6wider 84 41 107 [237977812711]
private def c625 := m .two6wider 87 26 105 [332643576155]
private def c626 := m .two6wider 90 40 107 [238155691739]
private def c627 := m .two6wider 91 23 105 [346062182828]
private def c628 := m .two6wider 92 30 106 [292756005634]
private def c629 := m .two6wider 95 22 105 [345515454962]
private def c630 := m .two6wider 96 39 107 [238086132669]
private def c631 := m .two6wider 97 20 104 [365055560932]
private def c632 := m .two6wider 99 29 106 [289816019253]
private def c633 := m .two6wider 101 19 104 [363415538992]
private def c634 := m .two6wider 101 38 107 [238491770174]
private def c635 := m .two6wider 102 3 101 [513588456564]
private def c636 := m .two6wider 103 6 102 [472357433385]
private def c637 := m .two6wider 103 21 105 [337260108240]
private def c638 := m .two6wider 103 27 106 [295111863917]
private def c639 := m .two6wider 104 17 104 [369664929634]
private def c640 := m .two6wider 105 12 104 [399182711989]
private def c641 := m .two6wider 107 37 107 [237858397260]
private def c642 := m .two6wider 111 36 107 [238540143567]
private def c643 := m .two6wider 116 35 107 [238153735559]
private def c644 := m .two6wider 119 23 106 [292167945120]
private def c645 := m .two6wider 120 9 104 [378830252389]
private def c646 := m .two6wider 120 16 105 [332488565498]
private def c647 := m .two6wider 120 34 107 [238382469940]
private def c648 := m .two6wider 121 22 106 [293700694066]
private def c649 := m .two6wider 122 50 108 [180806930600]
private def c650 := m .two7 1 3 44 [6100649235572, 1209555278004, 48403582533]
private def c651 := reuse (k' := .two7) rfl rfl c404
private def c652 := reuse (k' := .two7) rfl rfl c405
private def c653 := reuse (k' := .two7) rfl rfl c407
private def c654 := reuse (k' := .two7) rfl rfl c408
private def c655 := reuse (k' := .two7) rfl rfl c409
private def c656 := reuse (k' := .two7) rfl rfl c411
private def c657 := reuse (k' := .two7) rfl rfl c412
private def c658 := m .two7 11 33 87 [630517609326]
private def c659 := m .two7 14 40 88 [514431830525]
private def c660 := m .two7 17 49 89 [412485053456]
private def c661 := m .two7 50 6 71 [2231750418960, 25296782323]
private def c662 := m .two7 50 13 79 [1361273823888, 108255420]
private def c663 := m .two7 50 20 83 [949014322288]
private def c664 := m .two7 61 34 88 [548127512580]
private def c665 := reuse (k' := .two7) rfl rfl c428
private def c666 := m .two7 68 22 84 [825550895467]
private def c667 := m .two7 71 42 89 [440327264810]
private def c668 := m .two7 90 41 89 [436167664730]
private def c669 := m .two7 98 39 89 [448154117622]
private def c670 := m .two7 99 9 82 [1140998438444]
private def c671 := reuse (k' := .two7) rfl rfl c440
private def c672 := m .two7 102 3 79 [1412483124808]
private def c673 := m .two7 107 17 84 [839477882475]
private def c674 := m .two7 107 19 85 [777145552437]
private def c675 := m .two7 109 26 86 [631786050445]
private def c676 := m .two7 110 27 87 [599870677547]
private def c677 := m .two7 112 31 88 [531003488124]
private def c678 := m .two7 117 49 90 [351589473554]
private def c679 := m .two7 119 38 89 [440732594775]
private def c680 := m .two7 124 29 88 [539988298234]
private def c681 := m .two7 128 37 89 [442086562692]
private def c682 := m .two7 128 48 90 [352067435474]
private def c683 := m .two7 130 9 84 [919661474698]
private def c684 := reuse (k' := .two7) rfl rfl c446
private def c685 := m .two7 130 16 86 [748536917630]
private def c686 := reuse (k' := .two7) rfl rfl c450
private def c687 := m .two7wide 1 3 63 [3785674630956, 538104382188, 6953811806]
private def c688 := m .two7wide 2 6 80 [2094969797132, 68315171797]
private def c689 := m .two7wide 3 9 88 [1401903487600, 5640934178]
private def c690 := m .two7wide 4 12 92 [1053299427236, 59769751]
private def c691 := m .two7wide 5 15 95 [829325525477]
private def c692 := m .two7wide 6 17 96 [734836181536]
private def c693 := m .two7wide 7 19 97 [655454064172]
private def c694 := m .two7wide 8 24 99 [513524165094]
private def c695 := m .two7wide 10 29 100 [424390908240]
private def c696 := m .two7wide 11 33 101 [367493053624]
private def c697 := m .two7wide 13 39 102 [305816765599]
private def c698 := m .two7wide 17 49 103 [237949022076]
private def c699 := m .two7wide 33 6 87 [1450513302008, 16604119967]
private def c700 := m .two7wide 33 14 95 [785842282687]
private def c701 := m .two7wide 65 9 94 [854572312880]
private def c702 := m .two7wide 65 17 98 [571046711048]
private def c703 := m .two7wide 65 31 101 [348538850734]
private def c704 := m .two7wide 68 33 102 [319928891427]
private def c705 := m .two7wide 77 47 103 [227563740970]
private def c706 := m .two7wide 81 45 103 [234916771344]
private def c707 := m .two7wide 86 44 103 [237609097440]
private def c708 := m .two7wide 92 49 104 [207936511255]
private def c709 := m .two7wide 98 43 103 [237577805267]
private def c710 := m .two7wide 99 32 102 [307029084922]
private def c711 := m .two7wide 102 3 95 [777643371866]
private def c712 := m .two7wide 102 42 103 [240567426917]
private def c713 := m .two7wide 104 48 104 [207984048436]
private def c714 := m .two7wide 105 10 97 [603803310056]
private def c715 := m .two7wide 106 15 99 [499258643693]
private def c716 := m .two7wide 107 30 101 [325089864982]
private def c717 := m .two7wide 108 21 100 [413335414996]
private def c718 := m .two7wide 108 29 101 [331699279314]
private def c719 := m .two7wide 108 40 103 [247481065508]
private def c720 := m .two7wide 109 24 101 [371807207217]
private def c721 := m .two7wide 112 39 103 [250548779032]
private def c722 := m .two7wide 115 38 103 [254099412370]
private def c723 := m .two7wide 116 47 104 [207871145769]
private def c724 := m .two7wide 118 36 103 [262886353471]
private def c725 := m .two7wide 123 35 103 [265495070995]
private def c726 := m .two7wide 126 34 103 [269173403255]
private def c727 := m .two7wide 127 6 98 [569940414168]
private def c728 := m .two7wide 127 9 99 [519801933368]
private def c729 := m .two7wide 127 13 100 [462843402790]
private def c730 := m .two7wide 127 20 101 [384703718039]
private def c731 := m .two7wide 127 29 102 [306942535908]
private def c732 := m .two7wide 127 46 104 [207913287899]
private def c733 := m .two7wide 130 27 102 [317686247348]
private def c734 := m .two7last 1 3 91 [1696135255896, 125162735704, 9617601]
private def c735 := m .two7last 2 6 105 [899244360792, 8163016024]
private def c736 := m .two7last 3 7 108 [757300870488, 2462906641]
private def c737 := m .two7last 3 9 111 [601938706192, 97003970]
private def c738 := m .two7last 4 11 114 [480346637434]
private def c739 := m .two7last 4 12 115 [439279709157]
private def c740 := m .two7last 5 14 116 [382059423722]
private def c741 := m .two7last 5 15 117 [351570709627]
private def c742 := m .two7last 6 18 119 [285999845167]
private def c743 := m .two7last 7 21 120 [244641526172]
private def c744 := m .two7last 8 24 121 [211496293272]
private def c745 := m .two7last 10 28 122 [178515260470]
private def c746 := m .two7last 11 33 123 [148774561317]
private def c747 := m .two7last 14 41 124 [116869410464]
private def c748 := m .two7last 39 32 123 [144887375027]
private def c749 := m .two7last 41 39 124 [117150516103]
private def c750 := m .two7last 43 25 122 [181459133500]
private def c751 := m .two7last 43 31 123 [147543050281]
private def c752 := m .two7last 47 21 121 [211409570737]
private def c753 := m .two7last 48 19 120 [233969564050]
private def c754 := m .two7last 49 18 120 [241477400478]
private def c755 := m .two7last 49 24 122 [184238377848]
private def c756 := m .two7last 49 30 123 [149622815063]
private def c757 := m .two7last 49 38 124 [118234588337]
private def c758 := m .two7last 53 12 118 [320694279336]
private def c759 := m .two7last 53 15 119 [275346214386]
private def c760 := m .two7last 56 11 117 [340872172021]
private def c761 := m .two7last 56 14 119 [282462969083]
private def c762 := m .two7last 56 17 120 [244242759992]
private def c763 := m .two7last 56 20 121 [212709804967]
private def c764 := m .two7last 58 29 123 [150682885584]
private def c765 := m .two7last 62 37 124 [118214223424]
private def c766 := m .two7last 65 15 120 [253241391232]
private def c767 := m .two7last 65 23 122 [181925045757]
private def c768 := m .two7last 70 28 123 [150535042965]
private def c769 := m .two7last 71 22 122 [184190435836]
private def c770 := m .two7last 73 18 121 [214519767669]
private def c771 := m .two7last 74 36 124 [118269999779]
private def c772 := m .two7last 77 7 117 [347968733758]
private def c773 := m .two7last 77 10 118 [304498200898]
private def c774 := m .two7last 77 17 121 [218154197472]
private def c775 := m .two7last 77 49 125 [86757072322]
private def c776 := m .two7last 80 27 123 [150829079198]
private def c777 := m .two7last 81 21 122 [183968674089]
private def c778 := m .two7last 86 35 124 [118178945430]
private def c779 := m .two7last 87 6 118 [324172193364]
private def c780 := m .two7last 87 10 119 [277803142160]
private def c781 := m .two7last 88 9 119 [284613037589]
private def c782 := m .two7last 88 13 120 [243878526107]
private def c783 := m .two7last 90 20 122 [183782901239]
private def c784 := m .two7last 90 48 125 [86703624896]
private def c785 := m .two7last 91 12 120 [247443813775]
private def c786 := m .two7last 91 26 123 [150455201086]
private def c787 := m .two7last 95 16 121 [209146039648]
private def c788 := m .two7last 97 34 124 [118165075680]
private def c789 := m .two7last 98 15 121 [212245694627]
private def c790 := m .two7last 98 19 122 [183655442832]
private def c791 := m .two7last 100 25 123 [150552766720]
private def c792 := m .two7last 102 3 118 [316775082117]
private def c793 := m .two7last 102 47 125 [86711017708]
private def c794 := m .two7last 105 18 122 [183667764458]
private def c795 := m .two7last 107 33 124 [118240592986]
private def c796 := m .two7last 108 24 123 [150766948404]
private def c797 := m .two7last 109 12 121 [218038552611]
private def c798 := m .two7last 111 17 122 [183946093493]
private def c799 := m .two7last 114 46 125 [86646283394]
private def c800 := m .two7last 116 23 123 [150650637918]
private def c801 := m .two7last 117 16 122 [183839011622]
private def c802 := m .two7last 117 32 124 [118147763264]
private def c803 := m .two7last 119 9 120 [230215645908]
private def c804 := m .two7last 119 10 121 [217367880469]
private def c805 := m .two7last 122 15 122 [184185053434]
private def c806 := m .two7last 123 22 123 [150685644715]
private def c807 := m .two7last 125 45 125 [86646722952]
private def c808 := m .two7last 126 31 124 [118145833597]
private def c809 := m .two6last 1 3 110 [953934236652, 62646500460, 58484552]
private def c810 := m .two6last 2 6 123 [506195982176, 5536824832]
private def c811 := m .two6last 3 9 130 [324227293772, 155141115]
private def c812 := m .two6last 4 12 133 [244594810958]
private def c813 := m .two6last 5 15 135 [195530007556]
private def c814 := m .two6last 6 17 136 [171801509524]
private def c815 := m .two6last 7 20 138 [140595098892]
private def c816 := m .two6last 9 27 140 [102104966662]
private def c817 := m .two6last 12 36 141 [76182908668]
private def c818 := m .two6last 17 50 143 [51141853401]
private def c819 := m .two6last 61 9 138 [122228151880]
private def c820 := m .two6last 61 17 140 [96026543763]
private def c821 := m .two6last 62 15 140 [99004687204]
private def c822 := m .two6last 62 23 141 [80995530948]
private def c823 := m .two6last 63 21 141 [83670293517]
private def c824 := m .two6last 65 36 142 [59287661807]
private def c825 := m .two6last 95 48 143 [41402081913]
private def c826 := m .two6last 97 47 143 [41692627695]
private def c827 := m .two6last 99 34 142 [52028453356]
private def c828 := m .two6last 99 45 143 [42568689121]
private def c829 := m .two6last 102 3 140 [83117143314]
private def c830 := m .two6last 102 31 142 [53377145810]
private def c831 := m .two6last 103 44 143 [42478580523]
private def c832 := m .two6last 105 10 141 [71485558212]
private def c833 := m .two6last 105 43 143 [42707948473]
private def c834 := m .two6last 107 30 142 [52619929906]
private def c835 := m .two6last 107 42 143 [42919620203]
private def c836 := m .two6last 108 41 143 [43305797399]
private def c837 := m .two6last 110 27 142 [53740300393]
private def c838 := m .two6last 111 29 143 [49800225710]
private def c839 := m .two6last 116 50 144 [35643379710]
private def c840 := m .two6last 117 9 142 [63135612315]
private def c841 := m .two6last 117 23 143 [51651831235]
private def c842 := m .two6last 119 49 144 [35683623322]
private def c843 := m .one8 1 3 112 [670086414336, 5374605669]
private def c844 := m .one8 2 6 122 [336001387560]
private def c845 := m .one8 3 9 126 [225566066596]
private def c846 := m .one8 4 12 129 [162893353845]
private def c847 := m .one8 5 15 130 [133057456939]
private def c848 := m .one8 6 18 131 [110450998870]
private def c849 := m .one8 7 21 132 [92821859904]
private def c850 := m .one8 8 24 133 [78762303125]
private def c851 := m .one8 10 30 134 [61355654014]
private def c852 := m .one8 13 39 135 [45295582481]
private def c853 := m .one8 36 6 124 [274654643002]
private def c854 := m .one8 36 28 134 [63350737144]
private def c855 := m .one8 69 6 126 [223301757209]
private def c856 := m .one8 69 9 128 [172484541781]
private def c857 := m .one8 70 12 130 [134674249480]
private def c858 := m .one8 102 3 126 [227161942705]
private def c859 := m .one8 102 6 128 [179925285198]
private def c860 := m .one8 102 9 130 [142348505938]
private def c861 := m .one8 102 26 134 [62167037593]
private def c862 := m .one8 103 12 131 [118615008925]
private def c863 := m .one8 107 17 132 [92081880430]
private def c864 := reuse (k' := .two8) rfl rfl c843
private def c865 := reuse (k' := .two8) rfl rfl c844
private def c866 := reuse (k' := .two8) rfl rfl c845
private def c867 := reuse (k' := .two8) rfl rfl c846
private def c868 := reuse (k' := .two8) rfl rfl c847
private def c869 := reuse (k' := .two8) rfl rfl c848
private def c870 := reuse (k' := .two8) rfl rfl c849
private def c871 := reuse (k' := .two8) rfl rfl c850
private def c872 := m .two8 10 29 134 [63222145578]
private def c873 := m .two8 13 38 135 [46441725899]
private def c874 := reuse (k' := .two8) rfl rfl c858
private def c875 := m .two8 103 6 128 [179236649792]
private def c876 := m .two8 104 9 130 [141514293715]
private def c877 := m .two8 104 37 135 [43806325716]
private def c878 := m .two8 105 12 131 [118050847645]
private def c879 := m .two8 106 15 132 [99352290308]
private def c880 := m .two8 106 36 135 [44791159334]
private def c881 := m .two8 108 19 133 [81275435887]
private def c882 := m .two8 108 35 135 [45812718748]
private def c883 := m .two8 110 26 134 [61531627993]
private def c884 := m .two8 113 34 135 [46727910957]
private def c885 := m .two8 133 33 135 [46907222514]
private theorem nilGood (k : Band) : ∀ q ∈ ([] : List Threshold), Good k q := by
  simp

private theorem cg {k : Band} {a : Threshold} {rest : List Threshold} (ha : Good k a)
    (hs : ∀ q ∈ rest,Good k q) : ∀ q ∈ a :: rest,Good k q:=by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | h
  · exact ha
  · exact hs q h

private theorem thresholds_valid (k : Band) (q : Threshold) (hq : q ∈ thresholds k) :
    0 < q.j ∧ availableMass (start k) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed:=by
  revert q
  cases k
  · exact cg c0 (cg c1 (cg c2 (cg c3 (cg c4 (cg c5 (cg c6 (cg c7 (cg c8 (cg c9 (
    cg c10 (cg c11 (cg c12 (cg c13 (cg c14 (cg c15 (cg c16 (cg c17 (cg c18 (cg c19 (
    cg c20 (cg c21 (cg c22 (cg c23 (cg c24 (cg c25 (cg c26 (cg c27 (cg c28 (cg c29 (
    cg c30 (cg c31 (cg c32 (cg c33 (cg c34 (cg c35 (cg c36 (cg c37 (cg c38 (cg c39 (
    cg c40 (cg c41 (cg c42 (cg c43 (cg c44 (cg c45 (cg c46 (cg c47 (cg c48 (cg c49 (
    cg c50 (cg c51 (cg c52 (cg c53 (cg c54 (cg c55 (cg c56 (cg c57 (cg c58 (cg c59 (
    cg c60 (cg c61 (cg c62 (cg c63 (cg c64 (cg c65 (cg c66 (cg c67 (cg c68 (cg c69 (
    cg c70 (cg c71 (cg c72 (cg c73 (cg c74 (cg c75 (cg c76 (cg c77 (cg c78 (cg c79 (
    cg c80 (cg c81 (cg c82 (cg c83 (cg c84 (cg c85 (cg c86 (cg c87 (cg c88 (cg c89 (
    cg c90 (cg c91 (cg c92 (cg c93 (cg c94 (cg c95 (cg c96 (cg c97 (cg c98 (cg c99 (
    cg c100 (cg c101 (cg c102 (cg c103 (cg c104 (cg c105 (cg c106 (cg c107 (cg c108 (cg c109 (
    cg c110 (cg c111 (nilGood .empty))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact cg c112 (cg c113 (cg c114 (cg c115 (cg c116 (cg c117 (cg c118 (cg c119 (cg c120 (cg c121 (
    cg c122 (cg c123 (cg c124 (cg c125 (cg c126 (cg c127 (cg c128 (cg c129 (cg c130 (cg c131 (
    cg c132 (cg c133 (cg c134 (cg c135 (cg c136 (cg c137 (cg c138 (cg c139 (cg c140 (cg c141 (
    cg c142 (cg c143 (cg c144 (cg c145 (cg c146 (cg c147 (cg c148 (cg c149 (cg c150 (cg c151 (
    cg c152 (cg c153 (cg c154 (cg c155 (cg c156 (cg c157 (cg c158 (cg c159 (cg c160 (cg c161 (
    cg c162 (cg c163 (cg c164 (cg c165 (cg c166 (cg c167 (cg c168 (cg c169 (cg c170 (cg c171 (
    cg c172 (nilGood .one3)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact cg c173 (cg c174 (cg c175 (cg c176 (cg c177 (cg c178 (cg c179 (cg c180 (cg c181 (cg c182 (
    cg c183 (cg c184 (cg c185 (cg c186 (cg c187 (cg c188 (cg c189 (cg c190 (cg c191 (cg c192 (
    cg c193 (cg c194 (cg c195 (cg c196 (cg c197 (cg c198 (cg c199 (cg c200 (cg c201 (cg c202 (
    cg c203 (cg c204 (cg c205 (cg c206 (cg c207 (cg c208 (cg c209 (cg c210 (cg c211 (cg c212 (
    cg c213 (cg c214 (cg c215 (cg c216 (cg c217 (cg c218 (cg c219 (cg c220 (cg c221 (cg c222 (
    cg c223 (cg c224 (cg c225 (cg c226 (cg c227 (cg c228 (cg c229 (cg c230 (cg c231 (cg c232 (
    cg c233 (nilGood .one3wide)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact cg c234 (cg c235 (cg c236 (cg c237 (cg c238 (cg c239 (cg c240 (cg c241 (cg c242 (cg c243 (
    cg c244 (cg c245 (cg c246 (cg c247 (cg c248 (cg c249 (cg c250 (cg c251 (cg c252 (cg c253 (
    cg c254 (cg c255 (cg c256 (cg c257 (cg c258 (cg c259 (cg c260 (cg c261 (cg c262 (cg c263 (
    cg c264 (cg c265 (cg c266 (cg c267 (cg c268 (cg c269 (cg c270 (cg c271 (cg c272 (cg c273 (
    cg c274 (cg c275 (cg c276 (cg c277 (cg c278 (cg c279 (cg c280 (cg c281 (cg c282 (cg c283 (
    cg c284 (cg c285 (cg c286 (cg c287 (cg c288 (cg c289 (cg c290 (nilGood .one4)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact cg c291 (cg c292 (cg c293 (cg c294 (cg c295 (cg c296 (cg c297 (cg c298 (cg c299 (cg c300 (
    cg c301 (cg c302 (cg c303 (cg c304 (cg c305 (cg c306 (cg c307 (cg c308 (cg c309 (cg c310 (
    cg c311 (cg c312 (cg c313 (cg c314 (cg c315 (cg c316 (cg c317 (cg c318 (cg c319 (cg c320 (
    cg c321 (cg c322 (cg c323 (cg c324 (cg c325 (cg c326 (cg c327 (cg c328 (cg c329 (cg c330 (
    cg c331 (cg c332 (cg c333 (cg c334 (cg c335 (cg c336 (cg c337 (cg c338 (cg c339 (cg c340 (
    cg c341 (cg c342 (cg c343 (cg c344 (cg c345 (cg c346 (cg c347 (cg c348 (cg c349 (cg c350 (
    nilGood .one5))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact cg c351 (cg c352 (cg c353 (cg c354 (cg c355 (cg c356 (cg c357 (cg c358 (cg c359 (cg c360 (
    cg c361 (cg c362 (cg c363 (cg c364 (cg c365 (cg c366 (cg c367 (cg c368 (cg c369 (cg c370 (
    cg c371 (cg c372 (cg c373 (cg c374 (cg c375 (cg c376 (cg c377 (cg c378 (cg c379 (cg c380 (
    cg c381 (cg c382 (cg c383 (cg c384 (cg c385 (cg c386 (cg c387 (cg c388 (cg c389 (cg c390 (
    cg c391 (cg c392 (cg c393 (cg c394 (cg c395 (cg c396 (cg c397 (cg c398 (cg c399 (cg c400 (
    cg c401 (cg c402 (nilGood .one6))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact cg c403 (cg c404 (cg c405 (cg c406 (cg c407 (cg c408 (cg c409 (cg c410 (cg c411 (cg c412 (
    cg c413 (cg c414 (cg c415 (cg c416 (cg c417 (cg c418 (cg c419 (cg c420 (cg c421 (cg c422 (
    cg c423 (cg c424 (cg c425 (cg c426 (cg c427 (cg c428 (cg c429 (cg c430 (cg c431 (cg c432 (
    cg c433 (cg c434 (cg c435 (cg c436 (cg c437 (cg c438 (cg c439 (cg c440 (cg c441 (cg c442 (
    cg c443 (cg c444 (cg c445 (cg c446 (cg c447 (cg c448 (cg c449 (cg c450 (cg c451 (nilGood .one7)))))))))))))))))))))))))))))))))))))))))))))))))
  · exact cg c452 (cg c453 (cg c454 (cg c455 (cg c456 (cg c457 (cg c458 (cg c459 (cg c460 (cg c461 (
    cg c462 (cg c463 (cg c464 (cg c465 (cg c466 (cg c467 (cg c468 (cg c469 (cg c470 (cg c471 (
    cg c472 (cg c473 (cg c474 (cg c475 (cg c476 (cg c477 (cg c478 (cg c479 (cg c480 (cg c481 (
    cg c482 (cg c483 (cg c484 (cg c485 (cg c486 (cg c487 (cg c488 (cg c489 (cg c490 (cg c491 (
    cg c492 (cg c493 (cg c494 (cg c495 (cg c496 (cg c497 (nilGood .two6thin))))))))))))))))))))))))))))))))))))))))))))))
  · exact cg c498 (cg c499 (cg c500 (cg c501 (cg c502 (cg c503 (cg c504 (cg c505 (cg c506 (cg c507 (
    cg c508 (cg c509 (cg c510 (cg c511 (cg c512 (cg c513 (cg c514 (cg c515 (cg c516 (cg c517 (
    cg c518 (cg c519 (cg c520 (cg c521 (cg c522 (cg c523 (cg c524 (cg c525 (cg c526 (cg c527 (
    cg c528 (cg c529 (cg c530 (cg c531 (cg c532 (cg c533 (cg c534 (cg c535 (cg c536 (cg c537 (
    cg c538 (cg c539 (cg c540 (cg c541 (cg c542 (cg c543 (cg c544 (cg c545 (cg c546 (cg c547 (
    cg c548 (cg c549 (cg c550 (cg c551 (cg c552 (cg c553 (cg c554 (cg c555 (cg c556 (cg c557 (
    cg c558 (nilGood .two6thinwide)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact cg c559 (cg c560 (cg c561 (cg c562 (cg c563 (cg c564 (cg c565 (cg c566 (cg c567 (cg c568 (
    cg c569 (cg c570 (cg c571 (cg c572 (cg c573 (cg c574 (cg c575 (cg c576 (cg c577 (cg c578 (
    cg c579 (cg c580 (cg c581 (cg c582 (cg c583 (cg c584 (cg c585 (cg c586 (cg c587 (cg c588 (
    cg c589 (cg c590 (cg c591 (cg c592 (cg c593 (cg c594 (cg c595 (cg c596 (nilGood .two6wide))))))))))))))))))))))))))))))))))))))
  · exact cg c597 (cg c598 (cg c599 (cg c600 (cg c601 (cg c602 (cg c603 (cg c604 (cg c605 (cg c606 (
    cg c607 (cg c608 (cg c609 (cg c610 (cg c611 (cg c612 (cg c613 (cg c614 (cg c615 (cg c616 (
    cg c617 (cg c618 (cg c619 (cg c620 (cg c621 (cg c622 (cg c623 (cg c624 (cg c625 (cg c626 (
    cg c627 (cg c628 (cg c629 (cg c630 (cg c631 (cg c632 (cg c633 (cg c634 (cg c635 (cg c636 (
    cg c637 (cg c638 (cg c639 (cg c640 (cg c641 (cg c642 (cg c643 (cg c644 (cg c645 (cg c646 (
    cg c647 (cg c648 (cg c649 (nilGood .two6wider)))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact cg c650 (cg c651 (cg c652 (cg c653 (cg c654 (cg c655 (cg c656 (cg c657 (cg c658 (cg c659 (
    cg c660 (cg c661 (cg c662 (cg c663 (cg c664 (cg c665 (cg c666 (cg c667 (cg c668 (cg c669 (
    cg c670 (cg c671 (cg c672 (cg c673 (cg c674 (cg c675 (cg c676 (cg c677 (cg c678 (cg c679 (
    cg c680 (cg c681 (cg c682 (cg c683 (cg c684 (cg c685 (cg c686 (nilGood .two7)))))))))))))))))))))))))))))))))))))
  · exact cg c687 (cg c688 (cg c689 (cg c690 (cg c691 (cg c692 (cg c693 (cg c694 (cg c695 (cg c696 (
    cg c697 (cg c698 (cg c699 (cg c700 (cg c701 (cg c702 (cg c703 (cg c704 (cg c705 (cg c706 (
    cg c707 (cg c708 (cg c709 (cg c710 (cg c711 (cg c712 (cg c713 (cg c714 (cg c715 (cg c716 (
    cg c717 (cg c718 (cg c719 (cg c720 (cg c721 (cg c722 (cg c723 (cg c724 (cg c725 (cg c726 (
    cg c727 (cg c728 (cg c729 (cg c730 (cg c731 (cg c732 (cg c733 (nilGood .two7wide)))))))))))))))))))))))))))))))))))))))))))))))
  · exact cg c734 (cg c735 (cg c736 (cg c737 (cg c738 (cg c739 (cg c740 (cg c741 (cg c742 (cg c743 (
    cg c744 (cg c745 (cg c746 (cg c747 (cg c748 (cg c749 (cg c750 (cg c751 (cg c752 (cg c753 (
    cg c754 (cg c755 (cg c756 (cg c757 (cg c758 (cg c759 (cg c760 (cg c761 (cg c762 (cg c763 (
    cg c764 (cg c765 (cg c766 (cg c767 (cg c768 (cg c769 (cg c770 (cg c771 (cg c772 (cg c773 (
    cg c774 (cg c775 (cg c776 (cg c777 (cg c778 (cg c779 (cg c780 (cg c781 (cg c782 (cg c783 (
    cg c784 (cg c785 (cg c786 (cg c787 (cg c788 (cg c789 (cg c790 (cg c791 (cg c792 (cg c793 (
    cg c794 (cg c795 (cg c796 (cg c797 (cg c798 (cg c799 (cg c800 (cg c801 (cg c802 (cg c803 (
    cg c804 (cg c805 (cg c806 (cg c807 (cg c808 (nilGood .two7last)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · exact cg c809 (cg c810 (cg c811 (cg c812 (cg c813 (cg c814 (cg c815 (cg c816 (cg c817 (cg c818 (
    cg c819 (cg c820 (cg c821 (cg c822 (cg c823 (cg c824 (cg c825 (cg c826 (cg c827 (cg c828 (
    cg c829 (cg c830 (cg c831 (cg c832 (cg c833 (cg c834 (cg c835 (cg c836 (cg c837 (cg c838 (
    cg c839 (cg c840 (cg c841 (cg c842 (nilGood .two6last))))))))))))))))))))))))))))))))))
  · exact cg c843 (cg c844 (cg c845 (cg c846 (cg c847 (cg c848 (cg c849 (cg c850 (cg c851 (cg c852 (
    cg c853 (cg c854 (cg c855 (cg c856 (cg c857 (cg c858 (cg c859 (cg c860 (cg c861 (cg c862 (
    cg c863 (nilGood .one8)))))))))))))))))))))
  · exact cg c864 (cg c865 (cg c866 (cg c867 (cg c868 (cg c869 (cg c870 (cg c871 (cg c872 (cg c873 (
    cg c874 (cg c875 (cg c876 (cg c877 (cg c878 (cg c879 (cg c880 (cg c881 (cg c882 (cg c883 (
    cg c884 (cg c885 (nilGood .two8))))))))))))))))))))))

theorem order_valid (k : Band) (x : Shape) : order k x = 1 ∨
    availableMass (start k) x (order k x - 1) < layerNeed:=by
  rcases (P0_9_8.orderFor_select x.b x.j (thresholds k)).2 with h | ⟨q,hq,hb,hj,he⟩
  · exact Or.inl h
  · right
    change order k x=q.l at he
    rw [he]
    obtain ⟨hpos,hsmall⟩:=thresholds_valid k q hq
    have hr:start k=zeroShape ∨ 0 < (start k).j:=by cases k <;> decide
    have hi:0 < (start k).j+q.j:=by omega
    exact (Final50PriceLayer.availableMass_anti_prefix (y:=⟨q.b,q.j,0⟩) hr hi hb hj).trans_lt hsmall
#print axioms order_valid
end Final50PriceMass
