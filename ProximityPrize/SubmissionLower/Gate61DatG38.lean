import ProximityPrize.SubmissionLower.Gate61Assm
set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 400000
set_option Elab.async false
namespace Gate61DatG38
open Gate61Cell
def G : Gt := { m00 := 0, m01 := 990197695509184, m02 := 3262380704454720, m11 := 1884224939959888, m12 := 7056902731154160, m22 := 21754283429316816, xb := 27, xj := 56, xt := 13, lb := 18, lj := 54, lt := 10, A := 187364269863309391, sc := 32, lift := true }
def ws : List ℕ := [0x0,0x0,0x0,0x0,0x0,0x57e40301,0x4c4b4301,0x439e8301,0x3ccc0301,0x7a120301b208402,0x6275d301631e402,0x57e4030127ee402,0x51a00300fa67402,0x4c4b4300d6a2402,0x7a1203047acf300ba04403,0x6958a30439e8300a2c3403,0x5cc10304004f3008f9d403,0x57e40303ccc03007fa8403,0x8576b3053988301d9854007238404,0x7a120304fc1d301b20840066cc404,0x6d202304c4b430180fd4005d02404,0x49257301631e400548e403,0x464453013f084004d33403,0x57e4030439e830127ee40046c4404,0x7a12030549f730412c83010c9e400411b405,0x51a00303ee81300fa674003c19404,0x4edbd303ccc0300e53c40037a6404,0x8af21305eb5f304c4b4303ad40300d6a240033ac406,0x5abb53049e80301c564400c5e5400301c405,0x57e403047acf301b208400ba044002ce7405,0x5540e304595a3019061400ac8d4002a01405,0x6958a3052cb630439e83017276400a2c34002761406,0x6275d30507e13041c48301631e40097c740024fe406,0x5cc10304e54a304004f3014a6e4008f9d40022d1406,0x5a3e2304c4b4303e5d73013436400868840020d4406,0x725b83057e40304a5ef303ccc030127ee4007fa84001f01407,0x6b79f3055ae130488cd303b4ee301154a40078104001d54407,0x654ee30539883046d2b301d985401045840072384001bc9407,0x5fc143051a0030452e9301bbcc400fa674006bce4001a5c407,0x4fc1d30439e8301b208400ebfc40066cc400190b406,0x59e5c304dfb93042212301986b400dec4400615540017d2407,0x6d2023057e40304c4b43040b4f30180fd400d6a24005d0240016b0408,0x55fce304aaf1303f58c3016b81400cb40400584f40015a2407,0x542dd3049257303e0b7301631e400c0bf400548e40014a6407,0x5dd06305274d3047acf303ccc0301505b400ba04400507d40013bb408,0x5b7a33050cff3046445303b9993013f08400b0e04004d3340012df408,0x59a40304f3db3044ea8303a7343012f01400a86340049a94001212408,0x57e40304dbc930439e8303958530127ee400a2c340046c44001151408,0x64a993056386304c4b430425f7303848330119c84009b5040043aa400109c409,0x7a120306058230549f7304ae8d30412c830374223010c9e400945c400411b4000ff240a,0x5cc10305317c3049942304004f303645930100594008f9d4003e5f4000f52409,0x6f833305b0fb3051a0030484c4303ee813035521300fa6740089764003c194000ebb40a,0x6ad44305971330503703047108303dd543034671300ef7840083b140039ad4000e2d40a,0x7c0c430667d63057e40304edbd3045e01303ccc03033842300e53c4007fa840037a64000da740b,0x7a120306275d305666f304d8d93044ba4303bcbc3032a8c300dba34007a84400357d4000d2840b,0x8af2130750f2305eb5f3054f8d304c4b430439e8303ad403031d4c300d6a240075ae40033ac4000caf40c,0x8576b3070676305c3cf3053988304b14530428c43039e463031079300ce02400723840031be4000c3d40c,0x805f0306c122305abb530524513049e8030418303038fc7303040f300c5e54006de2400301c4000bd140c,0x7ba17306807b305948b3050fdc3048c5c304082430381bd302f809300be3f40069c94002e614000b6b40c,0x8e87f307a12030644163057e40304fc1d3047acf303f8993037422302ec62300ba0440066cc4002ce74000b0940d,0x8937130757673060b9030568c6304e90730469d1303e98830366f1302e115300b318400631b4002b574000aad40d,0x11a7b620844163071280305d696305540e304d692304595a303daed3035a24302d620300ac8d4005f9b4002a014000a5540e,0x115983207f9ea306d202305bd23305400c304c4b43044964303ccc03034db8302cb7d300a65c4005d0240028984000a0140e,0x1264f52110e40207b479306958a305a76d3052cb6304b36630439e8303befd30341a8302c128300a2c340059d6400276140009b140f,0x136f1321214e8210c5c1207a1203065cc2305927b3051a00304a29e3042ae1303b19f30335f0302b7203009d2040056d3400261a4000964410,0x1478dd2131a00211c7dc2107fd92075ce5306275d3057e4030507e130492573041c48303a4a23032a8c302ad6030097c7400548e40024fe400091c411,0x30720202dc1df0141e78212c8342117da020833c63071cce305f5143056ab2304f652304828a3040e1930398013031f79302a3e530092b140051cf40023d440008d6413,0x32553402fb21502d0b40013c7a921279762113609207efb7306e085305cc1030557c5304e54a3047330304004f3038bb930314b33029aac3008f9d4004f3240022d14000893414,0x31920702ef77002c59cf01374302122d98210f0ee207afaf306a7bd305b7a33054570304d4c23046445303f2e53037fc53030a3730291b43008af64004d3340021c14000854414,0x3361b3030d40002e41e702bad5b01323d6211e46a210ae2c207a120306722e305a3e230533ab304c4b430455c3303e5d73037422303000230288f830086884004ad040020d44000817415,0x32a0f00301afa02d914d02b05b5012d6692119dc52106d9f20761a03063f9b30590c5305226e304b51a30447a6303d92130368cd302f6113028077300824f40048884001fdb40007dd415,0x345e40031e50902f66cd02ce579013c7a92128bb921159832102f2b20725b83060fc83057e4030511b1304a5ef30439e8303ccc03035dc2302ec62302782f3007fa840046c44001f0140007a5416,0x360bf0033a0130312ddb02eb75402c3e4001378be212439f2111781207e6f4306ed22305e2833056c4d305016e304972c3042c87303c0b03035300302e2f1302701d3007bc640044ad4001e1d400076f417,0x354c18032e6770307b4802e0c6902b9b7c0132c9e211fdf2210d7a1207ab8d306b79f305c5b43055ae1304f1a030488cd3041f7d303b4ee3034882302d9be302683f300781040042ac4001d54400073c417,0x36e91803490a1032315302fcd2d02d65e702afd04012e31e211ba9021099c4207a12030684f4305b30530549f7304e23f3047acf30412c8303a9763033e46302d0c430260933007484400411b4001c82400070a418,0x362c58033d977031808b02f236902cc3aa013c7a92129c1821179582105dd120765bf30654ee305a0e73053988304d3483046d2b30406643039e46303344b302c803302591830072384003f434001bc940006db418,0x37b99e03573b20332683030d40002e7ddb02c258e0137cd321257662113a2d21023ae2072d83306275d3058f53305298c304c4b43045fe0303fa4d303935c3032a8c302bf7730251cb3006ef14003d7f4001b0740006ad419,0x370006034bf1703277af0302b9802ddc6502b8b72013348121214e8210fcf4207df58306f833305fc143057e403051a00304b68130452e9303ee8130388b43032109302b7203024aab3006bce4003c194001a5c4000682419,0x387e720364a450340e73031cce002f873502d3ee402af533012ee8e211d480210c192207a7f2306c59a305d2ed3056da93050adc304a8a93044642303e2fc3037e4c30317bf302aefb30243b630068cc4003a7740019aa400065741a,0x37c80d035984d03361b3031260002ee6ba01354be613c7a9212aad9211961221087f1207a120306958a305c04e3055d87304fc1d3049b2830439e8303d7bd30374223030eac302a7063023ceb30066cc40038e6400190b400062f41a,0x393870037153e034ea12032b8c4017feb56153746612b128610672470e547670c74c77104ffa207695d30667d6305af173054dd3304edbd3048dfc3042dd9303ccc03036a3330305cf3029f403023649300640240037a64001865400060841b,0x3a9b6e038854503665fc01d5a5551a2078517303f61483bd612158e60fe0c770de0ee70c11e880a6ff8808f7b09063c553059e5c3053e8a304dfb930481203042212303c203303607e302fd2430297a83022fcd3006155400363240017d240005e241c,0x39e862037d57001fbf8151c59745193fa95166c05613d8f6611816b60f60c370d72c470bb39080a1f9d808b3ab9076cc0a06481fa052fa5304d20d3047491304168f303b7843035700302f4ab302903b30229773005ec240034cc400173940005be41c,0x3b3e9503938700223cb851ea9a951b65865186a00515b15d6133662610f44860ee6b370d09a670b597a809d2d480872a2907360ea061a80a051d93b043d12c04684c3040b4f303ad403034db8302ec6230288f830223453005d0240033ac40016b0400059b41d,0x3a33730344a4302e44730281de3021d363005a9d400326040016214000579409,0x2dc593027aec302174a300584f400312040015a24000558407,0x2741f30088474005618400301c400151d4000539406,0x548e4002ef240014a6400051b404,0x2dd2400142a40004fd403,0x13bb40004e1402,0x4c6401,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def lv : Lv := [(66,32,10,22593),(133,67,19,360330),(201,100,31,1694536),(258,144,43,7021993),(325,179,52,16478280),(308,216,53,11259171),(374,251,55,23691906),(430,292,70,56602265),(496,326,85,108970815),(498,365,81,87248166),(606,399,94,216543570),(670,437,94,318976833),(713,470,131,462754601),(767,517,131,703061061),(796,546,115,571402922),(825,583,168,827402152),(890,620,180,1191172286),(969,667,162,1792765260),(998,694,191,1807183924),(1071,730,182,2273549565),(1134,781,168,3011065680),(1210,811,254,5158192050),(1267,856,259,6680618509),(1275,880,288,5813196699),(1310,918,233,5511128839),(1417,957,284,9264108820),(1470,1013,278,12015102036),(1469,1034,254,8699017795),(1569,1057,325,12494737782),(1606,1119,325,16044725389),(1694,1140,337,18542383231),(1692,1167,359,16663931328),(1794,1200,331,20197037874),(1886,1239,333,24740202870),(1897,1316,351,32157315225),(1954,1315,337,27153483351),(1983,1348,397,30666134394),(2060,1386,393,36092002694),(2137,1421,394,41833802784),(2240,1448,475,55823419004),(2250,1489,500,55210438668),(2284,1525,435,52312765253),(2378,1556,531,68470890338),(2395,1650,476,85741710077),(2422,1650,519,76358763780),(2582,1650,510,85729695318),(2681,1650,535,87808584535),(2811,1650,525,93554333730),(2913,1649,478,85387195336),(2947,1650,488,74858119710),(3384,1650,550,112346800776),(3218,1650,485,85659114905),(3306,1650,517,86718357117),(3384,1650,462,76558720426),(3812,1650,550,112353287970),(3919,1650,550,112353287970),(4012,1650,550,112346800776),(3763,1650,498,74353577804),(3887,1650,484,77047857250),(3888,1650,521,64806337350),(4012,1650,505,67296458850),(4012,1650,550,55978045233),(4012,1650,550,55978045233),(4012,1650,550,45992888700),(4012,1650,550,37260811644),(4012,1650,550,29700927870),(4012,1650,550,17770652448),(4012,1650,550,13234945470),(4012,1650,550,13234945470),(4012,1650,550,9901165962),(4012,1650,550,9540801114),(4012,1650,550,6603790245),(4012,1650,550,5455630845),(4012,1650,550,4474175370),(4012,1650,550,3506446545),(4012,1650,550,2659909488),(4012,1650,550,1926295584),(4012,1650,550,1622402496),(4012,1650,550,1416285585),(4012,1650,550,713698359),(4012,1650,550,441215490),(4012,1650,550,190312017),(4012,1650,550,89634600),(4012,1650,550,33334272),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0)]
def n : ℕ := 188
def ru : ℕ := 189
def rho0 : ℕ := 159
def amax : ℕ := 30
theorem T0 : tabAll 1 ws 0 8 = true := by decide +kernel
theorem T1 : tabAll 1 ws 8 8 = true := by decide +kernel
theorem T2 : tabAll 1 ws 16 8 = true := by decide +kernel
theorem T3 : tabAll 1 ws 24 8 = true := by decide +kernel
theorem T4 : tabAll 1 ws 32 8 = true := by decide +kernel
theorem T5 : tabAll 1 ws 40 8 = true := by decide +kernel
theorem T6 : tabAll 1 ws 48 8 = true := by decide +kernel
theorem T7 : tabAll 1 ws 56 8 = true := by decide +kernel
theorem T8 : tabAll 1 ws 64 8 = true := by decide +kernel
theorem T9 : tabAll 1 ws 72 8 = true := by decide +kernel
theorem T10 : tabAll 1 ws 80 8 = true := by decide +kernel
theorem T11 : tabAll 1 ws 88 8 = true := by decide +kernel
theorem T12 : tabAll 1 ws 96 8 = true := by decide +kernel
theorem T13 : tabAll 1 ws 104 8 = true := by decide +kernel
theorem T14 : tabAll 1 ws 112 8 = true := by decide +kernel
theorem T15 : tabAll 1 ws 120 8 = true := by decide +kernel
theorem T16 : tabAll 1 ws 128 8 = true := by decide +kernel
theorem T17 : tabAll 1 ws 136 8 = true := by decide +kernel
theorem T18 : tabAll 1 ws 144 8 = true := by decide +kernel
theorem T19 : tabAll 1 ws 152 8 = true := by decide +kernel
theorem T20 : tabAll 1 ws 160 8 = true := by decide +kernel
theorem T21 : tabAll 1 ws 168 8 = true := by decide +kernel
theorem T22 : tabAll 1 ws 176 8 = true := by decide +kernel
theorem T23 : tabAll 1 ws 184 4 = true := by decide +kernel
theorem tabOK : Gate61ClassTable.tableOK 1 ws = true := tableOK_of_all ws 1 0 (tabAll_add 1 ws 0 184 4 (tabAll_add 1 ws 0 176 8 (tabAll_add 1 ws 0 168 8 (tabAll_add 1 ws 0 160 8 (tabAll_add 1 ws 0 152 8 (tabAll_add 1 ws 0 144 8 (tabAll_add 1 ws 0 136 8 (tabAll_add 1 ws 0 128 8 (tabAll_add 1 ws 0 120 8 (tabAll_add 1 ws 0 112 8 (tabAll_add 1 ws 0 104 8 (tabAll_add 1 ws 0 96 8 (tabAll_add 1 ws 0 88 8 (tabAll_add 1 ws 0 80 8 (tabAll_add 1 ws 0 72 8 (tabAll_add 1 ws 0 64 8 (tabAll_add 1 ws 0 56 8 (tabAll_add 1 ws 0 48 8 (tabAll_add 1 ws 0 40 8 (tabAll_add 1 ws 0 32 8 (tabAll_add 1 ws 0 24 8 (tabAll_add 1 ws 0 16 8 (tabAll_add 1 ws 0 8 8 (tabAll_add 1 ws 0 0 8 (tabAll_nil 1 ws 0) T0) T1) T2) T3) T4) T5) T6) T7) T8) T9) T10) T11) T12) T13) T14) T15) T16) T17) T18) T19) T20) T21) T22) T23)
theorem C0 : allOK G 1 ws lv 0 1 = true := by decide +kernel
theorem C1 : allOK G 1 ws lv 1 1 = true := by decide +kernel
theorem C2 : allOK G 1 ws lv 2 1 = true := by decide +kernel
theorem C3 : allOK G 1 ws lv 3 1 = true := by decide +kernel
theorem C4 : allOK G 1 ws lv 4 1 = true := by decide +kernel
theorem C5 : allOK G 1 ws lv 5 4 = true := by decide +kernel
theorem C6 : allOK G 1 ws lv 9 4 = true := by decide +kernel
theorem C7 : allOK G 1 ws lv 13 1 = true := by decide +kernel
theorem C8 : allOK G 1 ws lv 14 1 = true := by decide +kernel
theorem C9 : allOK G 1 ws lv 15 1 = true := by decide +kernel
theorem C10 : allOK G 1 ws lv 16 1 = true := by decide +kernel
theorem C11 : allOK G 1 ws lv 17 1 = true := by decide +kernel
theorem C12 : allOK G 1 ws lv 18 1 = true := by decide +kernel
theorem C13 : allOK G 1 ws lv 19 1 = true := by decide +kernel
theorem C14 : allOK G 1 ws lv 20 1 = true := by decide +kernel
theorem C15 : allOK G 1 ws lv 21 1 = true := by decide +kernel
theorem C16 : allOK G 1 ws lv 22 1 = true := by decide +kernel
theorem C17 : allOK G 1 ws lv 23 1 = true := by decide +kernel
theorem C18 : allOK G 1 ws lv 24 1 = true := by decide +kernel
theorem C19 : allOK G 1 ws lv 25 1 = true := by decide +kernel
theorem C20 : allOK G 1 ws lv 26 1 = true := by decide +kernel
theorem C21 : allOK G 1 ws lv 27 1 = true := by decide +kernel
theorem C22 : allOK G 1 ws lv 28 1 = true := by decide +kernel
theorem C23 : allOK G 1 ws lv 29 1 = true := by decide +kernel
theorem C24 : allOK G 1 ws lv 30 1 = true := by decide +kernel
theorem C25 : allOK G 1 ws lv 31 1 = true := by decide +kernel
theorem C26 : allOK G 1 ws lv 32 1 = true := by decide +kernel
theorem C27 : allOK G 1 ws lv 33 1 = true := by decide +kernel
theorem C28 : allOK G 1 ws lv 34 1 = true := by decide +kernel
theorem C29 : allOK G 1 ws lv 35 1 = true := by decide +kernel
theorem C30 : allOK G 1 ws lv 36 1 = true := by decide +kernel
theorem C31 : allOK G 1 ws lv 37 1 = true := by decide +kernel
theorem C32 : allOK G 1 ws lv 38 1 = true := by decide +kernel
theorem C33 : allOK G 1 ws lv 39 1 = true := by decide +kernel
theorem C34 : allOK G 1 ws lv 40 1 = true := by decide +kernel
theorem C35 : allOK G 1 ws lv 41 1 = true := by decide +kernel
theorem C36 : allOK G 1 ws lv 42 1 = true := by decide +kernel
theorem C37 : allOK G 1 ws lv 43 1 = true := by decide +kernel
theorem C38 : allOK G 1 ws lv 44 1 = true := by decide +kernel
theorem C39 : allOK G 1 ws lv 45 1 = true := by decide +kernel
theorem C40 : allOK G 1 ws lv 46 1 = true := by decide +kernel
theorem C41 : allOK G 1 ws lv 47 1 = true := by decide +kernel
theorem C42 : allOK G 1 ws lv 48 1 = true := by decide +kernel
theorem C43 : allOK G 1 ws lv 49 1 = true := by decide +kernel
theorem C44 : allOK G 1 ws lv 50 1 = true := by decide +kernel
theorem C45 : allOK G 1 ws lv 51 1 = true := by decide +kernel
theorem C46 : allOK G 1 ws lv 52 1 = true := by decide +kernel
theorem C47 : allOK G 1 ws lv 53 1 = true := by decide +kernel
theorem C48 : allOK G 1 ws lv 54 1 = true := by decide +kernel
theorem C49 : allOK G 1 ws lv 55 1 = true := by decide +kernel
theorem C50 : allOK G 1 ws lv 56 1 = true := by decide +kernel
theorem C51 : allOK G 1 ws lv 57 1 = true := by decide +kernel
theorem C52 : allOK G 1 ws lv 58 1 = true := by decide +kernel
theorem C53 : allOK G 1 ws lv 59 1 = true := by decide +kernel
theorem C54 : allOK G 1 ws lv 60 1 = true := by decide +kernel
theorem C55 : allOK G 1 ws lv 61 1 = true := by decide +kernel
theorem C56 : allOK G 1 ws lv 62 1 = true := by decide +kernel
theorem C57 : allOK G 1 ws lv 63 1 = true := by decide +kernel
theorem C58 : allOK G 1 ws lv 64 1 = true := by decide +kernel
theorem C59 : allOK G 1 ws lv 65 1 = true := by decide +kernel
theorem C60 : allOK G 1 ws lv 66 1 = true := by decide +kernel
theorem C61 : allOK G 1 ws lv 67 1 = true := by decide +kernel
theorem C62 : allOK G 1 ws lv 68 1 = true := by decide +kernel
theorem C63 : allOK G 1 ws lv 69 1 = true := by decide +kernel
theorem C64 : allOK G 1 ws lv 70 1 = true := by decide +kernel
theorem C65 : allOK G 1 ws lv 71 1 = true := by decide +kernel
theorem C66 : allOK G 1 ws lv 72 1 = true := by decide +kernel
theorem C67 : allOK G 1 ws lv 73 1 = true := by decide +kernel
theorem C68 : allOK G 1 ws lv 74 1 = true := by decide +kernel
theorem C69 : allOK G 1 ws lv 75 1 = true := by decide +kernel
theorem C70 : allOK G 1 ws lv 76 1 = true := by decide +kernel
theorem C71 : allOK G 1 ws lv 77 1 = true := by decide +kernel
theorem C72 : allOK G 1 ws lv 78 1 = true := by decide +kernel
theorem C73 : allOK G 1 ws lv 79 1 = true := by decide +kernel
theorem C74 : allOK G 1 ws lv 80 1 = true := by decide +kernel
theorem C75 : allOK G 1 ws lv 81 1 = true := by decide +kernel
theorem C76 : allOK G 1 ws lv 82 1 = true := by decide +kernel
theorem C77 : allOK G 1 ws lv 83 1 = true := by decide +kernel
theorem C78 : allOK G 1 ws lv 84 1 = true := by decide +kernel
theorem C79 : allOK G 1 ws lv 85 1 = true := by decide +kernel
theorem C80 : allOK G 1 ws lv 86 1 = true := by decide +kernel
theorem C81 : allOK G 1 ws lv 87 1 = true := by decide +kernel
theorem C82 : allOK G 1 ws lv 88 1 = true := by decide +kernel
theorem C83 : allOK G 1 ws lv 89 4 = true := by decide +kernel
theorem C84 : allOK G 1 ws lv 93 24 = true := by decide +kernel
theorem C85 : allOK G 1 ws lv 117 24 = true := by decide +kernel
theorem C86 : allOK G 1 ws lv 141 24 = true := by decide +kernel
theorem C87 : allOK G 1 ws lv 165 23 = true := by decide +kernel
theorem allOKn : allOK G 1 ws lv 0 n = true := allOK_add G 1 ws lv 0 165 23 (allOK_add G 1 ws lv 0 141 24 (allOK_add G 1 ws lv 0 117 24 (allOK_add G 1 ws lv 0 93 24 (allOK_add G 1 ws lv 0 89 4 (allOK_add G 1 ws lv 0 88 1 (allOK_add G 1 ws lv 0 87 1 (allOK_add G 1 ws lv 0 86 1 (allOK_add G 1 ws lv 0 85 1 (allOK_add G 1 ws lv 0 84 1 (allOK_add G 1 ws lv 0 83 1 (allOK_add G 1 ws lv 0 82 1 (allOK_add G 1 ws lv 0 81 1 (allOK_add G 1 ws lv 0 80 1 (allOK_add G 1 ws lv 0 79 1 (allOK_add G 1 ws lv 0 78 1 (allOK_add G 1 ws lv 0 77 1 (allOK_add G 1 ws lv 0 76 1 (allOK_add G 1 ws lv 0 75 1 (allOK_add G 1 ws lv 0 74 1 (allOK_add G 1 ws lv 0 73 1 (allOK_add G 1 ws lv 0 72 1 (allOK_add G 1 ws lv 0 71 1 (allOK_add G 1 ws lv 0 70 1 (allOK_add G 1 ws lv 0 69 1 (allOK_add G 1 ws lv 0 68 1 (allOK_add G 1 ws lv 0 67 1 (allOK_add G 1 ws lv 0 66 1 (allOK_add G 1 ws lv 0 65 1 (allOK_add G 1 ws lv 0 64 1 (allOK_add G 1 ws lv 0 63 1 (allOK_add G 1 ws lv 0 62 1 (allOK_add G 1 ws lv 0 61 1 (allOK_add G 1 ws lv 0 60 1 (allOK_add G 1 ws lv 0 59 1 (allOK_add G 1 ws lv 0 58 1 (allOK_add G 1 ws lv 0 57 1 (allOK_add G 1 ws lv 0 56 1 (allOK_add G 1 ws lv 0 55 1 (allOK_add G 1 ws lv 0 54 1 (allOK_add G 1 ws lv 0 53 1 (allOK_add G 1 ws lv 0 52 1 (allOK_add G 1 ws lv 0 51 1 (allOK_add G 1 ws lv 0 50 1 (allOK_add G 1 ws lv 0 49 1 (allOK_add G 1 ws lv 0 48 1 (allOK_add G 1 ws lv 0 47 1 (allOK_add G 1 ws lv 0 46 1 (allOK_add G 1 ws lv 0 45 1 (allOK_add G 1 ws lv 0 44 1 (allOK_add G 1 ws lv 0 43 1 (allOK_add G 1 ws lv 0 42 1 (allOK_add G 1 ws lv 0 41 1 (allOK_add G 1 ws lv 0 40 1 (allOK_add G 1 ws lv 0 39 1 (allOK_add G 1 ws lv 0 38 1 (allOK_add G 1 ws lv 0 37 1 (allOK_add G 1 ws lv 0 36 1 (allOK_add G 1 ws lv 0 35 1 (allOK_add G 1 ws lv 0 34 1 (allOK_add G 1 ws lv 0 33 1 (allOK_add G 1 ws lv 0 32 1 (allOK_add G 1 ws lv 0 31 1 (allOK_add G 1 ws lv 0 30 1 (allOK_add G 1 ws lv 0 29 1 (allOK_add G 1 ws lv 0 28 1 (allOK_add G 1 ws lv 0 27 1 (allOK_add G 1 ws lv 0 26 1 (allOK_add G 1 ws lv 0 25 1 (allOK_add G 1 ws lv 0 24 1 (allOK_add G 1 ws lv 0 23 1 (allOK_add G 1 ws lv 0 22 1 (allOK_add G 1 ws lv 0 21 1 (allOK_add G 1 ws lv 0 20 1 (allOK_add G 1 ws lv 0 19 1 (allOK_add G 1 ws lv 0 18 1 (allOK_add G 1 ws lv 0 17 1 (allOK_add G 1 ws lv 0 16 1 (allOK_add G 1 ws lv 0 15 1 (allOK_add G 1 ws lv 0 14 1 (allOK_add G 1 ws lv 0 13 1 (allOK_add G 1 ws lv 0 9 4 (allOK_add G 1 ws lv 0 5 4 (allOK_add G 1 ws lv 0 4 1 (allOK_add G 1 ws lv 0 3 1 (allOK_add G 1 ws lv 0 2 1 (allOK_add G 1 ws lv 0 1 1 (allOK_add G 1 ws lv 0 0 1 (allOK_nil G 1 ws lv 0) C0) C1) C2) C3) C4) C5) C6) C7) C8) C9) C10) C11) C12) C13) C14) C15) C16) C17) C18) C19) C20) C21) C22) C23) C24) C25) C26) C27) C28) C29) C30) C31) C32) C33) C34) C35) C36) C37) C38) C39) C40) C41) C42) C43) C44) C45) C46) C47) C48) C49) C50) C51) C52) C53) C54) C55) C56) C57) C58) C59) C60) C61) C62) C63) C64) C65) C66) C67) C68) C69) C70) C71) C72) C73) C74) C75) C76) C77) C78) C79) C80) C81) C82) C83) C84) C85) C86) C87
end Gate61DatG38
