import ProximityPrize.SubmissionLower.Gate61Assm
set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 400000
set_option Elab.async false
namespace Gate61DatG47
open Gate61Cell
def G : Gt := { m00 := 0, m01 := 562774298947744, m02 := 1689462692225760, m11 := 4064084262423232, m12 := 12480051121358016, m22 := 37442432954839104, xb := 140, xj := 41, xt := 13, lb := 140, lj := 41, lt := 13, A := 183902167141590202, sc := 32, lift := true }
def ws : List ℕ := [0x0,0x0,0x0,0x0,0x7a120301,0x57e40301,0x4c4b4301,0x439e8301,0x3ccc0301,0x7a1203037422302,0x6275d3032a8c302,0x57e4030127ee402,0x51a00300fa67402,0x4c4b4300d6a2402,0x7a1203047acf300ba04403,0x6958a30439e8300a2c3403,0x5cc10304004f3008f9d403,0x57e40303ccc03007fa8403,0x539883039e463007238403,0x4fc1d303742230066cc403,0x6d202304c4b43034db83005d02404,0x6275d30492573032a8c300548e404,0x5b7a330464453013f084004d33404,0x57e4030439e830127ee40046c4404,0x549f730412c83010c9e400411b404,0x6f8333051a00303ee81300fa674003c19405,0x667d6304edbd303ccc0300e53c40037a6405,0x5eb5f304c4b4303ad40300d6a240033ac405,0x5abb53049e803038fc7300c5e5400301c405,0x57e403047acf3037422300ba044002ce7405,0x71280305540e304595a3035a24300ac8d4002a01406,0x6958a3052cb630439e830341a8300a2c34002761406,0x6275d30507e13041c483032a8c30097c740024fe406,0x7efb7305cc10304e54a304004f3014a6e4008f9d40022d1407,0x7a120305a3e2304c4b4303e5d73013436400868840020d4407,0x725b83057e40304a5ef303ccc030127ee4007fa84001f01407,0x6b79f3055ae130488cd303b4ee301154a40078104001d54407,0x8576b30654ee30539883046d2b3039e46301045840072384001bc9408,0x7df58305fc143051a0030452e930388b4300fa674006bce4001a5c408,0x9bcf5307a120305c04e304fc1d30439e83037422300ebfc40066cc400190b409,0x92ef530734603059e5c304dfb93042212303607e300dec4400615540017d2409,0x8af21306d2023057e40304c4b43040b4f3034db8300d6a24005d0240016b0409,0x83b9930678b53055fce304aaf1303f58c3033bc2300cb40400584f40015a2409,0x9fa36307d2c8306275d30542dd3049257303e0b73032a8c300c0bf400548e40014a640a,0x7a120305dd06305274d3047acf303ccc03031a0d300ba04400507d40013bb409,0x8fa3d3073feb305b7a33050cff3046445303b9993013f08400b0e04004d3340012df40a,0x88b42306e70a3059a40304f3db3044ea8303a7343012f01400a86340049a9400121240a,0x825d2306958a3057e40304dbc930439e8303958530127ee400a2c340046c4400115140a,0x7c8d63064a993056386304c4b430425f7303848330119c84009b5040043aa400109c40a,0x7a120306058230549f7304ae8d30412c830374223010c9e400945c400411b4000ff240a,0x8d0b33074940305cc10305317c3049942304004f303645930100594008f9d4003e5f4000f5240b,0x86eb2306f833305b0fb3051a0030484c4303ee813035521300fa6740089764003c194000ebb40b,0x81451306ad44305971330503703047108303dd543034671300ef7840083b140039ad4000e2d40b,0x7c0c430667d63057e40304edbd3045e01303ccc03033842300e53c4007fa840037a64000da740b,0x7a120306275d305666f304d8d93044ba4303bcbc3032a8c300dba34007a84400357d4000d2840b,0xa8288308af2130750f2305eb5f3054f8d304c4b430439e8303ad403031d4c300d6a240075ae40033ac4000caf40d,0xcca3130c226d30a100e308576b3070676305c3cf3053988304b14530428c43039e463031079300ce02400723840031be4000c3d40f,0x19d5c5217f4c221635cf20cb73630b9938309a61a30805f0306c122305abb530524513049e8030418303038fc7303040f300c5e54006de2400301c4000bd1412,0x1d59ab21b33cf2193ee721770d620dcd7f30cb73630b1a6730943d4307ba17306807b305948b3050fdc3048c5c304082430381bd302f809300be3f40069c94002e614000b6b414,0x21672721edf2e21c9c3821a906b218b09c216f3d020d38d530cb73630aa4f0308e87f307a12030644163057e40304fc1d3047acf303f8993037422302ec62300ba0440066cc4002ce74000b09416,0x196e6b3232526220747f21e10d721beb00219f6b62182a132167d1220cb73630c2bf830a37ea308937130757673060b9030568c6304e90730469d1303e98830366f1302e115300b318400631b4002b574000aad418,0x21e88f31ace55324f9362221b9821f937f21d505921b44b921965bd217aa9420e346830cb73630baae3309d28630844163071280305d696305540e304d692304595a303daed3035a2430111c5400ac8d4005f9b4002a014000a5541a,0x47868c01eee143196e6b323d672221260621ec22b21c9c3821aa848218dcac217318020da08230cb73630b32fc309740e307f9ea306d202305bd23305400c304c4b43044964303ccc03034db8301079b400a65c4005d0240028984000a0141b,0x4886bf0230dd231c1bba3196e6b322ca40220422821dfecb21bf32e21a14ba2185ac9216be4c20d178f30cb73630ac3673091be0307b479306958a305a76d3052cb6304b36630439e8303befd30341a8300fdff400a2c340059d6400276140009b141c,0x4968cd0272d903201fb03196e6b3248203221d20321f6e0521d47e721b541e2198936217df7220e94b130cb73630c345d30a5b5e308c96e307a1203065cc2305927b3051a00304a29e3042ae1303b19f30335f0300fa674009d2040056d3400261a400096441d,0x48ba2d02423a631d58053196e6b3237371220eb7b21ea7ed21c9c3821abe1121905022176a1720e01d130cb73630bba80309fa363087c363075ce5306275d3057e4030507e130492573041c48303a4a23032a8c300f19940097c7400548e40024fe400091c41d,0x49902e028279b32141a031ab3f03196e6b32278c222014b921dee6a21bfaa421a30302188778216fa3b20d796b30cb73630b48cf3099f5230833c63071cce305f5143056ab2304f652304828a3040e1930398013031f79300e93f40092b140051cf40023d440008d641e,0x4a49a602c2b913252b3a31e84803196e6b3196e6b3218fc421f4c1221d403721b6231219a9bd218100820eeef230cfa8030cb73630ade903094a28307efb7306e085305cc1030557c5304e54a3047330304004f3038bb930314b3300e1524008f9d4004f3240022d1400089341f,0x49b47d02914d4322551031be9953196e6b3231a89220b69121e901321c9c3821ad2082192a122179e3120e5d4b31301eb6104ef370de7fd70bc615809e2fe806a7bd305b7a33054570304d4c23046445303f2e53037fc53030a37300d9ca4008af64004d3340021c1400085441f,0x2cfe6e32625a031fa2533196e6b3196e6b3222f4721feb8321ddf7b21c017821a496921c06bf5186a005152d98612489160fb2e470d655b70b597a8098968807efe1906881ea054dd2b04c4b430455c3303e5d730374223030002300d6a240086884004ad040020d4400081741f,0x29f6303235b1231d107a3196e6b3196e6b32153cf21f2d2d21d392f22308c751ec25351aeaa0517774f6145f14611999c60f1f6c70ce9c970af2a3809347f907aa6b9064feba0520f0b0419c9d03371fe03d92130368cd302f611300cfb1400824f40048884001fdb40007dd41f,0x2713d0320b28a31a9d3b3196e6b3196e6b320868221e7a4e22625a04219e7151d8a80519df0e516927a6139c23610f44860e93ec70c74c770a9129808e3f09076875a061a80a04f63ec03f832d031d32e03ccc03035dc2302ec62300c9154007fa840046c44001f0140007a541f,0x24549931e29a93196e6b3196e6b321ecaf21fc5f622964624249b1952049a051c64d7518e2c6515ba7b612e3ee61057e370e0fd570c05df80a34af808977190729c5a05e7b1b04cd99c03d831d03047af03c0b03035300302e2f1300c2c84007bc640044ad4001e1d400076f41f,0x21b61731bbe463196e6b3196e6b3325b2842cc50c427b84b423280051f08aa51b4ff5517f4a2614ee5f61235ad60fc3cc70d92a170b9ca7809dcde8084ebd906ee23a05b752b04a6dfc03b9add02ece4f03b4ee3034882302d9be300bcc5400781040042ac4001d54400073c41f,0x1f360f3196e6b3196e6b33627be430479f42af60642625a0421ca8551dda0951a4a9a517139a6142d4b61190ac60f376e70d1bd970b38bd80989688080995906b55fa05893cb0481f3c039c8fd02d65ff03a9763033e463010c9e400ba044007484400411b4001c82400070a41f,0x1cd2793196e6b33a17b1433ec1a42e544b4294280424aa6a520810251cbc6151953a05163ebc6137677610f44860eb24470cab0e70ad9c88093a05907c7be9067f48a055d4bb045eb7c0380c1e02c0daf039e46303344b3010458400b47240072384003f434001bc940006db41f,0x1a897b33e2b02437b27e431d31b42c7ea0427a85942344df51f49f851bae715186a00515752a612c92d6105fe870e33d070c3fda80a7f74808ee7090789049064bb6a05335db043d12c03662fe03fa4d303935c3032a8c300fc72400af204006ef14003d7f4001b0740006ad41f,0x196e6b33b9aca435727442fda0042ac45142625a0421f36051e240d51aaf195178cc8614b61d61224c560fd30370dbba070bd9e180a2975808a66e9074d34a061a80a050b53b041cecd034cc7e03ee8130388b43032109300fa67400aa094006bce4003c194001a5c400068241f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def lv : Lv := [(89,25,9,9245),(187,52,18,144515),(317,75,26,701407),(412,100,35,1769454),(514,125,45,4149222),(642,148,53,8451794),(722,175,62,15785656),(824,200,72,26416350),(915,229,81,54402128),(1090,244,89,57219330),(1197,270,98,93231408),(1288,296,106,131901426),(1381,324,116,207799410),(1515,350,124,337386458),(1633,366,133,281366192),(1712,393,141,369797158),(1836,420,150,567332590),(1949,448,155,838696338),(2109,472,167,1188072486),(2257,497,176,1642769466),(2230,522,185,1320256344),(2375,546,194,1725766542),(2540,570,202,2337023865),(2688,595,206,3078493799),(2841,619,220,3949151980),(2809,644,228,3237152940),(2970,668,237,4165217760),(3130,692,246,5277778758),(3276,717,239,6613545528),(3423,741,247,8118549516),(3416,765,234,6922503640),(3572,789,280,8483995444),(3716,814,289,10348564820),(3692,839,298,9043882155),(3854,863,306,11010395367),(3838,900,319,13007262672),(3976,926,329,15618325860),(3895,954,341,13448562438),(3994,983,352,16051673092),(4006,1005,356,14372593227),(4009,1040,358,16479100092),(4010,1077,386,19351891492),(4012,1117,388,23645427883),(4012,1137,397,20467058634),(4010,1190,424,30222607326),(4012,1209,435,26125231173),(4012,1250,378,31298829723),(4012,1285,461,34393272911),(4011,1322,473,38504251938),(4012,1360,483,43498456576),(4012,1380,464,38721329880),(4012,1419,509,44094302055),(4012,1458,487,49920279868),(4012,1492,444,52596702401),(4011,1530,547,58638874582),(4012,1556,550,56899046376),(4012,1591,550,60777974808),(4012,1619,550,60195155184),(4012,1650,550,61669256755),(4012,1650,550,45128482785),(4012,1650,550,32229139293),(4012,1650,550,22464186597),(4012,1650,550,15141925708),(4012,1650,550,9725385345),(4012,1650,550,5954903493),(4012,1650,550,3339232270),(4012,1650,550,1684239867),(4012,1650,550,713698359),(4012,1650,550,29847644028),(4012,1650,550,46766477610),(4012,1650,550,63240563542),(4012,1650,550,48671933002),(4012,1650,550,34367193499),(4012,1650,550,20129614809),(3999,1650,550,509267001),(4012,1650,550,81751285),(4012,1650,550,3321960),(4012,1650,550,0),(3943,1547,550,1126537335),(4012,1563,550,1104475905),(3516,1650,550,1218104265),(3722,1650,540,1278098745),(3929,1650,550,1365780850),(4012,1650,550,377396635),(4012,1650,550,5563251),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0)]
def n : ℕ := 210
def ru : ℕ := 211
def rho0 : ℕ := 183
def amax : ℕ := 28
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
theorem T23 : tabAll 1 ws 184 8 = true := by decide +kernel
theorem T24 : tabAll 1 ws 192 7 = true := by decide +kernel
theorem tabOK : Gate61ClassTable.tableOK 1 ws = true := tableOK_of_all ws 1 0 (tabAll_add 1 ws 0 192 7 (tabAll_add 1 ws 0 184 8 (tabAll_add 1 ws 0 176 8 (tabAll_add 1 ws 0 168 8 (tabAll_add 1 ws 0 160 8 (tabAll_add 1 ws 0 152 8 (tabAll_add 1 ws 0 144 8 (tabAll_add 1 ws 0 136 8 (tabAll_add 1 ws 0 128 8 (tabAll_add 1 ws 0 120 8 (tabAll_add 1 ws 0 112 8 (tabAll_add 1 ws 0 104 8 (tabAll_add 1 ws 0 96 8 (tabAll_add 1 ws 0 88 8 (tabAll_add 1 ws 0 80 8 (tabAll_add 1 ws 0 72 8 (tabAll_add 1 ws 0 64 8 (tabAll_add 1 ws 0 56 8 (tabAll_add 1 ws 0 48 8 (tabAll_add 1 ws 0 40 8 (tabAll_add 1 ws 0 32 8 (tabAll_add 1 ws 0 24 8 (tabAll_add 1 ws 0 16 8 (tabAll_add 1 ws 0 8 8 (tabAll_add 1 ws 0 0 8 (tabAll_nil 1 ws 0) T0) T1) T2) T3) T4) T5) T6) T7) T8) T9) T10) T11) T12) T13) T14) T15) T16) T17) T18) T19) T20) T21) T22) T23) T24)
theorem C0 : allOK G 1 ws lv 0 1 = true := by decide +kernel
theorem C1 : allOK G 1 ws lv 1 1 = true := by decide +kernel
theorem C2 : allOK G 1 ws lv 2 1 = true := by decide +kernel
theorem C3 : allOK G 1 ws lv 3 1 = true := by decide +kernel
theorem C4 : allOK G 1 ws lv 4 4 = true := by decide +kernel
theorem C5 : allOK G 1 ws lv 8 4 = true := by decide +kernel
theorem C6 : allOK G 1 ws lv 12 2 = true := by decide +kernel
theorem C7 : allOK G 1 ws lv 14 1 = true := by decide +kernel
theorem C8 : allOK G 1 ws lv 15 1 = true := by decide +kernel
theorem C9 : allOK G 1 ws lv 16 1 = true := by decide +kernel
theorem C10 : allOK G 1 ws lv 17 1 = true := by decide +kernel
theorem C11 : allOK G 1 ws lv 18 1 = true := by decide +kernel
theorem C12 : allOK G 1 ws lv 19 1 = true := by decide +kernel
theorem C13 : allOK G 1 ws lv 20 1 = true := by decide +kernel
theorem C14 : allOK G 1 ws lv 21 1 = true := by decide +kernel
theorem C15 : allOK G 1 ws lv 22 1 = true := by decide +kernel
theorem C16 : allOK G 1 ws lv 23 1 = true := by decide +kernel
theorem C17 : allOK G 1 ws lv 24 1 = true := by decide +kernel
theorem C18 : allOK G 1 ws lv 25 1 = true := by decide +kernel
theorem C19 : allOK G 1 ws lv 26 1 = true := by decide +kernel
theorem C20 : allOK G 1 ws lv 27 1 = true := by decide +kernel
theorem C21 : allOK G 1 ws lv 28 1 = true := by decide +kernel
theorem C22 : allOK G 1 ws lv 29 1 = true := by decide +kernel
theorem C23 : allOK G 1 ws lv 30 1 = true := by decide +kernel
theorem C24 : allOK G 1 ws lv 31 1 = true := by decide +kernel
theorem C25 : allOK G 1 ws lv 32 1 = true := by decide +kernel
theorem C26 : allOK G 1 ws lv 33 1 = true := by decide +kernel
theorem C27 : allOK G 1 ws lv 34 1 = true := by decide +kernel
theorem C28 : allOK G 1 ws lv 35 1 = true := by decide +kernel
theorem C29 : allOK G 1 ws lv 36 1 = true := by decide +kernel
theorem C30 : allOK G 1 ws lv 37 1 = true := by decide +kernel
theorem C31 : allOK G 1 ws lv 38 1 = true := by decide +kernel
theorem C32 : allOK G 1 ws lv 39 1 = true := by decide +kernel
theorem C33 : allOK G 1 ws lv 40 1 = true := by decide +kernel
theorem C34 : allOK G 1 ws lv 41 1 = true := by decide +kernel
theorem C35 : allOK G 1 ws lv 42 1 = true := by decide +kernel
theorem C36 : allOK G 1 ws lv 43 1 = true := by decide +kernel
theorem C37 : allOK G 1 ws lv 44 1 = true := by decide +kernel
theorem C38 : allOK G 1 ws lv 45 1 = true := by decide +kernel
theorem C39 : allOK G 1 ws lv 46 1 = true := by decide +kernel
theorem C40 : allOK G 1 ws lv 47 1 = true := by decide +kernel
theorem C41 : allOK G 1 ws lv 48 1 = true := by decide +kernel
theorem C42 : allOK G 1 ws lv 49 1 = true := by decide +kernel
theorem C43 : allOK G 1 ws lv 50 1 = true := by decide +kernel
theorem C44 : allOK G 1 ws lv 51 1 = true := by decide +kernel
theorem C45 : allOK G 1 ws lv 52 1 = true := by decide +kernel
theorem C46 : allOK G 1 ws lv 53 1 = true := by decide +kernel
theorem C47 : allOK G 1 ws lv 54 1 = true := by decide +kernel
theorem C48 : allOK G 1 ws lv 55 1 = true := by decide +kernel
theorem C49 : allOK G 1 ws lv 56 1 = true := by decide +kernel
theorem C50 : allOK G 1 ws lv 57 1 = true := by decide +kernel
theorem C51 : allOK G 1 ws lv 58 1 = true := by decide +kernel
theorem C52 : allOK G 1 ws lv 59 1 = true := by decide +kernel
theorem C53 : allOK G 1 ws lv 60 1 = true := by decide +kernel
theorem C54 : allOK G 1 ws lv 61 1 = true := by decide +kernel
theorem C55 : allOK G 1 ws lv 62 1 = true := by decide +kernel
theorem C56 : allOK G 1 ws lv 63 1 = true := by decide +kernel
theorem C57 : allOK G 1 ws lv 64 1 = true := by decide +kernel
theorem C58 : allOK G 1 ws lv 65 1 = true := by decide +kernel
theorem C59 : allOK G 1 ws lv 66 1 = true := by decide +kernel
theorem C60 : allOK G 1 ws lv 67 1 = true := by decide +kernel
theorem C61 : allOK G 1 ws lv 68 1 = true := by decide +kernel
theorem C62 : allOK G 1 ws lv 69 1 = true := by decide +kernel
theorem C63 : allOK G 1 ws lv 70 1 = true := by decide +kernel
theorem C64 : allOK G 1 ws lv 71 1 = true := by decide +kernel
theorem C65 : allOK G 1 ws lv 72 1 = true := by decide +kernel
theorem C66 : allOK G 1 ws lv 73 1 = true := by decide +kernel
theorem C67 : allOK G 1 ws lv 74 1 = true := by decide +kernel
theorem C68 : allOK G 1 ws lv 75 1 = true := by decide +kernel
theorem C69 : allOK G 1 ws lv 76 1 = true := by decide +kernel
theorem C70 : allOK G 1 ws lv 77 1 = true := by decide +kernel
theorem C71 : allOK G 1 ws lv 78 4 = true := by decide +kernel
theorem C72 : allOK G 1 ws lv 82 4 = true := by decide +kernel
theorem C73 : allOK G 1 ws lv 86 24 = true := by decide +kernel
theorem C74 : allOK G 1 ws lv 110 24 = true := by decide +kernel
theorem C75 : allOK G 1 ws lv 134 24 = true := by decide +kernel
theorem C76 : allOK G 1 ws lv 158 24 = true := by decide +kernel
theorem C77 : allOK G 1 ws lv 182 24 = true := by decide +kernel
theorem C78 : allOK G 1 ws lv 206 4 = true := by decide +kernel
theorem allOKn : allOK G 1 ws lv 0 n = true := allOK_add G 1 ws lv 0 206 4 (allOK_add G 1 ws lv 0 182 24 (allOK_add G 1 ws lv 0 158 24 (allOK_add G 1 ws lv 0 134 24 (allOK_add G 1 ws lv 0 110 24 (allOK_add G 1 ws lv 0 86 24 (allOK_add G 1 ws lv 0 82 4 (allOK_add G 1 ws lv 0 78 4 (allOK_add G 1 ws lv 0 77 1 (allOK_add G 1 ws lv 0 76 1 (allOK_add G 1 ws lv 0 75 1 (allOK_add G 1 ws lv 0 74 1 (allOK_add G 1 ws lv 0 73 1 (allOK_add G 1 ws lv 0 72 1 (allOK_add G 1 ws lv 0 71 1 (allOK_add G 1 ws lv 0 70 1 (allOK_add G 1 ws lv 0 69 1 (allOK_add G 1 ws lv 0 68 1 (allOK_add G 1 ws lv 0 67 1 (allOK_add G 1 ws lv 0 66 1 (allOK_add G 1 ws lv 0 65 1 (allOK_add G 1 ws lv 0 64 1 (allOK_add G 1 ws lv 0 63 1 (allOK_add G 1 ws lv 0 62 1 (allOK_add G 1 ws lv 0 61 1 (allOK_add G 1 ws lv 0 60 1 (allOK_add G 1 ws lv 0 59 1 (allOK_add G 1 ws lv 0 58 1 (allOK_add G 1 ws lv 0 57 1 (allOK_add G 1 ws lv 0 56 1 (allOK_add G 1 ws lv 0 55 1 (allOK_add G 1 ws lv 0 54 1 (allOK_add G 1 ws lv 0 53 1 (allOK_add G 1 ws lv 0 52 1 (allOK_add G 1 ws lv 0 51 1 (allOK_add G 1 ws lv 0 50 1 (allOK_add G 1 ws lv 0 49 1 (allOK_add G 1 ws lv 0 48 1 (allOK_add G 1 ws lv 0 47 1 (allOK_add G 1 ws lv 0 46 1 (allOK_add G 1 ws lv 0 45 1 (allOK_add G 1 ws lv 0 44 1 (allOK_add G 1 ws lv 0 43 1 (allOK_add G 1 ws lv 0 42 1 (allOK_add G 1 ws lv 0 41 1 (allOK_add G 1 ws lv 0 40 1 (allOK_add G 1 ws lv 0 39 1 (allOK_add G 1 ws lv 0 38 1 (allOK_add G 1 ws lv 0 37 1 (allOK_add G 1 ws lv 0 36 1 (allOK_add G 1 ws lv 0 35 1 (allOK_add G 1 ws lv 0 34 1 (allOK_add G 1 ws lv 0 33 1 (allOK_add G 1 ws lv 0 32 1 (allOK_add G 1 ws lv 0 31 1 (allOK_add G 1 ws lv 0 30 1 (allOK_add G 1 ws lv 0 29 1 (allOK_add G 1 ws lv 0 28 1 (allOK_add G 1 ws lv 0 27 1 (allOK_add G 1 ws lv 0 26 1 (allOK_add G 1 ws lv 0 25 1 (allOK_add G 1 ws lv 0 24 1 (allOK_add G 1 ws lv 0 23 1 (allOK_add G 1 ws lv 0 22 1 (allOK_add G 1 ws lv 0 21 1 (allOK_add G 1 ws lv 0 20 1 (allOK_add G 1 ws lv 0 19 1 (allOK_add G 1 ws lv 0 18 1 (allOK_add G 1 ws lv 0 17 1 (allOK_add G 1 ws lv 0 16 1 (allOK_add G 1 ws lv 0 15 1 (allOK_add G 1 ws lv 0 14 1 (allOK_add G 1 ws lv 0 12 2 (allOK_add G 1 ws lv 0 8 4 (allOK_add G 1 ws lv 0 4 4 (allOK_add G 1 ws lv 0 3 1 (allOK_add G 1 ws lv 0 2 1 (allOK_add G 1 ws lv 0 1 1 (allOK_add G 1 ws lv 0 0 1 (allOK_nil G 1 ws lv 0) C0) C1) C2) C3) C4) C5) C6) C7) C8) C9) C10) C11) C12) C13) C14) C15) C16) C17) C18) C19) C20) C21) C22) C23) C24) C25) C26) C27) C28) C29) C30) C31) C32) C33) C34) C35) C36) C37) C38) C39) C40) C41) C42) C43) C44) C45) C46) C47) C48) C49) C50) C51) C52) C53) C54) C55) C56) C57) C58) C59) C60) C61) C62) C63) C64) C65) C66) C67) C68) C69) C70) C71) C72) C73) C74) C75) C76) C77) C78
end Gate61DatG47
