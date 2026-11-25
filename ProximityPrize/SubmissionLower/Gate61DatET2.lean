import ProximityPrize.SubmissionLower.Gate61Assm
set_option autoImplicit false
set_option maxRecDepth 400000
set_option maxHeartbeats 8000000
set_option Elab.async false
namespace Gate61DatET2
open Gate61Cell
def G : Gt := { m00 := 0, m01 := 47854454571521280, m02 := 155116782453707520, m11 := 201894506240791680, m12 := 789888822636696960, m22 := 2392773305388378240, xb := 138, xj := 58, xt := 14, lb := 85, lj := 52, lt := 2, A := 231623317742482350, sc := 1920, lift := false }
def ws : List ℕ := [0x0,0x0,0x0,0x0,0x0,0x57e40301,0x4c4b4301,0x439e8301,0x3ccc0301,0x37422301,0x32a8c301,0x57e4030127ee402,0x51a00300fa67402,0x4c4b4300d6a2402,0x47acf300ba04402,0x439e8300a2c3402,0x5cc10304004f3008f9d403,0x57e40303ccc03007fa8403,0x539883039e463007238403,0x4fc1d303742230066cc403,0x4c4b43034db83005d02403,0x492573032a8c300548e403,0x5b7a330464453030a373004d33404,0x57e4030439e830127ee40046c4404,0x549f730412c83010c9e400411b404,0x51a00303ee81300fa674003c19404,0x4edbd303ccc0300e53c40037a6404,0x4c4b4303ad40300d6a240033ac404,0x5abb53049e803038fc7300c5e5400301c405,0x57e403047acf3037422300ba044002ce7405,0x5540e304595a3035a24300ac8d4002a01405,0x52cb630439e830341a8300a2c34002761405,0x507e13041c483032a8c30097c740024fe405,0x5cc10304e54a304004f30314b33008f9d40022d1406,0x5a3e2304c4b4303e5d73013436400868840020d4406,0x57e40304a5ef303ccc030127ee4007fa84001f01406,0x55ae130488cd303b4ee301154a40078104001d54406,0x539883046d2b3039e46301045840072384001bc9406,0x51a0030452e930388b4300fa674006bce4001a5c406,0x5c04e304fc1d30439e83037422300ebfc40066cc400190b407,0x59e5c304dfb93042212303607e300dec4400615540017d2407,0x57e40304c4b43040b4f3034db8300d6a24005d0240016b0407,0x55fce304aaf1303f58c3033bc2300cb40400584f40015a2407,0x542dd3049257303e0b73032a8c300c0bf400548e40014a6407,0x5dd06305274d3047acf303ccc03031a0d300ba04400507d40013bb408,0x5b7a33050cff3046445303b9993030a37300b0e04004d3340012df408,0x59a40304f3db3044ea8303a7343012f01400a86340049a94001212408,0x57e40304dbc930439e8303958530127ee400a2c340046c44001151408,0x56386304c4b430425f7303848330119c84009b5040043aa400109c408,0x6058230549f7304ae8d30412c830374223010c9e400945c400411b4000ff2409,0x5cc10305317c3049942304004f303645930100594008f9d4003e5f4000f52409,0x5b0fb3051a0030484c4303ee813035521300fa6740089764003c194000ebb409,0x5971330503703047108303dd543034671300ef7840083b140039ad4000e2d409,0x57e40304edbd3045e01303ccc03033842300e53c4007fa840037a64000da7409,0x5666f304d8d93044ba4303bcbc3032a8c300dba34007a84400357d4000d28409,0x5eb5f3054f8d304c4b430439e8303ad403031d4c300d6a240075ae40033ac4000caf40a,0x5c3cf3053988304b14530428c43039e463031079300ce02400723840031be4000c3d40a,0x5abb530524513049e8030418303038fc73013879400c5e54006de2400301c4000bd140a,0x6807b305948b3050fdc3048c5c304082430381bd3012bf2400be3f40069c94002e614000b6b40b,0x7a12030644163057e40304fc1d3047acf303f899303742230127ee400ba0440066cc4002ce74000b0940c,0x8937130757673060b9030568c6304e90730469d1303e98830366f13011c87400b318400631b4002b574000aad40d,0x9d28630844163071280305d696305540e304d692304595a303daed3035a2430111c5400ac8d4005f9b4002a014000a5540e,0xb32fc309740e307f9ea306d202305bd23305400c304c4b43044964303ccc030180fd401079b400a65c4005d0240028984000a0140f,0x13c7a920ac3673091be0307b479306958a305a76d3052cb6304b36630439e8303befd3017276400fdff400a2c340059d6400276140009b1410,0xcb73630c345d30a5b5e308c96e307a1203065cc2305927b3051a00304a29e3042ae1303b19f30164bc400fa674009d2040056d3400261a4000964411,0xcb73630bba80309fa363087c363075ce5306275d3057e4030507e130492573041c48303a4a2301631e400f19940097c7400548e40024fe400091c411,0xd796b30cb73630b48cf3099f5230833c63071cce305f5143056ab2304f652304828a3040e1930398013015671400e93f40092b140051cf40023d440008d6412,0xeeef230cfa8030cb73630ade903094a28307efb7306e085305cc1030557c5304e54a3047330304004f301bfdf4014a6e400e1524008f9d4004f3240022d14000893413,0x179e3120e5d4b30cb73630c3bce30a7b1c308fa3d307afaf306a7bd305b7a33054570304d4c23046445303f2e5301b2084013f08400d9ca4008af64004d3340021c14000854414,0x18b09c20fde8030dd5a930cb73630bc86630a1de1308af21307a120306722e305a3e230533ab304c4b430455c33022956401b2084013436400d6a240086884004ad040020d44000817415,0x19c7ae211800030f43b230d572330cb73630b5c50309c65a308687130761a03063f9b30590c5305226e304b51a30447a63021e89401a31d40129ee400cfb1400824f40048884001fdb40007dd416,0x1ae46421343ab310d00f30eb36b30ce0e830cb73630af6ed309740e30825d230725b83060fc83057e4030511b1304a5ef30439e83021e8940194f140127ee400c9154007fa840046c44001f0140007a5417,0x1c07be21a60a82127c853102c3a30e2cbb30cb73630c427230a97b13092693307e6f4306ed22305e2833056c4d305016e304972c302a0e74020bf3401877a4011e62400c2c84007bc640044ad4001e1d400076f418,0x1d32bb21b7b002144ad9311c33830f936830daec930cb73630bd4d930a3e1c308dd88307ab8d306b79f305c5b43055ae1304f1a030488cd3028985401fa4a4017aa9401154a400bcc5400781040042ac4001d54400073c419,0x1c9c3821af5562137a11311168230f04a130d38d530cb73630b6dd8309e9bb3089895307a12030684f4305b30530549f7304e23f3047acf3027352401e97f4016e764010c9e400ba044007484400411b4001c82400070a419,0x1dc54021c0d8721a7627212b79b310754430e7f0730cca3130cb73630b0ce83099a28308576b30765bf30654ee305a0e73053988304d3483046d2b3025e39401d985401631e4010458400b47240072384003f434001bc940006db41a,0x1ef70821d2cca21b85fe2147847312022f30fde8030e01d130cb73630c486830ab18f3094f0530819c23072d83306275d3058f53305298c304c4b43045fe03024a29401ca4d401631e400fc72400af204006ef14003d7f4001b0740006ad41b,0x1e540021c9c382165a18313acde31158aa30f515130d8c4d30cb73630be01130a5b5e30907fb307df58306f833305fc143057e403051a00304b681302b98c4023710401bbcc4015836400fa67400aa094006bce4003c194001a5c400068241b,0x196e6b31db9ac21c12e121576cf312eeec310ba0730eccea30d1dd930cb73630b7db130a09f4308c4bf307a7f2306c59a305d2ed3056da93050adc304a8a9302b98c40224df401b2084014dcc400f308400a52a40068cc4003a7740019aa400065741c,0x196e6b31d274d21b902e21a14ba2123d48310255c30e509030cb73630cb73630b20d6309bcf5308850a307a120306958a305c04e3055d87304fc1d3049b28302b98c4021e89401b20840143d8400ebfc400a2c340066cc40038e6400190b400062f41c,0x196e6b3196e6b31c9c3821b1396219a48221196e830f99d630ddb9f30cb73630c4dca30ac914309740e308489b307695d30667d6305af173054dd3303a5324032b0f402a34f4021e89401a4ef4013a54400e53c4009e3b400640240037a64001865400060841d,0x196e6b3196e6b318685c31598c131322d2310fadd30f16b730d6d8030cb73630bea3930a760e3092ef53080f3830734603063c553059e5c3053e8a303a21040310d04028e194020df8401986b4013139400dec440099e24006155400363240017d240005e241d,0x196e6b31ec92521d223621773a5314ca5d31274da310685130e9b5530d05ac30cb73630b8c1630a276b308ed66307d8ad30701fb30612e43058e163052fa5303a210402f7cd40279dc401fe234018c724012880400d89240095b64005ec240034cc400173940005be41e,0x1feb8321e336221c9c382168ece3140900311d19030fde8030e271430cb73630cb73630ab5d1409dcdc308af21307a4c7306d202305eb5f3057e40305211f304c4b4302dff24026689401ef0040180fd40127ee400d6a240091b54005d0240033ac40016b0400059b41e,0x1f4c122196e6b31c1c77215b883313539a311381930f5cbd30db96930cb73630c316c409b04d507a85f507a120407a120306a44c305cc103056ed530512f6304b7ac3045c4f3025411401e08640176044011fb8400d0d34008f9d4005a9d40032604001621400057941e,0x206cf921eb4ba21d1d7b21ba277212f73af0f4240f0e015540ee26730d51d430cb73630bf37730880aa607a120507a1204076c9030678b5305bbaa3055fce303db15404aaf13045096303f58c301d2aa4016b8140117d8400cb404008be0400584f400312040015a2400055841f,0x1fcbfd21e24d321c9c382158d4ef11cd4bf0e2cc2f0d56a240cb73640cefe230cb73630b993830a4276307a120607a12050718c9405e4c2405abb53055128304f7a73034db7404451f303eb05301c564401631e4011048400c5e540088474005618400301c400151d400053941f,0x1f332121d9bc82182361f145856f10ad21f0d2038f0cb736f0cb73640cb73630cb73630b4396309fa36308d616307a120506a8bb5053b98505161640473ef403a210403341840439e83022156401b8ab401631e4010906400c0bf40084d1400548e4002ef240014a6400051b41f,0x1ea1c12196e6bf16e360f132d7ff0f9642f0cb736f0cb736f0cb73640cb73640c571f30af241309b57c3089c1d307a1f83061f13605161660516165045004403a2104031b98402a5494021e89401b208401598c401020c400bbcb400817d400527c4002dd2400142a40004fd41f,0x1b208401505b400fb58400ba044007fa8400507d4002ce740013bb40004e1409,0x14786400fa67400b55c4007c894004e904002bda400134840004c6408,0x13f08400f411400b0e040079874004d334002ad740012df40004ab408,0xedf7400ac8d40076a04004b664002a014001274400d204207,0xa86340073d340049a9400290e40012124000478406,0xa45f400723840047fa400282440011ad4000460406,0x6f9640046c44002761400115140064ab305,0x4530400268540010f24000432404,0x43aa40121d6300c33e300c74d204,0x24fe4018a9320061a6303,0x11c373000ff240125f3103,0xbd8f30003df402,0x17ef82005ece302,0x11d5c101,0x17969001,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def lv : Lv := [(73,28,7,14505),(171,52,14,172334),(256,78,21,794441),(338,105,25,2349612),(424,131,31,5527129),(512,157,38,11587233),(593,183,44,20147423),(680,210,50,35943477),(767,237,55,58740854),(852,263,62,88591722),(936,289,69,128021873),(1017,315,75,175274408),(1101,343,80,250114837),(1191,369,88,344836134),(1271,396,94,450818580),(1351,422,100,566700181),(1435,448,106,712235177),(1515,474,112,872049797),(1601,501,118,1101269993),(1684,527,124,1333705728),(1782,558,131,1845647383),(1860,584,138,2169833772),(1940,610,144,2535360415),(2023,635,149,2894358398),(2104,661,155,3353750064),(2184,687,161,3855952433),(2279,717,167,4830049583),(2359,743,173,5481557122),(2443,769,180,6278758616),(2527,795,186,7129015329),(2607,824,192,8330543293),(2699,850,199,9534654481),(2778,876,205,10596077731),(2862,902,211,11853511553),(2942,928,217,13127562601),(3022,954,223,14492536221),(3109,984,229,16873782356),(3209,1012,236,19528320872),(3277,1037,241,20737608095),(3365,1063,247,22913747896),(3446,1088,257,25085429982),(3535,1115,264,27987135333),(3616,1141,270,30420632914),(3696,1167,276,32985663977),(3776,1193,282,35695297415),(3859,1219,288,38747806150),(3945,1249,294,43603510228),(4008,1275,300,46081480584),(4012,1314,307,51130637424),(4011,1347,313,53426069947),(4012,1388,334,61655548953),(4012,1415,340,61365065313),(4012,1454,342,66155084857),(4012,1493,348,71758241757),(4008,1536,354,79445206363),(4012,1566,372,83086818750),(4012,1609,378,91729378590),(4012,1640,388,94341657881),(4012,1650,394,84408334649),(4012,1650,404,71267273085),(4012,1650,415,59963292320),(4012,1650,429,50549917774),(4012,1650,435,41483100231),(4012,1650,444,34038604821),(4012,1650,454,27750291821),(4012,1650,463,22321487022),(4012,1650,468,17560855522),(4012,1650,550,15575596960),(4012,1650,550,11918826197),(4012,1650,550,8836155967),(4012,1650,550,6464871173),(4012,1650,550,4524161776),(4012,1650,550,3073309895),(4012,1650,550,1971910512),(4012,1650,550,1383769480),(4012,1650,550,976594920),(4012,1650,550,669263930),(4012,1650,550,445395926),(4012,1650,550,284710179),(4012,1650,550,173751212),(4012,1650,550,99843570),(4012,1650,550,52944392),(4012,1650,550,25253401),(4012,1650,550,10262241),(4012,1650,550,3284648),(4012,1650,550,676429),(4012,1650,550,49893),(4012,1650,550,2),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0)]
def n : ℕ := 243
def ru : ℕ := 244
def rho0 : ℕ := 213
def amax : ℕ := 31
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
theorem T24 : tabAll 1 ws 192 8 = true := by decide +kernel
theorem T25 : tabAll 1 ws 200 8 = true := by decide +kernel
theorem T26 : tabAll 1 ws 208 8 = true := by decide +kernel
theorem T27 : tabAll 1 ws 216 8 = true := by decide +kernel
theorem T28 : tabAll 1 ws 224 8 = true := by decide +kernel
theorem T29 : tabAll 1 ws 232 8 = true := by decide +kernel
theorem T30 : tabAll 1 ws 240 3 = true := by decide +kernel
theorem tabOK : Gate61ClassTable.tableOK 1 ws = true := tableOK_of_all ws 1 0 (tabAll_add 1 ws 0 240 3 (tabAll_add 1 ws 0 232 8 (tabAll_add 1 ws 0 224 8 (tabAll_add 1 ws 0 216 8 (tabAll_add 1 ws 0 208 8 (tabAll_add 1 ws 0 200 8 (tabAll_add 1 ws 0 192 8 (tabAll_add 1 ws 0 184 8 (tabAll_add 1 ws 0 176 8 (tabAll_add 1 ws 0 168 8 (tabAll_add 1 ws 0 160 8 (tabAll_add 1 ws 0 152 8 (tabAll_add 1 ws 0 144 8 (tabAll_add 1 ws 0 136 8 (tabAll_add 1 ws 0 128 8 (tabAll_add 1 ws 0 120 8 (tabAll_add 1 ws 0 112 8 (tabAll_add 1 ws 0 104 8 (tabAll_add 1 ws 0 96 8 (tabAll_add 1 ws 0 88 8 (tabAll_add 1 ws 0 80 8 (tabAll_add 1 ws 0 72 8 (tabAll_add 1 ws 0 64 8 (tabAll_add 1 ws 0 56 8 (tabAll_add 1 ws 0 48 8 (tabAll_add 1 ws 0 40 8 (tabAll_add 1 ws 0 32 8 (tabAll_add 1 ws 0 24 8 (tabAll_add 1 ws 0 16 8 (tabAll_add 1 ws 0 8 8 (tabAll_add 1 ws 0 0 8 (tabAll_nil 1 ws 0) T0) T1) T2) T3) T4) T5) T6) T7) T8) T9) T10) T11) T12) T13) T14) T15) T16) T17) T18) T19) T20) T21) T22) T23) T24) T25) T26) T27) T28) T29) T30)
theorem C0 : allOK G 1 ws lv 0 2 = true := by decide +kernel
theorem C1 : allOK G 1 ws lv 2 1 = true := by decide +kernel
theorem C2 : allOK G 1 ws lv 3 1 = true := by decide +kernel
theorem C3 : allOK G 1 ws lv 4 1 = true := by decide +kernel
theorem C4 : allOK G 1 ws lv 5 1 = true := by decide +kernel
theorem C5 : allOK G 1 ws lv 6 1 = true := by decide +kernel
theorem C6 : allOK G 1 ws lv 7 1 = true := by decide +kernel
theorem C7 : allOK G 1 ws lv 8 1 = true := by decide +kernel
theorem C8 : allOK G 1 ws lv 9 1 = true := by decide +kernel
theorem C9 : allOK G 1 ws lv 10 1 = true := by decide +kernel
theorem C10 : allOK G 1 ws lv 11 1 = true := by decide +kernel
theorem C11 : allOK G 1 ws lv 12 1 = true := by decide +kernel
theorem C12 : allOK G 1 ws lv 13 1 = true := by decide +kernel
theorem C13 : allOK G 1 ws lv 14 1 = true := by decide +kernel
theorem C14 : allOK G 1 ws lv 15 1 = true := by decide +kernel
theorem C15 : allOK G 1 ws lv 16 1 = true := by decide +kernel
theorem C16 : allOK G 1 ws lv 17 1 = true := by decide +kernel
theorem C17 : allOK G 1 ws lv 18 1 = true := by decide +kernel
theorem C18 : allOK G 1 ws lv 19 1 = true := by decide +kernel
theorem C19 : allOK G 1 ws lv 20 1 = true := by decide +kernel
theorem C20 : allOK G 1 ws lv 21 1 = true := by decide +kernel
theorem C21 : allOK G 1 ws lv 22 1 = true := by decide +kernel
theorem C22 : allOK G 1 ws lv 23 1 = true := by decide +kernel
theorem C23 : allOK G 1 ws lv 24 1 = true := by decide +kernel
theorem C24 : allOK G 1 ws lv 25 1 = true := by decide +kernel
theorem C25 : allOK G 1 ws lv 26 1 = true := by decide +kernel
theorem C26 : allOK G 1 ws lv 27 1 = true := by decide +kernel
theorem C27 : allOK G 1 ws lv 28 1 = true := by decide +kernel
theorem C28 : allOK G 1 ws lv 29 1 = true := by decide +kernel
theorem C29 : allOK G 1 ws lv 30 1 = true := by decide +kernel
theorem C30 : allOK G 1 ws lv 31 1 = true := by decide +kernel
theorem C31 : allOK G 1 ws lv 32 1 = true := by decide +kernel
theorem C32 : allOK G 1 ws lv 33 1 = true := by decide +kernel
theorem C33 : allOK G 1 ws lv 34 1 = true := by decide +kernel
theorem C34 : allOK G 1 ws lv 35 1 = true := by decide +kernel
theorem C35 : allOK G 1 ws lv 36 1 = true := by decide +kernel
theorem C36 : allOK G 1 ws lv 37 1 = true := by decide +kernel
theorem C37 : allOK G 1 ws lv 38 1 = true := by decide +kernel
theorem C38 : allOK G 1 ws lv 39 1 = true := by decide +kernel
theorem C39 : allOK G 1 ws lv 40 1 = true := by decide +kernel
theorem C40 : allOK G 1 ws lv 41 1 = true := by decide +kernel
theorem C41 : allOK G 1 ws lv 42 1 = true := by decide +kernel
theorem C42 : allOK G 1 ws lv 43 1 = true := by decide +kernel
theorem C43 : allOK G 1 ws lv 44 1 = true := by decide +kernel
theorem C44 : allOK G 1 ws lv 45 1 = true := by decide +kernel
theorem C45 : allOK G 1 ws lv 46 1 = true := by decide +kernel
theorem C46 : allOK G 1 ws lv 47 1 = true := by decide +kernel
theorem C47 : allOK G 1 ws lv 48 1 = true := by decide +kernel
theorem C48 : allOK G 1 ws lv 49 1 = true := by decide +kernel
theorem C49 : allOK G 1 ws lv 50 1 = true := by decide +kernel
theorem C50 : allOK G 1 ws lv 51 1 = true := by decide +kernel
theorem C51 : allOK G 1 ws lv 52 1 = true := by decide +kernel
theorem C52 : allOK G 1 ws lv 53 1 = true := by decide +kernel
theorem C53 : allOK G 1 ws lv 54 1 = true := by decide +kernel
theorem C54 : allOK G 1 ws lv 55 1 = true := by decide +kernel
theorem C55 : allOK G 1 ws lv 56 1 = true := by decide +kernel
theorem C56 : allOK G 1 ws lv 57 1 = true := by decide +kernel
theorem C57 : allOK G 1 ws lv 58 1 = true := by decide +kernel
theorem C58 : allOK G 1 ws lv 59 1 = true := by decide +kernel
theorem C59 : allOK G 1 ws lv 60 1 = true := by decide +kernel
theorem C60 : allOK G 1 ws lv 61 1 = true := by decide +kernel
theorem C61 : allOK G 1 ws lv 62 1 = true := by decide +kernel
theorem C62 : allOK G 1 ws lv 63 1 = true := by decide +kernel
theorem C63 : allOK G 1 ws lv 64 1 = true := by decide +kernel
theorem C64 : allOK G 1 ws lv 65 1 = true := by decide +kernel
theorem C65 : allOK G 1 ws lv 66 1 = true := by decide +kernel
theorem C66 : allOK G 1 ws lv 67 1 = true := by decide +kernel
theorem C67 : allOK G 1 ws lv 68 1 = true := by decide +kernel
theorem C68 : allOK G 1 ws lv 69 1 = true := by decide +kernel
theorem C69 : allOK G 1 ws lv 70 1 = true := by decide +kernel
theorem C70 : allOK G 1 ws lv 71 1 = true := by decide +kernel
theorem C71 : allOK G 1 ws lv 72 1 = true := by decide +kernel
theorem C72 : allOK G 1 ws lv 73 1 = true := by decide +kernel
theorem C73 : allOK G 1 ws lv 74 1 = true := by decide +kernel
theorem C74 : allOK G 1 ws lv 75 1 = true := by decide +kernel
theorem C75 : allOK G 1 ws lv 76 1 = true := by decide +kernel
theorem C76 : allOK G 1 ws lv 77 1 = true := by decide +kernel
theorem C77 : allOK G 1 ws lv 78 1 = true := by decide +kernel
theorem C78 : allOK G 1 ws lv 79 1 = true := by decide +kernel
theorem C79 : allOK G 1 ws lv 80 1 = true := by decide +kernel
theorem C80 : allOK G 1 ws lv 81 1 = true := by decide +kernel
theorem C81 : allOK G 1 ws lv 82 1 = true := by decide +kernel
theorem C82 : allOK G 1 ws lv 83 1 = true := by decide +kernel
theorem C83 : allOK G 1 ws lv 84 1 = true := by decide +kernel
theorem C84 : allOK G 1 ws lv 85 1 = true := by decide +kernel
theorem C85 : allOK G 1 ws lv 86 3 = true := by decide +kernel
theorem C86 : allOK G 1 ws lv 89 1 = true := by decide +kernel
theorem C87 : allOK G 1 ws lv 90 1 = true := by decide +kernel
theorem C88 : allOK G 1 ws lv 91 1 = true := by decide +kernel
theorem C89 : allOK G 1 ws lv 92 1 = true := by decide +kernel
theorem C90 : allOK G 1 ws lv 93 1 = true := by decide +kernel
theorem C91 : allOK G 1 ws lv 94 1 = true := by decide +kernel
theorem C92 : allOK G 1 ws lv 95 1 = true := by decide +kernel
theorem C93 : allOK G 1 ws lv 96 1 = true := by decide +kernel
theorem C94 : allOK G 1 ws lv 97 1 = true := by decide +kernel
theorem C95 : allOK G 1 ws lv 98 1 = true := by decide +kernel
theorem C96 : allOK G 1 ws lv 99 1 = true := by decide +kernel
theorem C97 : allOK G 1 ws lv 100 1 = true := by decide +kernel
theorem C98 : allOK G 1 ws lv 101 1 = true := by decide +kernel
theorem C99 : allOK G 1 ws lv 102 1 = true := by decide +kernel
theorem C100 : allOK G 1 ws lv 103 1 = true := by decide +kernel
theorem C101 : allOK G 1 ws lv 104 1 = true := by decide +kernel
theorem C102 : allOK G 1 ws lv 105 2 = true := by decide +kernel
theorem C103 : allOK G 1 ws lv 107 3 = true := by decide +kernel
theorem C104 : allOK G 1 ws lv 110 6 = true := by decide +kernel
theorem C105 : allOK G 1 ws lv 116 13 = true := by decide +kernel
theorem C106 : allOK G 1 ws lv 129 40 = true := by decide +kernel
theorem C107 : allOK G 1 ws lv 169 40 = true := by decide +kernel
theorem C108 : allOK G 1 ws lv 209 34 = true := by decide +kernel
theorem allOKn : allOK G 1 ws lv 0 n = true := (allOK_add G 1 ws lv 0 209 34 (allOK_add G 1 ws lv 0 169 40 (allOK_add G 1 ws lv 0 129 40 (allOK_add G 1 ws lv 0 116 13 (allOK_add G 1 ws lv 0 110 6 (allOK_add G 1 ws lv 0 107 3 (allOK_add G 1 ws lv 0 105 2 (allOK_add G 1 ws lv 0 104 1 (allOK_add G 1 ws lv 0 103 1 (allOK_add G 1 ws lv 0 102 1 (allOK_add G 1 ws lv 0 101 1 (allOK_add G 1 ws lv 0 100 1 (allOK_add G 1 ws lv 0 99 1 (allOK_add G 1 ws lv 0 98 1 (allOK_add G 1 ws lv 0 97 1 (allOK_add G 1 ws lv 0 96 1 (allOK_add G 1 ws lv 0 95 1 (allOK_add G 1 ws lv 0 94 1 (allOK_add G 1 ws lv 0 93 1 (allOK_add G 1 ws lv 0 92 1 (allOK_add G 1 ws lv 0 91 1 (allOK_add G 1 ws lv 0 90 1 (allOK_add G 1 ws lv 0 89 1 (allOK_add G 1 ws lv 0 86 3 (allOK_add G 1 ws lv 0 85 1 (allOK_add G 1 ws lv 0 84 1 (allOK_add G 1 ws lv 0 83 1 (allOK_add G 1 ws lv 0 82 1 (allOK_add G 1 ws lv 0 81 1 (allOK_add G 1 ws lv 0 80 1 (allOK_add G 1 ws lv 0 79 1 (allOK_add G 1 ws lv 0 78 1 (allOK_add G 1 ws lv 0 77 1 (allOK_add G 1 ws lv 0 76 1 (allOK_add G 1 ws lv 0 75 1 (allOK_add G 1 ws lv 0 74 1 (allOK_add G 1 ws lv 0 73 1 (allOK_add G 1 ws lv 0 72 1 (allOK_add G 1 ws lv 0 71 1 (allOK_add G 1 ws lv 0 70 1 (allOK_add G 1 ws lv 0 69 1 (allOK_add G 1 ws lv 0 68 1 (allOK_add G 1 ws lv 0 67 1 (allOK_add G 1 ws lv 0 66 1 (allOK_add G 1 ws lv 0 65 1 (allOK_add G 1 ws lv 0 64 1 (allOK_add G 1 ws lv 0 63 1 (allOK_add G 1 ws lv 0 62 1 (allOK_add G 1 ws lv 0 61 1 (allOK_add G 1 ws lv 0 60 1 (allOK_add G 1 ws lv 0 59 1 (allOK_add G 1 ws lv 0 58 1 (allOK_add G 1 ws lv 0 57 1 (allOK_add G 1 ws lv 0 56 1 (allOK_add G 1 ws lv 0 55 1 (allOK_add G 1 ws lv 0 54 1 (allOK_add G 1 ws lv 0 53 1 (allOK_add G 1 ws lv 0 52 1 (allOK_add G 1 ws lv 0 51 1 (allOK_add G 1 ws lv 0 50 1 (allOK_add G 1 ws lv 0 49 1 (allOK_add G 1 ws lv 0 48 1 (allOK_add G 1 ws lv 0 47 1 (allOK_add G 1 ws lv 0 46 1 (allOK_add G 1 ws lv 0 45 1 (allOK_add G 1 ws lv 0 44 1 (allOK_add G 1 ws lv 0 43 1 (allOK_add G 1 ws lv 0 42 1 (allOK_add G 1 ws lv 0 41 1 (allOK_add G 1 ws lv 0 40 1 (allOK_add G 1 ws lv 0 39 1 (allOK_add G 1 ws lv 0 38 1 (allOK_add G 1 ws lv 0 37 1 (allOK_add G 1 ws lv 0 36 1 (allOK_add G 1 ws lv 0 35 1 (allOK_add G 1 ws lv 0 34 1 (allOK_add G 1 ws lv 0 33 1 (allOK_add G 1 ws lv 0 32 1 (allOK_add G 1 ws lv 0 31 1 (allOK_add G 1 ws lv 0 30 1 (allOK_add G 1 ws lv 0 29 1 (allOK_add G 1 ws lv 0 28 1 (allOK_add G 1 ws lv 0 27 1 (allOK_add G 1 ws lv 0 26 1 (allOK_add G 1 ws lv 0 25 1 (allOK_add G 1 ws lv 0 24 1 (allOK_add G 1 ws lv 0 23 1 (allOK_add G 1 ws lv 0 22 1 (allOK_add G 1 ws lv 0 21 1 (allOK_add G 1 ws lv 0 20 1 (allOK_add G 1 ws lv 0 19 1 (allOK_add G 1 ws lv 0 18 1 (allOK_add G 1 ws lv 0 17 1 (allOK_add G 1 ws lv 0 16 1 (allOK_add G 1 ws lv 0 15 1 (allOK_add G 1 ws lv 0 14 1 (allOK_add G 1 ws lv 0 13 1 (allOK_add G 1 ws lv 0 12 1 (allOK_add G 1 ws lv 0 11 1 (allOK_add G 1 ws lv 0 10 1 (allOK_add G 1 ws lv 0 9 1 (allOK_add G 1 ws lv 0 8 1 (allOK_add G 1 ws lv 0 7 1 (allOK_add G 1 ws lv 0 6 1 (allOK_add G 1 ws lv 0 5 1 (allOK_add G 1 ws lv 0 4 1 (allOK_add G 1 ws lv 0 3 1 (allOK_add G 1 ws lv 0 2 1 (allOK_add G 1 ws lv 0 0 2 (allOK_nil G 1 ws lv 0) C0) C1) C2) C3) C4) C5) C6) C7) C8) C9) C10) C11) C12) C13) C14) C15) C16) C17) C18) C19) C20) C21) C22) C23) C24) C25) C26) C27) C28) C29) C30) C31) C32) C33) C34) C35) C36) C37) C38) C39) C40) C41) C42) C43) C44) C45) C46) C47) C48) C49) C50) C51) C52) C53) C54) C55) C56) C57) C58) C59) C60) C61) C62) C63) C64) C65) C66) C67) C68) C69) C70) C71) C72) C73) C74) C75) C76) C77) C78) C79) C80) C81) C82) C83) C84) C85) C86) C87) C88) C89) C90) C91) C92) C93) C94) C95) C96) C97) C98) C99) C100) C101) C102) C103) C104) C105) C106) C107) C108)
end Gate61DatET2
