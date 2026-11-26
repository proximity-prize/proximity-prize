import ProximityPrize.SubmissionLower.Gate6966Assm

set_option Elab.async false

-- merged module Witness6966DatS1
section Merged_Witness6966DatS1
set_option autoImplicit false
set_option maxRecDepth 400000
set_option Elab.async false
namespace Witness6966DatS1
open Gate6966Cell
def G : Gt := { m00 := 0, m01 := 653957955172672, m02 := 1963013660900544, m11 := 4427679010801904, m12 := 13570835366494032, m22 := 40714785690247152, xb := 141, xj := 44, xt := 14, lb := 126, lj := 40, lt := 13, A := 204900000000000000, sc := 32, lift := true }
def ws : List ℕ := [0x0,0x0,0x0,0x0,0x0,0x57e40301,0x4c4b4301,0x439e8301,0x3ccc0301,0x7a1203037422302,0x6275d3032a8c302,0x57e40302ec62302,0x51a00300fa67402,0x8af21304c4b4300d6a2403,0x7a1203047acf300ba04403,0x6958a30439e8300a2c3403,0x5cc10304004f3008f9d403,0x57e40303ccc03007fa8403,0x8576b30539883039e463007238404,0x7a120304fc1d303742230066cc404,0x6d202304c4b43034db83005d02404,0x6275d30492573032a8c300548e404,0x8fa3d305b7a330464453030a373004d33405,0x825d23057e4030439e8302ec6230046c4405,0x7a12030549f730412c83010c9e400411b405,0x6f8333051a00303ee81300fa674003c19405,0x9740e30667d6304edbd303ccc0300e53c40037a6406,0x8af21305eb5f304c4b4303ad40300d6a240033ac406,0x805f0305abb53049e803038fc7300c5e5400301c406,0x7a1203057e403047acf3037422300ba044002ce7406,0x71280305540e304595a3035a24300ac8d4002a01406,0x91be0306958a3052cb630439e830341a8300a2c34002761407,0x87c36306275d30507e13041c483032a8c30097c740024fe407,0x7efb7305cc10304e54a304004f30314b33008f9d40022d1407,0x7a120305a3e2304c4b4303e5d73030002300868840020d4407,0x725b83057e40304a5ef303ccc0302ec623007fa84001f01407,0x8dd88306b79f3055ae130488cd303b4ee301154a40078104001d54408,0x8576b30654ee30539883046d2b3039e46301045840072384001bc9408,0x7df58305fc143051a0030452e930388b4300fa674006bce4001a5c408,0x7a120305c04e304fc1d30439e83037422300ebfc40066cc400190b408,0x92ef530734603059e5c304dfb93042212303607e300dec4400615540017d2409,0x8af21306d2023057e40304c4b43040b4f3034db8300d6a24005d0240016b0409,0x83b9930678b53055fce304aaf1303f58c3033bc2300cb40400584f40015a2409,0x7d2c8306275d30542dd3049257303e0b73032a8c300c0bf400548e40014a6409,0x9740e307a120305dd06305274d3047acf303ccc03031a0d300ba04400507d40013bb40a,0x8fa3d3073feb305b7a33050cff3046445303b9993030a37300b0e04004d3340012df40a,0x88b42306e70a3059a40304f3db3044ea8303a734302fb01300a86340049a9400121240a,0x825d2306958a3057e40304dbc930439e83039585302ec62300a2c340046c4400115140a,0x7c8d63064a993056386304c4b430425f7303848330119c84009b5040043aa400109c40a,0x7a120306058230549f7304ae8d30412c830374223010c9e400945c400411b4000ff240a,0x8d0b33074940305cc10305317c3049942304004f303645930100594008f9d4003e5f4000f5240b,0x86eb2306f833305b0fb3051a0030484c4303ee813035521300fa6740089764003c194000ebb40b,0x81451306ad44305971330503703047108303dd543034671300ef7840083b140039ad4000e2d40b,0x7c0c430667d63057e40304edbd3045e01303ccc03033842300e53c4007fa840037a64000da740b,0x7a120306275d305666f304d8d93044ba4303bcbc3032a8c300dba34007a84400357d4000d2840b,0x750f2305eb5f3054f8d304c4b430439e8303ad403031d4c300d6a240075ae40033ac4000caf40b,0x70676305c3cf3053988304b14530428c43039e463031079300ce02400723840031be4000c3d40b,0x6c122305abb530524513049e8030418303038fc7303040f300c5e54006de2400301c4000bd140b,0x7ba17306807b305948b3050fdc3048c5c304082430381bd302f809300be3f40069c94002e614000b6b40c,0x8e87f307a12030644163057e40304fc1d3047acf303f8993037422302ec62300ba0440066cc4002ce74000b0940d,0xc2bf830a37ea308937130757673060b9030568c6304e90730469d1303e98830366f1302e115300b318400631b4002b574000aad40f,0xcb73630baae3309d28630844163071280305d696305540e304d692304595a303daed3035a24302d620300ac8d4005f9b4002a014000a55410,0x17318020da08230cb73630b32fc309740e307f9ea306d202305bd23305400c304c4b43044964303ccc03034db8301079b400a65c4005d0240028984000a01412,0x185ac9216be4c20d178f30cb73630ac3673091be0307b479306958a305a76d3052cb6304b36630439e8303befd30341a8300fdff400a2c340059d6400276140009b1413,0x1b541e2198936217df7220e94b130cb73630c345d30a5b5e308c96e307a1203065cc2305927b3051a00304a29e3042ae1303b19f30335f0300fa674009d2040056d3400261a4000964415,0x1c9c3821abe1121905022176a1720e01d130cb73630bba80309fa363087c363075ce5306275d3057e4030507e130492573041c48303a4a23032a8c300f19940097c7400548e40024fe400091c416,0x2014b921dee6a21bfaa421a30302188778216fa3b20d796b30cb73630b48cf3099f5230833c63071cce305f5143056ab2304f652304828a3040e1930398013031f79300e93f40092b140051cf40023d440008d6418,0x218fc421f4c1221d403721b6231219a9bd218100820eeef230cfa8030cb73630ade903094a28307efb7306e085305cc1030557c5304e54a3047330304004f3038bb930314b3300e1524008f9d4004f3240022d14000893419,0x196e6b320b69121e901321c9c3821ad2082192a122179e3120e5d4b30cb73630c3bce30a7b1c308fa3d307afaf306a7bd305b7a33054570304d4c23046445303f2e53037fc53030a37300d9ca4008af64004d3340021c1400085441a,0x196e6b3196e6b3222f4721feb8321ddf7b21c017821a4969218b09c20fde8030dd5a930cb73630bc86630a1de1308af21307a120306722e305a3e230533ab304c4b430455c3303e5d730374223030002300d6a240086884004ad040020d4400081741c,0x1d107a3196e6b3196e6b32153cf21f2d2d21d392f21b6f1b219c7ae2183cd820f43b230d572330cb73630b5c50309c65a308687130761a03063f9b30590c5305226e304b51a30447a6303d92130368cd302f611300cfb1400824f40048884001fdb40007dd41d,0x20b28a31a9d3b3196e6b3196e6b320868221e7a4e21c9c3821ae4642194c40217ce5320eb36b30ce0e830cb73630af6ed309740e30825d230725b83060fc83057e4030511b1304a5ef30439e8303ccc03035dc2302ec62300c9154007fa840046c44001f0140007a541e,0x1e29a93196e6b3196e6b3196e6b31fc5f621dd1d021c07be21a60a8218d69e2102c3a30e2cbb30cb73630c427230a97b13092693307e6f4306ed22305e2833056c4d305016e304972c3042c87303c0b03035300302e2f1300c2c84007bc640044ad4001e1d400076f41e,0x1bbe463196e6b3196e6b3211d4821f10f021d32bb21b7b00219e353218665020f936830daec930cb73630bd4d930a3e1c308dd88307ab8d306b79f305c5b43055ae1304f1a030488cd3041f7d303b4ee3034882301154a400bcc5400781040042ac4001d54400073c41e,0x1f360f3196e6b3196e6b3196e6b3205aaa21e665b21c9c3821af5562196bdf211168230f04a130d38d530cb73630b6dd8309e9bb3089895307a12030684f4305b30530549f7304e23f3047acf30412c8303a9763033e463010c9e400ba044007484400411b4001c82400070a41f,0x1cd2793196e6b3196e6b3196e6b31fa39b21dc54021c0d8721a7627218f9d5210754430e7f0730cca3130cb73630b0ce83099a28308576b30765bf30654ee305a0e73053988304d3483046d2b30406643039e46303344b3010458400b47240072384003f434001bc940006db41f,0x1a897b3196e6b3196e6b3196e6b31ef70821d2cca21b85fe219fcef2188ccc20fde8030e01d130cb73630c486830ab18f3094f0530819c23072d83306275d3058f53305298c304c4b43045fe0303fa4d303935c3032a8c300fc72400af204006ef14003d7f4001b0740006ad41f,0x196e6b3196e6b3196e6b320328021e540021c9c3821b0506219893621158aa30f5151314b61d61224c560fd30370dbba070bd9e180a2975808a66e9074d34a057e403051a00304b68130452e9303ee8130388b43032109300fa67400aa094006bce4003c194001a5c400068241f,0x196e6b3196e6b3196e6b31f840c21db9ac21c12e121a8a172191a90219bd4f516bb1a61400dc61188a860f4d1a70d494e70b78ce809d78780861c59071422a05eb83b04e511c04a8a93044642303e2fc3037e4c30317bf300f308400a52a40068cc4003a7740019aa400065741f,0x196e6b3196e6b3196e6b31edf2e21d274d21b902e21f86c451c06bf518d822515f42c61354be610f44860ecdba70cdc7970b1c5080989688082041906dda3a05be9cb04c07bc03e0c5d0439e8303d7bd30374223030eac300ebfc400a2c340066cc40038e6400190b400062f41f,0x196e6b3196e6b3196e6b31e431021c9c38222195751e691951b0d36517feb56153746612b128610672470e547670c74c770ac41f8093ede907e1b1906a98fa0593adb049d7ac03c49bd0306e6f03ccc03036a3330305cf300e53c4009e3b400640240037a64001865400060841f,0x196e6b3196e6b31f66f721daef6224c5be520e45d51d5a5551a2078517303f61483bd612158e60fe0c770de0ee70c11e880a6ff8808f7b0907a5ea90677c4a056a98b047bf6c03a9a0d02f186f03c203303607e3013139400dec440099e24006155400363240017d240005e241f,0x196e6b3196e6b32c01f84278bf8423788a51fbf8151c59745193fa95166c05613d8f6611816b60f60c370d72c470bb39080a1f9d808b3ab9076cc0a06481fa054342b045bdac038fc3e02dd05f03b78430357003012880400d89240095b64005ec240034cc400173940005be41f,0x196e6b32f185442a6c0642625a04223cb851ea9a951b65865186a00515b15d6133662610f44860ee6b370d09a670b597a809d2d480872a2907360ea061a80a051d93b043d12c0376f4e02c958f03ad403034db830127ee400d6a240091b54005d0240033ac40016b0400059b41f,0x196e6b32d65e7428eba1424d1fb521111851da1d351a7db05179ec3614ffab6129b7b6106db570e723a70ca54670b03658098968808346790701b0a05eeccb04f974c041f8cd035f25e02b672f03a33730344a43011fb8400d0d34008f9d4005a9d40032604001621400057941f,0x312040015a24000558403,0x301c400151d4000539403,0x14a6400051b402,0x4fd401,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def lv : Lv := [(94,29,9,77530),(189,50,16,125077),(294,75,25,696338),(407,99,33,2239831),(524,126,42,8498909),(587,150,50,10196630),(691,175,58,19588159),(806,197,65,28974697),(900,224,74,52553436),(1023,248,82,85569799),(1130,271,90,113844253),(1243,296,98,172297822),(1346,321,107,240967429),(1443,345,115,302840430),(1540,368,122,359838708),(1660,394,131,529852141),(1765,419,139,685230747),(1868,444,148,871470140),(1949,467,154,941708455),(2061,492,164,1208084015),(2174,517,172,1528816161),(2270,541,180,1767159297),(2374,566,188,2140006250),(2471,590,196,2446400813),(2592,615,204,3044996598),(2688,639,213,3441055626),(2785,663,221,3877479368),(2881,687,229,4350634241),(2988,716,238,5640539471),(3107,737,244,6095530019),(3203,761,250,6756802822),(3314,787,258,8042894505),(3426,813,270,9506632749),(3539,837,279,10754214463),(3643,862,287,12157145291),(3747,887,295,13697034954),(3829,909,303,14000098324),(3942,934,311,15929107230),(4002,958,319,16349449832),(4012,993,330,18999771963),(4012,1022,339,19469473291),(4012,1060,353,23182417391),(4012,1092,364,24796355297),(4012,1124,374,26479107391),(4012,1156,385,28231705934),(4012,1193,397,32174436169),(4012,1232,410,37409639854),(4007,1265,421,39690831574),(4012,1299,407,42988649477),(4007,1333,444,46071996389),(4012,1365,455,48612562032),(4012,1403,438,54263762590),(4008,1434,478,55972500628),(4007,1467,489,58947193365),(4007,1503,501,64037554338),(4012,1547,481,75215250193),(4012,1581,516,79706338933),(4012,1613,537,82621678966),(4012,1643,547,83987310479),(4012,1650,512,68816393682),(4010,1650,550,52419028761),(4012,1650,550,39429124804),(4012,1650,550,28877089869),(4012,1650,550,20705705831),(4012,1650,550,14402592371),(4012,1650,550,9651899382),(4012,1650,550,6170312793),(4012,1650,550,3677956854),(4012,1650,550,2033518527),(4012,1650,550,983812390),(4012,1650,550,383622657),(4012,1650,550,102430908),(4012,1650,550,29591706),(4012,1650,550,7352833),(4012,1650,550,914361),(4012,1650,550,11045),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0),(4012,1650,550,0)]
def n : ℕ := 222
def ru : ℕ := 223
def rho0 : ℕ := 192
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
theorem T27 : tabAll 1 ws 216 6 = true := by decide +kernel
theorem tabOK : Gate6966ClassTable.tableOK 1 ws = true := tableOK_of_all ws 1 0 (by simpa [ws] using (tabAll_add 1 ws 0 216 6 (tabAll_add 1 ws 0 208 8 (tabAll_add 1 ws 0 200 8 (tabAll_add 1 ws 0 192 8 (tabAll_add 1 ws 0 184 8 (tabAll_add 1 ws 0 176 8 (tabAll_add 1 ws 0 168 8 (tabAll_add 1 ws 0 160 8 (tabAll_add 1 ws 0 152 8 (tabAll_add 1 ws 0 144 8 (tabAll_add 1 ws 0 136 8 (tabAll_add 1 ws 0 128 8 (tabAll_add 1 ws 0 120 8 (tabAll_add 1 ws 0 112 8 (tabAll_add 1 ws 0 104 8 (tabAll_add 1 ws 0 96 8 (tabAll_add 1 ws 0 88 8 (tabAll_add 1 ws 0 80 8 (tabAll_add 1 ws 0 72 8 (tabAll_add 1 ws 0 64 8 (tabAll_add 1 ws 0 56 8 (tabAll_add 1 ws 0 48 8 (tabAll_add 1 ws 0 40 8 (tabAll_add 1 ws 0 32 8 (tabAll_add 1 ws 0 24 8 (tabAll_add 1 ws 0 16 8 (tabAll_add 1 ws 0 8 8 (tabAll_add 1 ws 0 0 8 (tabAll_nil 1 ws 0) T0) T1) T2) T3) T4) T5) T6) T7) T8) T9) T10) T11) T12) T13) T14) T15) T16) T17) T18) T19) T20) T21) T22) T23) T24) T25) T26) T27))
theorem C0 : allOK G 1 ws lv 0 8 = true := by rw [allOK_eq_F]; decide +kernel
theorem C1 : allOK G 1 ws lv 8 3 = true := by rw [allOK_eq_F]; decide +kernel
theorem C2 : allOK G 1 ws lv 11 2 = true := by rw [allOK_eq_F]; decide +kernel
theorem C3 : allOK G 1 ws lv 13 2 = true := by rw [allOK_eq_F]; decide +kernel
theorem C4 : allOK G 1 ws lv 15 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C5 : allOK G 1 ws lv 16 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C6 : allOK G 1 ws lv 17 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C7 : allOK G 1 ws lv 18 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C8 : allOK G 1 ws lv 19 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C9 : allOK G 1 ws lv 20 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C10 : allOK G 1 ws lv 21 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C11 : allOK G 1 ws lv 22 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C12 : allOK G 1 ws lv 23 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C13 : allOK G 1 ws lv 24 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C14 : allOK G 1 ws lv 25 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C15 : allOK G 1 ws lv 26 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C16 : allOK G 1 ws lv 27 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C17 : allOK G 1 ws lv 28 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C18 : allOK G 1 ws lv 29 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C19 : allOK G 1 ws lv 30 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C20 : allOK G 1 ws lv 31 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C21 : allOK G 1 ws lv 32 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C22 : allOK G 1 ws lv 33 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C23 : allOK G 1 ws lv 34 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C24 : allOK G 1 ws lv 35 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C25 : allOK G 1 ws lv 36 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C26 : allOK G 1 ws lv 37 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C27 : allOK G 1 ws lv 38 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C28 : allOK G 1 ws lv 39 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C29 : allOK G 1 ws lv 40 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C30 : allOK G 1 ws lv 41 2 = true := by rw [allOK_eq_F]; decide +kernel
theorem C31 : allOK G 1 ws lv 43 3 = true := by rw [allOK_eq_F]; decide +kernel
theorem C32 : allOK G 1 ws lv 46 4 = true := by rw [allOK_eq_F]; decide +kernel
theorem C33 : allOK G 1 ws lv 50 4 = true := by rw [allOK_eq_F]; decide +kernel
theorem C34 : allOK G 1 ws lv 54 5 = true := by rw [allOK_eq_F]; decide +kernel
theorem C35 : allOK G 1 ws lv 59 3 = true := by rw [allOK_eq_F]; decide +kernel
theorem C36 : allOK G 1 ws lv 62 2 = true := by rw [allOK_eq_F]; decide +kernel
theorem C37 : allOK G 1 ws lv 64 2 = true := by rw [allOK_eq_F]; decide +kernel
theorem C38 : allOK G 1 ws lv 66 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C39 : allOK G 1 ws lv 67 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C40 : allOK G 1 ws lv 68 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C41 : allOK G 1 ws lv 69 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C42 : allOK G 1 ws lv 70 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C43 : allOK G 1 ws lv 71 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C44 : allOK G 1 ws lv 72 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C45 : allOK G 1 ws lv 73 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C46 : allOK G 1 ws lv 74 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C47 : allOK G 1 ws lv 75 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C48 : allOK G 1 ws lv 76 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C49 : allOK G 1 ws lv 77 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C50 : allOK G 1 ws lv 78 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C51 : allOK G 1 ws lv 79 2 = true := by rw [allOK_eq_F]; decide +kernel
theorem C52 : allOK G 1 ws lv 81 4 = true := by rw [allOK_eq_F]; decide +kernel
theorem C53 : allOK G 1 ws lv 85 1 = true := by rw [allOK_eq_F]; decide +kernel
theorem C54 : allOK G 1 ws lv 86 3 = true := by rw [allOK_eq_F]; decide +kernel
theorem C55 : allOK G 1 ws lv 89 3 = true := by rw [allOK_eq_F]; decide +kernel
theorem C56 : allOK G 1 ws lv 92 35 = true := by rw [allOK_eq_F]; decide +kernel
theorem C57 : allOK G 1 ws lv 127 95 = true := by rw [allOK_eq_F]; decide +kernel
theorem allOKn : allOK G 1 ws lv 0 n = true := allOK_add G 1 ws lv 0 127 95 (allOK_add G 1 ws lv 0 92 35 (allOK_add G 1 ws lv 0 89 3 (allOK_add G 1 ws lv 0 86 3 (allOK_add G 1 ws lv 0 85 1 (allOK_add G 1 ws lv 0 81 4 (allOK_add G 1 ws lv 0 79 2 (allOK_add G 1 ws lv 0 78 1 (allOK_add G 1 ws lv 0 77 1 (allOK_add G 1 ws lv 0 76 1 (allOK_add G 1 ws lv 0 75 1 (allOK_add G 1 ws lv 0 74 1 (allOK_add G 1 ws lv 0 73 1 (allOK_add G 1 ws lv 0 72 1 (allOK_add G 1 ws lv 0 71 1 (allOK_add G 1 ws lv 0 70 1 (allOK_add G 1 ws lv 0 69 1 (allOK_add G 1 ws lv 0 68 1 (allOK_add G 1 ws lv 0 67 1 (allOK_add G 1 ws lv 0 66 1 (allOK_add G 1 ws lv 0 64 2 (allOK_add G 1 ws lv 0 62 2 (allOK_add G 1 ws lv 0 59 3 (allOK_add G 1 ws lv 0 54 5 (allOK_add G 1 ws lv 0 50 4 (allOK_add G 1 ws lv 0 46 4 (allOK_add G 1 ws lv 0 43 3 (allOK_add G 1 ws lv 0 41 2 (allOK_add G 1 ws lv 0 40 1 (allOK_add G 1 ws lv 0 39 1 (allOK_add G 1 ws lv 0 38 1 (allOK_add G 1 ws lv 0 37 1 (allOK_add G 1 ws lv 0 36 1 (allOK_add G 1 ws lv 0 35 1 (allOK_add G 1 ws lv 0 34 1 (allOK_add G 1 ws lv 0 33 1 (allOK_add G 1 ws lv 0 32 1 (allOK_add G 1 ws lv 0 31 1 (allOK_add G 1 ws lv 0 30 1 (allOK_add G 1 ws lv 0 29 1 (allOK_add G 1 ws lv 0 28 1 (allOK_add G 1 ws lv 0 27 1 (allOK_add G 1 ws lv 0 26 1 (allOK_add G 1 ws lv 0 25 1 (allOK_add G 1 ws lv 0 24 1 (allOK_add G 1 ws lv 0 23 1 (allOK_add G 1 ws lv 0 22 1 (allOK_add G 1 ws lv 0 21 1 (allOK_add G 1 ws lv 0 20 1 (allOK_add G 1 ws lv 0 19 1 (allOK_add G 1 ws lv 0 18 1 (allOK_add G 1 ws lv 0 17 1 (allOK_add G 1 ws lv 0 16 1 (allOK_add G 1 ws lv 0 15 1 (allOK_add G 1 ws lv 0 13 2 (allOK_add G 1 ws lv 0 11 2 (allOK_add G 1 ws lv 0 8 3 (allOK_add G 1 ws lv 0 0 8 (allOK_nil G 1 ws lv 0) C0) C1) C2) C3) C4) C5) C6) C7) C8) C9) C10) C11) C12) C13) C14) C15) C16) C17) C18) C19) C20) C21) C22) C23) C24) C25) C26) C27) C28) C29) C30) C31) C32) C33) C34) C35) C36) C37) C38) C39) C40) C41) C42) C43) C44) C45) C46) C47) C48) C49) C50) C51) C52) C53) C54) C55) C56) C57
end Witness6966DatS1

end Merged_Witness6966DatS1

-- merged module Witness6966SumS1
section Merged_Witness6966SumS1
set_option Elab.async false
set_option maxRecDepth 100000
namespace Witness6966DatS1
open Gate6966Cell
theorem S0 : psum lv 0 10 = 4067279907959 := by decide +kernel
theorem P0 : psum lv 0 10 = 4067279907959 := S0
theorem S1 : psum lv 10 10 = 4046371076746 := by decide +kernel
theorem P1 : psum lv 0 20 = 8113650984705 := by
  have h : psum lv 0 20 = psum lv 0 10 + psum lv 10 10 := psum_add lv 0 10 10
  rw [h, P0, S1]; rfl
theorem S2 : psum lv 20 10 = 3927149691358 := by decide +kernel
theorem P2 : psum lv 0 30 = 12040800676063 := by
  have h : psum lv 0 30 = psum lv 0 20 + psum lv 20 10 := psum_add lv 0 20 10
  rw [h, P1, S2]; rfl
theorem S3 : psum lv 30 10 = 3559171246913 := by decide +kernel
theorem P3 : psum lv 0 40 = 15599971922976 := by
  have h : psum lv 0 40 = psum lv 0 30 + psum lv 30 10 := psum_add lv 0 30 10
  rw [h, P2, S3]; rfl
theorem S4 : psum lv 40 10 = 2774959633183 := by decide +kernel
theorem P4 : psum lv 0 50 = 18374931556159 := by
  have h : psum lv 0 50 = psum lv 0 40 + psum lv 40 10 := psum_add lv 0 40 10
  rw [h, P3, S4]; rfl
theorem S5 : psum lv 50 10 = 1467814607103 := by decide +kernel
theorem P5 : psum lv 0 60 = 19842746163262 := by
  have h : psum lv 0 60 = psum lv 0 50 + psum lv 50 10 := psum_add lv 0 50 10
  rw [h, P4, S5]; rfl
theorem S6 : psum lv 60 10 = 179627527501 := by decide +kernel
theorem P6 : psum lv 0 70 = 20022373690763 := by
  have h : psum lv 0 70 = psum lv 0 60 + psum lv 60 10 := psum_add lv 0 60 10
  rw [h, P5, S6]; rfl
theorem S7 : psum lv 70 10 = 523923510 := by decide +kernel
theorem P7 : psum lv 0 80 = 20022897614273 := by
  have h : psum lv 0 80 = psum lv 0 70 + psum lv 70 10 := psum_add lv 0 70 10
  rw [h, P6, S7]; rfl
theorem S8 : psum lv 80 10 = 0 := by decide +kernel
theorem P8 : psum lv 0 90 = 20022897614273 := by
  have h : psum lv 0 90 = psum lv 0 80 + psum lv 80 10 := psum_add lv 0 80 10
  rw [h, P7, S8]; rfl
theorem S9 : psum lv 90 10 = 0 := by decide +kernel
theorem P9 : psum lv 0 100 = 20022897614273 := by
  have h : psum lv 0 100 = psum lv 0 90 + psum lv 90 10 := psum_add lv 0 90 10
  rw [h, P8, S9]; rfl
theorem S10 : psum lv 100 10 = 0 := by decide +kernel
theorem P10 : psum lv 0 110 = 20022897614273 := by
  have h : psum lv 0 110 = psum lv 0 100 + psum lv 100 10 := psum_add lv 0 100 10
  rw [h, P9, S10]; rfl
theorem S11 : psum lv 110 10 = 0 := by decide +kernel
theorem P11 : psum lv 0 120 = 20022897614273 := by
  have h : psum lv 0 120 = psum lv 0 110 + psum lv 110 10 := psum_add lv 0 110 10
  rw [h, P10, S11]; rfl
theorem S12 : psum lv 120 10 = 0 := by decide +kernel
theorem P12 : psum lv 0 130 = 20022897614273 := by
  have h : psum lv 0 130 = psum lv 0 120 + psum lv 120 10 := psum_add lv 0 120 10
  rw [h, P11, S12]; rfl
theorem S13 : psum lv 130 10 = 0 := by decide +kernel
theorem P13 : psum lv 0 140 = 20022897614273 := by
  have h : psum lv 0 140 = psum lv 0 130 + psum lv 130 10 := psum_add lv 0 130 10
  rw [h, P12, S13]; rfl
theorem S14 : psum lv 140 10 = 0 := by decide +kernel
theorem P14 : psum lv 0 150 = 20022897614273 := by
  have h : psum lv 0 150 = psum lv 0 140 + psum lv 140 10 := psum_add lv 0 140 10
  rw [h, P13, S14]; rfl
theorem S15 : psum lv 150 10 = 0 := by decide +kernel
theorem P15 : psum lv 0 160 = 20022897614273 := by
  have h : psum lv 0 160 = psum lv 0 150 + psum lv 150 10 := psum_add lv 0 150 10
  rw [h, P14, S15]; rfl
theorem S16 : psum lv 160 10 = 0 := by decide +kernel
theorem P16 : psum lv 0 170 = 20022897614273 := by
  have h : psum lv 0 170 = psum lv 0 160 + psum lv 160 10 := psum_add lv 0 160 10
  rw [h, P15, S16]; rfl
theorem S17 : psum lv 170 10 = 0 := by decide +kernel
theorem P17 : psum lv 0 180 = 20022897614273 := by
  have h : psum lv 0 180 = psum lv 0 170 + psum lv 170 10 := psum_add lv 0 170 10
  rw [h, P16, S17]; rfl
theorem S18 : psum lv 180 10 = 0 := by decide +kernel
theorem P18 : psum lv 0 190 = 20022897614273 := by
  have h : psum lv 0 190 = psum lv 0 180 + psum lv 180 10 := psum_add lv 0 180 10
  rw [h, P17, S18]; rfl
theorem S19 : psum lv 190 10 = 0 := by decide +kernel
theorem P19 : psum lv 0 200 = 20022897614273 := by
  have h : psum lv 0 200 = psum lv 0 190 + psum lv 190 10 := psum_add lv 0 190 10
  rw [h, P18, S19]; rfl
theorem S20 : psum lv 200 10 = 0 := by decide +kernel
theorem P20 : psum lv 0 210 = 20022897614273 := by
  have h : psum lv 0 210 = psum lv 0 200 + psum lv 200 10 := psum_add lv 0 200 10
  rw [h, P19, S20]; rfl
theorem S21 : psum lv 210 10 = 0 := by decide +kernel
theorem P21 : psum lv 0 220 = 20022897614273 := by
  have h : psum lv 0 220 = psum lv 0 210 + psum lv 210 10 := psum_add lv 0 210 10
  rw [h, P20, S21]; rfl
theorem S22 : psum lv 220 2 = 0 := by decide +kernel
theorem P22 : psum lv 0 222 = 20022897614273 := by
  have h : psum lv 0 222 = psum lv 0 220 + psum lv 220 2 := psum_add lv 0 220 2
  rw [h, P21, S22]; rfl
theorem sumLt : (∑ i ∈ Finset.range n, lsum lv i) < Low6966Prices.layerNeed := by
  rw [← psum_eq]
  have h := P22
  have e : n = 222 := rfl
  rw [e, h]; decide
end Witness6966DatS1

end Merged_Witness6966SumS1
