import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.R6960Low6960Rectangle
set_option Elab.async false


set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6960Allocation.Group6

private def m0 : MassCell 6 :=
  ⟨⟨2,5,5⟩,mass_cell 6 2 5 5 210 (by decide)
    (by decide +kernel) [4569450052270, 3762174774488, 3045455850136, 2431479558232, 1910792936984, 1474311074776, 1113317110168, 819462231896, 584765678872, 401614740184, 262764755096, 161339113048, 90829253656, 45094666712, 18362892184, 5229520216, 658191128, 3947222] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 6 :=
  ⟨⟨2,6,13⟩,mass_cell 6 2 6 13 195 (by decide)
    (by decide +kernel) [4693214279464, 4017145869219, 3192018623139, 2494025264667, 1910793742347, 1430420617587, 1041471064659, 732978870699, 494446435707, 315844772547, 187613506947, 100660877499, 46363735659, 16567545747, 3586384947, 202943307, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 6 :=
  ⟨⟨3,7,20⟩,mass_cell 6 3 7 20 184 (by decide)
    (by decide +kernel) [4693214279464, 4246445414893, 3386189384964, 2584396644876, 1926455612308, 1395905474460, 977018090532, 654797991724, 414982381236, 244041134268, 129176798020, 58324591692, 20152406484, 4060805596, 183191354, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 6 :=
  ⟨⟨2,9,28⟩,mass_cell 6 2 9 28 164 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3724106156934, 2756069789880, 1965552741912, 1346297822328, 875733480408, 532004801592, 293973507480, 141217955832, 54033140568, 13430691768, 1138875672, 148760] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 6 :=
  ⟨⟨4,10,32⟩,mass_cell 6 4 10 32 157 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3868877334785, 2881689764969, 1997319401825, 1321333398033, 822663247865, 471713455001, 240361532529, 101958002945, 31326398153, 4763259465, 72932306, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 6 :=
  ⟨⟨1,12,36⟩,mass_cell 6 1 12 36 145 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3951913458350, 3065741489886, 2052812294466, 1292424999486, 748179371346, 383745160446, 162862101186, 49339911966, 7058295186, 76798938, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 6 :=
  ⟨⟨5,15,42⟩,mass_cell 6 5 15 42 132 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3397141871912, 2171536776552, 1242002368344, 628808289096, 262982787384, 78214623528, 10853069592, 105757062] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 6 :=
  ⟨⟨3,16,43⟩,mass_cell 6 3 16 43 128 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3446628401870, 2205808027619, 1233858264755, 601092356091, 234093090491, 59775122675, 5384973219, 1595662] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 6 :=
  ⟨⟨1,18,45⟩,mass_cell 6 1 18 45 122 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3531238624465, 2281260042671, 1213923389351, 543257719439, 180227630759, 31764963119, 823156274, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 6 :=
  ⟨⟨5,21,48⟩,mass_cell 6 5 21 48 115 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3614100196812, 2424692458808, 1176231628664, 454385316536, 113950097144, 9722545208, 1233948] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 6 :=
  ⟨⟨6,24,50⟩,mass_cell 6 6 24 50 110 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2566699820580, 1146131349744, 381505531548, 68578960872, 1959385100, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 6 :=
  ⟨⟨1,27,51⟩,mass_cell 6 1 27 51 105 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2636259611756, 1103934350930, 313872868202, 36393442754, 103162694] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 6 :=
  ⟨⟨1,29,52⟩,mass_cell 6 1 29 52 102 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2717847515266, 1096235559728, 280668471984, 24060841520, 2159005] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 6 :=
  ⟨⟨1,31,53⟩,mass_cell 6 1 31 53 100 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2802854776981, 1100981682006, 254861386374, 16009007734, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 6 :=
  ⟨⟨11,33,54⟩,mass_cell 6 11 33 54 98 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2871198903272, 1074365088882, 218293147698, 9707819199, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 6 :=
  ⟨⟨1,38,55⟩,mass_cell 6 1 38 55 94 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2947770439982, 1042837164686, 157604688914, 1903594452] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 6 :=
  ⟨⟨12,41,56⟩,mass_cell 6 12 41 56 92 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3019142073922, 1024509566988, 127313287052, 620681497] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 6 :=
  ⟨⟨1,48,57⟩,mass_cell 6 1 48 57 88 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3091943138871, 990001804089, 77269235529, 24308] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 6 :=
  ⟨⟨10,54,58⟩,mass_cell 6 10 54 58 85 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3159090628224, 964312144508, 49517253722, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 6 :=
  ⟨⟨62,4,44⟩,mass_cell 6 62 4 44 278 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3506696697474, 2334314779363, 1298429787379, 534221500435, 66473345321, 2126615, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 6 :=
  ⟨⟨59,27,54⟩,mass_cell 6 59 27 54 108 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2849435875888, 1048925617278, 243794090238, 25259379198, 210787959] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 6 :=
  ⟨⟨64,30,55⟩,mass_cell 6 64 30 55 104 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2927985876725, 1029661376583, 201526547151, 13593942975, 7862449] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 6 :=
  ⟨⟨55,36,56⟩,mass_cell 6 55 36 56 97 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3006638517387, 1008896945138, 151461114470, 3818135025, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 6 :=
  ⟨⟨27,45,57⟩,mass_cell 6 27 45 57 90 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3087143251748, 992204731120, 92877729520, 67762504] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 6 :=
  ⟨⟨58,21,52⟩,mass_cell 6 58 21 52 119 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2692521401082, 1089965299872, 329191409568, 60334163616, 3448189761, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 6 :=
  ⟨⟨36,44,57⟩,mass_cell 6 36 44 57 91 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3085196934296, 989646772655, 97175441167, 152735414] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 6 :=
  ⟨⟨38,51,58⟩,mass_cell 6 38 51 58 87 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3155127687077, 960160612491, 58918085199, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 6 :=
  ⟨⟨61,18,51⟩,mass_cell 6 61 18 51 128 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2613605934360, 1105081123709, 361897099229, 73703827469, 3584416866, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 6 :=
  ⟨⟨68,40,57⟩,mass_cell 6 68 40 57 94 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3079546609892, 979983308372, 110386433032, 1006076977] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 6 :=
  ⟨⟨55,49,58⟩,mass_cell 6 55 49 58 88 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3153028115701, 956997426666, 64683830506, 1003514] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 6 :=
  ⟨⟨62,35,56⟩,mass_cell 6 62 35 56 98 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3005449011295, 1007397632997, 154600186521, 4677438122, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 6 :=
  ⟨⟨63,48,58⟩,mass_cell 6 63 48 58 89 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3152146778113, 955387270423, 67287509335, 7706093] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 6 :=
  ⟨⟨75,24,54⟩,mass_cell 6 75 24 54 114 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2850744275554, 1051627120581, 243481427661, 23434774113, 12975071, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 6 :=
  ⟨⟨69,34,56⟩,mass_cell 6 69 34 56 99 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3004172089804, 1004469153186, 156118071174, 5403293949, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 6 :=
  ⟨⟨78,16,52⟩,mass_cell 6 78 16 52 137 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2713180024428, 1118309148584, 316646947548, 26576401690, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 6 :=
  ⟨⟨81,27,55⟩,mass_cell 6 81 27 55 109 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2927625181222, 1028058558670, 199934542918, 12658166203, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 6 :=
  ⟨⟨75,33,56⟩,mass_cell 6 75 33 56 100 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3003850214333, 1004484175866, 157848102234, 6011563194, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 6 :=
  ⟨⟨83,18,53⟩,mass_cell 6 83 18 53 130 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2787291121418, 1095692298693, 275664341445, 16386221692, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 6 :=
  ⟨⟨71,47,58⟩,mass_cell 6 71 47 58 90 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3151238445358, 952835459816, 69422564384, 24404681] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 6 :=
  ⟨⟨87,21,54⟩,mass_cell 6 87 21 54 121 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2858699124400, 1065597920374, 234825551878, 10916042683, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 6 :=
  ⟨⟨86,31,56⟩,mass_cell 6 86 31 56 103 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3004047002628, 1005356393389, 158257508809, 5988510090, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 6 :=
  ⟨⟨87,13,52⟩,mass_cell 6 87 13 52 154 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2733104181229, 1140918546972, 285276733844, 5862946839, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 6 :=
  ⟨⟨85,45,58⟩,mass_cell 6 85 45 58 91 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3150199876756, 950882321984, 73329135296, 100666520] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 6 :=
  ⟨⟨92,15,53⟩,mass_cell 6 92 15 53 143 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2803660681254, 1118267757849, 249023348154, 2909238805, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 6 :=
  ⟨⟨85,26,55⟩,mass_cell 6 85 26 55 110 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2929763228649, 1033847674711, 200328363455, 10998435537, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 6 :=
  ⟨⟨93,54,59⟩,mass_cell 6 93 54 59 86 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3216467354578, 919270902034, 38905700518, 0] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 6 :=
  ⟨⟨98,43,58⟩,mass_cell 6 98 43 58 92 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3149502630678, 948580074971, 75299419359, 207963977] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 6 :=
  ⟨⟨100,53,59⟩,mass_cell 6 100 53 59 87 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3216186798358, 918253534800, 39991951504, 0] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 6 :=
  ⟨⟨104,42,58⟩,mass_cell 6 104 42 58 93 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3149340226289, 947785744935, 75497719815, 236945925] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 6 :=
  ⟨⟨107,52,59⟩,mass_cell 6 107 52 59 88 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3215897693110, 916573851026, 40725536190, 0] (by decide +kernel) (by decide +kernel)⟩
private def m50 : MassCell 6 :=
  ⟨⟨93,36,57⟩,mass_cell 6 93 36 57 98 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3077974642516, 976973930152, 115091506060, 1828476392, 0] (by decide +kernel) (by decide +kernel)⟩
private def m51 : MassCell 6 :=
  ⟨⟨109,41,58⟩,mass_cell 6 109 41 58 94 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3149597069496, 949603687310, 75914355822, 226934910] (by decide +kernel) (by decide +kernel)⟩
private def m52 : MassCell 6 :=
  ⟨⟨103,6,52⟩,mass_cell 6 103 6 52 234 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2792717775182, 1195115912397, 174903306776, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m53 : MassCell 6 :=
  ⟨⟨112,12,54⟩,mass_cell 6 112 12 54 163 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2900816839842, 1124914457289, 145578219811, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m54 : MassCell 6 :=
  ⟨⟨113,51,59⟩,mass_cell 6 113 51 59 88 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3215823784178, 916830346410, 41538477618, 121562] (by decide +kernel) (by decide +kernel)⟩
private def m55 : MassCell 6 :=
  ⟨⟨108,33,57⟩,mass_cell 6 108 33 57 101 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3079072121940, 979234338048, 110450917824, 569634108, 0] (by decide +kernel) (by decide +kernel)⟩
private def m56 : MassCell 6 :=
  ⟨⟨117,16,55⟩,mass_cell 6 117 16 55 140 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2960203992869, 1086672827009, 128752257802, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m57 : MassCell 6 :=
  ⟨⟨116,31,57⟩,mass_cell 6 116 31 57 104 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3081114903423, 985239320255, 104073259005, 16239350, 0] (by decide +kernel) (by decide +kernel)⟩
private def m58 : MassCell 6 :=
  ⟨⟨115,40,58⟩,mass_cell 6 115 40 58 95 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3149398020520, 947189955669, 74077654093, 114965505] (by decide +kernel) (by decide +kernel)⟩
private def m59 : MassCell 6 :=
  ⟨⟨119,50,59⟩,mass_cell 6 119 50 59 89 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3215742834084, 916501290523, 41935287475, 851988] (by decide +kernel) (by decide +kernel)⟩
private def m60 : MassCell 6 :=
  ⟨⟨119,9,54⟩,mass_cell 6 119 9 54 190 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 2916683525896, 1136290414146, 109369402260, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m61 : MassCell 6 :=
  ⟨⟨120,30,57⟩,mass_cell 6 120 30 57 106 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3082100659425, 987068594839, 98841773469, 14950, 0] (by decide +kernel) (by decide +kernel)⟩
private def m62 : MassCell 6 :=
  ⟨⟨119,39,58⟩,mass_cell 6 119 39 58 96 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3150065331418, 951161853218, 73865296815, 32537682] (by decide +kernel) (by decide +kernel)⟩
private def m63 : MassCell 6 :=
  ⟨⟨117,23,56⟩,mass_cell 6 117 23 56 118 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3016791204727, 1033027601862, 122527820925, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m64 : MassCell 6 :=
  ⟨⟨126,28,57⟩,mass_cell 6 126 28 57 109 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3085501901991, 998396949049, 91495714779, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m65 : MassCell 6 :=
  ⟨⟨126,20,56⟩,mass_cell 6 126 20 56 126 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3023898431466, 1043755416019, 98396029767, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m66 : MassCell 6 :=
  ⟨⟨125,49,59⟩,mass_cell 6 125 49 59 89 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3215654811392, 915559538150, 41824530982, 1133756] (by decide +kernel) (by decide +kernel)⟩
private def m67 : MassCell 6 :=
  ⟨⟨124,38,58⟩,mass_cell 6 124 38 58 97 (by decide)
    (by decide +kernel) [4693214279464, 4314329684548, 3958786547728, 3625609680844, 3150276511450, 950836035660, 71132114636, 46376, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 6) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51, m52, m53, m54, m55, m56, m57, m58, m59, m60, m61, m62, m63, m64, m65, m66, m67]

end Low6960Allocation.Group6
