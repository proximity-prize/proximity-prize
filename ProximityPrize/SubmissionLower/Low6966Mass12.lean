import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Low48BentCyclePrice
set_option Elab.async false


set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6966Allocation.Group12

private def m0 : MassCell 12 :=
  ⟨⟨2,5,11⟩,mass_cell 12 2 5 11 193 (by decide)
    (by decide +kernel) [4641220278784, 3879151726290, 3084575393742, 2410801955754, 1846578405030, 1380999414786, 1003507338750, 703892211162, 472291746774, 299191340850, 175424069166, 92170688010, 40959634182, 13667024994, 2516658270, 81404064, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 12 :=
  ⟨⟨2,6,18⟩,mass_cell 12 2 6 18 182 (by decide)
    (by decide +kernel) [4651458495628, 4096898108156, 3230984993348, 2471622551364, 1844996180420, 1337116683716, 934395760452, 623646005828, 392080911044, 227314863300, 117363145796, 50641937732, 15968314308, 2560246724, 48042502, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 12 :=
  ⟨⟨3,9,32⟩,mass_cell 12 3 9 32 157 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3707085631839, 2755645496272, 1909448262972, 1260102447240, 779983866100, 442212434112, 220652163372, 89911163512, 25341641700, 3039902640, 12866768, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 12 :=
  ⟨⟨1,11,37⟩,mass_cell 12 1 11 37 146 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 2965962736969, 1979155295881, 1238730432073, 710113327945, 358239277897, 147553688329, 42012077641, 5080076233, 21394307, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 12 :=
  ⟨⟨1,12,39⟩,mass_cell 12 1 12 39 141 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3066154537883, 2006650756436, 1219048646708, 669302079252, 315723178484, 115718099156, 25787026356, 1524175508, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 12 :=
  ⟨⟨2,15,44⟩,mass_cell 12 2 15 44 129 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3283822560536, 2125240126904, 1181733765500, 568076196384, 214991669732, 51260649992, 3719815884, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 12 :=
  ⟨⟨1,16,45⟩,mass_cell 12 1 16 45 126 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3317787289577, 2156322755340, 1167786916076, 536893784012, 186878687148, 36774457484, 1419630196, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 12 :=
  ⟨⟨1,18,47⟩,mass_cell 12 1 18 47 121 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3371373390516, 2233404237625, 1142746301181, 477902974881, 138574745125, 17249398665, 82472855, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 12 :=
  ⟨⟨5,21,50⟩,mass_cell 12 5 21 50 115 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2413723171685, 1129430052685, 407858553685, 87899674685, 4664884249, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 12 :=
  ⟨⟨8,24,52⟩,mass_cell 12 8 24 52 109 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2545865246472, 1108930140724, 342853248068, 51644216404, 716990296, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 12 :=
  ⟨⟨1,27,53⟩,mass_cell 12 1 27 53 105 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2613347445078, 1091133009723, 290482874715, 27800238139, 13071765] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 12 :=
  ⟨⟨1,30,54⟩,mass_cell 12 1 30 54 101 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2671909457855, 1057163758139, 235736416455, 13074946433, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 12 :=
  ⟨⟨1,32,55⟩,mass_cell 12 1 32 55 99 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2744592290374, 1077210847548, 218254519260, 8729870526, 0] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 12 :=
  ⟨⟨1,36,56⟩,mass_cell 12 1 36 56 96 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2802691385946, 1045776671508, 165334945140, 2451294782] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 12 :=
  ⟨⟨8,39,57⟩,mass_cell 12 8 39 57 94 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2863719471726, 1046673293077, 138281839157, 896162679] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 12 :=
  ⟨⟨1,45,58⟩,mass_cell 12 1 45 58 90 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2921006868773, 1033067451011, 93870219139, 15032211] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 12 :=
  ⟨⟨10,51,59⟩,mass_cell 12 10 51 59 88 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2971044107290, 1016911528985, 61865803359, 0] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 12 :=
  ⟨⟨62,4,45⟩,mass_cell 12 62 4 45 250 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3325500120022, 2226280140858, 1244039965418, 548600288313, 104979346849, 193033401, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 12 :=
  ⟨⟨66,16,52⟩,mass_cell 12 66 16 52 133 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2523383012247, 1084611607404, 356298593788, 70913136012, 2460007975, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 12 :=
  ⟨⟨48,27,55⟩,mass_cell 12 48 27 55 107 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2726525499957, 1050730497111, 245090191447, 23237580255, 63023337] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 12 :=
  ⟨⟨38,36,57⟩,mass_cell 12 38 36 57 97 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2857301697168, 1033549281266, 153829563618, 2825734241, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 12 :=
  ⟨⟨11,44,58⟩,mass_cell 12 11 44 58 91 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2919731411877, 1031820337844, 99136175732, 52139718] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 12 :=
  ⟨⟨63,33,57⟩,mass_cell 12 63 33 57 100 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2853458635748, 1024200831296, 163991464212, 5613214805, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 12 :=
  ⟨⟨41,41,58⟩,mass_cell 12 41 41 58 93 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2915712122477, 1021390894068, 112055684064, 441006936] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 12 :=
  ⟨⟨31,49,59⟩,mass_cell 12 31 49 59 89 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2969451890731, 1011161519321, 68245994265, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 12 :=
  ⟨⟨52,30,56⟩,mass_cell 12 52 30 56 103 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2791867488554, 1040065442998, 204919917998, 12272666086, 5372] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 12 :=
  ⟨⟨59,39,58⟩,mass_cell 12 59 39 58 95 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2913646631517, 1014309005443, 118464838323, 1000955885] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 12 :=
  ⟨⟨50,47,59⟩,mass_cell 12 50 47 59 90 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2968207182016, 1006459531482, 74290768590, 5421283] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 12 :=
  ⟨⟨67,21,54⟩,mass_cell 12 67 21 54 119 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2657489449274, 1059560127827, 288643982115, 42662532803, 1247650125, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 12 :=
  ⟨⟨59,46,59⟩,mass_cell 12 59 46 59 91 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2967667792559, 1004023303191, 76982921531, 20450834] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 12 :=
  ⟨⟨74,37,58⟩,mass_cell 12 74 37 58 97 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2912642549356, 1012045691594, 124079684934, 1760481902, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 12 :=
  ⟨⟨75,44,59⟩,mass_cell 12 75 44 59 92 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2966959720030, 1001703280032, 82109112480, 102435552] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 12 :=
  ⟨⟨69,24,55⟩,mass_cell 12 69 24 55 112 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2723014131348, 1042899164160, 247303267712, 27345132032, 347723138, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 12 :=
  ⟨⟨79,53,60⟩,mass_cell 12 79 53 60 87 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 3012229139918, 992947795175, 46124471347, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 12 :=
  ⟨⟨84,21,55⟩,mass_cell 12 84 21 55 120 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2726510385468, 1051520827278, 245073248778, 20365201683, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 12 :=
  ⟨⟨77,31,57⟩,mass_cell 12 77 31 57 103 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2852342085716, 1021190579198, 167232558474, 7130295590, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 12 :=
  ⟨⟨89,16,54⟩,mass_cell 12 89 16 54 135 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2669375090133, 1080263518818, 271073024178, 14194927868, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 12 :=
  ⟨⟨79,26,56⟩,mass_cell 12 79 26 56 110 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2789382915222, 1034312160145, 209170119757, 15714217129, 24361079, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 12 :=
  ⟨⟨88,52,60⟩,mass_cell 12 88 52 60 88 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 3012030985262, 989854958364, 47323866620, 0] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 12 :=
  ⟨⟨95,51,60⟩,mass_cell 12 95 51 60 89 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 3011971109472, 990349123475, 48980389875, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 12 :=
  ⟨⟨92,15,54⟩,mass_cell 12 92 15 54 139 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2674066024981, 1089927190460, 266453103064, 9358457391, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 12 :=
  ⟨⟨85,25,56⟩,mass_cell 12 85 25 56 111 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2789296322265, 1032702253044, 206213395024, 13870330619, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 12 :=
  ⟨⟨83,43,59⟩,mass_cell 12 83 43 59 93 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2966591812769, 999360742597, 83792357261, 171875722] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 12 :=
  ⟨⟨96,18,55⟩,mass_cell 12 96 18 55 129 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2733440920467, 1066090150662, 231269358902, 6680410038, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 12 :=
  ⟨⟨94,28,57⟩,mass_cell 12 94 28 57 107 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2852964004842, 1024126611574, 167349579206, 6383733190, 0] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 12 :=
  ⟨⟨97,41,59⟩,mass_cell 12 97 41 59 94 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2966235204755, 997738198521, 86589032721, 345167073] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 12 :=
  ⟨⟨103,50,60⟩,mass_cell 12 103 50 60 89 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 3011839191373, 988158671577, 49893049701, 60657] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 12 :=
  ⟨⟨103,11,54⟩,mass_cell 12 103 11 54 163 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2694171843780, 1126288042334, 227766082192, 360012966, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 12 :=
  ⟨⟨110,39,59⟩,mass_cell 12 110 39 59 96 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2966052089350, 996033212860, 86957751208, 422809336] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 12 :=
  ⟨⟨110,49,60⟩,mass_cell 12 110 49 60 90 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 3011775899914, 987579058236, 50865539816, 1215074] (by decide +kernel) (by decide +kernel)⟩
private def m50 : MassCell 12 :=
  ⟨⟨81,36,58⟩,mass_cell 12 81 36 58 98 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2912302848090, 1011058778220, 125893829068, 2133161171, 0] (by decide +kernel) (by decide +kernel)⟩
private def m51 : MassCell 12 :=
  ⟨⟨88,35,58⟩,mass_cell 12 88 35 58 99 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2911941650434, 1009107652507, 126448156051, 2396102596, 0] (by decide +kernel) (by decide +kernel)⟩
private def m52 : MassCell 12 :=
  ⟨⟨117,48,60⟩,mass_cell 12 117 48 60 90 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 3011710973338, 986453914350, 51397673182, 4063940] (by decide +kernel) (by decide +kernel)⟩
private def m53 : MassCell 12 :=
  ⟨⟨111,31,58⟩,mass_cell 12 111 31 58 104 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2912303332390, 1009673250705, 122545616377, 1154230329, 0] (by decide +kernel) (by decide +kernel)⟩
private def m54 : MassCell 12 :=
  ⟨⟨116,38,59⟩,mass_cell 12 116 38 59 97 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2966052632584, 995592213594, 86203479186, 338483687, 0] (by decide +kernel) (by decide +kernel)⟩
private def m55 : MassCell 12 :=
  ⟨⟨115,6,54⟩,mass_cell 12 115 6 54 218 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2721657022585, 1163739767345, 161217852875, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m56 : MassCell 12 :=
  ⟨⟨115,30,58⟩,mass_cell 12 115 30 58 105 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2913063714689, 1014424460753, 121513297461, 604275694, 0] (by decide +kernel) (by decide +kernel)⟩
private def m57 : MassCell 12 :=
  ⟨⟨121,37,59⟩,mass_cell 12 121 37 59 98 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2966253272103, 997566167010, 85706829126, 196299453, 0] (by decide +kernel) (by decide +kernel)⟩
private def m58 : MassCell 12 :=
  ⟨⟨113,12,55⟩,mass_cell 12 113 12 55 157 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2755946462474, 1114135088980, 179391477536, 2331890, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m59 : MassCell 12 :=
  ⟨⟨123,47,60⟩,mass_cell 12 123 47 60 91 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 3011715283792, 987109925788, 52024034224, 7886185] (by decide +kernel) (by decide +kernel)⟩
private def m60 : MassCell 12 :=
  ⟨⟨127,27,58⟩,mass_cell 12 127 27 58 110 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2915285330930, 1025115260330, 110220416356, 52360, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m61 : MassCell 12 :=
  ⟨⟨126,36,59⟩,mass_cell 12 126 36 59 99 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2966448883527, 998974085238, 84164600054, 46411566, 0] (by decide +kernel) (by decide +kernel)⟩
private def m62 : MassCell 12 :=
  ⟨⟨129,46,60⟩,mass_cell 12 129 46 60 92 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 3011718260332, 987287351337, 52144279781, 8785579] (by decide +kernel) (by decide +kernel)⟩
private def m63 : MassCell 12 :=
  ⟨⟨118,16,56⟩,mass_cell 12 118 16 56 137 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2807349258768, 1079983520820, 156255403163, 249900, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m64 : MassCell 12 :=
  ⟨⟨122,21,57⟩,mass_cell 12 122 21 57 122 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2861231707227, 1051874248780, 136267445667, 292825, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m65 : MassCell 12 :=
  ⟨⟨131,35,59⟩,mass_cell 12 131 35 59 100 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2966639436711, 999790639721, 81479549322, 316251, 0] (by decide +kernel) (by decide +kernel)⟩
private def m66 : MassCell 12 :=
  ⟨⟨136,9,56⟩,mass_cell 12 136 9 56 181 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2827862198121, 1117721073078, 92932735328, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m67 : MassCell 12 :=
  ⟨⟨135,34,59⟩,mass_cell 12 135 34 59 101 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2967033790964, 1003355412883, 79532032647, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 12) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51, m52, m53, m54, m55, m56, m57, m58, m59, m60, m61, m62, m63, m64, m65, m66, m67]

end Low6966Allocation.Group12
