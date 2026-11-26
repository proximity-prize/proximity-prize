import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Low48BentCyclePrice
set_option Elab.async false


set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6966Allocation.Group11

private def m0 : MassCell 11 :=
  ⟨⟨2,5,8⟩,mass_cell 11 2 5 8 190 (by decide)
    (by decide +kernel) [4618363613502, 3810851996241, 3046518290073, 2393207797017, 1841801881809, 1383287724993, 1008758322921, 709412487753, 476554847457, 301595845809, 176051742393, 91544612601, 39802347633, 12658654497, 2053056009, 39599392] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 11 :=
  ⟨⟨2,6,16⟩,mass_cell 11 2 6 16 180 (by decide)
    (by decide +kernel) [4669890331228, 4079257488100, 3213178537686, 2471252232686, 1853985010886, 1349686952286, 946737256886, 633584244686, 398745355686, 230807149886, 118425307286, 50324627886, 15299031686, 2211558686, 25387968] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 11 :=
  ⟨⟨2,8,26⟩,mass_cell 11 2 8 26 162 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3551993795910, 2623286072262, 1871756478534, 1279009611462, 826506740550, 495565808070, 267361429062, 122924891334, 43144155462, 8763854790, 385891453, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 11 :=
  ⟨⟨3,9,30⟩,mass_cell 11 3 9 30 155 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3709656659028, 2722591766602, 1891532910118, 1249814516114, 772893923278, 436243655962, 215351424182, 85720123618, 22867835614, 2327827178, 2683796] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 11 :=
  ⟨⟨3,10,33⟩,mass_cell 11 3 10 33 149 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3799136565926, 2825070593795, 1917991971655, 1229045179627, 728541843695, 386603924563, 173163717655, 57963853115, 10557295807, 316656268, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 11 :=
  ⟨⟨1,12,37⟩,mass_cell 11 1 12 37 139 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3007786042176, 1962753668736, 1187948163520, 646594589952, 299653087296, 105818870656, 21522230976, 930461314, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 11 :=
  ⟨⟨1,15,42⟩,mass_cell 11 1 15 42 127 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3273632932226, 2060435984171, 1139661316323, 540023254787, 197643860363, 43287930747, 2363147342, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 11 :=
  ⟨⟨6,16,44⟩,mass_cell 11 6 16 44 125 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3360387485284, 2115400477756, 1122911833516, 503504140316, 169004930956, 31020554236, 959707777, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 11 :=
  ⟨⟨6,18,46⟩,mass_cell 11 6 18 46 120 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3432273956494, 2189391428386, 1095761884994, 445126759138, 123200222722, 13782874274, 33899982] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 11 :=
  ⟨⟨1,21,48⟩,mass_cell 11 1 21 48 113 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3480135050408, 2294038661575, 1065961140023, 373359491671, 73082956519, 2674381395, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 11 :=
  ⟨⟨2,24,50⟩,mass_cell 11 2 24 50 107 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2428895834464, 1034929505744, 307161641536, 39801348784, 228855118] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 11 :=
  ⟨⟨1,26,51⟩,mass_cell 11 1 26 51 105 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2502938502553, 1017331876627, 269453044735, 25218401803, 8589931] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 11 :=
  ⟨⟨1,29,52⟩,mass_cell 11 1 29 52 101 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2561597091100, 964095203799, 209238664959, 10539598482, 0] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 11 :=
  ⟨⟨1,31,53⟩,mass_cell 11 1 31 53 99 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2645342606761, 968926873604, 188042582872, 6401766472, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 11 :=
  ⟨⟨1,35,54⟩,mass_cell 11 1 35 54 95 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2707708239984, 914257043590, 133039065442, 1314402581] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 11 :=
  ⟨⟨1,38,55⟩,mass_cell 11 1 38 55 93 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2788213585168, 915583108227, 110318691399, 350970357] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 11 :=
  ⟨⟨10,42,56⟩,mass_cell 11 10 42 56 90 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2855363321095, 881634395654, 78830363174, 14629682] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 11 :=
  ⟨⟨11,48,57⟩,mass_cell 11 11 48 57 87 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2924575070867, 846264565684, 47886700208, 0] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 11 :=
  ⟨⟨60,15,49⟩,mass_cell 11 60 15 49 134 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2312207614797, 1026881331797, 368752903397, 91090046589, 9026570471, 23751, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 11 :=
  ⟨⟨56,25,53⟩,mass_cell 11 56 25 53 108 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2617238633856, 952038350825, 226075683913, 23587166809, 150808267] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 11 :=
  ⟨⟨32,35,55⟩,mass_cell 11 32 35 55 96 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2776720970581, 910110621105, 129715976745, 1761938649] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 11 :=
  ⟨⟨64,4,43⟩,mass_cell 11 64 4 43 248 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3332687254347, 2156003942786, 1195248545618, 517161160825, 91209382867, 86887681, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 11 :=
  ⟨⟨67,18,51⟩,mass_cell 11 67 18 51 125 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2462173240913, 987812096793, 298428133085, 53308332929, 2217552622, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 11 :=
  ⟨⟨59,28,54⟩,mass_cell 11 59 28 54 104 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2692279129127, 926455225728, 184521017600, 12033223808, 1157751] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 11 :=
  ⟨⟨67,31,55⟩,mass_cell 11 67 31 55 101 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2766525671487, 899194104480, 145339862780, 5302661700, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 11 :=
  ⟨⟨50,38,56⟩,mass_cell 11 50 38 56 94 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2844781834685, 874228215056, 97290395096, 499995340] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 11 :=
  ⟨⟨22,47,57⟩,mass_cell 11 22 47 57 88 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2922291994508, 844780224939, 51252789939, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 11 :=
  ⟨⟨67,36,56⟩,mass_cell 11 67 36 56 96 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2841467544130, 870901545116, 104147062716, 1133196458] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 11 :=
  ⟨⟨61,43,57⟩,mass_cell 11 61 43 57 91 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2915426870889, 839309871453, 63926757957, 16388903] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 11 :=
  ⟨⟨64,51,58⟩,mass_cell 11 64 51 58 87 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2984857996447, 799377695191, 33250238532, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 11 :=
  ⟨⟨70,42,57⟩,mass_cell 11 70 42 57 91 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2914004192454, 837004809186, 66385730498, 46265470] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 11 :=
  ⟨⟨74,30,55⟩,mass_cell 11 74 30 55 102 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2765764291629, 898898035200, 147720185064, 6148689232, 0] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 11 :=
  ⟨⟨64,21,52⟩,mass_cell 11 64 21 52 117 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2538605393425, 969975060841, 265416533097, 40033807953, 1390965409, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 11 :=
  ⟨⟨66,27,54⟩,mass_cell 11 66 27 54 106 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2691289662473, 926231586035, 187434366379, 13609345315, 12232392] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 11 :=
  ⟨⟨75,35,56⟩,mass_cell 11 75 35 56 97 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2840113882986, 868785970939, 106415094139, 1503726854, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 11 :=
  ⟨⟨64,24,53⟩,mass_cell 11 64 24 53 110 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2613707782084, 945586238672, 224940566624, 24727419888, 274722641, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 11 :=
  ⟨⟨81,49,58⟩,mass_cell 11 81 49 58 88 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2983482245967, 799016592838, 36951387450, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 11 :=
  ⟨⟨88,16,52⟩,mass_cell 11 88 16 52 133 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2553849820321, 987099669160, 249565794904, 15020338873, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 11 :=
  ⟨⟨73,26,54⟩,mass_cell 11 73 26 54 108 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2690105612702, 924144814435, 187876473295, 14384757595, 33446625] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 11 :=
  ⟨⟨81,21,53⟩,mass_cell 11 81 21 53 118 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2616634494798, 950585531285, 224572233533, 21757137956, 1581580, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 11 :=
  ⟨⟨90,48,58⟩,mass_cell 11 90 48 58 88 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2982570682844, 796492188440, 38253778632, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 11 :=
  ⟨⟨94,18,53⟩,mass_cell 11 94 18 53 127 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2626780644664, 963943589102, 212390887902, 7944413354, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 11 :=
  ⟨⟨87,28,55⟩,mass_cell 11 87 28 55 105 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2765140554574, 897953562836, 148625246836, 6651521987, 0] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 11 :=
  ⟨⟨98,47,58⟩,mass_cell 11 98 47 58 89 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2982003986973, 795406884182, 39544762202, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 11 :=
  ⟨⟨105,46,58⟩,mass_cell 11 105 46 58 90 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2981787836075, 795932122969, 40867394653, 369982] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 11 :=
  ⟨⟨78,41,57⟩,mass_cell 11 78 41 57 92 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2913128453296, 836324006055, 68838623583, 97947043] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 11 :=
  ⟨⟨104,15,53⟩,mass_cell 11 104 15 53 138 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2642683078672, 984783771065, 187759588510, 583049717, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 11 :=
  ⟨⟨103,25,55⟩,mass_cell 11 103 25 55 110 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2767934871347, 901739666311, 141970320839, 2798592755, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 11 :=
  ⟨⟨100,38,57⟩,mass_cell 11 100 38 57 95 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2911432634165, 833882727846, 73219957734, 336299775] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 11 :=
  ⟨⟨112,45,58⟩,mass_cell 11 112 45 58 90 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2981551391666, 795735270052, 41773995928, 2545493] (by decide +kernel) (by decide +kernel)⟩
private def m50 : MassCell 11 :=
  ⟨⟨113,36,57⟩,mass_cell 11 113 36 57 97 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2911115153713, 832364011624, 72791895528, 319969023, 0] (by decide +kernel) (by decide +kernel)⟩
private def m51 : MassCell 11 :=
  ⟨⟨110,13,53⟩,mass_cell 11 110 13 53 149 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2654377455984, 997359743416, 163717112541, 11719700, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m52 : MassCell 11 :=
  ⟨⟨82,34,56⟩,mass_cell 11 82 34 56 98 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2839575505407, 868782283218, 108612584386, 1877584723, 0] (by decide +kernel) (by decide +kernel)⟩
private def m53 : MassCell 11 :=
  ⟨⟨113,12,53⟩,mass_cell 11 113 12 53 155 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2660082862678, 1001698728032, 149969745852, 35960, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m54 : MassCell 11 :=
  ⟨⟨89,33,56⟩,mass_cell 11 89 33 56 99 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2838959532919, 867529360922, 109450130734, 2138638531, 0] (by decide +kernel) (by decide +kernel)⟩
private def m55 : MassCell 11 :=
  ⟨⟨117,28,56⟩,mass_cell 11 117 28 56 106 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2841350530676, 870480995464, 100580171160, 159940427, 0] (by decide +kernel) (by decide +kernel)⟩
private def m56 : MassCell 11 :=
  ⟨⟨119,35,57⟩,mass_cell 11 119 35 57 98 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2911211617854, 831791278353, 71326973289, 160945046, 0] (by decide +kernel) (by decide +kernel)⟩
private def m57 : MassCell 11 :=
  ⟨⟨119,44,58⟩,mass_cell 11 119 44 58 91 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2981294501131, 794777870568, 42153091464, 6165592] (by decide +kernel) (by decide +kernel)⟩
private def m58 : MassCell 11 :=
  ⟨⟨118,10,53⟩,mass_cell 11 118 10 53 169 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2673750791365, 1015151435398, 127584298522, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m59 : MassCell 11 :=
  ⟨⟨126,43,58⟩,mass_cell 11 126 43 58 92 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2981017002223, 793020560599, 41878459295, 7110930] (by decide +kernel) (by decide +kernel)⟩
private def m60 : MassCell 11 :=
  ⟨⟨129,25,56⟩,mass_cell 11 129 25 56 111 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2846741641825, 880752097784, 86406658626, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m61 : MassCell 11 :=
  ⟨⟨124,34,57⟩,mass_cell 11 124 34 57 99 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2911905971972, 833775377052, 69926550427, 28213269, 0] (by decide +kernel) (by decide +kernel)⟩
private def m62 : MassCell 11 :=
  ⟨⟨121,9,53⟩,mass_cell 11 121 9 53 178 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2679186821648, 1015387507190, 112608769575, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m63 : MassCell 11 :=
  ⟨⟨132,42,58⟩,mass_cell 11 132 42 58 92 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2981101255680, 793174726076, 41529160676, 658851] (by decide +kernel) (by decide +kernel)⟩
private def m64 : MassCell 11 :=
  ⟨⟨129,33,57⟩,mass_cell 11 129 33 57 100 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2912572397838, 834963943536, 67282624171, 4845, 0] (by decide +kernel) (by decide +kernel)⟩
private def m65 : MassCell 11 :=
  ⟨⟨134,54,59⟩,mass_cell 11 134 54 59 86 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 3047453390745, 751843669064, 18451920577, 0] (by decide +kernel) (by decide +kernel)⟩
private def m66 : MassCell 11 :=
  ⟨⟨132,4,53⟩,mass_cell 11 132 4 53 258 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2715725342677, 1035232137150, 63250683621, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m67 : MassCell 11 :=
  ⟨⟨119,21,55⟩,mass_cell 11 119 21 55 120 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2777663093574, 916937511054, 118286649789, 1028790, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m68 : MassCell 11 :=
  ⟨⟨137,41,58⟩,mass_cell 11 137 41 58 93 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2981553096973, 795448478214, 41216703894, 0] (by decide +kernel) (by decide +kernel)⟩
private def m69 : MassCell 11 :=
  ⟨⟨136,23,56⟩,mass_cell 11 136 23 56 116 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2851138615522, 888200392368, 75297979439, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 11) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51, m52, m53, m54, m55, m56, m57, m58, m59, m60, m61, m62, m63, m64, m65, m66, m67, m68, m69]

end Low6966Allocation.Group11
