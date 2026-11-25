import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass0

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group0
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def priceBatch0 : P :=
  ⟨unpack [2348878853, 755044361, 4513141769, 4412480525, 21693211661, 73485663253], by decide +kernel⟩
private def priceBatch1 : P :=
  ⟨unpack [83958829, 8791466029, 82311545901, 352392257, 134289473, 4647492677], by decide +kernel⟩
private def priceBatch2 : P :=
  ⟨unpack [26525903941, 26628248649, 18221048929, 5989931109, 35167094921, 60601691273], by decide +kernel⟩
private def priceBatch3 : P :=
  ⟨unpack [22935442585, 31626367169, 43254393049, 27046983933, 26393079037, 30453303549], by decide +kernel⟩
private def priceBatch4 : P :=
  ⟨unpack [25890116889, 21712513317, 17367286053, 12971660601, 8844535097, 22383252813], by decide +kernel⟩
private def priceBatch5 : P :=
  ⟨unpack [4348171601, 4348239185, 8693465429, 4381723989, 39562981725, 13290277213], by decide +kernel⟩
private def priceBatch6 : P :=
  ⟨unpack [13122509149, 8777279841, 8693396833, 36427105, 53270881, 19717473], by decide +kernel⟩
private def priceBatch7 : P :=
  ⟨unpack [2941281, 2941285, 2940265, 2941288, 36425069, 19648877], by decide +kernel⟩
private def priceBatch8 : P :=
  ⟨unpack [2872684, 2940268, 2941292, 4348166513, 53201265, 2872688], by decide +kernel⟩
private def priceBatch9 : P :=
  ⟨unpack [2939248, 2940272, 2941296, 2871668, 2938228, 2939252], by decide +kernel⟩
private def priceBatch10 : P :=
  ⟨unpack [2940276, 2941300, 2870648, 2871672, 2938232, 2939256], by decide +kernel⟩
private def priceBatch11 : P :=
  ⟨unpack [2940280, 2941304, 53273977, 19720569, 2944376, 4381717885], by decide +kernel⟩
private def priceBatch12 : P :=
  ⟨unpack [86752637, 2870652, 2871676, 2938236, 2939260, 2940284], by decide +kernel⟩
private def priceBatch13 : P :=
  ⟨unpack [2941308, 2944380, 36422017, 19645825, 2869632, 2870656], by decide +kernel⟩
private def priceBatch14 : P :=
  ⟨unpack [2871680, 2938240, 2939264, 2940288, 2941312, 2943360], by decide +kernel⟩
private def priceBatch15 : P :=
  ⟨unpack [2944384, 2869636, 2870660, 2871684, 2938244, 2939268], by decide +kernel⟩
private def priceBatch16 : P :=
  ⟨unpack [2940292, 2941316, 2943364, 2944388, 2868616, 2869640], by decide +kernel⟩
private def priceBatch17 : P :=
  ⟨unpack [2870664, 2871688, 2938248, 2939272, 2940296, 2941320], by decide +kernel⟩
private def priceBatch18 : P :=
  ⟨unpack [2942344, 2943368, 2944392, 2867597, 2868620, 2869644], by decide +kernel⟩
private def priceBatch19 : P :=
  ⟨unpack [2870668, 2937228, 2938252, 2939276, 2940300, 2941324], by decide +kernel⟩
private def priceBatch20 : P :=
  ⟨unpack [2942348, 2943372, 2944396, 4381649297, 120304017, 2867600], by decide +kernel⟩
private def priceBatch21 : P :=
  ⟨unpack [2868624, 2869648, 2870672, 2937232, 2938256, 2939280], by decide +kernel⟩
private def priceBatch22 : P :=
  ⟨unpack [2940304, 2941328, 2942352, 2943376, 2944400, 17719389589], by decide +kernel⟩
private def priceBatch23 : P :=
  ⟨unpack [13239943573, 69973397, 36419989, 2866581, 2867604, 2868628], by decide +kernel⟩
private def priceBatch24 : P :=
  ⟨unpack [2869652, 2870676, 2937236, 2938260, 2939284, 2940308], by decide +kernel⟩
private def priceBatch25 : P :=
  ⟨unpack [2941332, 2942356, 2943380, 2944404, 4532640153, 4448756121], by decide +kernel⟩
private def priceBatch26 : P :=
  ⟨unpack [2866584, 2867608, 2868632, 2869656, 2870680, 2937240], by decide +kernel⟩
private def priceBatch27 : P :=
  ⟨unpack [2938264, 2939288, 2940312, 2941336, 2942360, 2943384], by decide +kernel⟩
private def priceBatch28 : P :=
  ⟨unpack [2944408, 2866588, 2867612, 2868636, 2869660, 2870684], by decide +kernel⟩
private def priceBatch29 : P :=
  ⟨unpack [2937244, 2938268, 2939292, 2940316, 2941340, 2942364], by decide +kernel⟩
private def priceBatch30 : P :=
  ⟨unpack [2943388, 2944412, 2865569, 2866592, 2867616, 2868640], by decide +kernel⟩
private def priceBatch31 : P :=
  ⟨unpack [2869664, 2870688, 2937248, 2938272, 2939296, 2940320], by decide +kernel⟩
private def priceBatch32 : P :=
  ⟨unpack [2941344, 2942368, 2943392, 2944416, 2865572, 2866596], by decide +kernel⟩
private def priceBatch33 : P :=
  ⟨unpack [2867620, 2868644, 2869668, 2870692, 2937252, 2938276], by decide +kernel⟩
private def priceBatch34 : P :=
  ⟨unpack [2939300, 2940324, 2941348, 2942372, 2943396, 2944420], by decide +kernel⟩
private def priceBatch35 : P :=
  ⟨unpack [120301993, 86748585, 2864553, 2865576, 2866600, 2867624], by decide +kernel⟩
private def priceBatch36 : P :=
  ⟨unpack [2868648, 2869672, 2936232, 2937256, 2938280, 2939304], by decide +kernel⟩
private def priceBatch37 : P :=
  ⟨unpack [2940328, 2941352, 2942376, 2943400, 2944424, 2864556], by decide +kernel⟩
private def priceBatch38 : P :=
  ⟨unpack [2865580, 2866604, 2867628, 2868652, 2869676, 2936236], by decide +kernel⟩
private def priceBatch39 : P :=
  ⟨unpack [2937260, 2938284, 2939308, 2940332, 2941356, 2942380], by decide +kernel⟩
private def priceBatch40 : P :=
  ⟨unpack [2943404, 2944428, 19640753, 2864560, 2865584, 2866608], by decide +kernel⟩
private def priceBatch41 : P :=
  ⟨unpack [2867632, 2868656, 2869680, 2936240, 2937264, 2938288], by decide +kernel⟩
private def priceBatch42 : P :=
  ⟨unpack [2939312, 2940336, 2941360, 2942384, 2943408, 2944432], by decide +kernel⟩
private def priceBatch43 : P :=
  ⟨unpack [2864564, 2865588, 2866612, 2867636, 2868660, 2869684], by decide +kernel⟩
private def priceBatch44 : P :=
  ⟨unpack [2936244, 2937268, 2938292, 2939316, 2940340, 2941364], by decide +kernel⟩
private def priceBatch45 : P :=
  ⟨unpack [2942388, 2943412, 2944436, 2863544, 2864568, 2865592], by decide +kernel⟩
private def priceBatch46 : P :=
  ⟨unpack [2866616, 2867640, 2868664, 2869688, 2936248, 2937272], by decide +kernel⟩
private def priceBatch47 : P :=
  ⟨unpack [2938296, 2939320, 2940344, 2941368, 2942392, 2943416], by decide +kernel⟩
private def priceBatch48 : P :=
  ⟨unpack [2944440, 2863548, 2864572, 2865596, 2866620, 2867644], by decide +kernel⟩
private def priceBatch49 : P :=
  ⟨unpack [2868668, 2869692, 2936252, 2937276, 2938300, 2939324], by decide +kernel⟩
private def priceBatch50 : P :=
  ⟨unpack [2940348, 2941372, 2942396, 2943420, 2944444, 4532638145], by decide +kernel⟩
private def priceBatch51 : P :=
  ⟨unpack [103457217, 86746561, 2862529, 2863552, 2864576, 2865600], by decide +kernel⟩
private def priceBatch52 : P :=
  ⟨unpack [2866624, 2867648, 2868672, 2935232, 2936256, 2937280], by decide +kernel⟩
private def priceBatch53 : P :=
  ⟨unpack [2938304, 2939328, 2940352, 2941376, 2942400, 2943424], by decide +kernel⟩
private def priceBatch54 : P :=
  ⟨unpack [2944448, 2862532, 2863556, 2864580, 2865604, 2866628], by decide +kernel⟩
private def priceBatch55 : P :=
  ⟨unpack [2867652, 2868676, 2935236, 2936260, 2937284, 2938308], by decide +kernel⟩
private def priceBatch56 : P :=
  ⟨unpack [2939332, 2940356, 2941380, 2942404, 2943428, 2944452], by decide +kernel⟩
private def priceBatch57 : P :=
  ⟨unpack [19638729, 2862536, 2863560, 2864584, 2865608, 2866632], by decide +kernel⟩
private def priceBatch58 : P :=
  ⟨unpack [2867656, 2868680, 2935240, 2936264, 2937288, 2938312], by decide +kernel⟩
private def priceBatch59 : P :=
  ⟨unpack [2939336, 2940360, 2941384, 2942408, 2943432, 2944456], by decide +kernel⟩
private def priceBatch60 : P :=
  ⟨unpack [2862540, 2863564, 2864588, 2865612, 2866636, 2867660], by decide +kernel⟩
private def priceBatch61 : P :=
  ⟨unpack [2868684, 2935244, 2936268, 2937292, 2938316, 2939340], by decide +kernel⟩
private def priceBatch62 : P :=
  ⟨unpack [2940364, 2941388, 2942412, 2943436, 2944460, 2861521], by decide +kernel⟩
private def priceBatch63 : P :=
  ⟨unpack [2862544, 2863568, 2864592, 2865616, 2866640, 2867664], by decide +kernel⟩
private def priceBatch64 : P :=
  ⟨unpack [2868688, 2935248, 2936272, 2937296, 2938320, 2939344], by decide +kernel⟩
private def priceBatch65 : P :=
  ⟨unpack [2940368, 2941392, 2942416, 2943440, 2944464, 153786837], by decide +kernel⟩
private def priceBatch66 : P :=
  ⟨unpack [86678997, 2861524, 2862548, 2863572, 2864596, 2865620], by decide +kernel⟩
private def priceBatch67 : P :=
  ⟨unpack [2866644, 2867668, 2934228, 2935252, 2936276, 2937300], by decide +kernel⟩
private def priceBatch68 : P :=
  ⟨unpack [2938324, 2939348, 2940372, 2941396, 2942420, 2943444], by decide +kernel⟩
private def priceBatch69 : P :=
  ⟨unpack [2944468, 19637721, 2861528, 2862552, 2863576, 2864600], by decide +kernel⟩
private def priceBatch70 : P :=
  ⟨unpack [2865624, 2866648, 2867672, 2934232, 2935256, 2936280], by decide +kernel⟩
private def priceBatch71 : P :=
  ⟨unpack [2937304, 2938328, 2939352, 2940376, 2941400, 2942424], by decide +kernel⟩
private def priceBatch72 : P :=
  ⟨unpack [2943448, 2944472, 53191133, 2861532, 2862556, 2863580], by decide +kernel⟩
private def priceBatch73 : P :=
  ⟨unpack [2864604, 2865628, 2866652, 2867676, 2934236, 2935260], by decide +kernel⟩
private def priceBatch74 : P :=
  ⟨unpack [2936284, 2937308, 2938332, 2939356, 2940380, 2941404], by decide +kernel⟩
private def priceBatch75 : P :=
  ⟨unpack [2942428, 2943452, 2944476, 2860512, 2861536, 2862560], by decide +kernel⟩
private def priceBatch76 : P :=
  ⟨unpack [2863584, 2864608, 2865632, 2866656, 2867680, 2934240], by decide +kernel⟩
private def priceBatch77 : P :=
  ⟨unpack [2935264, 2936288, 2937312, 2938336, 2939360, 2940384], by decide +kernel⟩
private def priceBatch78 : P :=
  ⟨unpack [2941408, 2942432, 2943456, 2944480, 2860516, 2861540], by decide +kernel⟩
private def priceBatch79 : P :=
  ⟨unpack [2862564, 2863588, 2864612, 2865636, 2866660, 2867684], by decide +kernel⟩
private def priceBatch80 : P :=
  ⟨unpack [2934244, 2935268, 2936292, 2937316, 2938340, 2939364], by decide +kernel⟩
private def priceBatch81 : P :=
  ⟨unpack [2940388, 2941412, 2942436, 2943460, 2944484, 2860520], by decide +kernel⟩
private def priceBatch82 : P :=
  ⟨unpack [2861544, 2862568, 2863592, 2864616, 2865640, 2866664], by decide +kernel⟩
private def priceBatch83 : P :=
  ⟨unpack [2867688, 2934248, 2935272, 2936296, 2937320, 2938344], by decide +kernel⟩
private def priceBatch84 : P :=
  ⟨unpack [2939368, 2940392, 2941416, 2942440, 2943464, 2944488], by decide +kernel⟩
private def priceBatch85 : P :=
  ⟨unpack [8861155821, 4465528301, 69967341, 2859501, 2860524, 2861548], by decide +kernel⟩
private def priceBatch86 : P :=
  ⟨unpack [2862572, 2863596, 2864620, 2865644, 2866668, 2933228], by decide +kernel⟩
private def priceBatch87 : P :=
  ⟨unpack [2934252, 2935276, 2936300, 2937324, 2938348, 2939372], by decide +kernel⟩
private def priceBatch88 : P :=
  ⟨unpack [2940396, 2941420, 2942444, 2943468, 2944492, 2859505], by decide +kernel⟩
private def priceBatch89 : P :=
  ⟨unpack [2860528, 2861552, 2862576, 2863600, 2864624, 2865648], by decide +kernel⟩
private def priceBatch90 : P :=
  ⟨unpack [2866672, 2933232, 2934256, 2935280, 2936304, 2937328], by decide +kernel⟩
private def priceBatch91 : P :=
  ⟨unpack [2938352, 2939376, 2940400, 2941424, 2942448, 2943472], by decide +kernel⟩
private def priceBatch92 : P :=
  ⟨unpack [2944496, 2859508, 2860532, 2861556, 2862580, 2863604], by decide +kernel⟩
private def priceBatch93 : P :=
  ⟨unpack [2864628, 2865652, 2866676, 2933236, 2934260, 2935284], by decide +kernel⟩
private def priceBatch94 : P :=
  ⟨unpack [2936308, 2937332, 2938356, 2939380, 2940404, 2941428], by decide +kernel⟩
private def priceBatch95 : P :=
  ⟨unpack [2942452, 2943476, 2944500, 2859512, 2860536, 2861560], by decide +kernel⟩
private def priceBatch96 : P :=
  ⟨unpack [2862584, 2863608, 2864632, 2865656, 2866680, 2933240], by decide +kernel⟩
private def priceBatch97 : P :=
  ⟨unpack [2934264, 2935288, 2936312, 2937336, 2938360, 2939384], by decide +kernel⟩
private def priceBatch98 : P :=
  ⟨unpack [2940408, 2941432, 2942456, 2943480, 2944504, 103454205], by decide +kernel⟩
private def priceBatch99 : P :=
  ⟨unpack [69966333, 2859516, 2860540, 2861564, 2862588, 2863612], by decide +kernel⟩
private def priceBatch100 : P :=
  ⟨unpack [2864636, 2865660, 2866684, 2933244, 2934268, 2935292], by decide +kernel⟩
private def priceBatch101 : P :=
  ⟨unpack [2936316, 2937340, 2938364, 2939388, 2940412, 2941436], by decide +kernel⟩
private def priceBatch102 : P :=
  ⟨unpack [2942460, 2943484, 2944508, 2858497, 2859520, 2860544], by decide +kernel⟩
private def priceBatch103 : P :=
  ⟨unpack [2861568, 2862592, 2863616, 2864640, 2865664, 2932224], by decide +kernel⟩
private def priceBatch104 : P :=
  ⟨unpack [2933248, 2934272, 2935296, 2936320, 2937344, 2938368], by decide +kernel⟩
private def priceBatch105 : P :=
  ⟨unpack [2939392, 2940416, 2941440, 2942464, 2943488, 3010048], by decide +kernel⟩
private def priceBatch106 : P :=
  ⟨unpack [2858500, 2859524, 2860548, 2861572, 2862596, 2863620], by decide +kernel⟩
private def priceBatch107 : P :=
  ⟨unpack [2864644, 2865668, 2932228, 2933252, 2934276, 2935300], by decide +kernel⟩
private def priceBatch108 : P :=
  ⟨unpack [2936324, 2937348, 2938372, 2939396, 2940420, 2941444], by decide +kernel⟩
private def priceBatch109 : P :=
  ⟨unpack [2942468, 2943492, 3010052, 2858504, 2859528, 2860552], by decide +kernel⟩
private def priceBatch110 : P :=
  ⟨unpack [2861576, 2862600, 2863624, 2864648, 2865672, 2932232], by decide +kernel⟩
private def priceBatch111 : P :=
  ⟨unpack [2933256, 2934280, 2935304, 2936328, 2937352, 2938376], by decide +kernel⟩
private def priceBatch112 : P :=
  ⟨unpack [2939400, 2940424, 2941448, 2942472, 2943496, 3010056], by decide +kernel⟩
private def priceBatch113 : P :=
  ⟨unpack [2858508, 2859532, 2860556, 2861580, 2862604, 2863628], by decide +kernel⟩
private def priceBatch114 : P :=
  ⟨unpack [2864652, 2865676, 2932236, 2933260, 2934284, 2935308], by decide +kernel⟩
private def priceBatch115 : P :=
  ⟨unpack [2936332, 2937356, 2938380, 2939404, 2940428, 2941452], by decide +kernel⟩
private def priceBatch116 : P :=
  ⟨unpack [2942476, 2943500, 3010060, 19634705, 2858512, 2859536], by decide +kernel⟩
private def priceBatch117 : P :=
  ⟨unpack [2860560, 2861584, 2862608, 2863632, 2864656, 2865680], by decide +kernel⟩
private def priceBatch118 : P :=
  ⟨unpack [2932240, 2933264, 2934288, 2935312, 2936336, 2937360], by decide +kernel⟩
private def priceBatch119 : P :=
  ⟨unpack [2938384, 2939408, 2940432, 2941456, 2942480, 2943504], by decide +kernel⟩
private def priceBatch120 : P :=
  ⟨unpack [3010064, 2858516, 2859540, 2860564, 2861588, 2862612], by decide +kernel⟩
private def priceBatch121 : P :=
  ⟨unpack [2863636, 2864660, 2931220, 2932244, 2933268, 2934292], by decide +kernel⟩
private def priceBatch122 : P :=
  ⟨unpack [2935316, 2936340, 2937364, 2938388, 2939412, 2940436], by decide +kernel⟩
private def priceBatch123 : P :=
  ⟨unpack [2941460, 2942484, 2943508, 3010068, 21595057689, 120229401], by decide +kernel⟩
private def priceBatch124 : P :=
  ⟨unpack [120295961, 69965337, 2857497, 2858520, 2859544, 2860568], by decide +kernel⟩
private def priceBatch125 : P :=
  ⟨unpack [2861592, 2862616, 2863640, 2864664, 2931224, 2932248], by decide +kernel⟩
private def priceBatch126 : P :=
  ⟨unpack [2933272, 2934296, 2935320, 2936344, 2937368, 2938392], by decide +kernel⟩
private def priceBatch127 : P :=
  ⟨unpack [2939416, 2940440, 2941464, 2942488, 3009048, 3010072], by decide +kernel⟩
private def priceBatch128 : P :=
  ⟨unpack [2857500, 2858524, 2859548, 2860572, 2861596, 2862620], by decide +kernel⟩
private def priceBatch129 : P :=
  ⟨unpack [2863644, 2864668, 2931228, 2932252, 2933276, 2934300], by decide +kernel⟩
private def priceBatch130 : P :=
  ⟨unpack [2935324, 2936348, 2937372, 2938396, 2939420, 2940444], by decide +kernel⟩
private def priceBatch131 : P :=
  ⟨unpack [2941468, 2942492, 3009052, 3010076, 2857504, 2858528], by decide +kernel⟩
private def priceBatch132 : P :=
  ⟨unpack [2859552, 2860576, 2861600, 2862624, 2863648, 2864672], by decide +kernel⟩
private def priceBatch133 : P :=
  ⟨unpack [2931232, 2932256, 2933280, 2934304, 2935328, 2936352], by decide +kernel⟩
private def priceBatch134 : P :=
  ⟨unpack [2937376, 2938400, 2939424, 2940448, 2941472, 2942496], by decide +kernel⟩
private def priceBatch135 : P :=
  ⟨unpack [3009056, 3010080, 2857508, 2858532, 2859556, 2860580], by decide +kernel⟩
private def priceBatch136 : P :=
  ⟨unpack [2861604, 2862628, 2863652, 2930212, 2931236, 2932260], by decide +kernel⟩
private def priceBatch137 : P :=
  ⟨unpack [2933284, 2934308, 2935332, 2936356, 2937380, 2938404], by decide +kernel⟩
private def priceBatch138 : P :=
  ⟨unpack [2939428, 2940452, 2941476, 2942500, 3009060, 227021427365777005154790950], by decide +kernel⟩
private def priceBatch139 : P :=
  ⟨unpack [34412780073, 2857512, 2858536, 2859560, 2860584, 2861608], by decide +kernel⟩
private def priceBatch140 : P :=
  ⟨unpack [2862632, 2863656, 2930216, 2931240, 2932264, 2933288], by decide +kernel⟩
private def priceBatch141 : P :=
  ⟨unpack [2934312, 2935336, 2936360, 2937384, 2938408, 2939432], by decide +kernel⟩
private def priceBatch142 : P :=
  ⟨unpack [2940456, 2941480, 2942504, 3009064, 229006179682740326812741162, 2856493], by decide +kernel⟩
private def priceBatch143 : P :=
  ⟨unpack [2857516, 2858540, 2859564, 2860588, 2861612, 2862636], by decide +kernel⟩
private def priceBatch144 : P :=
  ⟨unpack [2863660, 2930220, 2931244, 2932268, 2933292, 2934316], by decide +kernel⟩
private def priceBatch145 : P :=
  ⟨unpack [2935340, 2936364, 2937388, 2938412, 2939436, 2940460], by decide +kernel⟩
private def priceBatch146 : P :=
  ⟨unpack [2941484, 2942508, 3009068, 230990931999703647396949550, 8609498673, 2856497], by decide +kernel⟩
private def priceBatch147 : P :=
  ⟨unpack [2857520, 2858544, 2859568, 2860592, 2861616, 2862640], by decide +kernel⟩
private def priceBatch148 : P :=
  ⟨unpack [2863664, 2930224, 2931248, 2932272, 2933296, 2934320], by decide +kernel⟩
private def priceBatch149 : P :=
  ⟨unpack [2935344, 2936368, 2937392, 2938416, 2939440, 2940464], by decide +kernel⟩
private def priceBatch150 : P :=
  ⟨unpack [2941488, 3008048, 3009072, 232833718152463847378513458, 2856500, 2857524], by decide +kernel⟩
private def priceBatch151 : P :=
  ⟨unpack [2858548, 2859572, 2860596, 2861620, 2862644, 2929204], by decide +kernel⟩
private def priceBatch152 : P :=
  ⟨unpack [2930228, 2931252, 2932276, 2933300, 2934324, 2935348], by decide +kernel⟩
private def priceBatch153 : P :=
  ⟨unpack [2936372, 2937396, 2938420, 2939444, 2940468, 213337054970526176784474678], by decide +kernel⟩
private def priceBatch154 : P :=
  ⟨unpack [3008052, 226957490148227335754476086, 233864999453276587600768566], by decide +kernel⟩
private def batches : List P := [priceBatch0, priceBatch1, priceBatch2, priceBatch3, priceBatch4, priceBatch5, priceBatch6, priceBatch7, priceBatch8, priceBatch9, priceBatch10, priceBatch11, priceBatch12, priceBatch13, priceBatch14, priceBatch15, priceBatch16, priceBatch17, priceBatch18, priceBatch19, priceBatch20, priceBatch21, priceBatch22, priceBatch23, priceBatch24, priceBatch25, priceBatch26, priceBatch27, priceBatch28, priceBatch29, priceBatch30, priceBatch31, priceBatch32, priceBatch33, priceBatch34, priceBatch35, priceBatch36, priceBatch37, priceBatch38, priceBatch39, priceBatch40, priceBatch41, priceBatch42, priceBatch43, priceBatch44, priceBatch45, priceBatch46, priceBatch47, priceBatch48, priceBatch49, priceBatch50, priceBatch51, priceBatch52, priceBatch53, priceBatch54, priceBatch55, priceBatch56, priceBatch57, priceBatch58, priceBatch59, priceBatch60, priceBatch61, priceBatch62, priceBatch63, priceBatch64, priceBatch65, priceBatch66, priceBatch67, priceBatch68, priceBatch69, priceBatch70, priceBatch71, priceBatch72, priceBatch73, priceBatch74, priceBatch75, priceBatch76, priceBatch77, priceBatch78, priceBatch79, priceBatch80, priceBatch81, priceBatch82, priceBatch83, priceBatch84, priceBatch85, priceBatch86, priceBatch87, priceBatch88, priceBatch89, priceBatch90, priceBatch91, priceBatch92, priceBatch93, priceBatch94, priceBatch95, priceBatch96, priceBatch97, priceBatch98, priceBatch99, priceBatch100, priceBatch101, priceBatch102, priceBatch103, priceBatch104, priceBatch105, priceBatch106, priceBatch107, priceBatch108, priceBatch109, priceBatch110, priceBatch111, priceBatch112, priceBatch113, priceBatch114, priceBatch115, priceBatch116, priceBatch117, priceBatch118, priceBatch119, priceBatch120, priceBatch121, priceBatch122, priceBatch123, priceBatch124, priceBatch125, priceBatch126, priceBatch127, priceBatch128, priceBatch129, priceBatch130, priceBatch131, priceBatch132, priceBatch133, priceBatch134, priceBatch135, priceBatch136, priceBatch137, priceBatch138, priceBatch139, priceBatch140, priceBatch141, priceBatch142, priceBatch143, priceBatch144, priceBatch145, priceBatch146, priceBatch147, priceBatch148, priceBatch149, priceBatch150, priceBatch151, priceBatch152, priceBatch153, priceBatch154]
private theorem i3 : checks (tilesOf batches) 141 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 141 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 141 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 141 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 141 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 141 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 141 51 8 = true := by
  decide +kernel
private theorem i59 : checks (tilesOf batches) 141 59 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤141) (hj : a.j≤59) :
    Covered orders a ∨ Low6960Gate.Gated ((0 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (checks_join i51 (i59)))))))) a ha ht hb hj
end Top1

end Low6960Allocation.Group0
