import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass0

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group0
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def priceBatch0 : P :=
  ⟨unpack [2197883909, 671158281, 4496364553, 4395703309, 21659657229, 69157141525], by decide +kernel⟩
private def priceBatch1 : P :=
  ⟨unpack [83958825, 8791466025, 73654435885, 369169469, 151066685, 22247648317], by decide +kernel⟩
private def priceBatch2 : P :=
  ⟨unpack [335682625, 35117516869, 13909041245, 6174480485, 30922327169, 47800607873], by decide +kernel⟩
private def priceBatch3 : P :=
  ⟨unpack [23220655257, 31659724973, 51827479753, 35620073721, 34513602813, 22265816329], by decide +kernel⟩
private def priceBatch4 : P :=
  ⟨unpack [30470012169, 21779553553, 21678961937, 13021990181, 8693472549, 372042021], by decide +kernel⟩
private def priceBatch5 : P :=
  ⟨unpack [4365016385, 4549567809, 8760505669, 8710242629, 4381723977, 4348171593], by decide +kernel⟩
private def priceBatch6 : P :=
  ⟨unpack [26745394513, 19717461, 8760648021, 19649881, 36493657, 13122575709], by decide +kernel⟩
private def priceBatch7 : P :=
  ⟨unpack [8743726429, 2940253, 53202273, 19648865, 2872673, 2940256], by decide +kernel⟩
private def priceBatch8 : P :=
  ⟨unpack [4364943717, 53201253, 19715429, 2939237, 2940260, 2871657], by decide +kernel⟩
private def priceBatch9 : P :=
  ⟨unpack [2939240, 2940264, 17618730349, 13172838765, 2871660, 2938220], by decide +kernel⟩
private def priceBatch10 : P :=
  ⟨unpack [2939244, 2940268, 4381718897, 2870641, 2871664, 2938224], by decide +kernel⟩
private def priceBatch11 : P :=
  ⟨unpack [2939248, 2940272, 2869621, 2870644, 2871668, 2938228], by decide +kernel⟩
private def priceBatch12 : P :=
  ⟨unpack [2939252, 2940276, 53199225, 19645817, 2869625, 2870648], by decide +kernel⟩
private def priceBatch13 : P :=
  ⟨unpack [2871672, 2938232, 2939256, 2940280, 2869628, 2870652], by decide +kernel⟩
private def priceBatch14 : P :=
  ⟨unpack [2871676, 2938236, 2939260, 2940284, 2868609, 2869632], by decide +kernel⟩
private def priceBatch15 : P :=
  ⟨unpack [2870656, 2937216, 2938240, 2939264, 2940288, 53272961], by decide +kernel⟩
private def priceBatch16 : P :=
  ⟨unpack [19719553, 2943360, 4398427525, 4364940677, 2868612, 2869636], by decide +kernel⟩
private def priceBatch17 : P :=
  ⟨unpack [2870660, 2937220, 2938244, 2939268, 2940292, 2943364], by decide +kernel⟩
private def priceBatch18 : P :=
  ⟨unpack [36421001, 2867593, 2868616, 2869640, 2870664, 2937224], by decide +kernel⟩
private def priceBatch19 : P :=
  ⟨unpack [2938248, 2939272, 2940296, 2942344, 2943368, 2867596], by decide +kernel⟩
private def priceBatch20 : P :=
  ⟨unpack [2868620, 2869644, 2870668, 2937228, 2938252, 2939276], by decide +kernel⟩
private def priceBatch21 : P :=
  ⟨unpack [2940300, 2942348, 2943372, 2867600, 2868624, 2869648], by decide +kernel⟩
private def priceBatch22 : P :=
  ⟨unpack [2870672, 2937232, 2938256, 2939280, 2940304, 2941328], by decide +kernel⟩
private def priceBatch23 : P :=
  ⟨unpack [2942352, 2943376, 2866581, 2867604, 2868628, 2869652], by decide +kernel⟩
private def priceBatch24 : P :=
  ⟨unpack [2870676, 2937236, 2938260, 2939284, 2940308, 2941332], by decide +kernel⟩
private def priceBatch25 : P :=
  ⟨unpack [2942356, 2943380, 4465533337, 4381649305, 69973401, 19642777], by decide +kernel⟩
private def priceBatch26 : P :=
  ⟨unpack [2866584, 2867608, 2868632, 2869656, 2936216, 2937240], by decide +kernel⟩
private def priceBatch27 : P :=
  ⟨unpack [2938264, 2939288, 2940312, 2941336, 2942360, 2943384], by decide +kernel⟩
private def priceBatch28 : P :=
  ⟨unpack [2866588, 2867612, 2868636, 2869660, 2936220, 2937244], by decide +kernel⟩
private def priceBatch29 : P :=
  ⟨unpack [2938268, 2939292, 2940316, 2941340, 2942364, 2943388], by decide +kernel⟩
private def priceBatch30 : P :=
  ⟨unpack [86749601, 2865569, 2866592, 2867616, 2868640, 2869664], by decide +kernel⟩
private def priceBatch31 : P :=
  ⟨unpack [2936224, 2937248, 2938272, 2939296, 2940320, 2941344], by decide +kernel⟩
private def priceBatch32 : P :=
  ⟨unpack [2942368, 2943392, 2865572, 2866596, 2867620, 2868644], by decide +kernel⟩
private def priceBatch33 : P :=
  ⟨unpack [2869668, 2936228, 2937252, 2938276, 2939300, 2940324], by decide +kernel⟩
private def priceBatch34 : P :=
  ⟨unpack [2941348, 2942372, 2943396, 2865576, 2866600, 2867624], by decide +kernel⟩
private def priceBatch35 : P :=
  ⟨unpack [2868648, 2869672, 2936232, 2937256, 2938280, 2939304], by decide +kernel⟩
private def priceBatch36 : P :=
  ⟨unpack [2940328, 2941352, 2942376, 2943400, 2864557, 2865580], by decide +kernel⟩
private def priceBatch37 : P :=
  ⟨unpack [2866604, 2867628, 2868652, 2869676, 2936236, 2937260], by decide +kernel⟩
private def priceBatch38 : P :=
  ⟨unpack [2938284, 2939308, 2940332, 2941356, 2942380, 2943404], by decide +kernel⟩
private def priceBatch39 : P :=
  ⟨unpack [137079217, 86748593, 2864561, 2865584, 2866608, 2867632], by decide +kernel⟩
private def priceBatch40 : P :=
  ⟨unpack [2868656, 2869680, 2936240, 2937264, 2938288, 2939312], by decide +kernel⟩
private def priceBatch41 : P :=
  ⟨unpack [2940336, 2941360, 2942384, 2943408, 8844382645, 4448755125], by decide +kernel⟩
private def priceBatch42 : P :=
  ⟨unpack [2864564, 2865588, 2866612, 2867636, 2868660, 2935220], by decide +kernel⟩
private def priceBatch43 : P :=
  ⟨unpack [2936244, 2937268, 2938292, 2939316, 2940340, 2941364], by decide +kernel⟩
private def priceBatch44 : P :=
  ⟨unpack [2942388, 2943412, 19640761, 2864568, 2865592, 2866616], by decide +kernel⟩
private def priceBatch45 : P :=
  ⟨unpack [2867640, 2868664, 2935224, 2936248, 2937272, 2938296], by decide +kernel⟩
private def priceBatch46 : P :=
  ⟨unpack [2939320, 2940344, 2941368, 2942392, 2943416, 2864572], by decide +kernel⟩
private def priceBatch47 : P :=
  ⟨unpack [2865596, 2866620, 2867644, 2868668, 2935228, 2936252], by decide +kernel⟩
private def priceBatch48 : P :=
  ⟨unpack [2937276, 2938300, 2939324, 2940348, 2941372, 2942396], by decide +kernel⟩
private def priceBatch49 : P :=
  ⟨unpack [2943420, 2863552, 2864576, 2865600, 2866624, 2867648], by decide +kernel⟩
private def priceBatch50 : P :=
  ⟨unpack [2868672, 2935232, 2936256, 2937280, 2938304, 2939328], by decide +kernel⟩
private def priceBatch51 : P :=
  ⟨unpack [2940352, 2941376, 2942400, 2943424, 137078213, 2863556], by decide +kernel⟩
private def priceBatch52 : P :=
  ⟨unpack [2864580, 2865604, 2866628, 2867652, 2868676, 2935236], by decide +kernel⟩
private def priceBatch53 : P :=
  ⟨unpack [2936260, 2937284, 2938308, 2939332, 2940356, 2941380], by decide +kernel⟩
private def priceBatch54 : P :=
  ⟨unpack [2942404, 2943428, 21896982985, 19639753, 2863560, 2864584], by decide +kernel⟩
private def priceBatch55 : P :=
  ⟨unpack [2865608, 2866632, 2867656, 2934216, 2935240, 2936264], by decide +kernel⟩
private def priceBatch56 : P :=
  ⟨unpack [2937288, 2938312, 2939336, 2940360, 2941384, 2942408], by decide +kernel⟩
private def priceBatch57 : P :=
  ⟨unpack [2943432, 2863564, 2864588, 2865612, 2866636, 2867660], by decide +kernel⟩
private def priceBatch58 : P :=
  ⟨unpack [2934220, 2935244, 2936268, 2937292, 2938316, 2939340], by decide +kernel⟩
private def priceBatch59 : P :=
  ⟨unpack [2940364, 2941388, 2942412, 2943436, 2862545, 2863568], by decide +kernel⟩
private def priceBatch60 : P :=
  ⟨unpack [2864592, 2865616, 2866640, 2867664, 2934224, 2935248], by decide +kernel⟩
private def priceBatch61 : P :=
  ⟨unpack [2936272, 2937296, 2938320, 2939344, 2940368, 2941392], by decide +kernel⟩
private def priceBatch62 : P :=
  ⟨unpack [2942416, 2943440, 36415957, 2862548, 2863572, 2864596], by decide +kernel⟩
private def priceBatch63 : P :=
  ⟨unpack [2865620, 2866644, 2867668, 2934228, 2935252, 2936276], by decide +kernel⟩
private def priceBatch64 : P :=
  ⟨unpack [2937300, 2938324, 2939348, 2940372, 2941396, 2942420], by decide +kernel⟩
private def priceBatch65 : P :=
  ⟨unpack [2943444, 8894712281, 2862552, 2863576, 2864600, 2865624], by decide +kernel⟩
private def priceBatch66 : P :=
  ⟨unpack [2866648, 2867672, 2934232, 2935256, 2936280, 2937304], by decide +kernel⟩
private def priceBatch67 : P :=
  ⟨unpack [2938328, 2939352, 2940376, 2941400, 2942424, 2943448], by decide +kernel⟩
private def priceBatch68 : P :=
  ⟨unpack [4398489053, 2862556, 2863580, 2864604, 2865628, 2866652], by decide +kernel⟩
private def priceBatch69 : P :=
  ⟨unpack [2867676, 2934236, 2935260, 2936284, 2937308, 2938332], by decide +kernel⟩
private def priceBatch70 : P :=
  ⟨unpack [2939356, 2940380, 2941404, 2942428, 2943452, 2861537], by decide +kernel⟩
private def priceBatch71 : P :=
  ⟨unpack [2862560, 2863584, 2864608, 2865632, 2866656, 2933216], by decide +kernel⟩
private def priceBatch72 : P :=
  ⟨unpack [2934240, 2935264, 2936288, 2937312, 2938336, 2939360], by decide +kernel⟩
private def priceBatch73 : P :=
  ⟨unpack [2940384, 2941408, 2942432, 2943456, 2861540, 2862564], by decide +kernel⟩
private def priceBatch74 : P :=
  ⟨unpack [2863588, 2864612, 2865636, 2866660, 2933220, 2934244], by decide +kernel⟩
private def priceBatch75 : P :=
  ⟨unpack [2935268, 2936292, 2937316, 2938340, 2939364, 2940388], by decide +kernel⟩
private def priceBatch76 : P :=
  ⟨unpack [2941412, 2942436, 2943460, 36414953, 2861544, 2862568], by decide +kernel⟩
private def priceBatch77 : P :=
  ⟨unpack [2863592, 2864616, 2865640, 2866664, 2933224, 2934248], by decide +kernel⟩
private def priceBatch78 : P :=
  ⟨unpack [2935272, 2936296, 2937320, 2938344, 2939368, 2940392], by decide +kernel⟩
private def priceBatch79 : P :=
  ⟨unpack [2941416, 2942440, 2943464, 2861548, 2862572, 2863596], by decide +kernel⟩
private def priceBatch80 : P :=
  ⟨unpack [2864620, 2865644, 2866668, 2933228, 2934252, 2935276], by decide +kernel⟩
private def priceBatch81 : P :=
  ⟨unpack [2936300, 2937324, 2938348, 2939372, 2940396, 2941420], by decide +kernel⟩
private def priceBatch82 : P :=
  ⟨unpack [2942444, 2943468, 2861552, 2862576, 2863600, 2864624], by decide +kernel⟩
private def priceBatch83 : P :=
  ⟨unpack [2865648, 2866672, 2933232, 2934256, 2935280, 2936304], by decide +kernel⟩
private def priceBatch84 : P :=
  ⟨unpack [2937328, 2938352, 2939376, 2940400, 2941424, 2942448], by decide +kernel⟩
private def priceBatch85 : P :=
  ⟨unpack [2943472, 4415198709, 2860533, 2861556, 2862580, 2863604], by decide +kernel⟩
private def priceBatch86 : P :=
  ⟨unpack [2864628, 2865652, 2932212, 2933236, 2934260, 2935284], by decide +kernel⟩
private def priceBatch87 : P :=
  ⟨unpack [2936308, 2937332, 2938356, 2939380, 2940404, 2941428], by decide +kernel⟩
private def priceBatch88 : P :=
  ⟨unpack [2942452, 2943476, 120299001, 53191161, 2860537, 2861560], by decide +kernel⟩
private def priceBatch89 : P :=
  ⟨unpack [2862584, 2863608, 2864632, 2865656, 2932216, 2933240], by decide +kernel⟩
private def priceBatch90 : P :=
  ⟨unpack [2934264, 2935288, 2936312, 2937336, 2938360, 2939384], by decide +kernel⟩
private def priceBatch91 : P :=
  ⟨unpack [2940408, 2941432, 2942456, 2943480, 2860540, 2861564], by decide +kernel⟩
private def priceBatch92 : P :=
  ⟨unpack [2862588, 2863612, 2864636, 2865660, 2932220, 2933244], by decide +kernel⟩
private def priceBatch93 : P :=
  ⟨unpack [2934268, 2935292, 2936316, 2937340, 2938364, 2939388], by decide +kernel⟩
private def priceBatch94 : P :=
  ⟨unpack [2940412, 2941436, 2942460, 2943484, 2860544, 2861568], by decide +kernel⟩
private def priceBatch95 : P :=
  ⟨unpack [2862592, 2863616, 2864640, 2865664, 2932224, 2933248], by decide +kernel⟩
private def priceBatch96 : P :=
  ⟨unpack [2934272, 2935296, 2936320, 2937344, 2938368, 2939392], by decide +kernel⟩
private def priceBatch97 : P :=
  ⟨unpack [2940416, 2941440, 2942464, 2943488, 2860548, 2861572], by decide +kernel⟩
private def priceBatch98 : P :=
  ⟨unpack [2862596, 2863620, 2864644, 2865668, 2932228, 2933252], by decide +kernel⟩
private def priceBatch99 : P :=
  ⟨unpack [2934276, 2935300, 2936324, 2937348, 2938372, 2939396], by decide +kernel⟩
private def priceBatch100 : P :=
  ⟨unpack [2940420, 2941444, 2942468, 2943492, 19636745, 2860552], by decide +kernel⟩
private def priceBatch101 : P :=
  ⟨unpack [2861576, 2862600, 2863624, 2864648, 2931208, 2932232], by decide +kernel⟩
private def priceBatch102 : P :=
  ⟨unpack [2933256, 2934280, 2935304, 2936328, 2937352, 2938376], by decide +kernel⟩
private def priceBatch103 : P :=
  ⟨unpack [2939400, 2940424, 2941448, 2942472, 3009032, 2860556], by decide +kernel⟩
private def priceBatch104 : P :=
  ⟨unpack [2861580, 2862604, 2863628, 2864652, 2931212, 2932236], by decide +kernel⟩
private def priceBatch105 : P :=
  ⟨unpack [2933260, 2934284, 2935308, 2936332, 2937356, 2938380], by decide +kernel⟩
private def priceBatch106 : P :=
  ⟨unpack [2939404, 2940428, 2941452, 2942476, 3009036, 2859537], by decide +kernel⟩
private def priceBatch107 : P :=
  ⟨unpack [2860560, 2861584, 2862608, 2863632, 2864656, 2931216], by decide +kernel⟩
private def priceBatch108 : P :=
  ⟨unpack [2932240, 2933264, 2934288, 2935312, 2936336, 2937360], by decide +kernel⟩
private def priceBatch109 : P :=
  ⟨unpack [2938384, 2939408, 2940432, 2941456, 2942480, 3009040], by decide +kernel⟩
private def priceBatch110 : P :=
  ⟨unpack [86052834837, 4398487061, 2859540, 2860564, 2861588, 2862612], by decide +kernel⟩
private def priceBatch111 : P :=
  ⟨unpack [2863636, 2864660, 2931220, 2932244, 2933268, 2934292], by decide +kernel⟩
private def priceBatch112 : P :=
  ⟨unpack [2935316, 2936340, 2937364, 2938388, 2939412, 2940436], by decide +kernel⟩
private def priceBatch113 : P :=
  ⟨unpack [2941460, 2942484, 3009044, 53190169, 2859544, 2860568], by decide +kernel⟩
private def priceBatch114 : P :=
  ⟨unpack [2861592, 2862616, 2863640, 2930200, 2931224, 2932248], by decide +kernel⟩
private def priceBatch115 : P :=
  ⟨unpack [2933272, 2934296, 2935320, 2936344, 2937368, 2938392], by decide +kernel⟩
private def priceBatch116 : P :=
  ⟨unpack [2939416, 2940440, 2941464, 2942488, 3009048, 2859548], by decide +kernel⟩
private def priceBatch117 : P :=
  ⟨unpack [2860572, 2861596, 2862620, 2863644, 2930204, 2931228], by decide +kernel⟩
private def priceBatch118 : P :=
  ⟨unpack [2932252, 2933276, 2934300, 2935324, 2936348, 2937372], by decide +kernel⟩
private def priceBatch119 : P :=
  ⟨unpack [2938396, 2939420, 2940444, 2941468, 2942492, 3009052], by decide +kernel⟩
private def priceBatch120 : P :=
  ⟨unpack [2859552, 2860576, 2861600, 2862624, 2863648, 2930208], by decide +kernel⟩
private def priceBatch121 : P :=
  ⟨unpack [2931232, 2932256, 2933280, 2934304, 2935328, 2936352], by decide +kernel⟩
private def priceBatch122 : P :=
  ⟨unpack [2937376, 2938400, 2939424, 2940448, 2941472, 3008032], by decide +kernel⟩
private def priceBatch123 : P :=
  ⟨unpack [3009056, 12971641381, 2859556, 2860580, 2861604, 2862628], by decide +kernel⟩
private def priceBatch124 : P :=
  ⟨unpack [2863652, 2930212, 2931236, 2932260, 2933284, 2934308], by decide +kernel⟩
private def priceBatch125 : P :=
  ⟨unpack [2935332, 2936356, 2937380, 2938404, 2939428, 2940452], by decide +kernel⟩
private def priceBatch126 : P :=
  ⟨unpack [2941476, 3008036, 3009060, 19635753, 2859560, 2860584], by decide +kernel⟩
private def priceBatch127 : P :=
  ⟨unpack [2861608, 2862632, 2863656, 2930216, 2931240, 2932264], by decide +kernel⟩
private def priceBatch128 : P :=
  ⟨unpack [2933288, 2934312, 2935336, 2936360, 2937384, 2938408], by decide +kernel⟩
private def priceBatch129 : P :=
  ⟨unpack [2939432, 2940456, 2941480, 3008040, 3009064, 2859564], by decide +kernel⟩
private def priceBatch130 : P :=
  ⟨unpack [2860588, 2861612, 2862636, 2929196, 2930220, 2931244], by decide +kernel⟩
private def priceBatch131 : P :=
  ⟨unpack [2932268, 2933292, 2934316, 2935340, 2936364, 2937388], by decide +kernel⟩
private def priceBatch132 : P :=
  ⟨unpack [2938412, 2939436, 2940460, 2941484, 3008044, 3009068], by decide +kernel⟩
private def priceBatch133 : P :=
  ⟨unpack [30101107249, 36411953, 2858544, 2859568, 2860592, 2861616], by decide +kernel⟩
private def priceBatch134 : P :=
  ⟨unpack [2862640, 2929200, 2930224, 2931248, 2932272, 2933296], by decide +kernel⟩
private def priceBatch135 : P :=
  ⟨unpack [2934320, 2935344, 2936368, 2937392, 2938416, 2939440], by decide +kernel⟩
private def priceBatch136 : P :=
  ⟨unpack [2940464, 2941488, 3008048, 3009072, 2858548, 2859572], by decide +kernel⟩
private def priceBatch137 : P :=
  ⟨unpack [2860596, 2861620, 2862644, 2929204, 2930228, 2931252], by decide +kernel⟩
private def priceBatch138 : P :=
  ⟨unpack [2932276, 2933300, 2934324, 2935348, 2936372, 2937396], by decide +kernel⟩
private def priceBatch139 : P :=
  ⟨unpack [2938420, 2939444, 2940468, 3007028, 3008052, 223506888296496781981510198], by decide +kernel⟩
private def priceBatch140 : P :=
  ⟨unpack [2858552, 2859576, 2860600, 2861624, 2862648, 2929208], by decide +kernel⟩
private def priceBatch141 : P :=
  ⟨unpack [2930232, 2931256, 2932280, 2933304, 2934328, 2935352], by decide +kernel⟩
private def priceBatch142 : P :=
  ⟨unpack [2936376, 2937400, 2938424, 2939448, 2940472, 3007032], by decide +kernel⟩
private def priceBatch143 : P :=
  ⟨unpack [3008056, 224548234799561770074499642], by decide +kernel⟩
private def batches : List P := [priceBatch0, priceBatch1, priceBatch2, priceBatch3, priceBatch4, priceBatch5, priceBatch6, priceBatch7, priceBatch8, priceBatch9, priceBatch10, priceBatch11, priceBatch12, priceBatch13, priceBatch14, priceBatch15, priceBatch16, priceBatch17, priceBatch18, priceBatch19, priceBatch20, priceBatch21, priceBatch22, priceBatch23, priceBatch24, priceBatch25, priceBatch26, priceBatch27, priceBatch28, priceBatch29, priceBatch30, priceBatch31, priceBatch32, priceBatch33, priceBatch34, priceBatch35, priceBatch36, priceBatch37, priceBatch38, priceBatch39, priceBatch40, priceBatch41, priceBatch42, priceBatch43, priceBatch44, priceBatch45, priceBatch46, priceBatch47, priceBatch48, priceBatch49, priceBatch50, priceBatch51, priceBatch52, priceBatch53, priceBatch54, priceBatch55, priceBatch56, priceBatch57, priceBatch58, priceBatch59, priceBatch60, priceBatch61, priceBatch62, priceBatch63, priceBatch64, priceBatch65, priceBatch66, priceBatch67, priceBatch68, priceBatch69, priceBatch70, priceBatch71, priceBatch72, priceBatch73, priceBatch74, priceBatch75, priceBatch76, priceBatch77, priceBatch78, priceBatch79, priceBatch80, priceBatch81, priceBatch82, priceBatch83, priceBatch84, priceBatch85, priceBatch86, priceBatch87, priceBatch88, priceBatch89, priceBatch90, priceBatch91, priceBatch92, priceBatch93, priceBatch94, priceBatch95, priceBatch96, priceBatch97, priceBatch98, priceBatch99, priceBatch100, priceBatch101, priceBatch102, priceBatch103, priceBatch104, priceBatch105, priceBatch106, priceBatch107, priceBatch108, priceBatch109, priceBatch110, priceBatch111, priceBatch112, priceBatch113, priceBatch114, priceBatch115, priceBatch116, priceBatch117, priceBatch118, priceBatch119, priceBatch120, priceBatch121, priceBatch122, priceBatch123, priceBatch124, priceBatch125, priceBatch126, priceBatch127, priceBatch128, priceBatch129, priceBatch130, priceBatch131, priceBatch132, priceBatch133, priceBatch134, priceBatch135, priceBatch136, priceBatch137, priceBatch138, priceBatch139, priceBatch140, priceBatch141, priceBatch142, priceBatch143]
private theorem i3 : checks (tilesOf batches) 142 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 142 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 142 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 142 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 142 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 142 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 142 51 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤142) (hj : a.j≤58) :
    Covered orders a ∨ Low6966Gate.Gated ((0 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

end Low6966Allocation.Group0
