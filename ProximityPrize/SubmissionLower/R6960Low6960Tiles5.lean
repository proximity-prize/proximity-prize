import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass5

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group5
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2264992773, 973148169, 536941577, 6543710217, 2232033293, 2030707727], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1762273297, 1577724945, 1426731025, 1292514325, 1191852053, 1107966997], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1024081945, 956974105, 906643481, 839535645, 789205021, 755651613], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [15034964001, 6428256293, 6411481129, 2116515881, 2032630829, 1982300205], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1915192365, 1848084529, 1797753905, 1764200497, 1697092661, 1663539253], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1629985845, 1579655225, 1546101817, 1512548409, 1462217789, 1445441597], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1411888189, 1378334785, 1361558593, 1328005185, 1294451781, 1277675589], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1260899397, 1227345993, 1210569801, 1193793609, 1160240205, 1160241229], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [14580520077, 18574955733, 18541400285, 18491067625, 14144311541, 22735702261], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [22685369601, 22618259729, 26846117153, 26762164533, 890451277, 1100303621479], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100303622503, 5067977065, 1100286974315, 1100270196079, 1100253417843, 1100236639607], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100219861371, 1100203083135, 1100186304899, 1100152749451, 4916981133, 1100136036751], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1100119192979, 1100085637531, 557231517, 523676069, 490120621, 4751532469], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [9027398073, 4717977021, 4684356037, 8945767885, 8895435225, 13156847073], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [13106514413, 8775738869, 17351149049, 17284039177, 17233706517], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i3 : checks (tilesOf batches) 136 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 136 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 136 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 136 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 136 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 136 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 136 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [6543710217, 2232033293, 2030707725, 1762273297, 1577724945, 1409953809], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1275737109, 1158297621, 1074412565, 973750297, 923419673, 856311833], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [789203997, 755650589, 705319965, 15034964001, 6428256293, 2116513833], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [2116514857, 2066184233, 1982299181, 1931968557, 1864860717, 1797752881], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1747422257, 1697091633, 1646761013, 1596430389, 1562876981, 1512546361], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1478992953, 1445439545, 1411886141, 1378332733, 1344779325, 1311225921], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1294449729, 1260896321, 1227342917, 1210566725, 1193790533, 1160237129], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1143460937, 1126684745, 1093131341, 1076355149, 14330320073, 18574954709], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [18541399261, 18491066601, 22718924025, 22668591365, 22584704281, 22500751661], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [907228489, 1100169404755, 1100169403735, 1100186179931, 1100202956127, 1100219732323], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [5084754277, 1100219731303, 1100286970219, 1100270191983, 1100253413747, 1100219858299], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100203080063, 1100186301827, 1100152746379, 4916981133, 1100119190931, 1100102412695], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [557229469, 523674021, 4785085869, 456432053, 9027398073, 4701132225], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [8962544073, 8912211413, 13156846049, 13106513389, 1099649573363, 8775738869], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099649572343, 13039403517, 1099649571327, 1099632793095, 17284038153, 1099599172111], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [1099582393875, 57876, 17216928281, 16834072, 16834076, 33610272], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i6 : checks (tilesOf batches) 136 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 136 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 136 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 136 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 136 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 136 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 136 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [2047484941, 1779050513, 1577724945, 1426731025, 1275737109, 1158297621], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1074412565, 973750297, 906642457, 839534617, 772426781, 722096157], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [671765533, 15034964001, 6428256293, 2116513833, 2116514857, 2032629801], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1948744749, 1898414125, 1831306285, 1764198449, 1713867825, 1663537201], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1596429365, 1562875957, 1512545333, 1462214713, 1428661305, 1395107897], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1344777277, 1328001085, 1294447677, 1260894273, 1227340865, 1210564673], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1177011269, 1143457861, 1126681669, 1093128265, 1076352073, 1059575881], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1026022477, 1026023501, 14363874497, 18608509133, 18558176473, 18507843813], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [22735701237, 22668591365, 22584704281, 22500751661, 1100169403719, 1100152627527], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [907228489, 1100186179915, 1100202956111, 1100219732307, 1100236508503, 1100253284699], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100253283683, 1100270059879, 5067977065, 1100286967147, 1100253411699, 1100236633463], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100203078015, 1100186299779, 1100152744331, 4916981133, 1100119188883, 574005657], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [540450209, 489986477, 4751398325, 9010620861, 4701131201, 8945765837], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [8895433177, 1099649573347, 13140067813, 1099666349543, 1099649571311, 13072957941], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099615950327, 8758961657, 1099615949311, 17317592577, 1099615948295, 57860], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [57864, 1099599170063, 16834060, 17250482705, 1099532129811, 33610256], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [1099565614615, 33610260, 1099532128795, 50386456, 1099532059167, 50386460], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [83938848], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17]
private theorem i9 : checks (tilesOf batches) 136 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 136 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 136 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 136 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 136 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 136 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1443508241, 1292514325, 1175074837, 1074412565, 973750297, 906642457], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [839534617, 755649565, 705318941, 671765533, 15034964001, 6428256293], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2116513833, 2099737641, 2015852585, 1931967533, 1864859693, 1814529069], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1730644017, 1680313393, 1629982769, 1562874933, 1529321525, 1478990901], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1428660281, 1395106873, 1361553465, 1311222845, 1277669437, 1260893245], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1210562625, 1177009217, 1160233025, 1126679621, 1093126213, 1076350021], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1042796617, 1026020425, 1009244233, 975690829, 958914637, 14363874497], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [18625286345, 18574953685, 18507843813, 22735701237, 22668591365, 22584704281], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [22483974449, 1100152627511, 1100169403707, 1100186179903, 1100202956099, 1100219732295], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100236508491, 890451277, 1100253284687, 1100253283671, 1100270059867, 1100303613279], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100303612263, 5051199853, 1100270187887, 1100253409651, 1100219854203, 1100186298755], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100152743307, 607560081, 574004633, 523540901, 489985453, 4734685625], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [8979320261, 8928987601, 1099649573331, 1099649572315, 8861877729, 1099649571299], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099615950315, 13106512365, 1099615949299, 57844, 1099615948283, 57848], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [13039402493, 16834044, 1099615947267, 16834048, 1099532129799, 33610244], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [1099615946251, 33610248, 17267259917, 67162636, 1099582390803, 3723792], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [50386448, 83938836, 83938840, 1099532058143, 100715036, 17183372833], by decide +kernel⟩
private def p17 : P :=
  ⟨unpack [100715040], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17]
private theorem i12 : checks (tilesOf batches) 136 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 136 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 136 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 136 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 136 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 136 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1091189781, 990527513, 906642457, 839534617, 772426781, 705318941], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [671765533, 15034964001, 6428256293, 2116513833, 2099737641, 2015852585], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1931967533, 1864859693, 1797751853, 1713866801, 1663536177, 1613205553], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1546097717, 1495767093, 1462213685, 1395105849, 1361552441, 1327999033], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1277668413, 1244115005, 1210561597, 1177008193, 1143454785, 1126678593], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1076347973, 1059571781, 1042795589, 1009242185, 975688777, 958912585], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [925359181, 908582989, 14363874497, 18625286345, 18558176473, 18507843813], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [22735701237, 22651814153, 22567927069, 1100169404715, 1100169403695, 1100186179891], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100202956087, 1100202955071, 1100219731267, 1100236507463, 1100270060875, 1100270059859], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100303613271, 1100320389471, 1100320388451, 1100286964075, 1100253408627, 1100219853179], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100186297731, 1100152742283, 590781845, 557095325, 506762665, 4751397301], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [4701130177, 1099649573323, 8945764813, 1099666349519, 1099615951319, 8878654941], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099615950303, 1099615949287, 13106512365, 1099632725487, 57836, 1099548908019], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [57840, 1099632724471, 16834036, 1099548907003, 16834040, 13039402493], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [33610236, 1099632723459, 53760, 33610240, 67162628, 1099615945227], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [67162632, 17267259917, 83938828, 83938832, 1099565612567, 100715028], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [100715032, 100715036, 17183372833, 3652128, 117491232], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
private theorem i15 : checks (tilesOf batches) 136 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 136 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 136 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 136 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 136 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 136 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [856311833, 772426781, 722096157, 671765533, 15034964001, 6428256293], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2116513833, 2099737641, 2015852585, 1931967533, 1848082477, 1780974637], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1713866801, 1646758961, 1596428337, 1529320501, 1478989877, 1445436469], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1378328633, 1344775225, 1311221817, 1260891197, 1227337789, 1193784381], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1143453761, 1109900353, 1093124161, 1042793541, 1026017349, 1009241157], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [958910537, 942134345, 925358153, 891804749, 875028557, 14363874497], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [18608509133, 18558176473, 18491066601, 1100152627491, 1100169403687, 1100186179883], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100202956079, 1100219732275, 1100219731259, 1100236507455, 1100270060867, 1100270059851], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100303613263, 1100320389463, 1100337165663, 1100303610215, 1100270185839, 1100236630391], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100203074943, 1100169519495, 607559057, 573872537, 523539877, 4768174513], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [4717907389, 1099649573311, 1099615952327, 8945764813, 1099615951311, 1099615950295], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [8895432153, 1099615949279, 1099532131811, 57824, 1099632725479, 57828], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [13123289577, 1099532130795, 16834024, 1099632724463, 16834028, 50386416], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [50386420, 1099632723451, 53752, 3724792, 33610232, 13039402493], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [67162620, 1099632722435, 67162624, 83938820, 83938824, 17267259917], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [1099599166991, 100715020, 100715024, 100715028, 1099548834331, 117491224], by decide +kernel⟩
private def p16 : P :=
  ⟨unpack [117491228, 17183372833, 134267424], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16]
private theorem i18 : checks (tilesOf batches) 136 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 136 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 136 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 136 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 136 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [671765533, 15034964001, 6428256293, 2116513833, 2116514857, 2032629801], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1931967533, 1864859693, 1797751853, 1713866801, 1646758961, 1596428337], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1529320501, 1478989877, 1428659253, 1378328633, 1327998009, 1294444601], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1244113981, 1210560573, 1177007165, 1126676545, 1093123137, 1076346945], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1026016325, 1009240133, 975686725, 942133321, 925357129, 891803721], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [858250317, 841474125, 14363874497, 1100152627483, 1100169403679, 1100186179875], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100186178859, 1100202955055, 1100236508467, 1100236507451, 1100253283647, 1100270059847], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100303613259, 1100320389459, 1100337165659, 1100320387427, 1100286963051, 1100253407603], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100219852155, 1100169519495, 624336269, 573872537, 523539877, 4768174513], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099649573303, 4717907389, 1099615952319, 1099615951303, 8945764813, 1099615950287], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099632726487, 1099532131803, 57816, 8878654941, 57820, 1099615948259], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099548908003, 16834016, 16834020, 1099632724459, 54760, 16834024], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [13106512365, 50386412, 1099632723443, 50386416, 67162612, 67162616], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [13039402493, 1099632722431, 83938812, 83938816, 83938820, 1099615944203], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [100715016, 100715020, 17250482705, 117491216, 1099565611543, 117491220], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [117491224, 134267420, 3651104, 134267424], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i21 : checks (tilesOf batches) 136 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 136 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 136 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 136 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 136 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [10739998753, 6428257317, 2116514857, 2032629801, 1948744749, 1864859693], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1797751853, 1713866801, 1663536177, 1596428337, 1529320501, 1478989877], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1428659253, 1361551417, 1327998009, 1277667385, 1227336765, 1193783357], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1160229949, 1109899329, 1076345921, 1059569729, 1009239109, 975685701], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [958909509, 908578889, 891802697, 875026505, 841473101, 824696909], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100152627479, 1100169403675, 1100186179871, 1100202956067, 1100219732263, 1100219731247], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100253284659, 1100253283643, 1100270059843, 1100303613255, 1100320389455, 1100337165655], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100337164639, 1100303609191, 1100270184815, 1100219852155, 1100186296707, 624336269], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [573872537, 523539877, 4768174513, 1099649573299, 1099615952315, 4701130177], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099615951299, 1099615950283, 8945764813, 1099632726483, 1099532131799, 57812], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099632725467, 57816, 8878654941, 33610204, 3725792, 16834016], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099632724455, 50386404, 50386408, 13106512365, 1099632723439, 50386412], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [67162608, 67162612, 1099632722427, 83938808, 83938812, 13022625281], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [83938816, 1099632721415, 100715012, 100715016, 117491212, 17250482705], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099582388755, 117491216, 117491220, 134267416, 1099532056095, 134267420], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [134267424], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i24 : checks (tilesOf batches) 136 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 136 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 136 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 136 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 136 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [6428257317, 2116514857, 2049407017, 1948744749, 1881636909, 1814529069], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1730644017, 1663536177, 1596428337, 1529320501, 1478989877, 1428659253], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1361551417, 1327998009, 1277667385, 1227336765, 1193783357, 1160229949], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1109899329, 1076345921, 1042792513, 992461893, 975685701, 942132293], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [891801673, 875025481, 858249289, 807918669, 791142477, 1099665236239], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100169403667, 1100186179867, 1100202956063, 1100219732259, 1100236508459, 1100236507443], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100270060855, 1099984855351, 1100286837055, 1100303613255, 1100320389455, 1100337165655], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100337164639, 1100303609191, 1100270184815, 1100219852155, 1100186296707, 624336269], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [573872537, 523539877, 1099615953323, 4768174513, 1099632729523, 1099615951295], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [4701130177, 1099615950279, 1099548910023, 1099632726479, 8928987601, 1099532131795], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [57808, 57812, 1099615948251, 33610200, 33610204, 8861877729], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099632724451, 50386400, 50386404, 50386408, 1099632723439, 67162604], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [13089735153, 67162608, 83938804, 1099632722427, 83938808, 83938812], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [13022625281, 100715008, 1099632721415, 100715012, 100715016, 117491212], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099582388755, 117491216, 17233705493, 117491220, 134267416, 1099532056095], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [134267420, 134267424], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i27 : checks (tilesOf batches) 136 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 136 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 136 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 136 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [2066184233, 1965521965, 1898414125, 1814529069, 1730644017, 1680313393], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1613205553, 1546097717, 1478989877, 1428659253, 1378328633, 1327998009], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1277667385, 1227336765, 1193783357, 1143452733, 1093122113, 1059568705], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1026015297, 992461893, 958908485, 925355077, 891801673, 858248265], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [841472073, 807918669, 774365261, 1099665236235, 1100169403667, 1100186179863], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100202956059, 1100202955043, 1100236508455, 1100253284655, 1100001632563, 1100253283639], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100286837051, 1100303613251, 1100337166667, 1100353942867, 1100337164639, 1100303609191], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100270184815, 1100219852155, 1100169519495, 624336269, 573872537, 506762665], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099615953323, 1099615952307, 4751397301, 1099615951291, 1099632727491, 8979320261], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099532132807, 1099632726475, 1099532131791, 57804, 8928987601, 57808], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099632725463, 33610196, 33610200, 33610204, 13156845025, 1099632724451], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [50386400, 50386404, 1099649500651, 67162600, 67162604, 67162608], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [13072957941, 1099649499639, 83938804, 83938808, 83938812, 1099649498627], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [100715008, 13005848069, 100715012, 100715016, 117491212, 1099582388755], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [117491216, 117491220, 17216928281, 134267416, 1099532056095, 134267420], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [134267424], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i30 : checks (tilesOf batches) 136 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 136 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 136 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 136 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1831306285, 1747421233, 1680313393, 1629982769, 1546097717, 1495767093], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1445436469, 1378328633, 1327998009, 1294444601, 1227336765, 1193783357], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1143452733, 1093122113, 1059568705, 1026015297, 975684677, 958908485], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [925355077, 875024457, 858248265, 824694857, 791141453, 774365261], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099648459019, 1099665235215, 1100186179859, 1100202956059, 1100219732255, 1100236508455], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100236507439, 1100001632559, 1100270060851, 1100001631543, 1100286837051, 1100303613251], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100337166667, 1100353942867, 1100337164639, 1100303609191, 1100253407603, 1100219852155], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100169519495, 607559057, 557095325, 1099615953319, 506762665, 1099615952303], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099632728503, 4734685625, 1099615950275, 1099532132803, 8979320261, 1099632726475], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099548909003, 57800, 57804, 57808, 8912210389, 1099632725463], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [33610196, 33610200, 1099632724447, 50386396, 50386400, 13140067813], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [50386404, 1099632723435, 67162600, 67162604, 67162608, 1099649499639], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [83938804, 83938808, 100715004, 1099649498627, 100715008, 100715012], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [117491208, 117491212, 1099582388755, 117491216, 117491220, 134267416], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099532056095, 134267420, 134267424], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i33 : checks (tilesOf batches) 136 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 136 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 136 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1629982769, 1562874933, 1495767093, 1445436469, 1378328633, 1344775225], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1294444601, 1227336765, 1193783357, 1160229949, 1093122113, 1059568705], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1026015297, 975684677, 958908485, 925355077, 875024457, 858248265], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [824694857, 791141453, 757588045, 1099665236231, 1099648457999, 1100186179859], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100186178843, 1100219732255, 1100236508455, 1100236507439, 1099984855343, 1100270060851], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100018408755, 1100286837051, 1100320390467, 1100337166667, 1100353942871, 1100337164639], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100303609191, 1100253407603, 1100203074943, 657891717, 607559057, 557095325], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099632730531, 489985453, 1099615952303, 1099615951287, 4734685625, 1099632727487], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099532132803, 1099632726475, 1099532131787, 57800, 57804, 33610192], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099632725463, 33610196, 33610200, 1099632724447, 50386396, 50386400], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [50386404, 1099649500651, 67162600, 67162604, 67162608, 1099649499639], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [83938804, 83938808, 100715004, 100715008, 1099632721415, 100715012], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [100715016, 117491212, 1099582388755, 117491216, 117491220, 134267416], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [134267420, 3651104, 134267424], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i36 : checks (tilesOf batches) 136 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 136 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 136 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1462213685, 1395105849, 1344775225, 1294444601, 1244113981, 1193783357], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1160229949, 1109899329, 1059568705, 1026015297, 975684677, 958908485], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [925355077, 875024457, 841471049, 824694857, 774364237, 757588045], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099648459015, 1099665235211, 1100186179859, 1100202956055, 1100219732255, 1100236508455], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100001632555, 1100253284655, 1100286838067, 1100018408755, 1100303614267, 1100320390467], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100320389455, 1100353942871, 1100337164639, 1100286963051, 1100253407603, 641115517], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [641114505, 590781845, 1099615953315, 1099615952303, 1099615951287, 1099632727487], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099548910015, 1099632726475, 1099532131787, 57800, 57804, 33610192], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099632725463, 33610196, 33610200, 50386396, 1099632724451, 50386400], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [50386404, 67162600, 1099632723439, 67162604, 67162608, 83938804], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099632722427, 83938808, 83938812, 100715008, 1099632721415, 100715012], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [100715016, 117491212, 1099582388755, 117491216, 117491220, 20424217], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [134267416, 134267420, 42528, 3651104, 134267424], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i39 : checks (tilesOf batches) 136 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 136 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 136 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤136) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 5 where
  orders := orders
  covers := by
    intro a ha box
    change 5+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
    have pos := ha.1
    have cases : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 ∨ a.t=13 := by omega
    rcases cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
    · exact Top1.exact a ha h1 (by omega) (by omega)
    · exact Top2.exact a ha h2 (by omega) (by omega)
    · exact Top3.exact a ha h3 (by omega) (by omega)
    · exact Top4.exact a ha h4 (by omega) (by omega)
    · exact Top5.exact a ha h5 (by omega) (by omega)
    · exact Top6.exact a ha h6 (by omega) (by omega)
    · exact Top7.exact a ha h7 (by omega) (by omega)
    · exact Top8.exact a ha h8 (by omega) (by omega)
    · exact Top9.exact a ha h9 (by omega) (by omega)
    · exact Top10.exact a ha h10 (by omega) (by omega)
    · exact Top11.exact a ha h11 (by omega) (by omega)
    · exact Top12.exact a ha h12 (by omega) (by omega)
    · exact Top13.exact a ha h13 (by omega) (by omega)
end Low6960Allocation.Group5
