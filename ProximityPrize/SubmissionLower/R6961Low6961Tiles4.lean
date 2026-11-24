import ProximityPrize.SubmissionLower.R6961Low6961AllocTiles
import ProximityPrize.SubmissionLower.R6961Low6961Mass4

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6961Allocation.Group4
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [1375865863, 1359089675, 23624029195, 44815166481, 1228757027, 1228758051], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1228824611, 1212048423, 1212114983, 1212116007, 1195339819, 1195406379], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1195407403, 1178631215, 1178697775, 2000782383, 1984006195, 1984072755], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1984073779, 1967297591, 1967298615, 1967365175, 1950588987, 1950590011], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1128507451, 31814036541, 43759196489, 34968217929, 35135229265, 47483728337], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [21663951325, 8762278369], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i3 : checks (tilesOf batches) 130 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 130 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 130 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [2132809739, 2116033551, 2116034575, 2116822031, 2100045843, 2100374547], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2100506643, 1781871639, 1781872663, 1782004759, 1765228571, 1765229595], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1765427227, 1748651039, 1748652063, 1748784159, 1732073507, 1732074531], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1732141091, 87061062693, 18996312129, 39514629437, 1100371692863, 1100371693887], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100371694911, 1100371695935, 1100371762495, 1100371763519, 1100371764543, 1100371765567], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100254326079, 26445394237, 47550838209, 17335431649, 17285098993, 4383426037], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [42953808393, 8594506249], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i6 : checks (tilesOf batches) 130 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 130 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 130 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [36443005965, 1245333531, 1228557343, 1228558367, 1228690463, 1211979811], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1211980835, 1212047395, 1195271207, 1195337767, 1195338791, 1178562603], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1178629163, 1178630187, 1161853999, 1161920559, 1161921583, 1145145395], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1145211955, 1145212979, 1128436791, 1363318839, 1363385399, 1346609211], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1346610235, 1346611259, 1329835071, 1329836095, 1329902655, 1313126467], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1313127491, 1313128515, 1296352327, 1296353351, 43775904069, 35186177349], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [26294393213, 21898835325, 13023688165, 4450534885, 21529663997, 12939801085], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [47282398721, 4299538953], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i9 : checks (tilesOf batches) 130 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 130 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 130 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [2083729427, 2067084311, 2067085335, 2067217431, 2050441243, 2050442267], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2050639899, 2033863711, 2033864735, 2033996831, 1178425379, 1178426403], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1178492963, 1161716775, 1161783335, 1161784359, 1145008171, 1145074731], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1145075755, 1128299567, 2000781359, 2000782383, 1984006195, 1984072755], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1984073779, 1967297591, 1967298615, 1967365175, 1715707963, 1715708987], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1715710011, 1698933823, 1698934847, 1883550783, 1866774595, 1866775619], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1866776643, 1850000453, 1866778693, 39514560829, 8913273257, 17402470869], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [8628057601, 4333093377, 47265624581, 21350917], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i12 : checks (tilesOf batches) 130 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 130 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 130 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1949776919, 1933000731, 1933001755, 1933199387, 1916423199, 1916424223], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1916556319, 1899845667, 1899846691, 1899913251, 1883137063, 86943688741], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [14617459777, 39548184865, 1100321362211, 1100321363235, 1100321364259, 1100321430819], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100321431843, 1100321432867, 1100321433891, 1100321434915, 26428616993, 13141127617], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4433756641, 1099683973603, 21630325221, 13040462309, 47383133673, 34431266297], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4333091329, 21348869, 21349893], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i15 : checks (tilesOf batches) 130 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 130 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 130 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1547323419, 1530547231, 1530548255, 1530680351, 1513969699, 1513970723], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1514037283, 1497261095, 1497327655, 1497328679, 1480552491, 1967158315], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1967159339, 1950383151, 1950449711, 1950450735, 1933674547, 1933741107], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1933742131, 1967297591, 1061328951, 1061395511, 1044619323, 1044620347], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1044621371, 1027845183, 1027846207, 1900327999, 1900329027, 1900330049], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1866776641, 1850000453, 1766115397, 30891213109, 30656471349, 43473979789], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [17436025285, 1099633641967, 17234696701, 30102746625, 38126081, 1099549754883], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [8611278341, 4299536905], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i18 : checks (tilesOf batches) 130 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 130 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 130 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 130 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 130 50 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [1430017055, 1413306403, 1413307427, 1413373987, 1396597799, 1396664359], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1396665383, 1379889195, 1379955755, 1379956779, 1363180591, 2000781359], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2000782383, 1984006195, 1984072755, 61358641201, 1100254253403, 1100254254427], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100254320987, 1100254322011, 1100153659739, 1100153660763, 1100153661787, 21965876569], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4920296793, 43557934453, 13074017745, 4500864465, 1099616863731, 1099616864755], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [12973285877, 8628056577, 21347845, 21348869, 42954020361], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i21 : checks (tilesOf batches) 130 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 130 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 130 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 130 45 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [1329487907, 1312711719, 1312778279, 1312779303, 1296003115, 1296069675], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1296070699, 1279294511, 1279361071, 1279362095, 1262585907, 1262652467], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1262653491, 1245877303, 1245878327, 1245944887, 1229168699, 1380164667], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1380165691, 1363389503, 1363390527, 1363457087, 1665448003, 1665449027], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1833222209, 1816446021, 1648674887, 39363633505, 26462095713, 17637352837], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4534417873, 1099751082451, 12973352437, 4383421941, 71680505, 1099583309307], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [25774295561], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i24 : checks (tilesOf batches) 130 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 130 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 130 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 130 48 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [1145007143, 1128230955, 1128297515, 1128298539, 1111522351, 1111588911], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1111589935, 1094813747, 1094880307, 1883410483, 1866634295, 1866635319], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1866701879, 1849925691, 1849926715, 1849927739, 1833151551, 1833152575], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1833219135, 1866774593, 1782889539, 1782890561, 1766114373, 1564788807], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [35236441401, 26294398265, 1099834968511, 4366646765, 1099633640943, 21563216373], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [12956576245, 4333091329, 38126081, 8594500105, 4299535881], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [1044412459, 1027636271, 1027702831, 1027703855, 1010927667, 1010994227], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1010995251, 994219063, 994220087, 1766038583, 1749262395, 1749263419], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1749264443, 1732488255, 1933815871, 1933882429, 944027715, 944028739], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [944029763, 927253575, 1732560965, 35236509989, 17838684453, 4584749509], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4484088261, 17368915421, 1099667196391, 88457717, 1099600086519, 30136302073], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [17251473913], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1061258287, 1044482099, 1044548659, 1044549683, 1027773495, 1027774519], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1027841079, 1011064891, 1011065915, 1011066939, 994290751, 994291775], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [994358335, 977582147, 977583171, 977584195, 960808007, 960809031], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [30924834093, 26411836717, 9332703533, 13157836233, 8812606921, 172343777], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099683972579, 1099683973603, 25824626173, 12939731453, 4333090305, 38125057], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1900187699, 1883411511, 1883412535, 1883479095, 1866702907, 1866703931], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1866704955, 1665379391, 1665380415, 1665446975, 1648670787, 1648671811], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1648672835, 1766114373, 1766115397, 13090794957, 4500864461, 1099633640943], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099633641967, 21546439161, 12956576249, 4333091329, 38126081], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [48574471221, 541367671, 541368695, 541369719, 1100052998519, 1100052999543], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100053000567, 1100053067127, 1100053068151, 1100103400823, 1100002738551, 1100002739575], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100002740599, 122012141, 1099633640943, 1099633641967, 17251474937, 8661611001], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21347845], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤130) (hj : a.j≤50) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 4 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤132 ∧ 5+a.j≤55 ∧ 1+a.t≤14 at box
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
end Low6961Allocation.Group4
