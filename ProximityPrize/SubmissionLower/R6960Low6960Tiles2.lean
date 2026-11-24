import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass2

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group2
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2315324421, 989925387, 536941577, 2298877961, 2064063501, 1661411341], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [15168054285, 6544569365, 2249604117, 2232827929, 23708779545, 10790329377], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [6478587941, 2166845481, 2166846505, 2116515881, 2049408045, 1982300205], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1931969581, 1864861745, 1814531121, 1764200497, 1713869877, 2117244981], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [2083691573, 2033360953, 1983030329, 1949476921, 1882369085, 1848815677], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1815262269, 1764931649, 1731378241, 1714602049, 1664271429, 1630718021], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1613941829, 1580388425, 1546835017, 1530058825, 1496505421, 1479729229], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [14630982797, 18472964347, 1100035318195, 1100018474423, 1100001696187, 1099984917951], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099951362503, 1099934584267, 1099917806031, 4684289489, 1099884250583, 4650734041], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099850695135, 1099833916899, 8895368677, 1099800361451, 4549872113, 1099766806003], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099733185019, 8794506749, 1099699629571, 8744174089, 1099649362447, 104179221], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [12972031513, 53846561, 12921698853, 20225577], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i3 : checks (tilesOf batches) 139 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 139 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 139 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [2298877961, 2097617935, 1678188559, 15168054285, 6544569365, 2249604117], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2232827929, 23708779545, 10790329377, 6478587941, 2166845481, 2150069289], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2082961449, 1999076397, 1931968557, 1881637933, 1797752881, 1764199473], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1713868849, 1646761013, 2083690549, 2033359925, 1966252089, 1932698681], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1882368057, 1832037437, 1798484029, 1748153405, 1697822785, 1681046593], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1647493185, 1597162565, 1580386373, 1546832965, 1513279561, 1479726153], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1462949961, 1429396557, 1412620365, 9178390945, 1099867480483, 1099867479463], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099884255659, 1099901031855, 1099901030839, 1099917807035, 1099967862211, 1099917806019], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099934582215, 405901773, 1099917803983, 1099884248535, 4650733017, 1099867470299], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [4616980961, 1099833914851, 1099783516655, 4549871089, 1099749961207, 1099532001787], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [8794505725, 1099716405759, 1099548777983, 57856, 13053926917, 1099531999751], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [57860, 1099666073099, 16834056, 8727395853, 1099531998735, 33610252], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099632517651, 33610256, 67162644, 67162648, 12955253277, 70557213], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [83938844, 83938848, 100715044, 20224553, 100715048, 12888143405], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [117491244], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i6 : checks (tilesOf batches) 139 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 139 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 139 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 139 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [15168054285, 6544569365, 2249604117, 2232827929, 23708779545, 10790329377], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [6478587941, 2166845481, 2116514857, 2049407017, 1965521965, 1898414125], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1831306285, 1764198449, 1713867825, 1663537201, 1613206581, 2050136117], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1999805493, 1932697657, 1882367033, 1832036409, 1781705789, 1748152381], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1697821757, 1647491137, 1613937729, 1597161537, 1546830917, 1513277509], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1496501317, 1446170697, 1429394505, 1395841097, 1362287693, 1345511501], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099867480467, 1099867479447, 1099884255643, 1099884254627, 1099901030823, 1099901029807], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099917806003, 1100001416635, 1099917804987, 456233409, 1099934581187, 1099951357383], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [405900749, 1099917801935, 1099884246487, 355568089, 1099833848291, 4600202725], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099800292843, 1099532001771, 1099548777967, 1099766737395, 57840, 4533092853], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099531999735, 57844, 16834040, 1099716404735, 50386428, 3593728], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [33610240, 8760950277, 67162628, 1099666072075, 67162632, 83938828], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [83938832, 8693840405, 1099615739415, 100715028, 100715032, 117491228], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [53778977, 117491232, 12921697829, 117491236, 134267432, 134267436], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i9 : checks (tilesOf batches) 139 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 139 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 139 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [10856312849, 2249604117, 2232827929, 23708779545, 10790329377, 6478587941], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2166845481, 2099737641, 2032629801, 1948744749, 1881636909, 1814529069], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1747421233, 1680313393, 1629982769, 1579652149, 2016581685, 1966251061], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1899143225, 1848812601, 1798481977, 1748151357, 1697820733, 1664267325], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1613936705, 1580383297, 1546829889, 1496499269, 1479723077, 1446169669], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1395839049, 1379062857, 1345509449, 1311956045, 1295179853, 1099850703239], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099867479435, 1099884255631, 1099867477399, 1099884253595, 1099901029795, 1099901028779], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099917804975, 1100034971059, 1099934581175, 1100001415611, 1099934580159, 439455173], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099951356359, 1099917800911, 372345301, 1099884179927, 1099532001755, 4616979937], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099833847267, 1099532000739, 57824, 57828, 1099800291819, 1099531999723], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [16834024, 54764, 16834028, 4549870065, 50386416, 1099749959159], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [67162612, 67162616, 67162620, 8777727489, 1099699626499, 83938816], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [83938820, 100715016, 1099649293839, 100715020, 8710617617, 117491216], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [117491220, 1099598961179, 117491224, 134267420, 12938475041, 134267424], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [151043620, 151043624, 151043628], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i12 : checks (tilesOf batches) 139 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 139 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 139 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 139 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [2249604117, 2232827929, 23708779545, 10790329377, 6478587941, 2166845481], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2099737641, 2015852585, 1931967533, 1864859693, 1797751853, 1730644017], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1663536177, 1613205553, 1546097717, 1999804469, 1949473845, 1865588793], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1815258169, 1781704761, 1714596925, 1681043517, 1630712893, 1580382273], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1546828865, 1513275457, 1462944837, 1429391429, 1412615237, 1362284617], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1328731209, 1311955017, 1278401613, 1244848205, 1099850703227, 1099850702211], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099867478407, 1099884254603, 1099884253587, 1099884252571, 1099901028767, 1099917804967], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100068525483, 1099917803951, 1100018192823, 1099934580151, 1099951356351, 456232385], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099951355335, 1099532001743, 389122513, 1099900957139, 1099532000727, 57812], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099867401691, 57816, 4633757149, 33610204, 33610208, 1099817069031], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [50386404, 50386408, 4566647277, 1099783513583, 67162604, 67162608], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [83938804, 1099733180923, 83938808, 8794504701, 100715004, 100715008], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [100715012, 1099666071051, 117491208, 8727394829, 117491212, 134267408], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099615738391, 134267412, 134267416, 151043612, 12938475041, 151043616], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [151043620, 167819816, 167819820], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i15 : checks (tilesOf batches) 139 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 139 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 139 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 139 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [19413813273, 10790329377, 6478587941, 2166845481, 2099737641, 2015852585], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1931967533, 1864859693, 1797751853, 1713866801, 1663536177, 1613205553], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1546097717, 1983027253, 1932696629, 1865588793, 1815258169, 1764927545], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1697819709, 1647489085, 1613935677, 1563605057, 1513274433, 1479721025], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1429390405, 1412614213, 1379060805, 1328730185, 1295176777, 1278400585], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1228069965, 1211293773, 1099733066099, 1099850702199, 1099850701183, 1099867477379], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099867476363, 1099884252563, 1099884251547, 1099917804959, 1099917803943, 1100068525483], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099599045035, 1099934580143, 1100018192823, 1099934579131, 456232385, 1099951355331], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099548778947, 1099833717195, 1099548777931, 405899725, 57804, 55760], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [57808, 1099884178903, 33610196, 50386392, 4633757149, 50386396], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099833846243, 67162592, 67162596, 67162600, 4566647277, 1099783513583], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [83938796, 83938800, 100714996, 1099733180923, 100715000, 8794504701], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [100715004, 117491200, 1099682848263, 117491204, 134267400, 8727394829], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [134267404, 1099632515603, 134267408, 151043604, 1099599032859, 151043608], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [151043612, 12938475041, 167819808, 167819812, 167819816, 184596012], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i18 : checks (tilesOf batches) 139 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 139 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 139 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 139 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 139 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [15102071837, 6478586917, 2183621669, 2166845481, 2116514857, 2032629801], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1931967533, 1864859693, 1797751853, 1713866801, 1663536177, 1596428337], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1529320501, 1983027253, 1915919413, 1848811577, 1798480953, 1748150329], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1681042493, 1647489085, 1597158461, 1546827841, 1496497217, 1462943809], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1412613189, 1379059781, 1345506373, 1311952969, 1278399561, 1244846153], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1211292749, 1177739341, 1099733066091, 1099716287859, 1099850701175, 1099850700159], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099867476359, 1099884252555, 1099901028755, 1099901027739, 1099917803939, 1099599045027], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100085302695, 1099615821223, 1099934580139, 1100034970035, 1099934579127, 1099548778939], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099951355327, 456232385, 56768, 16833988, 1099800162763, 55752], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [3595720, 57800, 405899725, 33610188, 1099900956115, 50386384], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [50386388, 50386392, 4633757149, 1099850623455, 67162588, 67162592], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [83938788, 1099800290795, 83938792, 4566647277, 83938796, 100714992], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099749958135, 100714996, 117491192, 8794504701, 117491196, 1099699625475], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [117491200, 134267396, 134267400, 134267404, 8710617617, 1099632515603], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099632587283, 151043600, 151043604, 151043608, 167819804, 167819808], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [12921697829, 167819812, 184596008, 184596012], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i21 : checks (tilesOf batches) 139 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 139 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 139 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 139 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 139 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [10790330401, 2183621669, 2166845481, 2133292073, 2049407017, 1948744749], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1864859693, 1797751853, 1713866801, 1663536177, 1596428337, 1529320501], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1983027253, 1915919413, 1848811577, 1798480953, 1748150329, 1681042493], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1630711869, 1580381245, 1530050625, 1496497217, 1446166593, 1395835973], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1362282565, 1328729157, 1278398537, 1261622345, 1228068937, 1177738317], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1160962125, 1099716288871, 1099733065067, 1099733064051, 1099850700155, 1099867476351], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099884252551, 1099884251535, 1099901027735, 1099615822235, 1099917803935, 1099615821219], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100085302695, 1099917802923, 1099615820203, 1100034970035, 1099934579123, 1099532001719], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099951355323, 16833980, 456232385, 16833984, 1099816939975, 33610180], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [33610184, 405899725, 50386380, 1099900956115, 50386384, 67162580], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [67162584, 4633757149, 1099850623455, 67162588, 83938784, 83938788], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099800290795, 100714984, 4566647277, 100714988, 100714992, 1099749958135], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [117491188, 117491192, 117491196, 8777727489, 1099699625475, 134267392], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [134267396, 134267400, 151043596, 1099632515603, 1099632587283, 151043600], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [8693840405, 151043604, 167819800, 167819804, 167819808, 184596004], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [12904920617, 184596008, 184596012], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i24 : checks (tilesOf batches) 139 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 139 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 139 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 139 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 139 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [2183621669, 2166845481, 2150069289, 2066184233, 1965521965, 1881636909], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1814529069, 1730644017, 1663536177, 1613205553, 1529320501, 1983027253], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1932696629, 1848811577, 1798480953, 1748150329, 1681042493, 1630711869], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1580381245, 1530050625, 1479720001, 1446166593, 1395835973, 1362282565], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1328729157, 1278398537, 1244845129, 1211291721, 1160961101, 1144184909], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099716288867, 1099733065063, 1099733064047, 1099850700151, 1099850699135, 1099867475335], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099884251535, 1099884250519, 1099599045015, 1099901026719, 1099615821215, 1100085302695], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099917802919, 1099615820199, 1099548778927, 1099934579123, 1100018192823, 1099951355323], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [16833976, 16833980, 456232385, 33610176, 1099816939975, 33610180], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [50386376, 50386380, 389122513, 1099900956115, 67162576, 67162580], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [67162584, 1099850623455, 83938780, 4616979937, 83938784, 83938788], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099800290795, 100714984, 100714988, 4549870065, 117491184, 1099749958135], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [117491188, 117491192, 134267388, 134267392, 8760950277, 1099682848263], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [134267396, 151043592, 151043596, 1099632515603, 1099632587283, 151043600], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [151043604, 8677063193, 167819800, 167819804, 167819808, 184596004], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [184596008, 12888143405, 184596012], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [2066184233, 1965521965, 1898414125, 1831306285, 1747421233, 1680313393], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1613205553, 1546097717, 1999804469, 1932696629, 1865588793, 1798480953], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1748150329, 1681042493, 1630711869, 1580381245, 1513273409, 1479720001], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1446166593, 1379058757, 1345505349, 1311951941, 1261621321, 1228067913], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1194514505, 1160961101, 1127407693, 1099716288863, 1099716287847, 1099733064043], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099733063027, 1099867476347, 1099867475331, 1099884251531, 1099901027731, 1099599045011], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099615821211, 1099901026719, 1099615820195, 1099917802919, 1100068525483, 1099615819179], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57768, 1099800164783, 1099532001711, 1100018192823, 16833972, 1099951355323], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [16833976, 33610172, 33610176, 439455173, 1099816939975, 50386372], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [50386376, 50386380, 1099900956115, 67162576, 372345301, 67162580], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [83938776, 1099850623455, 83938780, 83938784, 4600202725, 100714980], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1099800290795, 100714984, 100714988, 117491184, 4533092853, 1099632589303], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [117491188, 1099733180923, 117491192, 134267388, 134267392, 8760950277], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [1099682848263, 134267396, 151043592, 151043596, 1099632587283, 151043600], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [1099615738391, 167819796, 8677063193, 167819800, 167819804, 167819808], by decide +kernel⟩
private def p15 : P :=
  ⟨unpack [184596004, 184596008, 184596012], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15]
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 139 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1831306285, 1747421233, 1680313393, 1629982769, 1546097717, 2016581685], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1949473845, 1865588793, 1815258169, 1748150329, 1681042493, 1630711869], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1580381245, 1530050625, 1479720001, 1446166593, 1379058757, 1345505349], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1311951941, 1261621321, 1228067913, 1194514505, 1144183885, 1110630477], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099716288859, 1099716287843, 1099716286827, 1099716285811, 1099850699131, 1099867475331], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099884251531, 1099615822223, 1099901027731, 1099615821207, 1099901026719, 1099615820191], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099917802919, 1099632596391, 1100068525483, 57768, 3596716, 1099934579123], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [16833968, 16833972, 1100001415611, 1099951355323, 33610168, 33610172], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [33610176, 439455173, 1099816939975, 50386372, 50386376, 67162572], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099900956115, 67162576, 372345301, 67162580, 83938776, 1099850623455], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [83938780, 83938784, 4600202725, 100714980, 100714984, 1099783513583], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [100714988, 117491184, 117491188, 1099733180923, 117491192, 134267388], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [134267392, 134267396, 1099666071051, 151043592, 151043596, 1099632587283], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [151043600, 151043604, 1099598961179, 167819800, 167819804, 167819808], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [184596004, 184596008, 184596012], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1629982769, 1562874933, 2016581685, 1949473845, 1882366009, 1815258169], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1764927545, 1697819709, 1647489085, 1597158461, 1530050625, 1479720001], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1446166593, 1379058757, 1345505349, 1311951941, 1261621321, 1228067913], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1194514505, 1144183885, 1110630477, 1099699511643, 1099716287843, 1099716286827], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099716285811, 1099850699131, 1099867475331, 1099884251531, 1099615822219, 1099901027731], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099615821207, 1099901026719, 1099615820191, 1099917802919, 1099632596391, 57764], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57768, 473011629, 3596716, 1099934579123, 16833968, 16833972], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [489787833, 33610168, 1099934578111, 33610172, 33610176, 50386372], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099800162763, 50386376, 67162572, 67162576, 1099884178903, 67162580], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [83938776, 83938780, 1099833846243, 83938784, 100714980, 100714984], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099783513583, 100714988, 117491184, 117491188, 117491192, 1099716403711], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [134267388, 134267392, 134267396, 1099666071051, 151043592, 151043596], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1099632587283, 151043600, 151043604, 87333401, 167819800, 167819804], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [53777953, 167819808, 184596004, 184596008, 184596012], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 139 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [1966251061, 1882366009, 1832035385, 1764927545, 1697819709, 1647489085], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1597158461, 1530050625, 1479720001, 1446166593, 1379058757, 1345505349], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1311951941, 1261621321, 1228067913, 1194514505, 1144183885, 1110630477], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099699511643, 1099699510627, 1099716286827, 1099716285811, 1099850699131, 1099867475331], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099884251531, 1099615822219, 1099901027731, 1099615821203, 1099901026719, 1099615820191], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099934580135, 1099615819175, 57764, 57768, 16833964, 1099934579123], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [16833968, 16833972, 33610168, 1099951355327, 33610172, 50386368], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [50386372, 1099816939979, 50386376, 67162572, 67162576, 1099884178903], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [67162580, 83938776, 83938780, 1099833846243, 83938784, 100714980], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [100714984, 100714988, 70559217, 117491184, 117491188, 117491192], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [87335421, 134267388, 134267392, 42500, 134267396, 42504], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [134267400, 70557197, 42508, 151043596, 42512, 151043600], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [16818708, 1099615810071, 151043604, 16818712, 167819800, 16818716], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [167819804, 33594912, 167819808, 33594916, 167819812, 33594920], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [184596008, 33594924, 184596012], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 139 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤139) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((2 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 2 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group2
