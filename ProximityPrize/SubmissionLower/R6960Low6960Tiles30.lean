import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass30

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group30
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [10905848837, 2299140105, 2282363917, 1997152271, 1678386191, 2182031379], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1947151377, 1762603025, 1695560725, 1561344021, 1460681749, 1343242265], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1259357209, 1192249369, 1108364317, 1058033693, 1007703069, 940595233], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [907041825, 873488417, 823157797, 789604389, 772828197, 6462599209], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [2167633961, 2150857773, 2100527149, 2050196525, 1966311473, 1915980849], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1865650225, 1815319605, 1764988981, 1731435573, 1681104953, 1647551545], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1613998137, 1563667517, 1530114109, 1513337917, 1463007297, 1446231105], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1412677697, 1379124293, 1362348101, 1345571909, 1312018505, 1295242313], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [9985813729, 9969035493, 9935480045, 14196891893, 14163336445, 18424748293], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [18374415633, 22619050271, 22568717609, 22501607737, 26729465163, 26645578077], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [26544913781, 1100237690243, 1100220912007, 1100204133771, 30739216783, 1100187355535], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100170380691, 1100153602455, 1100120047007, 588260769, 1100103268771, 1100069713323], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [30604998063, 541307311, 474197429, 30554665401, 4769163711, 4735608263], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [8997020111, 8963464663, 13224876511, 30370115045, 13174543851, 4564460013], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [13140988403, 17385623039, 17335290379, 21563147803, 30135233053, 21512815143], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
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
private theorem i51 : checks (tilesOf batches) 139 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [2299140105, 2282363917, 2013929487, 1661608975, 2182031377, 1947151377], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1745825809, 1695560725, 1561344021, 1427127317, 1309687833, 1225802777], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1158694937, 1074809885, 1007702045, 957371421, 890263585, 856710177], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [823156769, 772826149, 739272741, 705719333, 6462599209, 2167633961], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [2117303341, 2066972717, 1999864877, 1932757041, 1865649201, 1815318577], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1764987957, 1714657333, 1681103925, 1613996089, 1580442681, 1546889273], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1496558653, 1479782461, 1446229053, 1395898433, 1379122241, 1345568833], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1312015429, 1295239237, 1278463045, 1244909641, 1228133449, 5757955281], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [10019367129, 9985811681, 14247223529, 14213668081, 14180112633, 18424747269], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [18374414609, 22602272033, 22535162161, 22468052289, 26679132501, 26578468205], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100304799091, 1100288020855, 1100271242619, 1100254464383, 1100237489539, 1100220711303], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [26444249485, 1100187155855, 1100170377619, 1100136822171, 605037981, 1100103266723], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [1100086488487, 30604998063, 541305263, 30571442613, 507749813, 4769161663], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [4718829001, 8980240851, 8929908191, 30370115045, 13191320039, 4547682801], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [13140987379, 17368844803, 17318512143, 30135233053, 17251402269, 21496036907], by decide +kernel⟩
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [1695163407, 2198808593, 1963928593, 1762603025, 1695560725, 1561344021], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1443904533, 1309687833, 1225802777, 1141917721, 1058032669, 990924829], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [940594205, 873486369, 823155745, 789602337, 739271717, 705718309], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [672164901, 6462599209, 2167633961, 2100526125, 2033418285, 1966310445], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1899202609, 1832094769, 1781764145, 1714656309, 1681102901, 1630772277], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1580441657, 1546888249, 1513334841, 1463004221, 1429450813, 1395897405], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1345566785, 1328790593, 1295237185, 1261683781, 1244907589, 1211354181], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1177800777, 1161024585, 5791509705, 10052921553, 10019366105, 9985810657], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [14247222505, 14196889845, 18441524481, 18391191821, 18324081949, 22551939373], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [22468052289, 26679132501, 1100371907939, 1100355129703, 1100338351467, 26561690993], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100304796019, 1100287821175, 1100271042939, 1100237487491, 1100220709255, 26444249485], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100187153807, 1100153598359, 1100120042911, 571483557, 1100086487463, 30604998063], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [541304239, 507748789, 30554665401, 4769160639, 4718827977, 8980239827], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [8929907165, 30353337833, 13174541803, 13107431931, 13057099269, 17284956695], by decide +kernel⟩
private def p14 : P :=
  ⟨unpack [30118455841, 17217846821], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14]
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
private theorem i49 : checks (tilesOf batches) 139 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1796157457, 1729115157, 1578121237, 1443904533, 1326465049, 1225802777], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1141917721, 1058032669, 990924829, 923816989, 856709153, 806378529], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [772825121, 722494501, 672163877, 655387685, 6462599209, 2167633961], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [2083748909, 2016641069, 1949533229, 1865648177, 1815317553, 1764986929], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1697879093, 1647548469, 1597217845, 1546887225, 1513333817, 1463003193], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1412672573, 1379119165, 1362342973, 1312012353, 1278458945, 1261682753], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1211352133, 1194575941, 1177799749, 1127469129, 1110692937, 5808286917], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [10086475977, 10036143317, 10002587869, 14263999717, 14213667057, 18458301693], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [18391191821, 18324081949, 22551939373, 22468052289, 1100422239575, 26662355289], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100405461339, 1100371905891, 1100355127655, 1100338152811, 26561690993, 1100304597363], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100287819127, 1100254263679, 1100220708231, 1100203929995, 26427472273, 1100170374547], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [1100136819099, 1100086486439, 541303215, 26276476341, 507747765, 30521110977], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [4752382403, 4702049741, 8946684379, 8896351717, 13140986355, 13073876481], by decide +kernel⟩
private def p13 : P :=
  ⟨unpack [17301733907, 17234624033], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13]
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
private theorem i52 : checks (tilesOf batches) 139 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1460681749, 1343242265, 1242579993, 1158694937, 1058032669, 990924829], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [923816989, 856709153, 806378529, 756047905, 705717285, 672163877], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [638610469, 6462599209, 2167633961, 2083748909, 2016641069, 1949533229], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1865648177, 1798540337, 1748209713, 1681101877, 1630771253, 1580440629], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1530110009, 1479779385, 1446225977, 1395895357, 1362341949, 1328788541], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1278457921, 1244904513, 1228128321, 1177797701, 1161021509, 1127468101], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1093914697, 1077138505, 5825064129, 10086475977, 10052920529, 10019365081], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [14263999717, 14213667057, 18458301693, 18391191821, 22619049245, 22535162161], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [22451275077, 1100455793999, 1100439015763, 1100422237527, 26645578077, 1100388682079], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100371707235, 1100338151787, 1100321373551, 26544913781, 1100287818103, 1100254262655], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1100220707207, 1100187151759, 1100153596311, 1100120040863, 1100069708203, 524524977], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [474192317, 4718826953, 4668494293, 8913128929, 8846019057, 13073876481], by decide +kernel⟩
private def p12 : P :=
  ⟨unpack [13006766609, 17234624035], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
private theorem i15 : checks (tilesOf batches) 139 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 139 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 139 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1175472153, 1074809885, 1007702045, 940594205, 873486369, 806378529], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [772825121, 705717285, 672163877, 638610469, 6462599209, 2167633961], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2083748909, 2016641069, 1949533229, 1865648177, 1798540337, 1748209713], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1664324661, 1613994037, 1563663413, 1513332793, 1463002169, 1429448761], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1379118141, 1328787517, 1295234109, 1261680705, 1228127297, 1194573889], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1161020485, 1127467077, 1110690885, 1060360265, 1043584073, 5825064129], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [10086475977, 10052920529, 14297555165, 14263999717, 14196889845, 18441524481], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [18374414609, 22602272033, 22518384949, 1100489348423, 1100472570187, 1100439014739], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100422236503, 1100388484447, 1100371706211, 1100338150763, 1100304595315, 1100287817079], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1100254261631, 1100203928971, 1100170373523, 1100136818075, 1100086485415, 541302189], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [490969529, 4735604165, 4668494293, 8913128929, 8846019057, 13073876481], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [13006766609, 17234624035], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i18 : checks (tilesOf batches) 139 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 139 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 139 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 139 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 139 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [957371421, 873486369, 823155745, 772825121, 705717285, 672163877], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [638610469, 6462599209, 2167633961, 2100526125, 2016641069, 1949533229], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1865648177, 1798540337, 1748209713, 1664324661, 1613994037, 1563663413], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1496555577, 1463002169, 1412671545, 1362340925, 1328787517, 1295234109], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1244903489, 1211350081, 1177796673, 1127466053, 1110689861, 1077136453], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1043583049, 1010029641, 5825064129, 10086475977, 10052920529, 14297555165], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [14247222505, 14196889845, 18424747269, 1100489151807, 1100489347399, 1100472569163], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100439013715, 1100422038871, 1100388483423, 1100354927975, 1100321372527, 1100287817079], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1100254261631, 1100220706183, 1100187150735, 1100136818075, 1100103262627, 541302189], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [490969529, 4735604165, 4668494293, 8913128929, 8846019057, 13073876481], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [13006766609, 17217846821, 1099533047339], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i21 : checks (tilesOf batches) 139 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 139 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 139 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 139 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 139 53 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [789602337, 722494501, 672163877, 638610469, 6462599209, 2167633961], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2117303341, 2033418285, 1966310445, 1865648177, 1815317553, 1748209713], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1664324661, 1613994037, 1563663413, 1496555577, 1446224953, 1412671545], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1345563709, 1312010301, 1278456893, 1228126273, 1194572865, 1161019457], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1110688837, 1093912645, 1060359237, 1026805833, 993252425, 5825064129], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [10086475977, 10036143317, 14280777953, 1100489151803, 1100505928003, 1100489346375], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100455790927, 1100438816083, 1100405260635, 1100371705187, 1100338149739, 1100304594291], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100271038843, 1100237483395, 1100187150735, 1100153595287, 1100103262627, 541302189], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [490969529, 4735604165, 4668494293, 8896351717, 8846019057, 13057099269], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [12989989397, 1099549824551, 17201069609], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i24 : checks (tilesOf batches) 139 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 139 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 139 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 139 48 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [638610469, 6462599209, 2167633961, 2134080557, 2050195501, 1966310445], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1882425393, 1815317553, 1748209713, 1681101877, 1630771253, 1563663413], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1496555577, 1463002169, 1412671545, 1345563709, 1312010301, 1278456893], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1228126273, 1194572865, 1161019457, 1110688837, 1077135429, 1043582021], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1010028617, 976475209, 5825064129, 1100489151799, 1100505927999, 1100505926979], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100472568139, 1100438816083, 1100405260635, 1100371705187, 1100338149739, 1100304594291], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100271038843, 1100237483395, 1100187150735, 1100136818075, 1100103262627, 541302189], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [474192317, 4718826953, 4668494293, 8896351717, 8829241845, 13057099269], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [12973212185, 1099566601763, 17184292397, 4641324], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [2167633961, 2150857773, 2066972717, 1983087661, 1899202609, 1832094769], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1764986929, 1681101877, 1630771253, 1580440629, 1513332793, 1463002169], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1412671545, 1362340925, 1312010301, 1278456893, 1211349057, 1177795649], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1144242241, 1093911621, 1077135429, 1043582021, 993251401, 976475209], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100472374583, 1100505927995, 1100505926979, 1100472568139, 1100455593295, 1100422037847], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100388482399, 1100354926951, 1100304594291, 1100271038843, 1100220706183, 1100187150735], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100136818075, 1100086485415, 524524977, 474192317, 4718826953, 4651717081], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [8879574505, 8812464633, 13040322057, 12956434973, 1099583378975, 1099533046315], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1999864877, 1915979825, 1848871985, 1781764145, 1697879093, 1647548469], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1580440629, 1513332793, 1463002169, 1412671545, 1362340925, 1312010301], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1278456893, 1228126273, 1177795649, 1144242241, 1093911621, 1060358213], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1043582021, 993251401, 959697993, 1100489151795, 1100505927995, 1100505926979], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100489345351, 1100455593295, 1100422037847, 1100388482399, 1100338149739, 1100304594291], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100271038843, 1100220706183, 1100187150735, 1100136818075, 574857637, 524524977], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4752382401, 4702049741, 8929907165, 8862797293, 13090654717, 13023544845], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099583378975, 1099533046315], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1781764145, 1714656309, 1647548469, 1597217845, 1530110009, 1479779385], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1429448761, 1362340925, 1328787517, 1278456893, 1228126273, 1177795649], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1144242241, 1093911621, 1060358213, 1026804805, 993251401, 959697993], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100472374579, 1100505927995, 1100522704191, 1100489345351, 1100455593295, 1100422037847], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100388482399, 1100338149739, 1100304594291, 1100254261631, 1100220706183, 1100170373523], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100120040863, 558080425, 507747765, 4752382401, 4685272529, 8929907165], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099600156187, 1099533046315], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 139 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤139) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 30 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤141 ∧ 6+a.j≤59 ∧ 2+a.t≤14 at box
    have pos := ha.1
    have cases : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 := by omega
    rcases cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
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
end Low6960Allocation.Group30
