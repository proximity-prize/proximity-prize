import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass37

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group37
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [19480579077, 15152062477, 10840322067, 2233613333, 2200059931, 2049066011], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1914849305, 1797409821, 1696747549, 1629639709, 1528977441, 1461869601], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1411538977, 15053317159, 6446609451, 2134866991, 2134868015, 2084537391], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [2000652339, 1950321715, 1899991091, 1832883255, 1782552631, 1748999223], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1698668603, 1648337979, 1614784571, 1564453951, 1547677759, 6363984959], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [2052242499, 2035466307, 1985135687, 1951582279, 1918028871, 1884475467], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [13644030327, 17888664963, 17821555091, 17737668007, 4803637683, 21965525431], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4786859447, 9048271295, 9014715847, 21864861135, 13259350483, 13225795035], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [13192239587, 26059164135, 17436874223, 17386541563, 25924945415, 21631176199], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099634496015, 21580843539, 1099617717779, 1099584162331, 21513733667, 1099550606883], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [25773949483, 5423656], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i3 : checks (tilesOf batches) 138 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 138 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 138 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 138 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 138 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 138 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 138 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [19463804939, 10840321041, 2233612309, 2233613333, 2183282715, 2015511577], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1898072089, 1780632605, 1679970333, 1596085277, 1495423009, 1428315169], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1377984545, 10758349863, 6446608427, 2151643179, 2134866991, 2067759151], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [2000651311, 1933543475, 1866435635, 1816105011, 1748997175, 1715443767], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1665113143, 1614782523, 1564451899, 1530898491, 1480567871, 1447014463], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [2069017663, 2035464259, 1985133635, 1951580227, 1901249607, 1850918983], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1817365575, 1783812171, 13677584751, 13627252091, 17855109515, 609333659], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [17771222431, 307342753, 4837190059, 21982302643, 4803634611, 9048269247], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [9014713799, 21881638347, 13259348435, 13225792987, 21780974051, 13175460327], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [17420094963, 1099735159287, 1099718381051, 25958499839, 17352985091, 1099684825603], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [21597619727, 1099634492943, 1099600937495, 21530509855, 1099567382047, 25790726695], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [5421608], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i6 : checks (tilesOf batches) 138 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 138 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 138 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 138 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 138 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 138 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [15152063501, 6528578581, 2233613333, 2183282713, 2032288793, 1914849305], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1780632605, 1679970333, 1596085277, 1495423009, 1411537953, 1361207329], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [10758349863, 6446608427, 2151643179, 2101312559, 2034204719, 1950319663], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1883211827, 1816103987, 1765773363, 1698665527, 1648334903, 1598004279], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1547673659, 1497343035, 1463789627, 1413459007, 1379905599, 2018686015], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1951578179, 1901247555, 1867694147, 1817363527, 1783810119, 1733479495], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1699926091, 13694361963, 13644029303, 17855109515, 1100188070283, 642887059], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [357673369, 17771222431, 4870743459, 4820410799, 17687335347, 4786855351], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [9031489987, 21881638347, 8981157327, 13225791963, 1099819045347, 21764196839], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [13175459303, 1099802267111, 1099751934451, 17403316727, 1099718379003, 25941722627], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [17352984067, 1099684823555, 1099651268107, 21564064279, 1099600935447, 1099550602787], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [25790726695, 21496954407], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i9 : checks (tilesOf batches) 138 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 138 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 138 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 138 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 138 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 138 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [10840322067, 2233613333, 2216837145, 2065843225, 1931626521, 1797409821], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1696747549, 1596085277, 1495423009, 1411537953, 1344430113, 10758349863], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [6446608427, 2151643179, 2067758127, 2000650287, 1933542447, 1849657395], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1782549555, 1715441715, 1648333879, 1598003255, 1547672631, 1497342011], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1447011387, 1413457979, 1363127359, 1329573951, 1951577151, 1884469315], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1850915907, 1800585283, 1750254663, 1699924039, 1666370631, 1616040011], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [13711139175, 13644029303, 1100238401919, 1100204846471, 17855109515, 659663247], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [391226773, 17771222431, 4870742435, 4837186987, 17670558135, 9081821623], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [9031488963, 21864861135, 8981156303, 1099902931407, 1099869375959, 13209013727], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099835820511, 21747419627, 1099785487851, 13141903855, 1099751932403, 17369761279], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099701599743, 1099668044295, 25908168203, 17302651407, 1099617711635, 21530508831], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i12 : checks (tilesOf batches) 138 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 138 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 138 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 138 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 138 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 138 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [2233613333, 2216837145, 2099397657, 1948403737, 1814187037, 1713524765], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1612862493, 1512200225, 1428315169, 1361207329, 10758349863, 6446608427], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2151643179, 2067758127, 1983873071, 1899988015, 1816102963, 1748995123], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1698664499, 1614779447, 1564448823, 1514118199, 1447010363, 1413456955], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1363126331, 1312795711, 1279242303, 1918022719, 1850914883, 1800584259], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1750253635, 1699923015, 1649592391, 1616038983, 1565708363, 13694361963], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100069450099, 13627252091, 1100086226299, 1100221622659, 17838332303, 659662223], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [424780181, 17754445219, 4870741411, 4820408751, 17653780923, 9065043387], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099953263043, 8997933515, 1099919707595, 21848083923, 1099886152147, 13242568151], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099835819487, 13175458279, 1099802264039, 21730642415, 1099751931379, 17403315703], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099718308347, 1099701598719, 1099667975687, 17319428619, 1099651266059, 25874613779], by decide +kernel⟩
private def p11 : P :=
  ⟨unpack [17235541535], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11]
private theorem i15 : checks (tilesOf batches) 138 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 138 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 138 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 138 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 138 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1981958169, 1847741469, 1730301981, 1629639709, 1528977441, 1445092385], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1377984545, 10758349863, 6446608427, 2151643179, 2067758127, 1983873071], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1899988015, 1816102963, 1748995123, 1681887283, 1598002231, 1547671607], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1497340983, 1430233147, 1379902523, 1346349115, 1279241277, 1245687869], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1884468287, 1817360451, 1767029827, 1716699203, 1649591367, 1616037959], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1565707335, 1515376715, 1100086227307, 13677584751, 1100103003507, 13610474879], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100238399871, 693216647, 17821555091, 441557393, 4887518623, 17737668007], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4837185963, 9081820599, 1100003594679, 17637003709, 1099970039231, 9014710727], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099919706571, 1099886151123, 13242568151, 21814529499, 1099835818463, 13175458279], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099785485803, 21697087991, 13108348407, 1099735085559, 1099735153143, 1099684752899], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [1099684820483, 17319428619, 17235541535], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
private theorem i18 : checks (tilesOf batches) 138 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 138 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 138 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 138 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 138 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [1663194141, 1545754657, 1461869601, 1394761761, 10758349861, 6446608427], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2151643179, 2084535343, 1983873071, 1916765231, 1816102963, 1748995123], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1681887283, 1598002231, 1547671607, 1480563767, 1413455929, 1363125305], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1329571897, 1279241277, 1245687869, 1850913855, 1783806019, 1733475395], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1683144771, 1616036935, 1582483527, 1532152903, 1481822283, 1100069450091], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [13660807539, 1100086226291, 1100103002491, 13593697667, 709993859, 458334605], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [17804777879, 4904295835, 4837185963, 17704113583, 1100037149103, 9081820599], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100003593655, 1099953260995, 9014710727, 1099919705547, 13242568151, 1099869372887], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099819040227, 13175458279, 1099768707567, 1099751862771, 13091571195, 1099718374907], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099701530111, 17319428619, 1099651197451, 17218764323], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i21 : checks (tilesOf batches) 138 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 138 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 138 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 138 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [1411538977, 10758349861, 6446608427, 2151643179, 2101312559, 2000650287], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1916765231, 1832880179, 1748995123, 1681887283, 1598002231, 1547671607], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1480563765, 1413455929, 1363125305, 1329571897, 1262464061, 1228910653], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1850913855, 1767028803, 1716698179, 1666367555, 1599259719, 1548929095], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1515375687, 1448267851, 1100069450087, 1100103003503, 13644030327, 1100103002491], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100221621635, 475111821, 4904295835, 1100070703527, 4837185963, 1100020370867], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [9081820599, 1099986815419, 9014710727, 1099936482759, 1099886150099, 13242568151], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099835817439, 13158681067, 1099785484779, 1099768639983, 13091571195, 1099718374907], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099701530111, 1099651197451, 17302651407, 17201987111], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i24 : checks (tilesOf batches) 138 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 138 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 138 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 138 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [10758351911, 2151643179, 2118089775, 2034204719, 1933542447, 1849657395], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1765772339, 1698664499, 1614779447, 1547671607, 1480563765, 1413455929], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1363125305, 1329571897, 1279241277, 1228910653, 1834136639, 1767028803], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1699920963, 1649590339, 1582482503, 1532151879, 1498598471, 1431490635], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100069450087, 1100086226291, 1100103002491, 709993859, 491889037, 4904295835], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100087480739, 4837185963, 1100037148079, 1100003592631, 9065043387, 1099953259971], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [8997933515, 1099902927311, 13225790939, 1099852594651, 1099785484779, 13141903855], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099768639983, 1099735152119, 17369761279, 1099701530111, 1099651197451, 17269096983], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [21480177195], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i27 : checks (tilesOf batches) 138 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 138 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 138 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 138 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [2151643179, 2134866991, 2050981935, 1967096879, 1866434611, 1782549555], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1715441715, 1614779447, 1564448823, 1497340981, 1430233145, 1379902521], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1329571897, 1279241277, 1228910653, 1834136639, 1767028803, 1699920963], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1649590339, 1582482503, 1532151879, 1481821255, 1414713419, 1100069450087], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100086226291, 1100119779707, 693216647, 475111825, 4887518623, 1100104257951], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100053925291, 4820408751, 1100003592631, 9065043387, 1099953259971, 8981156303], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099902927311, 1099852594651, 13209013727, 1099785484779, 1099768639983, 13125126643], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099735152119, 1099701530111, 17336206855, 1099634420239, 17252319771], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i30 : checks (tilesOf batches) 138 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 138 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 138 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1983874095, 1883211827, 1799326771, 1732218931, 1631556663, 1564448821], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1514118199, 1430233145, 1396679737, 1346349113, 1279241277, 1245687869], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1850913855, 1767028803, 1699920963, 1649590339, 1582482503, 1532151879], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1481821255, 1414713419, 1100069450091, 1100103003507, 1100238399871, 676439435], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [491889041, 1100104257951, 4870741411, 1100053925291, 4820408751, 1100003592631], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [9048266175, 1099953259971, 1099902927311, 8964379091, 1099852594651, 13192236515], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099785484779, 1099751862771, 13108349431, 1099718374907, 1099684752899, 17319429643], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i33 : checks (tilesOf batches) 138 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 138 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 138 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1732218931, 1648333879, 1581226039, 1514118197, 1447010361, 1396679737], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1346349113, 1296018493, 1245687869, 1850913855, 1783806019, 1716698179], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1649590339, 1582482503, 1532151879, 1481821255, 1414713419, 1100069450091], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100086226295, 1100238399871, 676439435, 491889045, 1100104257951, 4870741411], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100053925291, 4803631539, 1100003592631, 9031488963, 1099953259971, 1099902927311], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8964379091, 1099835817439, 1099768707567, 1099751862771, 1099718374907, 1099684752899], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i36 : checks (tilesOf batches) 138 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 138 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 138 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 37 where
  orders := orders
  covers := by
    intro a ha box
    change 3+a.b≤141 ∧ 7+a.j≤59 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group37
