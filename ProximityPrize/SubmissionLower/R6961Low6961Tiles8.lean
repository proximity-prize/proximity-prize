import ProximityPrize.SubmissionLower.R6961Low6961AllocTiles
import ProximityPrize.SubmissionLower.R6961Low6961Mass8

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6961Allocation.Group8
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23459073031, 1851794447, 1835018259, 1835019283, 1835282451, 1818506263], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1818638359, 1818704919, 1801928731, 1801929755, 1802061851, 1802062879], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1802063903, 1802195999, 1785419811, 1785420835, 1785487395, 1768711207], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1768712231, 1835887655, 1819111467, 1819112491, 1819113515, 1802337327], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1819181103, 1785627695, 1768851507, 1768852531, 1768919091, 1752142903], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1785698359, 1735367735, 1651482683, 1651483707, 1517267003, 1500490815], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1466937407, 1467003967, 1450227779, 1349565507, 1349566531, 1332790343], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099888180615, 1099888181639, 1099888182663, 1099787514271, 1099787515295, 1099787516319], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099753892263, 1099753893287, 1099619672519, 1099619673543, 38745744843, 30139174351], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099552562647, 8614086107, 4319121883, 17187171807], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i3 : checks (tilesOf batches) 119 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 119 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 119 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 119 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 119 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 119 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [1968707595, 1951931407, 1951932431, 1952457743, 1935681555, 1935682579], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1935945747, 1919169559, 1516648471, 1516715031, 1499938843, 1499939867], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1500071963, 1483295775, 1483296799, 1483428895, 1466652707, 1869306915], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1869373475, 1852597287, 1852598311, 1852664871, 1835888683, 1835889707], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1752004651, 1735228463, 1735295023, 1735296047, 1802405939, 1802406963], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1802473523, 1785697335, 1718589495, 1718590519, 1483710523, 1483711547], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1483712571, 1466936383, 1466937407, 1399895103, 1383118915, 1383119939], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1299234883, 1282458695, 1099938513275, 1099938514299, 34752772483, 1099854624143], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099854625167, 1099854626191, 1099787444639, 1099787445663, 1099787446687, 1099787447711], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099787514271, 12959381967, 57711059, 1099569339859], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i6 : checks (tilesOf batches) 119 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 119 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 119 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 119 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 119 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 119 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [1885348879, 1868572691, 1868573715, 1868836883, 1852060695, 1852192791], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1852259351, 1835483163, 1835484187, 1802061851, 1785285663, 1785286687], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1785418783, 1768642595, 1768643619, 1768710179, 1751933991, 1751935015], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1684892711, 1668116523, 1668117547, 1668118571, 1651342383, 1802403887], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1802404911, 1785628723, 1785629747, 1785696307, 1785697335, 1735366711], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1617927223, 1601151035, 1567597627, 1567598651, 1450159167, 1450160191], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1265677375, 1248901187, 1248902211, 1349566531, 1316013127, 1099988776303], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099988842863, 1099988843887, 7456128, 1099888181639, 1099888182663, 1099804224923], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099804291483, 1099703559603, 1099703560627, 17338166715, 1099670003131, 1099670004155], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [30155885003, 21566024139, 38712190419, 1099552561623, 8597307871, 4302343647], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i9 : checks (tilesOf batches) 119 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 119 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 119 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 119 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 119 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 119 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1919168531, 1902392343, 1902524439, 1902590999, 1885814811, 1885815835], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1885947931, 1869171743, 1869172767, 1869304863, 1869305891, 1869306915], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1869373475, 1852597287, 1852598311, 1852664871, 1835888683, 1835889707], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1835890731, 1819114543, 1819181103, 1819182127, 1802405939, 1802406963], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1802473523, 1685034039, 1735366711, 1567595575, 1550819387, 1550820411], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1315940411, 1332718655, 1332719679, 1332786239, 1316010051, 1265679427], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1265680451, 1248904263, 1099972066675, 1099972067699, 1099972068723, 1099955218807], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099921665407, 1099921666431, 1099921732991, 1099921734015, 1099720334767, 1099720335791], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099720336815, 91264459, 1099552561623, 38661927391], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i12 : checks (tilesOf batches) 119 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 119 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 119 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 119 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 119 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1550269463, 1533493275, 1533494299, 1533626395, 1516850207, 1516851231], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1516983327, 1500207139, 1500208163, 1500274723, 1483498535, 1483499559], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1483566119, 1466789931, 1466790955, 1466791979, 1701674031, 1701740591], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1701741615, 1684965427, 1752075315, 1752141875, 1752142903, 1752143927], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1651481655, 1500487739, 1500488763, 1500489787, 1383050303, 1383051327], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1383117887, 1181792323, 1181793347, 1181794371, 1165018183, 1100055951711], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100055952735, 1100055953759, 1100055954783, 34719219083, 26129424779, 1099871333771], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099871334795, 1099871401355, 1099770667427, 1099770668451, 1099770669475, 1099636448707], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [12992937415, 4335898071, 24155611, 1099535784411], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i15 : checks (tilesOf batches) 119 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 119 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 119 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 119 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 119 47 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1516849179, 1500072991, 1500074015, 1500206111, 1483429923, 1483430947], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1483497507, 1466721319, 1466722343, 1466788903, 1450012715, 1450013739], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1450014763, 1433238575, 1433305135, 1785627695, 1768851507, 1768852531], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1768919091, 1752142903, 1752143927, 1651481655, 1634705467, 1383048251], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1433380923, 1416604735, 1416605759, 1148236863, 1198569539, 1198570563], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1198571587, 1181795399, 1100106216787, 1100039174499, 1100039175523, 1100039176547], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100039177571, 34736064903, 21851237767, 1099888108935, 1099837778323, 1099837779347], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099837780371, 1099636448707, 1099636449731, 8614086107, 4319121883, 24156635], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i18 : checks (tilesOf batches) 119 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 119 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 119 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 119 42 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (i42)))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [1164661791, 1147885603, 1147886627, 1147953187, 1131176999, 1131178023], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1131244583, 1114468395, 1768780843, 1768781867, 1752005679, 1752072239], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1752073263, 1735297075, 60975647795, 1100391353599, 1100391354623, 1100458464511], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100341090559, 1100458532095, 1100240429311, 1100240430335, 1100122990847, 1100122991871], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100122992895, 1099904890111, 1099904891135, 1099904892159, 1099988779263, 1099988780287], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [30776579383, 1100055885151, 1100055951711, 1100055952735, 1099972067699, 1099972068723], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099837778323, 1099837779347, 1099837780371, 1099720335791, 1099720336815, 108042695], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [17237571027, 8647641555], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i21 : checks (tilesOf batches) 119 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 119 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 119 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 119 45 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [1802264611, 1785488423, 1785489447, 1785556007, 1768779819, 1768780843], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1768781867, 1819114543, 1617854511, 1617855535, 1601079347, 1601080371], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1768919091, 1752142903, 1752143927, 1752144951, 1617928251, 1617929275], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1433380923, 1232055359, 1232056383, 1232122943, 1215346755, 1215347779], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [930136131, 913359943, 1100307611939, 1100307612963, 1100022328679, 1100022329703], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100022330727, 1100022397287, 1100022398311, 1099837778323, 13076824499, 1099653226943], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099653227967, 25827434963, 4319121883, 24156635, 1099535785435], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i24 : checks (tilesOf batches) 119 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 119 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 119 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 119 48 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [1802333223, 1785557035, 1785558059, 1785559083, 1768782895, 1768849455], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1768850479, 1752074291, 1752075315, 1752141875, 1768920119, 1768921143], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1768922167, 1634705467, 1634706491, 1366272059, 1349495871, 1349496895], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1316009023, 1299232835, 1299233859, 1064353859, 1047577671, 1100173394243], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100173395267, 1099938510203, 1099938511227, 1099938512251, 1099904887171, 1099904888195], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099904889219, 1099636449731, 1099636450755, 21515693527, 12925830615, 4302345695], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [7380447], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i27 : checks (tilesOf batches) 119 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 119 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 119 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [1802336299, 1785560111, 1785626671, 1785627695, 1768851507, 1768852531], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1768919091, 1752142903, 1785698359, 1735367735, 1718591547, 1601152059], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1601153083, 1450159167, 1450160191, 1215345727, 1198569539, 1198570563], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1165017155, 1148240967, 1100072730971, 1100072731995, 1100039107939, 1100039174499], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100039175523, 1099804224923, 1099804291483, 1099670005179, 1099670006203, 40934871], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099552563671, 17204017627, 8614088155], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i30 : checks (tilesOf batches) 119 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 119 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 119 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1785627695, 1768851507, 1768852531, 1768919091, 1752142903, 1701812279], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1701813303, 1685037115, 1584374843, 1584375867, 1517268031, 1500491839], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1282454591, 1215346755, 1215347779, 1282457667, 1265681479, 1100022397287], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100022398311, 1099971999091, 1099955290487, 1099955291511, 7451044, 1099737116075], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099737182635, 1099686782391, 1099686783415, 4369455567, 74490319, 12909053403], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4319122907], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i33 : checks (tilesOf batches) 119 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 119 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 119 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1735364659, 1718588471, 1718589495, 1785699383, 1768923195, 1701815355], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1500489787, 1483713599, 1483714623, 1232122943, 1215346755, 1215347779], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1282457667, 1265681479, 1100022330727, 1100022397287, 1100022398311, 1099955290487], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099955291511, 1099770669475, 1099770670499, 1099770737059, 8647643603, 1099569341907], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 119 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 119 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 8 where
  orders := orders
  covers := by
    intro a ha box
    change 13+a.b≤132 ∧ 6+a.j≤55 ∧ 2+a.t≤14 at box
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
end Low6961Allocation.Group8
