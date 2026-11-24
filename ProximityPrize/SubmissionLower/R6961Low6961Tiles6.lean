import ProximityPrize.SubmissionLower.R6961Low6961AllocTiles
import ProximityPrize.SubmissionLower.R6961Low6961Mass6

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6961Allocation.Group6
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2148928519, 2132152331, 2132153355, 2133792779, 2117016591, 2117476367], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2117673999, 2100897811, 2100898835, 2067738643, 2051027991, 2051029015], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2051161111, 943931419, 943997979, 944064539, 927288351, 927289375], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [927421471, 910645283, 910711843, 910712867, 1934124071, 1934190631], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1934191655, 1917481003, 1917482027, 1917483051, 1900706863, 1900773423], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1548452911, 1531676723, 1531743283, 1531744307, 52836471863, 35488481535], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099718038895, 1099718039919, 1099718040943, 1099718041967, 1100154250607, 1100036876655], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1100036877679, 1100036878703, 1099869107567, 1099869108591, 1099869109615, 1099919442287], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099919443311, 17604380067, 13208754595, 1099801998791, 1099801999815, 1099802000839], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099751670227, 1099751671251, 122595823, 1099634224623, 1099634225647, 8695749107], by decide +kernel⟩
private def p10 : P :=
  ⟨unpack [25858696695, 17268834807, 38693122563, 34364460555, 8595084811, 5154315], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
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
private theorem i43 : checks (tilesOf batches) 130 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [27920373771, 2101359639, 2101360663, 2101492759, 2084782107, 2084848667], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2084915227, 2068139039, 2068140063, 2068272159, 2051495971, 1967676451], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1967677475, 1950901287, 1950967847, 1950968871, 1934258219, 1934259243], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1934260267, 1917484079, 1917550639, 1917551663, 1900775475, 1951173683], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1951174707, 1934398519, 1951176759, 1951177783, 1900847163, 1850582075], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1850583099, 1397599295, 1397600319, 1397601343, 1565374531, 1565375555], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1565376579, 1364116551, 8846749071, 1100036883855, 1099852331451, 1099852332475], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099852333499, 1099768442319, 1099768443343, 1099768444367, 1099600668151, 1099600669175], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [25841917435, 17252055547, 1099533558275, 8611794439, 4300118539, 5153291], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
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
private theorem i46 : checks (tilesOf batches) 130 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [32199222287, 2068071451, 2068138011, 2051361823, 2051362847, 2051494943], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2034718755, 2034785315, 2034786339, 2018010151, 1296656423, 1296657447], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1279946795, 1279947819, 1279948843, 1263172655, 1598783535, 1598784559], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1582008371, 1582074931, 1900843059, 1884066871, 1934399543, 1800182839], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1783406651, 1682809915, 1682810939, 1666034751, 1565372479, 1565373503], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1548597315, 793623619, 793624643, 776913991, 13494040835, 22201198943], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100003327383, 1100003328407, 1100003329431, 13275857327, 1099869106615, 1099869107639], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099869108663, 1099768440271, 1099768441295, 1099768442319, 156147175, 1099667775975], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4367159803, 21928455, 34364671499], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
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
private theorem i49 : checks (tilesOf batches) 130 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1967075347, 1950364695, 1950365719, 1950497815, 1933787163, 1933853723], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1933920283, 1917144095, 1917145119, 843535391, 826759203, 826825763], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [826826787, 810050599, 810117159, 810118183, 793407531, 2001368107], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [2001369131, 1984592943, 1984659503, 1984660527, 1967884339, 1967950899], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1984729139, 1900844087, 1900845111, 1800182839, 1783406651, 35539231803], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [31176873195, 1099902592343, 1099835550039, 1099835551063, 1099835552087, 1099835553111], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099533564247, 1100271762775, 1100271763799, 1100271764823, 1100238207327, 1099936213415], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099936214439, 1099936215463, 1099936216487, 1099869103543, 1099667774951, 1099667775975], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [38793720299, 25858628087, 55416319, 55482879, 17184945675, 4300048907], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i12 : checks (tilesOf batches) 130 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 130 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 130 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1564621847, 1547911195, 1547977755, 1548044315, 1531268127, 1531269151], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1531401247, 1514625059, 1514691619, 2051563555, 2034787367, 2034853927], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [2034854951, 2018144299, 2018145323, 1967814699, 1800043567, 1800110127], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1800111151, 1783334963, 1884064819, 1884065843, 1867289655, 1884067895], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1498192951, 1598857275, 1598923835, 1598924859, 1263381567, 1263382591], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1263383615, 1246607427, 1229831235, 1229832259, 1213121607, 1100187876715], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100187877739, 1100187878763, 1100171095407, 1100171096431, 1100171097455, 1100171098479], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [34884631951, 8829900191, 1099852325307, 1099852326331, 1099852327355, 1099718106587], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [13074529759, 4383935991, 88970743, 1099583887867, 12923533827], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i15 : checks (tilesOf batches) 130 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 130 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 130 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1531267099, 1514490911, 1514491935, 1514624031, 1497847843, 1497914403], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1497915427, 1481139239, 1481205799, 1481206823, 1464496171, 86625645609], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100237993179, 1100237994203, 1100237995227, 1100338659547, 1100338726107, 1100338727131], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100338728155, 1100691050715, 1100741448923, 1100624009435, 1100456238299, 1100456239323], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100087141595, 1100087142619, 1100087143643, 1100087144667, 17755452633, 8846681447], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100204650855, 1100204651879, 1100204652903, 1100204653927, 1100204654951, 1100204655975], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [30606444939, 21983095179, 13225460131, 1099936212391, 1099936213415, 1099936214439], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099835481535, 1099835548095, 1099667708391, 8678900215, 4383935991, 38639107], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [21496621575], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i18 : checks (tilesOf batches) 130 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 130 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 130 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 130 42 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (i42)))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [2068272159, 2051495971, 2051562531, 2051563555, 2034787367, 2034853927], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2034854951, 2018144299, 1951036459, 1951037483, 1934261295, 1934327855], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1934328879, 1917552691, 61023751217, 22050278667, 1100137473291, 1100137474315], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100137475339, 1099902595339, 1099902661899, 1099902662923, 9014525193, 1100187873643], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100187874667, 1100187875691, 1100154322291, 1100154323315, 1100154324339, 1099936140695], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099952918935, 1099885811095, 1099885812119, 4534934935, 1099952989603, 1099952990627], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099952991651, 1099751661011, 1099751662035, 105747955, 1099617442291, 12940244477], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [8645346815, 38638083], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i21 : checks (tilesOf batches) 130 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 130 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 130 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 130 45 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [1984454691, 1967678503, 1967745063, 1967746087, 1951035435, 1951036459], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1951037483, 1833597999, 1833664559, 1833665583, 1816889395, 1816955955], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1816956979, 1917621303, 48205961269, 1100322019615, 1100322020639, 1100087140639], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099986478367, 1099986479391, 1099818708255, 1099818709279, 1099818775839, 1099818776863], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099818777887, 1100506644767, 1100506645791, 1100187872619, 1100187873643, 1100187874667], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100187875691, 1100187876715, 1100020098451, 1100020099475, 1099919434155, 1099684485603], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099684552163, 13040975335, 4451044839, 25825141247, 38639107], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i24 : checks (tilesOf batches) 130 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 130 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 130 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 130 48 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [2018077735, 2001367083, 2001368107, 2001369131, 1984592943, 1984659503], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [843809839, 1766557747, 1766624307, 1951174707, 1850512439, 1850513463], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1514970167, 1531748411, 1531814971, 1531815995, 1196272703, 1196273727], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1196274751, 1179498563, 1129167939, 1129168963, 1112458311, 26697493755], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100288539987, 1100288541011, 1100288542035, 1100238204255, 1100238205279, 1100238206303], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100238207327, 1099952922019, 1099919434155, 1099919435179, 1099919436203, 8796341723], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [105747955, 1099617442291, 21860869, 17184878089, 8595014153], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [1766488107, 1749711919, 1749778479, 1749779503, 1733003315, 1733069875], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1733070899, 1800180791, 1800181815, 1733073975, 1716297787, 1431151675], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [877504571, 860728383, 860729407, 860730431, 843954243, 1162722371], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1162723395, 1146012743, 17570834701, 1100254985563, 1100254986587, 1100254987611], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100171094383, 1100171095407, 1100171096431, 1100171097455, 1100171098479, 1100020098451], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [13124794835, 8796342739, 1099734883799, 1099734884823, 156079591, 1099667708391], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4316826117, 21860869], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1917551663, 1900775475, 1900842035, 1967951923, 1582076983, 1582078007], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1615633463, 1598857275, 1598923835, 1246603323, 1229827135, 1229828159], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1229829183, 1213052995, 1213054019, 1213055043, 1297007685, 1100204648807], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100204649831, 1100204650855, 1100204651879, 1100204652903, 1100204653927, 1100204654951], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100103992703, 4568487347, 1099852258747, 1099852325307, 1099852326331, 88970743], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [89037303, 8662124027, 5083657], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1984729139, 1967952951, 1464637495, 1749851191, 1733075003, 1447928891], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1296934971, 1280158783, 1280159807, 1280160831, 1263384643, 827178051], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [827179075, 810468423, 8997747977, 1100171099503, 1100171100527, 1100171101551], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100154317171, 1100154318195, 1100154319219, 1100154320243, 1100154321267, 8930562455], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1100003321239, 1099718106587, 1099718107611, 139368939], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤130) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 6 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤132 ∧ 6+a.j≤55 ∧ 2+a.t≤14 at box
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
end Low6961Allocation.Group6
