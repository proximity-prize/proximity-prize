import ProximityPrize.SubmissionLower.R6961Low6961AllocTiles
import ProximityPrize.SubmissionLower.R6961Low6961Mass3

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6961Allocation.Group3
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2164329477, 5620568075, 23271381001, 1294610451, 1328165911, 1328166935], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1328495639, 1311719451, 1311851547, 1311918107, 1295141919, 1295142943], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1295340575, 1278629923, 1278630947, 1278697507, 1261921319, 87094224933], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [18962299969, 1099565852999, 1099565854023, 1099565855047, 1099565856071, 1099565857095], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099565858119, 1099565924679, 1099565925703, 1100337678663, 1100337679687, 1100136419655], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100136420679, 1100136421703, 1100136422727, 1100136423751, 1100136424775, 1100136425799], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1100136426823, 1100136493383, 1100136494407, 22150035781, 35168391497, 43708265813], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [39413506389, 25958388189, 17368526301, 8711553517, 121621997], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
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
private theorem i51 : checks (tilesOf batches) 130 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [1796544523, 1779768335, 1779769359, 1780687887, 1763911699, 1763912723], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1529491475, 1512715287, 1512716311, 1513045015, 1496268827, 1496400923], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1496467483, 1479691295, 1479692319, 1479889951, 1463179299, 1463180323], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [87027048481, 1765651519, 1866315843, 1866316865, 1648214083, 1631437895], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1631438919, 1631505479, 39530946865, 1100253792563, 1100253793587, 1100253794611], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1100253795635, 1100253862195, 1100253863219, 1100253864243, 1100253865267, 1100253866291], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [34917428529, 43523780993, 39228956033, 38993861049, 1099683507643, 1099683508667], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [8812216781, 255839693, 25924831717, 17334969829, 8627665409, 25790612997], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [4315923973], by decide +kernel⟩
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
private theorem i46 : checks (tilesOf batches) 130 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [32080339981, 1966162971, 1966229531, 1949453343, 2033340447, 2033538079], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2016827427, 2016828451, 2016895011, 2000118823, 2000185383, 2000186407], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1966633003, 1966699563, 1966700587, 1949924399, 1949990959, 78454096941], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [30806934849, 30605681985, 9281914177, 17418855877, 8828926405, 4383032809], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099650026987, 43054081521, 1099549214199, 1099549215223, 1099549216247, 1099549217271], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [21562824181, 34397319681, 8627596801, 4332698113, 4315922945, 1099549362691], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [38675370501, 4178441, 4179465], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
private theorem i49 : checks (tilesOf batches) 130 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40469409809, 74175633441, 1950130235, 1950131259, 1950132281, 1933356093], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1916645437, 1916646461, 1899870273, 1866316865, 1866317889, 1815987269], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1312671815, 1312738375, 39480547641, 30840488249, 17670447489, 17536300417], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4718512513, 43238633925, 1099650025963, 1099650026987, 25857720821, 1099599617527], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532584443, 38692216321, 4315921921, 1099549361667, 4299076105, 4299143689], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4178441], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i12 : checks (tilesOf batches) 130 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 130 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 130 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1764703255, 1747927067, 1748059163, 1748125723, 1731349535, 1731350559], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1731548191, 1714837539, 1714838563, 1714905123, 1698128935, 1983408167], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1983409191, 1966633003, 1966699563, 1966700587, 1949924399, 1949990959], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1949991983, 1933215795, 1094421555, 1094422579, 1077646391, 1077647415], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1077713975, 1060937787, 1060938811, 1060939835, 1044163647, 31545208893], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [26511969593, 30538574137, 1099801020835, 1099801021859, 13207775661, 8845703597], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [8778663341, 43272256957, 1099700356575, 1099650025963, 1099650026987, 21596311021], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [12989670893, 1099566070255, 1099599691247, 1099633246703, 4349408765, 34397252097], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [20954629, 8594040329, 4299076105], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i15 : checks (tilesOf batches) 130 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 130 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 130 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1412581403, 1395805215, 1395806239, 1396003871, 1379293219, 1379294243], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1379360803, 1362584615, 1362651175, 1362652199, 1345876011, 1345942571], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1345943595, 1329167407, 82581291053, 30941151513, 34917425433, 1100304270619], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100304271643, 1100270718235, 43557407085, 30723044717, 1099817722275, 1099817723299], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099868055971, 1099868056995, 1099868058019, 8912811425, 1099733844387, 1099750690259], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099717132763, 1099717133787, 1099717134811, 17301411309, 1099599623667, 1099599624691], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [104840689, 8661150201, 42987112961, 4109833, 4176393], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i18 : checks (tilesOf batches) 130 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 130 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 130 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 130 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 130 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [1429558303, 1412847651, 1412848675, 1412915235, 1396139047, 1396205607], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1396206631, 1379430443, 1379497003, 1379498027, 1362721839, 1362788399], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1362789423, 1346013235, 1346079795, 1346080819, 1329304631, 1715181623], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1715248183, 1698471995, 1698473019, 1698474043, 1027386431, 1027452991], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1027454015, 1010677827, 1010678851, 1010679875, 993903687, 993904711], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [993971271, 22032526645, 9198028085, 39279285621, 26394525045, 8862477757], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4533959101, 4450075069, 1099784243659, 1099784244683, 17402075601, 1099666801127], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099666802151, 71219705, 71286265, 4332629505, 37664257, 12889004553], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [8594041353], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i21 : checks (tilesOf batches) 130 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 130 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 130 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 130 45 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [1245143075, 1228366887, 1228433447, 1228434471, 1211658283, 1211724843], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1211725867, 1194949679, 1195016239, 1933214767, 1916438579, 1916505139], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1916506163, 1899729975, 1899730999, 1899797559, 48473350201, 35152093517], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099985428835, 1099985429859, 1099985430883, 1099985431907, 1099985498467, 1099985499491], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17536301409, 1100220452195, 4533959097, 1099851284923, 1099851351483, 1099851352507], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [13090333141, 4517179861, 87996917, 1099599691255, 21529200125, 12939337213], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4299075081], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i24 : checks (tilesOf batches) 130 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 130 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 130 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 130 48 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [1010330663, 993554475, 993621035, 993622059, 976845871, 976912431], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [976913455, 960137267, 960203827, 1681625139, 1664848951, 1664849975], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1664916535, 1648140347, 1648141371, 1648142395, 1631366207, 1933422653], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1832760381, 1866315841, 1480440899, 1480441923, 1463665735, 1463666757], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1446956101, 35269537049, 1099952016803, 8778595749, 1099935238567, 17469116869], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [13107111365, 1099733843415, 1099733909975, 1099733910999, 30152617461, 17267789301], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [87995893, 8644371965, 1099549358595], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 130 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [1949923371, 1933147183, 1933213743, 1933214767, 1916438579, 1916505139], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1916506163, 1899729975, 1715181623, 1715248183, 1698471995, 1698473019], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1950132281, 1883024445, 1883091005, 1883092029, 1866315841, 18660310081], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099532516775, 1099750621607, 1099750688167, 1099532585383, 1099935239591, 8828925357], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099901684143, 17402075601, 1099683578339, 1099683579363, 1099650022891, 30119131645], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4332629505, 37664257, 1099549358595, 12889004553], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [1983546415, 1966770227, 1966836787, 1966837811, 1950061623, 1950062647], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1950129207, 1933353019, 1933354041, 1933355065, 1933356093, 1883091005], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1564324927, 1547548739, 1547549763, 1564328001, 1547551813, 1547552837], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1648282693, 8795370933, 1099851284923, 1099851351483, 1099851352507, 4181456], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099733913047, 4382963177, 1099650022891, 4332630529, 37730817, 21478868489], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [12889005577], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [1060868147, 1044091959, 1044092983, 1044159543, 1027383355, 1027384379], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1027385403, 1010609215, 1010675775, 1010676799, 1732098113, 1732099137], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1732100161, 977126471, 977127495, 977194055, 26478416177, 22015749425], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [9181250865, 8896032181, 1099817797059, 1099817798083, 1099817799107, 17368453597], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8778589661, 171882977, 1099683577315, 1099683578339, 4332630529], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [52717984821, 591240531, 591241555, 591242579, 1100102871379, 1100253867347], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100253933907, 1100253934931, 1100253935955, 1100287491411, 1100153274707, 1099968726355], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4785621329, 1099817797059, 1099784243659, 1099784244683, 13056777697, 1099633246703], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4315852293, 20887045, 20953605], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤130) (hj : a.j≤51) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 3 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤132 ∧ 4+a.j≤55 ∧ 1+a.t≤14 at box
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
end Low6961Allocation.Group3
