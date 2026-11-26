import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass7
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group7
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2248215557, 1040257033, 5318579209, 19110435853, 48622612497, 87026589729], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [44396098621, 35553744129, 35469857029, 35353026865, 35135063345, 34967365937], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [43707939165, 17418472857, 13240936901, 8895642053, 13039617477, 1099817407959], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817408983, 1099817410007, 25957991917, 17351352813, 4432971245, 1099716742639], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099716743663, 34413482513, 4349082129, 54116881, 54117905, 1099565746707], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [42986715669, 12905390617, 21478475293, 17183579677, 4298682909], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i3 : checks (tilesOf batches) 135 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 135 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 135 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 135 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 135 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 135 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 135 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10704590859, 27617010701, 74057334809, 86976530481, 1681448013, 39748452629], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35336251669, 30789766453, 30622068021, 17770794293, 13173829053, 8828534205], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8778271165, 1099884516807, 1099884517831, 43305346505, 1099767078371, 21679803877], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13073163749, 1099716741615, 1099716742639, 1099716743663, 4382637561, 1099666408955], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [30185843201, 21595916801, 38758783493, 4382569989, 54115857, 1099565744659], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8627201557, 4332237333, 12905390617, 38658265629, 3783197], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i6 : checks (tilesOf batches) 135 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 135 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 135 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 135 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 135 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 135 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 135 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27617010701, 61340205081, 86926130221, 14415286345, 30907137317, 34950585637], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30571807013, 39597523261, 30957398333, 13089948065, 13274422709, 13157051829], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8811756981, 1099934847419, 1099934848443, 1099934849467, 1099934850491, 43305346505], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817404887, 1099817405911, 1099716673007, 1099716739567, 1099716740591, 17368058353], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4449676793, 4382569977, 54048273, 54114833, 30101957141, 8627199509], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4332235285], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i9 : checks (tilesOf batches) 135 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 135 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 135 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 135 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 135 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 135 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40234004497, 82580559905, 57029339193, 35436845325, 35168550157, 34984141069], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21797324121, 1100337503579, 43523453325, 13257646501, 13157052837, 8794980773], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100001955243, 1100001956267, 1100001957291, 1100001958315, 21797240273, 13207311825], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800560091, 1099800626651, 1099800627675, 4449677801, 1099733449195, 1099733450219], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8677533185, 34413633041, 54047249, 1099565676051, 42969936409, 4315457049], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [20491801], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i12 : checks (tilesOf batches) 135 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 135 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 135 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 135 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 135 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 135 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44562922517, 86825330725, 35655236673, 31158724869, 35118287109, 34917035269], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13073174905, 13257715085, 13123501453, 1100119330191, 39211777433, 30621918617], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100001956267, 1100001957291, 1100001958315, 1099968404907, 17586162109, 8996232637], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8895637949, 1099867667915, 1099867668939, 1099867669963, 1099867736523, 1099733448171], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099733449195, 4382566921, 87601673, 17250616845, 56856, 56860], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 135 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 135 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 135 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 135 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 135 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 135 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48757426201, 86808688681, 18559257669, 35202103557, 34950520069, 30571806981], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8895644033, 39295666565, 26410905989, 1100102552979, 1100102619539, 1100102620563], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100069067155, 1100035513747, 13324754325, 13207383445, 8845311381, 1099850959311], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17451945425, 1099817336279, 1099817337303, 1099817403863, 4466453989, 1099750225383], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099750226407, 8677532161, 54046225, 1099565675027, 56848, 17217130005], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56852, 4315456025, 20490777, 55832, 56856, 55836], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56860], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i18 : checks (tilesOf batches) 135 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 135 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 135 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 135 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 135 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57163011101, 86741650481, 35084733693, 30638846205, 13526159613, 35168474461], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26511571293, 13190607241, 8828535177, 1100136107403, 1100069065115, 1100052288923], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018735515, 1099968404891, 13324752301, 8979522989, 1099884446151, 1099884447175], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099884513735, 4466454997, 1099817335255, 1099817336279, 1099632783875, 1099632784899], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56840, 4365788685, 70823437, 56844, 21528803857, 12938940945], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56848, 55828, 56852, 4315456025, 55832, 56856], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54812, 55836, 56860], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i21 : checks (tilesOf batches) 135 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 135 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 135 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 135 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 135 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61357449249, 69662514229, 26427759897, 30454298905, 4869118233, 30957396297], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26494796105, 13173832057, 8811759993, 1100169729403, 1099951626663, 1099901296039], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968334259, 1099968400819, 1099968401843, 8979455417, 8862083513, 4533564857], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099901222339, 1099901223363, 1099901224387, 1099683116535, 1099683117559, 21612691961], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8744638969, 4399344125, 1099649561087, 56836, 56840, 56844], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55824, 56848, 55828, 56852, 4315457049, 20491801], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54808, 55832, 56856, 17183506973, 12888610333, 54812], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55836, 56860], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i24 : checks (tilesOf batches) 135 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 135 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 135 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 135 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [74007538725, 44060554301, 31058062613, 30772989205, 30538181909, 13207391561], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100270394699, 13224160649, 8845311369, 1100136106379, 1100068998555, 1100069065115], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018734491, 1099985181083, 17519054273, 8929190337, 1099867667915, 1099867668939], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867669963, 4466453981, 1099783779807, 1099783780831, 56832, 30169067013], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56836, 87600649, 1099599229451, 56840, 55820, 56844], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55824, 56848, 17217130005, 4332233237, 37267989, 54804], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55828, 56852, 54808, 55832, 56856, 54812], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55836, 56860], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i27 : checks (tilesOf batches) 135 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 135 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 135 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 135 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69763037225, 35537796161, 30890359077, 26377361701, 26176107813, 8845316445], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100169731423, 13140276617, 1100136105355, 1100136106379, 1100136107403, 1100035510687], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100001957279, 1099951626655, 13224090041, 8862083513, 1099867665867, 1099867666891], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867667915, 1099867668939, 25957988845, 13089936877, 4399344125, 1099649561087], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56828, 56832, 56836, 55816, 56840, 4365788685], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55820, 56844, 55824, 56848, 54804, 55828], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56852, 20491801, 54808, 55832, 56856, 21478472221], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [12888609309, 53788, 54812, 55836, 56860], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i30 : checks (tilesOf batches) 135 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 135 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 135 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 135 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [86708093997, 5707978825, 35168552177, 30705953009, 22032206065, 1100203215227], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100186439035, 1100136108411, 1100136174971, 13240936845, 8862087565, 1100119328143], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951626655, 1099901296031, 21881128373, 9013009845, 1099834112467, 1099834113491], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834114515, 4500007397, 1099750224359, 1099750225383, 56828, 56832], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56836, 55816, 56840, 55820, 56844, 1099548971539], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54800, 55824, 56848, 54804, 55828, 56852], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [17200285209, 8610421273, 20490777, 20491801, 54808, 55832], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56856, 4298679837, 1099515416095, 53788, 54812, 55836], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56860], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i33 : checks (tilesOf batches) 135 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 135 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 135 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [78151716913, 1413012557, 30840099069, 30588514557, 13459050749, 13224161661], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8845312381, 1100169661823, 1100119396747, 1100069066123, 1100018735499, 1099884518819], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17535832505, 8929191353, 1099918000575, 1099918001599, 1099918068159, 4483232209], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834112467, 1099834113491, 56828, 1099632783875, 1099632784899, 56832], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55812, 56836, 55816, 56840, 4365788685, 70823437], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55820, 56844, 12938940945, 8627200529, 54800, 55824], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56848, 54804, 55828, 56852, 54808, 55832], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [56856, 4298678813, 1099515416095, 53788, 54812, 55836], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56860], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i36 : checks (tilesOf batches) 135 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 135 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 135 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69612182581, 26461248781, 26243217677, 9130530061, 8929196417, 1100169659779], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100169660803, 1100169661827, 1100102553987, 1100035511699, 1099985181075, 1099951627667], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [9029787061, 8895637941, 4550342069, 1099817336279, 1099817337303, 1099683116535], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099683117559, 56828, 4399344129, 1099632783875, 56832, 55812], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56836, 55816, 56840, 55820, 56844, 1099548971539], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54800, 55824, 56848, 54804, 55828, 56852], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54808, 55832, 56856, 3713565, 3714589, 53788], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54812, 55836, 56860], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i39 : checks (tilesOf batches) 135 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 135 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 135 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [56828012601, 22048909609, 21864431913, 4751677737, 8811757961, 1100136107403], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100119396747, 1100069066123, 1099951626651, 1099918073243, 8912415157, 4567119285], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951553975, 1099901223363, 1099901224387, 1099901290947, 1099666339323, 1099666340347], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [56828, 56832, 4399344133, 87601669, 55812, 56836], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55816, 56840, 55820, 56844, 54800, 55824], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56848, 54804, 55828, 56852, 54808, 55832], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56856, 45596, 53788, 54812, 55836, 56860], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i42 : checks (tilesOf batches) 135 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 135 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 7 where
  orders := orders
  covers := by
    intro a ha box
    change 7+a.b≤142 ∧ 3+a.j≤58 ∧ 1+a.t≤15 at box
    have pos := ha.1
    have cases : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 ∨ a.t=13 ∨ a.t=14 := by omega
    rcases cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
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
    · exact Top14.exact a ha h14 (by omega) (by omega)
end Low6966Allocation.Group7
