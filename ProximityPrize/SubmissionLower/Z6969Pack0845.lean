import ProximityPrize.SubmissionLower.Z6969Pack0840
import ProximityPrize.SubmissionLower.Z6969Pack0844

set_option Elab.async false

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles7
section Z6969Source2333
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group7
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2248215557, 1040257033, 5318579209, 19110435853, 48622612497, 87026589729], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [44396098621, 35553744129, 35469857029, 35336249649, 35135063345, 39195224369], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [43707939165, 13173903769, 17519126965, 13157055925, 13090016693, 1099767078371], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4399418857, 1099733521899, 1099733522923, 25957991917, 17351352813, 4449746425], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4382639609, 1099616079367, 1099616080391, 4382569993, 34413482513, 54117905], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099565746707, 42986715669, 12905390617, 4315460121, 34363368989, 21478541853], by decide +kernel⟩
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
    Covered orders a ∨ Low6969Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10704590859, 27617010701, 74057334809, 86976530481, 1681448013, 39748452629], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35336251669, 30789766453, 30622068021, 17770794293, 13173829053, 8828534205], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8778271165, 1099884516807, 1099884517831, 43305346505, 1099767078371, 17418391013], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13106717157, 1099716741615, 1099716742639, 1099716743663, 4382637561, 1099666408955], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [30185843201, 21595916801, 38758783493, 4399346181, 104380933, 54115857], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099565744659, 38658265629, 8593646109, 4298681885], by decide +kernel⟩
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
    Covered orders a ∨ Low6969Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27617010701, 52934819865, 86909285417, 22954887237, 35202102557, 39211931933], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30588584221, 39413039465, 30823246185, 13106725277, 17586166181, 13224160677], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13106724261, 8744718761, 1100001959339, 43305346505, 1099834184147, 1099834185171], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834186195, 1099817405911, 1099783781855, 1099783782879, 1099783849439, 1099783850463], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17401612777, 4449676793, 4382569977, 12955721225, 54048273, 54114833], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8593645085, 4298680861], by decide +kernel⟩
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
    Covered orders a ∨ Low6969Gate.Gated ((7 : Band).val) a :=
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
    Covered orders a ∨ Low6969Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [40418950165, 78302438437, 48439406653, 31141946645, 30840030485, 39128114453], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17452027229, 17519060361, 13173832073, 8828537225, 1100035511715, 1100035512739], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100001959331, 39060782525, 1099884513735, 1099884514759, 1099884515783, 21746910673], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13140270545, 1099834112467, 1099834113491, 1099834114515, 1099834181075, 4516785629], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099783779807, 8643976721, 4332235281, 17217062421, 8627198485, 37270037], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [30085178905, 56856, 3713565, 3714589, 56860], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
    Covered orders a ∨ Low6969Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [52934952985, 86791912493, 14281068617, 30957468933, 34950520069, 30571806981], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39379487081, 26511503721, 8895644033, 1100169661827, 13324754325, 13190606229], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8845311381, 1100069065115, 1100069066139, 1100035512731, 1100001959323, 1099850959311], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817336279, 1099817337303, 1099817403863, 17401613789, 4483231201, 1099767002595], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099767003619, 8677532161, 54046225, 1099565675027, 56848, 17217130005], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56852, 38675040793, 4315456025, 20490777, 55832, 56856], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [25773437469, 55836, 56860], by decide +kernel⟩
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
    Covered orders a ∨ Low6969Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57163011101, 86741650481, 35084733693, 30638846205, 13526159613, 35168474461], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26494794077, 13190607241, 8828535177, 1100136107403, 1100069065115, 1100052288923], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018735515, 1099968404891, 13324752301, 8962745773, 1099884446151, 1099884447175], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099884513735, 4466454997, 1099817335255, 1099817336279, 1099632783875, 1099632784899], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4382565897, 87600649, 56840, 21545581069, 12955718157, 56844], by decide +kernel⟩
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
    Covered orders a ∨ Low6969Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61357449249, 69662514229, 26427759897, 30454298905, 4869118233, 30957396297], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26494796105, 13173832057, 8811759993, 1100169729403, 1099934849447, 1099901296039], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968334259, 1099968400819, 1099968401843, 8979455417, 8862083513, 4533564857], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099901222339, 1099901223363, 1099901224387, 1099683116535, 1099683117559, 21612691961], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8744638969, 4382566909, 1099649561087, 56836, 56840, 55820], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56844, 55824, 56848, 37267989, 37269013, 55828], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56852, 4315457049, 54808, 55832, 56856, 17183506973], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [12888610333, 54812, 55836, 56860], by decide +kernel⟩
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
    Covered orders a ∨ Low6969Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [74007538725, 44060554301, 31058062613, 26561907989, 26343876885, 17485579593], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100270328139, 1100270394699, 1100085773719, 1100085774743, 1100085775767, 1100085842327], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035511703, 8962746785, 8828532129, 1100035441059, 17435168213, 8845304277], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783779807, 1099783780831, 1099783781855, 137932285, 1099649561087, 1099548973571], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56832, 30169067013, 56836, 56840, 55820, 56844], by decide +kernel⟩
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
    Covered orders a ∨ Low6969Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69763037225, 35537796161, 30890359077, 26377361701, 26176107813, 8845316445], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100169731423, 8929195401, 8794980745, 1100119330187, 1100035510687, 1100001957279], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951626655, 13224090041, 8862083513, 1099918000575, 1099918001599, 1099918068159], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783779807, 1099783780831, 1099783781855, 25957988845, 13089936877, 4399344125], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099649561087, 56828, 56832, 56836, 55816, 56840], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4365788685, 55820, 56844, 55824, 56848, 54804], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55828, 56852, 20491801, 54808, 55832, 56856], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [21478472221, 12888609309, 1099515416095, 53788, 54812, 55836], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56860], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
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
    Covered orders a ∨ Low6969Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [86708093997, 5707978825, 35168552177, 30705953009, 22032206065, 1100203215227], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100186439035, 1100136108411, 1100136174971, 13240936845, 8862087565, 1100119328143], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934849439, 1099901296031, 21881128373, 9013009845, 1099834112467, 1099834113491], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834114515, 4500007397, 1099750224359, 1099750225383, 56828, 56832], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55812, 56836, 55816, 56840, 55820, 56844], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099548971539, 54800, 55824, 56848, 54804, 55828], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56852, 17200285209, 8610421273, 20490777, 20491801, 54808], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55832, 56856, 4298679837, 1099515416095, 53788, 54812], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55836, 56860], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i33 : checks (tilesOf batches) 135 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 135 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 135 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [78151716913, 1413012557, 30840099069, 30588514557, 13459050749, 13224161661], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8845312381, 1100169661823, 1100119396747, 1100069066123, 1100018735499, 1099884518819], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17519055289, 8929191353, 1099918000575, 1099918001599, 1099918068159, 4483232209], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834112467, 1099834113491, 56828, 1099632783875, 1099632784899, 56832], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55812, 56836, 55816, 56840, 12955718157, 8643977741], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [70823437, 55820, 56844, 54800, 55824, 56848], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54804, 55828, 56852, 54808, 55832, 56856], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4298678813, 3713565, 1099515416095, 53788, 54812, 55836], by decide +kernel⟩
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
    Covered orders a ∨ Low6969Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69612182581, 26461248781, 22015359245, 13391941901, 1100119396747, 1100069066123], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100018735499, 1099968404875, 8862087569, 1100102550931, 1100102551955, 1100085775763], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [9029787061, 8895637941, 4550342069, 1099817336279, 1099817337303, 1099683116535], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099683117559, 56824, 56828, 4399344129, 1099632783875, 56832], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55812, 56836, 55816, 56840, 55820, 56844], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54800, 55824, 56848, 54804, 55828, 56852], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54808, 55832, 56856, 3713565, 3714589, 1099515416095], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [53788, 54812, 55836, 56860], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i39 : checks (tilesOf batches) 135 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 135 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 135 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [56828012601, 22048909609, 21864431913, 4751677737, 8811757961, 1100136107403], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100119396747, 1100069066123, 1099951626651, 1099901296027, 8912415157, 4567119285], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951553975, 1099901223363, 1099901224387, 1099901290947, 1099666339323, 1099666340347], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [56824, 56828, 56832, 4382566917, 87601669, 55812], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56836, 55816, 56840, 55820, 56844, 54800], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55824, 56848, 54804, 55828, 56852, 54808], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55832, 56856, 3713565, 3714589, 45596, 53788], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [54812, 55836, 56860], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i42 : checks (tilesOf batches) 135 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 135 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤135) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((7 : Band).val) a :=
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
end Low6969Allocation.Group7
end Z6969Source2333

-- Source: ProximityPrize.SubmissionLower.Low6969Mass8
section Z6969Source2334
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group8

private def m0 : MassCell 8 :=
  ⟨⟨2,5,4⟩,mass_cell 8 2 5 4 209 (by decide)
    (by decide +kernel) [4520739782911, 3682715309684, 2955464290676, 2338303340148, 1820095769972, 1390242811508, 1038683615604, 755895252596, 532892712308, 361228904052, 232994656628, 140818718324, 77867756916, 37846359668, 14997033332, 4100204148, 474217844, 1822130] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 8 :=
  ⟨⟨2,6,12⟩,mass_cell 8 2 6 12 194 (by decide)
    (by decide +kernel) [4670444258785, 3926187704040, 3092392678092, 2393942504568, 1816330340076, 1345759818792, 969145052460, 674110630392, 448991619468, 282833564136, 165392486412, 87134885880, 39237739692, 13588502568, 2785106796, 135996158, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 8 :=
  ⟨⟨3,7,19⟩,mass_cell 8 3 7 19 183 (by decide)
    (by decide +kernel) [4674497865666, 4170599096342, 3273924170640, 2474857972064, 1826085129008, 1308827119872, 905369871056, 599063756960, 374323599984, 216628670528, 112522686992, 49613815776, 16574671280, 3142315904, 118822480, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 8 :=
  ⟨⟨2,9,27⟩,mass_cell 8 2 9 27 163 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3601438537103, 2630986651322, 1856595109418, 1257250879898, 807657701642, 483809258618, 262989179882, 123771039578, 46018356938, 10884596282, 813167018, 2495] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 8 :=
  ⟨⟨4,10,31⟩,mass_cell 8 4 10 31 156 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3758698566390, 2743976526938, 1880550747022, 1228789758730, 754520561486, 425772075994, 212775144238, 87962529482, 25968916270, 3630910426, 39218794] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 8 :=
  ⟨⟨1,12,35⟩,mass_cell 8 1 12 35 144 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3861401558706, 2912657432512, 1927877034244, 1198304211856, 683516984548, 344283099520, 142560031972, 41494985104, 5424890116, 38291116] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 8 :=
  ⟨⟨1,15,40⟩,mass_cell 8 1 15 40 130 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3186639157032, 1994392025310, 1133464986246, 566226705198, 230400380118, 64434803070, 7504360230, 25506610] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 8 :=
  ⟨⟨4,16,42⟩,mass_cell 8 4 16 42 127 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3292704332947, 2044168203544, 1120578362364, 532657152096, 200620985092, 48431616936, 3796146444, 84373] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 8 :=
  ⟨⟨2,18,44⟩,mass_cell 8 2 18 44 121 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3387572564083, 2109181768487, 1098531411479, 478349017055, 152322386687, 24715430135, 475349976, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 8 :=
  ⟨⟨2,19,45⟩,mass_cell 8 2 19 45 119 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3428104013385, 2146879088973, 1087274445025, 451633910613, 131128296873, 16781216989, 101057050] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 8 :=
  ⟨⟨6,21,47⟩,mass_cell 8 6 21 47 114 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3491630816444, 2228294757716, 1054202898644, 393440852564, 93020733908, 6834364244, 2763] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 8 :=
  ⟨⟨8,24,49⟩,mass_cell 8 8 24 49 109 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2342591523312, 1012586279388, 321735311880, 52946153268, 1124176116, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 8 :=
  ⟨⟨7,26,50⟩,mass_cell 8 7 26 50 105 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2421497802916, 994120703216, 284060011756, 35275229656, 184113107] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 8 :=
  ⟨⟨1,29,51⟩,mass_cell 8 1 29 51 101 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2501337696324, 967993409014, 234450659558, 17274302422, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 8 :=
  ⟨⟨1,32,52⟩,mass_cell 8 1 32 52 98 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2570195407684, 927019868395, 185122363563, 7233556210, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 8 :=
  ⟨⟨1,35,53⟩,mass_cell 8 1 35 53 95 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2648154178978, 903557571010, 148831581170, 2745235953] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 8 :=
  ⟨⟨1,39,54⟩,mass_cell 8 1 39 54 92 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2721217350342, 864428309146, 107388338914, 449071750] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 8 :=
  ⟨⟨8,42,55⟩,mass_cell 8 8 42 55 90 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2801093988555, 854299044624, 86966862132, 87476866] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 8 :=
  ⟨⟨15,47,56⟩,mass_cell 8 15 47 56 88 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2873034221409, 813407297546, 56684189706, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 8 :=
  ⟨⟨63,4,44⟩,mass_cell 8 63 4 44 278 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3405820596586, 2213796007936, 1167545766884, 403234153600, 21599164267, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 8 :=
  ⟨⟨57,36,55⟩,mass_cell 8 57 36 55 96 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2783526692031, 843564572598, 113010400146, 2037049400] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 8 :=
  ⟨⟨33,45,56⟩,mass_cell 8 33 45 56 89 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2867513306328, 810480931104, 63991970976, 7347680] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 8 :=
  ⟨⟨29,53,57⟩,mass_cell 8 29 53 57 85 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2943341629705, 765758893854, 32816855362, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 8 :=
  ⟨⟨57,21,51⟩,mass_cell 8 57 21 51 118 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2469245243128, 955650362468, 272570996804, 44074552100, 1604820467, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 8 :=
  ⟨⟨65,30,54⟩,mass_cell 8 65 30 54 103 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2702283285756, 871473550851, 154693157787, 8290520451, 770935] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 8 :=
  ⟨⟨41,44,56⟩,mass_cell 8 41 44 56 90 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2865541731563, 810056935212, 67631513608, 29543730] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 8 :=
  ⟨⟨37,52,57⟩,mass_cell 8 37 52 57 86 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2942046284616, 766839811446, 35309226400, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 8 :=
  ⟨⟨61,49,57⟩,mass_cell 8 61 49 57 87 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2937837626688, 764795545316, 41895442516, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 8 :=
  ⟨⟨66,19,51⟩,mass_cell 8 66 19 51 125 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2474177422969, 959249695939, 266259559463, 33541134930, 15098466, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 8 :=
  ⟨⟨64,26,53⟩,mass_cell 8 64 26 53 108 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2625162616090, 904074031534, 195973977962, 17572347214, 93069887] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 8 :=
  ⟨⟨57,42,56⟩,mass_cell 8 57 42 56 91 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2861305226820, 805480315608, 73353843588, 154260036] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 8 :=
  ⟨⟨69,48,57⟩,mass_cell 8 69 48 57 88 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2936325526045, 762175284623, 43526028311, 9314] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 8 :=
  ⟨⟨64,35,55⟩,mass_cell 8 64 35 55 97 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2781617319493, 840610346347, 114737678071, 2522773048, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 8 :=
  ⟨⟨75,13,50⟩,mass_cell 8 75 13 50 152 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2433541858538, 1016587165882, 276019365625, 11210763214, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 8 :=
  ⟨⟨74,24,53⟩,mass_cell 8 74 24 53 113 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2626397772898, 903797101374, 191160342834, 13418004437, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 8 :=
  ⟨⟨70,34,55⟩,mass_cell 8 70 34 55 98 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2780949772002, 840323559362, 116516657942, 2968434506, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 8 :=
  ⟨⟨71,21,52⟩,mass_cell 8 71 21 52 119 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2550513497541, 932612410878, 227441467374, 20608874199, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 8 :=
  ⟨⟨76,33,55⟩,mass_cell 8 76 33 55 99 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2780165224425, 838656516798, 116719688718, 3182092419, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 8 :=
  ⟨⟨76,16,51⟩,mass_cell 8 76 16 51 136 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2492690941187, 978219020052, 250395704641, 12203128546, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 8 :=
  ⟨⟨81,18,52⟩,mass_cell 8 81 18 52 129 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2565946774410, 950934964458, 213463653726, 6385591812, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 8 :=
  ⟨⟨84,26,54⟩,mass_cell 8 84 26 54 109 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2706312259709, 877991427625, 151353766969, 4839420883, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 8 :=
  ⟨⟨76,47,57⟩,mass_cell 8 76 47 57 89 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2935422427577, 761335538045, 45205997857, 1380537] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 8 :=
  ⟨⟨93,55,58⟩,mass_cell 8 93 55 58 85 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 3009063879201, 712154346444, 21735949975, 0] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 8 :=
  ⟨⟨95,44,57⟩,mass_cell 8 95 44 57 91 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2933783191468, 759291233250, 48447656398, 32227370] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 8 :=
  ⟨⟨77,39,56⟩,mass_cell 8 77 39 56 94 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2858179615080, 802692434886, 79526150574, 550462314] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 8 :=
  ⟨⟨90,15,52⟩,mass_cell 8 90 15 52 142 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2583120286266, 964043247189, 177150205489, 278575605, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 8 :=
  ⟨⟨99,54,58⟩,mass_cell 8 99 54 58 85 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 3008875506837, 713044905639, 22692634701, 0] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 8 :=
  ⟨⟨101,10,52⟩,mass_cell 8 101 10 52 177 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2622752903167, 996048518224, 119240364263, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 8 :=
  ⟨⟨99,6,51⟩,mass_cell 8 99 6 51 233 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2584784503802, 1040178609511, 116844363358, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 8 :=
  ⟨⟨100,43,57⟩,mass_cell 8 100 43 57 91 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2934061435705, 761088920469, 49291449073, 45450365] (by decide +kernel) (by decide +kernel)⟩
private def m50 : MassCell 8 :=
  ⟨⟨83,38,56⟩,mass_cell 8 83 38 56 95 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2857644237563, 801855252513, 80372897553, 671016370] (by decide +kernel) (by decide +kernel)⟩
private def m51 : MassCell 8 :=
  ⟨⟨106,53,58⟩,mass_cell 8 106 53 58 86 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 3008255628237, 710914961732, 23134855650, 0] (by decide +kernel) (by decide +kernel)⟩
private def m52 : MassCell 8 :=
  ⟨⟨88,37,56⟩,mass_cell 8 88 37 56 96 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2858047816694, 803762706636, 81413487756, 746261312] (by decide +kernel) (by decide +kernel)⟩
private def m53 : MassCell 8 :=
  ⟨⟨106,42,57⟩,mass_cell 8 106 42 57 92 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2933622021878, 758831778882, 48557354886, 34913962] (by decide +kernel) (by decide +kernel)⟩
private def m54 : MassCell 8 :=
  ⟨⟨109,12,53⟩,mass_cell 8 109 12 53 162 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2685102219206, 956279880724, 89622533535, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m55 : MassCell 8 :=
  ⟨⟨94,36,56⟩,mass_cell 8 94 36 56 97 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2857375842941, 800715020335, 79803653191, 611007506, 0] (by decide +kernel) (by decide +kernel)⟩
private def m56 : MassCell 8 :=
  ⟨⟨111,41,57⟩,mass_cell 8 111 41 57 93 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2933833135617, 759047512288, 47840964109, 6600969] (by decide +kernel) (by decide +kernel)⟩
private def m57 : MassCell 8 :=
  ⟨⟨112,52,58⟩,mass_cell 8 112 52 58 87 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 3008027854290, 710537403495, 23586251495, 0] (by decide +kernel) (by decide +kernel)⟩
private def m58 : MassCell 8 :=
  ⟨⟨103,34,56⟩,mass_cell 8 103 34 56 99 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2858916026832, 803670604460, 77120613180, 126903790, 0] (by decide +kernel) (by decide +kernel)⟩
private def m59 : MassCell 8 :=
  ⟨⟨115,40,57⟩,mass_cell 8 115 40 57 94 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2934707878487, 762017379527, 47337025464, 0] (by decide +kernel) (by decide +kernel)⟩
private def m60 : MassCell 8 :=
  ⟨⟨115,9,53⟩,mass_cell 8 115 9 53 189 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2705286957930, 966008735950, 63791585502, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m61 : MassCell 8 :=
  ⟨⟨117,51,58⟩,mass_cell 8 117 51 58 87 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 3008198330166, 712099543770, 24100345530, 0] (by decide +kernel) (by decide +kernel)⟩
private def m62 : MassCell 8 :=
  ⟨⟨118,30,56⟩,mass_cell 8 118 30 56 105 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2864589809786, 812490706414, 63171697469, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m63 : MassCell 8 :=
  ⟨⟨121,29,56⟩,mass_cell 8 121 29 56 106 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2866716214873, 816340589566, 59432643437, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m64 : MassCell 8 :=
  ⟨⟨120,39,57⟩,mass_cell 8 120 39 57 95 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2934859532631, 760705268117, 44871226431, 0] (by decide +kernel) (by decide +kernel)⟩
private def m65 : MassCell 8 :=
  ⟨⟨123,50,58⟩,mass_cell 8 123 50 58 88 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 3007934789929, 710470007086, 23850106960, 0] (by decide +kernel) (by decide +kernel)⟩
private def m66 : MassCell 8 :=
  ⟨⟨112,24,55⟩,mass_cell 8 112 24 55 115 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2794897393152, 857715646740, 83301392453, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m67 : MassCell 8 :=
  ⟨⟨130,26,56⟩,mass_cell 8 130 26 56 111 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2872924168489, 823518017287, 45670579094, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m68 : MassCell 8 :=
  ⟨⟨116,15,54⟩,mass_cell 8 116 15 54 144 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2749145242656, 922863723423, 72733546045, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m69 : MassCell 8 :=
  ⟨⟨124,38,57⟩,mass_cell 8 124 38 57 96 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2935683248502, 762295543409, 42865509713, 0] (by decide +kernel) (by decide +kernel)⟩
private def m70 : MassCell 8 :=
  ⟨⟨120,21,55⟩,mass_cell 8 120 21 55 122 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2804723886028, 869293780400, 65363394060, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m71 : MassCell 8 :=
  ⟨⟨121,13,54⟩,mass_cell 8 121 13 54 156 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2757765930181, 922699812125, 55405642888, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m72 : MassCell 8 :=
  ⟨⟨131,36,57⟩,mass_cell 8 131 36 57 98 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 2937973141680, 767406478064, 38479473503, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m73 : MassCell 8 :=
  ⟨⟨133,48,58⟩,mass_cell 8 133 48 58 89 (by decide)
    (by decide +kernel) [4674497865666, 4264177874262, 3881459829066, 3525078248286, 3008197106429, 710685608671, 22912997700, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 8) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51, m52, m53, m54, m55, m56, m57, m58, m59, m60, m61, m62, m63, m64, m65, m66, m67, m68, m69, m70, m71, m72, m73]

end Low6969Allocation.Group8
end Z6969Source2334

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles8
section Z6969Source2335
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group8
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2231438341, 1040257035, 5670966283, 19211164685, 57044840465, 87060277285], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35906960449, 35520254213, 43892487477, 39530619189, 35084798269, 39161736509], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8828671413, 17502416313, 13140345273, 8811827641, 25958058477, 17351419373], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099683254771, 1099683255795, 1099683256819, 1099683257843, 4416193017, 4382706169], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38725444105, 4365859337, 37407249, 1099549036051, 42953225753, 12888679961], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8593716761, 4298818073], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i3 : checks (tilesOf batches) 134 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 134 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 134 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 134 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 134 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 134 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 134 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [14596970507, 36022724625, 82630757405, 69947792437, 39715032341, 35269211413], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43557296405, 21914830173, 1100303949151, 43456407969, 39144593829, 17636563369], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13291335081, 13173898665, 4466527689, 1099851027915, 1099851028939, 30236243441], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17351349745, 4416191985, 1099683186163, 1099683252723, 1099666476535, 1099666477559], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8644046349, 4332304909, 37339665, 38675109397, 8593713689, 3783193], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [3784217], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i6 : checks (tilesOf batches) 134 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 134 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 134 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 134 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27684185101, 57162743833, 86926129193, 18710318149, 35185391905, 34967362849], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30605426977, 39463371097, 35084724569, 13106790821, 13308042677, 13190671797], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8845376949, 1099934847415, 1099934913975, 1099934914999, 1099934916023, 43221591513], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767073247, 1099767139807, 21646314985, 1099666406903, 1099666407927, 1099666408951], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8660823553, 104446465, 34430544393, 17200352789, 4315524629, 20559381], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 134 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 134 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 134 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36157206545, 82597336093, 61290751033, 35487175949, 35235723533, 43473411341], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21830945105, 17636564365, 17502417293, 13123569037, 1099985245611, 1099985246635], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985247659, 43322257857, 1099850958283, 1099850959307, 1099850960331, 1099851026891], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4533629405, 4449745373, 1099767071199, 26008386017, 13123491297, 8711153149], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099599297031, 1099599298055, 3781145, 3782169], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 134 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 134 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 134 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 134 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44546145301, 82597537829, 39916648513, 31125235989, 30840097045, 34900322581], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13157125489, 1100203285875, 43456413077, 13240936857, 8912484761, 8811824537], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934847415, 1099934913975, 1099934914999, 21730200017, 13123559889, 1099817403859], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817404883, 1099817405907, 1099716737515, 1099716738539, 1099716739563, 4416188913], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8644043277, 4349079053, 42986782225, 17217128977, 8627265041, 37336593], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [30085245461, 1099515485723], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i15 : checks (tilesOf batches) 134 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 134 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 134 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 134 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57162876953, 82547343405, 14314688585, 30907203857, 34900254993, 26276906257], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39463438681, 30789759321, 8828601741, 13324820885, 13190672789, 8828600725], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018733475, 1100018734499, 1100018801059, 1100018802083, 1099850960331, 1099817402835], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817403859, 1099817404883, 17401680349, 4466520545, 1099750291939, 1099750292963], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8660821505, 25840611849, 17250684425, 54112781, 1099565741583, 8610488853], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [20557333], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i18 : checks (tilesOf batches) 134 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 134 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 134 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 134 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 134 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61390935069, 82497081393, 35034468617, 30588581129, 9248036105, 35218806093], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26561902925, 13190673801, 8828601737, 1100119396747, 1099985245611, 1099985246635], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951693227, 13341595053, 8962745773, 8862151085, 1099867735495, 1099867736519], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867737543, 1099800624599, 1099800625623, 4382634481, 1099683183091, 4365854217], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4332301833, 1099582518795, 25823836685, 20557333, 20558357, 56852], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i21 : checks (tilesOf batches) 134 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 134 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 134 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 134 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 134 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61391069217, 69696134197, 26394205473, 26209728801, 9113818401, 35134988625], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22267004241, 8912484749, 8795047309, 1100102619535, 1100001957283, 1100002023843], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968470435, 13207379385, 8845372857, 1099884512707, 1099884513731, 1099884514755], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767069151, 1099767070175, 1099767071199, 4399410681, 1099649627643, 8660819465], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4365855241, 34413699597, 17217127953, 12922231313, 56848, 20558357], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56852, 1099515483675, 55832, 56856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i24 : checks (tilesOf batches) 134 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 134 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 134 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 134 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69796523045, 48355586109, 31007796521, 26511641897, 26276833577, 17519199561], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100320725323, 1100270394699, 1100035507615, 1100035508639, 1100035509663, 1100035510687], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100001957279, 8945969573, 8845374885, 1100001952167, 17435233757, 8845369821], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733513703, 1099733514727, 1099733515751, 4365856253, 1099549040131, 30118800909], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532261903, 56844, 37334545, 37335569, 56848, 1099532260887], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55828, 56852, 55832, 56856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i27 : checks (tilesOf batches) 134 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 134 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 134 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 134 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69763037225, 35571416129, 26763229477, 22267008293, 22048976165, 13157123429], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100236838247, 1100186507623, 1100152954215, 1099985175979, 1099985177003, 1099985178027], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985179051, 8878927281, 4550408625, 1099951620531, 13106714085, 8778261989], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099683183091, 1099683184115, 137998841, 1099649627643, 1099532262915, 1099549039115], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56840, 56844, 56848, 25790282261, 4315522581, 20557333], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099532260887, 55828, 56852, 55832, 56856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 134 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [73957409837, 18492214341, 26696123665, 26427760913, 21998648593, 1100119397763], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100069067139, 1100069133699, 8845376913, 1100085840275, 1100085841299, 1100085842323], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [9013076401, 8895704497, 4550408625, 1099817402835, 1099817403859, 21646312945], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13022895601, 1099683183091, 1099683184115, 4382633469, 1099632850431, 1099549039115], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56840, 56844, 56848, 8610487829, 20557333, 20558357], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099532260887, 55828, 56852, 4298746393, 55832, 56856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73923924017, 5691201609, 30806610189, 30555025677, 13425561869, 13224227205], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8845377925, 1100136172935, 1100085842323, 1100035511699, 1100002023835, 1099968470427], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17535898049, 8929256897, 1099867734471, 1099867735495, 1099867736519, 4483297753], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783846363, 1099783847387, 70889993, 1099582518795, 56840, 56844], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549038099, 55824, 56848, 4315522581, 20557333, 55828], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56852, 17183642137, 55832, 56856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 134 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69629025333, 30672395537, 26209729809, 4885960977, 13140344189, 1100169727359], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100169728383, 1100136174975, 1099968469411, 1099934916003, 13308042661, 8946036133], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8811821477, 1099901289919, 1099901290943, 1099767069151, 1099767070175, 1099767071199], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4399410685, 1099632850431, 56840, 8644042253, 4349078029, 56844], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55824, 56848, 1099532260887, 55828, 56852, 3781145], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55832, 56856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 134 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [56861632569, 22048975153, 17636639025, 9013155121, 1100018734491, 1100002023835], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099968470427, 1100018729379, 1100018730403, 1100018731427, 1100018732451, 1100018733475], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8912480701, 4567184829, 1099901287871, 1099616073219, 1099616074243, 56840], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4349078029, 54112781, 56844, 55824, 56848, 1099532260887], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55828, 56852, 55832, 56856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i42 : checks (tilesOf batches) 134 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 134 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 8 where
  orders := orders
  covers := by
    intro a ha box
    change 8+a.b≤142 ∧ 3+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6969Allocation.Group8
end Z6969Source2335

-- Source: ProximityPrize.SubmissionLower.Low6969Mass9
section Z6969Source2336
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group9

private def m0 : MassCell 9 :=
  ⟨⟨2,5,6⟩,mass_cell 9 2 5 6 211 (by decide)
    (by decide +kernel) [4569757821889, 3733193890716, 2987665837404, 2357139409948, 1829581498332, 1393581846684, 1038353053276, 753730570524, 530172704988, 358760617372, 231198322524, 139812689436, 77553441244, 37993155228, 15327262812, 4374049564, 574655196, 4840262] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 9 :=
  ⟨⟨1,6,13⟩,mass_cell 9 1 6 13 195 (by decide)
    (by decide +kernel) [4665139658767, 3955704731181, 3118031447877, 2415965635845, 1835002971117, 1361349607293, 981922175541, 684347784597, 456964020765, 288818947917, 169671107493, 89989518501, 40953677517, 14453558685, 3089613717, 172771893, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 9 :=
  ⟨⟨3,7,20⟩,mass_cell 9 3 7 20 184 (by decide)
    (by decide +kernel) [4665139658767, 4172688541213, 3287637331113, 2477591936949, 1822476690145, 1302285440301, 898242373017, 592802009893, 369649208529, 213699162525, 111097401481, 49219790997, 16672532673, 3292164109, 145689314, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 9 :=
  ⟨⟨2,9,28⟩,mass_cell 9 2 9 28 164 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3615955692135, 2643313020414, 1861326352446, 1258290244734, 807474417342, 483725189886, 263465481534, 124694811006, 46989296574, 11501656062, 961206846, 123797] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 9 :=
  ⟨⟨4,10,32⟩,mass_cell 9 4 10 32 157 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3755933931308, 2762862962435, 1889911193915, 1233183676755, 756803014283, 427458187043, 214404552795, 89463846515, 27024180395, 4040043843, 60886295, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 9 :=
  ⟨⟨1,12,36⟩,mass_cell 9 1 12 36 145 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3836179348025, 2940507742593, 1945123253553, 1209627912513, 691578367473, 350280866433, 146791257393, 43914988353, 6207107313, 66806079, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 9 :=
  ⟨⟨1,15,41⟩,mass_cell 9 1 15 41 131 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3207533601651, 2024845127307, 1154287559079, 580480815843, 239503751487, 69128272827, 8819339607, 53947464] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 9 :=
  ⟨⟨4,16,43⟩,mass_cell 9 4 16 43 128 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3302588415999, 2080401950887, 1144425435383, 548153852575, 209855878303, 52683357431, 4671303847, 1363568] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 9 :=
  ⟨⟨3,18,45⟩,mass_cell 9 3 18 45 122 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3383383226140, 2146693130278, 1119879491362, 491395806790, 159891216658, 27663546886, 705139432, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 9 :=
  ⟨⟨1,21,47⟩,mass_cell 9 1 21 47 114 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3443261607407, 2217191079564, 1066118734476, 404381857932, 97135403148, 7241087628, 2969] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 9 :=
  ⟨⟨4,23,49⟩,mass_cell 9 4 23 49 111 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2347079378228, 1065170809196, 367037171748, 72080425820, 2872390300, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 9 :=
  ⟨⟨1,25,50⟩,mass_cell 9 1 25 50 107 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2425336240204, 1053590154156, 330033346572, 50432437612, 717887530] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 9 :=
  ⟨⟨1,27,51⟩,mass_cell 9 1 27 51 105 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2496960832487, 1034664218711, 291283837451, 33476445791, 94159517] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 9 :=
  ⟨⟨3,29,52⟩,mass_cell 9 3 29 52 102 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2568394926160, 1017472912060, 256083061564, 21624429500, 1913885] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 9 :=
  ⟨⟨9,31,53⟩,mass_cell 9 9 31 53 100 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2636086226041, 994557005513, 221147380981, 13405401025, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 9 :=
  ⟨⟨1,36,54⟩,mass_cell 9 1 36 54 95 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2702869455999, 943033732199, 153937149695, 2743795800] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 9 :=
  ⟨⟨9,38,55⟩,mass_cell 9 9 38 55 94 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2779746410768, 948504022805, 138121129117, 1615921534] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 9 :=
  ⟨⟨1,44,56⟩,mass_cell 9 1 44 56 90 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2850046627701, 911654165707, 89037066795, 45515275] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 9 :=
  ⟨⟨1,50,57⟩,mass_cell 9 1 50 57 87 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2917981248637, 881029712534, 56372540466, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 9 :=
  ⟨⟨61,4,45⟩,mass_cell 9 61 4 45 279 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3397358187865, 2260048424409, 1211271106177, 442050416641, 31188732246, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 9 :=
  ⟨⟨66,26,54⟩,mass_cell 9 66 26 54 109 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2687879802229, 951709390105, 205433758633, 17956403945, 56299808, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 9 :=
  ⟨⟨35,35,55⟩,mass_cell 9 35 35 55 97 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2768359473519, 936188302063, 153815419083, 4408553656, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 9 :=
  ⟨⟨57,43,57⟩,mass_cell 9 57 43 57 91 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2907582618849, 876635675107, 81465599991, 204298509] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 9 :=
  ⟨⟨63,23,53⟩,mass_cell 9 63 23 53 115 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2614192380685, 974097869639, 243880406075, 29179209231, 253577649, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 9 :=
  ⟨⟨62,31,55⟩,mass_cell 9 62 31 55 102 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2761511905606, 927583749012, 164960068356, 8737683316, 328010] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 9 :=
  ⟨⟨41,39,56⟩,mass_cell 9 41 39 56 94 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2839627593123, 909862505021, 115259972609, 1195075774] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 9 :=
  ⟨⟨62,36,56⟩,mass_cell 9 62 36 56 97 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2835220133666, 903708730488, 123931762500, 2715541270, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 9 :=
  ⟨⟨57,51,58⟩,mass_cell 9 57 51 58 87 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2976236983355, 845531613579, 46345816551, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 9 :=
  ⟨⟨59,18,51⟩,mass_cell 9 59 18 51 128 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2469604123364, 1018445431056, 317151648420, 55478819897, 942644553, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 9 :=
  ⟨⟨73,29,55⟩,mass_cell 9 73 29 55 105 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2760875442008, 925776789956, 164450801348, 8771978937, 1] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 9 :=
  ⟨⟨75,24,54⟩,mass_cell 9 75 24 54 114 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2690305614073, 954953852232, 201361636524, 13057055660, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 9 :=
  ⟨⟨64,42,57⟩,mass_cell 9 64 42 57 92 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2906558650907, 874874393427, 83778291435, 328873449] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 9 :=
  ⟨⟨72,49,58⟩,mass_cell 9 72 49 58 88 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2974571019142, 841617153980, 49807547180, 627780] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 9 :=
  ⟨⟨75,13,51⟩,mass_cell 9 75 13 51 153 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2501385771834, 1050807213560, 282889230814, 10596042968, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 9 :=
  ⟨⟨74,34,56⟩,mass_cell 9 74 34 56 99 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2833909386004, 901133536863, 126031589447, 3461315874, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 9 :=
  ⟨⟨71,21,53⟩,mass_cell 9 71 21 53 120 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2619530716701, 982360158752, 240700808288, 21188654981, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 9 :=
  ⟨⟨82,27,55⟩,mass_cell 9 82 27 55 109 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2762751209832, 928958261354, 161131392818, 5945941713, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 9 :=
  ⟨⟨87,16,53⟩,mass_cell 9 87 16 53 138 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2640717186724, 1007770455816, 201973241326, 1162308410, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 9 :=
  ⟨⟨94,18,54⟩,mass_cell 9 94 18 54 131 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2711068118127, 986886870239, 164825982476, 157118120, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 9 :=
  ⟨⟨86,12,52⟩,mass_cell 9 86 12 52 161 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2589389532447, 1051062092618, 215613540083, 599484185, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 9 :=
  ⟨⟨85,47,58⟩,mass_cell 9 85 47 58 90 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2973654762405, 839971055379, 52669761575, 13687798] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 9 :=
  ⟨⟨91,46,58⟩,mass_cell 9 91 46 58 90 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2973378433367, 839461189799, 53671738159, 28112658] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 9 :=
  ⟨⟨102,44,58⟩,mass_cell 9 102 44 58 92 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2973199385756, 839315584550, 54611117770, 52940164] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 9 :=
  ⟨⟨102,15,54⟩,mass_cell 9 102 15 54 144 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2723554156013, 999121624632, 131162116493, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 9 :=
  ⟨⟨93,37,57⟩,mass_cell 9 93 37 57 97 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2904951826520, 872100292516, 88065336452, 735444728, 0] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 9 :=
  ⟨⟨106,55,59⟩,mass_cell 9 106 55 59 86 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 3037281333123, 802647838128, 26467208771, 0] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 9 :=
  ⟨⟨107,43,58⟩,mass_cell 9 107 43 58 92 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2973300720279, 839789329709, 54474945297, 39913585] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 9 :=
  ⟨⟨112,42,58⟩,mass_cell 9 112 42 58 93 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2973386553655, 839587859175, 53529266695, 6464943] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 9 :=
  ⟨⟨108,6,53⟩,mass_cell 9 108 6 53 235 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2706456950245, 1066018445447, 90703325561, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 9 :=
  ⟨⟨98,36,57⟩,mass_cell 9 98 36 57 98 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2905082929714, 871759808304, 86599557492, 481725111, 0] (by decide +kernel) (by decide +kernel)⟩
private def m50 : MassCell 9 :=
  ⟨⟨102,35,57⟩,mass_cell 9 102 35 57 99 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2905899305489, 874648445936, 85624686037, 224585918, 0] (by decide +kernel) (by decide +kernel)⟩
private def m51 : MassCell 9 :=
  ⟨⟨114,32,57⟩,mass_cell 9 114 32 57 103 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2908203007183, 878931834405, 75414195526, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m52 : MassCell 9 :=
  ⟨⟨117,53,59⟩,mass_cell 9 117 53 59 87 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 3037192146190, 803215290968, 27428967320, 0] (by decide +kernel) (by decide +kernel)⟩
private def m53 : MassCell 9 :=
  ⟨⟨112,17,55⟩,mass_cell 9 112 17 55 136 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2791061563056, 972674535064, 96000768243, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m54 : MassCell 9 :=
  ⟨⟨117,41,58⟩,mass_cell 9 117 41 58 94 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2973456762302, 838679028372, 51667054401, 0] (by decide +kernel) (by decide +kernel)⟩
private def m55 : MassCell 9 :=
  ⟨⟨114,9,54⟩,mass_cell 9 114 9 54 190 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2755853498333, 1031380238248, 78795726758, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m56 : MassCell 9 :=
  ⟨⟨121,40,58⟩,mass_cell 9 121 40 58 95 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2973952023910, 840580071612, 50210226285, 0] (by decide +kernel) (by decide +kernel)⟩
private def m57 : MassCell 9 :=
  ⟨⟨123,52,59⟩,mass_cell 9 123 52 59 88 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 3037026452866, 801447625903, 27193185999, 0] (by decide +kernel) (by decide +kernel)⟩
private def m58 : MassCell 9 :=
  ⟨⟨125,39,58⟩,mass_cell 9 125 39 58 96 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2974435827931, 841908618779, 48096568072, 0] (by decide +kernel) (by decide +kernel)⟩
private def m59 : MassCell 9 :=
  ⟨⟨107,26,56⟩,mass_cell 9 107 26 56 111 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2842155329509, 917314718340, 102894296674, 101270, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m60 : MassCell 9 :=
  ⟨⟨126,28,57⟩,mass_cell 9 126 28 57 109 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2913930129462, 893446255534, 60263153632, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m61 : MassCell 9 :=
  ⟨⟨121,21,56⟩,mass_cell 9 121 21 56 123 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2853345536468, 935122214580, 72129633258, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m62 : MassCell 9 :=
  ⟨⟨129,27,57⟩,mass_cell 9 129 27 57 111 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2915321755619, 895491819475, 55392253374, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m63 : MassCell 9 :=
  ⟨⟨128,18,56⟩,mass_cell 9 128 18 56 133 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2861371885388, 945768060009, 54906362033, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m64 : MassCell 9 :=
  ⟨⟨132,37,58⟩,mass_cell 9 132 37 58 98 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2975816101820, 846597532894, 43604354578, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m65 : MassCell 9 :=
  ⟨⟨128,51,59⟩,mass_cell 9 128 51 59 88 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 3037077304922, 801695042280, 27002839945, 0] (by decide +kernel) (by decide +kernel)⟩
private def m66 : MassCell 9 :=
  ⟨⟨120,6,54⟩,mass_cell 9 120 6 54 236 (by decide)
    (by decide +kernel) [4665139658767, 4239101969119, 3842796469735, 3474812532007, 2771427443509, 1033458998642, 53426435730, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 9) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51, m52, m53, m54, m55, m56, m57, m58, m59, m60, m61, m62, m63, m64, m65, m66]

end Low6969Allocation.Group9
end Z6969Source2336

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles9
section Z6969Source2337
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group9
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2214661125, 1023479817, 6358963211, 19311893517, 57078460433, 87060277285], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35906960449, 35520319745, 43858998589, 39530684733, 39329499453, 47667851581], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21814227365, 13123635637, 4567259573, 25991678433, 17401816545, 4416260593], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4399550961, 8711223801, 4416259577, 1099632990715, 1099632991739, 37474829], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549103631, 38675178001, 20696593], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 133 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 133 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 133 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 133 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 133 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 133 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 133 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [14731253769, 31996258321, 82647533593, 74226047029, 39731808533, 35336384789], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [47835550997, 26193085785, 21931595173, 17519193509, 13190742437, 8728007105], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867872707, 43271920069, 43171399137, 1099716809191, 1099716875751, 1099716876775], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4416258545, 1099666475507, 1099666476531, 12989410809, 4416257529, 34447389185], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [20629009, 42953218581, 21478675989, 8593780245, 4298816021], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 133 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 133 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 133 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 133 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 133 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 133 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 133 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27751359501, 53002059801, 86959748137, 23005349957, 35219010857, 34984204585], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34833284393, 43590697337, 34950573433, 13190741405, 8744783285, 1099918137783], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918204343, 17535965633, 13173960129, 1099750362591, 1099750363615, 1099750430175], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [43137770985, 4433034729, 1099700028907, 1099700029931, 21579272697, 34413833737], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8644111881, 4332370441, 37405197, 38658396693, 17183642133, 3848725], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [3849749], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i9 : checks (tilesOf batches) 133 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 133 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 133 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 133 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 133 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 133 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [44461994001, 86875659297, 48523423805, 35470531853, 35202236685, 34984207629], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17485711729, 1100203351411, 43590627709, 13291333029, 13173962149, 8828667301], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884581311, 1099884582335, 1099884583359, 26025230809, 13140336089, 1099733583331], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733584355, 1099733585379, 4449809901, 4382703085, 70958597, 1099582587399], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8627334665, 4298812949, 3847701, 3848725], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 133 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 133 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 133 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 133 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 133 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 133 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44596542485, 86842173477, 35688856641, 35386714377, 30890495241, 34950720777], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13090083201, 13241003417, 8912551321, 8811891097, 43439766945, 1099918136759], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918137783, 1099918204343, 21730266577, 8878925265, 1099800693203, 1099800694227], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800695251, 1099700026859, 1099700027883, 1099700028907, 4449808881, 154843633], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [30152354305, 21562493441, 8610554385], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 133 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 133 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 133 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 133 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 133 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 133 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53002192921, 86825597997, 14331531337, 31007931661, 30756347149, 34816507149], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43557210489, 26427749753, 13224295805, 13106859389, 1099985247655, 13274553781], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8929324469, 8811887029, 1099918134711, 1099918135735, 1099918136759, 1099918137783], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800692179, 1099800693203, 1099683248623, 1099683249647, 1099683250671, 17334637041], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4349144585, 54179337, 42986916365, 8593778197], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 133 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 133 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 133 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 133 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 133 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61390935069, 78269288497, 1513741389, 30789898521, 30571868441, 13459181849], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39429952845, 26545192269, 13173895573, 8845443477, 1100052352407, 1099985244583], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985245607, 1099985246631, 1099901427131, 13207443913, 8878991817, 1099783913943], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783914967, 1099783915991, 4449809885, 1099750358495, 70956549, 1099582585351], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38708729353, 25823903241, 4315589137, 20623889], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 133 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 133 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 133 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 133 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 133 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [69830008865, 61173376057, 35336380717, 26595525933, 26343940397, 21898050869], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [9063552309, 8828665245, 1100018796959, 1100018797983, 1100018799007, 1099968468395], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968469419, 1099968535979, 13190668729, 8845439417, 1099767135707, 1099767136731], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767137755, 21612824053, 13022961141, 4382700025, 1099632916987, 4365921797], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [20624913], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 133 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 133 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 133 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 133 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [61374426149, 56895187001, 22032263481, 26075578681, 1100387900731, 30890487121], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26394266961, 13106856325, 1100119462279, 1100119463303, 1100119464327, 1099884577215], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884578239, 1099884579263, 1099884580287, 8895769025, 4567250369, 4466589121], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17368190441, 8778326505, 1099683249647, 70956549, 1099582585351, 4332367373], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549105679], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 133 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 133 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 133 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 133 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [65552021545, 39816050753, 26696186169, 22216742201, 21998710073, 17468933465], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100287236443, 1100253683035, 1100002018723, 1100002019747, 1100002020771, 1100002021795], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100002022819, 8878992825, 4550474169, 1099901354427, 17317860845, 8711219693], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099632916987, 1099632918011, 87733761, 4332366349, 37401101, 1099532328463], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17200485905, 1099515550231, 56852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 133 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 133 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 133 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 133 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69746394157, 22787246149, 26645857573, 22166413605, 26193017125, 1100136240515], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100119464323, 1100069133699, 13140408717, 1100085905807, 1100085906831, 1100085907855], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8895701453, 8811883981, 4466588109, 1099817468367, 1099817469391, 21596046841], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13006183929, 1099632916987, 1099632918011, 4365921797, 70956549, 1099549105675], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099515550231, 56852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 133 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 133 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 133 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73940766769, 5724821577, 30823452945, 26344010001, 17687039249, 1100085906831], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100085907855, 1100085908879, 8962879901, 8828665245, 1100018796959, 1099985246627], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934916003, 17502409161, 8895702473, 1099767135707, 1099767136731, 1099767137755], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4382700025, 1099632916987, 1099549105675, 20623889, 20624913, 8593778197], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099515550231, 56852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i36 : checks (tilesOf batches) 133 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 133 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 133 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69645868085, 30689238293, 26226572565, 4902803733, 13140409733, 1100119461255], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100119462279, 1100119463303, 1099951692203, 1099951758763, 13308108205, 8946101677], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8811887021, 1099851023815, 1099851024839, 1099716803047, 1099716804071, 1099716805095], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4365921797, 70956549, 12888743445, 1099515550231, 56852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 133 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 133 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 133 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [56844855353, 26310453549, 21864564013, 1100421455151, 8811890061, 1100085907855], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100085908879, 1100069132687, 8962812337, 8845440433, 4500144561, 1099851024839], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099851025863, 1099716805095, 1099716806119, 4382701041, 1099666472435, 54179337], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099565808139, 1099549105675, 4332366349, 4315591181, 3846677, 1099515550231], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i42 : checks (tilesOf batches) 133 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 133 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((9 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 9 where
  orders := orders
  covers := by
    intro a ha box
    change 9+a.b≤142 ∧ 3+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6969Allocation.Group9
end Z6969Source2337

-- Source: ProximityPrize.SubmissionLower.Low6969Mass10
section Z6969Source2338
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group10

private def m0 : MassCell 10 :=
  ⟨⟨2,5,7⟩,mass_cell 10 2 5 7 189 (by decide)
    (by decide +kernel) [4606755133925, 3795097543302, 3042885585162, 2397139492422, 1849789550010, 1392750926310, 1017923673162, 717192725862, 482427903162, 305483907270, 178200323850, 92401622022, 39897154362, 12481156902, 1932749130, 30226326] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 10 :=
  ⟨⟨2,6,15⟩,mass_cell 10 2 6 15 179 (by decide)
    (by decide +kernel) [4679106249028, 4064152064581, 3203614905323, 2470172570607, 1857465547091, 1354934890775, 951924889659, 637683063743, 401360165027, 232010177511, 118590317195, 49961032079, 14886002163, 2032139447, 17280705] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 10 :=
  ⟨⟨1,8,25⟩,mass_cell 10 1 8 25 161 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3536291597878, 2626179279382, 1883279811574, 1292518703062, 838104826294, 503530417558, 271571076982, 124285768534, 43016820022, 8389923094, 316271865, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 10 :=
  ⟨⟨2,9,29⟩,mass_cell 10 2 9 29 154 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3705229214234, 2716670200562, 1896319540646, 1257859554786, 779954969126, 440556783602, 216902271942, 85514981666, 22204734086, 2067624306, 863338] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 10 :=
  ⟨⟨2,10,32⟩,mass_cell 10 2 10 32 148 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3806760990764, 2811219401009, 1916636752685, 1232061575433, 731466260933, 387723142241, 172604493789, 56782531385, 9829412213, 238488956, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 10 :=
  ⟨⟨4,12,37⟩,mass_cell 10 4 12 37 139 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3029924856228, 1962716544452, 1179386414564, 637411400196, 293362465316, 102904604228, 20796841572, 894073640, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 10 :=
  ⟨⟨1,14,40⟩,mass_cell 10 1 14 40 130 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3207360843648, 2023077022692, 1152014971812, 570508688292, 225280752612, 57974586468, 5154452772, 1012186] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 10 :=
  ⟨⟨1,15,41⟩,mass_cell 10 1 15 41 126 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3254585780626, 2022888190177, 1113287883977, 522348162457, 187347626449, 39069787889, 1805015739, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 10 :=
  ⟨⟨4,16,43⟩,mass_cell 10 4 16 43 124 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3355694148216, 2085976575004, 1109205408572, 495405932380, 163559368828, 28444444316, 697470818, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 10 :=
  ⟨⟨4,18,45⟩,mass_cell 10 4 18 45 119 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3439831024823, 2147394286147, 1074168198391, 432652698251, 116419484671, 11827556947, 12060931] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 10 :=
  ⟨⟨1,21,47⟩,mass_cell 10 1 21 47 112 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3503831622992, 2225646197728, 1021937317252, 349257483176, 64289615500, 1868101406, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 10 :=
  ⟨⟨1,24,49⟩,mass_cell 10 1 24 49 106 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2347139737968, 987735795584, 284106576272, 33498540960, 102317924] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 10 :=
  ⟨⟨9,27,51⟩,mass_cell 10 9 27 51 103 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2498979750770, 954384177627, 227571137587, 16345849059, 0] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 10 :=
  ⟨⟨4,30,52⟩,mass_cell 10 4 30 52 99 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2579001622818, 928685520131, 183250428111, 6768432046, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 10 :=
  ⟨⟨4,33,53⟩,mass_cell 10 4 33 53 96 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2654667473142, 899434666694, 144336582778, 2340667789] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 10 :=
  ⟨⟨11,36,54⟩,mass_cell 10 11 36 54 94 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2726570780113, 865719108884, 111177307764, 628812029] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 10 :=
  ⟨⟨6,41,55⟩,mass_cell 10 6 41 55 90 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2803600803136, 827085233619, 72471044331, 7743848] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 10 :=
  ⟨⟨1,48,56⟩,mass_cell 10 1 48 56 86 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2874181940465, 762535283350, 36473424276, 0] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 10 :=
  ⟨⟨9,54,57⟩,mass_cell 10 9 54 57 84 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2950318388025, 732722586978, 20909090041] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 10 :=
  ⟨⟨64,14,48⟩,mass_cell 10 64 14 48 138 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3524501299114, 2247004860567, 1004047459251, 360666850479, 85806659211, 5726614076, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 10 :=
  ⟨⟨60,24,52⟩,mass_cell 10 60 24 52 109 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2543911518276, 908414082612, 217990538132, 23862703604, 220005294, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 10 :=
  ⟨⟨65,4,42⟩,mass_cell 10 65 4 42 247 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3323108584601, 2118807006452, 1169192278356, 500119961421, 83897239562, 51332555, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 10 :=
  ⟨⟨65,18,50⟩,mass_cell 10 65 18 50 124 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2385250413836, 957384818484, 293601448412, 54958619396, 3074904415, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 10 :=
  ⟨⟨53,28,53⟩,mass_cell 10 53 28 53 103 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2628019221687, 886174176290, 176434640882, 10727425986, 5732] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 10 :=
  ⟨⟨48,37,55⟩,mass_cell 10 48 37 55 94 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2788369427668, 820043736248, 91769847084, 457910873] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 10 :=
  ⟨⟨61,21,51⟩,mass_cell 10 61 21 51 116 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2465596525622, 936986828720, 259641948948, 40054458776, 1449518204, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 10 :=
  ⟨⟨68,30,54⟩,mass_cell 10 68 30 54 101 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2702967205604, 849988920001, 139750283645, 5417914522, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 10 :=
  ⟨⟨57,36,55⟩,mass_cell 10 57 36 55 95 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2785854841287, 818593492830, 95773982254, 748968661] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 10 :=
  ⟨⟨15,46,56⟩,mass_cell 10 15 46 56 88 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2874880810053, 781414541172, 45280512219, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 10 :=
  ⟨⟨46,43,56⟩,mass_cell 10 46 43 56 90 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2867014733859, 779873771724, 55743206248, 878438] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 10 :=
  ⟨⟨52,50,57⟩,mass_cell 10 52 50 57 86 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2942320419817, 731334979419, 29110175996, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 10 :=
  ⟨⟨65,35,55⟩,mass_cell 10 65 35 55 96 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2784373839161, 818851533785, 99705688721, 1120681075] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 10 :=
  ⟨⟨65,41,56⟩,mass_cell 10 65 41 56 91 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2862614256841, 776561472498, 61680726102, 32863661] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 10 :=
  ⟨⟨71,48,57⟩,mass_cell 10 71 48 57 87 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2939357955375, 729924698308, 33010073464, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 10 :=
  ⟨⟨61,27,53⟩,mass_cell 10 61 27 53 105 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2625192844620, 883689276282, 179445744654, 12524460346, 3963753] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 10 :=
  ⟨⟨73,34,55⟩,mass_cell 10 73 34 55 97 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2782749606533, 817621518376, 102523931776, 1529988302, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 10 :=
  ⟨⟨80,47,57⟩,mass_cell 10 80 47 57 88 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2938078357902, 728864923290, 34757438838, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 10 :=
  ⟨⟨87,16,51⟩,mass_cell 10 87 16 51 132 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2479004838913, 947248837400, 242688855688, 16518759908, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 10 :=
  ⟨⟨68,26,53⟩,mass_cell 10 68 26 53 107 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2624130896012, 883613520839, 182139095819, 14041786799, 23235373] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 10 :=
  ⟨⟨88,27,54⟩,mass_cell 10 88 27 54 106 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2701619168891, 849445307287, 142805142047, 6602768630, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 10 :=
  ⟨⟨90,15,51⟩,mass_cell 10 90 15 51 136 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2488316137586, 959215883240, 240281259475, 11450184754, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 10 :=
  ⟨⟨78,21,52⟩,mass_cell 10 78 21 52 117 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2546063270615, 913081894575, 220739552415, 24083884675, 92579913, 0] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 10 :=
  ⟨⟨75,25,53⟩,mass_cell 10 75 25 53 108 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2622792486792, 881440754359, 182123000879, 14575334407, 46386435] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 10 :=
  ⟨⟨88,46,57⟩,mass_cell 10 88 46 57 89 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2937327430995, 729178279723, 36534904583, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 10 :=
  ⟨⟨96,45,57⟩,mass_cell 10 96 45 57 89 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2936528089832, 728595882057, 37983849961, 16906] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 10 :=
  ⟨⟨96,37,56⟩,mass_cell 10 96 37 56 95 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2858702987268, 774702415827, 70027844787, 343951187] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 10 :=
  ⟨⟨103,36,56⟩,mass_cell 10 103 36 56 96 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2858179879014, 773585311056, 70429852176, 408711008] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 10 :=
  ⟨⟨104,44,57⟩,mass_cell 10 104 44 57 90 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2935679854796, 727064559628, 38992415596, 1185336] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 10 :=
  ⟨⟨110,54,58⟩,mass_cell 10 110 54 58 85 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3011774368349, 674914737967, 16145126626, 0] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 10 :=
  ⟨⟨118,42,57⟩,mass_cell 10 118 42 57 91 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2935036123671, 726373660685, 40323402297, 10100725] (by decide +kernel) (by decide +kernel)⟩
private def m50 : MassCell 10 :=
  ⟨⟨81,33,55⟩,mass_cell 10 81 33 55 98 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2780980053228, 814810152087, 103938446591, 1904165328, 0] (by decide +kernel) (by decide +kernel)⟩
private def m51 : MassCell 10 :=
  ⟨⟨112,12,52⟩,mass_cell 10 112 12 52 154 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2595286172742, 957300917096, 143528439354, 73815, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m52 : MassCell 10 :=
  ⟨⟨115,34,56⟩,mass_cell 10 115 34 56 98 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2858716356891, 774711467838, 69826087822, 274632759, 0] (by decide +kernel) (by decide +kernel)⟩
private def m53 : MassCell 10 :=
  ⟨⟨118,53,58⟩,mass_cell 10 118 53 58 85 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3011268136363, 674268154633, 16842930658, 0] (by decide +kernel) (by decide +kernel)⟩
private def m54 : MassCell 10 :=
  ⟨⟨117,10,52⟩,mass_cell 10 117 10 52 168 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2612199469944, 970938414308, 120859757471, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m55 : MassCell 10 :=
  ⟨⟨101,30,55⟩,mass_cell 10 101 30 55 102 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2779812608789, 812240736826, 103873899498, 1973269623, 0] (by decide +kernel) (by decide +kernel)⟩
private def m56 : MassCell 10 :=
  ⟨⟨126,32,56⟩,mass_cell 10 126 32 56 100 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2859920793310, 775247155128, 65069987919, 720720, 0] (by decide +kernel) (by decide +kernel)⟩
private def m57 : MassCell 10 :=
  ⟨⟨111,28,55⟩,mass_cell 10 111 28 55 105 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2782711784653, 817580052026, 100973943882, 733535772, 0] (by decide +kernel) (by decide +kernel)⟩
private def m58 : MassCell 10 :=
  ⟨⟨124,41,57⟩,mass_cell 10 124 41 57 92 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2935255998336, 727469797296, 40637229924, 11460137] (by decide +kernel) (by decide +kernel)⟩
private def m59 : MassCell 10 :=
  ⟨⟨120,9,52⟩,mass_cell 10 120 9 52 177 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2618910008621, 970823848080, 105693457790, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m60 : MassCell 10 :=
  ⟨⟨128,24,55⟩,mass_cell 10 128 24 55 112 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2791513805756, 828988267972, 81532430962, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m61 : MassCell 10 :=
  ⟨⟨130,40,57⟩,mass_cell 10 130 40 57 93 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2935441507914, 727774838684, 40230423324, 1227535] (by decide +kernel) (by decide +kernel)⟩
private def m62 : MassCell 10 :=
  ⟨⟨132,4,52⟩,mass_cell 10 132 4 52 257 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2660459787516, 976353644760, 51416464879, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m63 : MassCell 10 :=
  ⟨⟨123,13,53⟩,mass_cell 10 123 13 53 149 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2671729415598, 930259472104, 102463363112, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m64 : MassCell 10 :=
  ⟨⟨116,21,54⟩,mass_cell 10 116 21 54 119 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2715235917457, 865307259265, 116736007184, 12842571, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m65 : MassCell 10 :=
  ⟨⟨135,22,55⟩,mass_cell 10 135 22 55 117 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2797550575293, 836184955716, 69744136047, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m66 : MassCell 10 :=
  ⟨⟨136,39,57⟩,mass_cell 10 136 39 57 94 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2935592287423, 727244398928, 38970107872, 0] (by decide +kernel) (by decide +kernel)⟩
private def m67 : MassCell 10 :=
  ⟨⟨125,52,58⟩,mass_cell 10 125 52 58 86 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 3011101524673, 674953598024, 17544105309, 0] (by decide +kernel) (by decide +kernel)⟩
private def m68 : MassCell 10 :=
  ⟨⟨134,9,53⟩,mass_cell 10 134 9 53 178 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2696206211498, 937249446054, 61144795598, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m69 : MassCell 10 :=
  ⟨⟨119,20,54⟩,mass_cell 10 119 20 54 121 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2720091663678, 872960778228, 111280642779, 73815, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m70 : MassCell 10 :=
  ⟨⟨139,21,55⟩,mass_cell 10 139 21 55 120 (by decide)
    (by decide +kernel) [4679106249028, 4274622143268, 3894297784836, 3537370752484, 2799806850592, 835498436372, 61640112138, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 10) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51, m52, m53, m54, m55, m56, m57, m58, m59, m60, m61, m62, m63, m64, m65, m66, m67, m68, m69, m70]

end Low6969Allocation.Group10
end Z6969Source2338

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles10
section Z6969Source2339
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group10
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2332101637, 1040257033, 10201011211, 23657521165, 82580092949, 87094036529], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39916157185, 39748657409, 35486568711, 30806608209, 30638909777, 17787636049], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13190670813, 8845375965, 8761492957, 1099834184167, 1099834250727, 1099834251751], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21663091205, 13056385541, 34531140105, 21646312969, 1099683186187, 1099683187211], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099683188235, 34480591381, 43053823513, 4349082141, 1099599299103, 4332302889], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [20560429, 20561453, 12888678961], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i3 : checks (tilesOf batches) 140 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 140 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 140 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 140 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 140 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 140 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 140 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [15083706379, 32029812753, 86908946457, 65703156789, 39782074637, 35369873677], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [47869039885, 21881275753, 21931529637, 17519127973, 17418535333, 1099934848463], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934915023, 4483301857, 1099850959331, 1099850960355, 1099850961379, 43255081449], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8778264057, 4449745401, 25974764033, 17384902145, 1099649630739, 1099649631763], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8711152149, 38758783513, 34447185437, 70892065, 1099582520867, 4332301865], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [37336617], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i6 : checks (tilesOf batches) 140 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 140 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 140 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 140 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 140 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 140 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 140 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27868865549, 57213141017, 86976526377, 14499236933, 30957533485, 34967361837], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30571805997, 39496925541, 30856800613, 13140344233, 13324818881, 13173828033], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8845375937, 1099951623627, 1099951624651, 1099951625675, 1099951692235, 1099817403883], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817404907, 1099716737539, 1099716738563, 1099716739587, 43120862725, 17368123909], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4466518537, 4416188937, 30118734373, 37335593, 37336617, 8610487853], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [42953156145, 34363298353], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i9 : checks (tilesOf batches) 140 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 140 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 140 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 140 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 140 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 140 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36308332561, 82614113309, 57079735353, 35487175953, 31058196753, 39262329105], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21814165861, 1100371056999, 17603008933, 13207383461, 8895708581, 1100018731451], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018732475, 1100018733499, 1100018734523, 38976893413, 1099783847411, 1099783848435], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783849459, 4500073973, 4416189941, 21679798785, 13089935873, 8744706573], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099632850455, 1099632851479, 34430474785, 37334569, 37335593], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 140 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 140 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 140 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 140 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 140 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 140 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [52951596053, 86859018281, 22921397317, 31074906385, 39279104273, 34849995025], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39496924521, 30856799593, 17452087689, 1100119395747, 1100119396771, 1100119397795], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100102621603, 17653338537, 13240935849, 8912483753, 1099934843343, 1099934844367], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099934845391, 1099750290939, 1099750291963, 1099750292987, 4500071937, 4432965121], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17368122885, 8677530141, 54111781, 1099565740583, 30101956137, 1099515484723], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 140 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 140 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 140 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 140 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 140 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57213274137, 82564120621, 10103607369, 30923981077, 30689173781, 26276839701], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35218737509, 26629008741, 13106790801, 13240934829, 8912482733, 8795045293], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035510711, 1100018734519, 1099985181111, 1099951622603, 1099951623627, 1099850956259], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099850957283, 1099850958307, 17502341605, 8878857701, 1099733512703, 1099733513727], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099733514751, 4449741317, 1099549039147, 8610487853, 20556333, 20557357], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099515483699], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i18 : checks (tilesOf batches) 140 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 140 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 140 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 140 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 140 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57213408285, 78269221937, 1580849225, 30823386393, 26377497881, 17754081561], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35185251689, 22317267305, 1100102617511, 1100102618535, 1100102619559, 1100052288935], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8912416173, 8811821485, 1100069062063, 1099934915015, 13291262417, 8895635921], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834178023, 1099834179047, 1099834180071, 4416187901, 1099733513727, 4382630429], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [87665181, 87666205, 1099599295007, 1099549038123, 55852, 34363364913], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i21 : checks (tilesOf batches) 140 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 140 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 140 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 140 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 140 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [69846786081, 56945517625, 31125168433, 26612236593, 26360651057, 17636571461], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13291343173, 1100085841323, 1100069065131, 1100018734507, 1099968403883, 4567185845], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035506615, 1100035507639, 1100035508663, 9013075393, 8862083521, 4567184833], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750292987, 21679866365, 8811747837, 4432964101, 1099699958279, 1099699959303], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099699960327, 1099549039131, 1099549038119, 55844, 4332299817, 37334569], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55848, 55852, 30068400689, 17183572529, 8593643057, 1099515482675], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54832, 55856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i24 : checks (tilesOf batches) 140 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 140 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 140 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 140 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65619061797, 48389139517, 26763160901, 26478086469, 22015419717, 17569529169], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8962822481, 1100035510703, 1099985180079, 1099934849455, 1100052282803, 1100052283827], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100052284851, 1100052285875, 1100052286899, 8878859721, 4567183817, 1099951618507], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17452009969, 8811748849, 1099666403855, 1099666404879, 4382632465, 1099549039127], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549038115, 55840, 55844, 8627265065, 37333545, 37334569], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55848, 1099532259887, 54828, 55852, 54832, 55856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i27 : checks (tilesOf batches) 140 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 140 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 140 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 140 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [74041292841, 27098923073, 30974310689, 26461313313, 26243282209, 1100203282819], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100152952195, 1100102621571, 8946038165, 8811823509, 1100169727383, 13224155593], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8828529097, 1099934843343, 1099934844367, 1099934845391, 1099800622575, 1099800623599], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800624623, 21696575997, 13106713085, 4432964101, 1099699958279, 1099549039123], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4382630429, 1099549038111, 55836, 55840, 55844, 37333545], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [37334569, 1099549037099, 54824, 55848, 54828, 55852], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54832, 55856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i30 : checks (tilesOf batches) 140 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 140 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 140 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 140 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69763171373, 18559322181, 30806541609, 26343941417, 21914829097, 1100035512723], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8811823509, 1100169727383, 1100119396759, 1100069066135, 8962745781, 8845373877], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100035505591, 1099934843343, 1099934844367, 1099934845391, 17535829469, 13157046749], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767067127, 1099767068151, 1099767069175, 4382632465, 1099549039123, 1099549038111], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55836, 8660752929, 4365854241, 55840, 55844, 37334569], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099549037099, 54824, 55848, 54828, 55852, 54832], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i33 : checks (tilesOf batches) 140 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 140 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 140 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73957543985, 1530517577, 26612306197, 26360720661, 17703749909, 1100169726359], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100169727383, 1100119396759, 1100069066135, 8929193381, 8828598693, 1100102616487], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901360571, 13224153569, 8845304289, 1099850955235, 1099850956259, 1099850957283], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4432965113, 1099750290939, 55832, 87666205, 1099599295007, 1099532260895], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55836, 4365853217, 4332300833, 55840, 54820, 55844], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099549037099, 54824, 55848, 20556333, 54828, 55852], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [54832, 55856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i36 : checks (tilesOf batches) 140 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 140 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 140 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [61173308469, 1530517577, 22166347057, 26176173361, 9080262961, 13157119381], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100169725335, 1100169726359, 1100169727383, 1100035510699, 1099985180075, 1099901360571], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8945966553, 4634290649, 4516852185, 1099884509659, 1099884510683, 1099884511707], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099649626643, 1099649627667, 55832, 1099532260895, 55836, 55840], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [54820, 55844, 1099549037099, 54824, 55848, 20556333], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [20557357, 54828, 55852, 8593710641, 54832, 55856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i39 : checks (tilesOf batches) 140 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 140 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [52633774137, 22015420737, 21814165825, 1100371056963, 8811823509, 1100169727383], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100119396759, 1100069066135, 8862083525, 4567184837, 1099968396743, 1099934843343], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934844367, 1099934845391, 4449741321, 154776073, 1099683182091, 1099683183115], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099532261907, 55832, 1099549038111, 55836, 55840, 55844], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549037099, 54824, 55848, 54828, 55852, 3779121], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [3780145, 45616, 54832, 55856], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i42 : checks (tilesOf batches) 140 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 140 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤140) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 10 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤142 ∧ 4+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6969Allocation.Group10
end Z6969Source2339

-- Source: ProximityPrize.SubmissionLower.Low6969Mass11
section Z6969Source2340
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group11

private def m0 : MassCell 11 :=
  ⟨⟨2,5,8⟩,mass_cell 11 2 5 8 190 (by decide)
    (by decide +kernel) [4618363613502, 3810851996241, 3046518290073, 2393207797017, 1841801881809, 1383287724993, 1008758322921, 709412487753, 476554847457, 301595845809, 176051742393, 91544612601, 39802347633, 12658654497, 2053056009, 39599392] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 11 :=
  ⟨⟨2,6,16⟩,mass_cell 11 2 6 16 180 (by decide)
    (by decide +kernel) [4669890331228, 4079257488100, 3213178537686, 2471252232686, 1853985010886, 1349686952286, 946737256886, 633584244686, 398745355686, 230807149886, 118425307286, 50324627886, 15299031686, 2211558686, 25387968] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 11 :=
  ⟨⟨2,8,26⟩,mass_cell 11 2 8 26 162 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3551993795910, 2623286072262, 1871756478534, 1279009611462, 826506740550, 495565808070, 267361429062, 122924891334, 43144155462, 8763854790, 385891453, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 11 :=
  ⟨⟨3,9,30⟩,mass_cell 11 3 9 30 155 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3709656659028, 2722591766602, 1891532910118, 1249814516114, 772893923278, 436243655962, 215351424182, 85720123618, 22867835614, 2327827178, 2683796] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 11 :=
  ⟨⟨3,10,33⟩,mass_cell 11 3 10 33 149 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3799136565926, 2825070593795, 1917991971655, 1229045179627, 728541843695, 386603924563, 173163717655, 57963853115, 10557295807, 316656268, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 11 :=
  ⟨⟨1,12,37⟩,mass_cell 11 1 12 37 139 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3007786042176, 1962753668736, 1187948163520, 646594589952, 299653087296, 105818870656, 21522230976, 930461314, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 11 :=
  ⟨⟨3,14,41⟩,mass_cell 11 3 14 41 131 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3224714194218, 2038332375387, 1157039935623, 573551305299, 228560923071, 60586445259, 5968745847, 4701969] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 11 :=
  ⟨⟨1,15,42⟩,mass_cell 11 1 15 42 127 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3273632932226, 2060435984171, 1139661316323, 540023254787, 197643860363, 43287930747, 2363147342, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 11 :=
  ⟨⟨6,16,44⟩,mass_cell 11 6 16 44 125 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3360387485284, 2115400477756, 1122911833516, 503504140316, 169004930956, 31020554236, 959707777, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 11 :=
  ⟨⟨6,18,46⟩,mass_cell 11 6 18 46 120 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3432273956494, 2189391428386, 1095761884994, 445126759138, 123200222722, 13782874274, 33899982] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 11 :=
  ⟨⟨1,21,48⟩,mass_cell 11 1 21 48 113 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3480135050408, 2294038661575, 1065961140023, 373359491671, 73082956519, 2674381395, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 11 :=
  ⟨⟨2,24,50⟩,mass_cell 11 2 24 50 107 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2428895834464, 1034929505744, 307161641536, 39801348784, 228855118] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 11 :=
  ⟨⟨1,26,51⟩,mass_cell 11 1 26 51 105 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2502938502553, 1017331876627, 269453044735, 25218401803, 8589931] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 11 :=
  ⟨⟨1,29,52⟩,mass_cell 11 1 29 52 101 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2561597091100, 964095203799, 209238664959, 10539598482, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 11 :=
  ⟨⟨1,31,53⟩,mass_cell 11 1 31 53 99 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2645342606761, 968926873604, 188042582872, 6401766472, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 11 :=
  ⟨⟨1,35,54⟩,mass_cell 11 1 35 54 95 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2707708239984, 914257043590, 133039065442, 1314402581] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 11 :=
  ⟨⟨1,38,55⟩,mass_cell 11 1 38 55 93 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2788213585168, 915583108227, 110318691399, 350970357] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 11 :=
  ⟨⟨9,42,56⟩,mass_cell 11 9 42 56 90 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2856211688062, 884276615489, 79306007133, 14757463] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 11 :=
  ⟨⟨11,48,57⟩,mass_cell 11 11 48 57 87 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2924575070867, 846264565684, 47886700208, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 11 :=
  ⟨⟨64,4,43⟩,mass_cell 11 64 4 43 248 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3332687254347, 2156003942786, 1195248545618, 517161160825, 91209382867, 86887681, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 11 :=
  ⟨⟨59,32,55⟩,mass_cell 11 59 32 55 99 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2768395584574, 901805230788, 142821787812, 4379697234, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 11 :=
  ⟨⟨20,41,56⟩,mass_cell 11 20 41 56 91 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2852889398215, 881936509518, 84235919994, 55379385] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 11 :=
  ⟨⟨61,19,51⟩,mass_cell 11 61 19 51 121 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2462071581384, 989117072619, 301494284299, 56435406843, 3492948603, 1119734, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 11 :=
  ⟨⟨51,29,54⟩,mass_cell 11 51 29 54 103 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2694704881778, 929153515823, 181429036127, 10267653167, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 11 :=
  ⟨⟨67,36,56⟩,mass_cell 11 67 36 56 96 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2841467544130, 870901545116, 104147062716, 1133196458] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 11 :=
  ⟨⟨61,43,57⟩,mass_cell 11 61 43 57 91 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2915426870889, 839309871453, 63926757957, 16388903] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 11 :=
  ⟨⟨63,51,58⟩,mass_cell 11 63 51 58 87 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2985222870520, 801470108060, 33488811496, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 11 :=
  ⟨⟨49,26,53⟩,mass_cell 11 49 26 53 107 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2618347460226, 951150747761, 221334882029, 20692711817, 48605883] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 11 :=
  ⟨⟨74,30,55⟩,mass_cell 11 74 30 55 102 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2765764291629, 898898035200, 147720185064, 6148689232, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 11 :=
  ⟨⟨74,14,50⟩,mass_cell 11 74 14 50 140 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2399888485560, 1020482460912, 327411240168, 50480450436, 39367791, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 11 :=
  ⟨⟨64,21,52⟩,mass_cell 11 64 21 52 117 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2538605393425, 969975060841, 265416533097, 40033807953, 1390965409, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 11 :=
  ⟨⟨63,24,53⟩,mass_cell 11 63 24 53 110 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2615850563074, 950793644876, 228023236524, 25449632012, 292598766, 0] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 11 :=
  ⟨⟨66,27,54⟩,mass_cell 11 66 27 54 106 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2691289662473, 926231586035, 187434366379, 13609345315, 12232392] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 11 :=
  ⟨⟨75,35,56⟩,mass_cell 11 75 35 56 97 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2840113882986, 868785970939, 106415094139, 1503726854, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 11 :=
  ⟨⟨70,42,57⟩,mass_cell 11 70 42 57 91 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2914004192454, 837004809186, 66385730498, 46265470] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 11 :=
  ⟨⟨85,24,54⟩,mass_cell 11 85 24 54 111 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2690584269231, 924262448454, 186131392406, 12898468656, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 11 :=
  ⟨⟨88,16,52⟩,mass_cell 11 88 16 52 133 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2553849820321, 987099669160, 249565794904, 15020338873, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 11 :=
  ⟨⟨87,28,55⟩,mass_cell 11 87 28 55 105 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2765140554574, 897953562836, 148625246836, 6651521987, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 11 :=
  ⟨⟨81,21,53⟩,mass_cell 11 81 21 53 118 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2616634494798, 950585531285, 224572233533, 21757137956, 1581580, 0] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 11 :=
  ⟨⟨81,49,58⟩,mass_cell 11 81 49 58 88 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2983482245967, 799016592838, 36951387450, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 11 :=
  ⟨⟨97,47,58⟩,mass_cell 11 97 47 58 89 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2982376622510, 797773193505, 39942232785, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 11 :=
  ⟨⟨78,41,57⟩,mass_cell 11 78 41 57 92 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2913128453296, 836324006055, 68838623583, 97947043] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 11 :=
  ⟨⟨105,46,58⟩,mass_cell 11 105 46 58 90 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2981787836075, 795932122969, 40867394653, 369982] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 11 :=
  ⟨⟨104,15,53⟩,mass_cell 11 104 15 53 138 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2642683078672, 984783771065, 187759588510, 583049717, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 11 :=
  ⟨⟨103,25,55⟩,mass_cell 11 103 25 55 110 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2767934871347, 901739666311, 141970320839, 2798592755, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 11 :=
  ⟨⟨100,38,57⟩,mass_cell 11 100 38 57 95 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2911432634165, 833882727846, 73219957734, 336299775] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 11 :=
  ⟨⟨106,10,52⟩,mass_cell 11 106 10 52 168 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2597415588862, 1033605243666, 182835815482, 24553915, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 11 :=
  ⟨⟨82,34,56⟩,mass_cell 11 82 34 56 98 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2839575505407, 868782283218, 108612584386, 1877584723, 0] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 11 :=
  ⟨⟨112,45,58⟩,mass_cell 11 112 45 58 90 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2981551391666, 795735270052, 41773995928, 2545493] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 11 :=
  ⟨⟨113,36,57⟩,mass_cell 11 113 36 57 97 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2911115153713, 832364011624, 72791895528, 319969023, 0] (by decide +kernel) (by decide +kernel)⟩
private def m50 : MassCell 11 :=
  ⟨⟨113,12,53⟩,mass_cell 11 113 12 53 155 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2660082862678, 1001698728032, 149969745852, 35960, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m51 : MassCell 11 :=
  ⟨⟨119,44,58⟩,mass_cell 11 119 44 58 91 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2981294501131, 794777870568, 42153091464, 6165592] (by decide +kernel) (by decide +kernel)⟩
private def m52 : MassCell 11 :=
  ⟨⟨118,35,57⟩,mass_cell 11 118 35 57 98 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2911841341725, 835211081974, 72666930226, 199111244, 0] (by decide +kernel) (by decide +kernel)⟩
private def m53 : MassCell 11 :=
  ⟨⟨125,43,58⟩,mass_cell 11 125 43 58 92 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2981397522743, 795691131600, 42520325820, 8328262] (by decide +kernel) (by decide +kernel)⟩
private def m54 : MassCell 11 :=
  ⟨⟨89,33,56⟩,mass_cell 11 89 33 56 99 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2838959532919, 867529360922, 109450130734, 2138638531, 0] (by decide +kernel) (by decide +kernel)⟩
private def m55 : MassCell 11 :=
  ⟨⟨107,30,56⟩,mass_cell 11 107 30 56 103 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2839447962382, 867762658793, 107131391781, 1378076651, 0] (by decide +kernel) (by decide +kernel)⟩
private def m56 : MassCell 11 :=
  ⟨⟨112,29,56⟩,mass_cell 11 112 29 56 105 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2840424870028, 869633598171, 104809988667, 700026117, 0] (by decide +kernel) (by decide +kernel)⟩
private def m57 : MassCell 11 :=
  ⟨⟨131,42,58⟩,mass_cell 11 131 42 58 92 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2981483766869, 795926329845, 42249165353, 2149327] (by decide +kernel) (by decide +kernel)⟩
private def m58 : MassCell 11 :=
  ⟨⟨124,34,57⟩,mass_cell 11 124 34 57 99 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2911905971972, 833775377052, 69926550427, 28213269, 0] (by decide +kernel) (by decide +kernel)⟩
private def m59 : MassCell 11 :=
  ⟨⟨121,9,53⟩,mass_cell 11 121 9 53 178 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2679186821648, 1015387507190, 112608769575, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m60 : MassCell 11 :=
  ⟨⟨116,28,56⟩,mass_cell 11 116 28 56 106 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2842303160052, 874831811424, 103070590579, 241513057, 0] (by decide +kernel) (by decide +kernel)⟩
private def m61 : MassCell 11 :=
  ⟨⟨129,33,57⟩,mass_cell 11 129 33 57 100 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2912572397838, 834963943536, 67282624171, 4845, 0] (by decide +kernel) (by decide +kernel)⟩
private def m62 : MassCell 11 :=
  ⟨⟨119,21,55⟩,mass_cell 11 119 21 55 120 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2777663093574, 916937511054, 118286649789, 1028790, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m63 : MassCell 11 :=
  ⟨⟨133,54,59⟩,mass_cell 11 133 54 59 86 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 3047647416251, 753815711159, 18675517174, 0] (by decide +kernel) (by decide +kernel)⟩
private def m64 : MassCell 11 :=
  ⟨⟨132,4,53⟩,mass_cell 11 132 4 53 258 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2715725342677, 1035232137150, 63250683621, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m65 : MassCell 11 :=
  ⟨⟨132,24,56⟩,mass_cell 11 132 24 56 113 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2849447497900, 887363281244, 82602824744, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m66 : MassCell 11 :=
  ⟨⟨129,18,55⟩,mass_cell 11 129 18 55 129 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2787115770877, 928861746671, 94341792226, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m67 : MassCell 11 :=
  ⟨⟨137,41,58⟩,mass_cell 11 137 41 58 93 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2981553096973, 795448478214, 41216703894, 0] (by decide +kernel) (by decide +kernel)⟩
private def m68 : MassCell 11 :=
  ⟨⟨136,23,56⟩,mass_cell 11 136 23 56 116 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2851138615522, 888200392368, 75297979439, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m69 : MassCell 11 :=
  ⟨⟨137,31,57⟩,mass_cell 11 137 31 57 103 (by decide)
    (by decide +kernel) [4669890331228, 4250435360524, 3857880843452, 3491211738988, 2915113823278, 842548998404, 62444428506, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 11) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51, m52, m53, m54, m55, m56, m57, m58, m59, m60, m61, m62, m63, m64, m65, m66, m67, m68, m69]

end Low6969Allocation.Group11
end Z6969Source2340

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles11
section Z6969Source2341
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group11
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2315324421, 1040257033, 10435957771, 23741472781, 69896583189, 87110810669], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [10372108361, 35536965895, 39714961713, 35403424049, 35051242833, 39145023825], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13274556873, 13173963209, 8845445577, 1099750364663, 1099750365687, 25974834681], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13106782713, 1099666475531, 1099666476555, 1099666477579, 4416256529, 4365926929], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38708515363, 37405221, 37406245, 8610558505, 34363433517, 25773573677], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i51 : checks (tilesOf batches) 139 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [15184435209, 36157073425, 86925790237, 61458587705, 39748586773, 35336385813], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43607693589, 21847786873, 17653406133, 13274557877, 13173964213, 43406076353], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884580311, 1099884581335, 1099884582359, 1099884583383, 4433034749, 1099716806143], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099716807167, 30236243457, 17368192513, 8694443541, 4365924885, 38725441053], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099565810211, 8610556457, 20625961, 20626985, 25773571629], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i54 : checks (tilesOf batches) 139 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27936039949, 57246760985, 86976526377, 14532856901, 31007930669, 30773123373], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34850060589, 39463436653, 30873643373, 13224294821, 13106858405, 1099901360595], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17468856793, 8862150105, 1099851024863, 1099851025887, 1099851026911, 1099851027935], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4433033721, 1099733582331, 1099733583355, 21596047889, 43053819413, 4365921821], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4332369437, 1099582586399, 8644043297, 20624937, 20625961], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i49 : checks (tilesOf batches) 139 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36308332561, 74158461981, 65619336245, 35403355441, 30957599025, 34933872945], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26142686549, 1100421454167, 8878996913, 8778336689, 1100035577267, 13358438845], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13190670781, 8862218685, 1099834247651, 1099834248675, 1099834249699, 43255149029], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733583355, 1099700025859, 1099700026883, 1099700027907, 25924499977, 13039670793], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4449741321, 4416254473, 20623913, 20624937, 34363432493], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i52 : checks (tilesOf batches) 139 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44663716885, 82631157797, 35722410049, 31125235997, 35068021021, 39128247581], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100203349387, 1100203350411, 13291335057, 13190741393, 8845446545, 39178288561], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [30588495281, 17603004873, 13240999369, 1099901357523, 1099901358547, 1099851021791], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099851022815, 1099851023839, 1099851024863, 4516916725, 4433032693, 1099599361563], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099599362587, 17250747933, 8644042273, 4349143585, 3846701], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57246894105, 86842376237, 5875815497, 35168682257, 34933875985, 17804413201], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39429884269, 30773047661, 13308110237, 13157119389, 8828667293, 1100069130667], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951691207, 1099951692231, 17502409173, 1099867801051, 1099867802075, 1099867803099], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4483364321, 1099834244579, 1099834245603, 4466517509, 4433030661, 1099632915987], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099632917011, 25857389081, 17267527193, 4332298789, 38675106345, 20622889], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [20623913], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i18 : checks (tilesOf batches) 139 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 139 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 139 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 139 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 139 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57247028253, 82547477553, 30840163605, 30638976277, 13543066901, 35151762801], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26494859633, 13190671777, 8862219681, 1100102683043, 1100018798007, 1100018799031], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018800055, 1100002023863, 13274551761, 8895702481, 1099817467367, 1099817468391], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817469415, 4466586093, 1099783911919, 87732761, 1099599361563, 4365854237], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [70954525, 21528869409, 12939006497, 1099515550255], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 139 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 139 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 139 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 139 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 139 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61441466401, 65485118517, 26377493813, 26176239925, 4869248309, 35168608605], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22250227037, 8878930329, 8811890073, 1100136239515, 1099968468419, 1099934915011], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13207444937, 8811818441, 1099901355475, 1099901356499, 1099901357523, 1099834243555], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834244579, 1099834245603, 4433030657, 1099700024835, 17267525145, 8677595673], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4382631449, 34413765153, 37400101, 37401125, 1099532327467], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 139 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 139 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 139 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 139 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65619061797, 48422759485, 30974307653, 26478153029, 22015486277, 13291340121], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8962888025, 1100018799031, 1100002022839, 1099968469431, 1099985240511, 1099985241535], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985242559, 1099985243583, 8862149065, 4567250377, 1099934907851, 17435299313], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8811815409, 4382699021, 1099649693199, 1099649694223, 30118800929, 37400101], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [37401125, 1099532327463, 4315521577, 4315589161, 54828, 55852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [74041292841, 27115765825, 30974310689, 26494933281, 26276902177, 1100220125575], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100203349383, 1100153018759, 8912483741, 8811889053, 1100119461279, 13240998353], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8828594641, 1099884577239, 1099884578263, 1099884579287, 1099783910895, 1099783911919], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783912943, 25974831613, 13090002429, 4433029645, 138064397, 1099549104675], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4315588137, 54828, 55852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 139 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69763171373, 18576164933, 26662634793, 26377494825, 26176240937, 8912551309], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100153014679, 1100153015703, 1100153016727, 1100119463319, 1100069132695, 9029919165], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8862150077, 4567251389, 1099851022815, 1099851023839, 17368122881, 13039671809], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4433030657, 1099700024835, 1099700025859, 1099700026883, 1099549104671, 37400101], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [37401125, 8610486825, 4315588137, 54824, 55848, 54828], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73957543985, 1530517577, 30840230165, 26360787221, 13475958037, 8929259941], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8828665253, 1100085905831, 1100085906855, 1100085907879, 1100052354471, 1099918137787], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17535963601, 8895702481, 1099834244579, 1099834245603, 1099834246627, 4416254457], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733580283, 87732761, 1099599361563, 4365854237, 4332367389, 1099549104671], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12905452073, 4315521577, 20622889, 54824, 55848, 54828], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [55852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 139 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65434786869, 26427825449, 26209794345, 4886025513, 8895707541, 8811890069], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100153016727, 1099968468411, 1099918137787, 13240999369, 8828595657, 1099918132687], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918133711, 1099918134735, 1099834243555, 1099834244579, 1099834245603, 4433030661], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099683247623, 1099549104671, 8644042273, 4349143585, 20623913, 54824], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55848, 54828, 55852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [52667394105, 22015486281, 17552752969, 4751807817, 4584030629, 1100085905831], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100085906855, 1100085907879, 1099968468411, 1099918137787, 8878926285, 4567250381], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918130639, 1099783913967, 1099783914991, 1099632915987, 1099632917011, 4399475221], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [104509973, 1099549104671, 54824, 55848, 54828, 55852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i42 : checks (tilesOf batches) 139 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 139 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((11 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 11 where
  orders := orders
  covers := by
    intro a ha box
    change 3+a.b≤142 ∧ 4+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6969Allocation.Group11
end Z6969Source2341

-- Source: ProximityPrize.SubmissionLower.Low6969Mass12
section Z6969Source2342
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group12

private def m0 : MassCell 12 :=
  ⟨⟨2,5,10⟩,mass_cell 12 2 5 10 192 (by decide)
    (by decide +kernel) [4640126133291, 3863748788439, 3081805035135, 2415940383399, 1855971741327, 1391942765175, 1014123859359, 713012176455, 479331617199, 304032830487, 178293213375, 93516911079, 41334816975, 13604572599, 2410567647, 66799858] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 12 :=
  ⟨⟨2,6,17⟩,mass_cell 12 2 6 17 181 (by decide)
    (by decide +kernel) [4660674413428, 4090156888322, 3222304671899, 2471739204503, 1849832866227, 1343752319471, 940899234635, 628910290119, 395657172323, 229246575647, 118020202491, 50554763255, 15661976339, 2388568143, 35610098, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 12 :=
  ⟨⟨2,8,27⟩,mass_cell 12 2 8 27 163 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3568895457666, 2634154620908, 1876498350476, 1280929330220, 827590766540, 496769193068, 268894470668, 124539787436, 44421658700, 9399927020, 477859382, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 12 :=
  ⟨⟨3,9,31⟩,mass_cell 12 3 9 31 156 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3711292618660, 2739500600713, 1900915647497, 1255368803545, 776792416441, 439498475369, 218178611113, 87904096057, 24125844185, 2674411081, 6425745] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 12 :=
  ⟨⟨1,11,36⟩,mass_cell 12 1 11 36 145 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3815250676646, 2939849593378, 1962242049238, 1226989075498, 701378984158, 351650327218, 142991896678, 39542724538, 4392082798, 10058146, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 12 :=
  ⟨⟨1,12,38⟩,mass_cell 12 1 12 38 140 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3040815749040, 1985194406128, 1203923438640, 658256275824, 307860900016, 110819846640, 23630204208, 1203896365, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 12 :=
  ⟨⟨1,15,43⟩,mass_cell 12 1 15 43 128 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3283702210666, 2097054177182, 1165350888186, 557352854414, 207913311194, 47666056542, 3025451162, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 12 :=
  ⟨⟨1,16,44⟩,mass_cell 12 1 16 44 125 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3321979329215, 2115882673810, 1139772849330, 518451786450, 176462333170, 32817737490, 1027109665, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 12 :=
  ⟨⟨1,18,46⟩,mass_cell 12 1 18 46 120 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3389400073072, 2182942284546, 1108632293778, 456784188130, 128153093874, 14515062210, 36096207] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 12 :=
  ⟨⟨1,20,48⟩,mass_cell 12 1 20 48 115 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3434661785024, 2291175656824, 1103128209976, 413497528312, 94832856760, 5924025976, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 12 :=
  ⟨⟨3,21,49⟩,mass_cell 12 3 21 49 114 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2353166808264, 1097878553812, 390853541760, 80478132108, 3588320948, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 12 :=
  ⟨⟨5,24,51⟩,mass_cell 12 5 24 51 108 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2492430004383, 1071935038180, 325227069940, 45636931844, 427657872] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 12 :=
  ⟨⟨5,26,52⟩,mass_cell 12 5 26 52 106 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2562039527590, 1056456246772, 287296229044, 29889640756, 37184344] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 12 :=
  ⟨⟨1,29,53⟩,mass_cell 12 1 29 53 102 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2629670673838, 1029417004736, 235708583948, 14184882510, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 12 :=
  ⟨⟨1,32,54⟩,mass_cell 12 1 32 54 98 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2695687530022, 1002834274602, 190644672234, 6035925852, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 12 :=
  ⟨⟨1,35,55⟩,mass_cell 12 1 35 55 96 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2766671645467, 994643358513, 157695160857, 2360872659] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 12 :=
  ⟨⟨1,39,56⟩,mass_cell 12 1 39 56 93 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2833067190195, 974223681015, 118890576207, 414317647] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 12 :=
  ⟨⟨1,44,57⟩,mass_cell 12 1 44 57 90 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2897312133260, 951375056874, 82468727898, 5300973] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 12 :=
  ⟨⟨17,49,58⟩,mass_cell 12 17 49 58 88 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2956112668023, 922583806111, 55444062135, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 12 :=
  ⟨⟨63,4,44⟩,mass_cell 12 63 4 44 249 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3333385246392, 2191842773868, 1220210261420, 533332041924, 98262255914, 134279606, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 12 :=
  ⟨⟨60,15,50⟩,mass_cell 12 60 15 50 135 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2389492395370, 1062450625598, 381494545978, 93519050974, 8578869978, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 12 :=
  ⟨⟨52,26,54⟩,mass_cell 12 52 26 54 108 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2678282674008, 999376206855, 235036713795, 23354634975, 99018925] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 12 :=
  ⟨⟨31,36,56⟩,mass_cell 12 31 36 56 96 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2824755209246, 968217779176, 137864273256, 1857681908] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 12 :=
  ⟨⟨65,44,58⟩,mass_cell 12 65 44 58 91 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2950512956504, 913299104206, 70644633598, 29152655] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 12 :=
  ⟨⟨65,32,56⟩,mass_cell 12 65 32 56 100 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2817531120076, 958460803032, 153931292040, 5408519470, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 12 :=
  ⟨⟨32,41,57⟩,mass_cell 12 32 41 57 92 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2891000908256, 945178214814, 97040017242, 184455900] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 12 :=
  ⟨⟨48,30,55⟩,mass_cell 12 48 30 55 102 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2750457412442, 981474799447, 189709852875, 10169564703, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 12 :=
  ⟨⟨59,38,57⟩,mass_cell 12 59 38 57 95 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2886540147736, 938828903726, 108862192334, 873416215] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 12 :=
  ⟨⟨70,27,55⟩,mass_cell 12 70 27 55 107 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2746560439593, 976374439713, 197293294297, 14715254961, 24597645] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 12 :=
  ⟨⟨72,20,53⟩,mass_cell 12 72 20 53 120 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2603030228602, 1009127505576, 271499338344, 37754063400, 573138158, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 12 :=
  ⟨⟨64,53,59⟩,mass_cell 12 64 53 59 86 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 3010149069595, 887266208886, 37015031865, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 12 :=
  ⟨⟨77,26,55⟩,mass_cell 12 77 26 55 109 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2745419632428, 972686080120, 195680109640, 14663628760, 32584680, 0] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 12 :=
  ⟨⟨81,42,58⟩,mass_cell 12 81 42 58 92 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2949284014924, 910982211430, 75321867974, 127386903] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 12 :=
  ⟨⟨66,24,54⟩,mass_cell 12 66 24 54 111 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2675665496650, 995504373664, 237786385504, 26642878496, 344953490, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 12 :=
  ⟨⟨75,36,57⟩,mass_cell 12 75 36 57 97 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2884521180569, 934612457098, 113911487674, 1589694413, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 12 :=
  ⟨⟨73,52,59⟩,mass_cell 12 73 52 59 87 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 3009649402590, 885810006598, 38745558294, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 12 :=
  ⟨⟨88,16,53⟩,mass_cell 12 88 16 53 134 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2619108972644, 1036280569860, 263443703556, 15650396160, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 12 :=
  ⟨⟨91,28,56⟩,mass_cell 12 91 28 56 106 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2816304116082, 956359411944, 156685832456, 6494587636, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 12 :=
  ⟨⟨83,21,54⟩,mass_cell 12 83 21 54 119 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2677331760136, 996743051266, 232497264214, 20407234761, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 12 :=
  ⟨⟨89,50,59⟩,mass_cell 12 89 50 59 88 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 3009012657652, 885076444836, 42134871060, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 12 :=
  ⟨⟨97,49,59⟩,mass_cell 12 97 49 59 89 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 3008680742167, 883707767655, 43406765215, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 12 :=
  ⟨⟨89,41,58⟩,mass_cell 12 89 41 58 93 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2948632609725, 908419686141, 76631507589, 201774487] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 12 :=
  ⟨⟨105,48,59⟩,mass_cell 12 105 48 59 89 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 3008339735862, 881627220576, 44288746192, 122229] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 12 :=
  ⟨⟨105,15,54⟩,mass_cell 12 105 15 54 139 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2699105592878, 1032735010993, 195063261940, 485201980, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 12 :=
  ⟨⟨103,39,58⟩,mass_cell 12 103 39 58 95 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2948032084719, 906266531217, 78345001041, 349082987] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 12 :=
  ⟨⟨109,38,58⟩,mass_cell 12 109 38 58 96 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2948090693352, 906936830030, 78806286902, 376356358] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 12 :=
  ⟨⟨112,47,59⟩,mass_cell 12 112 47 59 90 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 3008188726560, 881189336378, 45187793318, 1539356] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 12 :=
  ⟨⟨116,6,53⟩,mass_cell 12 116 6 53 217 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2680777007714, 1103641519721, 138395188057, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 12 :=
  ⟨⟨117,16,55⟩,mass_cell 12 117 16 55 136 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2769531837590, 1019727988636, 146284705627, 211876, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 12 :=
  ⟨⟨119,46,59⟩,mass_cell 12 119 46 59 91 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 3008030013550, 880101981242, 45604541722, 4439968] (by decide +kernel) (by decide +kernel)⟩
private def m50 : MassCell 12 :=
  ⟨⟨89,34,57⟩,mass_cell 12 89 34 57 99 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2883561802267, 932401865786, 116507472826, 2202365701, 0] (by decide +kernel) (by decide +kernel)⟩
private def m51 : MassCell 12 :=
  ⟨⟨95,33,57⟩,mass_cell 12 95 33 57 100 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2883653732525, 933226996675, 117249547579, 2321891013, 0] (by decide +kernel) (by decide +kernel)⟩
private def m52 : MassCell 12 :=
  ⟨⟨113,12,54⟩,mass_cell 12 113 12 54 156 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2714682057011, 1056874680208, 164226734923, 487635, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m53 : MassCell 12 :=
  ⟨⟨125,45,59⟩,mass_cell 12 125 45 59 91 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 3008064164966, 880855236334, 46059201674, 7246856] (by decide +kernel) (by decide +kernel)⟩
private def m54 : MassCell 12 :=
  ⟨⟨112,30,57⟩,mass_cell 12 112 30 57 104 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2884360617361, 933589797977, 111987354749, 834042817, 0] (by decide +kernel) (by decide +kernel)⟩
private def m55 : MassCell 12 :=
  ⟨⟨115,37,58⟩,mass_cell 12 115 37 58 97 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2948132024754, 906833032866, 78254466062, 307012252, 0] (by decide +kernel) (by decide +kernel)⟩
private def m56 : MassCell 12 :=
  ⟨⟨128,26,57⟩,mass_cell 12 128 26 57 111 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2889274058361, 949242260729, 97806634981, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m57 : MassCell 12 :=
  ⟨⟨125,35,58⟩,mass_cell 12 125 35 58 99 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2948955659674, 910907543788, 76425215867, 35794173, 0] (by decide +kernel) (by decide +kernel)⟩
private def m58 : MassCell 12 :=
  ⟨⟨110,24,56⟩,mass_cell 12 110 24 56 113 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2820770326954, 965970337280, 144161819407, 849089017, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m59 : MassCell 12 :=
  ⟨⟨131,44,59⟩,mass_cell 12 131 44 59 92 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 3008092013006, 881034107668, 45944498932, 4390471] (by decide +kernel) (by decide +kernel)⟩
private def m60 : MassCell 12 :=
  ⟨⟨121,21,56⟩,mass_cell 12 121 21 56 121 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2826872804157, 979170541413, 124713429140, 163185, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m61 : MassCell 12 :=
  ⟨⟨136,24,57⟩,mass_cell 12 136 24 57 114 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2891604680508, 952510105036, 84513563670, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m62 : MassCell 12 :=
  ⟨⟨130,34,58⟩,mass_cell 12 130 34 58 100 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2949347183443, 911925217557, 73774596643, 58905, 0] (by decide +kernel) (by decide +kernel)⟩
private def m63 : MassCell 12 :=
  ⟨⟨137,43,59⟩,mass_cell 12 137 43 59 93 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 3008113525036, 880611438907, 45148479840, 0] (by decide +kernel) (by decide +kernel)⟩
private def m64 : MassCell 12 :=
  ⟨⟨136,9,55⟩,mass_cell 12 136 9 55 180 (by decide)
    (by decide +kernel) [4660674413428, 4226248577780, 3821463902068, 3445052725492, 2796227922093, 1049088922653, 78132463615, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 12) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51, m52, m53, m54, m55, m56, m57, m58, m59, m60, m61, m62, m63, m64]

end Low6969Allocation.Group12
end Z6969Source2342

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles12
section Z6969Source2343
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group12
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2298547205, 1040257033, 10872296459, 27784847373, 86908812309, 78604898353], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35587363079, 44060261641, 39715236105, 30722855273, 30555156841, 9231389033], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13140406753, 8828731873, 8744848865, 43188106737, 1099666545159, 34497718793], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [25907858953, 13022964233, 1099649764875, 1099649765899, 1099649766923, 38742286869], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4349215261, 54250013, 8627403297], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i51 : checks (tilesOf batches) 138 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤138) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [19127146505, 36291488785, 86976253981, 57214018617, 39748718881, 35286120737], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39329570081, 21814297989, 17586363845, 13207515589, 13106921925, 8694518233], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [38976952797, 43255284193, 1099733651959, 1099733652983, 1099733654007, 4433101309], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700095487, 1099700096511, 30236310017, 17351481857, 8677732885, 4365991445], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549099555, 34363502121, 8593845801, 3915305, 3916329], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i46 : checks (tilesOf batches) 138 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 138 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤138) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [28019991565, 57246760985, 86993369129, 14549699653, 30991153457, 30789966129], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34866903345, 43674583405, 30856932717, 13190740397, 13106923949, 1099867871703], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17468922337, 8862215649, 1099800758759, 1099800759783, 1099800760807, 1099800761831], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4466653689, 4399546873, 21579337233, 1099599430167, 1099599431191, 43003626013], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8610623013, 20691493, 20692517, 42953287209, 8593778217], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i49 : checks (tilesOf batches) 138 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤138) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36358729745, 78419940381, 61357989945, 35436975401, 30991153449, 35001047337], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21881339233, 4835759457, 17552808389, 8946101701, 8828664261, 8761624005], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934978503, 1099800761831, 1099800762855, 43188105713, 1099750426099, 1099750427123], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750428147, 4399544833, 1099683316227, 25907788297, 17301149193, 4349144605], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4332434973, 1099565874719, 4332366369, 12888741417, 8593778217, 3913257], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [3914281], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i52 : checks (tilesOf batches) 138 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤138) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44714114069, 74175506469, 44295630909, 31058258237, 30773119293, 30555089213], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13207587201, 1100220193155, 13224290741, 8862218677, 8795178421, 43406212541], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884646867, 1099884647891, 21713488361, 13090071017, 1099783980523, 1099783981547], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783982571, 4399544825, 1099716870651, 4382700041, 87800341, 1099599429143], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8644108829, 4349144605, 37467681, 21495450149], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 138 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 138 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 138 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 138 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 138 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤138) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57246894105, 86859218989, 5909435465, 35185525013, 34950718741, 17821255957], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39446727021, 30806667629, 17519256997, 13123631525, 1100018862515, 1100018863539], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018864563, 1099901425103, 1099901426127, 17468854749, 4483430881, 1099817533923], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817534947, 8778327545, 4433031673, 1099616205331, 1099616206355, 54243869], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [54244893, 30102090273, 17200484901, 4298810921, 4298878505], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 138 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 138 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 138 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 138 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 138 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤138) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57280648221, 82564320305, 30857006361, 30622199065, 13526289689, 39329355129], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26444594553, 13224291745, 8862219681, 8795179425, 1100002088375, 1100002089399], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867867607, 1099867868631, 1099867869655, 13224286681, 8845437401, 1099800755687], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800756711, 1099800757735, 4433098229, 4365920793, 4332433945, 1099582650907], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38708729373, 21528935965, 12939073053, 20689445, 20690469], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 138 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 138 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 138 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 138 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 138 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤138) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65686167585, 61223772217, 26327228737, 21898116417, 4852536641, 35218940241], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26511705425, 8811888041, 1100052416939, 1100052417963, 1100052418987, 13190734281], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8811885001, 1099918202315, 1099918203339, 1099817532899, 1099817533923, 1099817534947], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4382700033, 1099683314179, 21629601285, 8744771077, 4382698005, 71021081], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [71022105, 34397053473], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 138 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 138 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 138 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 138 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤138) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [78336257061, 35655366721, 31175699741, 26645925149, 26394339613, 13140411769], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100253746555, 1100253747579, 8979655093, 8845440437, 4550541749, 1099985308091], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985309115, 1099985310139, 17418522097, 8828658161, 4416321013, 1099733646839], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733647863, 1099733648887, 4349144597, 87799317, 1099599428119, 4315655717], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [30068534825], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 138 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 138 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 138 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 138 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤138) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78302771241, 22887973957, 31041485081, 26562107673, 26344076569, 1100119527835], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100119528859, 1100119529883, 8912549285, 8811954597, 1100069195175, 13224286681], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8845437401, 1099834311135, 1099834312159, 1099834313183, 4416321013, 1099733646839], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [25924565509, 13039736325, 87799317, 1099599428119, 4365920793, 71021081], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 138 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 138 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 138 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 138 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤138) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [78269285421, 10086961225, 30957667605, 30672528661, 21998781717, 8845510037], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13291398569, 8895772073, 8795177385, 1100018864563, 1100018865587, 1100018866611], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867868631, 1099834311135, 1099834312159, 1099834313183, 21730264557, 13106847213], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4416321013, 1099733646839, 4382699021, 87799317, 1099599428119, 8610553381], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4315589157, 20689445], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 138 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 138 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 138 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤138) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [78235799601, 30857007377, 30622265617, 9248100625, 13207515545, 8828666265], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100119526811, 1100018864563, 1100018865587, 1100018866611, 17535963601, 8946099665], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867865559, 1099867866583, 1099867867607, 4483363305, 1099783977451, 1099783978475], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4332433945, 20689445, 20690469, 17183707689, 4298810921, 4298878505], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 138 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 138 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 138 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤138) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65451629621, 30655749421, 21965225261, 4902868269, 8828665253, 1100069194151], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100069195175, 1100069196199, 13324950973, 8929324477, 8778332605, 1099951756739], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934980547, 1099817534947, 4416322029, 1099767202287, 1099632982543, 1099632983567], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4382699025, 104576529, 8593776169, 4298811945, 3912233, 55848], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 138 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 138 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤138) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [52667394105, 22049106249, 21814231369, 1100455074123, 8811889053, 1100102749599], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102750623, 1100102751647, 8878991829, 4533695957, 4466654677, 1099867866583], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867867607, 1099683315203, 1099683316227, 104576529, 1099616205331, 4349143581], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4332433949, 3912233], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i42 : checks (tilesOf batches) 138 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 138 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤138) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((12 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 12 where
  orders := orders
  covers := by
    intro a ha box
    change 4+a.b≤142 ∧ 4+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6969Allocation.Group12
end Z6969Source2343

-- Source: ProximityPrize.SubmissionLower.Low6969Mass13
section Z6969Source2344
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group13

private def m0 : MassCell 13 :=
  ⟨⟨2,5,11⟩,mass_cell 13 2 5 11 193 (by decide)
    (by decide +kernel) [4641220278784, 3879151726290, 3084575393742, 2410801955754, 1846578405030, 1380999414786, 1003507338750, 703892211162, 472291746774, 299191340850, 175424069166, 92170688010, 40959634182, 13667024994, 2516658270, 81404064, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 13 :=
  ⟨⟨2,6,18⟩,mass_cell 13 2 6 18 182 (by decide)
    (by decide +kernel) [4651458495628, 4096898108156, 3230984993348, 2471622551364, 1844996180420, 1337116683716, 934395760452, 623646005828, 392080911044, 227314863300, 117363145796, 50641937732, 15968314308, 2560246724, 48042502, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 13 :=
  ⟨⟨3,9,32⟩,mass_cell 13 3 9 32 157 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3707085631839, 2755645496272, 1909448262972, 1260102447240, 779983866100, 442212434112, 220652163372, 89911163512, 25341641700, 3039902640, 12866768, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 13 :=
  ⟨⟨1,11,37⟩,mass_cell 13 1 11 37 146 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 2965962736969, 1979155295881, 1238730432073, 710113327945, 358239277897, 147553688329, 42012077641, 5080076233, 21394307, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 13 :=
  ⟨⟨1,12,39⟩,mass_cell 13 1 12 39 141 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3066154537883, 2006650756436, 1219048646708, 669302079252, 315723178484, 115718099156, 25787026356, 1524175508, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 13 :=
  ⟨⟨2,15,44⟩,mass_cell 13 2 15 44 129 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3283822560536, 2125240126904, 1181733765500, 568076196384, 214991669732, 51260649992, 3719815884, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 13 :=
  ⟨⟨1,16,45⟩,mass_cell 13 1 16 45 126 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3317787289577, 2156322755340, 1167786916076, 536893784012, 186878687148, 36774457484, 1419630196, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 13 :=
  ⟨⟨1,18,47⟩,mass_cell 13 1 18 47 121 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3371373390516, 2233404237625, 1142746301181, 477902974881, 138574745125, 17249398665, 82472855, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 13 :=
  ⟨⟨1,20,49⟩,mass_cell 13 1 20 49 116 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2352383578456, 1143489113368, 437034135256, 104921921176, 7589569624, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 13 :=
  ⟨⟨5,21,50⟩,mass_cell 13 5 21 50 115 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2413723171685, 1129430052685, 407858553685, 87899674685, 4664884249, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 13 :=
  ⟨⟨8,24,52⟩,mass_cell 13 8 24 52 109 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2545865246472, 1108930140724, 342853248068, 51644216404, 716990296, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 13 :=
  ⟨⟨9,26,53⟩,mass_cell 13 9 26 53 107 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2610957825122, 1095779179767, 304651975323, 34798767519, 102357821] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 13 :=
  ⟨⟨1,30,54⟩,mass_cell 13 1 30 54 101 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2671909457855, 1057163758139, 235736416455, 13074946433, 0] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 13 :=
  ⟨⟨1,32,55⟩,mass_cell 13 1 32 55 99 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2744592290374, 1077210847548, 218254519260, 8729870526, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 13 :=
  ⟨⟨1,36,56⟩,mass_cell 13 1 36 56 96 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2802691385946, 1045776671508, 165334945140, 2451294782] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 13 :=
  ⟨⟨8,39,57⟩,mass_cell 13 8 39 57 94 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2863719471726, 1046673293077, 138281839157, 896162679] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 13 :=
  ⟨⟨11,44,58⟩,mass_cell 13 11 44 58 91 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2919731411877, 1031820337844, 99136175732, 52139718] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 13 :=
  ⟨⟨9,51,59⟩,mass_cell 13 9 51 59 88 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2971240310776, 1019053326911, 62186012517, 0] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 13 :=
  ⟨⟨62,4,45⟩,mass_cell 13 62 4 45 250 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3325500120022, 2226280140858, 1244039965418, 548600288313, 104979346849, 193033401, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 13 :=
  ⟨⟨66,16,52⟩,mass_cell 13 66 16 52 133 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2523383012247, 1084611607404, 356298593788, 70913136012, 2460007975, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 13 :=
  ⟨⟨48,27,55⟩,mass_cell 13 48 27 55 107 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2726525499957, 1050730497111, 245090191447, 23237580255, 63023337] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 13 :=
  ⟨⟨38,36,57⟩,mass_cell 13 38 36 57 97 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2857301697168, 1033549281266, 153829563618, 2825734241, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 13 :=
  ⟨⟨35,32,56⟩,mass_cell 13 35 32 56 100 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2795875338961, 1048171023246, 197554080126, 8557416443, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 13 :=
  ⟨⟨63,33,57⟩,mass_cell 13 63 33 57 100 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2853458635748, 1024200831296, 163991464212, 5613214805, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 13 :=
  ⟨⟨50,40,58⟩,mass_cell 13 50 40 58 94 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2914693817007, 1018416017900, 115716256508, 693878128] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 13 :=
  ⟨⟨40,48,59⟩,mass_cell 13 40 48 59 89 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2968934376496, 1010396779396, 71661318548, 367719] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 13 :=
  ⟨⟨52,30,56⟩,mass_cell 13 52 30 56 103 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2791867488554, 1040065442998, 204919917998, 12272666086, 5372] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 13 :=
  ⟨⟨66,38,58⟩,mass_cell 13 66 38 58 96 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2913351468315, 1015208872118, 122322364262, 1385398021] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 13 :=
  ⟨⟨67,45,59⟩,mass_cell 13 67 45 59 91 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2967318365128, 1003245620940, 79796004984, 51720504] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 13 :=
  ⟨⟨58,20,53⟩,mass_cell 13 58 20 53 120 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2587392128420, 1065810611692, 322392359692, 59536223020, 3595679308, 1993588] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 13 :=
  ⟨⟨55,26,55⟩,mass_cell 13 55 26 55 109 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2725488585369, 1049901282595, 248613037615, 25894163035, 169353050, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 13 :=
  ⟨⟨67,21,54⟩,mass_cell 13 67 21 54 119 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2657489449274, 1059560127827, 288643982115, 42662532803, 1247650125, 0] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 13 :=
  ⟨⟨73,27,56⟩,mass_cell 13 73 27 56 108 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2789401342503, 1034567839521, 209594894241, 15959147689, 37936952] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 13 :=
  ⟨⟨68,24,55⟩,mass_cell 13 68 24 55 112 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2724348159290, 1047988594672, 250750993760, 28300084432, 388678888, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 13 :=
  ⟨⟨79,53,60⟩,mass_cell 13 79 53 60 87 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 3012229139918, 992947795175, 46124471347, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 13 :=
  ⟨⟨84,21,55⟩,mass_cell 13 84 21 55 120 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2726510385468, 1051520827278, 245073248778, 20365201683, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 13 :=
  ⟨⟨77,31,57⟩,mass_cell 13 77 31 57 103 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2852342085716, 1021190579198, 167232558474, 7130295590, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 13 :=
  ⟨⟨87,52,60⟩,mass_cell 13 87 52 60 88 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 3012101090353, 991937001452, 47699696908, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 13 :=
  ⟨⟨89,16,54⟩,mass_cell 13 89 16 54 135 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2669375090133, 1080263518818, 271073024178, 14194927868, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 13 :=
  ⟨⟨79,26,56⟩,mass_cell 13 79 26 56 110 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2789382915222, 1034312160145, 209170119757, 15714217129, 24361079, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 13 :=
  ⟨⟨95,51,60⟩,mass_cell 13 95 51 60 89 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 3011971109472, 990349123475, 48980389875, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 13 :=
  ⟨⟨83,43,59⟩,mass_cell 13 83 43 59 93 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2966591812769, 999360742597, 83792357261, 171875722] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 13 :=
  ⟨⟨103,50,60⟩,mass_cell 13 103 50 60 89 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 3011839191373, 988158671577, 49893049701, 60657] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 13 :=
  ⟨⟨97,41,59⟩,mass_cell 13 97 41 59 94 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2966235204755, 997738198521, 86589032721, 345167073] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 13 :=
  ⟨⟨81,36,58⟩,mass_cell 13 81 36 58 98 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2912302848090, 1011058778220, 125893829068, 2133161171, 0] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 13 :=
  ⟨⟨105,15,55⟩,mass_cell 13 105 15 55 140 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2744134974921, 1090505931576, 210142945277, 633291789, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 13 :=
  ⟨⟨104,40,59⟩,mass_cell 13 104 40 59 95 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2966045071611, 995804077148, 86719117388, 405243432] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 13 :=
  ⟨⟨110,39,59⟩,mass_cell 13 110 39 59 96 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2966052089350, 996033212860, 86957751208, 422809336] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 13 :=
  ⟨⟨110,49,60⟩,mass_cell 13 110 49 60 90 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 3011775899914, 987579058236, 50865539816, 1215074] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 13 :=
  ⟨⟨94,34,58⟩,mass_cell 13 94 34 58 100 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2911957515241, 1009623477292, 127194355892, 2542380376, 0] (by decide +kernel) (by decide +kernel)⟩
private def m50 : MassCell 13 :=
  ⟨⟨116,38,59⟩,mass_cell 13 116 38 59 97 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2966052632584, 995592213594, 86203479186, 338483687, 0] (by decide +kernel) (by decide +kernel)⟩
private def m51 : MassCell 13 :=
  ⟨⟨116,48,60⟩,mass_cell 13 116 48 60 90 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 3011781698140, 988748109652, 51965457956, 4268523] (by decide +kernel) (by decide +kernel)⟩
private def m52 : MassCell 13 :=
  ⟨⟨116,11,55⟩,mass_cell 13 116 11 55 164 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2759311384165, 1117597666755, 164987760736, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m53 : MassCell 13 :=
  ⟨⟨115,6,54⟩,mass_cell 13 115 6 54 218 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2721657022585, 1163739767345, 161217852875, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m54 : MassCell 13 :=
  ⟨⟨100,33,58⟩,mass_cell 13 100 33 58 101 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2911955686807, 1009285515899, 126566630099, 2379543225, 0] (by decide +kernel) (by decide +kernel)⟩
private def m55 : MassCell 13 :=
  ⟨⟨123,47,60⟩,mass_cell 13 123 47 60 91 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 3011715283792, 987109925788, 52024034224, 7886185] (by decide +kernel) (by decide +kernel)⟩
private def m56 : MassCell 13 :=
  ⟨⟨115,30,58⟩,mass_cell 13 115 30 58 105 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2913063714689, 1014424460753, 121513297461, 604275694, 0] (by decide +kernel) (by decide +kernel)⟩
private def m57 : MassCell 13 :=
  ⟨⟨121,37,59⟩,mass_cell 13 121 37 59 98 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2966253272103, 997566167010, 85706829126, 196299453, 0] (by decide +kernel) (by decide +kernel)⟩
private def m58 : MassCell 13 :=
  ⟨⟨129,46,60⟩,mass_cell 13 129 46 60 92 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 3011718260332, 987287351337, 52144279781, 8785579] (by decide +kernel) (by decide +kernel)⟩
private def m59 : MassCell 13 :=
  ⟨⟨118,16,56⟩,mass_cell 13 118 16 56 137 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2807349258768, 1079983520820, 156255403163, 249900, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m60 : MassCell 13 :=
  ⟨⟨122,21,57⟩,mass_cell 13 122 21 57 122 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2861231707227, 1051874248780, 136267445667, 292825, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m61 : MassCell 13 :=
  ⟨⟨127,27,58⟩,mass_cell 13 127 27 58 110 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2915285330930, 1025115260330, 110220416356, 52360, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m62 : MassCell 13 :=
  ⟨⟨131,26,58⟩,mass_cell 13 131 26 58 112 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2916005726826, 1027395694379, 104269462453, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m63 : MassCell 13 :=
  ⟨⟨135,45,60⟩,mass_cell 13 135 45 60 92 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 3011719898626, 986965472937, 51662169457, 1476032] (by decide +kernel) (by decide +kernel)⟩
private def m64 : MassCell 13 :=
  ⟨⟨126,36,59⟩,mass_cell 13 126 36 59 99 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2966448883527, 998974085238, 84164600054, 46411566, 0] (by decide +kernel) (by decide +kernel)⟩
private def m65 : MassCell 13 :=
  ⟨⟨135,9,56⟩,mass_cell 13 135 9 56 181 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2828971627431, 1125609887400, 97780847406, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m66 : MassCell 13 :=
  ⟨⟨135,34,59⟩,mass_cell 13 135 34 59 101 (by decide)
    (by decide +kernel) [4651458495628, 4202061795036, 3785046960684, 3398893711996, 2967033790964, 1003355412883, 79532032647, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 13) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51, m52, m53, m54, m55, m56, m57, m58, m59, m60, m61, m62, m63, m64, m65, m66]

end Low6969Allocation.Group13
end Z6969Source2344
