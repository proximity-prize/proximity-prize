import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass20

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group20
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2147552261, 14966067211, 36308328461, 87077307417, 74427963445, 52382483765], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43809536309, 30589232521, 26210452873, 47399772641, 17251419637, 4366522869], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [42987360765, 51560665601, 38659065349], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i3 : checks (tilesOf batches) 129 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 129 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 129 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 129 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 129 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 129 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 129 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [27784910857, 49043026965, 87111197733, 40236070977, 43742356809, 39346868553], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21764487613, 13141004733, 51812185541, 47349438957, 34447987185, 21563160049], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8627933693, 38002173, 8594378245], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i6 : checks (tilesOf batches) 129 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 129 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 129 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 129 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 129 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 129 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 129 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [36425966605, 70082054169, 87061138481, 35102231881, 39145615689, 5071165769], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [47936588129, 39330019681, 21747708353, 13124225473, 51577366013, 25807725053], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8627931645, 4332967421, 38659062277, 12889341445, 4447749], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i9 : checks (tilesOf batches) 129 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 129 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 129 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 129 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 129 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 129 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40738172945, 82765830177, 57180989497, 48054098233, 35169339705, 21999299965], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26093012349, 13073892813, 8728597965, 4349744625, 1099599961587, 47282477565], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [30102686205, 21512825341, 8627929597, 4332965373, 21222913, 21223937], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [51543814661], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i12 : checks (tilesOf batches) 129 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 129 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 129 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 129 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44949584917, 86993823781, 35840441409, 43792689453, 35102233901, 34900982061], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099918728615, 17469520305, 13090672049, 25925162465, 17335300577, 4416851429], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [138663397, 1099650292199, 51610926581, 38709326329, 8627930617, 4299408901], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4443653, 4444677], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 129 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 129 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 129 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 129 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57432033305, 86943629357, 10255258697, 35236380969, 34984797481, 22083193129], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [47701772697, 34817014169, 8812480957, 21730862529, 13124222401, 4383299033], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099700624859, 1099599959539, 1099599960563, 4332965365, 21512756733, 8627928573], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4332964349, 12906116609, 21221889], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 129 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 129 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 129 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 129 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 129 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61609694237, 82648731697, 30907928877, 30656344365, 13560434989, 47785661825], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34867348865, 13191262653, 8879587773, 8762150333, 1099734178259, 1099734179283], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4366519785, 1099633513963, 17234635257, 30102685181, 17217857021, 37998077], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099549626879, 47248922117, 4299407877, 4442629], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 129 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 129 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 129 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 129 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 129 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [74243072033, 57046771769, 43742355785, 30824041801, 22049631581, 21881931101], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100220718431, 8795702721, 4467184065, 1099801287107, 17284967913, 8678261225], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099616735727, 1099616736751, 71552501, 30085910017, 4316185089, 21219841], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12889337349, 8594374149], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 129 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 129 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 129 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 129 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [74209586213, 44279379005, 43692092741, 26512300357, 17620448637, 13258443133], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4668512637, 4450404825, 1099700621787, 1099700622811, 1099700623835, 1099700624859], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13006779881, 4416849385, 38709325305, 25824499193, 12939670009, 21220865], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i27 : checks (tilesOf batches) 129 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 129 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 129 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 129 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78403958825, 27217019973, 39481014577, 30723383601, 22049636657, 4517517729], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8846033341, 4517514685, 1099818063295, 21680529873, 13057112529, 1099700623835], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099700624859, 71552501, 1099583181303, 38709393913, 8627927549, 4332963325], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21479268869], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 129 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 129 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 129 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 129 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [78370473005, 14432784457, 35186050349, 26495592749, 26243941677, 8929920417], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4467184061, 1099818064319, 1099818065343, 17352010205, 8762146269, 1099633512939], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099633513963, 30136239605, 17251411445, 71551477, 71552501], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i33 : checks (tilesOf batches) 129 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 129 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 129 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [82564845617, 35186118937, 34900981017, 5071165721, 13291926941, 8946697629], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8812482973, 1099717398999, 1099717400023, 1099717401047, 1099717402071, 25925161441], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17335299553, 4366517749, 71552501, 4316185089], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 129 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69797452853, 26545855801, 26294270265, 9198359865, 13157775801, 4584622521], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4483961273, 1099750955471, 1099750956495, 1099633512939, 1099633513963, 21546311157], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [12956448245, 4332963325, 21220865], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 129 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 20 where
  orders := orders
  covers := by
    intro a ha box
    change 12+a.b≤141 ∧ 4+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group20
