import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass23

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group23
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23390194695, 36310623247, 86877882395, 57048472631, 35405646087, 35154128135], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39197511943, 25977141595, 13327110539, 13176119691, 8847602059, 8780561807], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100021025167, 1100021026191, 1100021027215, 1099819695551, 1099819696575, 1099819697599], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21749198279, 13159335367, 1099769360843, 1099769361867, 1099769362891, 34583547347], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4451967443, 1099735738835, 1099735739859, 38811546083, 4368078327, 4334525943], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099567965691, 30087469571, 22781443, 22782467], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i51 : checks (tilesOf batches) 129 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [32031840267, 48759846935, 86861375527, 22823025731, 30909491471, 34919319823], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39029812495, 17420758379, 39180581251, 26329309571, 1100054577543, 1100054578567], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100054579591, 1100054580615, 1100054581639, 13276711319, 13159340439, 8797268375], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099920291239, 1099920357799, 1099920358823, 1099769293259, 1099769294283, 1099769360843], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17353637339, 4451965403, 1099702182363, 1099702183387, 38811474403, 4368077303], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [34382365187, 22780419, 22781443, 12890897927, 8595934727], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i46 : checks (tilesOf batches) 129 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [36310623247, 74026534939, 69715202099, 35338537231, 26664856847, 26430048527], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26195240227, 17571758371, 1100071354755, 1100071355779, 1100071356803, 1100071357827], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100071358851, 8847598987, 1100037730699, 1100037731723, 1100037732747, 1100037799307], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13192890799, 8814041519, 1099769292235, 1099769293259, 1099769294283, 38811477475], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21614980583, 13008340455, 4384856551, 1099651850727, 30121020923, 4351301115], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [39558655, 8595932679, 4300968455], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i49 : checks (tilesOf batches) 129 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36361285651, 78254527519, 52585734203, 31110681859, 30808831235, 30590801155], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21749282103, 1100390124855, 1100390125879, 1100104840571, 1100104841595, 1100104908155], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100104909179, 1100104910203, 1100104911227, 13226448259, 8864376195, 1100071285123], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17521341879, 13142559159, 1099786069447, 1099786070471, 1099786071495, 4435188183], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099718959575, 38744437235, 8663042551, 4351301111, 1099567963643, 30104246783], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [6002183, 6003207], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i52 : checks (tilesOf batches) 129 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48759913495, 86710381607, 18427396163, 30959758571, 34952875243, 34785177835], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13159346515, 1100155240815, 1100155241839, 1100155242863, 1100155243887, 1100155244911], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13310266747, 8965037435, 8830822779, 39180582275, 26278978947, 1099987400087], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099987466647, 1099987467671, 1099853179319, 1099853180343, 1099853181367, 13176111555], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099718958551, 1099718959575, 1099718960599, 4451963363, 4384856547, 56334843], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [21514315263, 12924452351, 38677331459], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i15 : checks (tilesOf batches) 129 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 129 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 129 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48726493211, 86676895787, 5592828999, 26698414311, 34902545639, 26245576935], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100239059291, 1100239060315, 1100239126875, 1100239127899, 1100239128923, 13310334315], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13142566251, 1100171949419, 34935949695, 22051188095, 1100088135039, 1100088136063], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099903509931, 1099903510955, 1099903511979, 1099903513003, 13125780935, 4502296019], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099735735763, 1099735736787, 8612709891, 4317745667, 6003207], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 129 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 129 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 129 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 129 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 129 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [52887376927, 73842395187, 1297862731, 26480380155, 26262349051, 17622089979], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30758425955, 22101521763, 1100188795239, 1100188796263, 1100188797287, 1100188798311], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8897930611, 1100138393971, 1100138394995, 1100138396019, 1100138397043, 1100071358851], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8998587815, 8830818727, 1099819623871, 1099819624895, 1099819625919, 4384856547], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099668627939, 17236194811, 8646265339, 56334843, 56335867], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 129 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 129 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 129 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 129 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57031417891, 61007829047, 22051199243, 21883498763, 9015380235, 30825603395], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22084747587, 8797270383, 1100155174255, 1100155240815, 1100155241839, 1100138465651], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100138466675, 1100138467699, 8897927575, 4552631703, 1099987398039, 1099937067427], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099937068451, 1099937135011, 13092225495, 8746930647, 1099718960599, 1099718961623], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [156999139, 1099668627939, 25826058747, 17236196859, 4334522879, 39557631], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 129 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 129 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 129 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 129 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65436871719, 39667280959, 26681634075, 22168635675, 21933826331, 13192902963], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100406901043, 1100406902067, 1100406903091, 1100088064383, 1100088130943, 1100088131967], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100088132991, 8864375179, 1100037729675, 1100037730699, 1100037731723, 13142559171], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4552628675, 1099752513999, 1099752515023, 1099752516047, 21547871735, 12958008823], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4317746691, 22781443], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 129 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 129 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 129 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 129 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69631244331, 22621699139, 26614528263, 26329388295, 17672417543, 1100255905111], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100255906135, 1100255907159, 1100255908183, 1100088062335, 1100088063359, 1100088064383], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100088130943, 1100088131967, 9032144271, 8847597967, 1100020952463, 1099752513999], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099752515023, 1099752516047, 17403902419, 8814038483, 4334524923, 6003207], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [6004231], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 129 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 129 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 129 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [61108487215, 18360287299, 22252520731, 21967314203, 17554978075, 1100222351711], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100222352735, 1100222353759, 1100121617783, 1100121618807, 1100121685367, 1100121686391], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100121687415, 8914705811, 4552632723, 1100004176275, 1099735738835, 1099735739859], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13092226519, 8746931671, 157000163, 1099668628963, 4334523903, 39558655], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 129 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 129 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 129 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [65269239859, 1281085515, 26430050559, 26195242239, 9048934655, 8897932647], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100188727655, 1100188728679, 1100188795239, 1100188796263, 1100155242863, 1100155243887], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100088136063, 13226447263, 4636516767, 4519078303, 1099869958579, 1099870025139], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099718961623, 1099718962647, 8679821811, 4351303155, 1099601520115, 22781443], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [22782467], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 129 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [56746482743, 22017645843, 17605309715, 8981825811, 1100138465651, 1100138466675], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100138467699, 1100104840571, 1100104841595, 1100104908155, 1100104909179, 1100104910203], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8931483031, 4569409943, 1099987399063, 1099702184411, 1099702250971, 4401634795], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [89892331, 22849027, 6004231, 6005255], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤129) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((23 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 23 where
  orders := orders
  covers := by
    intro a ha box
    change 13+a.b≤142 ∧ 6+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6966Allocation.Group23
