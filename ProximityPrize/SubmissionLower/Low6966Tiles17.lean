import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass17

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group17
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2332101637, 10905784331, 27852151821, 61525145621, 87111070761, 14667401285], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30957860173, 30773450061, 30622528845, 43758664039, 35185714533, 13123892693], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8778597845, 1099784245747, 1099784246771, 17418786297, 13073558009, 43154742787], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4383032837, 1099700358663, 4399741457, 4366254609, 1099599694367, 21529201189], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [54510117, 1099566138919, 38692145705, 8627595817, 4332631593, 30085575213], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [20954669], by decide +kernel⟩
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
private theorem i51 : checks (tilesOf batches) 140 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6966Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [23523235849, 40586981393, 86993426465, 44430109757, 35454015785, 35185720617], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43490582825, 8912883105, 17586561453, 17452414381, 13090343341, 43272188385], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099851352547, 26042269169, 13157374449, 4517180913, 4450074097, 1099784242675], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099784244723, 1099784245747, 1099784246771, 38910040565, 8711481873, 1099616402971], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099616469531, 37664297, 37665321, 38658589233, 30068730417, 4299074097], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4108849], by decide +kernel⟩
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6966Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [32197911565, 69930730521, 82715576369, 39648249149, 31024966973, 26562301245], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30605683005, 13509773629, 13207775681, 8845703617, 4533962177, 1099901685207], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901686231, 1099901687255, 17402007037, 8812143101, 1099733911039, 1099733912063], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099717065219, 1099717066243, 1099717067267, 43104413197, 4416515601, 138327569], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [25824095781, 17234233893, 38675436077, 4107825, 4108849], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i49 : checks (tilesOf batches) 140 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6966Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36493340689, 74175566877, 61375028277, 35403683125, 30907529525, 30706342197], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21881600353, 4802400609, 8795371973, 1099968726471, 1099968793031, 1099968794055], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13241260497, 8896031185, 8778593745, 1099868131807, 1099868132831, 1099750621691], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [25958382081, 13073487361, 1099717064195, 1099717065219, 1099717066243, 43087704593], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4382960157, 87994909, 4332627497, 34363694641, 21478867505, 8594037297], by decide +kernel⟩
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
private theorem i52 : checks (tilesOf batches) 140 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6966Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48908745749, 86892899365, 22972055617, 35303091477, 35051573525, 30656083221], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39245659557, 30655866277, 13140669861, 8778597801, 1100086235563, 1100086236587], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17586557373, 13190997437, 1099884840411, 1099884906971, 1099884907995, 4450072037], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834506727, 1099834507751, 17418782201, 4466845193, 4399738377, 1099666732559], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099666733583, 8661146145, 54439461, 1099566068263], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 140 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 140 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 140 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 140 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 140 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6966Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57280776217, 82598068269, 5909696585, 30941151517, 34917425437, 17787962653], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39413434741, 26545451381, 13291594149, 13157446053, 8795373989, 1100052680115], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099935240655, 1099935241679, 1099884839387, 1099884840411, 1099884906971, 4466848233], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817728491, 1099817729515, 17402007025, 8711479817, 4382961161, 1099633178135], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [71216673, 1099582845475, 12922490409, 8627592745, 37661225, 38675368493], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [25773830705], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i18 : checks (tilesOf batches) 140 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 140 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 140 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 140 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 140 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6966Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [65686295581, 69763568693, 30689563953, 26243675441, 4903063857, 35319797069], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26612562253, 8896034213, 8778596773, 1100103011751, 1099968795079, 1099968796103], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13274813897, 8929584585, 4584288713, 1099901616599, 1099901617623, 1099901684183], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099784174067, 1099784175091, 1099649954323, 1099649955347, 21579528729, 12989600281], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4382959133, 87993885, 4332626473], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 140 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 140 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 140 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 140 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 140 53 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6966Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [69897510945, 52717986873, 35286311229, 22401549629, 22149963069, 21864822101], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8996703573, 8812148149, 1100035834295, 1100035835319, 1100035836343, 1100019125691], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100019126715, 1100019127739, 8929582561, 4584286689, 4483625441, 1099800951279], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800952303, 1099649954323, 1099649955347, 30152614429, 17267786269, 12972889629], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [37661225, 37662249], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 140 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 140 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 140 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 140 48 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6966Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69864025125, 39933816893, 31041744185, 26495192377, 22049302841, 13191004529], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100321050995, 1100321117555, 1100002279871, 1100002280895, 1100002281919, 1100002348479], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8896031173, 4550735301, 1099968724423, 17435561449, 8845697513, 1099700286983], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700288007, 138325521, 1099649954323, 25824095781, 17234233893, 8627592745], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [37661225], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 140 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 140 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 140 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 140 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6966Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78319876137, 18593203269, 31008192797, 26528815389, 26294007069, 1100153344411], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100153345435, 8912811421, 1100136497567, 1100136498591, 1100136499615, 1100136500639], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13190928853, 8828922325, 1099800950255, 1099800951279, 1099800952303, 25958382081], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13056710145, 4399737361, 1099649954323, 4366181921, 12905780781, 20885037], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21478865457, 12889002545], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 140 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 140 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 140 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6966Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69780276269, 14365411397, 26662962477, 26377822509, 21948710189, 8812150177], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100086167979, 1100086234539, 1100086235563, 1100086236587, 9030246849, 8862477761], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985500611, 1099884838363, 1099884839387, 1099884840411, 17368450565, 13039999493], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4399738373, 1099700286983, 71216673, 1099582845475, 8610814509, 4315850285], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 140 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 140 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 140 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6966Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73974648881, 30806937881, 30538576153, 4970172697, 13241332109, 8862482829], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100203609487, 1100002349503, 1100002350527, 17536225741, 8929584589, 1099918393811], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918394835, 1099918461395, 4483625445, 1099834505703, 1099834506727, 1099633177111], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099633178135, 4366181921, 71216673, 12939268645, 8627593765, 4299072049], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 140 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 140 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 140 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6966Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [61207256117, 26377821497, 21931931961, 4835955001, 8828926377, 1100086166955], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100086167979, 1100086234539, 1100002349503, 1100002350527, 9013403085, 8879253965], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4533958093, 1099834506727, 1099834507751, 1099683509771, 1099683510795, 4399737365], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099633177111, 4106801, 4107825], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 140 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 140 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6966Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [48423020601, 21948639573, 17519526229, 1100438558039, 1100086165931, 1100086166955], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100086167979, 1100086234539, 1100086235563, 8912808393, 4550735305, 1099951947211], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099683509771, 1099683510795, 4399737369, 104772121], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i42 : checks (tilesOf batches) 140 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 140 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6966Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 17 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤142 ∧ 5+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6966Allocation.Group17
