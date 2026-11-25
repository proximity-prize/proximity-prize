import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass5

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group5
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2214661125, 1006702601, 5285024777, 19043326989, 40301178897, 138213808161], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1698225229, 35638106333, 56576277725, 39497282781, 35553744121, 1177161981], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [30554946961, 21914754449, 43456412061, 13207385513, 13123569065, 4567193001], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4416194021, 1099716742631, 1099716743655, 1099716812263, 1099683190255, 1099683191279], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8677602809, 121225721, 12989275645, 8694377981, 1099582522887, 1099582523911], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [25823772169, 54041097, 21495244305, 4315527697], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10654259211, 27633853453, 57129123865, 108300302377, 39446739209, 39295885577], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22166423817, 39480082769, 30890355025, 17535902117, 13157053861, 13090014629], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934848435, 1099934849459, 1099934850483, 21763688905, 26075211213, 1099767072219], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767073243, 1099767074267, 1099767075291, 4466521577, 4399414761, 8710789625], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8694309373, 4399410685, 70893061, 1099582521863, 21495319057, 20559380], by decide +kernel⟩
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
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27633853453, 52884488217, 108233192489, 1580784717, 39497069817, 47801933049], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13677153529, 39429816669, 30806468957, 17670118785, 13291270529, 8979595649], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901291963, 1099901292987, 1099901294011, 1099901295035, 17519053253, 1099834187211], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [26075211213, 1099733516771, 1099733517795, 1099733518819, 4483297765, 4399413733], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8711085561, 4416186873, 1099599297027, 1099599298051, 30085179921, 20558356], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [32030011409, 65568329757, 82580967473, 34967359773, 34799662365, 4953069853], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35319402801, 26662499633, 13173831049, 13090014601, 1100102620555, 17519055281], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13157049777, 1099884512703, 1099884513727, 1099884514751, 1099884515775, 1099884517823], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099850964415, 4483298769, 1099800624595, 1099800625619, 30252806633, 4432897525], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4416187893, 1099599296003, 1099599297027, 12955718149, 70820357, 25823770121], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099532262931, 20557332], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48673340437, 82563984421, 35621682241, 31007730957, 30789766413, 17955335437], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39362706797, 30756136301, 13190676849, 13090017649, 1099985179047, 1099985180071], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951626663, 1099918073255, 17485499837, 8912413117, 1099884511679, 1099884512703], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099884513727, 1099884514751, 4533562825, 4483298761, 1099834179019, 17334568433], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099632850427, 1099632851451, 70888965, 70889989, 8643975689, 1099532262923], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4332299789, 1099532261907, 56848, 30068401685, 56852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48740714521, 74024450089, 31309938753, 26662500637, 26461312285, 13610037533], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13173899629, 8828604781, 1100102622575, 39245334913, 26394128769, 1099968401835], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934848427, 1099901295019, 1099918066103, 1099918067127, 1099918068151, 1099918069175], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13207377349, 8811750853, 4449677773, 1099817400783, 1099817401807, 13022825973], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099649626615, 1099649627639, 4382565885, 104443389, 1099549040127, 1099532261899], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56840, 56844, 38675040785, 33609232, 4298677781, 4298745365], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [3855892, 16833044], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57112679453, 78218890289, 5707978825, 30756211981, 30571801869, 9197636877], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35185251665, 22300490065, 13173829001, 8845376905, 1100102617483, 1099918072223], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884518815, 1100001955235, 1099985179043, 1099934848419, 13274419637, 8912413109], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834179019, 1099834180043, 1099834181067, 4466453969, 1099800622547, 1099800623571], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532262907, 104443389, 1099616072191, 1099532261891, 56832, 4365787653], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [70887941, 56836, 33609224, 33609228, 33609232, 12888609301], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [50385428], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57096036385, 69645735989, 1413012557, 26427758869, 26243282197, 9147371797], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30890352977, 22216606033, 8878863753, 8795046281, 1100102618507, 1099968401823], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934848415, 1099884517791, 1099834187171, 13207378357, 8811751861, 1099884511679], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099884512703, 1099884513727, 1099800622547, 1099800623571, 1099800624595, 4382566893], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099683181039, 1099549040115, 55800, 1099532261887, 56828, 56832], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [21545648645, 8660752901, 4349011461, 70888965, 33609220, 33609224], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [50385420, 50385424, 4298745365, 50385428], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69762968613, 48305254461, 30974242081, 26461244705, 22015355169, 17519132989], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8929269053, 1100069061011, 1100069062035, 1100069063059, 1100052286867, 1100018733459], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968402835, 1099918072211, 1099884518803, 8878860709, 4550342053, 1099985173927], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13207309769, 8895634889, 1099716736487, 1099716737511, 4382566893, 1099683181039], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532262895, 16833012, 16833016, 25874099709, 104368637, 3856892], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56828, 33609216, 4332300805, 33609220, 33609224, 50385420], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [20556305, 20557329, 50385424, 4298677781, 3778068, 67161620], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [61256988713, 44027065405, 26612234553, 22116013369, 17703677241, 17485578561], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8912491841, 1100085838223, 1100085839247, 1100085840271, 1100069064079, 1100018733455], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951625619, 1099918072211, 1099867741587, 4550340025, 4500075961, 1099901287867], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13140268501, 4550338005, 1099549040107, 1099683182063, 1099683183087, 16833012], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [121220601, 1099632849403, 16833016, 33609212, 33609216, 21545581061], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [12955718149, 33609220, 50385416, 50385420, 50385424, 4298678805], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [3779092, 67161620], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [61206725677, 31226052673, 26494797105, 22032130353, 13408713009, 13123570009], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100136175963, 1100102622555, 1100052285847, 1100035509655, 1099985179031, 1099934848407], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934841267, 1099934842291, 1099934843315, 1099934844339, 8912413113, 4567117241], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099901285819, 17401611745, 8811747809, 1099532262891, 16833008, 16833012], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [16833016, 104443389, 1099616072191, 33609212, 33609216, 33609220], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4332234249, 50385416, 50385420, 50385424, 4298745365, 67161620], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i33 : checks (tilesOf batches) 133 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 133 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 133 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [69645733937, 9902281801, 26494800145, 26293611793, 9164081425, 1100001957255], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099951626631, 1099901296007, 8929193361, 8794978705, 1100069062035, 1100018731423], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100001955231, 1099951624607, 17468789185, 4651001281, 1099850955207, 1099850956231], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099850957255, 4416187877, 1099716736487, 1099549040103, 16833008, 16833012], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [16833016, 33609212, 33609216, 70888965, 1099582517767, 33609220], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [12938940937, 54043145, 50385416, 50385420, 50385424, 67161620], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i36 : checks (tilesOf batches) 133 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 133 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 133 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65350835253, 1362680909, 26394205461, 26176174357, 4852405525, 8895641977], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8811824505, 1100102619515, 1099834187159, 1099901293983, 1099850963359, 9029852589], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8862083501, 1099951551919, 1099934844339, 1099934845363, 1099918069171, 1099850955207], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099850956231, 1099850957255, 1099549040103, 4399344113, 1099666403827, 16833008], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [16833012, 16833016, 33609212, 33609216, 33609220, 50385416], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4315523597, 50385420, 50385424, 20556308, 67161620], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i39 : checks (tilesOf batches) 133 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 133 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 133 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤133) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((5 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 5 where
  orders := orders
  covers := by
    intro a ha box
    change 5+a.b≤138 ∧ 3+a.j≤58 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group5
