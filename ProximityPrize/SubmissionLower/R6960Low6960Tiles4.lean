import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass4

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group4
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2231438341, 1006702601, 4949414921, 18942598157, 44411531281, 138230586401], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [27315541161, 35587775713, 56542724321, 39430109409, 35352285437, 39362639217], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [26310246797, 21914688909, 17552684429, 13123504541, 4567128477, 1099783784923], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783785947, 1099783786971, 1099783853531, 1099750300131, 1099750301155, 4500010473], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4432903657, 1099716675051, 34547634669, 13022764537, 4432899577, 34430410249], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [54050317, 1099565679119, 21512028689, 37198353], by decide +kernel⟩
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
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10452867083, 27566679053, 57129123865, 108283459625, 39429896453, 43523678469], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17921789189, 39480082769, 26612099409, 17586168209, 17468798353, 1100085774739], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918003643, 1099918004667, 1099918005691, 1099918072251, 1099918073275, 39043868093], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21813953985, 8962678209, 8928762313, 8727868889, 1099783782875, 1099783783899], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8711088629, 121157117, 1099632785919, 1099632786943, 21495252501, 4315458069], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [20492821, 25773297177], by decide +kernel⟩
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
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [23573701645, 48656497685, 112477695013, 5825353801, 35352964329, 43624272105], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26511654121, 39396195689, 26511435113, 17669984653, 17519060365, 8962750861], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13039617437, 1100035446175, 1099918072251, 1099918073275, 1099867669959, 1099867670983], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867672007, 1099867673031, 17451876825, 8778196449, 4466455009, 1099716671979], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099716673003, 1099716674027, 21562140165, 12955653637, 54047245, 1099565676047], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4332234257, 37269009, 8593577497, 3711512], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [31979614225, 52935086109, 95365071917, 35101443329, 34950588673, 17837903105], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35067744621, 22199760237, 13207316881, 13123500433, 1100085774739, 1100018666915], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018667939, 1100001891747, 1099968338339, 1099968404899, 17552608693, 8945902005], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834112463, 1099834113487, 1099834114511, 1099834115535, 38909784541, 4466453985], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099750225379, 4349010445, 54045197, 54046221, 1099565675023, 12922097169], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [37264913, 1099532196371, 56848, 56852, 25773365785, 3790360], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [16833048], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [40318221333, 65551754277, 61190022201, 30940620085, 22266873141, 22065618229], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26142553401, 13291278649, 8878863765, 8778203541, 1100068998551, 1100018667935], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968337311, 1099934783903, 1099934850463, 39144603045, 8895569349, 8761354693], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867668935, 1099867669959, 1099867670983, 1099767002591, 1099767003615, 1099767004639], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4416121329, 1099683115507, 17334502901, 8744573429, 1099548973575, 56836], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [30135445001, 56840, 1099548972559, 56844, 4332234257, 37269009], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [16833040, 16833044, 3789336, 33609240], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
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
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48707094553, 78252242985, 27031749701, 26695989517, 30705882381, 13609973005], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8845313397, 1100136108407, 1100102554999, 1100069001591, 1100035448183, 35034188153], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [26444393849, 13274420649, 8895571369, 4600672681, 1099934778807, 1099934779831], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099918003639, 1099901221311, 1099901222335, 1099901223359, 13073091053, 4432897525], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099666337271, 1099666338295, 1099666339319, 1099532197367, 1099532196351, 56828], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56832, 1099548972551, 16833028, 8643910153, 16833032, 1099548971535], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [16833036, 33609232, 33609236, 8593644057, 20489752, 3788312], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [50385432], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
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
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [52884755485, 82463459377, 5674358857, 30806477057, 30622066945, 13509380353], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35067745633, 22216538465, 8979458441, 13106722185, 1100119328139, 1099901229463], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901296023, 1100052220315, 1100001889691, 1099968336283, 1099918005659, 13274419637], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4701266357, 1099884443075, 1099884444099, 1099884445123, 1099884446147, 4416121321], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099716669931, 1099548973559, 56820, 56824, 1099548972543, 56828], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [16833024, 16833028, 70822409, 1099582451211, 1099532194315, 33609224], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [34413630989, 33609228, 1099548970515, 50385424, 21495249429, 8610353685], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [4315454997, 50385428, 3712536, 50385432], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
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
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61290274849, 69628959797, 26377362705, 26209663249, 9113752849, 30957330745], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22283649337, 9465927993, 13106723197, 1100152883583, 1100102552959, 1100068999551], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934782867, 1099901229459, 1099901296019, 8895571365, 4600672677, 1099934775735], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099934776759, 1099934777783, 1099934778807, 4432897521, 1099683114483, 1099683115507], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099683116531, 1099532196339, 56816, 56820, 1099548972539, 16833016], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [17300947453, 8711017981, 16833020, 16833024, 1099532194311, 33609220], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [33609224, 4349010445, 1099548970511, 50385420, 30101889553, 50385424], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [20490773, 50385428, 3787288, 67161624], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
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
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [61273631781, 56828012601, 26209659177, 17569465641, 4734900521, 26679209273], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26410912057, 9348556089, 1100119328139, 1100085774731, 1100035444107, 1100001890699], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951560075, 8828465557, 1100068994455, 1100068995479, 1099867675031, 1099867741591], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817333203, 1099817334227, 1099817335251, 17435167189, 4583824853, 1099532196335], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56812, 4432897521, 1099683114483, 56816, 1099548972535, 16833012], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [16833016, 16833020, 1099532194307, 33609216, 33609220, 1099548970507], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [50385416, 50385420, 50385424, 25790148117, 12905318933, 20421141], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [20489749, 20490773, 1099532192279, 67161620, 67161624], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
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
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69695862825, 35487464513, 26679212309, 26427692309, 17770721557, 13173835089], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8811763025, 1099934782859, 1099901229451, 1099901296011, 1100052219291, 1100018665883], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968335259, 1099918004635, 8794976677, 1100001885607, 1100001886631, 13224089013], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8828462517, 1099783778779, 1099783779803, 1099783780827, 1099532196331, 56808], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56812, 21646178801, 13039538673, 4432897521, 1099683114483, 1099548972531], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [16833008, 16833012, 16833016, 1099548971519, 33609212, 33609216], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [33609220, 4365787657, 1099532193291, 50385416, 50385420, 67161616], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [20490773, 1099532192279, 67161620, 8593576473, 3710488, 67161624], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
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
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69662377005, 22686451781, 26595394833, 22132728081, 13509310737, 1100219992427], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100169661803, 1100119331179, 1100069000555, 1100018669931, 1099985116523, 1099985107371], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985108395, 1099985109419, 1099985110443, 8912347569, 8794975665, 17451943385], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8862013913, 1099532197343, 1099733446119, 1099733447143, 1099733448167, 1099548973543], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56804, 56808, 56812, 1099532195315, 16833008, 16833012], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [33609208, 1099532194303, 33609212, 4382565889, 33609216, 50385412], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099532193291, 50385416, 50385420, 67161616, 1099532192279, 67161620], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [20489752, 67161624], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [61139619889, 18408262725, 22233387301, 21998577957, 9164079397, 1100152884591], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102553967, 1100052223343, 1100001892719, 1099951562095, 8862017957, 4550342053], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100001885607, 1099951554995, 1099951556019, 1099918002611, 1099548974555, 13140201949], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4550271453, 1099733448167, 1099733449191, 1099548973543, 56804, 4432898537], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099716669931, 56808, 56812, 1099532195315, 16833008, 16833012], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [33609208, 1099532194303, 33609212, 33609216, 50385412, 1099532193291], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [50385416, 54045197, 1099565673999, 50385420, 67161616, 1099532192279], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [67161620, 67161624], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 134 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65333992501, 1362680909, 26377362705, 26176108817, 4835562769, 8912419189], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100203214199, 1100169660791, 1100119330167, 1100068999543, 1099884451223, 1099834120599], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099834187159, 9029787045, 8862017957, 1100001883559, 1099867666887, 1099867667911], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099867668935, 1099532196327, 56804, 4432898537, 1099716669931, 56808], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [16833004, 1099532195315, 16833008, 16833012, 33609208, 1099532194303], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [33609212, 33609216, 50385412, 1099532193291, 50385416, 54045197], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099565673999, 50385420, 8627199505, 67161616, 1099532192279, 67161620], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [67161624], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 134 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤134) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((4 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 4 where
  orders := orders
  covers := by
    intro a ha box
    change 4+a.b≤138 ∧ 3+a.j≤58 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group4
