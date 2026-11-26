import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass15
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group15
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2298547205, 1057034251, 10670904331, 27784847373, 86908812309, 78604898353], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35570585867, 44060261641, 39732013321, 30722855273, 34799792489, 4969977193], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13190738389, 13106921941, 8778404309, 43188106737, 1099666543111, 21612892681], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13022964233, 34480941581, 25891081741, 4416324109, 4365994509, 1099632989711], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099632990735, 38742286869, 8627403297, 37472801, 1099549101603], by decide +kernel⟩
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
    Covered orders a ∨ Low6966Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [19127146505, 36291488785, 86976253981, 57214018617, 39748718881, 35286120737], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39329570081, 21797455237, 17586363845, 13207515589, 8895840709, 8728071637], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867871703, 38976952797, 43255284193, 1099716873723, 1099716874747, 1099716875771], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [30236310017, 17351481857, 4349215249, 1099616209427, 8677732885, 4365991445], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [37471777, 34363502121, 8593845801, 3915305, 3916329], by decide +kernel⟩
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
    Covered orders a ∨ Low6966Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [28019991565, 57246760985, 86993369129, 14566476869, 30991153457, 30789966129], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34866903345, 43674583405, 30856932717, 13190740397, 13106923949, 1099851094491], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17468922337, 8862215649, 1099800758759, 1099800759783, 1099800760807, 1099800761831], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4483430905, 4399546873, 21579337233, 1099599430167, 1099599431191, 43003626013], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8610623013, 42953287209, 8593778217, 3914281, 3915305], by decide +kernel⟩
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
    Covered orders a ∨ Low6966Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36358729745, 78419940381, 61357989945, 39631279401, 35185524009, 26276897121], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26125974881, 1100354410851, 8845442489, 8778402233, 1099985311163, 13173957085], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8811885021, 1099783981547, 1099783982571, 1099783983595, 43188105713, 26008452593], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13123623409, 4399545849, 1099716871675, 34447318549, 4382765589, 87800341], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099599429143, 1099599430167, 4315589157], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6966Gate.Gated ((15 : Band).val) a :=
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
    Covered orders a ∨ Low6966Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53069367321, 82614582317, 14432259141, 30957600033, 34950716705, 26293748001], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39329352073, 30689227145, 8845443489, 13358505393, 8979656113, 8862218673], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985309115, 1099985310139, 1099985311163, 1099985312187, 1099817534947, 1099817535971], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4399544821, 1099733647863, 17385034233, 4382699025, 104576529, 1099616205331], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099616206355, 30102090273, 4315588133, 4298878505], by decide +kernel⟩
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
    Covered orders a ∨ Low6966Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57280648221, 82564320305, 30857006361, 26411117849, 17787701529, 39329355129], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26444594553, 1100035639727, 1100035640751, 1100035641775, 1100035642799, 1100035643823], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13157182901, 8778333621, 13224286681, 8845437401, 1099800755687, 1099800756711], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800757735, 4416321017, 4365920793, 4332433945, 1099582650907, 38708729373], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21528935965, 12939073053, 20689445, 20690469], by decide +kernel⟩
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
    Covered orders a ∨ Low6966Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65686167585, 61223772217, 26327228737, 21914893633, 4852536641, 35218940241], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26511705425, 8795110829, 1100035639727, 1100035640751, 1100035641775, 13190734281], by decide +kernel⟩
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
    Covered orders a ∨ Low6966Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [78336257061, 35655366721, 31175699741, 26645925149, 26394339613, 13157188985], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100253746555, 1100253747579, 8996432309, 8845440437, 8761622965, 1099968531903], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968532927, 1099817533923, 1099817534947, 1099817535971, 17418522097, 8828658161], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4416321013, 1099733646839, 87799317, 1099599428119, 4332367385, 4315655717], by decide +kernel⟩
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
    Covered orders a ∨ Low6966Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78302771241, 22887973957, 31041485081, 30773188889, 30538381593, 13173963149], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8795179417, 1100119528859, 1100119529883, 13308172741, 8929323461, 4584027589], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901422031, 1099901423055, 1099901424079, 1099867864535, 1099867865559, 1099867866583], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [25924565509, 13039736325, 121353741, 1099632982543, 4365920793, 71021081], by decide +kernel⟩
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
    Covered orders a ∨ Low6966Gate.Gated ((15 : Band).val) a :=
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
  ⟨unpack [4416321013, 1099733646839, 4399476237, 87799317, 1099599428119, 8610553381], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4315589157, 3912233], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 138 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 138 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 138 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤138) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [78235799601, 30857007377, 26411184401, 13492735249, 1100069195175, 1100069196199], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100069197223, 1100069198247, 8929325485, 8795110829, 1100035639727, 17535963601], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8946099665, 1099817532899, 1099817533923, 1099817534947, 4399477249, 1099683314179], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [54243869, 54244893, 17183707689, 4298810921, 4298878505], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 138 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 138 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 138 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤138) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65451629621, 26461445421, 26226637101, 4902868269, 8912550301, 8811955613], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102750623, 1099951756739, 1099951757763, 13224287701, 8828661205, 1099867866583], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867867607, 1099867868631, 4416322029, 1099767202287, 1099632982543, 1099632983567], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4382699025, 104576529, 8593776169, 4298811945, 3912233], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 138 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 138 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤138) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [52667394105, 22049106249, 17603150153, 4785427785, 8778400177, 1100018863539], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100018864563, 1099951756739, 1099951757763, 8878991829, 4533695957, 4466654677], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099817534947, 1099817535971, 1099683315203, 1099683316227, 104576529, 1099616205331], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4349143581, 4332433949, 3912233], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i42 : checks (tilesOf batches) 138 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 138 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤138) (hj : a.j≤54) :
    Covered orders a ∨ Low6966Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 15 where
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
end Low6966Allocation.Group15
