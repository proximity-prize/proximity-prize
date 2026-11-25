import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass15

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group15
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [15150812167, 32282319887, 57398803479, 99879253035, 35270325555, 39280154931], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17939677491, 43574836623, 34985109903, 17553725899, 13191654859, 8879979979], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4434020843, 1099751346667, 8678575629, 1099600349711, 1099600350735, 4350131731], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [71943699, 8645094935, 4350130711, 30069235233, 4833824], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i3 : checks (tilesOf batches) 136 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 136 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 136 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 136 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 136 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 136 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 136 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [28020578315, 40688563223, 125363706915, 35672841447, 48054567143, 35169808615], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26227474859, 17587281323, 13208433067, 13107839403, 1100019782059, 4434018787], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099784899043, 1099784900067, 4467569147, 4400462331, 43105138175, 1099633902087], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099633903111, 12973547023, 88714765, 55163415, 1099566792215, 21513142811], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38312473, 30069383713], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 136 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 136 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 136 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 136 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 136 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 136 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [36477019151, 53120813083, 91171945517, 30958583067, 34951634203, 17872568603], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39246383511, 26361622935, 13325868459, 13158100395, 8846425515, 1099919116739], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099919117763, 1099919118787, 1099751341547, 1099751342571, 1099751343595, 4501122543], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4417238511, 17385950707, 34464867849, 1099600344591, 1099600345615, 8628249111], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4299727393, 4299794979, 4829728], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 136 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 136 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 136 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 136 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 136 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 136 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40671719443, 61459290145, 65536431157, 22150616387, 26193997123, 9114863939], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35169589603, 22284828003, 8896687531, 8812870059, 1100019778987, 1099919116739], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099919117763, 1099919118787, 1099784894947, 1099784895971, 1099784896995, 13107762663], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4534609383, 38843724277, 4417236471, 1099701007863, 55160343, 1099566789143], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8611468829, 4316504607, 4827680], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 136 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 136 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 136 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 136 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 136 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 136 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [36561501207, 65653661729, 52718706745, 30975287627, 22318383435, 22033176907], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17570509141, 13225280853, 1100019778987, 1100019780011, 1100019781035, 1100019782059], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4551389623, 1099969444279, 1099969445303, 1099969446327, 8930236883, 4584941011], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099851935187, 1099701006839, 1099701007863, 17234887191, 55088661, 38315545], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38382107], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 136 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 136 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 136 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 136 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 136 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48892954651, 86809868329, 5792910405, 26814609671, 34951632133, 17822169349], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13392975255, 13191652759, 8846423447, 1100053332387, 1100053333411, 1100053334435], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [39162497447, 21999546789, 1100003003823, 1100003004847, 1099835225559, 1099835226583], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099835227607, 4484277731, 1099784891875, 1099784892899, 13023873537, 8645024275], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [71869969, 71936531, 38659312163, 4299725345, 4760096], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 136 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 136 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 136 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 136 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 136 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61425669149, 69713956913, 26428805409, 26227551521, 9131641121, 35219854679], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22318315863, 8896687505, 8796092817, 1100120442259, 1100036557223, 1100036558247], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100036559271, 13258756547, 8846352835, 1099902335431, 1099902336455, 1099902337479], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099801603551, 1099801670111, 1099801671135, 4400390659, 1099650607619, 8611467805], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4316503583, 21538333, 21479520803], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 136 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 136 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 136 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 136 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61409026081, 56913009717, 22033243449, 21831923001, 1100489542971, 1100489543995], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30924955991, 22234497367, 9416776023, 8796026257, 1100120441235, 1100120442259], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100120443283, 4601718211, 1099919044035, 1099919110595, 1099902334407, 1099902335431], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099902336455, 17268441613, 8678577679, 88647181, 88713743, 21537309], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 136 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 136 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 136 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 136 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [61358763045, 44111996985, 30857915727, 22100282701, 17654392141, 17469847889], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100388879699, 1100388880723, 1100086884763, 1100086885787, 1100086886811, 1100086887835], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100086888859, 4601718211, 1099919044035, 1099919110595, 1099919111619, 13141315045], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4551384549, 25858371085, 88640013, 88647181, 88713743], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 136 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 136 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 136 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 136 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [65536358441, 27049637953, 26630060343, 22117061941, 13476867381, 8863202677], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100237883767, 1100237884791, 1100237885815, 1099952668091, 1099952669115, 1099952670139], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099902266823, 1099902333383, 1099902334407, 1099902335431, 8930235857, 4601717203], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099851934163, 21596961285, 122196485, 21537309, 21538333], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 136 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 136 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 136 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [65469252653, 14248625221, 22385493291, 26311433513, 9198680361, 1100137219471], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100137220495, 1100137221519, 1100137222543, 8980569517, 8829577645, 1100002997679], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099935889855, 1099935890879, 1099935891903, 1099751270891, 1099751337451, 1099751338475], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17302062597, 8695355911, 88647181, 4299725345, 4760096], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 136 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 136 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 136 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [65418989617, 1464389705, 26445582625, 26210774305, 4887005473, 8913464717], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8812870029, 1100137219471, 1100019782059, 1099986225587, 1099986226611, 13258756551], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4668826055, 4534610373, 1099902335431, 1099902336455, 1099902337479, 1099801670111], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099801671135, 1099650607619, 1099650674179, 8594690593, 4299726369, 4761120], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 136 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 136 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 136 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤136) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 15 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤138 ∧ 6+a.j≤58 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group15
