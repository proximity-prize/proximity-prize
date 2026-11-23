import ProximityPrize.SubmissionLower.R6960Low6960AllocTiles
import ProximityPrize.SubmissionLower.R6960Low6960Mass13

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group13
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27839302663, 40658544659, 86930575391, 31532491835, 39501451543, 35072407831], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39132568855, 17489960331, 8849764763, 4538023323, 25962445251, 13094327747], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8698766807, 1099637243351, 1099637244375, 4353470939, 1099620465115, 34434798051], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [25845003747, 41726443, 41727467, 42957548019, 12893000179, 4303136243], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4303138291], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 124 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 124 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 124 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 124 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 124 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 124 43 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36413380619, 53074017303, 86846828587, 30911656207, 34904707343, 13564163343], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39115570567, 30525777287, 13295653267, 13161505171, 8816210323, 1099788238259], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099788239283, 1099687571915, 1099687572939, 1099687573963, 4420575703, 4387023319], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17288627675, 24947183, 24948207], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i6 : checks (tilesOf batches) 124 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 124 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 124 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 124 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 124 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 124 46 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40658478095, 61395651615, 61194537011, 26331547955, 17674511667, 9101424947], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35055488335, 26432139599, 4571571627, 4487687595, 1099821790635, 1099805014447], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099805015471, 1099805016495, 13127880123, 8782650811, 1099620462043, 1099620463067], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4336688619, 42974324207, 25794671087, 24946159, 24947183], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i9 : checks (tilesOf batches) 124 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 124 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 124 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 124 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 124 41 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (i41))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40675454995, 61328611363, 48376812599, 35055556931, 22153952579, 21902366023], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13295725895, 4722572615, 4454133163, 1099821790635, 1099821791659, 8883246511], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4571570607, 4487686575, 1099805015471, 1099805016495, 1099654017491, 92056031], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099603684831, 17238293991, 8648364519, 30106343915, 21516483051, 8167923], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8168947], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 124 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 124 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 124 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 124 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 124 44 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44786072599, 57033713703, 35559022651, 30727104839, 17825499463, 17590623559], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13144731995, 1100157337947, 1099888898459, 1099888899483, 1099888900507, 1099888901531], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4605058475, 4538017195, 1099821788587, 38813580751, 30207010255, 12960106979], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4370176483, 12943328743, 58500583, 1099570129383, 25777825267, 17187963379], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 124 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 124 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 124 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 124 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 124 47 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [44719032347, 61160911915, 18496598079, 26566358307, 22070137123, 17641023779], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100023119227, 1100023120251, 4571572627, 1099922452883, 1099922453907, 1099922454931], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13094326707, 4554793395, 38863980995, 25962377667, 1099637238231, 1099637239255], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12960108003, 4353465831, 25777893875, 8168947], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 124 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 124 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 124 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 124 42 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (i42)))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [44635214879, 52638154799, 14235186239, 22204350775, 17708063031, 13295725879], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099989564803, 1099989565827, 4487687579, 1099888899483, 1099888900507, 34636125619], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21751364019, 8799361463, 4487685559, 1099687570891, 1099687571915, 8648364519], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [58500583, 1099570129383, 4336688619], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 124 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 124 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 124 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 124 45 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [52889673763, 48259372087, 17825502507, 17590692139, 4772904235, 34938184039], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17775166823, 8799431055, 1099939231119, 1099939232143, 1099872124319, 1099872125343], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [209496515, 1099721125315, 1099721126339, 8765807047, 4437353927, 41723371], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [30072791539, 17187963379, 8598100467], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 124 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 124 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 124 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 124 48 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [52805856295, 35491913787, 13345988939, 8983982411, 1100224445771, 1100224446795], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30710328663, 17775168855, 1099821789611, 1099821790635, 1099821791659, 4538016187], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4437354939, 92056031, 1099603684831, 12943330791, 4353465831, 25777827315], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17187965427], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 124 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 124 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 124 43 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [48527734827, 27002644539, 26381810015, 13480203615, 13262169439, 8832988515], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100123783523, 1099872122271, 1099872123295, 1099872124319, 4538017211, 1099754679739], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099754680763, 8614811119, 4319912431, 25777895923], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i30 : checks (tilesOf batches) 124 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 124 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 124 46 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [52621378607, 10007394371, 22271460659, 17724841267, 13295726899, 4504465815], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099905677719, 1099905678743, 1099905679767, 8832916919, 4504463799, 1099687571915], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099687572939, 41724395, 41725419, 17187964403, 8598100467, 4303136243], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i33 : checks (tilesOf batches) 124 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 124 41 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (i41)) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [48326479923, 1534902339, 17926164791, 17624180023, 9000761655, 1099888900507], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099888901531, 8849761699, 4470911395, 1099788239283, 1099670794703, 1099670795727], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4370245091, 75279843, 12926554603, 4336689643], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 124 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 124 44 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤124) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 13 where
  orders := orders
  covers := by
    intro a ha box
    change 8+a.b≤132 ∧ 7+a.j≤55 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group13
