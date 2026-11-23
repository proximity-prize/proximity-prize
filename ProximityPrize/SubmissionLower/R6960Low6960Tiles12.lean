import ProximityPrize.SubmissionLower.R6960Low6960AllocTiles
import ProximityPrize.SubmissionLower.R6960Low6960Mass12

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group12
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27719502855, 40757241875, 87029403679, 31681717307, 39566790959, 30943443247], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34970048815, 4569808319, 17471412675, 13109407171, 34550123995, 8646667771], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4334926331, 30087870979, 23183875, 6404615, 6405639], by decide +kernel⟩
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
private theorem i43 : checks (tilesOf batches) 129 43 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36377729035, 53156002839, 86928945195, 30993772835, 30742188323, 17874137379], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39113735579, 34785420699, 17437856199, 8864769479, 4519473611, 4452366795], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099769692619, 38761339375, 1099601918451, 1099601919475, 30087800323, 21497939459], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [23179779, 23180803, 8596332039], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i46 : checks (tilesOf batches) 129 46 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40656446479, 57249778719, 65554842671, 26447217983, 26212344127, 4922129727], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39248022899, 26380039539, 8948654507, 8831217067, 4502698411, 1099719360983], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099685804511, 1099685805535, 13042225635, 4368477671, 1099652249063, 43056375279], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [56733179, 1099568361979, 34382696963, 4318142979, 23177731, 25776125447], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (i41))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40740663315, 65604966435, 44197517367, 35154385215, 22286400831, 22034814271], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13277179235, 4687248739, 4452363715, 1099803243971, 1099803244995, 1099803246019], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099803247043, 8864699847, 8780882375, 1099635469803, 1099635470827, 4368474615], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [73509367, 34399541759, 21497937411, 42955780615], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i12 : checks (tilesOf batches) 129 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 129 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 129 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44817726487, 65504372775, 27118315579, 30909819179, 22219360555, 17756627243], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8814441855, 1100088459647, 8814436791, 4469140919, 1099853575607, 1099853576631], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099853577655, 38862142935, 30272349655, 13059000799, 8747325919, 1099669024227], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099669025251, 107062767, 1099618691567, 12958336503, 4301363719, 6398471], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 129 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 129 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 129 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [44750751771, 56981615659, 22806572095, 26531034431, 22018036031, 17588922687], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100088458623, 1100088459647, 4569803171, 1099937460643, 1099937461667, 1099937462691], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8881476035, 4586577347, 4502693315, 38912477643, 25994162635, 1099652247015], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12941561335, 73508343, 1099585137143, 21497868803, 12908005891], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 129 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 129 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 129 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 129 42 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (i42)))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [48794129439, 61092103215, 1533132867, 22286402839, 22018039063, 13394621719], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34852459923, 21967632787, 1100004570515, 1100004571539, 1100004572563, 8915033499], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4586580379, 1099971015067, 1099870355891, 8780812763, 1099669023203, 1099669024227], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4418805227, 123839979], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 129 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 129 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 129 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 129 45 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [48727154723, 48307867699, 1516355651, 17874063667, 17605633331, 8998992179], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30607827335, 21934145927, 1099987794327, 1099987795351, 4653688219, 4519472539], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099971016091, 1099887133103, 1099736133075, 1099736134099, 8747325915, 90285555], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099601914355, 17253302775, 8646596087, 23175683, 8596329991], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 129 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 129 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 129 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 129 48 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [52787244071, 35490144315, 13360996683, 8982212939, 1100306562379, 1100306563403], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30742113619, 17806953811, 1099903906219, 1099903907243, 1099903908267, 4569801151], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099820018111, 1099820019135, 13008670187, 4418805227, 25843166711, 12958337527], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [23176707], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 129 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 129 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 129 43 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [52703426603, 22722686015, 26497481027, 17756624195, 13310732611, 1100172343659], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100172344683, 1100172345707, 4519471531, 1099903906219, 1099903907243, 8831145423], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4502692303, 1099669023203, 1099669024227, 21565045235, 8680149491, 23175683], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [23176707], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 129 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 129 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 129 46 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [52602831919, 9988847683, 22269691183, 17723071791, 13293957423, 1100004569491], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100004570515, 1100004571539, 1100004572563, 1100004573587, 8881544627, 4502694323], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099652245991, 1099652247015, 17286858223, 8696994287, 56731131], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i33 : checks (tilesOf batches) 129 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 129 41 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (i41)) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [48274313267, 1499578435, 22118699307, 17622477099, 4771134763, 4636912023], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099987792279, 1099987793303, 1099987794327, 1099954240927, 1099903910315, 13142888903], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4569801159, 123841003, 1099635469803, 8596263431, 4301364743], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤129) (hj : a.j≤48) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 12 where
  orders := orders
  covers := by
    intro a ha box
    change 3+a.b≤132 ∧ 7+a.j≤55 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group12
