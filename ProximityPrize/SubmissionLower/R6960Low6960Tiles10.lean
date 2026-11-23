import ProximityPrize.SubmissionLower.R6960Low6960AllocTiles
import ProximityPrize.SubmissionLower.R6960Low6960Mass10

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group10
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27707313159, 40425760787, 86831943711, 35628164155, 35225424127, 35007395071], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43345680639, 17508833631, 13096430955, 8767913323, 1099773492631, 1099773493655], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099773494679, 21719905691, 13129977243, 4405833119, 1099739936159, 1099739937183], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4456160687, 4405831087, 38765472187, 1099622493627, 1099622494651, 43754955], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099555383755, 34386629071], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 116 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 116 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 116 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 116 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 116 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 116 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36281325579, 74047568919, 69769724975, 39486766351, 30863353103, 26316801323], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26165879083, 9053125931, 8851792267, 8751132043, 1099823823243, 1099756715419], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099756716443, 1099756717467, 17341056431, 8751126959, 144420275, 1099656049075], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099656050099, 4321945035, 30091732431, 10200531, 10201555], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i6 : checks (tilesOf batches) 116 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 116 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 116 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 116 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 116 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 116 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40559911951, 78309116959, 48429176887, 39470058767, 30796313871, 30578218255], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17441731923, 13197088139, 8851793291, 4540051851, 4439390611, 1099790270867], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099790271891, 1099639273911, 1099639274935, 25863878079, 12978983359, 60535239], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099572164039, 4338722251, 43757003, 38664818131], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i9 : checks (tilesOf batches) 116 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 116 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 116 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 116 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 116 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 116 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [44754415635, 82570599459, 27105340479, 39419731211, 30729209099, 30561510667], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099874157951, 13146760579, 8784688515, 4472947075, 21652800939, 13046095275], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099672830383, 4372280755, 1099656052147, 43026887107, 34436963779, 21552136643], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4372278723, 60536263, 1099572165063, 8600133075, 4305168851], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i12 : checks (tilesOf batches) 116 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 116 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 116 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 116 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 116 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48932076567, 82570669095, 10110090307, 35158387983, 30662103311, 22021910799], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8784687507, 17408168351, 13062874527, 43127553451, 34537630123, 1099672829359], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099672830383, 1099672831407, 4338726339, 8633689547, 4338725323, 21501808079], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [26982863], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 116 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 116 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 116 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 116 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 116 47 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53126514715, 78292548655, 30813093147, 26367204635, 13482309915, 43211442583], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30326617495, 17341062571, 8734355883, 4405837227, 1099689608619, 60538311], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [60604871, 17206842831, 4321948111, 26982863, 8600136147], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i18 : checks (tilesOf batches) 116 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 116 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 116 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 116 42 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (i42)))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [69937353759, 48496285751, 43563767107, 30662099267, 17643053411, 17475286371], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8734356907, 4405838251, 60604871, 60605895, 4321949135, 26983887], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [30074962387, 12895101395, 8600138195], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i21 : checks (tilesOf batches) 116 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 116 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 116 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 116 45 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [74165280803, 31484192827, 43614101815, 26434243895, 17424951695, 8801467791], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4372282819, 77383107, 12928657867, 4338727371], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i24 : checks (tilesOf batches) 116 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 116 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 116 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 116 48 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [78376365095, 14488942659, 39386246439, 30695724327, 17777276199, 8717579703], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21568918975, 12978990527, 4372283843], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i27 : checks (tilesOf batches) 116 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 116 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 116 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [82604292139, 39403026715, 30678950171, 5076926747, 21636030895, 8751135151], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [38681672143], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i30 : checks (tilesOf batches) 116 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 116 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 116 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69836833839, 35007399227, 26283321659, 647742779, 17307511223, 8717581751], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i33 : checks (tilesOf batches) 116 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 116 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 116 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [57102995507, 30544728419, 17643057507, 479970659, 12895105491, 4305240531], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i36 : checks (tilesOf batches) 116 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 116 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤116) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 10 where
  orders := orders
  covers := by
    intro a ha box
    change 16+a.b≤132 ∧ 6+a.j≤55 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group10
