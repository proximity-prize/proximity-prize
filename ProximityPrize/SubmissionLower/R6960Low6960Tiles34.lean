import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass34

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group34
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23591914503, 19263398927, 10639915031, 2033206297, 2033207321, 1999653919], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1882214431, 1781552159, 19181230115, 27755506727, 19115247667, 6213573687], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [6196798523, 1885056063, 1851502655, 1817949247, 1767618627, 1734065219], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1717289027, 1666958407, 1633404999, 1616628807, 1566298187, 1549521995], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099786081727, 1099769303491, 30288401867, 1099735748043, 1099718969807, 1099685414359], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099651858911, 30187737571, 1099635080675, 1099601525227, 1099567969779, 1099534414331], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [30070296063], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i3 : checks (tilesOf batches) 127 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 127 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 127 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 127 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 127 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 127 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 127 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [23575140363, 14951657491, 6328172569, 2033207321, 1982876703, 1865437215], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1764774943, 19181230115, 27755506727, 14820280371, 6213572663, 6196797499], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1901832251, 1851501631, 1817948223, 1767617599, 1717286979, 1683733571], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1666957379, 1616626759, 1583073351, 1566297159, 1515966539, 1499190347], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099836413363, 1099819635127, 1099786079679, 1099769301443, 26010211783, 1099735745995], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099702190547, 1099685412311, 30204514783, 1099651856863, 1099618301415, 1099567968755], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [30087073275, 1099534413307], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i6 : checks (tilesOf batches) 127 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 127 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 127 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 127 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 127 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 127 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [19263398925, 10639915029, 2033206297, 2033207321, 1982876703, 1865437215], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1747997727, 19181230115, 27755506727, 14820280371, 6213572663, 1901830203], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1901831227, 1885055035, 1817947199, 1784393791, 1734063167, 1683732547], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1650179139, 1616625731, 1566295111, 1549518919, 1515965511, 1482412107], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1448858699, 1099886744999, 1099853189551, 1099836411315, 1099802855867, 1099786077631], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [26026988995, 1099752522183, 1099718966735, 1099685411287, 30204514783, 1099651855839], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099601523179, 1099567967731, 30087073275, 6007292], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i9 : checks (tilesOf batches) 127 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 127 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 127 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 127 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 127 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 127 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [14951657489, 6328172569, 2033207321, 1999653919, 1882214431, 1764774943], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [19181230115, 27755506727, 14820280371, 6213572663, 1901830203, 1901831227], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1851500603, 1801169983, 1750839359, 1717285951, 1666955331, 1616624707], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1583071299, 1549517895, 1515964487, 1482411079, 1432080459, 1415304267], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099920299423, 1099903521187, 1099869965739, 1099836410291, 1099802854843, 1099786076607], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [26010211783, 1099752521159, 1099702188499, 1099668633051, 30187737571, 1099635077603], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099584744943, 1099551189495, 30070296063], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i12 : checks (tilesOf batches) 127 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 127 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 127 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 127 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 127 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 127 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [10639916055, 2033207321, 2016431135, 1915768863, 1798329375, 19181230115], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [27755506727, 14820280371, 6213572663, 1901830203, 1901831227, 1851500603], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1784392767, 1734062143, 1700508735, 1633400899, 1599847491, 1566294083], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1515963463, 1482410055, 1448856647, 1415303243, 1381749835, 1099953853847], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099920298399, 1099903520163, 1099869964715, 1099836409267, 1099802853819, 1099769298371], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099735742923, 25976657359, 1099685410263, 1099651854815, 30154183147, 1099601522155], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099551189495], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i15 : checks (tilesOf batches) 127 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 127 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 127 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 127 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 127 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [2033207321, 2016431133, 1949323295, 1815106591, 19181230115, 27755506727], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [14820280371, 6213572663, 1901830203, 1901831227, 1851500603, 1784392767], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1734062143, 1683731519, 1633400899, 1583070275, 1549516867, 1499186247], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1465632839, 1432079431, 1381748811, 1364972619, 1099970631059, 1099953852823], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099920297375, 1099886741927, 1099853186479, 1099819631031, 1099786075583, 1099735742923], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [30254847443, 1099702187475, 1099651854815, 1099601522155, 30120628723, 1099551189495], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i18 : checks (tilesOf batches) 127 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 127 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 127 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 127 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 127 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [1848661023, 19181230115, 27755506727, 14820280371, 6213572663, 1901830203], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1901831227, 1851500603, 1784392767, 1734062143, 1683731519, 1633400899], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1583070275, 1549516867, 1499186247, 1448855623, 1415302215, 1381748811], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1348195403, 1099987408271, 1099953852823, 1099937074587, 1099903519139, 1099853186479], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099819631031, 1099786075583, 1099735742923, 1099702187475, 30221293019, 1099651854815], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099601522155, 1099551189495], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i21 : checks (tilesOf batches) 127 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 127 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 127 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 127 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 127 53 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [14886264867, 27738730539, 14820281395, 6213573687, 1901831227, 1851500603], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1784392767, 1734062143, 1683731519, 1633400899, 1583070275, 1549516867], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1482409031, 1448855623, 1415302215, 1364971595, 1331418187, 1100004185483], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099970630035, 1099937074587, 1099903519139, 1099869963691, 1099819631031, 1099786075583], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099735742923, 1099702187475, 1099651854815, 1099601522155, 1099551189495], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 127 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 127 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 127 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 127 48 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [27755506727, 14820280371, 6213572663, 1901830203, 1901831227, 1868277819], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1801169983, 1750839359, 1700508735, 1633400899, 1583070275, 1549516867], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1482409031, 1448855623, 1415302215, 1364971595, 1331418187, 1100004185483], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099970630035, 1099937074587, 1099903519139, 1099869963691, 1099819631031, 1099786075583], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099735742923, 1099685410263, 1099635077603, 1099584744943, 1099534412283], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 127 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 127 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 127 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 127 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [23443765291, 10525315123, 6213573687, 1901831227, 1885055035, 1817947199], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1750839359, 1700508735, 1633400899, 1599847491, 1549516867, 1482409031], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1448855623, 1415302215, 1364971595, 1331418187, 1100004185483, 1099970630035], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099937074587, 1099903519139, 1099869963691, 1099819631031, 1099769298371, 1099735742923], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099685410263, 1099635077603, 1099567967731, 6007292], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 127 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 127 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 127 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [19132023855, 10508539959, 1901831227, 1901832251, 1817947199, 1767616575], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1717285951, 1650178115, 1599847491, 1549516867, 1499186247, 1448855623], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1415302215, 1364971595, 1331418187, 1100004185483, 1099970630035, 1099937074587], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099903519139, 1099853186479, 1099819631031, 1099769298371, 1099718965711, 1099668633051], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099618300391, 1099567967731], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 127 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 127 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 127 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [14820282419, 6196797499, 1901832251, 1834724415, 1784393791, 1734063167], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1666955331, 1616624707, 1566294083, 1499186247, 1465632839, 1415302215], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1364971595, 1331418187, 1100004185483, 1099970630035, 1099937074587, 1099886741927], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099853186479, 1099802853819, 1099752521159, 1099702188499, 1099651855839, 1099601523179], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099551190519], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i36 : checks (tilesOf batches) 127 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 127 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 127 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤127) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((34 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 34 where
  orders := orders
  covers := by
    intro a ha box
    change 14+a.b≤141 ∧ 6+a.j≤59 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group34
