import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass30

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group30
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [40677346311, 66397811735, 87503828011, 6168037447, 64804320683, 26149696939], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43060891115, 64519027183], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i3 : checks (tilesOf batches) 128 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 128 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 128 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 128 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 128 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 128 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 128 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [53579618315, 83275893791, 53479709751, 64787467695, 60492647855, 51617274355], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i6 : checks (tilesOf batches) 128 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 128 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 128 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 128 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 128 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 128 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [62153040911, 87503822883, 27676423231, 64837869987, 47658082723, 60207277555], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i9 : checks (tilesOf batches) 128 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 128 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 128 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 128 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 128 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 128 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [66498474003, 87453495339, 10463003719, 64854651295, 30494994847, 64435139075], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i12 : checks (tilesOf batches) 128 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 128 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 128 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 128 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 128 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [70743178263, 83208929327, 60492579247, 17542987183, 68763663867], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i15 : checks (tilesOf batches) 128 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 128 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 128 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 128 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 128 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [70776801307, 70491802675, 60308098523, 4473539035], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i18 : checks (tilesOf batches) 128 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 128 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 128 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 128 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 128 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [74987951135, 53479709751, 73075480055], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i21 : checks (tilesOf batches) 128 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 128 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 128 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 128 45 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [75004796963, 40578099259, 73041928703], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i24 : checks (tilesOf batches) 128 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 128 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 128 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 128 48 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [79148772391, 23364679747, 68881182175, 30226559455], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i27 : checks (tilesOf batches) 128 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 128 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 128 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 128 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [79132063787, 10463003719, 68881185247, 17341660639], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i30 : checks (tilesOf batches) 128 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 128 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 128 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [74870653999, 1873071175, 68830922219, 4406430187], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i33 : checks (tilesOf batches) 128 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 128 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 128 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [66381385779], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i36 : checks (tilesOf batches) 128 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 128 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [53479709751], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i39 : checks (tilesOf batches) 128 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 128 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤128) (hj : a.j≤51) :
    Covered orders a ∨ Low6966Gate.Gated ((30 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 30 where
  orders := orders
  covers := by
    intro a ha box
    change 14+a.b≤142 ∧ 7+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6966Allocation.Group30
