import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass21

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group21
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27922009095, 44918974483, 125433369631, 1802423367, 44030448883, 48040345843], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26649473267, 26129301939, 17539440051, 8848847303, 8798584263, 1099787389383], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [43074071019, 38728914423, 74284535, 1099586063863, 4352622075, 57656827], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8597254663], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
private theorem i43 : checks (tilesOf batches) 129 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 129 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36496283659, 53224029207, 99747590187, 31095288083, 39299420435, 22169958675], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43342577067, 4688013737, 21800849839, 13177366959, 8798583227, 4486841787], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099837722043, 1099636393451, 1099636394475, 4369398255, 1099619615215, 8664295927], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4369397239, 17220669951, 40805887, 24100355], by decide +kernel⟩
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
private theorem i46 : checks (tilesOf batches) 129 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [44885353487, 61545730079, 69850729523, 26414517571, 26230040899, 9150907715], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39282495859, 26397735283, 8899176883, 8781739443, 1099871273395, 1099770611147], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099770612171, 1099770613195, 43124401631, 17321334239, 4402951651, 1099669945827], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4335774207, 4335841791, 40876543, 12908926467, 24028675], by decide +kernel⟩
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
private theorem i49 : checks (tilesOf batches) 129 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [44969504787, 61478689827, 56999385143, 22052510031, 21851189583, 4805609807], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35037928807, 22153101671, 8815292843, 4520394155, 1099904828843, 1099770612171], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099770613195, 13076699611, 4486769115, 4386107875, 1099669944803, 1099669945827], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099669946851, 43023806967, 57651707, 57652731], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i12 : checks (tilesOf batches) 129 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 129 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 129 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44952861719, 61411649575, 44164817979, 30793296219, 22136326491, 17690435931], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13278033247, 8949581151, 1099854497207, 1099854498231, 1099854499255, 4486837695], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099820940735, 1099820941759, 8798511575, 4453215703, 1099619612143, 1099619613167], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [43023810039, 17237445115, 57581051, 40807935, 40874495], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 129 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 129 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 129 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [44902664219, 57116750891, 35625282623, 30709478751, 22002177375, 13278031215], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13143883119, 1100156489071, 1099888049583, 1099888050607, 1099888051631, 1099888052655], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4469992911, 1099753829839, 1099753830863, 13059921375, 4469990879, 43057433071], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [25827309051, 57577979, 57585147, 57651707], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 129 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 129 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 129 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 129 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 129 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53123568671, 69682956339, 1533987911, 26582288667, 26313925915, 9201172763], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39114790299, 26213186971, 8966284703, 8815292831, 1099955158431, 1099888050607], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099888051631, 1099888052655, 1099854499255, 208581079, 1099720275415, 1099720276439], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8764955103, 4352550395, 57585147, 25777044999], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 129 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 129 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 129 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 129 45 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57234055203, 56865167415, 22153173295, 21901521199, 4839164207, 34987598195], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22102771059, 8848847255, 4537171351, 1099988714903, 1099871275443, 1099871276467], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13059923411, 4469992915, 1099737054675, 1099737055699, 1099720275415, 1099720276439], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8630738431, 4335774207, 40874495], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 129 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 129 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 129 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 129 48 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [52972710951, 48325566523, 22002180415, 17539447103, 1100357815615, 34920557951], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17757540735, 4587501975, 1099988713879, 1099988714903, 1099988715927, 8865621439], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4503548351, 1099686722015, 1099686723039, 91206131, 1099602834931, 4318995971], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [24030723, 30071942663, 7245316], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 129 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 129 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 129 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 129 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [52888893483, 35574950975, 13328362851, 8966356323, 1100206819683, 1100206820707], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30675925359, 17740765551, 1099820940735, 1099820941759, 1099820942783, 4520324559], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4419728847, 107984367, 1099619613167, 12959259127, 4369328631, 25793755651], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [24024579, 7320068], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 129 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 129 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 129 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [52788233263, 22807492675, 26448069979, 17723990363, 9083729243, 4587504003], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100072601987, 1100072603011, 1099770610123, 1099770611147, 4419728851, 1099737054675], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8764957151, 4469992927, 91207155, 1099602835955, 21515634175, 40803839], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i33 : checks (tilesOf batches) 129 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 129 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 129 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [52704415795, 10040034375, 22220280139, 17690437963, 4855872843, 1099938383267], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099938384291, 1099938385315, 8815290823, 4486837703, 1099737054675, 1099737055699], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [74429943, 1099586058743, 17220669951, 8630740479, 40874495], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤129) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 21 where
  orders := orders
  covers := by
    intro a ha box
    change 9+a.b≤138 ∧ 7+a.j≤58 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group21
