import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass17

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group17
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27752860679, 44968323091, 134039229471, 48307852535, 48106669303, 30960432375], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34567521735, 21682694599, 13059211727, 174313935, 38744821219, 51545912823], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [25776253429], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i3 : checks (tilesOf batches) 125 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 125 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 125 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 125 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 125 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 125 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 125 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [40538478603, 49146314779, 104108879915, 39533441315, 39332256035, 17974935843], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [25977592263, 13092763079, 47418644943, 47334902243, 8680359395, 90427875], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [30071224823], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i6 : checks (tilesOf batches) 125 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 125 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 125 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 125 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 125 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 125 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [44884304911, 65856622623, 69950541875, 30675210587, 26229256539, 4905487707], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [47771046263, 30608032119, 17337397707, 4486055371, 47351604703, 21514920431], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [40095215, 40096239, 8613247475, 42956051959], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i9 : checks (tilesOf batches) 125 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 125 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 125 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 125 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 125 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 125 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [44985298963, 74262076451, 48609993787, 43660631375, 30725474639, 17639319939], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17505172867, 1100004708739, 8730688979, 4402170323, 25809816047, 17219954159], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [40094191, 40095215, 8613247475, 6538740], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i12 : checks (tilesOf batches) 125 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 125 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 125 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 125 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 125 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 125 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [49129470999, 82684308519, 23024811075, 39483108651, 30792652075, 9452041515], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8781021623, 4469280183, 47368388059, 21598737883, 4418940379, 1099602054627], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099602055651, 4368613863, 73648615, 38677933555], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i15 : checks (tilesOf batches) 125 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 125 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 125 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 125 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 125 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [49112827931, 74161551403, 18746622019, 35137878335, 26413800767, 9351444799], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4502832571, 4418948539, 47368456667, 17303772635, 8713908699, 1099635609051], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099635610075, 40093167, 1099551721967, 4301503991], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i18 : checks (tilesOf batches) 125 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 125 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 125 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 125 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 125 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53223379999, 78322370611, 30876469543, 30624885031, 9284340007, 17438058927], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8831352239, 47536231859, 30356440499, 1099685939663, 1099685940687, 1099685941711], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17236731371, 4351835627, 56870379, 40090095], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i21 : checks (tilesOf batches) 125 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 125 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 125 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 125 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57350643747, 61293566007, 26380245327, 21900735823, 4855156047, 43392262543], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26212470159, 8864904631, 4536385975, 1099786602935, 1099652386263, 1099652387287], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8680352227, 23314931, 23315955], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i24 : checks (tilesOf batches) 125 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 125 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 125 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 125 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [57300380711, 48492553275, 21967840615, 17538727271, 1100122149223, 39130852743], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21951059335, 4536384959, 4469278143, 1099753049535, 12992097759, 56870379], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099568499179], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i27 : checks (tilesOf batches) 125 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 125 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 125 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 125 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [61444421675, 31480525887, 34970106215, 22051724647, 13243757971, 8864908691], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099937599891, 4368614871, 1099652386263, 8646800875, 4335059435, 1099568499179], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21498142195, 23314932], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i30 : checks (tilesOf batches) 125 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 125 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 125 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [61394158639, 18696290371, 30708696415, 17823868255, 9217227103, 4536386991], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4452502959, 1099652386263, 1099652387287, 56870379, 1099568499179, 4301502967], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [6537716], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i33 : checks (tilesOf batches) 125 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 125 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 125 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [65538134067, 1667420235, 30775873855, 22018175295, 4972595519, 13092762051], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4502831555, 1099635610075, 1099602053603, 1099602054627, 25826595307, 12941766123], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4301503991, 6538740], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 125 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 125 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 125 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 17 where
  orders := orders
  covers := by
    intro a ha box
    change 13+a.b≤138 ∧ 6+a.j≤58 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group17
