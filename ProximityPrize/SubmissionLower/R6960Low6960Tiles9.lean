import ProximityPrize.SubmissionLower.R6960Low6960AllocTiles
import ProximityPrize.SubmissionLower.R6960Low6960Mass9

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group9
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27722189831, 40424122387, 86847213599, 35626656827, 35223851267, 30794806531], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34854900995, 13044595051, 13212358011, 13094921595, 8766403963, 1099805606291], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099805607315, 1099721651623, 1099721652647, 1099721719207, 4421100975, 1099688095151], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099688096175, 21634446771, 13044583859, 38780676539, 4353990091, 42247631], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099553876431, 34385121747], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 117 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 117 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 117 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 117 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 117 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 117 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36212512779, 61345643543, 82552387627, 30710921487, 30543223055, 13413693711], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39317486907, 30660519227, 13145250179, 8799955331, 8716072323, 1099822383503], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099822384527, 1099738428835, 1099738429859, 1099738496419, 17356326315, 1099654539703], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099654540727, 1099654541751, 4387543491, 4370768323, 38730340807, 25828746699], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17238884811, 8598623703, 8692183, 8693207], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 117 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 117 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 117 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 117 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 117 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 117 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40457544719, 86763260959, 39854514235, 35341290735, 35089707247, 34905232623], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8850291035, 1100040422747, 13245912435, 13111698803, 8766403955, 1099772051867], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [25979744671, 13128469919, 1099755206047, 1099755207071, 1099755273631, 4437878187], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099704872363, 1099704873387, 43058865599, 4353990091, 42247631, 42248655], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [25795260883], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 117 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 117 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 117 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 117 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 117 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 117 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40541696019, 82501916707, 31314913339, 35240630523, 30778031355, 34821414139], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099990090087, 1099990091111, 13212360043, 13094923627, 8749628779, 1099805539731], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4421103007, 1099755206047, 1099755207071, 21684845991, 13044585895, 4387546555], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099620986303, 1099620987327, 34401901007, 8632178127, 4337213903, 25471443], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [42958205399], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 117 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 117 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 117 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 117 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 117 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44669090839, 86746687527, 9991142467, 30996064499, 34955561203, 26298592499], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8833510771, 8749627763, 17540876675, 8934169987, 8816732547, 1099805607315], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099771984283, 1099771985307, 1099772051867, 1099688097199, 38814236083, 30224377267], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4370770363, 1099637764539, 42248655, 1099553877455, 17205331411, 4303658455], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8693207], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 117 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 117 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 117 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 117 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 117 47 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57185028123, 73928966191, 26516619531, 26298588427, 13413693707, 39166560607], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26281734495, 8917392779, 8799955339, 4471436683, 1099839094155, 1099839160715], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099839161739, 1099654542775, 1099654609335, 17272442303, 4370770367, 1099620987327], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [25471443, 25472467, 12893588951], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 117 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 117 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 117 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 117 42 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (i42)))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61362623519, 56866541619, 22037106987, 21869406507, 4773429547, 39267226951], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26332069191, 8816732555, 4488213899, 1099839094155, 1099755274655, 1099755275679], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13011032499, 1099637765563, 1099637832123, 4370770371, 1099604210115, 21517073871], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12927145423, 4320437715, 8695255], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 117 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 117 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 117 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 117 45 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65556996131, 39820959803, 35056148787, 22171321651, 21953289523, 13162034515], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100073977171, 4454659479, 1099788762519, 1099788829079, 13044587943, 4471434663], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099620988351, 1099621054911, 8632180175, 4337215951, 25473491], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i24 : checks (tilesOf batches) 117 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 117 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 117 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 117 48 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [78240640039, 14286108739, 35190369543, 30660595975, 21986849031, 8799957379], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099805539731, 1099805606291, 1099805607315, 17456992663, 8850285975, 4387549623], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099654609335, 30106938831, 17222110671, 42250703, 42317263, 4303660503], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8695255], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 117 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 117 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 117 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69717817387, 10041474115, 30845139227, 22137837851, 21902962971, 8833511811], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099755273631, 1099755274655, 1099755275679, 13011032507, 8682514875, 109360575], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [109427135, 4320438739, 25473491, 30073453015], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i30 : checks (tilesOf batches) 117 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 117 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 117 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69684331567, 26566952215, 26298589463, 9169059095, 13145252247, 8766402967], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4404395427, 1099738498467, 1099621055935, 1099621056959, 4370772419, 92649923], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [25778488791, 8598626775, 4303662551, 8762839], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i33 : checks (tilesOf batches) 117 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 117 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 117 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [56900096051, 22137770291, 21902960947, 4823761203, 8850287003, 4521768347], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4421107099, 1099671389619, 1099637833147, 1099637834171, 21500301779, 4320507347], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i36 : checks (tilesOf batches) 117 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 117 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤117) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 9 where
  orders := orders
  covers := by
    intro a ha box
    change 15+a.b≤132 ∧ 6+a.j≤55 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group9
