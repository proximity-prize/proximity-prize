import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass32

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group32
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23406185479, 40722375695, 87078620191, 57282764859, 48071855419, 39448575291], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21950014871, 21815868823, 1100020438423, 38894636503, 13007830507, 4434677227], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [34449030651, 21564137979, 47317005823, 38710371843, 8612198923, 4317234699], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [5492239, 5493263], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i3 : checks (tilesOf batches) 131 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 131 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 131 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 131 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 131 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 131 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 131 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36309374987, 53255552023, 87045337131, 18846237767, 35237425471, 30774760767], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30607062335, 47635709363, 39012363699, 13158823363, 8729642455, 4417901015], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [43156117983, 21631243755, 13041380843, 1099617784311, 1099617785335, 4350789115], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099601006075, 4334009863, 34381852171, 22267403, 22268427], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i6 : checks (tilesOf batches) 131 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 131 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 131 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 131 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 131 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 131 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40688821263, 82699766815, 61409958967, 43911105831, 35220650279, 26278534507], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21899753835, 4803776875, 8779971027, 4468229587, 1099768778195, 17353055719], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8763191783, 1099684893159, 1099684894183, 47350490615, 30170839543, 17285945847], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099584226815, 1099584227839, 4334009859, 42955003407, 5488143, 5489167], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i9 : checks (tilesOf batches) 131 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 131 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 131 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 131 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 131 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 131 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [44917075987, 82683124771, 44280425535, 39616208167, 30908974375, 30690944295], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17453794687, 13192308159, 8863856063, 8763195839, 1099835887043, 1099835888067], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099835889091, 47400825323, 1099668111851, 1099668112875, 1099668113899, 25892652531], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13007757811, 4350785027, 55819779, 4317229579, 38660039183], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i12 : checks (tilesOf batches) 131 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 131 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 131 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 131 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 131 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 131 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44917275671, 74177210407, 39985459263, 35237423423, 26513345855, 26295314751], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13175604607, 1100121101695, 8930896319, 8830301631, 4501782975, 1099819108807], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099819109831, 1099819110855, 47384116719, 21597687283, 12991047155, 1099634557427], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099634558451, 4384339451, 89374203, 8595416591], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 131 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 131 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 131 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 131 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 131 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53205420059, 86827301935, 5860675659, 31026347279, 35002686735, 22067462415], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8830304671, 1099986881951, 43374299563, 30489540011, 17520827819, 13142045099], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099835888067, 1099835889091, 1099735220699, 1099735221723, 1099735222747, 4451447275], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [156482027, 1099668110827, 17285944823, 8662526463], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 131 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 131 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 131 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 131 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 131 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53138379807, 78270990387, 1565709387, 30875420955, 26395978011, 17755784475], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43391145375, 26228130207, 4518561191, 1099953327527, 1099953328551, 8947673523], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8847078835, 4501782963, 1099835889091, 13091642847, 1099718445535, 1099684889063], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099684890087, 4367562227, 1099634556403, 39040519, 39041543, 42971780619], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4317228555, 25775211023], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 131 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 131 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 131 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 131 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 131 53 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61493567523, 61208632375, 22168116539, 21933241659, 9098743099, 39331062123], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22168045931, 8863856043, 4518560171, 1099936549291, 1099886218679, 1099886219703], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099886220727, 8779899363, 8729636323, 1099701666275, 1099701667299, 139704815], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099651333615, 4334005767, 39040519, 38660039183], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 131 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 131 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 131 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 131 48 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [57232223271, 52669031483, 22000346443, 21815868747, 1100339205451, 34985766263], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22067450231, 8813526431, 1099986880927, 1099986881951, 1099986882975, 8847010251], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4535334347, 1099751996887, 1099751997911, 1099751998935, 17218834951, 8628971015], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [39040519, 39041543, 4317229579, 34365074959], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 131 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 131 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 131 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 131 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [61376264235, 35640226879, 30841862487, 22101006679, 17621496151, 8914191731], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100171432307, 1100171433331, 8813523395, 4468227523, 1099835884995, 1099835886019], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099835887043, 13024532975, 8729635311, 1099651333615, 1099651334639, 89372155], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [89373179], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 131 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 131 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 131 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [65537082415, 18561025095, 26647561531, 26328867131, 17655119163, 1100037214611], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100037215635, 4552113583, 1099919771055, 1099919772079, 1099919773103, 13192307139], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8813523395, 1099651333615, 1099651334639, 4384338427, 89373179, 25775212047], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12890382863], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 131 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 131 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 131 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [69697835059, 1532154955, 30791536927, 26278539551, 9182629151, 8998072731], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8830303643, 1100003658139, 1099919773103, 1099919774127, 1099869443515, 21731905999], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8847010255, 1099751996887, 1099751997911, 1099751998935, 4334007807, 22263307], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [22264331, 17185280527, 8595416591, 4300452367], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 131 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 131 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 131 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤131) (hj : a.j≤53) :
    Covered orders a ∨ Low6960Gate.Gated ((32 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 32 where
  orders := orders
  covers := by
    intro a ha box
    change 10+a.b≤141 ∧ 6+a.j≤59 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group32
