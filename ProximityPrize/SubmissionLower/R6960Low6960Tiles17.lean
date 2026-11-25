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
  ⟨unpack [2147552261, 989925385, 10721301513, 27734581261, 82630687765, 87111076913], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1765597261, 35487027449, 48221273357, 39665102093, 34950845781, 34799925589], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4953333077, 17418795457, 13073501633, 47382672869, 25907992037, 17318130149], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4382903793, 4349351409, 1099582791159, 1099582857719, 38708930041, 8627537405], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [30085516801, 20829697, 20830721], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i51 : checks (tilesOf batches) 129 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [19009705993, 40334863377, 86959608861, 61425231929, 43876111645, 43658150173], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26209987953, 21847984497, 1100136440179, 47650975141, 43238562241, 30320329161], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21696913865, 8744978893, 4433237453, 1099750563279, 13023164893, 1099599566323], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099599567347, 4349348341, 71160309, 42987118077, 21495652865, 8610757121], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4315792897, 4050437], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i46 : checks (tilesOf batches) 129 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 129 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27885773837, 57230114841, 86959945769, 22988770373, 35202431273, 30756543785], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34850258217, 43607671145, 35017878889, 13190938017, 8778534321, 8711428529], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17401945553, 13090271697, 1099733785043, 1099733786067, 1099733787091, 1099666673123], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099666674147, 1099666675171, 4399677933, 104712685, 21545914869, 8593977861], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4299013637], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i49 : checks (tilesOf batches) 129 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36291686417, 74141815837, 74125581365, 39564367149, 30924242221, 26394467649], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30471403841, 9130858817, 13157382565, 8812087717, 8728204709, 1099784118727], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099767338443, 1099767339467, 1099767340491, 17368391129, 8778527193, 1099683449311], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099683450335, 1099683451359, 47399449057, 4416454121, 121488873, 30102289917], by decide +kernel⟩
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
private theorem i52 : checks (tilesOf batches) 129 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44647070741, 82614511653, 44211877953, 35336579353, 35051441433, 34883809561], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13140612465, 13207646617, 8895971737, 8795311513, 43322523053, 1099868002739], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099868003763, 1099868004787, 21764017601, 13157311937, 1099750559183, 1099750560207], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750561231, 138265061, 1099649893863, 1099649894887, 4416452073, 4382899689], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [20823553, 34363632133, 12888942085], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 129 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 129 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 129 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 129 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53035943961, 86825729069, 18593140809, 35219209485, 34967625997, 30555292941], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43507075457, 30622250369, 13140608389, 1099951887775, 1099951888799, 1099951889823], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951890847, 17519387041, 8912680353, 8828862881, 1099784113607, 1099784114631], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17351611869, 1099683447263, 1099683448287, 1099683449311, 4382897649, 87932401], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8661084661], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 129 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 129 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 129 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 129 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 129 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61424686109, 86792310833, 35051442441, 34867033353, 9265076489, 39396660565], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30722915669, 13224424837, 13123831173, 8761759109, 1099884781999, 17485831601], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8862347697, 1099868001715, 1099868002739, 1099868003763, 4433233345, 1099800890819], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800891843, 4399676889, 1099649893863, 1099649894887, 25840877045, 17250949621], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4366119413, 4332567029, 1099582783991, 8627531261, 20822529, 20823553], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 129 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 129 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 129 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 129 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 129 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [69846982689, 65434985529, 26327360813, 26159661357, 4819115309, 39497326897], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26545391921, 8879194509, 8778534285, 1100018997647, 1099884780975, 1099884781999], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13174089141, 8828859829, 1099817668031, 1099817669055, 1099817670079, 1099717001687], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099717002711, 1099717003735, 21579467245, 12989538797, 4382897649, 87932401], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38692151805, 4332564989], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 129 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 129 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 129 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 129 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 129 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65619258405, 56878607421, 22015683897, 21831140665, 4752006457, 35118476613], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22233715013, 21998905669, 8812086673, 1100002218387, 1100002219411, 1100002220435], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901558187, 1099901559211, 4466786749, 8862345669, 4567446981, 4466785733], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767335371, 1099767336395, 1099633116651, 87932401, 1099599561203, 34397187581], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17217393149, 8627529213], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 129 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 129 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 129 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 129 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [74041489449, 35554836545, 31008127265, 30689433889, 22015686945, 13123834209], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100203549027, 1099951886751, 1099951887775, 1099951888799, 1099951889823, 8845638053], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4517119397, 1099918331303, 17502607801, 8879123897, 1099683448287, 1099683449311], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4382898661, 1099649892839, 37599741, 37600765, 8610754049, 30068734469], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 129 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 129 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 129 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 129 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69763367981, 27015235653, 30840358185, 22133056809, 21931801897, 8795313521], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100136440179, 8862416281, 4517120409, 1099968663963, 1099918333351, 1099918334375], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918335399, 13106980297, 4550669769, 1099733780947, 1099733781971, 171818461], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099683447263, 1099683448287, 25907987941, 13023093221, 4315787777], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 129 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 129 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 129 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [86708424753, 30924247285, 34900521205, 13509645557, 13291532665, 13157384569], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8795312505, 1100018998671, 1100018999695, 1099884777903, 1099884778927, 1099884779951], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4466786749, 1099817667007, 1099817668031, 21747241413, 8862345669, 4466783709], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [171818461, 1099633115627, 1099633116651], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 129 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [73924254773, 26528685329, 26293877009, 13425825041, 8912681361, 8812086673], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100002218387, 1099985442199, 1099985443223, 1099985444247, 1099985445271, 17401945545], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8812081609, 1099767334347, 1099767335371, 1099767336395, 155041249, 1099666670051], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12905651713, 8610754049, 20822529], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 129 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤129) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 17 where
  orders := orders
  covers := by
    intro a ha box
    change 12+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group17
