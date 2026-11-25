import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass21

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group21
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [19412814855, 36544389135, 87044736027, 61543847991, 43944330543, 35354603823], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39347655983, 21865938315, 21765199319, 13175270871, 8779709931, 4467968491], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099718185451, 22006295, 22007319, 47249564187, 4300193307, 5228059], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i3 : checks (tilesOf batches) 134 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 134 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 134 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 134 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 134 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 134 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 134 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [32265738251, 44933724183, 87028229159, 27385575491, 35320980791, 35103017271], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39146401079, 13275934127, 8846818759, 8762935751, 25976277483, 13091382763], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [43122375155, 1099684628979, 1099684630003, 1099684631027, 4367302151, 1099600741895], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8628712975, 42954529307, 4300191259, 5226011, 5227035], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i6 : checks (tilesOf batches) 134 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 134 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 134 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40655004687, 86927363103, 52886872123, 39750028567, 35304273175, 39280548119], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17520640383, 17621227951, 13208825263, 8897150383, 1099818846675, 1099818847699], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099818848723, 43139081711, 30204065275, 17319237115, 139443707, 1099651072507], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099651073531, 8712596991, 4384078335, 22002199, 8595155483], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i9 : checks (tilesOf batches) 134 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 134 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 134 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40772775955, 74193590307, 52819763259, 39532058943, 30841602367, 21966528879], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17554127215, 4753182063, 8762931659, 1099852400075, 1099852401099, 1099768516063], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099768517087, 13057827303, 4518293991, 156219895, 1099667848695, 1099667849719], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [25909166587, 13024271867, 43004932623, 34398363155, 4333743635], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i12 : checks (tilesOf batches) 134 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 134 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 134 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 134 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44900236311, 82615822375, 27217803331, 35337759003, 30841605403, 30623575323], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100036951455, 1100036952479, 8980966819, 13108230563, 1100020173219, 17470229975], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8880300503, 4451187163, 1099785290203, 1099785291227, 43155930603, 4400852483], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [105887235, 1099617516035, 1099617517059, 30153730567, 17268902407], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 134 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 134 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 134 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48977233947, 86827038763, 5877189703, 31059638539, 30774499595, 26345388299], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8913926551, 8796489111, 13309483447, 8913856951, 8813262263, 43340483003], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [30422169019, 1099885957571, 1099852400075, 1099852401099, 1099852402123, 1099734958567], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [189773295, 1099701402095, 1099701403119, 13024269819, 4384074247, 89108999], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [25808434707, 12923605523, 42954672667], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 134 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 134 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 134 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 134 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 134 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57298867231, 73992539187, 30791273759, 30539689247, 4971285791, 39313954175], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26395639167, 13192048019, 8863595923, 1100087282067, 1099885956547, 1099885957571], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13192042959, 4618889679, 1099802066391, 1099802067415, 1099802068439, 4484739551], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099768510943, 55554575, 1099567183375, 25791725079, 8595085851, 4300187163], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 134 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 134 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 134 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 134 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [57265446947, 61174749239, 22167787827, 21966532915, 9132034355, 35035832699], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22134228347, 8846750123, 4535074219, 1099986617771, 1099936287159, 1099936288183], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099936289207, 13091380699, 4501450203, 1099734957543, 1099734958567, 1099718178283], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099718179307, 8645418511, 4350519823, 55554575, 21479982619], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 134 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 134 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 134 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 134 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65620569127, 39867755583, 30958972231, 22251670855, 21983307079, 13242449251], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100288609635, 1100288610659, 1099919506875, 1099919507899, 1099919508923, 1099919509947], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8897078723, 4551782851, 4484741571, 1099684624883, 17285680643, 8695751171], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [105886211, 1099617515011, 55553551], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 134 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 134 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 134 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 134 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [61342447659, 31361774655, 26630453583, 22117455183, 17671564623, 8897151351], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100204723575, 1100204724599, 1099885953475, 1099885954499, 1099885955523, 4585336263], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4518294983, 1099869175239, 13091378667, 8729306603, 1099634292223, 1099634293247], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4350453263, 4333743631, 5221915, 5222939], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69714281519, 10054715463, 30891935007, 26362160415, 17654792479, 4585406867], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100003396007, 1100003397031, 1100003398055, 8997741999, 8829972911, 4518297007], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099785291227, 21698086375, 13057826279, 1099734957543, 1099734958567, 4417630699], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099718179307, 72331787, 1099583960587, 8628641299, 4333742611], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [69664018481, 30791274775, 26278277399, 4954508567, 8947413395, 8830041491], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100087282067, 1099936288183, 1099936289207, 17537339847, 8897078727, 1099835620815], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099835621839, 1099835622863, 4434407915, 1099718179307, 55554575, 1099567183375], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4333676051, 4333743635], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 134 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [56896625719, 22167854391, 17688343863, 9081702711, 1099969841583, 1099969842607], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099969843631, 4618958259, 1099953061299, 1099953062323, 1099953063347, 13108157919], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4518227423, 105887235, 1099617516035, 8611864087, 4316965399, 22000151], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 134 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 134 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((21 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 21 where
  orders := orders
  covers := by
    intro a ha box
    change 8+a.b≤142 ∧ 6+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6966Allocation.Group21
