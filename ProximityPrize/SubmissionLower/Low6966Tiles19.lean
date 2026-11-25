import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass19

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group19
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [14697499655, 32365943823, 87043947543, 70183522355, 48272129323, 39732800811], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26428609939, 26260910483, 4970696083, 34867056057, 13057241611, 8762343947], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [47316090403, 38675967535, 25774364211], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i3 : checks (tilesOf batches) 140 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 140 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 140 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 140 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 140 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 140 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 140 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [32097179659, 49127372823, 87111526439, 23257791555, 39548250443, 30891348299], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34917953867, 13241790931, 47618013659, 8812675567, 4484156911, 43222243827], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [25891803667, 13006908947, 1099600154143, 1099600155167, 34431265315, 25841471011], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4349936167, 54970919, 4333157931, 12889467443, 8594569779], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i6 : checks (tilesOf batches) 140 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 140 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 140 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 140 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 140 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 140 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [36610974735, 70065604633, 74260384817, 43809524063, 30958384479, 26495718751], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26294464863, 5004250463, 8913269215, 8795831775, 8728791519, 1099717593603], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099684040203, 1099684041227, 17335424525, 8745495055, 4400266771, 1099650483731], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [47282464299, 38675895853, 4316378671, 21413421, 21414447], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i9 : checks (tilesOf batches) 140 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 140 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 140 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 140 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 140 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 140 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40822452243, 74260043809, 52919836729, 39564958031, 26680197455, 26428611919], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17570314631, 4769369479, 4534417895, 4484153831, 1099835034087, 13174676973], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8829382127, 1099751149051, 1099751150075, 1099633705495, 1099633706519, 47349576219], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [71744033, 71745059, 34397708841, 21512881705, 4333088297, 38123049], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i12 : checks (tilesOf batches) 140 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 140 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 140 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 140 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 140 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 140 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44949912597, 86960531493, 23073242177, 35421055271, 30908124455, 39145811237], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13325675935, 8795831745, 1099986028995, 1099986030019, 1099986031043, 17452797425], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13107569139, 43205606901, 4417043959, 1099767924215, 4433752587, 4383488523], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099633705495, 71744035, 1099583372835, 30119520805, 17234692645, 8628052521], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4333088297, 21411373], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 140 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 140 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 140 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 140 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 140 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [61609887769, 82648925229, 30908056873, 30673249577, 13560562985, 43641751935], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30757057919, 13241787837, 8879715773, 8762278333, 1099935698383, 1099935699407], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099818254827, 1099818255851, 1099818256875, 17402533367, 1099700745735, 1099700746759], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700813319, 4416973333, 122008085, 43004348967, 25824622117, 17234760229], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4316309037], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 140 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 140 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 140 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 140 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 140 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [65804325917, 65586566197, 26428609869, 21999497549, 9131379021, 39497848171], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26562755945, 8829383117, 4500864461, 1099935696335, 1099918920147, 1099918921171], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918922195, 13174675949, 8795826669, 1099717590531, 1099717591555, 1099683968523], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099684035083, 4366641697, 71676449, 25807846955], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 140 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 140 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 140 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 140 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [69981921313, 48540984377, 35303612753, 26562757969, 26294395217, 17519983985], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100321575283, 4534418885, 1099969250759, 1099969251783, 1099969252807, 13208232401], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8812605905, 1099717590531, 1099717591555, 4383420937, 1099684035083, 21613544977], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12990127633, 4333088289, 1099583305251, 8611274285, 4316310061, 21344813], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 140 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 140 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 140 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 140 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [78404152357, 27233925185, 31159643437, 26663488813, 26395126061, 8829453729], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100120248739, 8963598789, 8812606917, 4517708229, 1099868588511, 1099868589535], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099734300159, 1099734301183, 1099734367743, 1099734368767, 1099734369791, 17368911365], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8779047429, 4333088289, 21343789, 21344813], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 140 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 140 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 140 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 140 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78370666537, 14466532421, 31075825961, 26546051369, 30539101481, 13191460253], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099986027971, 1099986028995, 1099986030019, 1099986031043, 13208230373, 8829381093], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4467308009, 1099818253803, 1099818254827, 1099633636887, 1099633703447, 25858177565], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12973348381, 4366641697, 71676449], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 140 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 140 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 140 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [74092545069, 5960485957, 30908056881, 26395059505, 17738088753, 1100019515835], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100019582395, 1100019583419, 9013929417, 8862937545, 4517641673, 1099902143959], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099902144983, 21697431037, 13090790909, 1099717590531, 4383420941, 1099667257871], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [54899237, 1099566528039, 8594497073, 4299532849], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 140 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 140 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 140 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [69797646385, 30790684981, 26294464821, 4953853237, 8946823605, 8795831733], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100036360631, 1099902143959, 1099902144983, 17503130085, 8913266149, 1099818253803], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099818254827, 1099818255851, 4400198157, 1099667257871, 38122025, 38123049], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 140 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 140 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 140 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [57030188085, 22150421845, 21915612501, 4853255509, 8846161345, 4534485441], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099986028995, 1099868589535, 1099868590559, 13124345337, 4534414841, 1099734368767], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099734369791, 4400199169, 1099717590531, 88454685, 1099600149023], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 140 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 140 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [44279572537, 17704528249, 13275348345, 4702260601, 1099885297115, 1099885363675], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099885364699, 1099885365723, 1099868589535, 1099868590559, 8795826681, 4433753593], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [88454685, 88521245, 4316310061, 21344813], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i42 : checks (tilesOf batches) 140 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 140 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤140) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((19 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 19 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤142 ∧ 6+a.j≤58 ∧ 1+a.t≤15 at box
    have pos := ha.1
    have cases : a.t=1 ∨ a.t=2 ∨ a.t=3 ∨ a.t=4 ∨ a.t=5 ∨ a.t=6 ∨ a.t=7 ∨ a.t=8 ∨ a.t=9 ∨ a.t=10 ∨ a.t=11 ∨ a.t=12 ∨ a.t=13 ∨ a.t=14 := by omega
    rcases cases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
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
    · exact Top14.exact a ha h14 (by omega) (by omega)
end Low6966Allocation.Group19
