import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass13
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group13
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2197883909, 1006702601, 10117125131, 27633786893, 82597002261, 87077391409], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35520385277, 44026772741, 39664904453, 34984268109, 34833347917, 4986755405], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13207582145, 13090145729, 8761628097, 47516693965, 25941414373, 17334775269], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099666544111, 4416325109, 121359861, 1099632988663, 1099633056247, 1099633057271], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [34464164345, 25874304505, 38692021769, 12905590285, 47248324113, 17183779345], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4298882577], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i3 : checks (tilesOf batches) 132 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 132 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 132 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 132 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 132 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 132 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 132 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [14983043083, 32013101073, 86892234777, 69964700725, 39765428489, 39564308745], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43624536329, 26142819681, 21847775661, 13257912749, 13140476333, 8728072637], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867872703, 1099716874723, 1099716875747, 1099716942307, 43137837541, 30253085157], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21663224293, 4416324077, 1099666541039, 1099666542063, 43020392961, 12922366473], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4332435977, 20693517, 20694541], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 132 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 132 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 132 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 132 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 132 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 132 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 132 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27784979469, 61390733337, 86926261293, 14449037385, 30957665573, 34967493925], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30571938085, 43741692233, 35135188297, 13140476321, 17502477753, 13157249465], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099851092419, 1099851093443, 1099851094467, 1099851095491, 4416324065, 1099716872675], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099716873699, 43087504881, 17267593725, 8660955645, 87801341, 71025153], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099582653955, 30118866437, 21529005573, 38692016649, 12922365449, 4298880529], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 132 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 132 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 132 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 132 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 132 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 132 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40334864401, 82597468193, 57029470265, 39631345937, 35168747793, 39195354385], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17552887129, 17552811413, 13207583125, 13090146709, 43406209445, 1099901426103], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901427127, 1099817535947, 1099817536971, 1099817537995, 1099817539019, 26025296341], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13140401621, 4433099237, 1099700093415, 1099700094439, 8711286257, 34447384061], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [37468681, 37469705, 4298878481, 3913233], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 132 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 132 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 132 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 132 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 132 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 132 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44596608021, 82580826149, 39933556801, 35336448273, 35051310353, 39128314129], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100169861495, 1100169862519, 13274624389, 13174030725, 8828735877, 43423055265], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21814218169, 8962876857, 1099851092419, 1099851093443, 4433101261, 1099800758735], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800759759, 4483428837, 4399544805, 1099649761779, 1099649762803, 30152419837], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21562558973, 71023105, 1099582651907, 8610619917], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 132 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 132 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 132 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 132 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 132 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 132 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53002258457, 82547407917, 18593008709, 35168746769, 34917163281, 26260194577], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43540498809, 26411038073, 13090145673, 13324951961, 13157183897, 8828731801], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100018865563, 1100018866587, 1100018867611, 1099867868607, 1099867869631, 17435365845], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767202263, 1099767203287, 1099767204311, 4500206045, 4416322013, 1099599428095], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099599429119, 8644175365, 42986981897, 3912209, 3913233], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 132 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 132 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 132 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 132 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 132 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61391000605, 82513989681, 35034599693, 30588712205, 9248167181, 39430018381], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26545257805, 13157184909, 8828732813, 1100069196175, 1099934979503, 1099934980527], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934981551, 13291395505, 8929323441, 1099817534923, 1099817535947, 1099817536971], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4500207057, 1099783978451, 1099783979475, 4349209093, 54243845, 54244869], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099565873671, 38692017673, 25807191561], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 132 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 132 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 132 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 132 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 132 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65602215969, 65418076217, 26344005929, 21931670825, 9097172265, 35252560189], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26511705405, 8845507993, 1100018862491, 1100018863515, 1100018864539, 1099968533927], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968534951, 1099951758759, 13190734261, 8845504949, 1099750424027, 1099750425051], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750426075, 21612889585, 12989406705, 4382765557, 1099632982519, 4365987329], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12905586189, 20690445, 1099515616787], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 132 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 132 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 132 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 132 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69813431333, 48372494397, 31024704813, 26528550189, 26293741869, 17519330637], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100337633615, 1100304080207, 1099985307043, 1099985308067, 1099985309091, 1099985310115], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985311139, 8929323437, 8828728749, 4500210093, 1099716870627, 17368255973], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8778326501, 4382766569, 1099683315179, 4365987329, 71022081, 1099582650883], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532393999], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 132 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 132 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 132 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 132 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69779945513, 35554704449, 30924110121, 26411112745, 21982000425, 13140479329], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100220194147, 1099985309091, 1099985310115, 1099985311139, 1099985312163, 8862283173], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4516987301, 1099968530855, 13207509445, 8828660165, 1099733647839, 1099733648863], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4382766569, 1099683315179, 25874299385, 12989404665, 4365986305, 4332433921], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099582650883, 20689421, 20690445, 1099532393999], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 132 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 132 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 132 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 132 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [78218953773, 14230933577, 30924113161, 30655751433, 26209862921, 8895841653], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100069196175, 1100069197199, 1100069198223, 1100018867599, 13257844121, 8912614809], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8778400153, 1099851091395, 1099817533899, 1099817534923, 1099817535947, 21713552857], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13106847193, 4382766569, 1099683315179, 4416318965, 71022081, 1099582650883], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549171211, 12888808977], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 132 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 132 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 132 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73940832305, 5708109897, 30806741265, 30555156753, 13425692945, 13190738313], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8845509001, 1100085972363, 1100035641751, 1100035642775, 1100002089375, 1099951758751], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17502474693, 8895768005, 1099817533899, 1099817534923, 1099817535947, 4516983253], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4416322005, 1099632982519, 1099632983543, 1099549171211, 20689421, 20690445], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8593843729], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i36 : checks (tilesOf batches) 132 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 132 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 132 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69645933621, 26478222613, 22032333077, 13408915733, 1100035641751, 1100035642775], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100035643799, 1099985313175, 8862284189, 1100002084255, 1100002085279, 1100002086303], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13224287681, 8862281153, 1099716868579, 1099716869603, 1099716870627, 4349210117], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [54244869, 1099549171211], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 132 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 132 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 132 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [56844920889, 26293741869, 21831009581, 1100421520687, 8828732805, 1100102750599], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102751623, 1100102752647, 8962877869, 8845505965, 4500210093, 1099851090371], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099851091395, 1099716870627, 1099716871651, 4382766573, 1099666537967, 54244869], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099565873671, 4332431881, 4315656713, 1099549171211, 3912209], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i42 : checks (tilesOf batches) 132 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 132 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6966Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 13 where
  orders := orders
  covers := by
    intro a ha box
    change 10+a.b≤142 ∧ 3+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6966Allocation.Group13
