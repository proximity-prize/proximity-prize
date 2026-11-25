import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass10

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group10
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2046888965, 10620571657, 31895526413, 61626072085, 108485507113, 47970285877], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [47819434293, 5071165749, 56274926973, 47718692221, 34548722113, 8778927553], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [47416614341, 37987813, 38675762665], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i3 : checks (tilesOf batches) 123 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 123 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 123 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 123 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 123 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 123 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 123 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤123) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [27516278793, 48959075349, 125447136293, 1749212237, 48238650621, 52282103037], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [18157324541, 47517211053, 51795544497, 34615760305, 21730933169, 8611221993], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21479194093], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i6 : checks (tilesOf batches) 123 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 123 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 123 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 123 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 123 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 123 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 123 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤123) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [36325237773, 65803798553, 91305773105, 39346866493, 39145615677, 5037611325], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [52097403237, 39229422949, 25975566773, 8829259189, 51577365989, 25807791589], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8611152361, 34364086765], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i9 : checks (tilesOf batches) 123 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 123 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 123 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 123 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 123 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 123 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤123) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40637444113, 70015080481, 69948447797, 47869614425, 34984790361, 26294267229], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21915486557, 13006784969, 4450474441, 21546380765, 8661485021, 4316254697], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [38658978285], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i12 : checks (tilesOf batches) 123 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 123 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 123 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 123 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 123 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 123 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤123) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48992828437, 78470999077, 40051521601, 43658538301, 30773778749, 17536629137], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13174558097, 1099901951379, 51761921465, 4383296985, 4383364569, 42970804713], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [25791012329, 12906117609, 21219817], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i15 : checks (tilesOf batches) 123 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 123 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 123 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 123 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 123 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 123 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤123) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [49009805337, 91171420201, 14449561673, 39531346197, 39262986517, 9466792213], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21764415913, 13174553001, 51728435649, 4450473409, 1099700690371, 34380873193], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4316187113, 4316254697, 21289449], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i18 : checks (tilesOf batches) 123 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 123 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 123 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 123 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 123 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤123) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53187531805, 86876588081, 1631771725, 35186116893, 34934533405, 9349353757], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [47534134697, 34649310633, 17469517225, 13107446185, 4383363541, 1099616803287], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099616804311, 8644706785, 4349808097, 37988837, 4511212], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i21 : checks (tilesOf batches) 123 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 123 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 123 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 123 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 123 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤123) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [69981659169, 61274629177, 26344596813, 21915484493, 4836284749, 47852839249], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26428412241, 8812478905, 4483960249, 1099734177211, 1099633580499, 1099633581523], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17268190681, 47282545125, 4316253673], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i24 : checks (tilesOf batches) 123 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 123 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 123 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 123 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤123) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65720314917, 52735093821, 43524320605, 26378148189, 21915415901, 17519856989], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8728595889, 4433697201, 13040334281, 4450403785, 4349742549, 1099616802263], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099616803287, 1099616804311, 4316253669, 42970803689, 21286380], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i27 : checks (tilesOf batches) 123 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 123 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 123 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 123 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤123) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69897910313, 35672669249, 39363639621, 26411704645, 17519852925, 13124227453], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4433629625, 1099734243771, 1099734244795, 8711814609, 4416850385, 71619037], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099583247839, 21529600481, 54770145], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i30 : checks (tilesOf batches) 123 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 123 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 123 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 123 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤123) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [74092282925, 18643864645, 35152561457, 26411706673, 9332573489, 8728596901], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099818130855, 1099667067339, 1099667133899, 1099667134923, 17318521293, 8728591821], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4316187109, 4299475437], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i33 : checks (tilesOf batches) 123 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 123 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 123 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤123) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [65569525809, 14365675593, 30756933957, 22049632581, 5004052805, 4467184045], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099784509871, 1099784576431, 17284968913, 121882065, 88396249, 1099600025051], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [30069199341, 12889338349, 4440556], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 123 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 123 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 123 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤123) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65519262773, 1581440077, 26495589693, 26227161405, 4903392573, 13157775789], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4567845293, 272880045, 1099667135947, 1099633579475, 1099633580499, 25774235117], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i39 : checks (tilesOf batches) 123 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 123 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 123 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤123) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((10 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 10 where
  orders := orders
  covers := by
    intro a ha box
    change 15+a.b≤138 ∧ 3+a.j≤58 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group10
