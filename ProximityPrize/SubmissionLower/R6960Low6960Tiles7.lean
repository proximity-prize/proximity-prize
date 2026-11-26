import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.R6960Low6960FractionContact
import ProximityPrize.SubmissionLower.R6960Low6960Mass7
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group7
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2013334533, 14596837387, 36257931277, 87077307417, 70166550581, 56576918837], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [52248542517, 39011529105, 356833681, 43222307237, 60200992213, 51560807905], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i3 : checks (tilesOf batches) 121 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 121 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 121 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 121 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 121 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 121 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 121 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤121) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [27633784841, 49043026965, 87128040485, 36025055297, 52181427533, 39296604493], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [55973066181, 47366347209, 25858195921], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i6 : checks (tilesOf batches) 121 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 121 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 121 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 121 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 121 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 121 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 121 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤121) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40486052877, 78537837597, 70032332853, 56476323141, 43625121093, 30538969457], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [9080983921, 51678094789, 51560733153, 30069273061], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i9 : checks (tilesOf batches) 121 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 121 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 121 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 121 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 121 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 121 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤121) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [44831813649, 87027309601, 44447215677, 52265246001, 39380488497, 26025965989], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4567913893, 55905956309, 47265835489, 34381011425, 21479341541], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i12 : checks (tilesOf batches) 121 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 121 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 121 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 121 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 121 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 121 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤121) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [49076780053, 87010667557, 27368013889, 47987125553, 35051969841, 17335370177], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4450473409, 55939513805, 30119599577, 17234705881, 42954094053], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i15 : checks (tilesOf batches) 121 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 121 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 121 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 121 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 121 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤121) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57432033305, 86960472109, 6027465801, 39430750509, 34984929581, 13627608365], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [51862653337, 43256020377, 25908521413, 13023626693, 42954096101], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i18 : checks (tilesOf batches) 121 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 121 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 121 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 121 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 121 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤121) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [65837618205, 74125972533, 35001636161, 26327890241, 4987344193, 52030428529], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39112051057, 17301813705, 8711884233, 21512892893, 38675909089], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i21 : checks (tilesOf batches) 121 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 121 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 121 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 121 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 121 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤121) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65804132385, 61341802553, 30606074205, 21932327261, 574937437, 47752241517], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34867482989, 12990071245, 8661553613, 17201149409, 4316254689], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i24 : checks (tilesOf batches) 121 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 121 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 121 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 121 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤121) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [74226428965, 40051586109, 47869685065, 30706736457, 17536695693, 8913211789], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4333031901, 38132189, 47265836513, 30069267941, 12889406949, 8594443749], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i27 : checks (tilesOf batches) 121 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 121 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 121 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 121 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤121) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78420801577, 22989161541, 43658606901, 30723515701, 13090735537, 4500805041], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [25841411541, 12956516821, 42970872289, 4299477477, 4577765], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i30 : checks (tilesOf batches) 121 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 121 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 121 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 121 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤121) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69914821677, 18761369669, 39296599373, 26327887181, 8745437633, 4433696193], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21546446293, 12939740629, 8594441701, 4299544037], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i33 : checks (tilesOf batches) 121 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 121 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 121 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤121) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [78337052721, 35135852841, 26411775273, 9315864873, 17318589893, 8728660421], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4333032921, 34364166629, 4299544037], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i36 : checks (tilesOf batches) 121 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 121 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 121 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤121) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65569659957, 30723513673, 21999369545, 4937012553, 13006847433, 8695107017], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4299476453, 4299544037], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i39 : checks (tilesOf batches) 121 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 121 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤121) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((7 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 7 where
  orders := orders
  covers := by
    intro a ha box
    change 15+a.b≤136 ∧ 3+a.j≤57 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group7
