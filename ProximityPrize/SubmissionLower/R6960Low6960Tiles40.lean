import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass40

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group40
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27938851847, 44885485587, 87047164959, 44399765563, 39567775027, 35088334131], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34903859507, 13127107991, 13210919351, 8899244471, 13043219895, 1099753835987], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099753837011, 4402953695, 1099703502303, 1099703503327, 43124468195, 25944817123], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17321335267, 74431995, 1099586060795, 4335841795, 40876547, 12908993031], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8614029831], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 130 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 130 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 130 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 130 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36513060875, 61545528343, 86963419179, 5946461255, 30894029099, 34903857451], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22035807531, 43611012459, 34970888555, 13278026159, 13160655279, 8815360431], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099888051635, 1099888052659, 1099753835987, 1099753837011, 1099669944807, 1099669945831], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099669946855, 17287777779, 8664361459, 107984371, 30122273279, 17237445119], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4319062535, 24097287, 42956766731], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 130 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 130 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 130 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40774935567, 61528951839, 78356777011, 30743103791, 30525008175, 9184463151], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39316114799, 26431288687, 8983128479, 8865691039, 8765030815, 1099837722047], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099837723071, 1099787387339, 1099787388363, 1099787389387, 13127029203, 8832131539], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099686720995, 1099686722019, 1099686723043, 4335840767, 42956695051, 7319051], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [7320075], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 130 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 130 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 130 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [44919173139, 69900852259, 52721262651, 35222478143, 26498400575, 22052511039], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17573066071, 8966359383, 1099888052659, 1099888053683, 1099888054707, 4520392119], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099871272375, 1099871273399, 1099871274423, 8865619403, 4570720715, 4486836683], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [43090981355, 21599519215, 8714623471, 1099636390383, 74428923, 1099586057723], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i12 : checks (tilesOf batches) 130 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 130 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 130 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 130 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44902530071, 69850589223, 39886695487, 30961133879, 26481690935, 22002181431], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13194214759, 1100206820711, 1100206821735, 1099888049587, 1099888050611, 1099888051635], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099888052659, 8882464183, 4553945527, 4470061495, 17354885603, 8764956131], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099686722019, 43090984427, 91206135, 1099602834935, 4352616959], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 130 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 130 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 130 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [49013082139, 69783549995, 22824270915, 26699725099, 26397807915, 21968695595], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100072601991, 1100072603015, 1100072604039, 8832135587, 1099955158435, 1099955159459], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099955160483, 38963792323, 26078966211, 13194139075, 8832132547, 191869407], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099703498207, 1099703499231, 4352615935, 57650687, 17187114507], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i18 : checks (tilesOf batches) 130 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 130 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 130 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 130 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 130 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53140411423, 69699733555, 5778689095, 30776658207, 22052514079, 17640177951], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100039045519, 1100039046543, 1100039047567, 39114790303, 26213252511, 8882465195], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4553946539, 1099921604011, 1099921608107, 1099921609131, 13127031243, 1099653166571], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099653167595, 4402948595, 107983347, 12908993031, 21482077707, 12892149259], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 130 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 130 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 130 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 130 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [53073371171, 61143356471, 1500500043, 22220281131, 21951851819, 13328434475], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34870223251, 21985396115, 1100005492119, 1100005493143, 1100005494167, 8899243423], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4553947551, 1099971936671, 1099888054707, 8781733343, 4486834655, 1099703499231], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099703500255, 141537771, 1099653166571], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 130 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 130 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 130 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 130 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [61378096167, 44097775675, 17640106319, 13261323599, 1100307483983, 1100307485007], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35088330067, 17958867283, 17673659731, 1099921604011, 1099921605035, 1099921606059], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099921607083, 1099837716927, 8848909771, 4486836683, 74428923, 1099586057723], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [30105562627, 17220668931, 4302284299, 7319051], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 130 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [65538914347, 27035351107, 30910806327, 22153173303, 17707282743, 8815363443], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100156490099, 1099921606059, 1099921607083, 1099921608107, 4587499959, 4470061495], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099871273399, 13093476827, 8731470299, 1099686722019, 1099686723043, 4352616959], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [57651711, 1099569280511, 25810598403, 12925703683], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [61260792879, 18529304643, 26599130431, 22035734847, 17589844287, 1100072603015], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100072604039, 4570724771, 1099955159459, 1099955160483, 1099955161507, 13143876039], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4537168327, 1099669944807, 1099669945831, 40874499, 40875523, 21498856967], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [12908994055, 4319063559], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [56949051443, 10040100935, 22270611775, 17757546815, 17556290879, 4570725787], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099988714907, 1099955161507, 1099955162531, 1099955163555, 8848910795, 4486837707], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099703500255, 1099703501279, 74429947, 1099586058747, 17237447167, 8647583231], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [7320075], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 130 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 40 where
  orders := orders
  covers := by
    intro a ha box
    change 11+a.b≤141 ∧ 7+a.j≤59 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group40
