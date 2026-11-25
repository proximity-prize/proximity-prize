import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass37

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group37
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23691660295, 40823104527, 87095397407, 53088460859, 43927817535, 35304536383], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43542224191, 8981236143, 21815729615, 17453725135, 122866191, 1099634494991], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099634561551, 8696018451, 4401054227, 47333582359, 34431831579, 30103665187], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21513804323, 8628908579, 42954872363], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i3 : checks (tilesOf batches) 138 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 138 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 138 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 138 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 138 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 138 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 138 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36426946571, 57483475991, 87045338155, 10390521927, 35254203711, 35002620223], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22117793087, 43525160355, 34918590883, 17520761307, 13158755803, 8796683739], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099735157239, 1099735158263, 1099735224823, 43155986939, 4367498767, 1099634492943], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21564067351, 8645684767, 4333943327, 1099550605859, 34365008427, 5421611], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [5422635], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 138 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 138 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 138 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 138 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 138 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 138 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40755995663, 61594029087, 78438762547, 30791469379, 30573439299, 9249671491], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39381257599, 30741132671, 13225863615, 8863791551, 8763131327, 1099819045347], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099785487851, 1099785488875, 1099785489899, 17386542579, 173193731, 1099684822531], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099684823555, 43105723911, 8679238163, 4350719507, 30103664163, 38975011], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12907025959, 8612128295, 4300386859], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 138 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 138 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 138 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 138 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 138 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 138 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40873766931, 65754912803, 61309229111, 22151272787, 26194653523, 4854041939], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35203733859, 26563607907, 8897343931, 8779906491, 1099986815419, 1099852598747], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099852599771, 1099785485803, 1099785486827, 1099785487851, 13091576311, 8746346999], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099668043271, 1099668044295, 4350716447, 55751199, 21513731619, 12923803171], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [42971574823, 4300383787], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 138 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 138 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 138 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 138 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 138 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 138 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44984450071, 69882177575, 39968681023, 31059831103, 26530056511, 26278470975], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13175538043, 1100255252859, 13192308155, 8813458875, 1099953258947, 1099953259971], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099953260995, 1099953262019, 1099751929331, 1099751930355, 1099751931379, 17403316727], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8813387255, 43139350015, 4451379719, 156414471], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i15 : checks (tilesOf batches) 138 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 138 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 138 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 138 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 138 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [53205420059, 74026286127, 14383498311, 26781711651, 30674098467, 26228209955], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8897345939, 39196707243, 30539805099, 1100037146031, 1100037147055, 1100037148079], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100037149103, 13292902839, 8930896311, 4585600439, 1099835817439, 1099835818463], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099701597695, 1099701598719, 4401048075, 1099651265035, 12974133783, 4367491611], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [25825407519, 12940578335, 22194727, 22195751], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 138 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 138 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 138 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 138 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 138 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [48960853023, 78203814957, 1565708363, 26781713671, 30690877703, 17789272327], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100121031067, 1100121032091, 1100121033115, 1100121034139, 9098600863, 8964451743], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8813459871, 39112889787, 21949873595, 1099953263043, 1099869370839, 1099869371863], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13058020859, 4401049083, 1099718374907, 89304599, 1099600933399, 4367492635], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8612058663, 4317159975, 34364937771, 25775143467], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 138 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 138 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 138 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 138 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [53071405091, 61141455927, 1532153931, 22268712235, 21983505707, 13360088363], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35002474899, 22067381651, 1100104254879, 1100104255903, 1100104256927, 8914120103], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4568824231, 1100070699431, 1099986817467, 8830164459, 4518488555, 1099785484779], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099785485803, 1099735151095, 1099735152119, 17218766371, 8628902435, 38971939], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38972963, 4317160999], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 138 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 138 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 138 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 138 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [57181891623, 48340509755, 17772422467, 17571166531, 1100490132803, 1100490133827], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30858505579, 17956965739, 17654980971, 1100087474595, 1100087475619, 1100087476643], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100087477667, 1100087478691, 1099886147027, 8863785439, 4501712351, 106081811], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099617710611, 4333937187, 38971939, 12907023911, 8612126247, 30070042155], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 138 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 138 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 138 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 138 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [61309155371, 31294862399, 26714601799, 22151271751, 13460680007, 8964455783], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100339136871, 1100339137895, 1100339138919, 1099953257923, 1099953258947, 1099953259971], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4552043987, 1099886147027, 1099886148051, 13141906923, 4568819179, 106081811], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099617710611, 25775143467, 8595281451, 4300382763], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 138 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 138 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 138 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [65436353581, 14266057799, 26681050403, 22151274787, 21899688227, 8863791499], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100154586515, 1100154587539, 1100154588563, 1100154589587, 8930828743, 4602375623], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099936478663, 1099902925263, 1099902926287, 1099902927311, 21647951359, 8779898367], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [106081811, 1099617710611, 4333939227, 22194727, 17185211947, 8595348011], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 138 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 138 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 138 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [65386090545, 1498599499, 26580455707, 22033837339, 13376865563, 1100154586515], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100154587539, 1100154588563, 8947674531, 1100087474595, 1100087475619, 1100087476643], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100020371891, 13209014751, 8897339871, 4401049083, 1099718374907, 89304599], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099600933399, 4300382763, 5417515], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 138 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 138 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 138 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤138) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((37 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 37 where
  orders := orders
  covers := by
    intro a ha box
    change 3+a.b≤141 ∧ 7+a.j≤59 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group37
