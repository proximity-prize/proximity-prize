import ProximityPrize.SubmissionLower.R6960Low6960AllocTiles
import ProximityPrize.SubmissionLower.R6960Low6960Mass8

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group8
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23459073031, 36211532815, 86795438107, 44131392567, 35272804595, 35038063859], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39131779315, 13093615955, 13261377895, 13143941479, 8815423847, 1099888180615], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099888181639, 1099888182663, 21767351703, 13160711575, 1099787514271, 1099787515295], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099787516319, 4419789223, 1099753892263, 1099753893287, 4419786179, 124820931], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099619672519, 1099619673543, 38745744843, 30139174351, 8614086107, 4319121883], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [17187171807, 12892275167], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i3 : checks (tilesOf batches) 119 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 119 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 119 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 119 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 119 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 119 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (i43)))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [32033478667, 44466321431, 86762087463, 14184134723, 26666231031, 39131775223], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30491584759, 8848976223, 8781870431, 13345194347, 13211046251, 13093609835], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099938513275, 1099938514299, 34752772483, 26162912643, 1099854624143, 1099854625167], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099854626191, 1099787444639, 1099787445663, 1099787446687, 1099787447711, 1099787514271], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4453339579, 4386232763, 12959381967, 57711059, 1099569339859, 8614087131], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 119 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 119 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 119 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 119 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 119 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 119 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [36245087247, 73944090651, 56848519219, 35222472955, 26565569787, 30575397115], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21767432487, 4688298279, 8765090159, 1099988776303, 1099988842863, 1099988843887], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13227821431, 8865749367, 4537230711, 1099888181639, 1099888182663, 1099804224923], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099804291483, 1099703559603, 1099703560627, 17338166715, 13026492859, 158374331], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099670003131, 1099670004155, 30155885003, 21566024139, 4386230731, 38712190419], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [8597307871, 4302343647], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i9 : checks (tilesOf batches) 119 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 119 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 119 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 119 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 119 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 119 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36278906899, 73927447583, 43997174839, 30977905915, 26481685755, 26280431867], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13194276147, 8848981299, 1099972066675, 1099972067699, 1099972068723, 8932856183], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8815418743, 1099955218807, 1099921665407, 1099921666431, 1099921732991, 1099921734015], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17422054823, 8832190887, 1099720334767, 1099720335791, 1099720336815, 91264459], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [91265483, 30105621975, 38661927391], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 119 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 119 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 119 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 119 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 119 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44499942423, 78121822247, 18378437695, 26683009259, 26431423723, 30491582699], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8916083027, 8815422803, 1100055951711, 1100055952735, 1100055953759, 1100055954783], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [34719219083, 26129424779, 13194265995, 8815416715, 1099871333771, 1099871334795], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099871401355, 1099770667427, 1099770668451, 1099770669475, 4386231747, 1099636448707], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12992937415, 4335898071, 24155611, 24156635], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 119 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 119 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 119 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 119 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 119 47 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [44466522139, 69582287915, 14083471427, 26498462971, 22052573435, 26129508603], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8848976211, 1100106216787, 1100039174499, 1100039175523, 1100039176547, 1100039177571], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [34736064903, 21851237767, 8882524551, 4537228679, 1099888108935, 1099837778323], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099837779347, 1099837780371, 13076825515, 1099636448707, 1099636449731, 4335900111], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8614086107, 4319121883, 24156635], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 119 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 119 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 119 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 119 42 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (i42)))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [56999236639, 60975647795, 26280430847, 21868095743, 4772118783, 30776579383], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22119675191, 8798644575, 1100055885151, 1100055951711, 1100055952735, 1099972067699], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099972068723, 13194268027, 8798641531, 1099837778323, 1099837779347, 1099837780371], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [208706991, 1099720335791, 1099720336815, 8681196999, 108042695, 17237571027], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8647641555, 4302345695], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 119 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 119 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 119 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 119 45 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61176832035, 43930065975, 30810202399, 22086123807, 17657010463, 17455688995], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100307611939, 1100307612963, 1100022328679, 1100022329703, 1100022330727, 1100022397287], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100022398311, 4587559315, 4470120851, 1099837778323, 13076824499, 8748306867], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099653226943, 1099653227967, 25827434963, 17237573075, 4319121883, 24156635], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [24157659], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 119 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 119 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 119 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 119 48 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [65371204647, 26850864191, 26615901451, 22102903051, 17673789707, 8815424835], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100173394243, 1100173395267, 1099938510203, 1099938511227, 1099938512251, 4554006915], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099904887171, 1099904888195, 1099904889219, 13127158179, 4537227683, 1099636449731], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099636450755, 21515693527, 12925830615, 4302345695, 7380447], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 119 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 119 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 119 43 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (i43))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [61076240427, 18361660479, 22321002767, 22019019023, 21817764111, 1100072730971], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100072731995, 8815421795, 1100039107939, 1100039174499, 1100039175523, 8916078995], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4570783123, 4453344659, 1099804224923, 1099804291483, 1099670005179, 1099670006203], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [40934871, 40935895, 17204017627, 8614088155], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 119 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 119 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 119 46 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [61025977391, 5577424963, 26397869319, 21918425351, 13278165255, 1100022397287], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100022398311, 8865751411, 4520455539, 1099971999091, 1099955290487, 1099955291511], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17422124447, 8781863327, 1099737116075, 1099737182635, 1099686782391, 1099686783415], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4369455567, 74490319, 12909053403, 4319122907], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 119 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 119 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 119 49 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [56731078707, 22069350667, 21851318539, 4738564363, 8832199015, 1100022330727], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100022397287, 1100022398311, 1099955290487, 1099955291511, 13110383003, 4520452507], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099770669475, 1099770670499, 1099770737059, 8647643603, 4352679379, 1099569341907], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 119 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 119 44 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤119) (hj : a.j≤49) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 8 where
  orders := orders
  covers := by
    intro a ha box
    change 13+a.b≤132 ∧ 6+a.j≤55 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group8
