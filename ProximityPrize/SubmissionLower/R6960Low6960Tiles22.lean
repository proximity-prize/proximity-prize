import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass22

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group22
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2315324421, 10889007113, 27969592333, 65803335701, 87161403433, 14734511173], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35185719641, 30773452121, 30622530905, 43808930145, 39463839073, 13123894753], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4450143745, 4383036929, 21646712325, 13023229445, 1099599697435, 1099599698459], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [43020525085, 4366255645, 25824169505, 38692218405, 8610821673, 4315857449], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [20958761, 20959785], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 139 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 139 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 139 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [23640676361, 44798062609, 87060536353, 44497219645, 39648386361, 35202565433], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43473807673, 4651472305, 17603406265, 17452416441, 8879329721, 43356074445], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4500405757, 4433298941, 4399812093, 25941607941, 17351746053, 1099666806283], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099666807307, 43070855697, 1099599695387, 1099599696411, 8644376097, 54511137], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [54512161, 38675439145], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 139 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 139 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 139 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 139 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [32332129293, 65786758169, 87027254317, 1832835145, 30941152573, 34950980925], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17838295357, 43741889889, 30924304737, 13291660749, 13157447117, 8795375053], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099851354591, 1099851355615, 1099700291075, 1099700357635, 1099700358659, 1099700361731], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21579534865, 4416517649, 4366188049, 43003889185, 37666341, 37667365], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [42953483821, 17183904301], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 139 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 139 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 139 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36610781201, 82715169821, 57147171897, 39715427625, 35219275049, 35018088745], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21814494581, 13291594185, 13174223305, 8812151241, 1099935174091, 1099935240651], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099935241675, 1099935242699, 25991937529, 17368455673, 1099700290051, 1099700291075], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700357635, 4416516625, 4366187025, 37665317, 37666341, 38675437097], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17200749097, 42953486893, 4299075117], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 139 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 139 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 139 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 139 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44865436693, 86943229989, 31545211969, 35403753761, 30924377377, 34934205729], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8795378085, 13291662765, 13140671917, 8795377069, 1099868133851, 43272256993], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099834576355, 1099834577379, 1099834578403, 4450074093, 1099784177135, 1099784243695], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21713751537, 13090334193, 4382963217, 1099616402967, 1099616403991, 30135839261], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21545978397, 8627594789, 4332630565, 20888105, 12889006637], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 139 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 139 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 139 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57364662297, 86909812781, 5976806473, 35185721633, 30739899681, 22099707169], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39346325897, 30739755401, 8778597817, 1100002349499, 13258106309, 8879257029], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8761819589, 1099851355615, 1099851356639, 17469116905, 1099801021931, 1099767398899], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767399923, 1099767466483, 4382963213, 1099649957391, 8644372001, 4349407777], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [37665317, 30068797997], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 139 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 139 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 139 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 139 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 139 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [65753404445, 74075313205, 30739830069, 30555419957, 4953396533, 39497323869], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26646183261, 13174224301, 8812152237, 1100052681135, 1099884910039, 1099884911063], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13241260505, 8929585625, 1099817731559, 1099817732583, 1099817799143, 4466849269], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750620663, 1099750621687, 54441505, 1099566070307, 38675437097, 4299074093], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4108845], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 139 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 139 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 139 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 139 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 139 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65753538593, 61291143225, 22133186897, 21931931985, 9080590673, 35219202401], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26528744801, 8828926401, 1099968726467, 1099968727491, 1099968728515, 1099935240651], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099935241675, 1099935242699, 13107110385, 4533957105, 1099717065215, 1099717066239], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099717067263, 21562754585, 12972891673, 4315852329, 4109869], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 139 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 139 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 139 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 139 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [74158992421, 39984149565, 35303157049, 26562302265, 30538575161, 13140675965], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13241331117, 8862481837, 1100052613551, 1099985505727, 1099985572287, 1099985573311], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985574335, 1099767397875, 1099767398899, 1099767399923, 17402008057, 8812144121], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4450071045, 1099683510791, 30135840285, 17251012125, 4108845, 4109869], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 139 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 139 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 139 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 139 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [74125506601, 27183136833, 31024970037, 26528815413, 26294007093, 1100153278871], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100153345431, 1100153346455, 8929588661, 8795374005, 1100019060151, 1099800953323], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099800954347, 1099800955371, 13157374445, 8845699565, 4382963209, 1099666734603], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [25840941597, 12956046877, 54441505, 1099566070307, 4299074093, 4108845], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 139 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 139 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 139 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 139 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [82564514861, 5892920393, 35236119829, 34934204693, 13560106261, 13358770593], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8963144097, 8828929441, 1100002349499, 1099935241675, 1099935242699, 1099851285983], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099851287007, 1099851353567, 26025493993, 13157442025, 1099717065215, 1099717066239], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099717067263, 4382962197, 21495645737, 12905782825, 4299075117, 4109869], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 139 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 139 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 139 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [78286393393, 30890823965, 26394603805, 13526551837, 8979919285, 8828927413], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100019059127, 1100002282939, 1100002349499, 1100002350523, 1100002351547, 17485894117], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13123888613, 1099767397875, 1099767398899, 1099767399923, 104773141, 104774165], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8644372001, 4349407777], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 139 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 139 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 139 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65519000629, 26461707581, 26226899261, 4869510461, 8929589677, 4584293805], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100052614575, 1100052681135, 1099935241675, 1099935242699, 13190929893, 8845700581], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099750622711, 1099750689271, 188660225, 1099700289027, 1099700290051, 4332629541], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [37664293], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 139 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 139 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤139) (hj : a.j≤54) :
    Covered orders a ∨ Low6960Gate.Gated ((22 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 22 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤141 ∧ 5+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group22
