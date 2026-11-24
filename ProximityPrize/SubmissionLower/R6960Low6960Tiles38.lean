import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass38

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group38
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23709420549, 23675872271, 15052389399, 45085903903, 27855714347, 19215455287], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [10608748603, 2002039871, 1985263683, 1951710275, 1918156867, 1867826247], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1851050055, 1817496647, 1767166027, 1099684958707, 1099651403259, 1099617847811], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099601069575, 1099567514127, 1099533958679], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
    Covered orders a ∨ Low6960Gate.Gated ((38 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [27987613707, 19347354647, 45102680091, 27855713323, 14937264179, 10608746555], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2002037823, 2002038847, 1968485439, 1918154819, 1884601411, 1834270787], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1783940167, 1767163975, 1733610567, 1683279947, 1099768844767, 1099735289319], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099701733871, 1099684955635, 1099651400187, 1099601067527, 1099567512079, 1099533956631], by decide +kernel⟩
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
    Covered orders a ∨ Low6960Gate.Gated ((38 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [23675872271, 15052389399, 40790936607, 27855713323, 14937264179, 6313779259], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2018814011, 2002037823, 1951707199, 1918153791, 1851045955, 1817492547], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1767161923, 1716831303, 1683277895, 1649724487, 1616171083, 1099835953615], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099819175379, 1099785619931, 1099752064483, 1099718509035, 1099668176375, 1099634620927], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099584288267, 1099550732819], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6960Gate.Gated ((38 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [19364130833, 40807711771, 27872488487, 14937262131, 10625521719, 2018812987], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2018814011, 1951706175, 1918152767, 1867822143, 1800714307, 1767160899], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1716830275, 1666499655, 1632946247, 1599392839, 1549062219, 1099903062463], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099869507015, 1099835951567, 1099802396119, 1099768840671, 1099718508011, 1099684952563], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099634619903, 1099584287243, 1099550731795], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6960Gate.Gated ((38 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [15052389399, 40790936607, 23560746027, 14937263155, 6330555447, 2018812987], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [2002036795, 1934928959, 1884598335, 1834267711, 1767159875, 1716829251], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1683275843, 1616168007, 1582614599, 1549061191, 1498730571, 1099953394099], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099919838651, 1099886283203, 1099852727755, 1099802395095, 1099768839647, 1099718506987], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099668174327, 1099617841667, 1099567509007, 5548568], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6960Gate.Gated ((38 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [40807712795, 27855712299, 14937263155, 6330555447, 2018812987, 1985259579], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1901374527, 1851043903, 1800713279, 1733605443, 1683274819, 1649721411], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1582613575, 1549060167, 1515506759, 1465176139, 1099986948523, 1099953393075], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099919837627, 1099886282179, 1099835949519, 1099802394071, 1099752061411, 1099701728751], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099651396091, 1099601063431, 1099533953559], by decide +kernel⟩
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
    Covered orders a ∨ Low6960Gate.Gated ((38 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [36495971359, 23560747051, 10642296883, 6330555447, 2018812987, 1968482363], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1901374527, 1834266687, 1783936063, 1716828227, 1666497603, 1632944195], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1565836359, 1515505735, 1481952327, 1431621707, 1100020502947, 1099986947499], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099953392051, 1099903059391, 1099852726731, 1099819171283, 1099768838623, 1099718505963], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099668173303, 1099601063431, 1099550730771], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6960Gate.Gated ((38 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [36479197219, 19249005615, 6330554423, 2018811963, 2018812987, 1968482363], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1901374527, 1834266687, 1783936063, 1716828227, 1666497603, 1616166979], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1549059143, 1498728519, 1465175111, 1414844491, 1100037280159, 1100003724711], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099970169263, 1099919836603, 1099869503943, 1099819171283, 1099768838623, 1099718505963], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099668173303, 1099601063431, 1099550730771], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6960Gate.Gated ((38 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [27872488487, 14937262131, 6330554423, 2018811963, 2018812987, 1985259579], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1901374527, 1834266687, 1783936063, 1700051011, 1649720387, 1599389763], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1532281927, 1498728519, 1448397895, 1398067275, 1100054057371, 1100020501923], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099970169263, 1099936613815, 1099886281155, 1099835948495, 1099785615835, 1099718505963], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099668173303, 1099601063431, 1099533953559], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
    Covered orders a ∨ Low6960Gate.Gated ((38 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [23560747051, 10642296883, 6330555447, 2018812987, 1985259579, 1901374527], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1851043903, 1783936063, 1716828227, 1649720387, 1599389763, 1532281927], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1481951303, 1448397895, 1381290059, 1100070834583, 1100020501923, 1099986946475], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099936613815, 1099886281155, 1099835948495, 1099768838623, 1099718505963, 1099651396091], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099601063431, 1099533953559], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 134 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 134 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 134 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((38 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [19249005615, 10625521719, 2018812987, 2002036795, 1918151743, 1851043903], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1783936063, 1716828227, 1666497603, 1599389763, 1532281927, 1481951303], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1448397895, 1381290059, 1100070834583, 1100020501923, 1099986946475, 1099936613815], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099886281155, 1099819171283, 1099768838623, 1099718505963, 1099651396091, 1099584286219], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [5548568], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 134 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 134 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 134 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((38 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [14937264179, 6313779259, 2018814011, 1934928959, 1867821119, 1800713279], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1716828227, 1666497603, 1616166979, 1549059143, 1481951303, 1448397895], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1381290059, 1100070834583, 1100020501923, 1099986946475, 1099919836603, 1099869503943], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099819171283, 1099768838623, 1099701728751, 1099634618879, 1099567509007], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 134 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 134 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 134 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤134) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((38 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 38 where
  orders := orders
  covers := by
    intro a ha box
    change 7+a.b≤141 ∧ 7+a.j≤59 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group38
