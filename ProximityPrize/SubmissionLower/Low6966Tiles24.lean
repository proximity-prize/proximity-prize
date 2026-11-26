import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Low6966Mass24
set_option Elab.async false



set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6966Allocation.Group24
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6966Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [27670350855, 36396214291, 86879390751, 52738170939, 35356822795, 30877380875], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39165399307, 17455757659, 4621192539, 17522856327, 13144008071, 8815490439], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099888247199, 1099888248223, 1099888249247, 1099837918635, 1099837919659, 1099753960895], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099753961919, 1099754028479, 4436633031, 1099720404423, 1099720405447, 34534788559], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21650043343, 13060114895, 4419852763, 4386300379, 1099569408491, 24224243], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [24225267], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i3 : checks (tilesOf batches) 125 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 125 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 125 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 125 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 125 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 125 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 125 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36227848203, 61394664471, 86879664171, 5745265735, 30776785175, 30575466775], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26213464343, 39400127815, 30726382919, 8781937027, 1100005623171, 1100005689731], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13177559443, 8832264595, 8731604371, 1099871473059, 1099871474083, 1099804361139], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099787515319, 1099787516343, 1099787582903, 17371858371, 38846536139, 1099686848975], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099686849999, 1099686851023, 4419852763, 4369523163, 25844344295, 17254416871], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [41001455, 41002479, 4319188467], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i6 : checks (tilesOf batches) 125 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 125 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 125 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 125 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 125 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 125 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [36412859407, 82567645211, 61210597431, 39601457411, 30894158083, 34920763651], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17573197115, 8966490427, 13278220683, 13144007051, 8781934987, 1099921803671], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099921804695, 1099921805719, 1099904957851, 1099904958875, 1099905025435, 1099770737083], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099770738107, 1099770739131, 21666820555, 13076892107, 4453409227, 1099703626187], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099703627211, 34434206183, 25844346343, 4352743915, 24224243, 24225267], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 125 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 125 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 125 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 125 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 125 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 125 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40590716947, 86812416035, 39853272127, 35323271423, 35054976255, 30609023231], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13093683551, 1100156686687, 13177561475, 8815489411, 1100005621123, 1099938513299], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099938579859, 1099938580883, 1099938581907, 21784264103, 13144004007, 1099770737083], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099770738107, 1099770739131, 4419855819, 1099703627211, 43040911843, 30139244007], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8664487399, 4335968743, 1099569408491, 17204084211, 8614154739, 24224243], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [24225267], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i12 : checks (tilesOf batches) 125 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 125 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 125 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 125 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 125 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 125 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44718111767, 86795708455, 22757293123, 31028373759, 30760012031, 34820172031], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13194340719, 8849045871, 1100055954807, 1100055955831, 1100056022391, 1100056023415], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17472522663, 8865815975, 1099821070767, 1099821071791, 1099821138351, 4453411259], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099770737083, 1099770738107, 43175132607, 1099602962915, 1099602963939, 25844345319], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17254417895, 4352744939, 57779691, 4335966703, 38662061559, 30072202743], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 125 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 125 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 125 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 125 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 125 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57217271835, 86745448495, 30860673275, 34853658875, 13479560443, 39265978727], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26381152615, 13261447539, 8899375475, 8798715251, 1099972135307, 1099972136331], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099972137355, 1099854626215, 1099854692775, 1099854693799, 13144001979, 8798707131], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099753959871, 1099753960895, 1099753961919, 4386302415, 74557927, 1099586186727], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4335967727, 41002479], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 125 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 125 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 125 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 125 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 125 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [65622725663, 65404900407, 22119748899, 21935271203, 13311788323, 39383422271], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26448264511, 1099972068747, 1099972135307, 1099972136331, 1099972137355, 8815488403], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099938511251, 1099938512275, 1099938513299, 8832260543, 4520519103, 1099703627211], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099703628235, 1099703629259, 21566160355, 8681264611, 34400654831, 21515827695], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [7448055, 7449079], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 125 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 125 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 125 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 125 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61378158627, 56882076727, 22019153203, 21817832755, 4721855795, 35054903631], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22119744847, 8798713223, 1099988844935, 1099988845959, 1099988912519, 1099905027483], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099905028507, 8865815991, 4520520119, 4436636087, 1099770739131, 1099770805691], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099636519387, 1099636585947, 17237640683, 8647711211, 41003503, 41070063], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [34367169015], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 125 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 125 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 125 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 125 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69800389671, 35558305855, 30927711531, 26397936939, 26179905835, 8849048927], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100156686687, 8916150671, 8781936015, 1099955290511, 1099888248223, 1099888249247], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099888250271, 1099753960895, 1099753961919, 1099754028479, 17405414851, 8781930947], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [108113375, 108179935, 4319191539, 24226291], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 125 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 125 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 125 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 125 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78256175147, 14251312199, 30927714575, 26414717199, 26230240527, 8865822079], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100022399359, 1099955357071, 1099955358095, 1099955359119, 1099955360143, 13194336683], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8815487403, 1099737183683, 1099737250243, 1099737251267, 25877903839, 12993009119], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4386302435, 91402723, 4302415351], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 125 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 125 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 125 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [82484102191, 30894228739, 26414785795, 17740972291, 1099972067723, 1099972068747], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099972135307, 1099972136331, 1099972137355, 8932926879, 8798712223, 1099888180639], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21666825675, 13043342795, 158446035, 158512595, 1099670141395, 8614157811], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4319193587], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 125 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 125 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 125 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [69683089459, 26498601243, 26263792923, 9134262555, 8916151699, 8781937043], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099938579859, 1099888249247, 1099888250271, 1099888251295, 4403149251, 1099737252291], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17371861451, 8765154763, 1099619809759, 1099619810783, 4352815587, 24293875], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [24294899, 4302415351, 4302482935], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 125 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 125 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 125 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [56898853943, 26297343287, 21834610999, 1100324393271, 8815491471, 1099955357071], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099955358095, 1099955359119, 13160783287, 8781934007, 4403149255, 1099720475079], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099603032547, 1099603033571, 4369526247, 74626535], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 125 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 125 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤125) (hj : a.j≤52) :
    Covered orders a ∨ Low6966Gate.Gated ((24 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 24 where
  orders := orders
  covers := by
    intro a ha box
    change 17+a.b≤142 ∧ 6+a.j≤58 ∧ 2+a.t≤15 at box
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
end Low6966Allocation.Group24
