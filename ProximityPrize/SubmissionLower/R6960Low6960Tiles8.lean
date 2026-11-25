import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
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
  ⟨unpack [2214661125, 1006702601, 5637411851, 19160833037, 44461928465, 87009811489], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [52918988861, 35503476989, 35336248621, 35135062317, 43473478957, 43590563197], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17452093833, 17535903149, 13207452077, 13106792877, 1099817474511, 1099817475535], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099817476559, 4399417829, 1099716809191, 1099716810215, 25958056425, 17351351785], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4399413757, 4349084157, 1099599301123, 1099599367683, 8660824581, 37339661], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [37340685, 38674960913, 17183645205], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i3 : checks (tilesOf batches) 133 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 133 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 133 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 133 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 133 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 133 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 133 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [14563416075, 35989170193, 82613980189, 74175650869, 39681477905, 35252434193], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43540519185, 30437655885, 43473185177, 39161371037, 17636563361, 17468796321], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13140345249, 8761495977, 1099968470443, 1099968471467, 1099783852503, 1099783919063], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783920087, 4416192993, 1099733518819, 1099733519843, 25957987817, 17368125929], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8761486825, 4449745385, 1099599299075, 1099599300099, 38708663817, 8610489873], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [20560401, 20561425, 4298748437], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i6 : checks (tilesOf batches) 133 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 133 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 133 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 133 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 133 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 133 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 133 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27650630669, 61340270617, 86909418541, 18643210313, 30907202849, 34933808417], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34799665441, 39564034365, 30957463869, 17401758093, 1099968402859, 1099968403883], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099968470443, 1099968471467, 13291265453, 13190671789, 8828599725, 1099850959303], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099850960327, 1099850961351, 43238368721, 1099699961323, 1099699962347, 1099699963371], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21629536749, 4416187897, 4365858297, 37336589, 37337613, 8610488849], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [30068468245, 17183574549, 12888677909], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i9 : checks (tilesOf batches) 133 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 133 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 133 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 133 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 133 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 133 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36123652113, 78302303261, 69780021305, 35436844301, 35185391885, 34967362829], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30420877625, 1100404613435, 13106790801, 1100069065107, 1100069066131, 1100069067155], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100069133715, 17519123873, 13157118369, 43339035065, 1099834180043, 1099834181067], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834182091, 1099834183115, 26025097685, 13157045717, 4449743333, 1099716737511], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099716738535, 8711153141, 37335565, 37336589, 34380144145, 1099532263955], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [21478539797, 4298745365, 4298747413], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i12 : checks (tilesOf batches) 133 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 133 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 133 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 133 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 133 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 133 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44512590869, 86825396261, 39866317889, 31108393221, 35067955461, 39144959237], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13123573093, 13274492285, 13173898621, 13073239421, 39228554637, 30638761357], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100002024867, 1099968471459, 1099951623599, 1099951624623, 1099951625647, 1099951692207], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21830863281, 8979521969, 1099850956231, 1099850957255, 1099850958279, 1099850959303], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4500073949, 4416189917, 1099616073215, 1099616074239, 17267459585, 12939008521], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4315523601, 20558353, 57872, 57876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i15 : checks (tilesOf batches) 133 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 133 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 133 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 133 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 133 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 133 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48757491737, 82530498601, 27048593477, 30940690697, 34950584585, 34782887177], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13207453041, 13056462201, 1100102622587, 1100102689147, 39262177669, 26377351557], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13358373273, 8979523993, 13106787737, 1099985178023, 1099985179047, 1099985180071], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099951626663, 1099867735491, 1099867736515, 4449744337, 1099800624595, 1099800625619], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17401679325, 4416186873, 121221625, 1099632850427, 1099632851451, 1099532262923], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [57864, 4332298765, 57868, 1099532261907, 56848, 57872], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [12888608277, 8593710613, 56852, 57876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i18 : checks (tilesOf batches) 133 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 133 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 133 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 133 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 133 50 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57129456669, 86741716017, 1446633549, 35034402045, 34866770173, 13492671741], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35168474453, 26494794069, 13224161657, 8895709561, 1100169727355, 1100169728379], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100052288915, 1100001958291, 1100018802067, 13358372257, 8979522977, 1099867808171], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099850957255, 1099850958279, 1099850959303, 4483297741, 1099817400783, 1099817401807], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099616072191, 1099616073215, 4382631425, 87666177, 57856, 21545646597], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [12955718149, 57860, 1099549039115, 57864, 56844, 57868], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [56848, 57872, 4298744341, 1099515483671, 55828, 56852], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i21 : checks (tilesOf batches) 133 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 133 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 133 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 133 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 133 53 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65551753249, 69629026361, 26377429269, 30437588245, 4852407573, 35235651889], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26494797105, 13157121393, 8811826545, 1100119398771, 1099934915999, 1099901362591], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8979521961, 8878927273, 4533631401, 1099968400811, 1099968401835, 1099934848427], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099918066103, 1099918067127, 1099918068151, 21663090145, 8794971617, 1099716737511], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099716738535, 4382633457, 1099666404851, 57852, 57856, 34430476805], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099549039111, 56836, 57860, 4332300809, 1099565740555, 56840], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [57864, 56844, 57868, 17200350737, 8610486801, 1099532260883], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55824, 56848, 57872, 4298745365, 3780117, 55828], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [56852, 57876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i24 : checks (tilesOf batches) 133 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 133 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 133 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 133 48 8 = true := by
  decide +kernel
private theorem i56 : checks (tilesOf batches) 133 56 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (checks_join i48 (i56))))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [74007604261, 48305255485, 31041350933, 26561973525, 30555023637, 17502423357], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100287171903, 1100253618495, 13190605197, 8862153101, 1100085839247, 1100085840271], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100085841295, 1100069065103, 1100035511695, 1099985181071, 1099800623571, 1099800624595], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800625619, 17435233749, 8794972629, 4483296729, 1099767068123, 1099532263923], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532262907, 57848, 57852, 25857322497, 17267460609, 1099549039107], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [56832, 57856, 56836, 57860, 8627266057, 54111753], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099565740555, 56840, 57864, 1099532260879, 55820, 56844], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57868, 55824, 56848, 57872, 8593710613, 3779093], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099515482647, 54804, 55828, 56852, 57876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i27 : checks (tilesOf batches) 133 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 133 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 133 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 133 51 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [73974118441, 35504308289, 26796783889, 30705947921, 22032200977, 13123571029], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100169731415, 1100136178007, 1100069064083, 1100052287891, 1100001957267, 1099968403859], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8845374873, 1100035506587, 1100035507611, 1100035508635, 13324817837, 8912414125], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8811819437, 1099767070171, 1099716735463, 1099716736487, 1099716737511, 1099532263919], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099549040119, 57844, 57848, 4399408637, 104443389, 57852], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099532261891, 56832, 57856, 56836, 57860, 25823836681], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099549038091, 55816, 56840, 57864, 55820, 56844], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57868, 55824, 56848, 57872, 1099515482647, 54804], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55828, 56852, 57876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i30 : checks (tilesOf batches) 133 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 133 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 133 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 133 54 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69695996973, 26964707397, 30806541593, 26343941401, 21897986329, 1100136175975], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102622567, 1100052291943, 8828600705, 1100136172931, 1100119396739, 1100069066115], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8962745765, 8845373861, 1099985173927, 1099884511679, 1099884512703, 1099884513727], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21763753421, 8895634893, 1099716735463, 1099716736487, 1099716737511, 1099549041131], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099532262903, 57844, 57848, 1099549039103, 56828, 57852], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4382632449, 56832, 57856, 56836, 57860, 1099549038091], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55816, 56840, 57864, 55820, 56844, 57868], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55824, 56848, 57872, 17183573525, 8593709589, 1099515482647], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [54804, 55828, 56852, 57876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i33 : checks (tilesOf batches) 133 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 133 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 133 49 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [82396418097, 1379524685, 30890496241, 30638911729, 17737306353, 1100152951163], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102620539, 1100052289915, 1100001959291, 13190607229, 8845377917, 1100152950143], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867808155, 17519120825, 8878859705, 1099884511679, 1099884512703, 1099884513727], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4500074953, 1099834177995, 1099834179019, 1099549040115, 57840, 57844], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57848, 104444413, 1099616073215, 1099549039103, 56828, 57852], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4382631425, 87666177, 56832, 57856, 56836, 57860], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099532260875, 55816, 56840, 57864, 12922163725, 8627266061], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [55820, 56844, 57868, 54800, 55824, 56848], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [57872, 1099515482647, 54804, 55828, 56852, 57876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i36 : checks (tilesOf batches) 133 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 133 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 133 52 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69612248117, 1379524685, 30655618317, 26192952589, 9097042189, 8929262965], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100186503543, 1100186504567, 1100169728375, 1100119397751, 1099985181067, 1099934850443], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867808155, 13308042653, 8895638941, 8795044253, 1099834181067, 1099800623571], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800624595, 1099800625619, 4432965097, 1099699959275, 1099549040115, 57840], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [57844, 57848, 1099549039103, 56828, 57852, 56832], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [57856, 8660819461, 4365855237, 56836, 57860, 1099549038091], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [55816, 56840, 57864, 37335565, 55820, 56844], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [57868, 55824, 56848, 57872, 1099515482647, 54804], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [55828, 56852, 57876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i39 : checks (tilesOf batches) 133 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 133 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 133 55 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤133) (hj : a.j≤56) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 8 where
  orders := orders
  covers := by
    intro a ha box
    change 8+a.b≤141 ∧ 3+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group8
