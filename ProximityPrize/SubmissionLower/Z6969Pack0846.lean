import ProximityPrize.SubmissionLower.Z6969Pack0840
import ProximityPrize.SubmissionLower.Z6969Pack0845

set_option Elab.async false

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles13
section Z6969Source2345
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group13
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2281769989, 1006702601, 14613681163, 28020057101, 86908944409, 74309997621], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35604205823, 44026839309, 35453889805, 52180914445, 21931738477, 21998768553], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17619986857, 17485774249, 4466725341, 1099817605599, 8744910325, 4416391669], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099633054219, 1099633055243, 43037245969, 34430676501, 12955920917, 4366055957], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [71092757, 1099582721559, 4315726365, 3981861, 3982885], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 137 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 137 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 137 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 137 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 137 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 137 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 137 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [19160766473, 36274777105, 86959542301, 57180529721, 39681610013, 35269409053], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39312858397, 21797520765, 17586429373, 13190803901, 8845509053, 8728137165], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884714447, 43255279069, 38926686693, 1099733716467, 1099733717491, 1099733718515], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [25958185465, 17368323577, 4382835197, 1099683383807, 4416320009, 4416387593], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38725573141, 71090709, 1099582719511, 8610621985], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 137 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 137 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 137 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 137 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 137 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 137 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 137 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [28003279885, 57230049305, 86976657449, 14516210757, 30957664557, 30773254445], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34850191661, 39446790505, 30856997225, 13174028709, 13106989477, 1099884714447], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17452210649, 8862281177, 1099817601503, 1099817602527, 1099817603551, 1099817604575], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4449876461, 4416389613, 21596113413, 1099616272911, 1099616273935, 71088661], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [71089685, 8627397149, 4332432925, 4315723293, 42953352741, 21478738469], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [3978789], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i9 : checks (tilesOf batches) 137 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 137 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 137 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 137 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 137 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 137 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36342018065, 78403228701, 61341278265, 35437040933, 30974441765, 34984335653], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26109263197, 1100354476383, 8845508017, 8778467761, 1100002153907, 13308172733], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8979720637, 8862283197, 1099800824291, 1099800825315, 1099800826339, 43188171245], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733713395, 1099733714419, 25924631041, 13039801857, 154908161, 1099666536963], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099666603523, 4332431901, 37466653, 8593843749], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 137 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 137 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 137 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 137 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 137 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 137 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44680625173, 82631288869, 35722541121, 31125367069, 35068152093, 34866900253], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8845578633, 13257911705, 8912616857, 8811956633, 43406278069, 17569581513], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13224353225, 1099901490635, 1099901491659, 1099867933139, 1099867934163, 1099867935187], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767201259, 1099767267819, 1099767268843, 4466650613, 1099716867575, 1099716868599], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [30102153757, 8627396125, 4332431901, 20689441, 42953358885], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 137 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 137 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 137 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 137 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 137 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57230182425, 86842507309, 5875946569, 30940889361, 30739702033, 26327367953], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39446792553, 26562031977, 8845509017, 8778468761, 13257908661, 8879059381], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8761621941, 1099918268871, 1099901488587, 1099901489611, 1099901490635, 1099834378715], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099800755683, 1099800822243, 1099800823267, 17435364837, 4382765565, 1099683314175], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [8677728785, 87797265, 71021077, 1099582649879, 17183772197], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 137 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 137 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 137 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 137 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 137 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61458240541, 78286196785, 26562105629, 26360851741, 17737435421, 39413306717], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26528546141, 1100052482471, 1100052483495, 1100052484519, 1100052485543, 1100052486567], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8946167213, 8811952557, 1100018861487, 13174020573, 4600867293, 1099783977447], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099783978471, 1099784045031, 138129925, 1099649758727, 38725572117, 21545778709], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12955915797, 4298876453], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 137 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 137 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 137 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 137 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 137 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [69880537121, 56945648697, 35286114617, 26578879801, 26327294265, 21864627525], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4802270533, 8795176357, 1100052482471, 1100052483495, 1100052484519, 13190799809], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8811950529, 1099935045059, 1099935046083, 1099834310107, 1099834376667, 1099834377691], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [188461561, 1099700090363, 1099700091387, 17351476733, 13039802877, 4399540749], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [34413830681, 8593840677, 4298876453], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 137 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 137 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 137 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 137 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69847051301, 44161478717, 31041547573, 26494995765, 22049106229, 13257916769], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8929464673, 1099985375671, 1099985376695, 1099985377719, 1099951751615, 1099951818175], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951819199, 1099951820223, 8895834561, 8761619905, 17452142053, 8845500901], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750421999, 1099750423023, 1099750489583, 104574477, 104575501, 30085377569], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4298875429, 4298877477], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 137 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 137 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 137 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 137 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78286059561, 22820865093, 31024773397, 26545395989, 30555223317, 1100169926027], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100169927051, 8979723661, 8845509005, 1100153146767, 1100153147791, 1099884642767], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884709327, 1099884710351, 13241129425, 8828725713, 1099750421999, 1099750423023], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750489583, 25941408253, 13056579069, 4399540749, 104575501], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 137 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 137 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 137 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 137 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [78252573741, 10053472329, 30940955921, 30655816977, 21982070033, 8795178381], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13274686881, 8895837601, 1100069192099, 1100035707307, 1100035708331, 1100018932139], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099935040963, 1099935041987, 1099935043011, 21747107301, 13106912741, 1099750421999], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750423023, 1099750489583, 4399541761, 8627396125, 4332431901, 37466653], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [55844], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 137 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 137 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 137 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [73957675057, 1530648649, 30806741269, 26327298325, 13442469141, 8962945437], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8811953565, 1100086036895, 1100086037919, 1100086038943, 1100086039967, 1099951823291], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17536029129, 8929387977, 1099851087319, 1099851153879, 1099851154903, 188461561], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700090363, 1099700091387, 4332430877, 37465629, 17200550433, 55844], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 137 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 137 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 137 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65434917941, 26427956521, 26209925417, 4852536617, 8895838613, 1100119524759], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100119525783, 1100119592343, 1100119593367, 1100002153907, 1099985377715, 13241130441], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8828726729, 1099800754659, 1099800755683, 1099800822243, 4399541765, 1099649758727], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8610618913, 4315654689, 20689441, 55844], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 137 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 137 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [52633905209, 22015551809, 17603215681, 4785493313, 1100035637675, 1100035638699], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100035705259, 1100035706283, 1100035707307, 1099968599483, 1099951823291, 8912611781], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4567315909, 1099918196167, 1099632981515, 1099633048075, 4365986325, 71021077], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [55844], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i42 : checks (tilesOf batches) 137 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 137 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤137) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((13 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 13 where
  orders := orders
  covers := by
    intro a ha box
    change 5+a.b≤142 ∧ 4+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6969Allocation.Group13
end Z6969Source2345

-- Source: ProximityPrize.SubmissionLower.Low6969Mass14
section Z6969Source2346
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group14

private def m0 : MassCell 14 :=
  ⟨⟨2,5,7⟩,mass_cell 14 2 5 7 212 (by decide)
    (by decide +kernel) [4584482563956, 3747397713480, 2988535389928, 2349164728200, 1816370057256, 1377943494856, 1022384947560, 738902110728, 517410468520, 348533293896, 223601648616, 134654383240, 74438137128, 36407338440, 14724204136, 4258739976, 588740520, 6688784] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 14 :=
  ⟨⟨2,6,15⟩,mass_cell 14 2 6 15 197 (by decide)
    (by decide +kernel) [4655781451868, 4009883623750, 3143626861011, 2419743134643, 1825484661483, 1345031138427, 963514604643, 667019441571, 442582372923, 278192464683, 162791125107, 86272104723, 39481496331, 14217735003, 3231598083, 226205187, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 14 :=
  ⟨⟨3,8,26⟩,mass_cell 14 3 8 26 175 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3503717090033, 2583102701361, 1851292148393, 1281978397145, 850611589185, 534399041633, 312305247161, 165051873993, 75117765905, 26738942225, 5908597833, 377103161, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 14 :=
  ⟨⟨2,9,29⟩,mass_cell 14 2 9 29 165 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3624527690184, 2654767205284, 1865072458084, 1258346914852, 806399402980, 482902003876, 263390052964, 125262139684, 47780107492, 12069053860, 1117330276, 646318] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 14 :=
  ⟨⟨4,10,33⟩,mass_cell 14 4 10 33 158 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3746791023752, 2780870554484, 1898258781960, 1236570321812, 758188337432, 428426825364, 215530615304, 90675370100, 27967585752, 4444591412, 88886852, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 14 :=
  ⟨⟨1,12,37⟩,mass_cell 14 1 12 37 146 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 2967268193522, 1961202197438, 1219879496834, 698779381310, 355690612466, 150711423902, 46249521218, 7022082014, 107221018, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 14 :=
  ⟨⟨1,15,42⟩,mass_cell 14 1 15 42 132 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3219452089444, 2054050417848, 1174073052072, 594038670744, 248281006728, 73794304632, 10233320808, 99661182] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 14 :=
  ⟨⟨5,16,44⟩,mass_cell 14 5 16 44 129 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3301765752446, 2107254265081, 1157639434041, 555784442817, 214981642897, 55682206377, 5496125961, 5956549] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 14 :=
  ⟨⟨4,18,46⟩,mass_cell 14 4 18 46 123 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3369835890439, 2183881817529, 1140244484553, 503557516881, 167038176465, 30624988617, 993818673, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 14 :=
  ⟨⟨1,21,48⟩,mass_cell 14 1 21 48 115 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3414158776320, 2274708405800, 1103473541864, 426278432936, 106901493608, 9121138472, 1157620] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 14 :=
  ⟨⟨1,24,50⟩,mass_cell 14 1 24 50 110 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2404829945799, 1078404836607, 360450800127, 65049461703, 1865024706, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 14 :=
  ⟨⟨1,26,51⟩,mass_cell 14 1 26 51 106 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2470968607868, 1056359247251, 318227620651, 44170703155, 398402803] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 14 :=
  ⟨⟨3,27,52⟩,mass_cell 14 3 27 52 106 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2553977959914, 1077931961540, 311954053940, 39398917220, 217008300] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 14 :=
  ⟨⟨1,30,53⟩,mass_cell 14 1 30 53 102 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2617915314208, 1047744100754, 258094178198, 20211492410, 158671] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 14 :=
  ⟨⟨3,32,54⟩,mass_cell 14 3 32 54 100 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2690811913831, 1051778112743, 234039165207, 13542183670, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 14 :=
  ⟨⟨6,35,55⟩,mass_cell 14 6 35 55 97 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2755101627545, 1031766257779, 192893160095, 6294334264, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 14 :=
  ⟨⟨5,39,56⟩,mass_cell 14 5 39 56 94 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2821075571166, 1017032575156, 150993794644, 1839689234] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 14 :=
  ⟨⟨5,44,57⟩,mass_cell 14 5 44 57 91 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2883333228976, 995443710906, 108511721734, 188665626] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 14 :=
  ⟨⟨16,49,58⟩,mass_cell 14 16 49 58 88 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2941068578799, 972363446338, 76013786418, 1390042] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 14 :=
  ⟨⟨60,4,46⟩,mass_cell 14 60 4 46 280 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3378749849046, 2293254962085, 1234022187373, 456012036037, 34122337347, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 14 :=
  ⟨⟨60,15,51⟩,mass_cell 14 60 15 51 141 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2471795137027, 1085280395589, 362245959873, 60083622545, 131699746, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 14 :=
  ⟨⟨48,26,54⟩,mass_cell 14 48 26 54 109 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2669447344749, 1025427352585, 259513750297, 32467567649, 547133309, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 14 :=
  ⟨⟨65,36,57⟩,mass_cell 14 65 36 57 98 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2872192717748, 976113138544, 138004513972, 3584045503, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 14 :=
  ⟨⟨56,44,58⟩,mass_cell 14 56 44 58 92 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2935699322185, 959297736599, 91828369399, 280595236] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 14 :=
  ⟨⟨59,52,59⟩,mass_cell 14 59 52 59 88 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2992863379814, 940659272958, 54776218330, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 14 :=
  ⟨⟨59,18,52⟩,mass_cell 14 59 18 52 129 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2532168335044, 1057768302772, 328773967408, 55891607644, 648326992, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 14 :=
  ⟨⟨57,28,55⟩,mass_cell 14 57 28 55 107 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2737576132217, 1006646686522, 218919081430, 19658756714, 98085453] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 14 :=
  ⟨⟨52,33,56⟩,mass_cell 14 52 33 56 100 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2807196693094, 994353448812, 176680543308, 8466104364, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 14 :=
  ⟨⟨67,26,55⟩,mass_cell 14 67 26 55 110 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2737976203691, 1007520801421, 218509108941, 18876968149, 24102919, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 14 :=
  ⟨⟨58,32,56⟩,mass_cell 14 58 32 56 102 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2806451242425, 993139470252, 178713234320, 9520120628, 104406] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 14 :=
  ⟨⟨71,21,54⟩,mass_cell 14 71 21 54 121 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2674153407788, 1033752411406, 254243280862, 21645539164, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 14 :=
  ⟨⟨64,31,56⟩,mass_cell 14 64 31 56 103 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2805630274418, 990587263447, 178839437595, 10084395519, 2159286] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 14 :=
  ⟨⟨73,50,59⟩,mass_cell 14 73 50 59 89 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2992105394974, 937589407517, 58311315165, 3705916] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 14 :=
  ⟨⟨71,35,57⟩,mass_cell 14 71 35 57 99 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2871632326463, 974045218002, 138516581218, 3940324884, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 14 :=
  ⟨⟨69,42,58⟩,mass_cell 14 69 42 58 93 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2934664889826, 956766587178, 96264510654, 597589818] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 14 :=
  ⟨⟨75,16,53⟩,mass_cell 14 75 16 53 138 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2618678727176, 1069998316687, 277925492408, 13722005609, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 14 :=
  ⟨⟨82,27,56⟩,mass_cell 14 82 27 56 110 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2808136947457, 998046555261, 176525528289, 6525157089, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 14 :=
  ⟨⟨79,49,59⟩,mass_cell 14 79 49 59 89 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2991938528922, 937757397198, 60080288494, 12243512] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 14 :=
  ⟨⟨75,24,55⟩,mass_cell 14 75 24 55 115 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2741012488837, 1014755410545, 216314564289, 13805878965, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 14 :=
  ⟨⟨81,33,57⟩,mass_cell 14 81 33 57 101 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2871839528750, 975264705078, 139074953622, 3937557640, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 14 :=
  ⟨⟨80,18,54⟩,mass_cell 14 80 18 54 131 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2685327974670, 1055403411805, 242832313323, 7712791507, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 14 :=
  ⟨⟨85,48,59⟩,mass_cell 14 85 48 59 90 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2991764372023, 937316959025, 61426394033, 27441067] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 14 :=
  ⟨⟨97,46,59⟩,mass_cell 14 97 46 59 91 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2991394037626, 934499075132, 62440190392, 65561304] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 14 :=
  ⟨⟨81,40,58⟩,mass_cell 14 81 40 58 95 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2933983239018, 954143457243, 98366602987, 909194371] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 14 :=
  ⟨⟨91,38,58⟩,mass_cell 14 91 38 58 97 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2934111561572, 955454799419, 99177645635, 961234659, 0] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 14 :=
  ⟨⟨101,15,55⟩,mass_cell 14 101 15 55 145 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2767326120421, 1062930328866, 148928727287, 52360, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 14 :=
  ⟨⟨102,45,59⟩,mass_cell 14 102 45 59 92 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2991426391410, 935133973904, 62836672592, 75167472] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 14 :=
  ⟨⟨104,35,58⟩,mass_cell 14 104 35 58 100 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2935087860280, 959780476817, 95344272101, 154718173, 0] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 14 :=
  ⟨⟨107,44,59⟩,mass_cell 14 107 44 59 93 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2991452925840, 935204393732, 62544929352, 56646594] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 14 :=
  ⟨⟨112,43,59⟩,mass_cell 14 112 43 59 93 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2991473614733, 934685506507, 61447062830, 13624181] (by decide +kernel) (by decide +kernel)⟩
private def m50 : MassCell 14 :=
  ⟨⟨105,13,55⟩,mass_cell 14 105 13 55 157 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2775617158610, 1077613864972, 132104805527, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m51 : MassCell 14 :=
  ⟨⟨107,12,55⟩,mass_cell 14 107 12 55 164 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2779724193651, 1083800382700, 123128158463, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m52 : MassCell 14 :=
  ⟨⟨112,33,58⟩,mass_cell 14 112 33 58 102 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2935976589322, 962019902058, 87937051689, 27405, 0] (by decide +kernel) (by decide +kernel)⟩
private def m53 : MassCell 14 :=
  ⟨⟨111,10,55⟩,mass_cell 14 111 10 55 180 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2787858282071, 1093667835757, 104606433339, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m54 : MassCell 14 :=
  ⟨⟨107,26,57⟩,mass_cell 14 107 26 57 112 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2878333823659, 995163482199, 115572838798, 595665, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m55 : MassCell 14 :=
  ⟨⟨120,54,60⟩,mass_cell 14 120 54 60 87 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 3040388501873, 916727088050, 32935753934, 0] (by decide +kernel) (by decide +kernel)⟩
private def m56 : MassCell 14 :=
  ⟨⟨113,9,55⟩,mass_cell 14 113 9 55 191 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2791884126957, 1097268634934, 95281121132, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m57 : MassCell 14 :=
  ⟨⟨121,30,58⟩,mass_cell 14 121 30 58 107 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2938608866457, 974063444999, 77971762692, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m58 : MassCell 14 :=
  ⟨⟨119,6,55⟩,mass_cell 14 119 6 55 237 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2803789480276, 1102264289594, 68293210835, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m59 : MassCell 14 :=
  ⟨⟨120,41,59⟩,mass_cell 14 120 41 59 95 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2991961035209, 938571702742, 59267990740, 0] (by decide +kernel) (by decide +kernel)⟩
private def m60 : MassCell 14 :=
  ⟨⟨123,20,57⟩,mass_cell 14 123 20 57 127 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2887957940766, 1018492292054, 78846528129, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m61 : MassCell 14 :=
  ⟨⟨127,28,58⟩,mass_cell 14 127 28 58 110 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2940325249109, 979463449056, 68730438697, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m62 : MassCell 14 :=
  ⟨⟨128,39,59⟩,mass_cell 14 128 39 59 97 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2992431257387, 940487775697, 54444913700, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m63 : MassCell 14 :=
  ⟨⟨130,27,58⟩,mass_cell 14 130 27 58 112 (by decide)
    (by decide +kernel) [4655781451868, 4214026063976, 3804133110404, 3424546815728, 2941171684657, 981303706167, 63592969221, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 14) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51, m52, m53, m54, m55, m56, m57, m58, m59, m60, m61, m62, m63]

end Low6969Allocation.Group14
end Z6969Source2346

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles14
section Z6969Source2347
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group14
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2197883909, 1006702601, 10117125131, 27633786893, 82597002261, 87077391409], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [35520385277, 44026772741, 43859208453, 34950714701, 39061207373, 17468996017], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13106924977, 1099918204339, 43238503885, 21696779741, 17368329693, 38843017697], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [25958191585, 4399549929, 1099683321323, 1099683387883, 4399546873, 4365994489], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099565879815, 38692020745, 12905590285, 4315659789, 20695565, 20696589], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [25773640209], by decide +kernel⟩
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
    Covered orders a ∨ Low6969Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [14983043083, 31996323857, 86892234777, 69964700725, 39765428489, 39564308745], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [47852394761, 21881407841, 21914884509, 13291401629, 13207585181, 4466659781], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099834317255, 1099834318279, 43154614753, 30253085157, 21663224293, 4416324077], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099666541039, 1099666542063, 1099649765875, 1099649766899, 43020392961, 8660955649], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4365991425, 12922366473, 20694541], by decide +kernel⟩
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
    Covered orders a ∨ Low6969Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27784979469, 61390733337, 86926261293, 14449037385, 35151969573, 39178576165], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [22065957157, 43724915017, 35135188297, 17552810405, 13207582117, 13090145701], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099851093443, 1099851094467, 1099851095491, 4416325081, 1099750428123, 1099750429147], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17368256997, 43087504881, 4416321013, 4365991413, 1099616208379, 1099616209403], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [12955919873, 38708793861, 30118935045, 37469705, 37470729], by decide +kernel⟩
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
    Covered orders a ∨ Low6969Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36224446481, 74108130333, 69847260213, 39581013285, 30924111141, 26344004933], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26193082693, 9113949509, 8879061421, 8778401197, 1099934978479, 1099834316231], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099834317255, 1099834318279, 43221725649, 13157178833, 8845503953, 1099733648863], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733649887, 1099733650911, 25891077621, 13006182901, 4365990389, 1099632984567], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [34413829637, 37468681, 37469705, 4298878481, 3913233], by decide +kernel⟩
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
    Covered orders a ∨ Low6969Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [44596608021, 82580826149, 39933556801, 35336448273, 35051310353, 39128314129], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100169861495, 1100169862519, 17485705605, 13140477317, 8795182469, 43423055265], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21814218169, 8962876857, 1099884647867, 1099834312135, 1099834313159, 1099834314183], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834315207, 8778396113, 4449877457, 1099616206331, 1099616207355, 30152419837], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [21562558973, 4365988353, 71023105, 8610619917], by decide +kernel⟩
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
    Covered orders a ∨ Low6969Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57179785241, 82564251693, 14314819657, 30907334933, 34900386069, 26243417365], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39413238109, 30789890397, 13090145673, 13324951961, 13157183897, 8828731801], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985311139, 1099985312163, 1099985313187, 1099867868607, 1099867869631, 1099767202263], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767203287, 1099767204311, 4500206045, 4416322013, 17385034209, 1099599428095], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099599429119, 8644175365, 30085378573, 3912209, 3913233], by decide +kernel⟩
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
    Covered orders a ∨ Low6969Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [65602081821, 78235800629, 30756410645, 30555157781, 9214612757, 39497127225], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26612366649, 13157184909, 8828732813, 1100069196175, 1099934979503, 1099934980527], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099934981551, 13241063869, 8862214589, 1099817534923, 1099817535947, 1099817536971], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4483429841, 1099783978451, 1099783979475, 4365986305, 4332433921, 1099582650883], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38708794885, 25823968773, 20689421, 20690445], by decide +kernel⟩
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
    Covered orders a ∨ Low6969Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61374357537, 69696265269, 26411113761, 26226637089, 9130726689, 35185451341], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26478216525, 8912615825, 8795178385, 1100052418963, 1099968533927, 1099968534951], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099951758759, 13157179837, 8811950525, 1099834312135, 1099834313159, 1099834314183], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099716869603, 1099716870627, 4382765557, 1099632982519, 21579335161, 8694439417], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4365986305, 20689421, 20690445, 1099515616787], by decide +kernel⟩
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
    Covered orders a ∨ Low6969Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69813431333, 48355717181, 31007927597, 26528550189, 26276964653, 17536107849], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100354410827, 1100320857419, 1099985307043, 1099985308067, 1099985309091, 1099985310115], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099985311139, 8946100649, 8845505961, 1099951751595, 17368255973, 8778326501], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [171685353, 1099683314155, 1099683315179, 4365987329, 1099532393999, 30068600337], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
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
    Covered orders a ∨ Low6969Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [78252439593, 27048723525, 31007930637, 30739634445, 30521604365, 1100153084283], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100119530875, 13157185917, 8828733821, 1100136306047, 13291395505, 8912546225], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8811951537, 1099884644795, 1099884645819, 1099884646843, 1099851088323, 1099851089347], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4382766569, 1099683315179, 25907853809, 13022959089, 4365986305, 4332433921], by decide +kernel⟩
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
    Covered orders a ∨ Low6969Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [78218953773, 14230933577, 30924113161, 26427893001, 26243416329, 8895840637], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100136303999, 1100069196175, 1100069197199, 1100069198223, 1100018867599, 9013208489], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8845439401, 8761621929, 1099817535947, 1099767201239, 1099767202263, 1099767203287], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [21713552857, 13090069977, 4433097193, 1099683314155, 1099549171211, 12905586189], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [20689421, 20690445, 4298878481], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 132 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 132 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 132 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [78185467953, 1429920845, 30857072901, 30605488389, 13476024581, 13190738313], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8845509001, 1100085972363, 1100035641751, 1100035642775, 1100035643799, 1099918204327], by decide +kernel⟩
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
    Covered orders a ∨ Low6969Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69645933621, 26478222613, 26243414293, 9147503893, 8946170249, 8811955593], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100085973387, 1100002088351, 1100002089375, 1099951758751, 13207510465, 8845503937], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099851089347, 1099851090371, 1099851091395, 1099716868579, 1099716869603, 1099716870627], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4365987329, 71022081, 1099549171211, 12888808977], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 132 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 132 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 132 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤132) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((14 : Band).val) a :=
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
    Covered orders a ∨ Low6969Gate.Gated ((14 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 14 where
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
end Low6969Allocation.Group14
end Z6969Source2347

-- Source: ProximityPrize.SubmissionLower.Low6969Mass15
section Z6969Source2348
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group15

private def m0 : MassCell 15 :=
  ⟨⟨1,3,11⟩,mass_cell 15 1 3 11 285 (by decide)
    (by decide +kernel) [4547042380019, 3759962573163, 3006802602687, 2370094403763, 1837411741767, 1397018144379, 1037866901583, 749601065667, 522553451223, 347746635147, 216892956639, 122394517203, 57372897433, 16956578455, 1204270912, 143066, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 15 :=
  ⟨⟨2,6,36⟩,mass_cell 15 2 6 36 218 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3375878381084, 2637145945104, 1906279003572, 1338443991672, 907471232412, 589473646944, 362846754564, 208268672712, 108700116972, 49384401072, 17847436884, 3912497240, 130323290, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 15 :=
  ⟨⟨3,7,42⟩,mass_cell 15 3 7 42 206 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2785846871377, 1991917526301, 1360329609945, 892004974069, 556113737073, 325047009357, 174416893321, 83056483365, 33019865889, 9582119293, 1272244054, 2345436, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 15 :=
  ⟨⟨3,9,48⟩,mass_cell 15 3 9 48 184 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2867797452734, 2117268017002, 1383400226458, 859341011914, 500643503866, 268163940394, 128061667162, 51799137418, 16141911994, 3158659306, 221155354, 341182, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 15 :=
  ⟨⟨2,12,54⟩,mass_cell 15 2 12 54 163 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2296582854777, 1448691200834, 836415677030, 441491592866, 205546071542, 79234172258, 22238890214, 3271156610, 72673560, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 15 :=
  ⟨⟨5,15,59⟩,mass_cell 15 5 15 59 149 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2397247081787, 1547586871113, 813151493589, 376141332801, 143564448909, 39601296057, 5604722373, 108077450, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 15 :=
  ⟨⟨4,17,61⟩,mass_cell 15 4 17 61 142 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 1616931223886, 814078197166, 351972069646, 119273193326, 25654400206, 1801002286, 61863] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 15 :=
  ⟨⟨5,18,62⟩,mass_cell 15 5 18 62 139 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 1654772840844, 808328862384, 333883591116, 104687107296, 19146219756, 824678466, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 15 :=
  ⟨⟨1,20,63⟩,mass_cell 15 1 20 63 133 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 1698117722423, 810992227301, 316616597181, 87125445365, 11007772493, 89103240, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 15 :=
  ⟨⟨3,21,64⟩,mass_cell 15 3 21 64 131 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 1735683323661, 808624157380, 300197196196, 75552873604, 7699280740, 17863564] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 15 :=
  ⟨⟨5,24,66⟩,mass_cell 15 5 24 66 126 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 1810144329561, 806676402042, 262142523414, 50063270562, 2263945412, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 15 :=
  ⟨⟨1,27,67⟩,mass_cell 15 1 27 67 121 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 1846883256123, 806373633143, 234480620027, 32748841631, 387735517, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 15 :=
  ⟨⟨8,28,68⟩,mass_cell 15 8 28 68 120 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 1879685409776, 806321083016, 217781471916, 27019910072, 219123210] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 15 :=
  ⟨⟨2,32,69⟩,mass_cell 15 2 32 69 115 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 1913592410863, 813385639129, 189100129953, 14083364337, 135860] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 15 :=
  ⟨⟨1,36,70⟩,mass_cell 15 1 36 70 111 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 1942587547923, 812337669467, 156606504515, 6170911352, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 15 :=
  ⟨⟨6,39,71⟩,mass_cell 15 6 39 71 109 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 1968350994174, 822957860626, 136055414482, 3258027340, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 15 :=
  ⟨⟨7,44,72⟩,mass_cell 15 7 44 72 106 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 1988901534039, 835429749917, 108334233301, 840968077] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 15 :=
  ⟨⟨17,49,73⟩,mass_cell 15 17 49 73 103 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 2001457617979, 848884756476, 83062843228, 134658242] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 15 :=
  ⟨⟨68,27,72⟩,mass_cell 15 68 27 72 126 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 1988709776649, 834379668300, 107042495295, 89084490, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 15 :=
  ⟨⟨75,33,73⟩,mass_cell 15 75 33 73 117 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 2001457617979, 845371881828, 82867269168, 4598196, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 15 :=
  ⟨⟨78,43,74⟩,mass_cell 15 78 43 74 108 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 2001457617979, 869025856416, 63186289731, 5160680] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 15 :=
  ⟨⟨77,32,73⟩,mass_cell 15 77 32 73 119 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 2001457617979, 847620987414, 80767944610, 316251, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 15 :=
  ⟨⟨84,28,73⟩,mass_cell 15 84 28 73 125 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 2001457617979, 858174427552, 71954615006, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 15 :=
  ⟨⟨81,42,74⟩,mass_cell 15 81 42 74 109 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 2001457617979, 868885423698, 61394059607, 52360, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 15 :=
  ⟨⟨80,20,72⟩,mass_cell 15 80 20 72 142 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 1989591947199, 854606359638, 82350439630, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 15 :=
  ⟨⟨88,39,74⟩,mass_cell 15 88 39 74 112 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 2001457617979, 872311975338, 56984592080, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 15 :=
  ⟨⟨84,17,72⟩,mass_cell 15 84 17 72 153 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 1990056407584, 865070756150, 72868576467, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 15 :=
  ⟨⟨86,55,75⟩,mass_cell 15 86 55 75 102 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 2001457617979, 892815594020, 39926675060, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 15 :=
  ⟨⟨90,24,73⟩,mass_cell 15 90 24 73 133 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 2001457617979, 869582512131, 62564480833, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 15 :=
  ⟨⟨90,38,74⟩,mass_cell 15 90 38 74 113 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 2001457617979, 873993221008, 55521934438, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 15 :=
  ⟨⟨95,21,73⟩,mass_cell 15 95 21 73 140 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 2001457617979, 874207766382, 52981343249, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 15 :=
  ⟨⟨93,36,74⟩,mass_cell 15 93 36 74 115 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 2001457617979, 879658576807, 53766820109, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 15 :=
  ⟨⟨102,15,73⟩,mass_cell 15 102 15 73 163 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 2001457617979, 891172240705, 40380496866, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 15 :=
  ⟨⟨100,50,75⟩,mass_cell 15 100 50 75 105 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 2001457617979, 894570006908, 36769022322, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 15 :=
  ⟨⟨112,6,73⟩,mass_cell 15 112 6 73 255 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 2001457617979, 907811956436, 23045225237, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 15 :=
  ⟨⟨118,41,75⟩,mass_cell 15 118 41 75 111 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 2001457617979, 904029832758, 27336402648, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 15 :=
  ⟨⟨112,24,74⟩,mass_cell 15 112 24 74 134 (by decide)
    (by decide +kernel) [4552841175979, 3938191107403, 3378836157763, 2871623936659, 2413489953595, 2001457617979, 900123351840, 31865637870, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 15) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36]

end Low6969Allocation.Group15
end Z6969Source2348

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles15
section Z6969Source2349
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group15
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [14898891781, 40586845197, 82984125465, 78790431797, 64966116709, 60654454117], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30388437401, 55872921053, 60134426085], by decide +kernel⟩
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
private theorem i51 : checks (tilesOf batches) 121 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [36224374793, 61844700181, 87262787625, 18929536069, 56325929329, 47702520177], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [64647413169, 51661838793, 42971410913], by decide +kernel⟩
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
private theorem i54 : checks (tilesOf batches) 121 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [44915762189, 82917150749, 65905598521, 60721484121, 52114853209, 30371660189], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [60134335973, 51544493541], by decide +kernel⟩
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
private theorem i49 : checks (tilesOf batches) 121 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [49211125777, 82934128673, 48843239485, 60654379361, 43508211041, 21647575485], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [60151194081], by decide +kernel⟩
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
private theorem i52 : checks (tilesOf batches) 121 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [53472869397, 87128567849, 27519468613, 56443367761, 39280355665, 60134342117], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [51544488421], by decide +kernel⟩
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
private theorem i55 : checks (tilesOf batches) 121 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57650595865, 87078305837, 10322826313, 52165181769, 34985391433, 60235008461], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [47266301409, 30086510049], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i18 : checks (tilesOf batches) 121 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 121 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 121 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 121 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 121 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [66005783581, 78521996343, 43524920665, 30589763929, 60453115289, 43273327001], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [25825100249, 55303641, 25774767589], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i21 : checks (tilesOf batches) 121 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 121 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 121 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 121 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 121 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [74411302945, 57215002681, 56325923185, 43407546737, 26127025541, 21513356765], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [38526429, 38676371937, 25791545825], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i24 : checks (tilesOf batches) 121 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 121 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 121 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 121 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [87061392423, 31663374401, 56510410045, 39297066301, 17335832001, 34415027673], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21530135001, 55856229857], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i27 : checks (tilesOf batches) 121 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 121 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 121 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 121 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [87044683819, 18912758853, 52232223037, 35035721021, 34381475297, 51544488421], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [12889870821], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i30 : checks (tilesOf batches) 121 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 121 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 121 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 121 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [87027975215, 6027860041, 47954101565, 30757532989, 9299481917, 30069732837], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i33 : checks (tilesOf batches) 121 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 121 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 121 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [82749853747, 43625582917, 26429013317, 4970961221, 25774767589], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i36 : checks (tilesOf batches) 121 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 121 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 121 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69982460983, 39196466533, 22016607589, 541842789], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i39 : checks (tilesOf batches) 121 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 121 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 121 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [57198225467, 34784061825, 17604201857], by decide +kernel⟩
private def batches : List P := [p0]
private theorem i42 : checks (tilesOf batches) 121 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 121 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤121) (hj : a.j≤55) :
    Covered orders a ∨ Low6969Gate.Gated ((15 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 15 where
  orders := orders
  covers := by
    intro a ha box
    change 21+a.b≤142 ∧ 3+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6969Allocation.Group15
end Z6969Source2349

-- Source: ProximityPrize.SubmissionLower.Low6969Mass16
section Z6969Source2350
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group16

private def m0 : MassCell 16 :=
  ⟨⟨1,3,3⟩,mass_cell 16 1 3 3 237 (by decide)
    (by decide +kernel) [4459068999570, 3631656341141, 2923400411669, 2324034120621, 1821797373917, 1405601018405, 1065026841861, 790327572989, 572426881421, 402919377717, 274070613365, 178817080781, 110766213309, 64196385221, 34056911717, 15968048925, 6220993901, 1777884629, 271800021, 6893322] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 16 :=
  ⟨⟨2,5,25⟩,mass_cell 16 2 5 25 207 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3248933318787, 2468757342171, 1837387893099, 1334755239987, 942225722931, 642601753707, 420121815771, 260460464259, 150728325987, 79472099451, 36674554827, 13754533971, 3566950419, 402789387, 2017753, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 16 :=
  ⟨⟨1,6,31⟩,mass_cell 16 1 6 31 195 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3393309376193, 2579174017886, 1886069616606, 1340822679326, 921269878046, 606975884766, 379233371486, 221063010206, 117213472926, 54161431646, 20111558366, 4996525086, 477003806, 561064, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 16 :=
  ⟨⟨3,9,44⟩,mass_cell 16 3 9 44 169 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2921203837645, 2063309341878, 1349444669082, 834861521638, 480035120538, 249464887734, 111674446138, 39211619622, 8648433018, 581112118, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 16 :=
  ⟨⟨4,11,49⟩,mass_cell 16 4 11 49 158 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2212844954245, 1375433156149, 795434619013, 416462845237, 188359913221, 67196477365, 15271768069, 1113591733, 11155, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 16 :=
  ⟨⟨1,12,50⟩,mass_cell 16 1 12 50 152 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2255424572248, 1385929334104, 785387320664, 396680418136, 167899838296, 52346118488, 8529121624, 188225674, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 16 :=
  ⟨⟨2,13,52⟩,mass_cell 16 2 13 52 148 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2332353690974, 1407730449029, 770616923229, 370104473957, 144458428637, 38633969925, 4276135709, 12938718, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 16 :=
  ⟨⟨3,15,55⟩,mass_cell 16 3 15 55 140 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2436044203566, 1453285675350, 745389195698, 323718836966, 106018028658, 19464672470, 676825209, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 16 :=
  ⟨⟨2,18,58⟩,mass_cell 16 2 18 58 132 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2517511600769, 1524270319531, 716473291063, 267412371491, 64391637871, 5166221851, 321120] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 16 :=
  ⟨⟨4,19,59⟩,mass_cell 16 4 19 59 129 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2536729601607, 1550317712979, 701563454931, 246358752403, 52531846611, 2964579364, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 16 :=
  ⟨⟨1,21,60⟩,mass_cell 16 1 21 60 125 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2551163542108, 1582932816905, 680208214905, 214119537905, 34546785905, 680884692, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 16 :=
  ⟨⟨3,22,61⟩,mass_cell 16 3 22 61 123 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1629547109104, 677149257528, 201329442432, 28512409288, 323609587, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 16 :=
  ⟨⟨2,24,62⟩,mass_cell 16 2 24 62 119 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1678202840480, 659261936256, 173889410144, 17623380800, 21926156] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 16 :=
  ⟨⟨1,27,63⟩,mass_cell 16 1 27 63 115 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1716236300014, 618588450803, 132474223723, 7031090170, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 16 :=
  ⟨⟨1,29,64⟩,mass_cell 16 1 29 64 113 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1772941315246, 614354751463, 116175510895, 4004426038, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 16 :=
  ⟨⟨1,32,65⟩,mass_cell 16 1 32 65 109 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1821835376474, 592462787910, 90320809830, 1290124839, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 16 :=
  ⟨⟨1,35,66⟩,mass_cell 16 1 35 66 107 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1875553054178, 582437762216, 71897278076, 328234204] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 16 :=
  ⟨⟨2,39,67⟩,mass_cell 16 2 39 67 104 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1924853327329, 560917218330, 50771024766, 13025660] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 16 :=
  ⟨⟨14,43,68⟩,mass_cell 16 14 43 68 102 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1969760650595, 531378354200, 34213149508, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 16 :=
  ⟨⟨1,52,69⟩,mass_cell 16 1 52 69 97 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 2019122487341, 493947748250, 14143179577, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 16 :=
  ⟨⟨62,36,68⟩,mass_cell 16 62 36 68 108 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1960867001270, 525146146640, 47010473168, 205928552] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 16 :=
  ⟨⟨58,44,69⟩,mass_cell 16 58 44 69 102 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 2011720636204, 497269045400, 25778893208, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 16 :=
  ⟨⟨69,52,70⟩,mass_cell 16 69 52 70 98 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 2060086495053, 464620074064, 11814814159, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 16 :=
  ⟨⟨52,32,67⟩,mass_cell 16 52 32 67 111 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1911272214194, 552761717064, 69455164488, 1191483184, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 16 :=
  ⟨⟨75,41,69⟩,mass_cell 16 75 41 69 104 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 2010613080249, 496825256079, 28370910375, 5875391] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 16 :=
  ⟨⟨71,23,66⟩,mass_cell 16 71 23 66 126 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1863055426908, 577601022681, 87196187372, 971471958, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 16 :=
  ⟨⟨75,27,67⟩,mass_cell 16 75 27 67 119 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1912445881149, 554647090591, 67416396613, 438024314, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 16 :=
  ⟨⟨76,33,68⟩,mass_cell 16 76 33 68 111 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1961308673541, 527374033294, 48191820682, 239856910, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 16 :=
  ⟨⟨75,51,70⟩,mass_cell 16 75 51 70 99 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 2059763913374, 464612439206, 12446859800, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 16 :=
  ⟨⟨80,40,69⟩,mass_cell 16 80 40 69 105 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 2010541107396, 496981987844, 28764224612, 10799702] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 16 :=
  ⟨⟨74,22,66⟩,mass_cell 16 74 22 66 128 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1865455256486, 581154808923, 84145296683, 342850302, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 16 :=
  ⟨⟨85,39,69⟩,mass_cell 16 85 39 69 106 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 2010440973685, 496510388991, 28643520215, 9850259] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 16 :=
  ⟨⟨82,19,66⟩,mass_cell 16 82 19 66 136 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1873881472599, 592087033067, 70627948361, 46376, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 16 :=
  ⟨⟨81,32,68⟩,mass_cell 16 81 32 68 112 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1961087404778, 525472357452, 46316789472, 81267735, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 16 :=
  ⟨⟨93,21,67⟩,mass_cell 16 93 21 67 132 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1923053444068, 567663934092, 45718418519, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 16 :=
  ⟨⟨81,50,70⟩,mass_cell 16 81 50 70 99 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 2059424793286, 464119115670, 12949210768, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 16 :=
  ⟨⟨101,18,67⟩,mass_cell 16 101 18 67 141 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1929012867219, 568655393476, 31247766613, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 16 :=
  ⟨⟨85,31,68⟩,mass_cell 16 85 31 68 114 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1961644341871, 526037302347, 44591935132, 5359221, 0] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 16 :=
  ⟨⟨111,44,70⟩,mass_cell 16 111 44 70 103 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 2059067005774, 462636074142, 12767861950, 0] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 16 :=
  ⟨⟨90,38,69⟩,mass_cell 16 90 38 69 107 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 2010312380731, 495374354077, 27888706867, 194580] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 16 :=
  ⟨⟨107,15,67⟩,mass_cell 16 107 15 67 152 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1937220491762, 574103667868, 21125685896, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 16 :=
  ⟨⟨118,9,67⟩,mass_cell 16 118 9 67 192 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1954324105389, 573352692010, 6676973851, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 16 :=
  ⟨⟨115,43,70⟩,mass_cell 16 115 43 70 104 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 2059300357916, 462907631692, 12075598146, 0] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 16 :=
  ⟨⟨98,36,69⟩,mass_cell 16 98 36 69 109 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 2011087289638, 496675136496, 25990303808, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 16 :=
  ⟨⟨125,40,70⟩,mass_cell 16 125 40 70 106 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 2060631136607, 466053975786, 9595598344, 0] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 16 :=
  ⟨⟨111,22,68⟩,mass_cell 16 111 22 68 130 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 1973793928341, 539335711852, 19997495616, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 16 :=
  ⟨⟨125,27,69⟩,mass_cell 16 125 27 69 121 (by decide)
    (by decide +kernel) [4568515235428, 3984380750340, 3457294488228, 2983462590532, 2559220370148, 2018837915194, 504491367670, 9770234918, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 16) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46]

end Low6969Allocation.Group16
end Z6969Source2350

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles16
section Z6969Source2351
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group16
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [6425873413, 23590409225, 44915829777, 87178434593, 48876530749, 52248598869], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39380618581, 26026096069, 8846234053, 51644673513, 51544089089], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i3 : checks (tilesOf batches) 128 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 128 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 128 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 128 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 128 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 128 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 128 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [27885770761, 44949582869, 87144947745, 40286598205, 48003965261, 39347065165], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21731129797, 8846234053, 51594343925, 34414629365, 21529802229], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i6 : checks (tilesOf batches) 128 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 128 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 128 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 128 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 128 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 128 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 128 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40603755533, 70115871773, 78572064817, 35001766241, 30572655969, 4970698081], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [52131155309, 39279952237, 21613688285, 13006982621, 51678225889, 47265896957], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [25791212029, 8611352061, 12889540097], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i9 : checks (tilesOf batches) 128 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 128 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 128 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 128 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 128 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 128 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [44882341905, 87027440673, 44447346749, 48087850289, 35203091761, 21814948261], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17452943781, 51678228961, 8695237097, 4400272873, 17218056697, 8628127225], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [42970932733, 30086107645], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i12 : checks (tilesOf batches) 128 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 128 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 128 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 128 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 128 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 128 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [49127308309, 87010798629, 27368144961, 43792952625, 39296735537, 13141197249], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8779125185, 25992468941, 17402607053, 51711786457, 4366717425, 71752177], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [42971001341, 4299606529], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i15 : checks (tilesOf batches) 128 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 128 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 128 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 128 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 128 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57465784345, 86960603181, 6044374089, 35253354797, 30790755629, 22116943149], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [51946670497, 39028293025, 8829453769, 4500935113, 21630395869, 13023755741], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099600157167, 34381069821, 21418493, 21419517, 8594570753], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i18 : checks (tilesOf batches) 128 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 128 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 128 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 128 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 128 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61643445277, 78404292657, 30874571065, 26411905337, 13560630585, 47752369545], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34850768265, 17369051605, 8762344917, 4400271837, 1099667266015, 38195705], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099549824507, 17201277437, 34364294657, 4299605505, 4640257], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i21 : checks (tilesOf batches) 128 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 128 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 128 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 128 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 128 53 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [61626802209, 65620122677, 30673313109, 26193804629, 1100237691223, 43457405321], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [30572580233, 13124419005, 8762346941, 17285164521, 4366716393, 1099616933355], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8628126201, 21417469, 21418493], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i24 : checks (tilesOf batches) 128 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 128 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 128 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 128 48 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [74226560037, 40051717181, 43692289353, 26529274185, 17587090829, 13208308109], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100002810255, 4450601437, 155636189, 1099667264991, 12956644849, 4366714353], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [42971000317, 25774365185], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i27 : checks (tilesOf batches) 128 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 128 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 128 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 128 51 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [74193074217, 27267481665, 39430879557, 26495787333, 22016277829, 4534490537], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13074087369, 4484156873, 1099633710567, 1099633711591, 21529797109, 8644901365], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4333159929, 38194681, 38195705, 38659258881], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i30 : checks (tilesOf batches) 128 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 128 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 128 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 128 54 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [78387446829, 10238677065, 35236644145, 30706870577, 17771645233, 4568041921], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17402538445, 13057310157, 4400271829, 1099700820439, 71750129, 1099583378931], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8628125177], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i33 : checks (tilesOf batches) 128 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 128 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 128 49 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [78337183793, 30958457129, 30673318185, 9332773161, 17452937661, 8829453757], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [155636189, 1099667264991, 1099667266015, 4333159929, 38194681, 30069330433], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [12889534977, 8594571777], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i36 : checks (tilesOf batches) 128 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 128 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 128 52 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [65569791029, 26512497993, 22033054025, 9198555465, 13090863569, 4500933073], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [155636189, 1099667264991, 1099667266015, 25791143421], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i39 : checks (tilesOf batches) 128 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 128 47 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [52802332729, 22083381609, 17620648297, 4802925929, 8779121109, 4450602453], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099633710567, 1099633711591, 21496244733, 21417469, 21418493], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i42 : checks (tilesOf batches) 128 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 128 50 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤128) (hj : a.j≤54) :
    Covered orders a ∨ Low6969Gate.Gated ((16 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 16 where
  orders := orders
  covers := by
    intro a ha box
    change 14+a.b≤142 ∧ 4+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6969Allocation.Group16
end Z6969Source2351

-- Source: ProximityPrize.SubmissionLower.Low6969Mass17
section Z6969Source2352
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group17

private def m0 : MassCell 17 :=
  ⟨⟨2,4,9⟩,mass_cell 17 2 4 9 191 (by decide)
    (by decide +kernel) [4600262810217, 3813721816035, 3058740478371, 2410476707451, 1860853229931, 1401777655923, 1025142478995, 722825076171, 486687707931, 308577518211, 180326534403, 93751667355, 40654711371, 12822344211, 2026127091, 34595196] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 17 :=
  ⟨⟨1,6,24⟩,mass_cell 17 1 6 24 173 (by decide)
    (by decide +kernel) [4628005587678, 4133785273020, 3379650087932, 2561315481376, 1883990405548, 1335646306592, 903803836924, 575532855232, 337452426476, 175730821888, 76085518972, 23783201504, 3639759532, 52895035, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 17 :=
  ⟨⟨3,7,30⟩,mass_cell 17 3 7 30 166 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3568311643159, 2669937958404, 1906524404532, 1304061132132, 843798898836, 506845135044, 274163943924, 126576101412, 44759056212, 9246929796, 430859248, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 17 :=
  ⟨⟨2,9,37⟩,mass_cell 17 2 9 37 153 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 2901340877255, 1986412916979, 1284023076287, 768178518827, 411786349623, 186653615075, 63487302959, 11894342427, 388722661, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 17 :=
  ⟨⟨3,12,44⟩,mass_cell 17 3 12 44 140 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3168718718690, 2126624540577, 1258108976865, 662941071697, 292051732401, 94096636353, 15456230977, 302396644, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 17 :=
  ⟨⟨2,14,47⟩,mass_cell 17 2 14 47 132 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3240356969420, 2233928798764, 1254422563440, 608620036788, 232260469432, 55725848892, 4040899584, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 17 :=
  ⟨⟨1,15,48⟩,mass_cell 17 1 15 48 129 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3254278045664, 2274223655782, 1244673145862, 578258221222, 203446824262, 40523089382, 1595731054, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 17 :=
  ⟨⟨1,17,50⟩,mass_cell 17 1 17 50 124 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2376184662936, 1231386333936, 522355589320, 154286354208, 19860727800, 111583445, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 17 :=
  ⟨⟨1,18,51⟩,mass_cell 17 1 18 51 121 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2434789558527, 1235096717548, 501601643176, 135538839932, 13647008104, 11693842, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 17 :=
  ⟨⟨1,21,53⟩,mass_cell 17 1 21 53 115 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2539112832372, 1215728812694, 427400250246, 83854750262, 3060173722, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 17 :=
  ⟨⟨1,22,54⟩,mass_cell 17 1 22 54 114 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2600307605739, 1243481069256, 421298404764, 75600853656, 1977022684, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 17 :=
  ⟨⟨7,23,55⟩,mass_cell 17 7 23 55 112 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2651524344068, 1252451396834, 402077049218, 65083280418, 1183586915, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 17 :=
  ⟨⟨1,26,56⟩,mass_cell 17 1 26 56 108 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2700171168742, 1245808853739, 348240265779, 37623778387, 56643192] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 17 :=
  ⟨⟨10,30,58⟩,mass_cell 17 10 30 58 104 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2789864325616, 1275708007608, 291366115060, 18227860272, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 17 :=
  ⟨⟨1,35,59⟩,mass_cell 17 1 35 59 99 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2826722177542, 1275200600088, 226943249944, 5407946236, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 17 :=
  ⟨⟨1,39,60⟩,mass_cell 17 1 39 60 96 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2856496670304, 1305054086820, 190097681812, 1810132404] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 17 :=
  ⟨⟨11,43,61⟩,mass_cell 17 11 43 61 94 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1344631805366, 158457780806, 484517090] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 17 :=
  ⟨⟨1,51,62⟩,mass_cell 17 1 51 62 90 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1391803879224, 109396755832, 7637] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 17 :=
  ⟨⟨67,14,54⟩,mass_cell 17 67 14 54 139 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2583365024932, 1218077531778, 445104174414, 113334613714, 12035920187, 163185, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 17 :=
  ⟨⟨60,25,58⟩,mass_cell 17 60 25 58 112 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2784483883619, 1246581941241, 308744481189, 35374813617, 338185869, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 17 :=
  ⟨⟨60,33,60⟩,mass_cell 17 60 33 60 102 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2855403400288, 1289914540101, 222168960801, 8557811908, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 17 :=
  ⟨⟨34,41,61⟩,mass_cell 17 34 41 61 95 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1335519686499, 166982766767, 1125685444] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 17 :=
  ⟨⟨23,49,62⟩,mass_cell 17 23 49 62 91 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1388183563494, 117486786726, 13119525] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 17 :=
  ⟨⟨60,22,57⟩,mass_cell 17 60 22 57 117 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2738898823442, 1233044447094, 346869597114, 54123324750, 1823534526, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 17 :=
  ⟨⟨69,32,60⟩,mass_cell 17 69 32 60 103 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2855266665778, 1286520367550, 224243482010, 9832361237, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 17 :=
  ⟨⟨75,23,58⟩,mass_cell 17 75 23 58 115 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2783960440693, 1243441703792, 310522196384, 38490090192, 721848427, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 17 :=
  ⟨⟨45,40,61⟩,mass_cell 17 45 40 61 96 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1330841253801, 170412057561, 1565217978] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 17 :=
  ⟨⟨74,37,61⟩,mass_cell 17 74 37 61 99 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1321129365327, 178805839635, 3261509014, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 17 :=
  ⟨⟨76,44,62⟩,mass_cell 17 76 44 62 94 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1373182071661, 131562698517, 397254174] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 17 :=
  ⟨⟨73,27,59⟩,mass_cell 17 73 27 59 109 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2823748178980, 1261012190952, 269696807848, 22570304616, 56474729, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 17 :=
  ⟨⟨82,36,61⟩,mass_cell 17 82 36 61 100 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1320356294585, 181492832425, 3901394158, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 17 :=
  ⟨⟨67,21,57⟩,mass_cell 17 67 21 57 119 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2738752761148, 1233010498428, 348672013588, 56116027692, 2300772804, 0] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 17 :=
  ⟨⟨77,31,60⟩,mass_cell 17 77 31 60 104 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2855192138248, 1285071554322, 226465215858, 11044481490, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 17 :=
  ⟨⟨85,18,57⟩,mass_cell 17 85 18 57 127 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2739912909482, 1238940593044, 348432737848, 50759552428, 466683645, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 17 :=
  ⟨⟨85,43,62⟩,mass_cell 17 85 43 62 95 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1371394608872, 133711385288, 562074805] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 17 :=
  ⟨⟨90,17,57⟩,mass_cell 17 90 17 57 131 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2740852057057, 1243442189453, 347035005401, 44482158425, 12174175, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 17 :=
  ⟨⟨85,53,63⟩,mass_cell 17 85 53 63 90 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1417930925458, 86362838984, 43359] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 17 :=
  ⟨⟨103,41,62⟩,mass_cell 17 103 41 62 96 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1366328800326, 135668560694, 914510409] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 17 :=
  ⟨⟨103,51,63⟩,mass_cell 17 103 51 63 91 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1415643411650, 89680842838, 6877665] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 17 :=
  ⟨⟨99,15,57⟩,mass_cell 17 99 15 57 138 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2743280066296, 1254626779620, 340849299732, 28678462622, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 17 :=
  ⟨⟨81,26,59⟩,mass_cell 17 81 26 59 111 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2823520164542, 1257736067854, 268816547906, 23232669934, 100488946, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 17 :=
  ⟨⟨112,50,63⟩,mass_cell 17 112 50 63 92 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1413982751999, 90747169473, 16961019] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 17 :=
  ⟨⟨109,12,57⟩,mass_cell 17 109 12 57 153 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2748999156036, 1284241841670, 332272836370, 11117817366, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 17 :=
  ⟨⟨110,40,62⟩,mass_cell 17 110 40 62 97 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1366886853840, 137404073892, 1098971628, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 17 :=
  ⟨⟨118,39,62⟩,mass_cell 17 118 39 62 98 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1365086065772, 137185884684, 1195428383, 0] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 17 :=
  ⟨⟨120,49,63⟩,mass_cell 17 120 49 63 92 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1413416997148, 91945512723, 32934684] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 17 :=
  ⟨⟨91,35,61⟩,mass_cell 17 91 35 61 101 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1316600952952, 181628847608, 4377700714, 0] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 17 :=
  ⟨⟨124,12,58⟩,mass_cell 17 124 12 58 154 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2792590303495, 1304241043773, 273597074828, 958887560, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 17 :=
  ⟨⟨125,38,62⟩,mass_cell 17 125 38 62 99 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1364822365036, 137165503440, 1214195599, 0] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 17 :=
  ⟨⟨112,32,61⟩,mass_cell 17 112 32 61 104 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1316262630222, 183304784378, 4929833960, 0] (by decide +kernel) (by decide +kernel)⟩
private def m50 : MassCell 17 :=
  ⟨⟨128,48,63⟩,mass_cell 17 128 48 63 93 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1412535660774, 92672312114, 52796601] (by decide +kernel) (by decide +kernel)⟩
private def m51 : MassCell 17 :=
  ⟨⟨116,25,60⟩,mass_cell 17 116 25 60 114 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2855294057322, 1288141068149, 224265893057, 7841544544, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m52 : MassCell 17 :=
  ⟨⟨127,6,57⟩,mass_cell 17 127 6 57 206 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2761403489933, 1337576965409, 265091566369, 28388816, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m53 : MassCell 17 :=
  ⟨⟨124,30,61⟩,mass_cell 17 124 30 61 107 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1318576509558, 181475235634, 3566151356, 0] (by decide +kernel) (by decide +kernel)⟩
private def m54 : MassCell 17 :=
  ⟨⟨131,37,62⟩,mass_cell 17 131 37 62 100 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1366203200760, 137510288208, 1132271934, 0] (by decide +kernel) (by decide +kernel)⟩
private def m55 : MassCell 17 :=
  ⟨⟨125,23,60⟩,mass_cell 17 125 23 60 117 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2855579012754, 1297231516308, 220614071428, 3854315556, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m56 : MassCell 17 :=
  ⟨⟨136,47,63⟩,mass_cell 17 136 47 63 93 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1411328505824, 92850085666, 71724654] (by decide +kernel) (by decide +kernel)⟩
private def m57 : MassCell 17 :=
  ⟨⟨133,9,58⟩,mass_cell 17 133 9 58 174 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2796453604094, 1328506831448, 242217371694, 8783390, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m58 : MassCell 17 :=
  ⟨⟨137,20,60⟩,mass_cell 17 137 20 60 125 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2856099524277, 1312787585247, 207625535955, 282170905, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m59 : MassCell 17 :=
  ⟨⟨121,18,59⟩,mass_cell 17 121 18 59 129 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2826036954440, 1290227063124, 259129996640, 4671518607, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m60 : MassCell 17 :=
  ⟨⟨134,28,61⟩,mass_cell 17 134 28 61 110 (by decide)
    (by decide +kernel) [4628005587678, 4137434455250, 3682501885502, 3261913664034, 2874369528446, 1324501268349, 178528884933, 1586160979, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 17) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51, m52, m53, m54, m55, m56, m57, m58, m59, m60]

end Low6969Allocation.Group17
end Z6969Source2352

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles17
section Z6969Source2353
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group17
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2332101637, 10905784329, 27969592333, 86942627861, 78638713905, 44127631633], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43976910097, 26545590641, 30588972401, 9231584625, 13157445105, 8812150257], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8761887217, 38826436105, 25941609993, 1099666806287, 43037302301, 4349479453], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099599696415, 4332699177, 4332701225, 42970335789, 12905785901, 20958765], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i3 : checks (tilesOf batches) 140 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 140 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 140 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 140 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 140 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 140 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 140 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [23623899145, 44798062609, 87077379105, 40252583997, 39631609149, 35169011005], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39212394813, 4634694077, 13341993413, 13191002565, 13107186117, 43372851661], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4416588285, 25975162369, 17368523265, 43104410127, 4433295889, 4399809041], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099650028051, 1099650029075, 1099599694367, 1099599695391, 38692216361, 20955693], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [20956717, 12889006641], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 140 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 140 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 140 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 140 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 140 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 140 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [32315352077, 61575676953, 87027253293, 1849611337, 30974705981, 34967757117], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17855071549, 43691623797, 30857195893, 17519518161, 8912811473, 8812151249], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099851353571, 1099851354595, 1099700360711, 4399809033, 1099683580427, 17284567577], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4366186017, 4332699169, 8644372005, 4349407781, 1099566138919, 42987038249], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [38692213289, 20954669, 20955693], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i9 : checks (tilesOf batches) 140 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 140 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 140 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 140 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 140 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 140 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [40670867473, 86959872033, 44396555325, 39698651425, 35252896033, 35018089761], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13174229401, 17519519169, 8912812481, 8812152257, 1099851354595, 1099851355619], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [43205145077, 26008715769, 13123886585, 1099750688251, 1099750689275, 1099750690299], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4366187025, 1099650023955, 8677928469, 34447580701, 54442533, 54509093], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4315852333, 20887085], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 140 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 140 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 140 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 140 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 140 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 140 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [48992631829, 86943231013, 23055941697, 31192673569, 30924377377, 34934205729], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13291662765, 13140671917, 43456740793, 30571981241, 8761888189, 1099817799147], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099817800171, 1099817801195, 4450074093, 1099801019887, 1099801020911, 17452338673], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [13123887601, 4433293841, 138328593, 1099633180183, 1099633246743, 8610816557], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4315852333, 21478869553], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 140 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 140 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 140 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 140 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 140 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [61542189081, 82648400941, 1748948041, 30941152553, 34917426473, 13576882473], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39480543597, 30857195885, 13341992369, 13174224305, 8812152241, 1099918463443], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099817797099, 1099817798123, 1099817799147, 1099801023983, 4466849273, 1099750620667], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750621691, 17402008061, 8661149217, 4332630561, 1099566070311, 30085575213], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [20886061, 20887085], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 140 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 140 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 140 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 140 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 140 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [65753404445, 69830677557, 26512037185, 26294006081, 9181252929, 39497323869], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26646183261, 8929587649, 8795372993, 1099985570243, 1099918462419, 1099918463443], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918464467, 13140662773, 8795367925, 1099767397879, 1099767398903, 1099767465463], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [121550357, 1099633179159, 38692214313, 4332628521, 37663273, 25773833777], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i21 : checks (tilesOf batches) 140 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 140 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 140 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 140 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 140 53 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [69964619809, 52785095737, 35319865677, 26612630861, 26344268109, 17603411301], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4768846181, 4533960141, 1099935172047, 1099935238607, 1099935239631, 13207773657], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8812147161, 1099884909019, 1099884910043, 1099683511819, 1099683578379, 4382962193], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099649956371, 21579531801, 12989668889, 4332629545, 37664297], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i24 : checks (tilesOf batches) 140 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 140 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 140 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 140 48 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [69931133989, 40000925757, 35236048201, 26528813385, 22032526665, 13174228353], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100254008707, 1099951949259, 1099952015819, 1099952016843, 1099952017867, 8896032209], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8761817553, 1099733842431, 1099733843455, 1099733844479, 17385230849, 8795366913], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [30152617501, 17267789341, 87994909, 87995933], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 140 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 140 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 140 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 140 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69914490921, 27216690241, 30924306761, 22250625353, 22015816009, 8795376029], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100136568223, 8862478797, 4517182925, 1099935172047, 1099918461395, 1099918462419], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099918463443, 13073553925, 8728259077, 1099700289031, 1099700355591, 138327569], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099649956371, 25874496025, 17284634137, 4332628521, 37663273], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 140 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 140 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 140 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [82564514861, 1681839177, 31041815829, 30739899669, 17838294293, 1100035835319], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100035836343, 1100035902903, 1100035903927, 13291660729, 8896034233, 4567515577], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099868132831, 1099733844479, 21680195073, 13090332161, 4399740421, 1099700289031], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4382961181, 71218721, 1099582847523], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 140 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 140 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 140 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [74041757745, 26646188329, 26377825577, 13492996393, 13190999485, 8795372989], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100002281919, 1100002348479, 1100002349503, 1100002350527, 1099784175091, 1099784176115], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099784242675, 17402008061, 8812144125, 4433293833, 1099683510795, 20886061], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [20887085], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 140 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 140 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 140 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [61274364981, 26411375945, 21948709193, 4852732233, 8845703613, 1100002280895], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100002281919, 1100002348479, 1099918463443, 1099918464467, 13207772645, 8828923365], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099733842431, 1099733843455, 1099733844479, 4366183969, 71218721], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 140 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 140 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [48490129465, 17771112805, 17586634085, 4752068965, 8761818569, 1099952015819], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099952016843, 1099901686231, 1099901687255, 8828922357, 4483626485, 1099767397879], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099767398903, 1099767465463, 54441509, 1099566070311, 4299074097, 4108849], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i42 : checks (tilesOf batches) 140 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 140 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤140) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((17 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 17 where
  orders := orders
  covers := by
    intro a ha box
    change 2+a.b≤142 ∧ 5+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6969Allocation.Group17
end Z6969Source2353

-- Source: ProximityPrize.SubmissionLower.Low6969Mass18
section Z6969Source2354
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group18

private def m0 : MassCell 18 :=
  ⟨⟨1,3,9⟩,mass_cell 18 1 3 9 214 (by decide)
    (by decide +kernel) [4535673134286, 3724046369786, 2979912180874, 2350634548762, 1824187957418, 1389169744954, 1034800103626, 750922079834, 528001574122, 357127341178, 230010989834, 138986983066, 77012637994, 37668125882, 15156472138, 4303556314, 558112106, 4392987] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 18 :=
  ⟨⟨1,6,36⟩,mass_cell 18 1 6 36 185 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3405350498000, 2675541142544, 1938901521772, 1359030814576, 913933660316, 582930280048, 346656476524, 187063634192, 87418719196, 32304279376, 7618444268, 574925104, 4377, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 18 :=
  ⟨⟨1,7,41⟩,mass_cell 18 1 7 41 177 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2809011252555, 2010503728380, 1374186396396, 894550570716, 546323629260, 305809549500, 150888908460, 61018882716, 17233248396, 2142381180, 12316596, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 18 :=
  ⟨⟨2,9,48⟩,mass_cell 18 2 9 48 164 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2919506578590, 2165077976157, 1404281807649, 853454526661, 474454558281, 231681842349, 92077833457, 25125500949, 2849328921, 9179633, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 18 :=
  ⟨⟨1,12,54⟩,mass_cell 18 1 12 54 150 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2360123712713, 1467624250171, 812820849475, 392552627915, 151976522515, 38864286811, 3602490851, 1764643, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 18 :=
  ⟨⟨1,14,57⟩,mass_cell 18 1 14 57 142 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2437268773557, 1525575728801, 794398625697, 347544814793, 112460851097, 19200807057, 464807612, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 18 :=
  ⟨⟨1,15,58⟩,mass_cell 18 1 15 58 139 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2456919287228, 1543908614344, 778214183544, 322452491304, 93902334424, 12275533704, 86328703, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 18 :=
  ⟨⟨1,16,59⟩,mass_cell 18 1 16 59 136 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2473416865289, 1569798082665, 766914540777, 301122087993, 78590516121, 7602014025, 5568139, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 18 :=
  ⟨⟨1,18,61⟩,mass_cell 18 1 18 61 131 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 1645205968544, 758483602308, 268336117568, 55758320084, 2671521779, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 18 :=
  ⟨⟨2,19,62⟩,mass_cell 18 2 19 62 129 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 1692449042828, 756709900556, 253706830988, 46753430540, 1486595805, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 18 :=
  ⟨⟨1,21,63⟩,mass_cell 18 1 21 63 125 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 1730152018975, 732591936748, 217991329436, 29573806156, 241991278, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 18 :=
  ⟨⟨1,23,64⟩,mass_cell 18 1 23 64 121 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 1770794373547, 713667885674, 187581180938, 18051323562, 11096500, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 18 :=
  ⟨⟨2,24,65⟩,mass_cell 18 2 24 65 120 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 1824528687156, 730834059202, 183883833254, 15674755474, 1805725] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 18 :=
  ⟨⟨1,27,66⟩,mass_cell 18 1 27 66 116 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 1862573100806, 703268705838, 145279283742, 6557992588, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 18 :=
  ⟨⟨1,29,67⟩,mass_cell 18 1 29 67 114 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 1910289864114, 711461503540, 131372251860, 3956267305, 0] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 18 :=
  ⟨⟨3,32,68⟩,mass_cell 18 3 32 68 111 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 1951043581044, 700426045378, 105869008222, 1407142510, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 18 :=
  ⟨⟨3,36,69⟩,mass_cell 18 3 36 69 108 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 1990718194136, 688193451950, 78997598658, 208610556] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 18 :=
  ⟨⟨3,41,70⟩,mass_cell 18 3 41 70 104 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2028335179419, 676262803846, 54343974758, 699414] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 18 :=
  ⟨⟨1,48,71⟩,mass_cell 18 1 48 71 101 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2062391759430, 660017681293, 31371102469, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 18 :=
  ⟨⟨71,33,70⟩,mass_cell 18 71 33 70 112 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2022709931106, 662032139482, 72467885594, 772024404, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 18 :=
  ⟨⟨46,43,71⟩,mass_cell 18 46 43 71 104 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2060258607414, 656821937424, 41983407696, 19790] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 18 :=
  ⟨⟨55,51,72⟩,mass_cell 18 55 51 72 100 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2090249349386, 645740078006, 22447000002, 0] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 18 :=
  ⟨⟨78,32,70⟩,mass_cell 18 78 32 70 113 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2022360350511, 659875317454, 72451348946, 876987331, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 18 :=
  ⟨⟨55,42,71⟩,mass_cell 18 55 42 71 105 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2059805212368, 654259804792, 43463445932, 1755180] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 18 :=
  ⟨⟨63,50,72⟩,mass_cell 18 63 50 72 101 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2090141353967, 645367924733, 23609084250, 0] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 18 :=
  ⟨⟨72,23,68⟩,mass_cell 18 72 23 68 125 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 1940770900437, 682622922262, 124148288710, 6685583901, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 18 :=
  ⟨⟨74,27,69⟩,mass_cell 18 74 27 69 119 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 1982900823386, 673427836432, 99699807504, 3266105944, 0] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 18 :=
  ⟨⟨84,16,67⟩,mass_cell 18 84 16 67 144 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 1904382997713, 707391241712, 136932415689, 1921779506, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 18 :=
  ⟨⟨70,40,71⟩,mass_cell 18 70 40 71 106 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2059335209753, 652756357098, 46518590718, 23844298] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 18 :=
  ⟨⟨77,39,71⟩,mass_cell 18 77 39 71 107 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2059166981258, 652090567422, 47665792510, 48075473] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 18 :=
  ⟨⟨87,47,72⟩,mass_cell 18 87 47 72 102 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2089807578674, 641581115650, 26140767842, 0] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 18 :=
  ⟨⟨84,38,71⟩,mass_cell 18 84 38 71 108 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2058992083808, 650834335216, 48292597940, 77423077] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 18 :=
  ⟨⟨89,24,69⟩,mass_cell 18 89 24 69 124 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 1983937731029, 676348939521, 95847157633, 1307213229, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 18 :=
  ⟨⟨94,46,72⟩,mass_cell 18 94 46 72 103 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2089746969866, 640967189162, 26795023718, 0] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 18 :=
  ⟨⟨105,3,66⟩,mass_cell 18 105 3 66 271 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 1905973166046, 776091621114, 72115017082, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 18 :=
  ⟨⟨110,18,69⟩,mass_cell 18 110 18 69 139 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 1990137892793, 695399721451, 72666444043, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 18 :=
  ⟨⟨83,31,70⟩,mass_cell 18 83 31 70 114 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2022605228148, 662069576952, 73565413128, 953294976, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 18 :=
  ⟨⟨107,44,72⟩,mass_cell 18 107 44 72 104 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2089675772714, 640116876453, 27575906965, 102020] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 18 :=
  ⟨⟨104,14,68⟩,mass_cell 18 104 14 68 153 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 1954002763273, 714656253192, 87626577192, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 18 :=
  ⟨⟨113,43,72⟩,mass_cell 18 113 43 72 105 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2089665435426, 639929493112, 27645257272, 297756] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 18 :=
  ⟨⟨118,42,72⟩,mass_cell 18 118 42 72 106 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2089708409009, 641131661117, 27772380178, 0] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 18 :=
  ⟨⟨119,15,69⟩,mass_cell 18 119 15 69 150 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 1993850945942, 702941198934, 56576458549, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 18 :=
  ⟨⟨112,33,71⟩,mass_cell 18 112 33 71 113 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2059129613385, 651266638567, 46269290025, 7315, 0] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 18 :=
  ⟨⟨116,32,71⟩,mass_cell 18 116 32 71 114 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2059397436464, 653634093330, 45201376505, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 18 :=
  ⟨⟨124,13,69⟩,mass_cell 18 124 13 69 159 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 1996820275635, 709603416957, 47488406795, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 18 :=
  ⟨⟨128,40,72⟩,mass_cell 18 128 40 72 107 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2089791704914, 642538649730, 26861356131, 0] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 18 :=
  ⟨⟨123,6,68⟩,mass_cell 18 123 6 68 217 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 1971928817151, 742259838232, 41433359020, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 18 :=
  ⟨⟨126,12,69⟩,mass_cell 18 126 12 69 165 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 1998571546373, 714577660995, 44031182728, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 18 :=
  ⟨⟨121,22,70⟩,mass_cell 18 121 22 70 130 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2026527691224, 677131704540, 52031706659, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 18 :=
  ⟨⟨124,30,71⟩,mass_cell 18 124 30 71 117 (by decide)
    (by decide +kernel) [4555403468678, 3950877244698, 3408417881318, 2923641154538, 2492322680358, 2059923804006, 657213001702, 41467485605, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 18) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49]

end Low6969Allocation.Group18
end Z6969Source2354

-- Source: ProximityPrize.SubmissionLower.Low6969Tiles18
section Z6969Source2355
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6969Allocation.Group18
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low6969Encoding (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [14630325255, 36476361743, 82900107289, 74545729587, 56644288851, 48037722451], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34817419683, 9064467873, 39095242153, 55872665097, 47249324561, 34364500499], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
private theorem i51 : checks (tilesOf batches) 132 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤132) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [32214620171, 53405628437, 87229099047, 23392141379, 47970610535, 35085852007], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [56090704343, 47265880589, 21496381967], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤132) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [40805344269, 78638894109, 65871910967, 52282215775, 43642159455, 26277817747], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13426542993, 38709723653, 25824897541, 12906448397, 51544073745, 51544218131], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
private theorem i49 : checks (tilesOf batches) 132 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤132) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [45067153425, 87094746145, 40269951037, 48121535811, 35220000067, 21815144897], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13191662019, 55855886863, 8611482125, 21550605, 34364427793], by decide +kernel⟩
private def batches : List P := [p0, p1]
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
private theorem i52 : checks (tilesOf batches) 132 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤132) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [49261722645, 87078104101, 23241146433, 43826638147, 35085785409, 26412039489], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13107772893, 8728923625, 30186904051, 17302075889, 51644808697, 4316515853], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21550605, 25774496273, 17184634385], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i15 : checks (tilesOf batches) 132 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 132 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 132 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 132 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 132 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤132) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57583421465, 87027908653, 1917310025, 39498187069, 30774110525, 13678201149], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [51896469949, 38994869693, 21647370729, 13023887849, 4366848509, 21513152009], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8611480077, 4316515853, 38659390993], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i18 : checks (tilesOf batches) 132 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 132 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 132 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 132 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 132 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤132) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [57566778397, 78471531569, 35119336777, 26428813641, 9349680457, 47601505725], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34716681661, 17352405481, 8762476009, 21546707457, 4333294081, 21549581], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21550605], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i21 : checks (tilesOf batches) 132 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 132 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 132 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 132 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 132 53 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤132) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [70133047329, 52936746041, 47886721397, 30706930037, 17738215817, 17570514313], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8745698793, 4417180137, 38326793, 1099549955595, 47249252881, 30069461521], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17184633361, 4299736593, 4771345], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i24 : checks (tilesOf batches) 132 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 132 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 132 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 132 48 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤132) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [70099561509, 40152510525, 43625311601, 30673443185, 17553734053, 8947027365], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4366847485, 1099600287231, 12956776961, 4366846465, 25824827909, 12939998725], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4772369], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i27 : checks (tilesOf batches) 132 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 132 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 132 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 132 51 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤132) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [74277156905, 23157260353, 39431010649, 26495918425, 22016408921, 1099768059351], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13074218461, 4484287965, 21513150985, 12923222537, 4316514829, 21549581], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i30 : checks (tilesOf batches) 132 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 132 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 132 46 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤132) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [86944023597, 39548519721, 30774111529, 9450343721, 17436290517, 8846361045], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [4366847481, 1099617064443, 34431534593, 21546707457, 21548557, 21549581], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i33 : checks (tilesOf batches) 132 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 132 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 132 49 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤132) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [74176630833, 30908256585, 26395259209, 9316126025, 17385959905, 8762476001], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [105435641, 1099617064443, 4316513805, 21548557], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i36 : checks (tilesOf batches) 132 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 132 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 132 52 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤132) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [61409172533, 30690221417, 21982920041, 1100221044075, 13040664037, 4467510757], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [25841606145, 12956776961, 4316514829, 4772369], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i39 : checks (tilesOf batches) 132 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 132 47 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤132) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

namespace Top14
private abbrev P := PaidBatch orders 14

private def p0 : P :=
  ⟨unpack [48658556985, 22016403853, 17587290509, 1100070049167, 8728920561, 4417179121], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21479598609, 4771345, 4772369], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i42 : checks (tilesOf batches) 132 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 132 50 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=14)
    (hb : a.b≤132) (hj : a.j≤53) :
    Covered orders a ∨ Low6969Gate.Gated ((18 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i42 (i50)) a ha ht hb hj
end Top14

def receipt : Receipt 18 where
  orders := orders
  covers := by
    intro a ha box
    change 10+a.b≤142 ∧ 5+a.j≤58 ∧ 1+a.t≤15 at box
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
end Low6969Allocation.Group18
end Z6969Source2355

-- Source: ProximityPrize.SubmissionLower.Low6969Mass19
section Z6969Source2356
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6969Allocation.Group19

private def m0 : MassCell 19 :=
  ⟨⟨1,3,33⟩,mass_cell 19 1 3 33 238 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3154031017234, 2465535219460, 1865699891556, 1382633961924, 1000094488612, 703055926404, 477710126820, 311466338116, 192951205284, 112008770052, 59700470884, 28305142980, 11319018276, 3455725444, 646289892, 39133764, 9480, 0] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 19 :=
  ⟨⟨2,6,56⟩,mass_cell 19 2 6 56 205 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2126095182664, 1503194782440, 998376703900, 632142574776, 376670588220, 207220894504, 102135601020, 42838772280, 13836429916, 2716552680, 149076444, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 19 :=
  ⟨⟨1,9,65⟩,mass_cell 19 1 9 65 181 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1660670149479, 1042314756763, 603232592367, 317191104291, 145124776759, 53240788779, 13019014143, 1212021427, 1252439, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 19 :=
  ⟨⟨3,10,68⟩,mass_cell 19 3 10 68 177 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1709030237930, 1073298127105, 597034124425, 297458283745, 125774261065, 40534032385, 7637893705, 334596700, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 19 :=
  ⟨⟨2,12,71⟩,mass_cell 19 2 12 71 167 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1742943929099, 1117863078098, 588511776454, 269105756698, 98226960782, 23592209122, 2053200598, 943710, 0] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 19 :=
  ⟨⟨4,15,75⟩,mass_cell 19 4 15 75 156 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1753253317913, 1210186949351, 581653158112, 229358304464, 64218582976, 8447958448, 82890826, 0] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 19 :=
  ⟨⟨6,17,77⟩,mass_cell 19 6 17 77 151 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1753253317913, 1259414133832, 579529713448, 205931824624, 47115162680, 3620190208, 286125, 0] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 19 :=
  ⟨⟨1,21,79⟩,mass_cell 19 1 21 79 141 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1753253317913, 1307101105952, 577305907533, 171326411337, 24546490789, 306433165, 0] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 19 :=
  ⟨⟨4,22,80⟩,mass_cell 19 4 22 80 140 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1753253317913, 1330234086828, 585642952872, 164583144972, 21021065352, 157994160, 0] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 19 :=
  ⟨⟨5,24,81⟩,mass_cell 19 5 24 81 136 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1753253317913, 1350874561504, 588154436032, 148781846500, 14328236672, 14966617, 0] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 19 :=
  ⟨⟨2,27,82⟩,mass_cell 19 2 27 82 132 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1753253317913, 1370091320655, 593295431082, 129772000346, 7717652234, 0] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 19 :=
  ⟨⟨3,30,83⟩,mass_cell 19 3 30 83 129 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1753253317913, 1386377159941, 598509862500, 111129440520, 3811158740, 0] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 19 :=
  ⟨⟨9,33,84⟩,mass_cell 19 9 33 84 126 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1753253317913, 1399206343555, 605600979067, 93687650199, 1722099382, 0] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 19 :=
  ⟨⟨1,39,85⟩,mass_cell 19 1 39 85 121 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1753253317913, 1407144591225, 620522806632, 70454839656, 183914850, 0] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 19 :=
  ⟨⟨1,45,86⟩,mass_cell 19 1 45 86 118 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1753253317913, 1407144591225, 642644442297, 52428939117, 1359645] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 19 :=
  ⟨⟨12,52,87⟩,mass_cell 19 12 52 87 114 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1753253317913, 1407144591225, 659387082191, 36194986244, 0] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 19 :=
  ⟨⟨83,30,86⟩,mass_cell 19 83 30 86 132 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1753253317913, 1407144591225, 633769634848, 60287792706, 34881845, 0] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 19 :=
  ⟨⟨53,46,87⟩,mass_cell 19 53 46 87 118 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1753253317913, 1407144591225, 652878178075, 41843757540, 3283948] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 19 :=
  ⟨⟨99,24,86⟩,mass_cell 19 99 24 86 141 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1753253317913, 1407144591225, 643216195125, 51275561853, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 19 :=
  ⟨⟨79,41,87⟩,mass_cell 19 79 41 87 121 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1753253317913, 1407144591225, 650628601886, 43568162929, 44338955, 0] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 19 :=
  ⟨⟨104,34,87⟩,mass_cell 19 104 34 87 128 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1753253317913, 1407144591225, 654536261797, 39508073746, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 19 :=
  ⟨⟨98,50,88⟩,mass_cell 19 98 50 88 117 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1753253317913, 1407144591225, 668952320916, 26430156985, 27] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 19 :=
  ⟨⟨104,22,86⟩,mass_cell 19 104 22 86 146 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1753253317913, 1407144591225, 645808700772, 46791329517, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 19 :=
  ⟨⟨106,10,85⟩,mass_cell 19 106 10 85 194 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1753253317913, 1407144591225, 649492095490, 43952674583, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 19 :=
  ⟨⟨122,12,86⟩,mass_cell 19 122 12 86 182 (by decide)
    (by decide +kernel) [4491876614553, 3787639685465, 3168594377657, 2627652708729, 2158031688281, 1753253317913, 1407144591225, 665496305764, 29321828128, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 19) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24]

end Low6969Allocation.Group19
end Z6969Source2356
