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
  ⟨unpack [2164329477, 989925385, 10100347915, 23607255053, 52985149461, 121202043941], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [14028771577, 39614639369, 47919502601, 26562249993, 43590760817, 35000968561], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [26109187501, 17502548397, 8795178441, 8744915401, 1099784052171, 25874303473], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4349284849, 1099616279027, 12939145725, 8644248061, 54316541, 8627398145], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [37540353, 1099549169155], by decide +kernel⟩
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
private theorem i51 : checks (tilesOf batches) 130 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤130) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [14949488651, 31979546641, 65685833753, 91254917169, 39279233329, 39111536945], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [5003532593, 43708205385, 30873777481, 13274689953, 13157253537, 4617720225], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [21730334153, 8862281161, 43137837533, 1099700165087, 1099700166111, 4416324069], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4382837221, 1099616276979, 1099616278003, 12955621881, 54315517, 1099565944319], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [30102083073, 4332435969, 4315726341, 21478741513], by decide +kernel⟩
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
private theorem i46 : checks (tilesOf batches) 130 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 130 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤130) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27751425037, 48791044121, 116789702697, 39597863153, 43641313521, 26528695537], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [43473387917, 30588628365, 17653471641, 13291466137, 8946171289, 8778402217], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8744916393, 1099750495699, 1099750496723, 1099750497747, 8811875797, 1099716938203], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099716939227, 1099716940251, 25907635689, 4349214193, 104646129, 8644177405], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4332435965, 37536257, 3914248, 3980808], by decide +kernel⟩
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
private theorem i49 : checks (tilesOf batches) 130 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤130) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36241289233, 65652479005, 78353306677, 30672524593, 30504826161, 9164281137], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39413241157, 26562035013, 13157250461, 8811955613, 1099968598431, 1099834381759], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099834382783, 1099834383807, 17435367877, 8862281157, 43171394005, 1099733648855], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733715415, 1099733716439, 4416322017, 1099683316195, 34413829629, 37468673], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [37469697, 25790415365, 12905586181, 4298878473, 3913224], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
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
private theorem i52 : checks (tilesOf batches) 130 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤130) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [40469478421, 69846918181, 56995981369, 35185452341, 26528549173, 22099436853], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21847850321, 8979731793, 8778399149, 1099901421999, 1099901488559, 1099901489583], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099884713395, 1099884714419, 1099884715443, 43221794249, 8845501901, 8761618893], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700092383, 1099700093407, 1099700159967, 21596113389, 121348589, 4365988345], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [71023097, 30118930941], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 130 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 130 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 130 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 130 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤130) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [48791177241, 86825662505, 18576231493, 35202300169, 34950716681, 9399157001], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39178422669, 30588629389, 1100002086295, 1100002152855, 1100002153879, 1100002154903], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1100002155927, 13324950937, 13190802841, 1099985304987, 1099767202255, 1099767203279], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099767269839, 17401811413, 4449873381, 4382766565, 54244861, 1099565873663], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4315653637], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 130 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 130 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 130 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 130 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 130 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤130) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [52985680925, 78252574769, 10036696137, 35034597653, 30571932949, 5003529493], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39245534585, 26360774009, 13207580049, 8845507985, 1100018862483, 1099935045031], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099935046055, 1099935047079, 13224286649, 8895834553, 1099817602499, 1099817603523], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099750424019, 1099750425043, 1099750426067, 4382766561, 71022073, 1099582650875], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4315654661, 20689413, 38658463241, 25773637129], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 130 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 130 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 130 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 130 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 130 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤130) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [65602281505, 65401299001, 26360848677, 30421007653, 1100438297895, 35219005757], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26511770941, 13140475261, 8778403197, 1100102818175, 1099901488559, 1099901489583], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099901490607, 13190799797, 8811950517, 1099834310079, 1099834311103, 1099834312127], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099834313151, 4365988333, 1099632982511, 21579335153, 12989472241, 4332432897], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [37467649, 1099532393991], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 130 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 130 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 130 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 130 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤130) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [61340937253, 56878540857, 26226633013, 21814297909, 1100354411831, 30873775433], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26377555273, 8778401161, 1100052418955, 1100052485515, 1100052486539, 8962943397], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8828728741, 1099934974375, 1099851089339, 1099851090363, 1099851156923, 17368255965], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8778392029, 171685345, 1099683314147, 1099683315171, 4332432897, 1099532393987], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56840], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 130 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤130) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [69780011049, 35554769985, 30890555689, 26377558313, 13509506345, 13157254497], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100220192099, 1100220258659, 1100203482467, 1099934975399, 1099934976423, 1099934977447], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099935044007, 13207509437, 8862280125, 4500207041, 1099817532867, 1099817533891], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [25874299377, 104568305, 87799285, 1099599428087, 4332431873, 37466625], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56840], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 130 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤130) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [65501889581, 26998391877, 26578879793, 26310517041, 13442465073, 8811957613], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100169927023, 1100136373615, 1099934977447, 1099935044007, 1099935045031, 13190799797], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [8811950517, 1099851087291, 1099851088315, 1099851089339, 1099851090363, 4382765549], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099632982511, 21562557941, 12972695029, 4332432897, 20690437, 56836], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [56840], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤130) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [61190148145, 18475568197, 26444665137, 21981998385, 9147499825, 1100102750591], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100102817151, 1100102818175, 1100069264767, 8895835565, 4550539693, 1099901419951], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099851089339, 1099851090363, 1099851156923, 17401811413, 8811947477, 1099632982511], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099632983535, 4332433913, 20689413, 20690437, 56836, 56840], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 130 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤130) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [69629156405, 26461445393, 22015555857, 13392138513, 1100035641743, 1100035708303], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100035709327, 1100002155919, 8862284181, 1100002084247, 1100002085271, 1100002086295], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [13207510457, 8845503929, 1099716868571, 1099716869595, 1099716870619, 4365987321], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [71022073, 56836, 12888808969, 56840], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 130 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤130) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((8 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 8 where
  orders := orders
  covers := by
    intro a ha box
    change 8+a.b≤138 ∧ 3+a.j≤58 ∧ 1+a.t≤14 at box
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
