import ProximityPrize.SubmissionLower.R6961Low6961AllocTiles
import ProximityPrize.SubmissionLower.R6961Low6961Mass1

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6961Allocation.Group1
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2181106693, 1040257033, 4966192137, 19026484237, 57061617681, 87043434533], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [23172987969, 31543399597, 35402617093, 43808470329, 39513776441, 39312591161], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [34933879097, 13190607301, 25991547353, 17401685465, 8795046361, 4483304921], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [38708384257, 42969938441, 38675047945, 20565513, 20566537, 4298752525], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4298754573], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i3 : checks (tilesOf batches) 131 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 131 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 131 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 131 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 131 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 131 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 131 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤131) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10536753163, 27633787917, 61390536729, 86993239085, 1798885449, 30940757301], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [34950585653, 17854677301, 43724718409, 35151768905, 21730205125, 13106722245], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [43221460429, 4483302873, 4416196057, 38859381213, 1099599302139, 1099599303163], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [8660825597, 4365861373, 38691820037, 17217134085, 8627270149, 30085184009], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17200355849, 20564489], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i6 : checks (tilesOf batches) 131 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 131 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 131 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 131 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 131 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 131 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤131) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [27633787917, 57145901081, 86942906409, 6026742853, 30957467941, 30773057829], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26377500965, 39429751125, 35084659029, 13106788793, 8761493945, 43221460429], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17435236817, 8845307345, 1099683187175, 1099683188199, 1099683189223, 4416190961], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4365861361, 21545651709, 34396924421, 37339653, 1099548968455], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i9 : checks (tilesOf batches) 131 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 131 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 131 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 131 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 131 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 131 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤131) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [36190760977, 74107999261, 57096444981, 39547262245, 30890360101, 21998574949], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [21847651685, 4802071909, 8794977729, 4516856257, 4449749441, 43238240713], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099699966435, 13056384485, 8727866853, 1099666409963, 1099666410987, 25907658221], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [17301019117, 4365859317, 1099599299067, 1099599300091, 34430410237, 8610491913], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [20560393, 20561417, 12888611341], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i12 : checks (tilesOf batches) 131 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 131 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 131 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 131 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 131 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 131 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤131) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [40435727381, 82580694053, 31494485053, 35336250641, 35084732689, 39144959249], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13291269513, 13140344213, 4567190933, 43271863745, 21780466113, 13173825985], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4432969173, 1099750294999, 1099750296023, 1099733519835, 1099733520859, 4432966125], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4365859309, 1099599299067, 30135446013, 54114817, 1099565743619, 8610423305], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4315524617, 21478541837], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i15 : checks (tilesOf batches) 131 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 131 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 131 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 131 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 131 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤131) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [52985350169, 86791912493, 1631113289, 35168550149, 34967363845, 13610042629], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [39295601013, 30689096053, 13324820889, 13157052825, 8828600729, 1099884514743], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [17451946441, 1099767075283, 1099750293975, 1099750294999, 1099750296023, 4466455005], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4416190941, 70892029, 1099582520831, 8627201541, 4315525641, 30068404749], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [17183576589], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 131 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 131 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 131 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 131 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 131 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤131) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [61374092317, 69746397233, 30705946921, 22048977193, 9180858665, 35185186121], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [26595457353, 8811753909, 4516855221, 1099884512695, 1099867736507, 1099867737531], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099867738555, 17452012997, 8845306309, 4365858285, 1099649629679, 1099649630703], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [54113793, 1099565742595, 4332235269, 4315525637, 12905387529, 4315457033], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [3781133], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 131 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 131 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 131 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 131 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤131) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [69813166113, 48422626361, 35285917993, 30772987177, 21948310869, 17519131989], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1100287168855, 8761490857, 1099934845355, 1099934846379, 8862082505, 4516786633], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4466522569, 21713356245, 13106716117, 1099750293975, 1099750294999, 1099616074231], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099616075255, 4332302849, 34380079625, 8593645069, 4298680845, 3781133], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [3782157], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 131 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 131 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 131 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 131 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤131) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [74041158693, 31393821757, 31024508189, 26545130781, 30538180893, 8828602749], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13240936849, 8862087569, 8778270097, 1099867738555, 1099834181059, 1099834182083], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099834183107, 4416190933, 1099750293975, 17401613785, 8811749849, 4432899561], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [154777065, 1099616074231, 1099616075255, 30101958149, 4298747405], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i27 : checks (tilesOf batches) 131 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 131 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 131 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 131 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤131) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [74007672873, 18592809025, 26779941145, 30722725145, 26260059417, 8895640977], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8795046293, 1100018732439, 1100018733463, 17502344633, 8878860729, 1099800625611], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099800626635, 1099800627659, 4416189917, 1099716738527, 70891005, 1099582519807], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [4349012481, 54112769, 12905387529, 4315457033, 25773439501], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i30 : checks (tilesOf batches) 131 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 131 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 131 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤131) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [69729551405, 10086828101, 30823318817, 26327098657, 17670127905, 8778269081], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [13190604201, 8794977705, 1099918069167, 1099918070191, 1099800625611, 1099800626635], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099800627659, 21696579033, 13089938905, 4416189917, 1099716738527, 4382567925], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [70891005, 1099582519807, 8593645069, 4298680845, 3781133], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 131 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 131 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 131 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤131) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [69679288369, 26528354585, 26327166233, 9197635865, 8929193377, 8794978721], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099968398755, 1099918068143, 1099918069167, 1099918070191, 17435234769, 8845305297], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [4416190933, 1099750293975, 4382634485, 1099616074231, 1099616075255, 3781133], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [3782157], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 131 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 131 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 131 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤131) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [56911895605, 22116015417, 21897983289, 4835626297, 8845309345, 4533633441], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1099968399779, 1099850960319, 1099850961343, 13123493333, 4533562837, 1099716739551], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1099716740575, 4416189921, 1099699961315, 54113793, 1099565742595], by decide +kernel⟩
private def batches : List P := [p0, p1, p2]
private theorem i39 : checks (tilesOf batches) 131 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 131 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤131) (hj : a.j≤52) : Covered orders a :=
  cover_at (batches:=batches) (checks_join i39 (i47)) a ha ht hb hj
end Top13

def receipt : Receipt 1 where
  orders := orders
  covers := by
    intro a ha box
    change 1+a.b≤132 ∧ 3+a.j≤55 ∧ 1+a.t≤14 at box
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
end Low6961Allocation.Group1
