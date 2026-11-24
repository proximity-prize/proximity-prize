import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass20

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group20
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [2147552261, 15016464395, 6409756685, 2098014225, 1980574737, 1796026385], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1628255253, 1510815765, 1393376277, 1292714009, 1208828953, 1141721113], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1057836061, 1007505437, 957174813, 906844193, 856513569, 822960161], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [789406757, 755853349, 739077157, 688746537, 671970345, 36360321065], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [23425096757, 14801613885, 6178128965, 1883163717, 1866387529, 1832834121], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1816057929, 1765727309, 14196569293, 14179791057, 18441202905, 18424424669], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [22685836517, 22669058281, 22635502833, 26880137469, 26846582021, 26796249361], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [31040883997, 30973774125, 30906664253, 30822777169, 35033857381, 34916415873], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [34798974365, 34647978433, 34463428077, 1099582856695, 1099549301247, 1099532523011], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i3 : checks (tilesOf batches) 129 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 129 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 129 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 129 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 129 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 129 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 129 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [10721499145, 2114790413, 2098014225, 1980574737, 1796026385, 1611478037], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1477261333, 1376599061, 1259159577, 1175274521, 1091389465, 1024281629], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [957173789, 906843165, 856512545, 806181921, 772628513, 722297893], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [705521701, 671968293, 638414889, 621638697, 36360321065, 19130129461], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [10506645565, 6194904129, 1883161669, 1883162693, 1849609285, 1799278665], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1765725257, 1748949065, 1698618445, 14246900929, 14230122693, 14213344457], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [18474756305, 18457978069, 22719389917, 22685834469, 22635501809, 26896913657], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [26846580997, 26779471125, 31024105761, 30940218677, 30856331593, 30755667297], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [34949970297, 34815751577, 34647978433, 1099649965543, 34463428077, 1099616410095], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099599631859, 1099566076411, 1099532520963], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i6 : checks (tilesOf batches) 129 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 129 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 129 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 129 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 129 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 129 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 129 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (checks_join i46 (i54))))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [2114790413, 2098014225, 1997351953, 1812803601, 1628255253, 1477261333], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1359821845, 1242382361, 1158497305, 1091389465, 1007504413, 940396573], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [890065949, 822958113, 789404705, 739074081, 688743461, 655190053], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [638413861, 588083241, 571307049, 32065353769, 19130128437, 10506644541], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [6194903105, 1899937857, 1866384453, 1832831045, 1799277637, 1748947017], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1715393609, 1698617417, 1648286797, 10002265269, 14280454329, 14246898881], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [18525087941, 18491532493, 18457977045, 22702611681, 22669056233, 22618723573], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [26863358209, 26796248337, 26729138465, 30956995889, 30873108805, 30772444509], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [34949970297, 34798974365, 34631201221, 1099700297179, 1099666741731, 1099649963495], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099616408047, 34446650865, 1099582852599, 1099549297151, 4113924], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i9 : checks (tilesOf batches) 129 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 129 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 129 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 129 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 129 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 129 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [1829580817, 1645032469, 1494038549, 1376599061, 1259159577, 1158497305], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1091389465, 990727197, 940396573, 873288733, 806180897, 772627489], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [722296865, 671966245, 638412837, 604859429, 571306025, 537752617], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [32065353769, 19130128437, 10506644541, 1899935809, 1899936833, 1883160641], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1816052805, 1782499397, 1748945989, 1698615369, 1681839177, 1648285769], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1597955149, 10035819693, 14297231541, 14280453305, 14246897857, 18508309705], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [18474754257, 22719388893, 22685833445, 22635500785, 26863358209, 26813025549], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [26729138465, 30956995889, 30856331593, 30755667297, 30638225789, 34782197153], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [34614424009, 1099750628815, 1099717073367, 1099683517919, 1099666739683, 1099633184235], by decide +kernel⟩
private def p9 : P :=
  ⟨unpack [1099599628787, 1099566073339, 4112900], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
private theorem i12 : checks (tilesOf batches) 129 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 129 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 129 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 129 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [1393376277, 1275936793, 1175274521, 1091389465, 1007504413, 940396573], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [873288733, 806180897, 755850273, 722296865, 655189029, 621635621], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [588082213, 554528809, 520975401, 32065353769, 19130128437, 6211677245], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1916711997, 1899935809, 1883159617, 1849606209, 1799275589, 1748944965], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1715391557, 1665060937, 1631507529, 1614731337, 1564400717, 10052596905], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [14314008753, 14297230517, 14263675069, 18525086917, 18474754257, 22736166105], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [22685833445, 22635500785, 26863358209, 26796248337, 26729138465, 30940218677], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [30839554381, 30738890085, 1099784183239, 1099750627791, 1099733849555, 1099700294107], by decide +kernel⟩
private def p8 : P :=
  ⟨unpack [1099666738659, 1099633183211, 1099582850551, 1099549295103, 4111876], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7, p8]
private theorem i15 : checks (tilesOf batches) 129 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 129 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 129 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 129 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (checks_join i47 (i55)))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [1108166681, 1007504413, 940396573, 890065949, 806180897, 755850273], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [722296865, 655189029, 621635621, 588082213, 537751593, 504198185], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [32065353769, 14835161141, 10523420729, 1916711997, 1899935809, 1866382401], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1816051777, 1765721157, 1732167749, 1698614341, 1648283721, 1614730313], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1581176905, 1530846285, 10069374117, 14330785965, 14297230517, 14263675069], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [18525086917, 18474754257, 22736166105, 22685833445, 22618723573, 26863358209], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [26796248337, 26712361253, 1099817737663, 1099784182215, 1099750626767, 1099717071319], by decide +kernel⟩
private def p7 : P :=
  ⟨unpack [1099683515871, 1099649960423, 1099616404975, 1099582849527, 1099532516867], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6, p7]
private theorem i18 : checks (tilesOf batches) 129 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 129 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 129 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 129 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 129 50 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [890065949, 822958113, 772627489, 722296865, 671966245, 621635621], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [588082213, 537751593, 504198185, 32065353769, 14835161141, 6228453433], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [6211678269, 1899935809, 1849605185, 1799274561, 1748943941, 1715390533], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1665059909, 1614729289, 1581175881, 1547622473, 1497291853, 10069374117], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [14330785965, 14297230517, 14263675069, 18508309705, 18474754257, 22719388893], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [22669056233, 26913690869, 1099851292087, 1099817736639, 1099784181191, 1099750625743], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [1099717070295, 1099666737635, 1099633182187, 1099599626739, 1099549294079], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i21 : checks (tilesOf batches) 129 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 129 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 129 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 129 45 8 = true := by
  decide +kernel
private theorem i53 : checks (tilesOf batches) 129 53 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (checks_join i45 (i53))))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [739074081, 671966245, 638412837, 588082213, 537751593, 504198185], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [32065353769, 14835161141, 6228453433, 1916710973, 1916711997, 1883158593], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1849605185, 1799274561, 1732166725, 1698613317, 1665059909, 1597952073], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1564398665, 1530845257, 1480514637, 10069374117, 14330785965, 14297230517], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [18541865153, 18508309705, 18457977045, 1099868069299, 1099834513851, 1099800958403], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099767402955, 1099717070295, 1099683514847, 1099649959399, 1099599626739, 1099549294079], by decide +kernel⟩
private def p6 : P :=
  ⟨unpack [4110852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5, p6]
private theorem i24 : checks (tilesOf batches) 129 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 129 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 129 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 129 48 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [604859429, 554528809, 520975401, 32065353769, 14835161141, 6228453433], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1916710973, 1916711997, 1883158593, 1832827969, 1799274561, 1732166725], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1681836101, 1648282693, 1597952073, 1564398665, 1514068041, 1463737421], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [10052596905, 14314008753, 14280453305, 1099884846511, 1099851291063, 1099800958403], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099767402955, 1099733847507, 1099700292059, 1099649959399, 1099599626739, 1099566071291], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [4110852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i27 : checks (tilesOf batches) 129 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 129 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 129 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 129 51 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [32065353769, 14835161141, 6228453433, 1916710973, 1916711997, 1883158593], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1832827969, 1782497345, 1732166725, 1681836101, 1648282693, 1581174857], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1547621449, 1514068041, 1463737421, 1099884846511, 1099851291063, 1099817735615], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099784180167, 1099733847507, 1099700292059, 1099649959399, 1099616403951, 1099566071291], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [4110852], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 129 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 129 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 129 46 8 = true := by
  decide +kernel
private theorem i54 : checks (tilesOf batches) 129 54 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (checks_join i46 (i54)))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [27753612333, 10523418681, 6211677245, 1916711997, 1899935809, 1849605185], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1799274561, 1732166725, 1681836101, 1648282693, 1581174857, 1547621449], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1514068041, 1446960205, 1099901623723, 1099851291063, 1099817735615, 1099784180167], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099733847507, 1099700292059, 1099649959399, 1099599626739, 1099549294079], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 129 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 129 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 129 49 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [19146903601, 10523419705, 6211678269, 1899935809, 1849605185, 1799274561], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1732166725, 1681836101, 1648282693, 1581174857, 1547621449, 1497290825], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1446960205, 1099901623723, 1099868068275, 1099817735615, 1099784180167, 1099733847507], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099700292059, 1099649959399, 1099599626739, 1099549294079], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 129 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 129 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 129 52 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

namespace Top13
private abbrev P := PaidBatch orders 13

private def p0 : P :=
  ⟨unpack [14835162165, 6211677245, 1916711997, 1899935809, 1849605185, 1799274561], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1732166725, 1698613317, 1648282693, 1581174857, 1547621449, 1497290825], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1446960205, 1099901623723, 1099868068275, 1099817735615, 1099784180167, 1099733847507], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099683514847, 1099649959399, 1099599626739, 1099549294079], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i39 : checks (tilesOf batches) 129 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 129 47 8 = true := by
  decide +kernel
private theorem i55 : checks (tilesOf batches) 129 55 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=13)
    (hb : a.b≤129) (hj : a.j≤55) :
    Covered orders a ∨ Low6960Gate.Gated ((20 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i39 (checks_join i47 (i55))) a ha ht hb hj
end Top13

def receipt : Receipt 20 where
  orders := orders
  covers := by
    intro a ha box
    change 12+a.b≤141 ∧ 4+a.j≤59 ∧ 1+a.t≤14 at box
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
end Low6960Allocation.Group20
