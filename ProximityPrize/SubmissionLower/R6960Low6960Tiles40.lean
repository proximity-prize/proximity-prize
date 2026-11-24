import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Mass40

set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group40
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [23643950087, 23610401807, 27872934935, 14937708579, 10625968167, 23495275563], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [14871792691, 6265084983, 1953342523, 1936566331, 1886235711, 1852682303], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1819128895, 1768798275, 1735244867, 1701691459, 1651360839, 1634584647], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1601031239, 1567477835, 1099820814787, 1099804036551, 1099770481103, 1099753702867], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099720147419, 1099686591971, 1099653036523, 1099619481075, 1099585925627, 1099552370179], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [7186952], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i51 : checks (tilesOf batches) 130 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [27922143243, 27872932887, 19249451039, 10625967143, 23495274539, 14871791667], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [6265083959, 1953341499, 1936565307, 1903011899, 1835904063, 1802350655], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1768797247, 1718466627, 1684913219, 1651359811, 1601029191, 1567475783], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1550699591, 1500368971, 1099887923635, 1099854368187, 1099837589951, 1099804034503], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099770479055, 1099736923607, 1099703368159, 1099669812711, 1099636257263, 1099602701815], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099552369155, 7185928], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i46 : checks (tilesOf batches) 130 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [23610401807, 27872934935, 14937708579, 6331000871, 23495274539, 10576824371], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [6265082935, 1970117687, 1953341499, 1919788091, 1869457467, 1802349631], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1768796223, 1735242815, 1668134979, 1634581571, 1601028163, 1550697543], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1517144135, 1500367943, 1450037323, 1099938255271, 1099904699823, 1099887921587], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099854366139, 1099820810691, 1099787255243, 1099753699795, 1099703367135, 1099669811687], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099636256239, 1099585923579, 1099535590919], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i49 : checks (tilesOf batches) 130 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [32184676371, 19249451039, 10625967143, 23495274539, 10576824371, 6265082935], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1970117687, 1953341499, 1903010875, 1852680251, 1785572415, 1752019007], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1701688383, 1651357763, 1601027139, 1567473731, 1517143111, 1483589703], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1450036295, 1416482891, 1099971809695, 1099955031459, 1099921476011, 1099887920563], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099854365115, 1099820809667, 1099770477007, 1099736921559, 1099686588899, 1099653033451], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099602700791, 1099552368131], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
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
private theorem i52 : checks (tilesOf batches) 130 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (checks_join i44 (i52)))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [27872934935, 19232675875, 6331001895, 23495275563, 10576825395, 6265083959], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1953341499, 1903010875, 1852680251, 1785572415, 1735241791, 1684911167], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1634580547, 1584249923, 1550696515, 1500365895, 1466812487, 1433259079], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1382928459, 1100005364119, 1099971808671, 1099938253223, 1099904697775, 1099871142327], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099837586879, 1099787254219, 1099753698771, 1099703366111, 1099653033451, 1099602700791], by decide +kernel⟩
private def p5 : P :=
  ⟨unpack [1099552368131], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4, p5]
private theorem i15 : checks (tilesOf batches) 130 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 130 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 130 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 130 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 130 47 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [23561193499, 14937710627, 23495274539, 14871791667, 6265083959, 1953341499], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1903010875, 1852680251, 1785572415, 1735241791, 1684911167, 1617803331], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1584249923, 1533919299, 1483588679, 1450035271, 1416481863, 1366151243], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100022141331, 1099988585883, 1099955030435, 1099921474987, 1099887919539, 1099837586879], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099804031431, 1099753698771, 1099703366111, 1099653033451, 1099602700791, 1099552368131], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i18 : checks (tilesOf batches) 130 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 130 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 130 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 130 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 130 50 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [19249452063, 10625968167, 23495275563, 10576825395, 6265083959, 1953341499], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1919788091, 1852680251, 1785572415, 1735241791, 1684911167, 1617803331], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1567472707, 1533919299, 1466811463, 1433258055, 1399704647, 1349374027], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100038918543, 1100005363095, 1099971807647, 1099938252199, 1099887919539, 1099854364091], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099804031431, 1099753698771, 1099703366111, 1099653033451, 1099602700791, 1099535590919], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i21 : checks (tilesOf batches) 130 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 130 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 130 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 130 45 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [14937710627, 27790241835, 10576825395, 6265083959, 1953341499, 1936565307], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1869457467, 1802349631, 1752019007, 1684911167, 1617803331, 1584249923], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1533919299, 1466811463, 1433258055, 1382927431, 1332596811, 1100055695755], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1100022140307, 1099971807647, 1099938252199, 1099887919539, 1099837586879, 1099804031431], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099753698771, 1099686588899, 1099636256239, 1099585923579, 7185928], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i24 : checks (tilesOf batches) 130 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 130 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 130 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 130 48 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [10625969191, 23495276587, 10576826419, 6265084983, 1953342523, 1903011899], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1819126847, 1768796223, 1701688383, 1634580547, 1584249923, 1533919299], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1483588679, 1433258055, 1382927431, 1332596811, 1100055695755, 1100022140307], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099971807647, 1099921474987, 1099887919539, 1099837586879, 1099787254219, 1099736921559], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099669811687, 1099619479027, 1099552369155], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i27 : checks (tilesOf batches) 130 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 130 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 130 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 130 51 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [23495276587, 10576826419, 6265084983, 1953342523, 1919789115, 1835904063], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1785573439, 1718465599, 1651357763, 1601027139, 1550696515, 1483588679], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1433258055, 1399704647, 1332596811, 1100055695755, 1100005363095, 1099971807647], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099921474987, 1099871142327, 1099820809667, 1099770477007, 1099720144347, 1099653034475], by decide +kernel⟩
private def p4 : P :=
  ⟨unpack [1099602701815, 1099535591943], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3, p4]
private theorem i30 : checks (tilesOf batches) 130 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 130 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 130 46 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [19183535151, 10560051255, 1953342523, 1953343547, 1869458495, 1802350655], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1735242815, 1668134979, 1617804355, 1567473731, 1500365895, 1450035271], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1399704647, 1349374027, 1100038918543, 1100005363095, 1099955030435, 1099904697775], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099854365115, 1099804032455, 1099753699795, 1099703367135, 1099636257263, 1099569147391], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i33 : checks (tilesOf batches) 130 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 130 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 130 49 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [14871793715, 6248308795, 1953343547, 1886235711, 1819127871, 1768797247], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [1684912195, 1634581571, 1584250947, 1517143111, 1466812487, 1416481863], by decide +kernel⟩
private def p2 : P :=
  ⟨unpack [1349374027, 1100038918543, 1099988585883, 1099938253223, 1099887920563, 1099837587903], by decide +kernel⟩
private def p3 : P :=
  ⟨unpack [1099787255243, 1099736922583, 1099669812711, 1099619480051, 1099552370179], by decide +kernel⟩
private def batches : List P := [p0, p1, p2, p3]
private theorem i36 : checks (tilesOf batches) 130 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 130 44 8 = true := by
  decide +kernel
private theorem i52 : checks (tilesOf batches) 130 52 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤130) (hj : a.j≤52) :
    Covered orders a ∨ Low6960Gate.Gated ((40 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (checks_join i44 (i52))) a ha ht hb hj
end Top12

def receipt : Receipt 40 where
  orders := orders
  covers := by
    intro a ha box
    change 11+a.b≤141 ∧ 7+a.j≤59 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group40
