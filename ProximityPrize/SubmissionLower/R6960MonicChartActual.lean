import ProximityPrize.SubmissionLower.R6960Low6960AllocTotal
import ProximityPrize.SubmissionLower.R6960Low6960Gates
import ProximityPrize.SubmissionLower.R6960Low6960CountCore
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0
import ProximityPrize.SubmissionLower.R6960Low6960Tiles1
import ProximityPrize.SubmissionLower.R6960Low6960Tiles2
import ProximityPrize.SubmissionLower.R6960Low6960Tiles3
import ProximityPrize.SubmissionLower.R6960Low6960Tiles4
import ProximityPrize.SubmissionLower.R6960Low6960Tiles5
import ProximityPrize.SubmissionLower.R6960Low6960Tiles6
import ProximityPrize.SubmissionLower.R6960Low6960Tiles7
import ProximityPrize.SubmissionLower.R6960Low6960Tiles8
import ProximityPrize.SubmissionLower.R6960Low6960Tiles9
import ProximityPrize.SubmissionLower.R6960Low6960Tiles10
import ProximityPrize.SubmissionLower.R6960Low6960Tiles11
import ProximityPrize.SubmissionLower.R6960Low6960Tiles12
import ProximityPrize.SubmissionLower.R6960Low6960Tiles13
import ProximityPrize.SubmissionLower.R6960Low6960Tiles14
import ProximityPrize.SubmissionLower.R6960Low6960Tiles15
import ProximityPrize.SubmissionLower.R6960Low6960Tiles16
import ProximityPrize.SubmissionLower.R6960Low6960Tiles17
import ProximityPrize.SubmissionLower.R6960Low6960Tiles18
import ProximityPrize.SubmissionLower.R6960Low6960Tiles19
import ProximityPrize.SubmissionLower.R6960Low6960Tiles20
import ProximityPrize.SubmissionLower.R6960Low6960Tiles21
import ProximityPrize.SubmissionLower.R6960Low6960Tiles22
import ProximityPrize.SubmissionLower.R6960Low6960Tiles23
import ProximityPrize.SubmissionLower.R6960Low6960Tiles24
import ProximityPrize.SubmissionLower.R6960Low6960Tiles25
import ProximityPrize.SubmissionLower.R6960Low6960Tiles26
import ProximityPrize.SubmissionLower.R6960Low6960Tiles27
import ProximityPrize.SubmissionLower.R6960Low6960Tiles28
import ProximityPrize.SubmissionLower.R6960Low6960Tiles29
import ProximityPrize.SubmissionLower.R6960Low6960Tiles30
import ProximityPrize.SubmissionLower.R6960Low6960Tiles31
import ProximityPrize.SubmissionLower.R6960Low6960Tiles32
import ProximityPrize.SubmissionLower.R6960Low6960Tiles33
import ProximityPrize.SubmissionLower.R6960Low6960Tiles34
import ProximityPrize.SubmissionLower.R6960Low6960Tiles35
import ProximityPrize.SubmissionLower.R6960Low6960Tiles36
import ProximityPrize.SubmissionLower.R6960Low6960Tiles37
import ProximityPrize.SubmissionLower.R6960Low6960Tiles38
import ProximityPrize.SubmissionLower.R6960Low6960Tiles39
import ProximityPrize.SubmissionLower.R6960Low6960Tiles40
import ProximityPrize.SubmissionLower.R6960Low6960Tiles41
import ProximityPrize.SubmissionLower.R6960Low6960Tiles42
import ProximityPrize.SubmissionLower.R6960Front6960List
import ProximityPrize.SubmissionLower.R6960MarkedEvaluationLedger
import ProximityPrize.SubmissionLower.R6960Front6960Rank2
import ProximityPrize.SubmissionLower.R6960Front6960Rank3
import ProximityPrize.SubmissionLower.R6960Front6960Rank4
import ProximityPrize.SubmissionLower.R6960Front6960Rank5
import ProximityPrize.SubmissionLower.R6960RetainedCompressionPureNodes
import ProximityPrize.SubmissionLower.R6960RetainedCompressionDiscriminant
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.AdjoinRoot
import ProximityPrize.SubmissionLower.R6960MonicChartInfinityRing
import ProximityPrize.SubmissionLower.R6960ChartIntegrality
import Mathlib.LinearAlgebra.Basis.SMul

-- merged module R6960Low6960Tiles43
section Merged_R6960Low6960Tiles43
set_option Elab.async false
set_option maxRecDepth 22000
set_option maxHeartbeats 6000000

namespace Low6960Allocation.Group43
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (checks checks_join)

namespace Top1
private abbrev P := PaidBatch orders 1

private def p0 : P :=
  ⟨unpack [36513319943, 58006319123, 87450675239, 19201113155, 56412891547, 43494515099], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [38762909195, 55875876379, 38679454239], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i3 : checks (tilesOf batches) 136 3 8 = true := by
  decide +kernel
private theorem i11 : checks (tilesOf batches) 136 11 8 = true := by
  decide +kernel
private theorem i19 : checks (tilesOf batches) 136 19 8 = true := by
  decide +kernel
private theorem i27 : checks (tilesOf batches) 136 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 136 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 136 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 136 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=1)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((43 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i3 (checks_join i11 (checks_join i19 (checks_join i27 (checks_join i35 (checks_join i43 (i51))))))) a ha ht hb hj
end Top1

namespace Top2
private abbrev P := PaidBatch orders 2

private def p0 : P :=
  ⟨unpack [45204707339, 57956123675, 87282973743, 47923625339, 30777388411, 712691067], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [55892723223, 47269379615], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i6 : checks (tilesOf batches) 136 6 8 = true := by
  decide +kernel
private theorem i14 : checks (tilesOf batches) 136 14 8 = true := by
  decide +kernel
private theorem i22 : checks (tilesOf batches) 136 22 8 = true := by
  decide +kernel
private theorem i30 : checks (tilesOf batches) 136 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 136 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 136 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=2)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((43 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i6 (checks_join i14 (checks_join i22 (checks_join i30 (checks_join i38 (i46)))))) a ha ht hb hj
end Top2

namespace Top3
private abbrev P := PaidBatch orders 3

private def p0 : P :=
  ⟨unpack [53694374927, 61999568931, 61697791031, 34854245807, 21969418671, 51815864803], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [38931107299, 51614393875], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i9 : checks (tilesOf batches) 136 9 8 = true := by
  decide +kernel
private theorem i17 : checks (tilesOf batches) 136 17 8 = true := by
  decide +kernel
private theorem i25 : checks (tilesOf batches) 136 25 8 = true := by
  decide +kernel
private theorem i33 : checks (tilesOf batches) 136 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 136 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 136 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=3)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((43 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i9 (checks_join i17 (checks_join i25 (checks_join i33 (checks_join i41 (i49)))))) a ha ht hb hj
end Top3

namespace Top4
private abbrev P := PaidBatch orders 4

private def p0 : P :=
  ⟨unpack [57905655827, 66059724839, 40390731835, 47739070895, 30559279535, 17489902043], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [310037979, 55976538627], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i12 : checks (tilesOf batches) 136 12 8 = true := by
  decide +kernel
private theorem i20 : checks (tilesOf batches) 136 20 8 = true := by
  decide +kernel
private theorem i28 : checks (tilesOf batches) 136 28 8 = true := by
  decide +kernel
private theorem i36 : checks (tilesOf batches) 136 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 136 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=4)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((43 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i12 (checks_join i20 (checks_join i28 (checks_join i36 (i44))))) a ha ht hb hj
end Top4

namespace Top5
private abbrev P := PaidBatch orders 5

private def p0 : P :=
  ⟨unpack [57905724439, 65959130155, 27589719103, 43511215515, 26348200347, 13094272499], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [209374707, 51664797191, 43075006983, 25777774115], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i15 : checks (tilesOf batches) 136 15 8 = true := by
  decide +kernel
private theorem i23 : checks (tilesOf batches) 136 23 8 = true := by
  decide +kernel
private theorem i31 : checks (tilesOf batches) 136 31 8 = true := by
  decide +kernel
private theorem i39 : checks (tilesOf batches) 136 39 8 = true := by
  decide +kernel
private theorem i47 : checks (tilesOf batches) 136 47 5 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=5)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((43 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i15 (checks_join i23 (checks_join i31 (checks_join i39 (i47))))) a ha ht hb hj
end Top5

namespace Top6
private abbrev P := PaidBatch orders 6

private def p0 : P :=
  ⟨unpack [57889081371, 65824915503, 14855880771, 39350534527, 22153898367, 51664865799], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [38780108295, 8631534107, 41602587, 21482875427], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i18 : checks (tilesOf batches) 136 18 8 = true := by
  decide +kernel
private theorem i26 : checks (tilesOf batches) 136 26 8 = true := by
  decide +kernel
private theorem i34 : checks (tilesOf batches) 136 34 8 = true := by
  decide +kernel
private theorem i42 : checks (tilesOf batches) 136 42 8 = true := by
  decide +kernel
private theorem i50 : checks (tilesOf batches) 136 50 2 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=6)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((43 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i18 (checks_join i26 (checks_join i34 (checks_join i42 (i50))))) a ha ht hb hj
end Top6

namespace Top7
private abbrev P := PaidBatch orders 7

private def p0 : P :=
  ⟨unpack [53711623199, 57318869043, 14822326339, 34954906007, 21986127255, 17255018003], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8665088531, 75157011], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i21 : checks (tilesOf batches) 136 21 8 = true := by
  decide +kernel
private theorem i29 : checks (tilesOf batches) 136 29 8 = true := by
  decide +kernel
private theorem i37 : checks (tilesOf batches) 136 37 8 = true := by
  decide +kernel
private theorem i45 : checks (tilesOf batches) 136 45 7 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=7)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((43 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i21 (checks_join i29 (checks_join i37 (i45)))) a ha ht hb hj
end Top7

namespace Top8
private abbrev P := PaidBatch orders 8

private def p0 : P :=
  ⟨unpack [53611028515, 57201497143, 2004536391, 30760605055, 17825445247, 4990880127], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [47319638547, 30139847187, 12926498331, 4336567835], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i24 : checks (tilesOf batches) 136 24 8 = true := by
  decide +kernel
private theorem i32 : checks (tilesOf batches) 136 32 8 = true := by
  decide +kernel
private theorem i40 : checks (tilesOf batches) 136 40 8 = true := by
  decide +kernel
private theorem i48 : checks (tilesOf batches) 136 48 4 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=8)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((43 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i24 (checks_join i32 (checks_join i40 (i48)))) a ha ht hb hj
end Top8

namespace Top9
private abbrev P := PaidBatch orders 9

private def p0 : P :=
  ⟨unpack [53460036647, 48661897275, 26348200335, 13463371151, 628805007, 47437082099], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [25979100659, 12926499355, 4336568859, 42957565475, 25777773091], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i27 : checks (tilesOf batches) 136 27 8 = true := by
  decide +kernel
private theorem i35 : checks (tilesOf batches) 136 35 8 = true := by
  decide +kernel
private theorem i43 : checks (tilesOf batches) 136 43 8 = true := by
  decide +kernel
private theorem i51 : checks (tilesOf batches) 136 51 1 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=9)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((43 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i27 (checks_join i35 (checks_join i43 (i51)))) a ha ht hb hj
end Top9

namespace Top10
private abbrev P := PaidBatch orders 10

private def p0 : P :=
  ⟨unpack [49198692395, 40189405243, 21952571819, 13278822827, 43108628991, 21633803775], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [8698642955, 108711435, 8614755871], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i30 : checks (tilesOf batches) 136 30 8 = true := by
  decide +kernel
private theorem i38 : checks (tilesOf batches) 136 38 8 = true := by
  decide +kernel
private theorem i46 : checks (tilesOf batches) 136 46 6 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=10)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((43 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i30 (checks_join i38 (i46))) a ha ht hb hj
end Top10

namespace Top11
private abbrev P := PaidBatch orders 11

private def p0 : P :=
  ⟨unpack [53191672879, 23210866755, 39098877371, 21885529531, 8816084451, 4336567835], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [41602587, 17204686367, 8614756895], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i33 : checks (tilesOf batches) 136 33 8 = true := by
  decide +kernel
private theorem i41 : checks (tilesOf batches) 136 41 8 = true := by
  decide +kernel
private theorem i49 : checks (tilesOf batches) 136 49 3 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=11)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((43 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i33 (checks_join i41 (i49))) a ha ht hb hj
end Top11

namespace Top12
private abbrev P := PaidBatch orders 12

private def p0 : P :=
  ⟨unpack [53074300979, 10560914503, 34887799203, 17708004771, 4319791647, 30072738339], by decide +kernel⟩
private def p1 : P :=
  ⟨unpack [17187910179, 4303013411], by decide +kernel⟩
private def batches : List P := [p0, p1]
private theorem i36 : checks (tilesOf batches) 136 36 8 = true := by
  decide +kernel
private theorem i44 : checks (tilesOf batches) 136 44 8 = true := by
  decide +kernel
theorem exact (a : Shape) (ha : Valid a) (ht : a.t=12)
    (hb : a.b≤136) (hj : a.j≤51) :
    Covered orders a ∨ Low6960Gate.Gated ((43 : Band).val) a :=
  cover_at (batches:=batches) (checks_join i36 (i44)) a ha ht hb hj
end Top12

def receipt : Receipt 43 where
  orders := orders
  covers := by
    intro a ha box
    change 5+a.b≤141 ∧ 8+a.j≤59 ∧ 2+a.t≤14 at box
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
end Low6960Allocation.Group43
end Merged_R6960Low6960Tiles43

-- merged module R6960Low6960Count
section Merged_R6960Low6960Count

set_option Elab.async false

namespace Lower6960.Low
open Low6960Allocation (Band Receipt Gates bandOrders)

private def receipts : ∀ k : Band, Receipt k
  | ⟨0,_⟩ => Low6960Allocation.Group0.receipt
  | ⟨1,_⟩ => Low6960Allocation.Group1.receipt
  | ⟨2,_⟩ => Low6960Allocation.Group2.receipt
  | ⟨3,_⟩ => Low6960Allocation.Group3.receipt
  | ⟨4,_⟩ => Low6960Allocation.Group4.receipt
  | ⟨5,_⟩ => Low6960Allocation.Group5.receipt
  | ⟨6,_⟩ => Low6960Allocation.Group6.receipt
  | ⟨7,_⟩ => Low6960Allocation.Group7.receipt
  | ⟨8,_⟩ => Low6960Allocation.Group8.receipt
  | ⟨9,_⟩ => Low6960Allocation.Group9.receipt
  | ⟨10,_⟩ => Low6960Allocation.Group10.receipt
  | ⟨11,_⟩ => Low6960Allocation.Group11.receipt
  | ⟨12,_⟩ => Low6960Allocation.Group12.receipt
  | ⟨13,_⟩ => Low6960Allocation.Group13.receipt
  | ⟨14,_⟩ => Low6960Allocation.Group14.receipt
  | ⟨15,_⟩ => Low6960Allocation.Group15.receipt
  | ⟨16,_⟩ => Low6960Allocation.Group16.receipt
  | ⟨17,_⟩ => Low6960Allocation.Group17.receipt
  | ⟨18,_⟩ => Low6960Allocation.Group18.receipt
  | ⟨19,_⟩ => Low6960Allocation.Group19.receipt
  | ⟨20,_⟩ => Low6960Allocation.Group20.receipt
  | ⟨21,_⟩ => Low6960Allocation.Group21.receipt
  | ⟨22,_⟩ => Low6960Allocation.Group22.receipt
  | ⟨23,_⟩ => Low6960Allocation.Group23.receipt
  | ⟨24,_⟩ => Low6960Allocation.Group24.receipt
  | ⟨25,_⟩ => Low6960Allocation.Group25.receipt
  | ⟨26,_⟩ => Low6960Allocation.Group26.receipt
  | ⟨27,_⟩ => Low6960Allocation.Group27.receipt
  | ⟨28,_⟩ => Low6960Allocation.Group28.receipt
  | ⟨29,_⟩ => Low6960Allocation.Group29.receipt
  | ⟨30,_⟩ => Low6960Allocation.Group30.receipt
  | ⟨31,_⟩ => Low6960Allocation.Group31.receipt
  | ⟨32,_⟩ => Low6960Allocation.Group32.receipt
  | ⟨33,_⟩ => Low6960Allocation.Group33.receipt
  | ⟨34,_⟩ => Low6960Allocation.Group34.receipt
  | ⟨35,_⟩ => Low6960Allocation.Group35.receipt
  | ⟨36,_⟩ => Low6960Allocation.Group36.receipt
  | ⟨37,_⟩ => Low6960Allocation.Group37.receipt
  | ⟨38,_⟩ => Low6960Allocation.Group38.receipt
  | ⟨39,_⟩ => Low6960Allocation.Group39.receipt
  | ⟨40,_⟩ => Low6960Allocation.Group40.receipt
  | ⟨41,_⟩ => Low6960Allocation.Group41.receipt
  | ⟨42,_⟩ => Low6960Allocation.Group42.receipt
  | ⟨43,_⟩ => Low6960Allocation.Group43.receipt
  | ⟨n+44,h⟩ => absurd h (by omega)

private theorem receipts_orders : (fun k => (receipts k).orders) = bandOrders :=
  funext fun k => by fin_cases k <;> rfl

/-- The 69.61 low count for the actual family at every positive height through 2367, given the
payment `gates` of the gated shapes (empty band and bands `(w,3,1)`, `w ≤ 5`) by the two-cut gates. -/
theorem count (gates : Gates) {cap u del Γ} (M : P1.ModelAt cap u del)
    (F : P1.FamilyAt 179798 M Γ) (lo : 1≤M.overhead) (hi : M.overhead≤2367) :
    Γ.card≤274796225155308725 := by
  obtain ⟨G,gate,htab⟩ := gates
  rw [← receipts_orders] at htab
  exact count_with_receipts receipts htab gate M F lo hi

#print axioms count
end Lower6960.Low

end Merged_R6960Low6960Count

-- merged module R6960Front6960Assembly
section Merged_R6960Front6960Assembly
set_option Elab.async false
namespace Lower6960
open ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower.Front6960Radius (p q)
theorem low_front_count (gates : Low6960Allocation.Gates) : Front6960.c6 := by
  intro _ _ M _ F lo hi
  exact Low.count gates M F lo hi
/-- The Lo-band count on [2368, 2401] (patternrecognition9's two-jet split, ported in
`R6963LoHighCount`). It is taken as a hypothesis here and supplied in `Solution`, because the
Lo-band modules import this file. -/
def LoCount : Prop :=
  ∀ {u deleted Γ} (M : P1.ModelAt 33619 u deleted) (_F : P1.FamilyAt 179798 M Γ),
    2368 ≤ M.overhead → M.overhead ≤ 2401 → Γ.card ≤ 274796225155308725
theorem protocol_claim (gates : Low6960Allocation.Gates)
    (lo : ∀ {u deleted Γ} (M : P1.ModelAt 33619 u deleted) (_F : P1.FamilyAt 179798 M Γ),
      2368 ≤ M.overhead → M.overhead ≤ 2401 → Γ.card ≤ 274796225155308725)
    (high : ∀ {u deleted Γ} (M : P1.ModelAt 33619 u deleted) (_F : P1.FamilyAt 179798 M Γ),
      2402 ≤ M.overhead → M.overhead ≤ 33619 → Γ.card ≤ 274796225155308725) :
    ProtocolClaim 6963 p q := by
  apply ProximityPrize.SubmissionLower.Front6960Radius.extend
  apply Front6960.of_children Front6960ListBank.scalar_list
    Front6960_1.proof Front6960_2.proof
    (Front6960_3.of_children Front6960_3_1.proof Front6960_3_2.proof)
    (Front6960_4.of_children Front6960_4_1.proof Front6960_4_2.proof)
    Front6960_5.proof (low_front_count gates)
  intro _ _ M _ F lo' hi'
  have hc : Front6960.lowCutoff = 2367 := rfl
  have lo3 : Front6960.lowCutoff + 1 ≤ P1.ModelAt.overhead M := lo'
  have lo2 : (2368 : ℤ) ≤ P1.ModelAt.overhead M := by rw [hc] at lo3; omega
  by_cases h : P1.ModelAt.overhead M ≤ 2401
  · exact lo M F lo2 h
  · exact high M F (by have h3 : ¬ P1.ModelAt.overhead M ≤ 2401 := h; omega) hi'
theorem protocol_claim_of_retained (gates : Low6960Allocation.Gates) (loc : LoCount) (retained : RetainedCount) : ProtocolClaim 6963 p q :=
  protocol_claim gates (fun M F l h => loc M F l h) (fun M F lo hi => high_count_of_retained retained M F lo hi)
#print axioms protocol_claim_of_retained
#print axioms low_front_count
#print axioms protocol_claim
end Lower6960

end Merged_R6960Front6960Assembly

-- merged module R6960RetainedCompressionAssembly
section Merged_R6960RetainedCompressionAssembly

set_option Elab.async false
namespace Lower6960

/-- The 69.61 claim reduces to the remaining bounded-weight,
positive-seed, nonpure marked-factor estimate. -/
theorem protocol_claim_of_nonpure (gates : Low6960Allocation.Gates) (loc : LoCount) (count : RetainedCompression.NonPureFactorPrice) :
    ProximityPrize.Benchmark.ProtocolClaim 6963
      ProximityPrize.SubmissionLower.Front6960Radius.p
      ProximityPrize.SubmissionLower.Front6960Radius.q :=
  protocol_claim_of_retained gates loc (RetainedCompression.retained_of_nonpure count)

#print axioms protocol_claim_of_nonpure
end Lower6960

end Merged_R6960RetainedCompressionAssembly

-- merged module R6960RetainedLinearBase
section Merged_R6960RetainedLinearBase
set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 2500000
namespace Lower6960.RetainedLinear
noncomputable section
open Polynomial
open scoped Polynomial nonZeroDivisors
variable {F E : Type} [Field F] [Field E] [Algebra F E]
abbrev Fn (F : Type) [Field F] := FractionRing (Polynomial F)
def constants : (Polynomial F) →+* (Polynomial E) := mapRingHom (algebraMap F E)
theorem constants_injective : Function.Injective (constants (F:=F) (E:=E)) :=
  Polynomial.map_injective _ (algebraMap F E).injective
def rationalConstants : Fn F →+* Fn E :=
  IsFractionRing.map (constants_injective (F:=F) (E:=E))
abbrev incl (F : Type) [Field F] := algebraMap (Polynomial F) (Fn F)
theorem incl_injective (F : Type) [Field F] : Function.Injective (incl F) :=
  IsFractionRing.injective (Polynomial F) (Fn F)
@[simp] theorem rationalConstants_incl (a : (Polynomial F)) :
    rationalConstants (E:=E) (incl F a)=incl E (constants a) := by
  unfold rationalConstants IsFractionRing.map
  exact IsLocalization.map_eq _ _
@[simp] theorem eval_constants (a : (Polynomial F)) (x : F) :
    (constants (E:=E) a).eval (algebraMap F E x)=algebraMap F E (a.eval x) :=
  Polynomial.eval_map_apply (algebraMap F E) (p:=a) x
private theorem base_multiple_linear [Algebra.IsAlgebraic F E] (x : F) (r : E)
    (away : r≠algebraMap F E x) :
    ∃ b : (Polynomial F), b.eval x≠0 ∧ (Polynomial.X-C r)∣constants b := by
  have integ : IsIntegral F r := Algebra.IsIntegral.isIntegral r
  let b := minpoly F r
  have root : (constants (E:=E) b).eval r=0 := by
    change (b.map (algebraMap F E)).eval r=0
    rw [eval_map]
    exact minpoly.aeval F r
  refine ⟨b,?_ ,dvd_iff_isRoot.mpr root⟩
  intro zero
  have dvd : Polynomial.X-C x∣b := dvd_iff_isRoot.mpr zero
  have assoc := (irreducible_X_sub_C x).associated_of_dvd (minpoly.irreducible integ) dvd
  obtain ⟨a,eq⟩ := assoc.symm.dvd
  have mapped := congrArg (fun g : (Polynomial F) => (constants (E:=E) g).eval r) eq
  change (constants (E:=E) (Polynomial.X-C x)).eval r=(constants (E:=E) (b*a)).eval r at mapped
  rw [map_mul,eval_mul,root,zero_mul] at mapped
  have eq' : (constants (E:=E) (Polynomial.X-C x)).eval r=r-algebraMap F E x := by
    simp only [constants,coe_mapRingHom,Polynomial.map_sub,Polynomial.map_X,
      Polynomial.map_C,eval_sub,eval_X,eval_C]
  rw [eq'] at mapped
  exact away (sub_eq_zero.mp mapped)
theorem base_multiple [IsAlgClosed E] [Algebra.IsAlgebraic F E]
    (x : F) (q : (Polynomial E)) (regular : q.eval (algebraMap F E x)≠0) :
    ∃ b : (Polynomial F), b.eval x≠0 ∧ q∣constants b := by
  induction q using WfDvdMonoid.induction_on_irreducible with
  | zero => simp at regular
  | unit q hu => exact ⟨1,by simp,hu.dvd⟩
  | mul a q an ir ih =>
    rw [eval_mul] at regular
    have qa : a.eval (algebraMap F E x)≠0 := fun z=>regular (by rw [z,mul_zero])
    have qq : q.eval (algebraMap F E x)≠0 := fun z=>regular (by rw [z,zero_mul])
    obtain ⟨u,hu,dU⟩ := ih qa
    obtain ⟨r,hr⟩ := IsAlgClosed.exists_root q (degree_pos_of_irreducible ir).ne'
    have away : r≠algebraMap F E x := fun h=>qq (h ▸ hr)
    have n : Polynomial.X-C r∣q := dvd_iff_isRoot.mpr hr
    have tied := (irreducible_X_sub_C r).associated_of_dvd ir n
    obtain ⟨v,hv,dV⟩ := base_multiple_linear x r away
    exact ⟨v*u,by rw [eval_mul]; exact mul_ne_zero hv hu,
      by rw [map_mul]; exact mul_dvd_mul (tied.symm.dvd.trans dV) dU⟩
def base : (Polynomial F) →+* Fn E := (incl E).comp constants
theorem polynomial_integral [Algebra.IsAlgebraic F E] (p : (Polynomial E)) :
    (base (F:=F) (E:=E)).IsIntegralElem (incl E p) := by
  let j := base (F:=F) (E:=E)
  letI : Algebra (Polynomial F) (Fn E) := j.toAlgebra
  have const (a : E) : IsIntegral (Polynomial F) (incl E (C a)) := by
    let η : E →+* Fn E := (incl E).comp C
    have h : (algebraMap F E).IsIntegralElem a := Algebra.IsIntegral.isIntegral a
    have mapped := h.map η
    have eq : η.comp (algebraMap F E)=j.comp C := by
      apply RingHom.ext
      intro t
      simp [η,j,base,constants]
    rw [eq] at mapped
    exact mapped.of_comp
  have abscissa : IsIntegral (Polynomial F) (incl E (Polynomial.X : (Polynomial E))) := by
    have eq : (algebraMap (Polynomial F) (Fn E)) Polynomial.X=incl E (Polynomial.X : (Polynomial E)) := by
      change j Polynomial.X=_
      simp [j,base,constants]
    exact eq ▸ isIntegral_algebraMap
  change IsIntegral (Polynomial F) (incl E p)
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial,map_mul,map_pow]
    exact (const a).mul (abscissa.pow n)
theorem integral_is_polynomial {r : Fn E} (h : (base (F:=F) (E:=E)).IsIntegralElem r) :
    ∃ p : (Polynomial E), incl E p=r := by
  have integral : IsIntegral (Polynomial E) r := h.of_comp
  exact (isIntegrallyClosed_iff (K:=Fn E)).mp (inferInstance : IsIntegrallyClosed (Polynomial E)) integral
end
end Lower6960.RetainedLinear

end Merged_R6960RetainedLinearBase

-- merged module R6960RetainedLinearFactor
section Merged_R6960RetainedLinearFactor
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 2300000
namespace Lower6960.RetainedLinear
noncomputable section
open Polynomial
open scoped Polynomial nonZeroDivisors
variable {F E : Type} [Field F] [Field E] [Algebra F E]
abbrev Plane (F : Type) [Field F] := Polynomial (Polynomial F)
def arithmetic (P : Plane F) : Polynomial (Fn F) := P.map (incl F)
def geometric (P : Plane F) : Polynomial (Fn E) := P.map (base (E:=E))
theorem geometric_map (P : Plane F) : geometric (E:=E) P=(arithmetic P).map rationalConstants := by
  unfold geometric arithmetic
  rw [Polynomial.map_map]
  congr 1
  apply RingHom.ext
  intro a
  simp [base]
theorem geometric_deg (P : Plane F) : (geometric (E:=E) P).natDegree=P.natDegree := by
  have injective : Function.Injective (base (F:=F) (E:=E)) :=
    (incl_injective E).comp (constants_injective (F:=F) (E:=E))
  exact natDegree_map_eq_of_injective injective P
theorem arithmetic_irred {P : Plane F} (ir : Irreducible P) (pos : 0<P.natDegree) :
    Irreducible (arithmetic P) :=
  (ir.isPrimitive (Nat.ne_of_gt pos)).irreducible_iff_irreducible_map_fraction_map.mp ir
theorem node_not_zero {P : Plane F} (ir : Irreducible P) (pos : 0<P.natDegree) (x : F) :
    P.map (evalRingHom x)≠0 := by
  intro zero
  have prime := ir.isPrimitive (Nat.ne_of_gt pos)
  apply (irreducible_X_sub_C x).not_isUnit
  apply isPrimitive_iff_isUnit_of_C_dvd.mp prime
  apply (C_dvd_iff_dvd_coeff ..).mpr
  intro i
  apply dvd_iff_isRoot.mpr
  have gone := congrArg (fun Q : (Polynomial F) => Q.coeff i) zero
  simpa only [Polynomial.IsRoot,coeff_map,coe_evalRingHom,coeff_zero] using gone
abbrev numerator (r : Fn E) : (Polynomial E) := IsFractionRing.num (Polynomial E) r
abbrev denominator (r : Fn E) : (Polynomial E) := (IsFractionRing.den (Polynomial E) r).val
theorem denominator_ne (r : Fn E) : denominator r≠0 :=
  nonZeroDivisors.coe_ne_zero (IsFractionRing.den (Polynomial E) r)
theorem numerator_eq (r : Fn E) : r*incl E (denominator r)=incl E (numerator r) :=
  (IsFractionRing.num_mul_den_eq_num_iff_eq' (A:=(Polynomial E))).mpr rfl
private def line (r : Fn E) : Plane E := C (denominator r)*Polynomial.X+C (-numerator r)
private theorem line_primitive (r : Fn E) : (line r).IsPrimitive := by
  apply isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro b hb
  have coef := (C_dvd_iff_dvd_coeff ..).mp hb
  have first : b∣denominator r := by simpa [line] using coef 1
  have second : b∣numerator r := dvd_neg.mp (by simpa [line] using coef 0)
  exact IsFractionRing.num_den_reduced (Polynomial E) r second first
private theorem mapped_line (r : Fn E) :
    (line r).map (incl E)=C (incl E (denominator r))*(Polynomial.X-C r) := by
  simp only [line,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,
    Polynomial.map_neg,map_neg]
  rw [← numerator_eq r]
  rw [mul_sub, mul_comm r, C_mul]
  ring
private theorem line_prod_primitive (s : Multiset (Fn E)) : ((s.map line).prod).IsPrimitive := by
  letI : NormalizedGCDMonoid (Polynomial E) := Classical.choice inferInstance
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    rw [Multiset.map_cons,Multiset.prod_cons]
    exact (line_primitive r).mul ih
private theorem mapped_lines (s : Multiset (Fn E)) :
    ((s.map line).prod).map (incl E)=C ((s.map (fun r=>incl E (denominator r))).prod) *
      (s.map (fun r=>Polynomial.X-C r)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    simp only [Multiset.map_cons,Multiset.prod_cons,Polynomial.map_mul,mapped_line,ih,C_mul]
    ring
theorem exists_regular_root {P : Plane F} (ir : Irreducible P) (pos : 0<P.natDegree)
    (splits : (geometric (E:=E) P).Splits) (x t : F) (hit : (P.map (evalRingHom x)).eval t=0) :
    ∃ r ∈ (geometric (E:=E) P).roots,
      (denominator r).eval (algebraMap F E x)≠0 ∧
      (numerator r).eval (algebraMap F E x)=(denominator r).eval (algebraMap F E x)*algebraMap F E t := by
  classical
  let Qe := P.map (constants (F:=F) (E:=E))
  let L := geometric (E:=E) P
  let rs := L.roots
  let G := (rs.map line).prod
  let b := (rs.map (fun r=>incl E (denominator r))).prod
  have Pn := ir.ne_zero
  have geo : Qe.map (incl E)=L := by
    simp [Qe, L, geometric, base, Polynomial.map_map]
  have dn : b≠0 := by
    apply Multiset.prod_ne_zero
    intro mem
    obtain ⟨r,_,eq⟩ := Multiset.mem_map.mp mem
    exact ((map_ne_zero_iff _ (incl_injective E)).mpr (denominator_ne r)) eq
  have Gmap : G.map (incl E)=C b*(rs.map (fun r=>Polynomial.X-C r)).prod := mapped_lines rs
  have fac := splits.eq_prod_roots
  have mapped_dvd : G.map (incl E)∣Qe.map (incl E) := by
    refine ⟨C (L.leadingCoeff/b),?_⟩
    rw [geo,Gmap]
    change L=C b*(rs.map (fun r=>Polynomial.X-C r)).prod*C (L.leadingCoeff/b)
    calc
      _ = C L.leadingCoeff*(rs.map (fun r=>Polynomial.X-C r)).prod := fac
      _ = _ := by
        rw [mul_right_comm,← C_mul,← mul_div_assoc,mul_div_cancel_left₀ _ dn]
  obtain ⟨q,hq⟩ := (line_prod_primitive rs).dvd_of_fraction_map_dvd_fraction_map mapped_dvd
  have Gn : G≠0 := (line_prod_primitive rs).ne_zero
  have Yn : Qe≠0 := by
    have inj : Function.Injective (Polynomial.mapRingHom (constants (F:=F) (E:=E))) :=
      Polynomial.map_injective _ (constants_injective (F:=F) (E:=E))
    exact (map_ne_zero_iff _ inj).mpr Pn
  have qn : q≠0 := fun z=>Yn (by rw [hq,z,mul_zero])
  have degg : G.natDegree=P.natDegree := by
    rw [← natDegree_map_eq_of_injective (incl_injective E) G,Gmap,natDegree_C_mul dn,
      natDegree_multiset_prod_X_sub_C_eq_card,← splits.natDegree_eq_card_roots]
    exact geometric_deg P
  have degY : Qe.natDegree=P.natDegree := natDegree_map_eq_of_injective constants_injective _
  have size : q.natDegree=0 := by
    rw [hq,natDegree_mul Gn qn,degg] at degY
    omega
  let c := q.coeff 0
  have facY : Qe=G*C c := hq.trans (by rw [eq_C_of_natDegree_eq_zero size])
  let x' := algebraMap F E x
  let t' := algebraMap F E t
  let node := evalRingHom x'
  have compare : Qe.map node=(P.map (evalRingHom x)).map (algebraMap F E) := by
    apply Polynomial.ext
    intro i
    simp only [Qe,coeff_map,node,coe_evalRingHom,eval_constants,x']
  have Yn' : Qe.map node≠0 := by
    rw [compare]
    intro zero
    apply node_not_zero ir pos x
    apply Polynomial.map_injective _ (algebraMap F E).injective
    simpa only [Polynomial.map_zero] using zero
  have cn' : c.eval x'≠0 := by
    intro ch
    apply Yn'
    rw [facY,Polynomial.map_mul,Polynomial.map_C,coe_evalRingHom,ch,C_0,mul_zero]
  have hit' : (Qe.map node).eval t'=0 := by
    rw [compare,eval_map_apply,hit,map_zero]
  let select : Plane E →+* E := (evalRingHom t').comp (mapRingHom node)
  change select Qe=0 at hit'
  rw [facY,map_mul] at hit'
  have pc : select (C c)=c.eval x' := by
    simp only [select, RingHom.comp_apply,coe_mapRingHom,Polynomial.map_C,
      coe_evalRingHom,eval_C,node]
  rw [pc] at hit'
  have gone := (mul_eq_zero.mp hit').resolve_right cn'
  change select (rs.map line).prod=0 at gone
  rw [← Multiset.prod_hom, Multiset.map_map] at gone
  obtain ⟨r,hr,val⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp gone)
  have v : (denominator r).eval x'*t'+(-(numerator r)).eval x'=0 := by
    simpa [select,node,line] using val
  rw [eval_neg] at v
  have relation : (numerator r).eval x'=(denominator r).eval x'*t' := by
    linear_combination -v
  have den : (denominator r).eval x'≠0 := by
    intro collapse
    have num : (numerator r).eval x'=0 := by rw [relation,collapse,zero_mul]
    have d₀ : Polynomial.X-C x'∣numerator r := dvd_iff_isRoot.mpr num
    have d₁ : Polynomial.X-C x'∣denominator r := dvd_iff_isRoot.mpr collapse
    exact (irreducible_X_sub_C x').not_isUnit (IsFractionRing.num_den_reduced (Polynomial E) r d₀ d₁)
  exact ⟨r,hr,den,relation⟩
#print axioms node_not_zero
#print axioms exists_regular_root
end
end Lower6960.RetainedLinear

end Merged_R6960RetainedLinearFactor

-- merged module R6960RetainedLinearConjugacy
section Merged_R6960RetainedLinearConjugacy

set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 2700000

namespace Lower6960.RetainedLinear
noncomputable section
open Polynomial
open scoped Polynomial

variable {F E : Type} [Field F] [Field E] [Algebra F E]

private theorem base_injective : Function.Injective (base (F:=F) (E:=E)) :=
  (incl_injective E).comp (constants_injective (F:=F) (E:=E))

private theorem adjoint_conjugates {P : Plane F} (ir : Irreducible P) (pos : 0<P.natDegree)
    (b : (Polynomial F)) (x t : F) {r s : Fn E} (hr : r∈(geometric (E:=E) P).roots)
    (hs : s∈(geometric (E:=E) P).roots) :
    (base (F:=F) (E:=E)).IsIntegralElem ((base b)*(r-base (C t))/(base (Polynomial.X-C x))) →
    (base (F:=F) (E:=E)).IsIntegralElem ((base b)*(s-base (C t))/(base (Polynomial.X-C x))) := by
  let Q := arithmetic P
  letI : Fact (Irreducible Q) := ⟨arithmetic_irred ir pos⟩
  let j := (AdjoinRoot.of Q).comp (incl F)
  let u : AdjoinRoot Q := j b*(AdjoinRoot.root Q-j (C t))/j (Polynomial.X-C x)
  have raw (a : Fn E) (ha : a∈(geometric (E:=E) P).roots) :
      Q.eval₂ (rationalConstants (F:=F) (E:=E)) a=0 := by
    have injective : Function.Injective (Polynomial.mapRingHom (base (F:=F) (E:=E))) :=
      Polynomial.map_injective _ base_injective
    have nonzero : geometric (E:=E) P≠0 := (map_ne_zero_iff _ injective).mpr ir.ne_zero
    have ez := (mem_roots nonzero).mp ha
    change (geometric (E:=E) P).eval a=0 at ez
    rw [geometric_map,eval_map] at ez
    exact ez
  let lift (a : Fn E) (ha : a∈(geometric (E:=E) P).roots) :=
    AdjoinRoot.lift (rationalConstants (F:=F) (E:=E)) a (raw a ha)
  have extends_base (a : Fn E) (ha : a∈(geometric (E:=E) P).roots) :
      (lift a ha).comp j=base (F:=F) (E:=E) := by
    apply RingHom.ext
    intro a'
    dsimp [lift,j]
    rw [AdjoinRoot.lift_of,rationalConstants_incl]
    rfl
  have eq (a : Fn E) (ha : a∈(geometric (E:=E) P).roots) :
      lift a ha u=base b*(a-base (C t))/base (Polynomial.X-C x) := by
    simp only [u,map_div₀,map_mul,map_sub]
    have root : lift a ha (AdjoinRoot.root Q)=a := AdjoinRoot.lift_root (raw a ha)
    have one (v : (Polynomial F)) : lift a ha (j v)=base v := DFunLike.congr_fun (extends_base a ha) v
    simp only [root,one]
  intro original
  have at_r : ((lift r hr).comp j).IsIntegralElem (lift r hr u) := by
    rwa [extends_base r hr,eq r hr]
  have integral : j.IsIntegralElem u :=
    at_r.of_map (lift r hr).injective
  have at_s := integral.map (lift s hs)
  rwa [extends_base s hs,eq s hs] at at_s

/-- Lift the received ordinate along one primitive branch. Every conjugate
has a common arithmetic denominator and the same physical residue. -/
theorem common_numerators [IsAlgClosed E] [Algebra.IsAlgebraic F E] {P : Plane F}
    (ir : Irreducible P) (pos : 0<P.natDegree)
    (splits : (geometric (E:=E) P).Splits) (x t : F) (hit : (P.map (evalRingHom x)).eval t=0) :
    ∃ b : (Polynomial F), b.eval x≠0 ∧
      ∀ r∈(geometric (E:=E) P).roots, ∃ a : (Polynomial E),
        incl E a=base b*r ∧
        a.eval (algebraMap F E x)=algebraMap F E (b.eval x)*algebraMap F E t := by
  obtain ⟨r,hr,rden,rt⟩ := exists_regular_root (E:=E) ir pos splits x t hit
  obtain ⟨b,hb,m,hm⟩ := base_multiple x (denominator r) rden
  let x' := algebraMap F E x
  let t' := algebraMap F E t
  let pX : (Polynomial E) := Polynomial.X-C x'
  have pX_image : base (Polynomial.X-C x) = incl E pX := by
    simp [base,constants,pX,x']
  have x_nonzero : base (E:=E) (Polynomial.X-C x)≠0 :=
    (map_ne_zero_iff _ base_injective).mpr (X_sub_C_ne_zero _)
  have t_image : base (C t)=incl E (C t') := by simp [base,constants,t']
  have exact_root : pX ∣ numerator r-C t'*denominator r := by
    apply dvd_iff_isRoot.mpr
    change (numerator r-C t'*denominator r).eval x'=0
    rw [eval_sub,eval_mul,eval_C,rt]
    ring
  obtain ⟨c,hc⟩ := exact_root
  have b_image : base b=incl E (denominator r*m) := by
    change incl E (constants b)=_
    rw [hm]
  have b_slope : base b*(r-base (C t))/base (Polynomial.X-C x)=incl E (c*m) := by
    apply (div_eq_iff x_nonzero).mpr
    calc
      _ = incl E ((numerator r-C t'*denominator r)*m) := by
        rw [b_image,t_image]
        simp only [map_mul,map_sub]
        rw [← numerator_eq r]
        ring
      _ = _ := by rw [hc,pX_image]; simp only [map_mul]; ring
  have regular : (base (F:=F) (E:=E)).IsIntegralElem
      (base b*(r-base (C t))/base (Polynomial.X-C x)) := by
    rw [b_slope]
    exact polynomial_integral (c*m)
  refine ⟨b,hb,?_⟩
  intro s hs
  have h := adjoint_conjugates ir pos b x t hr hs regular
  obtain ⟨n,hn⟩ := integral_is_polynomial h
  let a := constants (E:=E) b*C t'+pX*n
  have eq : base b*(s-base (C t))=incl E n*base (Polynomial.X-C x) :=
    (div_eq_iff x_nonzero).mp hn.symm
  refine ⟨a,?_ ,?_⟩
  · unfold a
    simp only [map_add,map_mul]
    have b_incl : incl E (constants (E:=E) b)=base b := rfl
    rw [b_incl,← t_image,← pX_image]
    linear_combination -eq
  · simp [a,pX,x',t',eval_constants]

#print axioms common_numerators
end
end Lower6960.RetainedLinear

end Merged_R6960RetainedLinearConjugacy

-- merged module R6960RetainedLinearSpecialization
section Merged_R6960RetainedLinearSpecialization
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
namespace Lower6960.RetainedLinear
noncomputable section
open Polynomial
open scoped Polynomial
variable {F E : Type} [Field F] [Field E] [Algebra F E]
private def linearAt (B A : (Polynomial E)) : Plane E := C B*Polynomial.X-C A
private theorem map_linearAt (B A : (Polynomial E)) (r : Fn E) (ha : incl E A=incl E B*r) :
    (linearAt B A).map (incl E)=C (incl E B)*(Polynomial.X-C r) := by
  simp only [linearAt,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,
    ha,C_mul,mul_sub]
private theorem mapped_all (B : (Polynomial E)) (A : Fn E→(Polynomial E)) (s : Multiset (Fn E))
    (h : ∀ r∈s,incl E (A r)=incl E B*r) :
    ((s.map (fun r=>linearAt B (A r))).prod).map (incl E)=C ((incl E B)^s.card) *
      (s.map (fun r=>Polynomial.X-C r)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    have hr := h r (Multiset.mem_cons_self r s)
    have rest := ih (fun a ha=>(h a (Multiset.mem_cons_of_mem ha)))
    simp only [Multiset.map_cons,Multiset.prod_cons,Polynomial.map_mul,map_linearAt B _ r hr,
      rest,Multiset.card_cons,pow_succ,C_mul]
    ring
private theorem specialized_all (B : (Polynomial E)) (A : Fn E→(Polynomial E)) (s : Multiset (Fn E)) (x t : E)
    (h : ∀ r∈s,(A r).eval x=B.eval x*t) :
    ((s.map (fun r=>linearAt B (A r))).prod).map (evalRingHom x)=
      C ((B.eval x)^s.card)*(Polynomial.X-C t)^s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    have hr := h r (Multiset.mem_cons_self r s)
    have first : (linearAt B (A r)).map (evalRingHom x)=C (B.eval x)*(Polynomial.X-C t) := by
      simp only [linearAt,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,
        Polynomial.map_X,coe_evalRingHom,hr,C_mul,mul_sub]
    have rest := ih (fun a ha=>h a (Multiset.mem_cons_of_mem ha))
    simp only [Multiset.map_cons,Multiset.prod_cons,Polynomial.map_mul,first,rest,
      Multiset.card_cons,pow_succ,C_mul]
    ring
theorem pure_specialization [IsAlgClosed E] [Algebra.IsAlgebraic F E] {P : Plane F}
    (ir : Irreducible P) (pos : 0<P.natDegree) (splits : (geometric (E:=E) P).Splits)
    (x t : F) (hit : (P.map (evalRingHom x)).eval t=0) :
    P.map (evalRingHom x)=C (P.map (evalRingHom x)).leadingCoeff*(Polynomial.X-C t)^P.natDegree := by
  classical
  let G := geometric (E:=E) P
  let roots := G.roots
  let Q := P.map (constants (F:=F) (E:=E))
  let x' := algebraMap F E x
  let t' := algebraMap F E t
  let atX := evalRingHom x'
  let degree := P.natDegree
  have lifts : Q.map (incl E)=G := by
    simp [Q,G,geometric,base,Polynomial.map_map]
  have d : roots.card=degree := splits.natDegree_eq_card_roots.symm.trans (geometric_deg P)
  obtain ⟨b,hb,numerators⟩ := common_numerators (E:=E) ir pos splits x t hit
  let B := constants (E:=E) b
  let A (r : Fn E) : (Polynomial E) := if h : r∈roots then (numerators r h).choose else 0
  have den : B.eval x'≠0 := by rw [eval_constants]; exact (map_ne_zero_iff _ (algebraMap F E).injective).mpr hb
  have both (r : Fn E) (h : r∈roots) :
      incl E (A r)=incl E B*r ∧ (A r).eval x'=B.eval x'*t' := by
    simpa only [A,dite_eq_left h,eval_constants,x',t',B,base,RingHom.comp_apply] using
      (numerators r h).choose_spec
  let H := (roots.map (fun r=>linearAt B (A r))).prod
  have shape : H.map (incl E)=C ((incl E B)^degree)*(roots.map (fun r=>Polynomial.X-C r)).prod := by
    rw [mapped_all B A roots (fun r hr=>(both r hr).1),d]
  have fibre : H.map atX=C ((B.eval x')^degree)*(Polynomial.X-C t')^degree := by
    rw [specialized_all B A roots x' t' (fun r hr=>(both r hr).2),d]
  have lead : incl E Q.leadingCoeff=G.leadingCoeff := by
    rw [← lifts, leadingCoeff_map_of_injective (incl_injective E)]
  have packed : C (B^degree)*Q=C Q.leadingCoeff*H := by
    apply Polynomial.map_injective _ (incl_injective E)
    rw [Polynomial.map_mul,Polynomial.map_C,map_pow,lifts,Polynomial.map_mul,Polynomial.map_C,lead,shape]
    calc
      C ((incl E B)^degree)*G =
          C ((incl E B)^degree)*(C G.leadingCoeff*(roots.map (fun r=>Polynomial.X-C r)).prod) :=
        congrArg _ splits.eq_prod_roots
      _ = _ := by ring
  have mapped := congrArg (Polynomial.map atX) packed
  simp only [Polynomial.map_mul,Polynomial.map_C,atX,coe_evalRingHom,eval_pow] at mapped
  change C ((B.eval x')^degree)*(Q.map atX)=C (Q.leadingCoeff.eval x')*(H.map atX) at mapped
  rw [fibre] at mapped
  have qeq : Q.map atX=C (Q.leadingCoeff.eval x')*(Polynomial.X-C t')^degree := by
    apply mul_left_cancel₀ (a:=C ((B.eval x')^degree)) (C_ne_zero.mpr (pow_ne_zero _ den))
    calc
      _ = C (Q.leadingCoeff.eval x')*(C ((B.eval x')^degree)*(Polynomial.X-C t')^degree) := mapped
      _ = _ := by ring
  have lead_eq : (Q.map atX).leadingCoeff=Q.leadingCoeff.eval x' := by
    have monic : ((Polynomial.X-C t')^degree).Monic := (monic_X_sub_C t').pow _
    rw [qeq,leadingCoeff_mul,leadingCoeff_C,monic.leadingCoeff,mul_one]
  rw [← lead_eq] at qeq
  have recover : Q.map atX=(P.map (evalRingHom x)).map (algebraMap F E) := by
    apply Polynomial.ext
    intro i
    simp only [Q,atX,coeff_map,coe_evalRingHom,eval_constants,x']
  apply Polynomial.map_injective _ (algebraMap F E).injective
  simp only [Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_sub,
    Polynomial.map_X,← leadingCoeff_map_of_injective (algebraMap F E).injective,← recover]
  exact qeq
#print axioms pure_specialization
end
end Lower6960.RetainedLinear

end Merged_R6960RetainedLinearSpecialization

-- merged module R6960RetainedLinearAssembly
section Merged_R6960RetainedLinearAssembly
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
namespace Lower6960.RetainedLinear
noncomputable section
open Polynomial Finset
open K1 (K I node)
open K1_14 (L liftPoly)
open CurvatureSquares (Ordinate)
open RescueGeometry (Model Family)
open RetainedShortening (Word)
open RetainedCompression (Curve ordinate parameter height heightCap wordDegree MarkedFiber
  PureNodes atNode NonPureFactorPrice view view_y scalar)
open scoped Polynomial
abbrev Seed := Fn L
def toSeed : Ordinate →+* Plane Seed :=
  mapRingHom (mapRingHom (incl L))
theorem toSeed_injective : Function.Injective toSeed :=
  Polynomial.map_injective _ (Polynomial.map_injective _ (incl_injective L))
theorem toSeed_degree (P : Ordinate) : (toSeed P).natDegree=P.natDegree :=
  natDegree_map_eq_of_injective (Polynomial.map_injective _ (incl_injective L)) P
private def seedScalar (b : (Polynomial L)) : Plane Seed := C (C (incl L b))
private theorem seedScalar_isUnit (b : (Polynomial L)) (hb : b≠0) : IsUnit (seedScalar b) :=
  isUnit_C.mpr (isUnit_C.mpr (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (incl_injective L)).mpr hb)))
private theorem clear_seed (Q : Plane Seed) :
    ∃ (b : (Polynomial L)) (R : Ordinate), b≠0 ∧ toSeed R=seedScalar b*Q := by
  obtain ⟨b,R,nonzero,hr⟩ := RetainedCompression.clear_abscissa Q
  refine ⟨b,R.map Bivariate.swap.toRingHom,nonzero,?_⟩
  show (R.map Bivariate.swap.toRingHom).map (mapRingHom (incl L))=_
  rw [Polynomial.map_map]
  exact hr
private theorem lifted_scalar_product (P : Ordinate) (a b : (Polynomial L)) :
    toSeed (C (C (a*b))*P)=seedScalar a*seedScalar b*toSeed P := by
  rw [map_mul]
  simp only [toSeed,coe_mapRingHom,Polynomial.map_C,map_mul,seedScalar]
theorem toSeed_irreducible {P : Ordinate} (ir : Irreducible P) (pos : 0<P.natDegree) :
    Irreducible (toSeed P) := by
  have pn : toSeed P≠0 := (map_ne_zero_iff _ toSeed_injective).mpr ir.ne_zero
  have prime : Prime P := UniqueFactorizationMonoid.irreducible_iff_prime.mp ir
  refine ⟨fun u => ?_, fun A B split => ?_⟩
  · have d := natDegree_eq_zero_of_isUnit u
    rw [toSeed_degree] at d
    omega
  obtain ⟨a,U,an,ua⟩ := clear_seed A
  obtain ⟨b,V,bn,vb⟩ := clear_seed B
  have product : U*V=P*C (C (a*b)) := by
    apply toSeed_injective
    rw [mul_comm P, lifted_scalar_product,map_mul,ua,vb,split]
    ring
  have dvd : P∣U*V := ⟨_,product⟩
  have with_unit {c : (Polynomial L)} {H : Ordinate} {J : Plane Seed}
      (cn : c≠0) (h : toSeed H=seedScalar c*J) (dv : P∣H) : toSeed P∣J := by
    have image := map_dvd toSeed dv
    rw [h] at image
    exact (seedScalar_isUnit c cn).dvd_mul_left.mp image
  have other {J K : Plane Seed} (dv : toSeed P∣J) (eq : toSeed P=J*K) : IsUnit K := by
    obtain ⟨c,fac⟩ := dv
    have unit : (1 : Plane Seed)=c*K := by
      apply mul_left_cancel₀ pn
      rw [mul_one,← mul_assoc,← fac,← eq]
    exact isUnit_of_dvd_one ⟨c,unit.trans (mul_comm c K)⟩
  rcases prime.dvd_mul.mp dvd with h | h
  · exact Or.inr (other (with_unit an ua h) split)
  · exact Or.inl (other (with_unit bn vb h) (split.trans (mul_comm A B)))
def GeometricallyLinear (P : Ordinate) : Prop :=
  (geometric (E:=AlgebraicClosure Seed) (toSeed P)).Splits
private theorem node_map (P : Ordinate) (i : I) :
    (toSeed P).map (evalRingHom (incl L (C (algebraMap K L (node i)))))=
    (atNode P i).map (incl L) := by
  apply Polynomial.ext
  intro j
  simp only [toSeed,atNode,coe_mapRingHom,coeff_map,coe_evalRingHom]
  exact Polynomial.eval_map_apply (incl L) _
theorem pure_of_geometrically_linear (w : I→K) (P : Ordinate)
    (ir : Irreducible P) (pos : 0<P.natDegree) (linear : GeometricallyLinear P) :
    PureNodes w P := by
  intro i hit
  let x := incl L (C (algebraMap K L (node i)))
  let t := incl L (C (algebraMap K L (w i)))
  have equal : (toSeed P).map (evalRingHom x)=(atNode P i).map (incl L) := node_map P i
  have root : ((toSeed P).map (evalRingHom x)).eval t=0 := by
    rw [equal,eval_map_apply,hit,map_zero]
  have degree : 0<(toSeed P).natDegree := by rw [toSeed_degree]; exact pos
  have formula := pure_specialization (E:=AlgebraicClosure Seed)
    (toSeed_irreducible ir pos) degree linear x t root
  rw [equal,toSeed_degree] at formula
  apply Polynomial.map_injective _ (incl_injective L)
  simp only [Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_sub,
    Polynomial.map_X,← leadingCoeff_map_of_injective (incl_injective L)]
  exact formula
def NonlinearFactorPrice : Prop :=
  ∀ {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) (T : Finset K), T⊆Γ →
    Word 179798 wordDegree M.word F.scalar T→
    ∀ f : Curve (Polynomial L), Irreducible f →
      3≤f.degreeOf ordinate → f.degreeOf ordinate<48 → 0<f.degreeOf parameter →
      height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree →
      ¬GeometricallyLinear (view f) →
      (∀ γ∈T, MarkedFiber (view f) (scalar M γ) (liftPoly (F.scalar γ))) →
      T.card≤MarkedSheet.rate (f.degreeOf ordinate)*(f.degreeOf parameter)+
        (f.degreeOf ordinate-1)*(f.degreeOf ordinate)
theorem nonpure_of_nonlinear (price : NonlinearFactorPrice) : NonPureFactorPrice := by
  intro u deleted M Γ F T sub W f ir lo hi sv cap nonpure marks
  apply price F T sub W f ir lo hi sv cap _ marks
  intro linear
  apply nonpure
  have irr : Irreducible (view f) := (MulEquiv.irreducible_iff view).mpr ir
  have pos : 0<(view f).natDegree := by rw [view_y]; omega
  exact pure_of_geometrically_linear M.word _ irr pos linear
theorem protocol_claim_of_nonlinear (gates : Low6960Allocation.Gates) (loc : Lower6960.LoCount) (price : NonlinearFactorPrice) :
    ProximityPrize.Benchmark.ProtocolClaim 6963
      ProximityPrize.SubmissionLower.Front6960Radius.p
      ProximityPrize.SubmissionLower.Front6960Radius.q :=
  Lower6960.protocol_claim_of_nonpure gates loc (nonpure_of_nonlinear price)
#print axioms toSeed_irreducible
#print axioms pure_of_geometrically_linear
#print axioms protocol_claim_of_nonlinear
end
end Lower6960.RetainedLinear

end Merged_R6960RetainedLinearAssembly

-- merged module R6960MonicChartFinite
section Merged_R6960MonicChartFinite
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open scoped Polynomial Differential
theorem constant_evaluation_avoids {K : Type*} [Field K] [Infinite K]
    (f : (Polynomial (Polynomial K))) (primitive : f.IsPrimitive) (q : (Polynomial K)) (ir : Irreducible q) :
    ∃ c : K, ¬q∣f.eval (C c) := by
  let J : Ideal (Polynomial K) := Ideal.span {q}
  letI : J.IsPrime := (Ideal.span_singleton_prime ir.ne_zero).mpr ir.prime
  let ρ := Ideal.Quotient.mk J
  let embed : K→+*((Polynomial K)⧸J) := ρ.comp C
  by_contra! no
  have roots : (Set.range embed : Set ((Polynomial K)⧸J)) ⊆ {z | (f.map ρ).IsRoot z} := by
    rintro _ ⟨c,rfl⟩
    change (f.map ρ).eval (ρ (C c))=0
    rw [Polynomial.eval_map_apply]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr (no c)
  have zero : f.map ρ=0 := eq_zero_of_infinite_isRoot (f.map ρ)
    ((Set.infinite_range_of_injective embed.injective).mono roots)
  apply ir.not_isUnit
  apply (isPrimitive_iff_isUnit_of_C_dvd.mp primitive) q
  apply (C_dvd_iff_dvd_coeff ..).mpr
  intro j
  have vanish := congrArg (fun P : (Polynomial ((Polynomial K)⧸J)) => P.coeff j) zero
  rw [coeff_map,coeff_zero] at vanish
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp vanish)
section Finite
variable {K F E : Type*} [Field K] [Infinite K] [Field F] [Field E]
    [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F] [Algebra F E] [Algebra (Polynomial K) E]
    [IsScalarTower (Polynomial K) F E] [Algebra.IsSeparable F E] [FiniteDimensional F E]
    [Differential (Polynomial K)] [Differential E] [DifferentialAlgebra (Polynomial K) E]
theorem clears_finite (b : PowerBasis F E) (f : (Polynomial (Polynomial K))) (primitive : f.IsPrimitive)
    (e2 : 2≤f.natDegree) (degree : f.natDegree=b.dim) (tame : (f.natDegree:F)≠0)
    (root : aeval b.gen f=0) (x : E) (integral : IsIntegral (Polynomial K) x) :
    IsIntegral (Polynomial K) (algebraMap (Polynomial K) E ((paddedRes f)^2)*x′) := by
  apply ChartIntegrality.integral_from_places F
  intro q ir
  obtain ⟨c,n⟩ := constant_evaluation_avoids f primitive q ir
  let u := f.eval (C c)
  have un : u≠0 := by
    intro h
    apply n
    change q∣u
    rw [h]
    exact dvd_zero q
  let k := 2*((f.natDegree-1)*(f.natDegree-2))
  refine ⟨u^k,fun h=>n (ir.prime.dvd_of_dvd_pow h),?_⟩
  rw [←mul_assoc,←map_mul]
  exact scaled_raw_square_clears b f (C c) un e2 degree tame root x integral
end Finite
section Actual
open K1_14 (L)
open RetainedCompression (Curve ordinate view view_y)
abbrev Scalar := RetainedLinear.Seed
theorem actual_finite {E : Type*} [Field E] [Algebra (RatFunc Scalar) E]
    [Algebra (Polynomial Scalar) E] [IsScalarTower (Polynomial Scalar) (RatFunc Scalar) E]
    [Algebra.IsSeparable (RatFunc Scalar) E] [FiniteDimensional (RatFunc Scalar) E]
    [Differential (Polynomial Scalar)] [Differential E] [DifferentialAlgebra (Polynomial Scalar) E]
    (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48)
    (b : PowerBasis (RatFunc Scalar) E) (root : aeval b.gen (RetainedLinear.toSeed (view f))=0)
    (x : E) (int : IsIntegral (Polynomial Scalar) x) :
    IsIntegral (Polynomial Scalar)
      (algebraMap (Polynomial Scalar) E ((paddedRes (RetainedLinear.toSeed (view f)))^2)*x′) := by
  let P := RetainedLinear.toSeed (view f)
  have deg : P.natDegree=f.degreeOf ordinate := (RetainedLinear.toSeed_degree _).trans (view_y _)
  have pos : 0<(view f).natDegree := by rw [view_y]; omega
  have pir : Irreducible P :=
    RetainedLinear.toSeed_irreducible ((MulEquiv.irreducible_iff view).mpr ir) pos
  have pd : P.natDegree≠0 := by omega
  have prim := pir.isPrimitive pd
  let ι := algebraMap (Polynomial Scalar) (RatFunc Scalar)
  let Q := P.map ι
  have irrQ : Irreducible Q := prim.irreducible_iff_irreducible_map_fraction_map.mp pir
  have rootQ : aeval b.gen Q=0 := by rw [aeval_map_algebraMap]; exact root
  have dvd : minpoly (RatFunc Scalar) b.gen∣Q := minpoly.dvd _ _ rootQ
  have assoc := (minpoly.irreducible b.isIntegral_gen).associated_of_dvd irrQ dvd
  have oq : Q.natDegree=(minpoly (RatFunc Scalar) b.gen).natDegree :=
    le_antisymm (natDegree_le_of_dvd assoc.symm.dvd (minpoly.ne_zero b.isIntegral_gen))
      (natDegree_le_of_dvd dvd irrQ.ne_zero)
  have dim : P.natDegree=b.dim :=
    (natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial Scalar) (RatFunc Scalar)) P).symm.trans
      (oq.trans b.natDegree_minpoly)
  let seed : L→+*Scalar := (algebraMap (Polynomial L) Scalar).comp C
  letI : Infinite Scalar := Infinite.of_injective seed seed.injective
  haveI : CharP (RatFunc Scalar) K1.p :=
    charP_of_injective_ringHom ((RatFunc.C : Scalar→+*RatFunc Scalar).comp seed).injective K1.p
  have tame : (P.natDegree:RatFunc Scalar)≠0 := by
    intro zero
    have h := (CharP.cast_eq_zero_iff (RatFunc Scalar) K1.p P.natDegree).mp zero
    have lt : P.natDegree<K1.p := by rw [deg]; exact hi.trans (by decide)
    exact pd (Nat.eq_zero_of_dvd_of_lt h lt)
  exact clears_finite b P prim (by omega) dim tame root x int
end Actual
#print axioms clears_finite
#print axioms actual_finite
end
end Lower6960.MonicChart

end Merged_R6960MonicChartFinite

-- merged module R6960MonicChartInfinityClearing
section Merged_R6960MonicChartInfinityClearing

set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 3600000

namespace Lower6960.MonicChart
noncomputable section
open Polynomial Algebra
open scoped Polynomial Differential

private def scaleBasis {F E : Type*} [Field F] [Field E] [Algebra F E]
    (b : PowerBasis F E) (u : Fˣ) : PowerBasis F E where
  gen := algebraMap F E (u:F)*b.gen
  dim := b.dim
  basis := b.basis.unitsSMul (fun j=>u^j.val)
  basis_eq_pow j := by
    rw [Module.Basis.unitsSMul_apply,Units.smul_def,Units.val_pow_eq_pow_val,b.basis_eq_pow,
      Algebra.smul_def,map_pow,mul_pow]

section Infinity

variable {K E : Type*} [Field K] [Infinite K] [DecidableEq (RatFunc K)]
    [Field E] [Algebra (RatFunc K) E] [Algebra (Polynomial K) E]
    [IsScalarTower (Polynomial K) (RatFunc K) E]
    [Algebra (Infinity K) E] [IsScalarTower (Infinity K) (RatFunc K) E]
    [Algebra.IsSeparable (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
    [Differential (Infinity K)] [Differential E] [DifferentialAlgebra (Infinity K) E]

local notation "S" => Infinity K
local notation "F" => RatFunc K

private theorem primitive_unit_infty (p : (Polynomial (Polynomial K))) (prim : p.IsPrimitive) :
    ∃ i, IsUnit ((p.map (inftyRingEval K)).coeff i) := by
  by_contra! no
  have dvd : C (Polynomial.X : (Polynomial K))∣p := by
    apply (C_dvd_iff_dvd_coeff ..).mpr
    intro j
    apply X_dvd_iff.mpr
    by_contra nz
    exact no j (by rw [coeff_map]; exact inftyRingEval_isUnit _ nz)
  exact not_isUnit_X ((isPrimitive_iff_isUnit_of_C_dvd.mp prim) _ dvd)

/-- The weighted infinity chart controls derivatives by its own padded
resultant. Primitive part is taken before choosing the monic chart, and
its content factor is returned to the resultant. -/
theorem clears_homogeneous_infinity (b : PowerBasis F E) (f : (Polynomial (Polynomial K))) (H d : ℕ)
    (e2 : 2≤f.natDegree) (dim : f.natDegree=b.dim)
    (weights : ∀ i≤f.natDegree,(f.coeff i).natDegree+d*i≤H)
    (root : aeval b.gen f=0) (x : E) (hx : IsIntegral S x) :
    IsIntegral S (algebraMap S E ((inftyRingEval K (paddedRes (weightedInfinity f H d)))^2)*x′) := by
  classical
  letI : NormalizedGCDMonoid (Polynomial K) := Classical.choice inferInstance
  let e := f.natDegree
  let t := ((RatFunc.X : F)⁻¹)
  let a := t^d
  have an : a≠0 := pow_ne_zero _ (inv_ne_zero RatFunc.X_ne_zero)
  let v := scaleBasis b (Units.mk0 a an)
  have vg : v.gen=algebraMap F E a*b.gen := rfl
  have vd : v.dim=b.dim := rfl
  let fI := weightedInfinity f H d
  let j := inftyRingEval K
  let r := fI.map j
  let p := fI.primPart.map j
  let c := j fI.content
  let ι := algebraMap S F
  have rdegree : r.natDegree=e := (natDegree_map_eq_of_injective inftyRingEval_injective _).trans
    (infinity_degree f H d)
  have pdegree : p.natDegree=e := by
    rw [natDegree_map_eq_of_injective inftyRingEval_injective,natDegree_primPart,infinity_degree]
  have rawSplit : r=C c*p := by
    have eq := congrArg (Polynomial.map j) fI.eq_C_content_mul_primPart
    simpa only [Polynomial.map_mul,Polynomial.map_C] using eq
  have cn : c≠0 := by
    intro zero
    rw [rawSplit,zero,C_0,zero_mul,natDegree_zero] at rdegree
    omega
  have mapped_r : r.map ι=fI.map (AtInfinity K) := by
    rw [Polynomial.map_map]
    rfl
  have rroot : aeval v.gen r=0 := by
    rw [← aeval_map_algebraMap F,mapped_r,infinity_field f H d weights,map_mul]
    have baseRoot : aeval b.gen (f.map (algebraMap (Polynomial K) F))=0 := by
      rw [aeval_map_algebraMap]
      exact root
    have newRoot : aeval v.gen ((f.map (algebraMap (Polynomial K) F)).scaleRoots a)=0 := by
      rw [vg]
      exact scaleRoots_eval₂_eq_zero (algebraMap F E) baseRoot
    rw [newRoot,mul_zero]
  have proot : aeval v.gen p=0 := by
    rw [rawSplit,map_mul,aeval_C] at rroot
    have injective : Function.Injective (algebraMap S E) := by
      rw [IsScalarTower.algebraMap_eq S F E]
      exact (algebraMap F E).injective.comp (IsFractionRing.injective _ _)
    exact (mul_eq_zero.mp rroot).resolve_left ((map_ne_zero_iff _ injective).mpr cn)
  let emb : K→+*IsLocalRing.ResidueField S := (IsLocalRing.residue S).comp (j.comp C)
  letI : Infinite (IsLocalRing.ResidueField S) := Infinite.of_injective emb emb.injective
  have unit : ∃ i, IsUnit (p.coeff i) := primitive_unit_infty _ fI.isPrimitive_primPart
  have bounded := raw_square_clears_local v p unit (pdegree.trans (dim.trans vd.symm))
    (pdegree.symm ▸ e2) proot x hx
  have mapped_result : j (paddedRes fI)=paddedRes r := by
    unfold paddedRes
    rw [←resultant_map_map,←derivative_map]
    have d := natDegree_map_eq_of_injective inftyRingEval_injective fI
    rw [←d]
  have content_result : paddedRes r=c^(e+(e-1))*paddedRes p := by
    unfold paddedRes
    rw [rdegree,rawSplit,derivative_C_mul,resultant_C_mul_left,resultant_C_mul_right,←mul_assoc,←pow_add]
    rw [show e-1+e=e+(e-1) by omega,←pdegree]
  rw [mapped_result,content_result,mul_pow,map_mul,mul_assoc]
  exact isIntegral_algebraMap.mul bounded

end Infinity

#print axioms clears_homogeneous_infinity
end
end Lower6960.MonicChart

end Merged_R6960MonicChartInfinityClearing

-- merged module R6960MonicChartCoboundary
section Merged_R6960MonicChartCoboundary
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3600000
namespace Lower6960.MonicChart
noncomputable section
open Polynomial Algebra
open scoped Polynomial Differential
open Lower6960.RetainedCompression (derivative_weighted_add_le)
theorem inverse_abscissa_derivative {E : Type*} [Field E] [Differential E]
    (x : E) (coordinate : x′=1) : (x⁻¹)′=-(x⁻¹)^2 := by
  have h := (Differential.deriv (R:=E)).leibniz_inv x
  rw [coordinate,smul_eq_mul,mul_one] at h
  exact h
private theorem derivative_power_zero {E : Type*} [Field E] [Differential E]
    (p : ℕ) [CharP E p] (x : E) : (x^p)′=0 := by
  rw [Differential.deriv.leibniz_pow,nsmul_eq_mul,CharP.cast_eq_zero,zero_mul]
section Inverse
variable {K E : Type*} [Field K] [Infinite K] [DecidableEq (RatFunc K)]
    [Field E] [Algebra (RatFunc K) E] [Algebra (Polynomial K) E]
    [IsScalarTower (Polynomial K) (RatFunc K) E]
    [Algebra (Infinity K) E] [IsScalarTower (Infinity K) (RatFunc K) E]
    [Algebra.IsSeparable (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
    [Differential (Infinity K)] [Differential E] [DifferentialAlgebra (Infinity K) E]
local notation "S" => Infinity K
local notation "F" => RatFunc K
theorem clears_inverse_power (b : PowerBasis F E) (f : (Polynomial (Polynomial K))) (H d : ℕ)
    (e2 : 2≤f.natDegree) (dim : f.natDegree=b.dim) (tame : (f.natDegree:K)≠0)
    (weights : ∀ i≤f.natDegree,(f.coeff i).natDegree+d*i≤H)
    (resBound : (paddedRes f).natDegree≤resultantWidth f.natDegree H d)
    (nonzero : paddedRes f≠0) (root : aeval b.gen f=0) (x : E) (hx : IsIntegral S x) :
    IsIntegral S (algebraMap F E (((RatFunc.X : F)⁻¹)^
      (2*(resultantWidth f.natDegree H d-(paddedRes f).natDegree)))*x′) := by
  let r := resultantWidth f.natDegree H d-(paddedRes f).natDegree
  let t := inftyRingEval K (Polynomial.X : (Polynomial K))
  let u := inftyRingEval K (paddedRes f).reverse
  have co : ((paddedRes f).reverse).coeff 0≠0 := by
    rw [coeff_zero_reverse]
    exact leadingCoeff_ne_zero.mpr nonzero
  have unit : IsUnit u := inftyRingEval_isUnit _ co
  obtain ⟨w,hw⟩ := unit
  have hom := clears_homogeneous_infinity b f H d e2 dim weights root x hx
  rw [infinity_resultant f H d (by omega) tame weights resBound,
    reflected_local_factor _ _ resBound] at hom
  change IsIntegral S (algebraMap S E ((t^r*u)^2)*x′) at hom
  have cancel : (↑w⁻¹:S)^2*(t^r*u)^2=t^(2*r) := by
    have single : (↑w⁻¹:S)*(t^r*u)=t^r := by
      rw [←hw,mul_comm (↑w⁻¹:S),mul_assoc,Units.mul_inv,mul_one]
    rw [←mul_pow,single,←pow_mul,Nat.mul_comm]
  have mul := (isIntegral_algebraMap (x:=(↑w⁻¹:S)^2)).mul hom
  rw [←mul_assoc,←map_mul,cancel] at mul
  have loc : algebraMap S F t=(RatFunc.X : F)⁻¹ := mapped_X_infty
  rw [IsScalarTower.algebraMap_apply S F E,map_pow,loc] at mul
  exact mul
section Both
variable [Differential (Polynomial K)] [DifferentialAlgebra (Polynomial K) E]
theorem common_coboundary_zero_generic (b : PowerBasis F E) (f : (Polynomial (Polynomial K))) (H d p : ℕ)
    [CharP E p] (primitive : f.IsPrimitive) (e2 : 2≤f.natDegree) (dim : f.natDegree=b.dim)
    (tame : (f.natDegree:K)≠0)
    (weights : ∀ i≤f.natDegree,(f.coeff i).natDegree+d*i≤H)
    (resBound : (paddedRes f).natDegree≤resultantWidth f.natDegree H d)
    (widthRoom : 2*resultantWidth f.natDegree H d<p)
    (nonzero : paddedRes f≠0) (root : aeval b.gen f=0)
    (x y z : E) (fx : IsIntegral (Polynomial K) x) (iy : IsIntegral S y)
    (overlap : y=(algebraMap F E RatFunc.X)^p*x+z^p) :
    x′=0 := by
  let r := resultantWidth f.natDegree H d-(paddedRes f).natDegree
  let Xval := algebraMap F E (RatFunc.X : F)
  have xn : Xval≠0 := (map_ne_zero_iff _ (algebraMap F E).injective).mpr RatFunc.X_ne_zero
  have inv := clears_inverse_power b f H d e2 dim tame weights resBound nonzero root y iy
  have dv : y′=Xval^p*x′ := by
    rw [overlap,map_add,Differential.deriv.leibniz,derivative_power_zero p,
      derivative_power_zero p,smul_eq_mul,smul_eq_mul,mul_zero,add_zero,add_zero]
  rw [dv] at inv
  have le : 2*r≤p := by dsimp only [r]; omega
  have cancel : (Xval⁻¹)^(2*r)*Xval^p=Xval^(p-2*r) := by
    have e : p=2*r+(p-2*r) := (Nat.add_sub_of_le le).symm
    calc
      _ = (Xval⁻¹)^(2*r)*(Xval^(2*r)*Xval^(p-2*r)) := by
        rw [←pow_add,←e]
      _ = _ := by rw [←mul_assoc,←mul_pow,inv_mul_cancel₀ xn,one_pow,one_mul]
  have hi : IsIntegral S (Xval^(p-2*r)*x′) := by
    rw [←cancel,mul_assoc]
    change IsIntegral S (((algebraMap F E (RatFunc.X : F))⁻¹)^(2*r)*(Xval^p*x′))
    rw [←map_inv₀,←map_pow]
    exact inv
  have fit : 2*(paddedRes f).natDegree<p-2*r := by dsimp only [r]; omega
  have tame' : (f.natDegree:F)≠0 := by
    simpa only [map_natCast] using
      (map_ne_zero_iff (algebraMap K F) (algebraMap K F).injective).mpr tame
  exact DifferentialPoles.pole_budget (paddedRes f) nonzero (p-2*r) fit (x′)
    (clears_finite b f primitive e2 dim tame' root x fx) hi
end Both
end Inverse
#print axioms clears_inverse_power
#print axioms common_coboundary_zero_generic
end
end Lower6960.MonicChart

end Merged_R6960MonicChartCoboundary

-- merged module R6960MonicChartActual
section Merged_R6960MonicChartActual

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4200000

namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open K1_14 (L)
open RetainedCompression (Curve ordinate view view_y height heightCap wordDegree abscissa_coeff_height)
open scoped Polynomial Differential
open Lower6960.RetainedCompression (derivative_weighted_add_le)

private theorem width_at_cutoff (e d : ℕ) (pos : 0<e) :
    resultantWidth e (heightCap e d) d=(3*e-1)*(e-1)*d := by
  have mul : d*e≤heightCap e d := by
    unfold heightCap
    rw [mul_comm d e]
    exact Nat.mul_le_mul_right d (by omega)
  have eq := resultantWidth_eq (e:=e) (d:=d) pos mul
  have identity : (2*e-1)*heightCap e d=d*e^2+(3*e-1)*(e-1)*d := by
    obtain ⟨k,h⟩ := Nat.exists_eq_add_of_le (show 1≤e from pos)
    unfold heightCap
    rw [h,show 2*(1+k)-1=2*k+1 by omega,show 3*(1+k)-1=3*k+2 by omega,
      show 1+k-1=k by omega]
    ring
  omega

/-- For the actual bounded projected factor, the overlap of the finite
and infinity chart coefficients has zero derivative. The only overlap
input is their Frobenius relation in the root field. -/
theorem actual_coboundary_zero {E : Type*} [Field E] [DecidableEq (RatFunc Scalar)]
    [Algebra (RatFunc Scalar) E] [Algebra (Polynomial Scalar) E]
    [IsScalarTower (Polynomial Scalar) (RatFunc Scalar) E]
    [Algebra (Infinity Scalar) E] [IsScalarTower (Infinity Scalar) (RatFunc Scalar) E]
    [Algebra.IsSeparable (RatFunc Scalar) E] [FiniteDimensional (RatFunc Scalar) E]
    [Differential (Polynomial Scalar)] [Differential (Infinity Scalar)] [Differential E]
    [DifferentialAlgebra (Polynomial Scalar) E] [DifferentialAlgebra (Infinity Scalar) E]
    (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48)
    (bounded : height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree)
    (b : PowerBasis (RatFunc Scalar) E) (root : aeval b.gen (RetainedLinear.toSeed (view f))=0)
    (x y z : E) (fx : IsIntegral (Polynomial Scalar) x) (iy : IsIntegral (Infinity Scalar) y)
    (overlap : y=(algebraMap (RatFunc Scalar) E RatFunc.X)^K1.p*x+z^K1.p) :
    x′=0 := by
  let seed : L→+*Scalar := (algebraMap (Polynomial L) Scalar).comp C
  letI : Infinite Scalar := Infinite.of_injective seed seed.injective
  letI : CharP Scalar K1.p := charP_of_injective_ringHom seed.injective K1.p
  let inE : Scalar→+*E := (algebraMap (RatFunc Scalar) E).comp RatFunc.C
  letI : CharP E K1.p := charP_of_injective_ringHom inE.injective K1.p
  let P := RetainedLinear.toSeed (view f)
  let e := f.degreeOf ordinate
  let H := heightCap e wordDegree
  have deg : P.natDegree=e := (RetainedLinear.toSeed_degree _).trans (view_y _)
  have e2 : 2≤P.natDegree := by omega
  have ep : 0<P.natDegree := by omega
  have pir : Irreducible P := RetainedLinear.toSeed_irreducible
    ((MulEquiv.irreducible_iff view).mpr ir) (by rw [view_y]; omega)
  have tame : (P.natDegree:Scalar)≠0 := by
    intro zero
    have dvd := (CharP.cast_eq_zero_iff Scalar K1.p P.natDegree).mp zero
    exact ep.ne' (Nat.eq_zero_of_dvd_of_lt dvd (deg.symm ▸ hi.trans (by decide)))
  have coefficient (j : ℕ) : (P.coeff j).natDegree=((view f).coeff j).natDegree := by
    unfold P RetainedLinear.toSeed
    simp only [coe_mapRingHom,coeff_map,natDegree_map_eq_of_injective (RetainedLinear.incl_injective L)]
  have weights (j : ℕ) (jle : j≤P.natDegree) :
      (P.coeff j).natDegree+wordDegree*j≤H := by
    rw [coefficient]
    by_cases zero : (view f).coeff j=0
    · rw [zero,natDegree_zero,zero_add,mul_comm wordDegree]
      exact Nat.mul_le_mul_right _ (by omega)
    exact (abscissa_coeff_height f wordDegree j zero).trans bounded
  have Hfit : wordDegree*P.natDegree≤H :=
    (Nat.le_add_left ..).trans (weights _ le_rfl)
  have resBound : (paddedRes P).natDegree≤resultantWidth P.natDegree H wordDegree := by
    have h := Lower6960.RetainedCompression.derivative_weighted_add_le P P.natDegree
      H wordDegree ep weights
    have eq := resultantWidth_eq (e:=P.natDegree) (d:=wordDegree) (H:=H) ep Hfit
    exact Nat.le_of_add_le_add_right (h.trans_eq eq.symm)
  have room : 2*resultantWidth P.natDegree H wordDegree<K1.p := by
    rw [deg,width_at_cutoff e wordDegree (by omega)]
    exact (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right wordDegree
      (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 3 (by omega : e≤47)) 1)
       (Nat.sub_le_sub_right (by omega : e≤47) 1)))).trans_lt (by decide +kernel)
  have tameA : (P.natDegree:(Polynomial Scalar))≠0 := by
    simpa only [map_natCast] using
      (map_ne_zero_iff (Polynomial.C : Scalar→+*(Polynomial Scalar)) Polynomial.C_injective).mpr tame
  have dp := derivative_degree P ep tameA
  have der : P.derivative≠0 := by intro zero; rw [zero,natDegree_zero] at dp; omega
  have resNZ : paddedRes P≠0 := Polynomial.resultant_derivative_ne_zero_of_irreducible P pir der
  have prim := pir.isPrimitive ep.ne'
  let ι := algebraMap (Polynomial Scalar) (RatFunc Scalar)
  let Q := P.map ι
  have iq : Irreducible Q := prim.irreducible_iff_irreducible_map_fraction_map.mp pir
  have rq : aeval b.gen Q=0 := by rw [aeval_map_algebraMap]; exact root
  have dvd : minpoly (RatFunc Scalar) b.gen∣Q := minpoly.dvd _ _ rq
  have associated := (minpoly.irreducible b.isIntegral_gen).associated_of_dvd iq dvd
  have size : Q.natDegree=(minpoly (RatFunc Scalar) b.gen).natDegree :=
    le_antisymm (natDegree_le_of_dvd associated.symm.dvd (minpoly.ne_zero b.isIntegral_gen))
      (natDegree_le_of_dvd dvd iq.ne_zero)
  have dimension : P.natDegree=b.dim :=
    (natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial Scalar) (RatFunc Scalar)) P).symm.trans
      (size.trans b.natDegree_minpoly)
  exact common_coboundary_zero_generic b P H wordDegree K1.p prim e2 dimension tame weights
    resBound room resNZ root x y z fx iy overlap

#print axioms actual_coboundary_zero
end
end Lower6960.MonicChart

end Merged_R6960MonicChartActual
