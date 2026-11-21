import ProximityPrize.SubmissionLower.Low52At2390PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low52At2390PriceTableOne7
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low52At2390Price (fullCap)
open Low52At2390PriceCaps (Band start)
open Low52At2390PriceTableBase (Covered)
open Low52At2390PriceTableCover (PaidBatch packedBatch tilesOf checks checks_join Certificate)

namespace Top1
private def b0 : PaidBatch .one7 1 := packedBatch [5943199236,5695738380,12721200148,24356205092] (by decide +kernel)
private def batches : List (PaidBatch .one7 1) := [b0]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 124 3 44 = true := by decide +kernel
def receipt : Certificate .one7 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch .one7 2 := packedBatch [13224512520,12461154840,23282464292] (by decide +kernel)
private def batches : List (PaidBatch .one7 2) := [b0]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 124 6 41 = true := by decide +kernel
def receipt : Certificate .one7 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch .one7 3 := packedBatch [11353854476,12196914716,23014029352] (by decide +kernel)
private def batches : List (PaidBatch .one7 3) := [b0]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 124 9 38 = true := by decide +kernel
def receipt : Certificate .one7 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch .one7 4 := packedBatch [22405847056,21940288552] (by decide +kernel)
private def batches : List (PaidBatch .one7 4) := [b0]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 124 12 35 = true := by decide +kernel
def receipt : Certificate .one7 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch .one7 5 := packedBatch [19188817428,21671853612] (by decide +kernel)
private def batches : List (PaidBatch .one7 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 124 15 32 = true := by decide +kernel
def receipt : Certificate .one7 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch .one7 6 := packedBatch [18391901208,20598112812] (by decide +kernel)
private def batches : List (PaidBatch .one7 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 124 18 29 = true := by decide +kernel
def receipt : Certificate .one7 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch .one7 7 := packedBatch [16785484316,20061242416] (by decide +kernel)
private def batches : List (PaidBatch .one7 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 124 21 26 = true := by decide +kernel
def receipt : Certificate .one7 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch .one7 8 := packedBatch [16525439008,18987501616] (by decide +kernel)
private def batches : List (PaidBatch .one7 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 124 24 23 = true := by decide +kernel
def receipt : Certificate .one7 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch .one7 9 := packedBatch [25698383396] (by decide +kernel)
private def batches : List (PaidBatch .one7 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 124 27 20 = true := by decide +kernel
def receipt : Certificate .one7 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch .one7 10 := packedBatch [23014030376] (by decide +kernel)
private def batches : List (PaidBatch .one7 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 124 30 17 = true := by decide +kernel
def receipt : Certificate .one7 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch .one7 11 := packedBatch [20866548268] (by decide +kernel)
private def batches : List (PaidBatch .one7 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 124 33 14 = true := by decide +kernel
def receipt : Certificate .one7 11 := ⟨batches, i33⟩
end Top11

namespace Top12
private def b0 : PaidBatch .one7 12 := packedBatch [18987501616] (by decide +kernel)
private def batches : List (PaidBatch .one7 12) := [b0]
private abbrev tiles := tilesOf batches
private theorem i36 : checks tiles 124 36 11 = true := by decide +kernel
def receipt : Certificate .one7 12 := ⟨batches, i36⟩
end Top12

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .one7).plus a) (fullCap top)) : Covered top .one7 a := by
  change 3+a.b ≤ 127 ∧ 7+a.j ≤ 53 ∧ 1+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 124 := by omega
  have hj' : a.j ≤ 46 := by omega
  have hcases : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 ∨ a.t = 12 := by omega
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
  · exact Certificate.apply Top1.receipt a ha h1 hb' hj' ht htop
  · exact Certificate.apply Top2.receipt a ha h2 hb' hj' ht htop
  · exact Certificate.apply Top3.receipt a ha h3 hb' hj' ht htop
  · exact Certificate.apply Top4.receipt a ha h4 hb' hj' ht htop
  · exact Certificate.apply Top5.receipt a ha h5 hb' hj' ht htop
  · exact Certificate.apply Top6.receipt a ha h6 hb' hj' ht htop
  · exact Certificate.apply Top7.receipt a ha h7 hb' hj' ht htop
  · exact Certificate.apply Top8.receipt a ha h8 hb' hj' ht htop
  · exact Certificate.apply Top9.receipt a ha h9 hb' hj' ht htop
  · exact Certificate.apply Top10.receipt a ha h10 hb' hj' ht htop
  · exact Certificate.apply Top11.receipt a ha h11 hb' hj' ht htop
  · exact Certificate.apply Top12.receipt a ha h12 hb' hj' ht htop

end Low52At2390PriceTableOne7
