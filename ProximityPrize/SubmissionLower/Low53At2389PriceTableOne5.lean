import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableOne5
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Top1
private def b0 : PaidBatch .one5 1 := ⟨[
  .rectangle 1 3 127 5 7,
  .rectangle 2 6 127 8 12,
  .rectangle 3 9 127 14 26], by decide +kernel⟩
private def b1 : PaidBatch .one5 1 := ⟨[
  .rectangle 5 15 127 25 50,
  .rectangle 9 26 68 48 46,
  .rectangle 69 26 127 37 62], by decide +kernel⟩
private def b2 : PaidBatch .one5 1 := ⟨[
  .rectangle 69 38 127 48 68], by decide +kernel⟩
private def batches : List (PaidBatch .one5 1) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 127 3 46 = true := by decide +kernel
def receipt : Certificate .one5 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch .one5 2 := ⟨[
  .rectangle 2 6 127 11 24,
  .rectangle 4 12 127 16 26,
  .rectangle 6 17 127 27 53], by decide +kernel⟩
private def b1 : PaidBatch .one5 2 := ⟨[
  .rectangle 10 28 68 48 47,
  .rectangle 69 28 127 38 62,
  .rectangle 69 39 127 48 69], by decide +kernel⟩
private def batches : List (PaidBatch .one5 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 127 6 43 = true := by decide +kernel
def receipt : Certificate .one5 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch .one5 3 := ⟨[
  .rectangle 3 9 127 18 45,
  .rectangle 7 19 127 28 51,
  .rectangle 10 29 68 48 48], by decide +kernel⟩
private def b1 : PaidBatch .one5 3 := ⟨[
  .rectangle 69 29 127 38 61,
  .rectangle 69 39 127 48 70], by decide +kernel⟩
private def batches : List (PaidBatch .one5 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 127 9 40 = true := by decide +kernel
def receipt : Certificate .one5 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch .one5 4 := ⟨[
  .rectangle 4 12 127 21 46,
  .rectangle 8 22 127 30 51,
  .rectangle 11 31 69 48 48], by decide +kernel⟩
private def b1 : PaidBatch .one5 4 := ⟨[
  .rectangle 70 31 127 39 61,
  .rectangle 70 40 127 48 70], by decide +kernel⟩
private def batches : List (PaidBatch .one5 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 127 12 37 = true := by decide +kernel
def receipt : Certificate .one5 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch .one5 5 := ⟨[
  .rectangle 5 15 127 23 44,
  .rectangle 8 24 127 31 50,
  .rectangle 11 32 69 48 48], by decide +kernel⟩
private def b1 : PaidBatch .one5 5 := ⟨[
  .rectangle 70 32 127 40 63,
  .rectangle 70 41 127 48 69], by decide +kernel⟩
private def batches : List (PaidBatch .one5 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 127 15 34 = true := by decide +kernel
def receipt : Certificate .one5 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch .one5 6 := ⟨[
  .rectangle 6 18 127 25 43,
  .rectangle 9 26 127 33 53,
  .rectangle 12 34 69 48 47], by decide +kernel⟩
private def b1 : PaidBatch .one5 6 := ⟨[
  .rectangle 70 34 127 41 62,
  .rectangle 70 42 127 48 69], by decide +kernel⟩
private def batches : List (PaidBatch .one5 6) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 127 18 31 = true := by decide +kernel
def receipt : Certificate .one5 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch .one5 7 := ⟨[
  .rectangle 7 21 127 27 43,
  .rectangle 10 28 127 34 52,
  .rectangle 12 35 69 48 46], by decide +kernel⟩
private def b1 : PaidBatch .one5 7 := ⟨[
  .rectangle 70 35 127 41 61,
  .rectangle 70 42 127 48 69], by decide +kernel⟩
private def batches : List (PaidBatch .one5 7) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 127 21 28 = true := by decide +kernel
def receipt : Certificate .one5 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch .one5 8 := ⟨[
  .rectangle 8 24 67 36 37,
  .rectangle 13 37 70 48 45,
  .rectangle 68 24 127 36 68], by decide +kernel⟩
private def b1 : PaidBatch .one5 8 := ⟨[
  .rectangle 71 37 127 42 60,
  .rectangle 71 43 127 48 68], by decide +kernel⟩
private def batches : List (PaidBatch .one5 8) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 127 24 25 = true := by decide +kernel
def receipt : Certificate .one5 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch .one5 9 := ⟨[
  .rectangle 9 27 127 37 64,
  .rectangle 13 38 70 48 44,
  .rectangle 71 38 127 43 62], by decide +kernel⟩
private def b1 : PaidBatch .one5 9 := ⟨[
  .rectangle 71 44 127 48 67], by decide +kernel⟩
private def batches : List (PaidBatch .one5 9) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 127 27 22 = true := by decide +kernel
def receipt : Certificate .one5 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch .one5 10 := ⟨[
  .rectangle 10 30 68 48 55,
  .rectangle 69 40 98 48 58,
  .rectangle 69 30 127 39 64], by decide +kernel⟩
private def b1 : PaidBatch .one5 10 := ⟨[
  .rectangle 99 40 127 44 61,
  .rectangle 99 45 127 48 65], by decide +kernel⟩
private def batches : List (PaidBatch .one5 10) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 127 30 19 = true := by decide +kernel
def receipt : Certificate .one5 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch .one5 11 := ⟨[
  .rectangle 11 33 69 48 51,
  .rectangle 70 41 98 48 56,
  .rectangle 70 33 127 40 61], by decide +kernel⟩
private def b1 : PaidBatch .one5 11 := ⟨[
  .rectangle 99 41 127 48 72], by decide +kernel⟩
private def batches : List (PaidBatch .one5 11) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 127 33 16 = true := by decide +kernel
def receipt : Certificate .one5 11 := ⟨batches, i33⟩
end Top11

namespace Top12
private def b0 : PaidBatch .one5 12 := ⟨[
  .rectangle 12 36 69 48 47,
  .rectangle 70 36 127 42 62,
  .rectangle 70 43 127 48 68], by decide +kernel⟩
private def batches : List (PaidBatch .one5 12) := [b0]
private abbrev tiles := tilesOf batches
private theorem i36 : checks tiles 127 36 13 = true := by decide +kernel
def receipt : Certificate .one5 12 := ⟨batches, i36⟩
end Top12

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .one5).plus a) (fullCap top)) : Covered top .one5 a := by
  change 2+a.b ≤ 129 ∧ 5+a.j ≤ 53 ∧ 1+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 127 := by omega
  have hj' : a.j ≤ 48 := by omega
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

end Low53At2389PriceTableOne5
