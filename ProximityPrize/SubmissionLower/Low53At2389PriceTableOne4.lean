import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableOne4
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Top1
private def b0 : PaidBatch .one4 1 := ⟨[
  .rectangle 1 3 127 3 1,
  .rectangle 2 4 127 4 2,
  .rectangle 2 5 127 5 4], by decide +kernel⟩
private def b1 : PaidBatch .one4 1 := ⟨[
  .rectangle 2 6 127 8 11,
  .rectangle 3 9 127 14 25,
  .rectangle 5 15 66 26 26], by decide +kernel⟩
private def b2 : PaidBatch .one4 1 := ⟨[
  .rectangle 9 27 68 49 44,
  .rectangle 67 15 127 26 52,
  .rectangle 69 39 98 49 48], by decide +kernel⟩
private def b3 : PaidBatch .one4 1 := ⟨[
  .rectangle 69 27 127 38 59,
  .rectangle 99 39 127 44 54,
  .rectangle 99 45 127 49 57], by decide +kernel⟩
private def batches : List (PaidBatch .one4 1) := [b0, b1, b2, b3]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 127 3 33 = true := by decide +kernel
private theorem i36 : checks tiles 127 36 14 = true := by decide +kernel
def receipt : Certificate .one4 1 := ⟨batches, checks_join i3 i36⟩
end Top1

namespace Top2
private def b0 : PaidBatch .one4 2 := ⟨[
  .rectangle 2 6 127 11 23,
  .rectangle 4 12 127 16 25,
  .rectangle 6 17 127 27 50], by decide +kernel⟩
private def b1 : PaidBatch .one4 2 := ⟨[
  .rectangle 10 28 68 49 46,
  .rectangle 69 39 98 49 51,
  .rectangle 69 28 127 38 59], by decide +kernel⟩
private def b2 : PaidBatch .one4 2 := ⟨[
  .rectangle 99 39 127 44 55,
  .rectangle 99 45 127 49 59], by decide +kernel⟩
private def batches : List (PaidBatch .one4 2) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 127 6 44 = true := by decide +kernel
def receipt : Certificate .one4 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch .one4 3 := ⟨[
  .rectangle 3 9 127 14 25,
  .rectangle 5 15 127 19 28,
  .rectangle 7 20 127 29 50], by decide +kernel⟩
private def b1 : PaidBatch .one4 3 := ⟨[
  .rectangle 10 30 68 49 46,
  .rectangle 69 40 98 49 51,
  .rectangle 69 30 127 39 59], by decide +kernel⟩
private def b2 : PaidBatch .one4 3 := ⟨[
  .rectangle 99 40 127 44 55,
  .rectangle 99 45 127 49 60], by decide +kernel⟩
private def batches : List (PaidBatch .one4 3) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 127 9 41 = true := by decide +kernel
def receipt : Certificate .one4 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch .one4 4 := ⟨[
  .rectangle 4 12 127 21 44,
  .rectangle 8 22 127 30 49,
  .rectangle 11 31 69 49 47], by decide +kernel⟩
private def b1 : PaidBatch .one4 4 := ⟨[
  .rectangle 70 41 98 49 52,
  .rectangle 70 31 127 40 61,
  .rectangle 99 41 127 45 58], by decide +kernel⟩
private def b2 : PaidBatch .one4 4 := ⟨[
  .rectangle 99 46 127 49 60], by decide +kernel⟩
private def batches : List (PaidBatch .one4 4) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 127 12 38 = true := by decide +kernel
def receipt : Certificate .one4 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch .one4 5 := ⟨[
  .rectangle 5 15 127 23 42,
  .rectangle 8 24 127 32 51,
  .rectangle 11 33 69 49 46], by decide +kernel⟩
private def b1 : PaidBatch .one4 5 := ⟨[
  .rectangle 70 42 98 49 52,
  .rectangle 70 33 127 41 61,
  .rectangle 99 42 127 45 57], by decide +kernel⟩
private def b2 : PaidBatch .one4 5 := ⟨[
  .rectangle 99 46 127 49 61], by decide +kernel⟩
private def batches : List (PaidBatch .one4 5) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 127 15 35 = true := by decide +kernel
def receipt : Certificate .one4 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch .one4 6 := ⟨[
  .rectangle 6 18 127 25 41,
  .rectangle 9 26 127 33 50,
  .rectangle 12 34 69 49 46], by decide +kernel⟩
private def b1 : PaidBatch .one4 6 := ⟨[
  .rectangle 70 42 98 49 53,
  .rectangle 70 34 127 41 59,
  .rectangle 99 42 127 45 58], by decide +kernel⟩
private def b2 : PaidBatch .one4 6 := ⟨[
  .rectangle 99 46 127 49 62], by decide +kernel⟩
private def batches : List (PaidBatch .one4 6) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 127 18 32 = true := by decide +kernel
def receipt : Certificate .one4 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch .one4 7 := ⟨[
  .rectangle 7 21 127 28 44,
  .rectangle 10 29 127 35 51,
  .rectangle 12 36 69 49 45], by decide +kernel⟩
private def b1 : PaidBatch .one4 7 := ⟨[
  .rectangle 70 43 98 49 52,
  .rectangle 70 36 127 42 59,
  .rectangle 99 43 127 46 59], by decide +kernel⟩
private def b2 : PaidBatch .one4 7 := ⟨[
  .rectangle 99 47 127 49 61], by decide +kernel⟩
private def batches : List (PaidBatch .one4 7) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 127 21 29 = true := by decide +kernel
def receipt : Certificate .one4 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch .one4 8 := ⟨[
  .rectangle 8 24 67 36 36,
  .rectangle 13 37 70 49 45,
  .rectangle 68 24 127 30 45], by decide +kernel⟩
private def b1 : PaidBatch .one4 8 := ⟨[
  .rectangle 68 31 127 36 50,
  .rectangle 71 44 99 49 52,
  .rectangle 71 37 127 43 61], by decide +kernel⟩
private def b2 : PaidBatch .one4 8 := ⟨[
  .rectangle 100 44 127 46 58,
  .rectangle 100 47 127 49 62], by decide +kernel⟩
private def batches : List (PaidBatch .one4 8) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 127 24 26 = true := by decide +kernel
def receipt : Certificate .one4 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch .one4 9 := ⟨[
  .rectangle 9 27 68 38 36,
  .rectangle 13 39 70 49 43,
  .rectangle 69 27 127 32 45], by decide +kernel⟩
private def b1 : PaidBatch .one4 9 := ⟨[
  .rectangle 69 33 127 38 53,
  .rectangle 71 45 99 49 51,
  .rectangle 71 39 127 44 60], by decide +kernel⟩
private def b2 : PaidBatch .one4 9 := ⟨[
  .rectangle 100 45 127 49 65], by decide +kernel⟩
private def batches : List (PaidBatch .one4 9) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 127 27 23 = true := by decide +kernel
def receipt : Certificate .one4 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch .one4 10 := ⟨[
  .rectangle 10 30 68 39 34,
  .rectangle 14 40 70 49 42,
  .rectangle 69 30 127 39 61], by decide +kernel⟩
private def b1 : PaidBatch .one4 10 := ⟨[
  .rectangle 71 45 99 49 51,
  .rectangle 71 40 127 44 59,
  .rectangle 100 45 127 49 65], by decide +kernel⟩
private def batches : List (PaidBatch .one4 10) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 127 30 20 = true := by decide +kernel
def receipt : Certificate .one4 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch .one4 11 := ⟨[
  .rectangle 11 33 69 49 51,
  .rectangle 70 42 98 49 55,
  .rectangle 70 33 127 41 62], by decide +kernel⟩
private def b1 : PaidBatch .one4 11 := ⟨[
  .rectangle 99 42 127 45 59,
  .rectangle 99 46 127 49 64], by decide +kernel⟩
private def batches : List (PaidBatch .one4 11) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 127 33 17 = true := by decide +kernel
def receipt : Certificate .one4 11 := ⟨batches, i33⟩
end Top11

namespace Top12
private def b0 : PaidBatch .one4 12 := ⟨[
  .rectangle 12 36 69 49 47,
  .rectangle 70 43 98 49 53,
  .rectangle 70 36 127 42 59], by decide +kernel⟩
private def b1 : PaidBatch .one4 12 := ⟨[
  .rectangle 99 43 127 46 60,
  .rectangle 99 47 127 49 62], by decide +kernel⟩
private def batches : List (PaidBatch .one4 12) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i36 : checks tiles 127 36 14 = true := by decide +kernel
def receipt : Certificate .one4 12 := ⟨batches, i36⟩
end Top12

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .one4).plus a) (fullCap top)) : Covered top .one4 a := by
  change 2+a.b ≤ 129 ∧ 4+a.j ≤ 53 ∧ 1+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 127 := by omega
  have hj' : a.j ≤ 49 := by omega
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

end Low53At2389PriceTableOne4
