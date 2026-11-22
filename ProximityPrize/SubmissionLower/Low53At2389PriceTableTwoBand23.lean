import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableTwoBand23
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Band23
namespace Top1
private def b0 : PaidBatch (.two7 2) 1 := ⟨[
  .rectangle 1 3 124 8 40,
  .rectangle 3 9 124 13 37,
  .rectangle 5 14 124 24 83], by decide +kernel⟩
private def b1 : PaidBatch (.two7 2) 1 := ⟨[
  .rectangle 9 25 66 46 74,
  .rectangle 67 25 124 35 96,
  .rectangle 67 36 124 46 111], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 2) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 124 3 44 = true := by decide +kernel
def receipt : Certificate (.two7 2) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two7 2) 2 := ⟨[
  .rectangle 2 6 124 16 88,
  .rectangle 6 17 124 26 81,
  .rectangle 9 27 66 46 74], by decide +kernel⟩
private def b1 : PaidBatch (.two7 2) 2 := ⟨[
  .rectangle 67 27 124 36 96,
  .rectangle 67 37 124 46 111], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 2) 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 124 6 41 = true := by decide +kernel
def receipt : Certificate (.two7 2) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two7 2) 3 := ⟨[
  .rectangle 3 9 124 18 74,
  .rectangle 7 19 124 27 79,
  .rectangle 10 28 67 46 77], by decide +kernel⟩
private def b1 : PaidBatch (.two7 2) 3 := ⟨[
  .rectangle 68 28 124 37 99,
  .rectangle 68 38 124 46 110], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 2) 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 124 9 38 = true := by decide +kernel
def receipt : Certificate (.two7 2) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two7 2) 4 := ⟨[
  .rectangle 4 12 124 20 68,
  .rectangle 7 21 124 29 82,
  .rectangle 10 30 67 46 74], by decide +kernel⟩
private def b1 : PaidBatch (.two7 2) 4 := ⟨[
  .rectangle 68 30 124 38 98,
  .rectangle 68 39 124 46 109], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 2) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 124 12 35 = true := by decide +kernel
def receipt : Certificate (.two7 2) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two7 2) 5 := ⟨[
  .rectangle 5 15 124 22 65,
  .rectangle 8 23 124 30 80,
  .rectangle 11 31 67 46 74], by decide +kernel⟩
private def b1 : PaidBatch (.two7 2) 5 := ⟨[
  .rectangle 68 31 124 38 95,
  .rectangle 68 39 124 46 110], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 2) 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 124 15 32 = true := by decide +kernel
def receipt : Certificate (.two7 2) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two7 2) 6 := ⟨[
  .rectangle 6 18 124 25 70,
  .rectangle 9 26 124 32 80,
  .rectangle 11 33 67 46 71], by decide +kernel⟩
private def b1 : PaidBatch (.two7 2) 6 := ⟨[
  .rectangle 68 33 124 39 94,
  .rectangle 68 40 124 46 108], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 2) 6) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 124 18 29 = true := by decide +kernel
def receipt : Certificate (.two7 2) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two7 2) 7 := ⟨[
  .rectangle 7 21 124 33 106,
  .rectangle 12 34 68 46 71,
  .rectangle 69 34 124 40 96], by decide +kernel⟩
private def b1 : PaidBatch (.two7 2) 7 := ⟨[
  .rectangle 69 41 124 46 105], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 2) 7) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 124 21 26 = true := by decide +kernel
def receipt : Certificate (.two7 2) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two7 2) 8 := ⟨[
  .rectangle 8 24 124 35 104,
  .rectangle 12 36 68 46 68,
  .rectangle 69 36 124 41 95], by decide +kernel⟩
private def b1 : PaidBatch (.two7 2) 8 := ⟨[
  .rectangle 69 42 124 46 103], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 2) 8) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 124 24 23 = true := by decide +kernel
def receipt : Certificate (.two7 2) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two7 2) 9 := ⟨[
  .rectangle 9 27 124 36 97,
  .rectangle 13 37 68 46 66,
  .rectangle 69 37 124 41 92], by decide +kernel⟩
private def b1 : PaidBatch (.two7 2) 9 := ⟨[
  .rectangle 69 42 124 46 103], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 2) 9) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 124 27 20 = true := by decide +kernel
def receipt : Certificate (.two7 2) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two7 2) 10 := ⟨[
  .rectangle 10 30 67 46 81,
  .rectangle 68 30 124 38 97,
  .rectangle 68 39 124 46 111], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 2) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 124 30 17 = true := by decide +kernel
def receipt : Certificate (.two7 2) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two7 2) 11 := ⟨[
  .rectangle 11 33 67 46 74,
  .rectangle 68 33 124 39 93,
  .rectangle 68 40 124 46 108], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 2) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 124 33 14 = true := by decide +kernel
def receipt : Certificate (.two7 2) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two7 2)).plus a) (fullCap top)) : Covered top (.two7 2) a := by
  change 5+a.b ≤ 129 ∧ 7+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 124 := by omega
  have hj' : a.j ≤ 46 := by omega
  have hcases : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 := by omega
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
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
end Band23


end Low53At2389PriceTableTwoBand23
