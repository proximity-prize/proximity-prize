import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableTwoBand22
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Band22
namespace Top1
private def b0 : PaidBatch (.two7 1) 1 := ⟨[
  .rectangle 1 3 125 8 40,
  .rectangle 3 9 125 13 38,
  .rectangle 5 14 125 24 84], by decide +kernel⟩
private def b1 : PaidBatch (.two7 1) 1 := ⟨[
  .rectangle 9 25 67 46 76,
  .rectangle 68 36 96 46 82,
  .rectangle 68 25 125 35 97], by decide +kernel⟩
private def b2 : PaidBatch (.two7 1) 1 := ⟨[
  .rectangle 97 36 125 41 90,
  .rectangle 97 42 125 46 96], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 1) 1) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 125 3 44 = true := by decide +kernel
def receipt : Certificate (.two7 1) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two7 1) 2 := ⟨[
  .rectangle 2 6 125 16 89,
  .rectangle 6 17 125 26 82,
  .rectangle 9 27 67 46 75], by decide +kernel⟩
private def b1 : PaidBatch (.two7 1) 2 := ⟨[
  .rectangle 68 37 96 46 83,
  .rectangle 68 27 125 36 97,
  .rectangle 97 37 125 41 90], by decide +kernel⟩
private def b2 : PaidBatch (.two7 1) 2 := ⟨[
  .rectangle 97 42 125 46 98], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 1) 2) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 125 6 41 = true := by decide +kernel
def receipt : Certificate (.two7 1) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two7 1) 3 := ⟨[
  .rectangle 3 9 125 18 74,
  .rectangle 7 19 125 27 79,
  .rectangle 10 28 67 46 77], by decide +kernel⟩
private def b1 : PaidBatch (.two7 1) 3 := ⟨[
  .rectangle 68 38 96 46 83,
  .rectangle 68 28 125 37 100,
  .rectangle 97 38 125 42 93], by decide +kernel⟩
private def b2 : PaidBatch (.two7 1) 3 := ⟨[
  .rectangle 97 43 125 46 98], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 1) 3) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 125 9 38 = true := by decide +kernel
def receipt : Certificate (.two7 1) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two7 1) 4 := ⟨[
  .rectangle 4 12 125 20 68,
  .rectangle 7 21 125 29 83,
  .rectangle 10 30 67 46 74], by decide +kernel⟩
private def b1 : PaidBatch (.two7 1) 4 := ⟨[
  .rectangle 68 30 125 38 99,
  .rectangle 68 39 125 46 110], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 1) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 125 12 35 = true := by decide +kernel
def receipt : Certificate (.two7 1) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two7 1) 5 := ⟨[
  .rectangle 5 15 125 22 66,
  .rectangle 8 23 125 30 81,
  .rectangle 11 31 68 46 75], by decide +kernel⟩
private def b1 : PaidBatch (.two7 1) 5 := ⟨[
  .rectangle 69 39 97 46 85,
  .rectangle 69 31 125 38 96,
  .rectangle 98 39 125 46 111], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 1) 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 125 15 32 = true := by decide +kernel
def receipt : Certificate (.two7 1) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two7 1) 6 := ⟨[
  .rectangle 6 18 125 25 71,
  .rectangle 9 26 125 32 81,
  .rectangle 11 33 68 46 72], by decide +kernel⟩
private def b1 : PaidBatch (.two7 1) 6 := ⟨[
  .rectangle 69 33 125 39 95,
  .rectangle 69 40 125 46 108], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 1) 6) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 125 18 29 = true := by decide +kernel
def receipt : Certificate (.two7 1) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two7 1) 7 := ⟨[
  .rectangle 7 21 66 33 58,
  .rectangle 12 34 68 46 71,
  .rectangle 67 21 125 33 107], by decide +kernel⟩
private def b1 : PaidBatch (.two7 1) 7 := ⟨[
  .rectangle 69 34 125 40 97,
  .rectangle 69 41 125 46 106], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 1) 7) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 125 21 26 = true := by decide +kernel
def receipt : Certificate (.two7 1) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two7 1) 8 := ⟨[
  .rectangle 8 24 125 35 105,
  .rectangle 12 36 68 46 68,
  .rectangle 69 36 125 41 96], by decide +kernel⟩
private def b1 : PaidBatch (.two7 1) 8 := ⟨[
  .rectangle 69 42 125 46 104], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 1) 8) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 125 24 23 = true := by decide +kernel
def receipt : Certificate (.two7 1) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two7 1) 9 := ⟨[
  .rectangle 9 27 125 36 98,
  .rectangle 13 37 69 46 67,
  .rectangle 70 37 125 41 93], by decide +kernel⟩
private def b1 : PaidBatch (.two7 1) 9 := ⟨[
  .rectangle 70 42 125 46 104], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 1) 9) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 125 27 20 = true := by decide +kernel
def receipt : Certificate (.two7 1) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two7 1) 10 := ⟨[
  .rectangle 10 30 67 46 81,
  .rectangle 68 39 96 46 87,
  .rectangle 68 30 125 38 98], by decide +kernel⟩
private def b1 : PaidBatch (.two7 1) 10 := ⟨[
  .rectangle 97 39 125 42 92,
  .rectangle 97 43 125 46 101], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 1) 10) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 125 30 17 = true := by decide +kernel
def receipt : Certificate (.two7 1) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two7 1) 11 := ⟨[
  .rectangle 11 33 68 46 75,
  .rectangle 69 33 125 39 93,
  .rectangle 69 40 125 46 109], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 1) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 125 33 14 = true := by decide +kernel
def receipt : Certificate (.two7 1) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two7 1)).plus a) (fullCap top)) : Covered top (.two7 1) a := by
  change 4+a.b ≤ 129 ∧ 7+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 125 := by omega
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
end Band22


end Low53At2389PriceTableTwoBand22
