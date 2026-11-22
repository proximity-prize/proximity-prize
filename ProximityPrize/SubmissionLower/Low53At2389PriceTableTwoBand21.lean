import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableTwoBand21
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Band21
namespace Top1
private def b0 : PaidBatch (.two7 0) 1 := ⟨[
  .rectangle 1 3 126 8 40,
  .rectangle 3 9 126 13 38,
  .rectangle 5 14 126 24 85], by decide +kernel⟩
private def b1 : PaidBatch (.two7 0) 1 := ⟨[
  .rectangle 9 25 67 46 76,
  .rectangle 68 36 97 46 83,
  .rectangle 68 25 126 35 98], by decide +kernel⟩
private def b2 : PaidBatch (.two7 0) 1 := ⟨[
  .rectangle 98 36 126 41 91,
  .rectangle 98 42 126 46 96], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 0) 1) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 126 3 44 = true := by decide +kernel
def receipt : Certificate (.two7 0) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two7 0) 2 := ⟨[
  .rectangle 2 6 126 11 40,
  .rectangle 4 12 126 16 44,
  .rectangle 6 17 126 26 82], by decide +kernel⟩
private def b1 : PaidBatch (.two7 0) 2 := ⟨[
  .rectangle 9 27 67 46 75,
  .rectangle 68 37 97 46 84,
  .rectangle 68 27 126 36 98], by decide +kernel⟩
private def b2 : PaidBatch (.two7 0) 2 := ⟨[
  .rectangle 98 37 126 41 91,
  .rectangle 98 42 126 46 99], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 0) 2) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 126 6 41 = true := by decide +kernel
def receipt : Certificate (.two7 0) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two7 0) 3 := ⟨[
  .rectangle 3 9 126 18 75,
  .rectangle 7 19 126 27 80,
  .rectangle 10 28 68 46 78], by decide +kernel⟩
private def b1 : PaidBatch (.two7 0) 3 := ⟨[
  .rectangle 69 38 97 46 84,
  .rectangle 69 28 126 37 100,
  .rectangle 98 38 126 42 94], by decide +kernel⟩
private def b2 : PaidBatch (.two7 0) 3 := ⟨[
  .rectangle 98 43 126 46 98], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 0) 3) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 126 9 38 = true := by decide +kernel
def receipt : Certificate (.two7 0) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two7 0) 4 := ⟨[
  .rectangle 4 12 126 20 69,
  .rectangle 7 21 126 29 83,
  .rectangle 10 30 68 46 76], by decide +kernel⟩
private def b1 : PaidBatch (.two7 0) 4 := ⟨[
  .rectangle 69 39 97 46 84,
  .rectangle 69 30 126 38 100,
  .rectangle 98 39 126 42 93], by decide +kernel⟩
private def b2 : PaidBatch (.two7 0) 4 := ⟨[
  .rectangle 98 43 126 46 100], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 0) 4) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 126 12 35 = true := by decide +kernel
def receipt : Certificate (.two7 0) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two7 0) 5 := ⟨[
  .rectangle 5 15 126 22 66,
  .rectangle 8 23 126 30 81,
  .rectangle 11 31 68 46 75], by decide +kernel⟩
private def b1 : PaidBatch (.two7 0) 5 := ⟨[
  .rectangle 69 39 97 46 85,
  .rectangle 69 31 126 38 97,
  .rectangle 98 39 126 42 93], by decide +kernel⟩
private def b2 : PaidBatch (.two7 0) 5 := ⟨[
  .rectangle 98 43 126 46 101], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 0) 5) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 126 15 32 = true := by decide +kernel
def receipt : Certificate (.two7 0) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two7 0) 6 := ⟨[
  .rectangle 6 18 126 25 71,
  .rectangle 9 26 126 32 82,
  .rectangle 11 33 68 46 72], by decide +kernel⟩
private def b1 : PaidBatch (.two7 0) 6 := ⟨[
  .rectangle 69 40 97 46 84,
  .rectangle 69 33 126 39 96,
  .rectangle 98 40 126 43 96], by decide +kernel⟩
private def b2 : PaidBatch (.two7 0) 6 := ⟨[
  .rectangle 98 44 126 46 99], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 0) 6) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 126 18 29 = true := by decide +kernel
def receipt : Certificate (.two7 0) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two7 0) 7 := ⟨[
  .rectangle 7 21 66 33 58,
  .rectangle 12 34 69 46 72,
  .rectangle 67 21 126 27 71], by decide +kernel⟩
private def b1 : PaidBatch (.two7 0) 7 := ⟨[
  .rectangle 67 28 126 33 80,
  .rectangle 70 41 98 46 84,
  .rectangle 70 34 126 40 98], by decide +kernel⟩
private def b2 : PaidBatch (.two7 0) 7 := ⟨[
  .rectangle 99 41 126 43 93,
  .rectangle 99 44 126 46 99], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 0) 7) := [b0, b1, b2]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 126 21 26 = true := by decide +kernel
def receipt : Certificate (.two7 0) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two7 0) 8 := ⟨[
  .rectangle 8 24 67 35 58,
  .rectangle 12 36 69 46 69,
  .rectangle 68 24 126 29 71], by decide +kernel⟩
private def b1 : PaidBatch (.two7 0) 8 := ⟨[
  .rectangle 68 30 126 35 84,
  .rectangle 70 36 126 41 97,
  .rectangle 70 42 126 46 104], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 0) 8) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 126 24 23 = true := by decide +kernel
def receipt : Certificate (.two7 0) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two7 0) 9 := ⟨[
  .rectangle 9 27 126 36 99,
  .rectangle 13 37 69 46 67,
  .rectangle 70 37 126 41 94], by decide +kernel⟩
private def b1 : PaidBatch (.two7 0) 9 := ⟨[
  .rectangle 70 42 126 46 104], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 0) 9) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 126 27 20 = true := by decide +kernel
def receipt : Certificate (.two7 0) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two7 0) 10 := ⟨[
  .rectangle 10 30 68 46 83,
  .rectangle 69 39 97 46 88,
  .rectangle 69 30 126 38 99], by decide +kernel⟩
private def b1 : PaidBatch (.two7 0) 10 := ⟨[
  .rectangle 98 39 126 42 93,
  .rectangle 98 43 126 46 102], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 0) 10) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 126 30 17 = true := by decide +kernel
def receipt : Certificate (.two7 0) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two7 0) 11 := ⟨[
  .rectangle 11 33 68 46 75,
  .rectangle 69 40 97 46 85,
  .rectangle 69 33 126 39 94], by decide +kernel⟩
private def b1 : PaidBatch (.two7 0) 11 := ⟨[
  .rectangle 98 40 126 43 95,
  .rectangle 98 44 126 46 99], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 0) 11) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 126 33 14 = true := by decide +kernel
def receipt : Certificate (.two7 0) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two7 0)).plus a) (fullCap top)) : Covered top (.two7 0) a := by
  change 3+a.b ≤ 129 ∧ 7+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 126 := by omega
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
end Band21


end Low53At2389PriceTableTwoBand21
