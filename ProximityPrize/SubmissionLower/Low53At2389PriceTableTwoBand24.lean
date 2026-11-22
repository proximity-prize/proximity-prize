import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableTwoBand24
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Band24
namespace Top1
private def b0 : PaidBatch (.two7 3) 1 := ⟨[
  .rectangle 1 3 123 8 39,
  .rectangle 3 9 123 13 37,
  .rectangle 5 14 123 24 83], by decide +kernel⟩
private def b1 : PaidBatch (.two7 3) 1 := ⟨[
  .rectangle 9 25 66 46 74,
  .rectangle 67 25 123 35 95,
  .rectangle 67 36 123 46 110], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 3) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 123 3 44 = true := by decide +kernel
def receipt : Certificate (.two7 3) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two7 3) 2 := ⟨[
  .rectangle 2 6 123 16 87,
  .rectangle 6 17 123 26 80,
  .rectangle 9 27 66 46 74], by decide +kernel⟩
private def b1 : PaidBatch (.two7 3) 2 := ⟨[
  .rectangle 67 27 123 36 95,
  .rectangle 67 37 123 46 110], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 3) 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 123 6 41 = true := by decide +kernel
def receipt : Certificate (.two7 3) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two7 3) 3 := ⟨[
  .rectangle 3 9 123 18 73,
  .rectangle 7 19 123 27 78,
  .rectangle 10 28 66 46 75], by decide +kernel⟩
private def b1 : PaidBatch (.two7 3) 3 := ⟨[
  .rectangle 67 28 123 37 98,
  .rectangle 67 38 123 46 109], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 3) 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 123 9 38 = true := by decide +kernel
def receipt : Certificate (.two7 3) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two7 3) 4 := ⟨[
  .rectangle 4 12 123 20 67,
  .rectangle 7 21 123 29 81,
  .rectangle 10 30 66 46 73], by decide +kernel⟩
private def b1 : PaidBatch (.two7 3) 4 := ⟨[
  .rectangle 67 30 123 38 97,
  .rectangle 67 39 123 46 108], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 3) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 123 12 35 = true := by decide +kernel
def receipt : Certificate (.two7 3) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two7 3) 5 := ⟨[
  .rectangle 5 15 123 22 65,
  .rectangle 8 23 123 30 79,
  .rectangle 11 31 67 46 74], by decide +kernel⟩
private def b1 : PaidBatch (.two7 3) 5 := ⟨[
  .rectangle 68 31 123 38 94,
  .rectangle 68 39 123 46 109], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 3) 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 123 15 32 = true := by decide +kernel
def receipt : Certificate (.two7 3) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two7 3) 6 := ⟨[
  .rectangle 6 18 123 32 117,
  .rectangle 11 33 67 46 71,
  .rectangle 68 33 123 39 93], by decide +kernel⟩
private def b1 : PaidBatch (.two7 3) 6 := ⟨[
  .rectangle 68 40 123 46 107], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 3) 6) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 123 18 29 = true := by decide +kernel
def receipt : Certificate (.two7 3) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two7 3) 7 := ⟨[
  .rectangle 7 21 123 33 105,
  .rectangle 12 34 67 46 70,
  .rectangle 68 34 123 40 95], by decide +kernel⟩
private def b1 : PaidBatch (.two7 3) 7 := ⟨[
  .rectangle 68 41 123 46 104], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 3) 7) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 123 21 26 = true := by decide +kernel
def receipt : Certificate (.two7 3) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two7 3) 8 := ⟨[
  .rectangle 8 24 123 35 103,
  .rectangle 12 36 123 46 120], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 3) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 123 24 23 = true := by decide +kernel
def receipt : Certificate (.two7 3) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two7 3) 9 := ⟨[
  .rectangle 9 27 123 36 96,
  .rectangle 13 37 123 46 116], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 3) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 123 27 20 = true := by decide +kernel
def receipt : Certificate (.two7 3) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two7 3) 10 := ⟨[
  .rectangle 10 30 66 46 80,
  .rectangle 67 30 123 38 96,
  .rectangle 67 39 123 46 110], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 3) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 123 30 17 = true := by decide +kernel
def receipt : Certificate (.two7 3) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two7 3) 11 := ⟨[
  .rectangle 11 33 67 46 74,
  .rectangle 68 33 123 39 92,
  .rectangle 68 40 123 46 107], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 3) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 123 33 14 = true := by decide +kernel
def receipt : Certificate (.two7 3) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two7 3)).plus a) (fullCap top)) : Covered top (.two7 3) a := by
  change 6+a.b ≤ 129 ∧ 7+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 123 := by omega
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
end Band24


end Low53At2389PriceTableTwoBand24
