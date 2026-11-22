import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableTwoBand14
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Band14
namespace Top1
private def b0 : PaidBatch (.two6 8) 1 := ⟨[
  .rectangle 1 3 119 8 33,
  .rectangle 3 9 119 14 37,
  .rectangle 5 15 119 25 71], by decide +kernel⟩
private def b1 : PaidBatch (.two6 8) 1 := ⟨[
  .rectangle 9 26 64 47 62,
  .rectangle 65 26 119 36 82,
  .rectangle 65 37 119 47 94], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 8) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 119 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 8) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 8) 2 := ⟨[
  .rectangle 2 6 119 16 74,
  .rectangle 6 17 119 26 69,
  .rectangle 9 27 64 47 65], by decide +kernel⟩
private def b1 : PaidBatch (.two6 8) 2 := ⟨[
  .rectangle 65 27 119 37 85,
  .rectangle 65 38 119 47 95], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 8) 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 119 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 8) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 8) 3 := ⟨[
  .rectangle 3 9 119 18 62,
  .rectangle 7 19 119 28 72,
  .rectangle 10 29 64 47 64], by decide +kernel⟩
private def b1 : PaidBatch (.two6 8) 3 := ⟨[
  .rectangle 65 29 119 38 85,
  .rectangle 65 39 119 47 94], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 8) 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 119 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 8) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 8) 4 := ⟨[
  .rectangle 4 12 119 20 58,
  .rectangle 7 21 119 29 70,
  .rectangle 10 30 64 47 65], by decide +kernel⟩
private def b1 : PaidBatch (.two6 8) 4 := ⟨[
  .rectangle 65 30 119 38 83,
  .rectangle 65 39 119 47 96], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 8) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 119 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 8) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 8) 5 := ⟨[
  .rectangle 5 15 119 23 61,
  .rectangle 8 24 119 31 70,
  .rectangle 11 32 65 47 64], by decide +kernel⟩
private def b1 : PaidBatch (.two6 8) 5 := ⟨[
  .rectangle 66 32 119 39 83,
  .rectangle 66 40 119 47 95], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 8) 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 119 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 8) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 8) 6 := ⟨[
  .rectangle 6 18 119 25 60,
  .rectangle 9 26 119 32 69,
  .rectangle 11 33 65 47 64], by decide +kernel⟩
private def b1 : PaidBatch (.two6 8) 6 := ⟨[
  .rectangle 66 33 119 40 85,
  .rectangle 66 41 119 47 93], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 8) 6) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 119 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 8) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 8) 7 := ⟨[
  .rectangle 7 21 119 34 97,
  .rectangle 12 35 65 47 62,
  .rectangle 66 35 119 41 84], by decide +kernel⟩
private def b1 : PaidBatch (.two6 8) 7 := ⟨[
  .rectangle 66 42 119 47 92], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 8) 7) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 119 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 8) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 8) 8 := ⟨[
  .rectangle 8 24 119 35 89,
  .rectangle 12 36 65 47 61,
  .rectangle 66 36 119 41 82], by decide +kernel⟩
private def b1 : PaidBatch (.two6 8) 8 := ⟨[
  .rectangle 66 42 119 47 92], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 8) 8) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 119 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 8) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 8) 9 := ⟨[
  .rectangle 9 27 119 37 88,
  .rectangle 13 38 119 47 102], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 8) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 119 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 8) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 8) 10 := ⟨[
  .rectangle 10 30 64 47 73,
  .rectangle 65 30 119 38 84,
  .rectangle 65 39 119 47 100], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 8) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 119 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 8) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 8) 11 := ⟨[
  .rectangle 11 33 65 47 67,
  .rectangle 66 33 119 40 84,
  .rectangle 66 41 119 47 94], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 8) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 119 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 8) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 8)).plus a) (fullCap top)) : Covered top (.two6 8) a := by
  change 10+a.b ≤ 129 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 119 := by omega
  have hj' : a.j ≤ 47 := by omega
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
end Band14


end Low53At2389PriceTableTwoBand14
