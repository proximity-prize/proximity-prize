import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableTwoBand11
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Band11
namespace Top1
private def b0 : PaidBatch (.two6 5) 1 := ⟨[
  .rectangle 1 3 122 8 27,
  .rectangle 3 9 122 14 30,
  .rectangle 5 15 122 25 58], by decide +kernel⟩
private def b1 : PaidBatch (.two6 5) 1 := ⟨[
  .rectangle 9 26 65 47 51,
  .rectangle 66 26 122 36 68,
  .rectangle 66 37 122 47 78], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 5) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 122 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 5) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 5) 2 := ⟨[
  .rectangle 2 6 122 16 61,
  .rectangle 6 17 122 26 57,
  .rectangle 9 27 65 47 53], by decide +kernel⟩
private def b1 : PaidBatch (.two6 5) 2 := ⟨[
  .rectangle 66 27 122 37 71,
  .rectangle 66 38 122 47 78], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 5) 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 122 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 5) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 5) 3 := ⟨[
  .rectangle 3 9 122 18 52,
  .rectangle 7 19 122 28 59,
  .rectangle 10 29 66 47 54], by decide +kernel⟩
private def b1 : PaidBatch (.two6 5) 3 := ⟨[
  .rectangle 67 29 122 38 71,
  .rectangle 67 39 122 47 78], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 5) 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 122 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 5) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 5) 4 := ⟨[
  .rectangle 4 12 122 20 48,
  .rectangle 7 21 122 29 58,
  .rectangle 10 30 66 47 55], by decide +kernel⟩
private def b1 : PaidBatch (.two6 5) 4 := ⟨[
  .rectangle 67 30 122 38 69,
  .rectangle 67 39 122 47 80], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 5) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 122 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 5) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 5) 5 := ⟨[
  .rectangle 5 15 122 23 51,
  .rectangle 8 24 122 31 58,
  .rectangle 11 32 66 47 53], by decide +kernel⟩
private def b1 : PaidBatch (.two6 5) 5 := ⟨[
  .rectangle 67 32 122 39 69,
  .rectangle 67 40 122 47 79], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 5) 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 122 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 5) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 5) 6 := ⟨[
  .rectangle 6 18 122 32 84,
  .rectangle 11 33 66 47 53,
  .rectangle 67 33 122 40 71], by decide +kernel⟩
private def b1 : PaidBatch (.two6 5) 6 := ⟨[
  .rectangle 67 41 122 47 78], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 5) 6) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 122 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 5) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 5) 7 := ⟨[
  .rectangle 7 21 122 34 81,
  .rectangle 12 35 122 47 92], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 5) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 122 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 5) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 5) 8 := ⟨[
  .rectangle 8 24 122 35 75,
  .rectangle 12 36 122 47 90], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 5) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 122 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 5) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 5) 9 := ⟨[
  .rectangle 9 27 122 37 74,
  .rectangle 13 38 122 47 86], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 5) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 122 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 5) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 5) 10 := ⟨[
  .rectangle 10 30 66 47 62,
  .rectangle 67 30 122 38 70,
  .rectangle 67 39 122 47 83], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 5) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 122 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 5) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 5) 11 := ⟨[
  .rectangle 11 33 66 47 56,
  .rectangle 67 33 122 40 71,
  .rectangle 67 41 122 47 79], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 5) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 122 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 5) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 5)).plus a) (fullCap top)) : Covered top (.two6 5) a := by
  change 7+a.b ≤ 129 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 122 := by omega
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
end Band11


end Low53At2389PriceTableTwoBand11
