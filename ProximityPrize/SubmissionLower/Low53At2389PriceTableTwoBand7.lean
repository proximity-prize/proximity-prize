import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableTwoBand7
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Band7
namespace Top1
private def b0 : PaidBatch (.two6 1) 1 := ⟨[
  .rectangle 1 3 126 8 27,
  .rectangle 3 9 126 14 30,
  .rectangle 5 15 126 25 57], by decide +kernel⟩
private def b1 : PaidBatch (.two6 1) 1 := ⟨[
  .rectangle 9 26 67 47 50,
  .rectangle 68 26 126 36 66,
  .rectangle 68 37 126 47 76], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 1) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 126 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 1) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 1) 2 := ⟨[
  .rectangle 2 6 126 11 27,
  .rectangle 4 12 126 16 29,
  .rectangle 6 17 126 26 55], by decide +kernel⟩
private def b1 : PaidBatch (.two6 1) 2 := ⟨[
  .rectangle 9 27 67 47 52,
  .rectangle 68 27 126 37 69,
  .rectangle 68 38 126 47 76], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 1) 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 126 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 1) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 1) 3 := ⟨[
  .rectangle 3 9 126 18 50,
  .rectangle 7 19 126 28 58,
  .rectangle 10 29 68 47 52], by decide +kernel⟩
private def b1 : PaidBatch (.two6 1) 3 := ⟨[
  .rectangle 69 29 126 38 69,
  .rectangle 69 39 126 47 76], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 1) 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 126 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 1) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 1) 4 := ⟨[
  .rectangle 4 12 126 20 47,
  .rectangle 7 21 126 29 56,
  .rectangle 10 30 68 47 53], by decide +kernel⟩
private def b1 : PaidBatch (.two6 1) 4 := ⟨[
  .rectangle 69 30 126 38 67,
  .rectangle 69 39 126 47 78], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 1) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 126 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 1) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 1) 5 := ⟨[
  .rectangle 5 15 126 23 49,
  .rectangle 8 24 126 31 57,
  .rectangle 11 32 68 47 52], by decide +kernel⟩
private def b1 : PaidBatch (.two6 1) 5 := ⟨[
  .rectangle 69 32 126 39 67,
  .rectangle 69 40 126 47 77], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 1) 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 126 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 1) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 1) 6 := ⟨[
  .rectangle 6 18 126 25 49,
  .rectangle 9 26 126 32 56,
  .rectangle 11 33 68 47 51], by decide +kernel⟩
private def b1 : PaidBatch (.two6 1) 6 := ⟨[
  .rectangle 69 33 126 40 69,
  .rectangle 69 41 126 47 76], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 1) 6) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 126 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 1) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 1) 7 := ⟨[
  .rectangle 7 21 66 34 42,
  .rectangle 12 35 69 47 50,
  .rectangle 67 21 126 34 79], by decide +kernel⟩
private def b1 : PaidBatch (.two6 1) 7 := ⟨[
  .rectangle 70 35 126 41 68,
  .rectangle 70 42 126 47 75], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 1) 7) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 126 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 1) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 1) 8 := ⟨[
  .rectangle 8 24 126 35 73,
  .rectangle 12 36 69 47 50,
  .rectangle 70 36 126 41 67], by decide +kernel⟩
private def b1 : PaidBatch (.two6 1) 8 := ⟨[
  .rectangle 70 42 126 47 75], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 1) 8) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 126 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 1) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 1) 9 := ⟨[
  .rectangle 9 27 126 37 72,
  .rectangle 13 38 126 47 83], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 1) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 126 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 1) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 1) 10 := ⟨[
  .rectangle 10 30 68 47 60,
  .rectangle 69 30 126 38 68,
  .rectangle 69 39 126 47 81], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 1) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 126 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 1) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 1) 11 := ⟨[
  .rectangle 11 33 68 47 54,
  .rectangle 69 33 126 40 69,
  .rectangle 69 41 126 47 77], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 1) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 126 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 1) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 1)).plus a) (fullCap top)) : Covered top (.two6 1) a := by
  change 3+a.b ≤ 129 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 126 := by omega
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
end Band7


end Low53At2389PriceTableTwoBand7
