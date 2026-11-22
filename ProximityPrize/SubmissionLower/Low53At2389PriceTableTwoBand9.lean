import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableTwoBand9
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Band9
namespace Top1
private def b0 : PaidBatch (.two6 3) 1 := ⟨[
  .rectangle 1 3 124 8 26,
  .rectangle 3 9 124 14 29,
  .rectangle 5 15 124 25 56], by decide +kernel⟩
private def b1 : PaidBatch (.two6 3) 1 := ⟨[
  .rectangle 9 26 66 47 49,
  .rectangle 67 26 124 36 65,
  .rectangle 67 37 124 47 75], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 3) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 124 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 3) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 3) 2 := ⟨[
  .rectangle 2 6 124 16 58,
  .rectangle 6 17 124 26 54,
  .rectangle 9 27 66 47 51], by decide +kernel⟩
private def b1 : PaidBatch (.two6 3) 2 := ⟨[
  .rectangle 67 27 124 37 68,
  .rectangle 67 38 124 47 75], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 3) 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 124 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 3) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 3) 3 := ⟨[
  .rectangle 3 9 124 18 49,
  .rectangle 7 19 124 28 57,
  .rectangle 10 29 67 47 52], by decide +kernel⟩
private def b1 : PaidBatch (.two6 3) 3 := ⟨[
  .rectangle 68 29 124 38 68,
  .rectangle 68 39 124 47 75], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 3) 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 124 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 3) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 3) 4 := ⟨[
  .rectangle 4 12 124 20 46,
  .rectangle 7 21 124 29 56,
  .rectangle 10 30 67 47 52], by decide +kernel⟩
private def b1 : PaidBatch (.two6 3) 4 := ⟨[
  .rectangle 68 30 124 38 66,
  .rectangle 68 39 124 47 77], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 3) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 124 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 3) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 3) 5 := ⟨[
  .rectangle 5 15 124 23 49,
  .rectangle 8 24 124 31 56,
  .rectangle 11 32 67 47 51], by decide +kernel⟩
private def b1 : PaidBatch (.two6 3) 5 := ⟨[
  .rectangle 68 32 124 39 66,
  .rectangle 68 40 124 47 76], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 3) 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 124 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 3) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 3) 6 := ⟨[
  .rectangle 6 18 124 32 80,
  .rectangle 11 33 67 47 51,
  .rectangle 68 33 124 40 68], by decide +kernel⟩
private def b1 : PaidBatch (.two6 3) 6 := ⟨[
  .rectangle 68 41 124 47 75], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 3) 6) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 124 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 3) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 3) 7 := ⟨[
  .rectangle 7 21 124 34 77,
  .rectangle 12 35 68 47 50,
  .rectangle 69 35 124 41 67], by decide +kernel⟩
private def b1 : PaidBatch (.two6 3) 7 := ⟨[
  .rectangle 69 42 124 47 73], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 3) 7) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 124 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 3) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 3) 8 := ⟨[
  .rectangle 8 24 124 35 71,
  .rectangle 12 36 124 47 86], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 3) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 124 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 3) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 3) 9 := ⟨[
  .rectangle 9 27 124 37 71,
  .rectangle 13 38 124 47 82], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 3) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 124 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 3) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 3) 10 := ⟨[
  .rectangle 10 30 67 47 59,
  .rectangle 68 30 124 38 67,
  .rectangle 68 39 124 47 80], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 3) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 124 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 3) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 3) 11 := ⟨[
  .rectangle 11 33 67 47 54,
  .rectangle 68 33 124 40 68,
  .rectangle 68 41 124 47 76], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 3) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 124 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 3) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 3)).plus a) (fullCap top)) : Covered top (.two6 3) a := by
  change 5+a.b ≤ 129 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 124 := by omega
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
end Band9


end Low53At2389PriceTableTwoBand9
