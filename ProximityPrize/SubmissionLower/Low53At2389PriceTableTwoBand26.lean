import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableTwoBand26
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Band26
namespace Top1
private def b0 : PaidBatch (.two7 5) 1 := ⟨[
  .rectangle 1 3 121 8 45,
  .rectangle 3 9 121 13 42,
  .rectangle 5 14 121 24 95], by decide +kernel⟩
private def b1 : PaidBatch (.two7 5) 1 := ⟨[
  .rectangle 9 25 65 46 85,
  .rectangle 66 25 121 35 109,
  .rectangle 66 36 121 46 126], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 5) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 121 3 44 = true := by decide +kernel
def receipt : Certificate (.two7 5) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two7 5) 2 := ⟨[
  .rectangle 2 6 121 16 100,
  .rectangle 6 17 121 26 92,
  .rectangle 9 27 65 46 84], by decide +kernel⟩
private def b1 : PaidBatch (.two7 5) 2 := ⟨[
  .rectangle 66 27 121 36 108,
  .rectangle 66 37 121 46 125], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 5) 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 121 6 41 = true := by decide +kernel
def receipt : Certificate (.two7 5) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two7 5) 3 := ⟨[
  .rectangle 3 9 121 18 83,
  .rectangle 7 19 121 27 89,
  .rectangle 10 28 65 46 86], by decide +kernel⟩
private def b1 : PaidBatch (.two7 5) 3 := ⟨[
  .rectangle 66 28 121 37 112,
  .rectangle 66 38 121 46 124], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 5) 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 121 9 38 = true := by decide +kernel
def receipt : Certificate (.two7 5) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two7 5) 4 := ⟨[
  .rectangle 4 12 121 20 76,
  .rectangle 7 21 121 29 93,
  .rectangle 10 30 65 46 83], by decide +kernel⟩
private def b1 : PaidBatch (.two7 5) 4 := ⟨[
  .rectangle 66 30 121 38 110,
  .rectangle 66 39 121 46 122], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 5) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 121 12 35 = true := by decide +kernel
def receipt : Certificate (.two7 5) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two7 5) 5 := ⟨[
  .rectangle 5 15 121 30 141,
  .rectangle 11 31 66 46 84,
  .rectangle 67 31 121 38 107], by decide +kernel⟩
private def b1 : PaidBatch (.two7 5) 5 := ⟨[
  .rectangle 67 39 121 46 123], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 5) 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 121 15 32 = true := by decide +kernel
def receipt : Certificate (.two7 5) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two7 5) 6 := ⟨[
  .rectangle 6 18 121 32 132,
  .rectangle 11 33 121 46 148], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 5) 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 121 18 29 = true := by decide +kernel
def receipt : Certificate (.two7 5) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two7 5) 7 := ⟨[
  .rectangle 7 21 121 33 119,
  .rectangle 12 34 121 46 144], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 5) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 121 21 26 = true := by decide +kernel
def receipt : Certificate (.two7 5) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two7 5) 8 := ⟨[
  .rectangle 8 24 121 35 117,
  .rectangle 12 36 121 46 135], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 5) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 121 24 23 = true := by decide +kernel
def receipt : Certificate (.two7 5) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two7 5) 9 := ⟨[
  .rectangle 9 27 121 36 109,
  .rectangle 13 37 121 46 131], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 5) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 121 27 20 = true := by decide +kernel
def receipt : Certificate (.two7 5) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two7 5) 10 := ⟨[
  .rectangle 10 30 65 46 91,
  .rectangle 66 30 121 38 109,
  .rectangle 66 39 121 46 124], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 5) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 121 30 17 = true := by decide +kernel
def receipt : Certificate (.two7 5) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two7 5) 11 := ⟨[
  .rectangle 11 33 121 46 147], by decide +kernel⟩
private def batches : List (PaidBatch (.two7 5) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 121 33 14 = true := by decide +kernel
def receipt : Certificate (.two7 5) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two7 5)).plus a) (fullCap top)) : Covered top (.two7 5) a := by
  change 8+a.b ≤ 129 ∧ 7+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 121 := by omega
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
end Band26


end Low53At2389PriceTableTwoBand26
