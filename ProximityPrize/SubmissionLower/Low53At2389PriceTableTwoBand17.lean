import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableTwoBand17
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Band17
namespace Top1
private def b0 : PaidBatch (.two6 11) 1 := ⟨[
  .rectangle 1 3 116 8 43,
  .rectangle 3 9 116 14 48,
  .rectangle 5 15 116 25 92], by decide +kernel⟩
private def b1 : PaidBatch (.two6 11) 1 := ⟨[
  .rectangle 9 26 62 47 79,
  .rectangle 63 26 116 36 106,
  .rectangle 63 37 116 47 122], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 11) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 116 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 11) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 11) 2 := ⟨[
  .rectangle 2 6 116 16 97,
  .rectangle 6 17 116 26 89,
  .rectangle 9 27 62 47 83], by decide +kernel⟩
private def b1 : PaidBatch (.two6 11) 2 := ⟨[
  .rectangle 63 27 116 37 110,
  .rectangle 63 38 116 47 122], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 11) 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 116 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 11) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 11) 3 := ⟨[
  .rectangle 3 9 116 18 80,
  .rectangle 7 19 116 28 92,
  .rectangle 10 29 63 47 83], by decide +kernel⟩
private def b1 : PaidBatch (.two6 11) 3 := ⟨[
  .rectangle 64 29 116 38 109,
  .rectangle 64 39 116 47 121], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 11) 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 116 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 11) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 11) 4 := ⟨[
  .rectangle 4 12 116 20 74,
  .rectangle 7 21 116 29 89,
  .rectangle 10 30 63 47 84], by decide +kernel⟩
private def b1 : PaidBatch (.two6 11) 4 := ⟨[
  .rectangle 64 30 116 38 107,
  .rectangle 64 39 116 47 123], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 11) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 116 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 11) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 11) 5 := ⟨[
  .rectangle 5 15 116 23 78,
  .rectangle 8 24 116 31 89,
  .rectangle 11 32 63 47 82], by decide +kernel⟩
private def b1 : PaidBatch (.two6 11) 5 := ⟨[
  .rectangle 64 32 116 39 105,
  .rectangle 64 40 116 47 121], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 11) 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 116 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 11) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 11) 6 := ⟨[
  .rectangle 6 18 116 25 76,
  .rectangle 9 26 116 32 87,
  .rectangle 11 33 63 47 81], by decide +kernel⟩
private def b1 : PaidBatch (.two6 11) 6 := ⟨[
  .rectangle 64 33 116 40 108,
  .rectangle 64 41 116 47 119], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 11) 6) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 116 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 11) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 11) 7 := ⟨[
  .rectangle 7 21 116 27 76,
  .rectangle 10 28 116 34 91,
  .rectangle 12 35 64 47 79], by decide +kernel⟩
private def b1 : PaidBatch (.two6 11) 7 := ⟨[
  .rectangle 65 35 116 41 107,
  .rectangle 65 42 116 47 116], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 11) 7) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 116 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 11) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 11) 8 := ⟨[
  .rectangle 8 24 116 35 113,
  .rectangle 12 36 64 47 77,
  .rectangle 65 36 116 41 103], by decide +kernel⟩
private def b1 : PaidBatch (.two6 11) 8 := ⟨[
  .rectangle 65 42 116 47 117], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 11) 8) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 116 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 11) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 11) 9 := ⟨[
  .rectangle 9 27 116 37 112,
  .rectangle 13 38 64 47 74,
  .rectangle 65 38 116 42 102], by decide +kernel⟩
private def b1 : PaidBatch (.two6 11) 9 := ⟨[
  .rectangle 65 43 116 47 114], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 11) 9) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 116 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 11) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 11) 10 := ⟨[
  .rectangle 10 30 116 38 105,
  .rectangle 13 39 116 47 126], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 11) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 116 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 11) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 11) 11 := ⟨[
  .rectangle 11 33 63 47 84,
  .rectangle 64 33 116 40 106,
  .rectangle 64 41 116 47 119], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 11) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 116 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 11) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 11)).plus a) (fullCap top)) : Covered top (.two6 11) a := by
  change 13+a.b ≤ 129 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 116 := by omega
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
end Band17


end Low53At2389PriceTableTwoBand17
