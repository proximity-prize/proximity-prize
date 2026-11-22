import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableTwoBand18
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Band18
namespace Top1
private def b0 : PaidBatch (.two6 12) 1 := ⟨[
  .rectangle 1 3 115 8 48,
  .rectangle 3 9 115 14 53,
  .rectangle 5 15 115 25 103], by decide +kernel⟩
private def b1 : PaidBatch (.two6 12) 1 := ⟨[
  .rectangle 9 26 62 47 90,
  .rectangle 63 26 115 36 119,
  .rectangle 63 37 115 47 136], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 12) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 115 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 12) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 12) 2 := ⟨[
  .rectangle 2 6 115 16 108,
  .rectangle 6 17 115 26 99,
  .rectangle 9 27 62 47 93], by decide +kernel⟩
private def b1 : PaidBatch (.two6 12) 2 := ⟨[
  .rectangle 63 27 115 37 123,
  .rectangle 63 38 115 47 136], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 12) 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 115 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 12) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 12) 3 := ⟨[
  .rectangle 3 9 115 18 89,
  .rectangle 7 19 115 28 103,
  .rectangle 10 29 62 47 92], by decide +kernel⟩
private def b1 : PaidBatch (.two6 12) 3 := ⟨[
  .rectangle 63 29 115 38 122,
  .rectangle 63 39 115 47 135], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 12) 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 115 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 12) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 12) 4 := ⟨[
  .rectangle 4 12 115 20 82,
  .rectangle 7 21 115 29 99,
  .rectangle 10 30 62 47 93], by decide +kernel⟩
private def b1 : PaidBatch (.two6 12) 4 := ⟨[
  .rectangle 63 30 115 38 118,
  .rectangle 63 39 115 47 137], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 12) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 115 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 12) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 12) 5 := ⟨[
  .rectangle 5 15 115 23 86,
  .rectangle 8 24 115 31 99,
  .rectangle 11 32 63 47 91], by decide +kernel⟩
private def b1 : PaidBatch (.two6 12) 5 := ⟨[
  .rectangle 64 32 115 39 117,
  .rectangle 64 40 115 47 134], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 12) 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 115 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 12) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 12) 6 := ⟨[
  .rectangle 6 18 115 25 84,
  .rectangle 9 26 115 32 96,
  .rectangle 11 33 63 47 90], by decide +kernel⟩
private def b1 : PaidBatch (.two6 12) 6 := ⟨[
  .rectangle 64 33 115 40 119,
  .rectangle 64 41 115 47 131], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 12) 6) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 115 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 12) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 12) 7 := ⟨[
  .rectangle 7 21 115 34 136,
  .rectangle 12 35 63 47 86,
  .rectangle 64 35 115 41 118], by decide +kernel⟩
private def b1 : PaidBatch (.two6 12) 7 := ⟨[
  .rectangle 64 42 115 47 129], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 12) 7) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 115 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 12) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 12) 8 := ⟨[
  .rectangle 8 24 115 35 125,
  .rectangle 12 36 63 47 85,
  .rectangle 64 36 115 41 114], by decide +kernel⟩
private def b1 : PaidBatch (.two6 12) 8 := ⟨[
  .rectangle 64 42 115 47 129], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 12) 8) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 115 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 12) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 12) 9 := ⟨[
  .rectangle 9 27 115 37 123,
  .rectangle 13 38 64 47 82,
  .rectangle 65 38 115 42 113], by decide +kernel⟩
private def b1 : PaidBatch (.two6 12) 9 := ⟨[
  .rectangle 65 43 115 47 125], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 12) 9) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 115 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 12) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 12) 10 := ⟨[
  .rectangle 10 30 115 38 116,
  .rectangle 13 39 115 47 138], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 12) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 115 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 12) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 12) 11 := ⟨[
  .rectangle 11 33 63 47 93,
  .rectangle 64 33 115 40 116,
  .rectangle 64 41 115 47 131], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 12) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 115 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 12) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 12)).plus a) (fullCap top)) : Covered top (.two6 12) a := by
  change 14+a.b ≤ 129 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 115 := by omega
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
end Band18


end Low53At2389PriceTableTwoBand18
