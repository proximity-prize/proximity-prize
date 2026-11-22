import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableTwoBand19
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Band19
namespace Top1
private def b0 : PaidBatch (.two6 13) 1 := ⟨[
  .rectangle 1 3 114 8 55,
  .rectangle 3 9 114 14 60,
  .rectangle 5 15 114 25 117], by decide +kernel⟩
private def b1 : PaidBatch (.two6 13) 1 := ⟨[
  .rectangle 9 26 61 47 101,
  .rectangle 62 26 114 36 135,
  .rectangle 62 37 114 47 155], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 13) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 114 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 13) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 13) 2 := ⟨[
  .rectangle 2 6 114 16 123,
  .rectangle 6 17 114 26 112,
  .rectangle 9 27 61 47 105], by decide +kernel⟩
private def b1 : PaidBatch (.two6 13) 2 := ⟨[
  .rectangle 62 27 114 37 139,
  .rectangle 62 38 114 47 154], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 13) 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 114 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 13) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 13) 3 := ⟨[
  .rectangle 3 9 114 18 101,
  .rectangle 7 19 114 28 116,
  .rectangle 10 29 62 47 105], by decide +kernel⟩
private def b1 : PaidBatch (.two6 13) 3 := ⟨[
  .rectangle 63 29 114 38 137,
  .rectangle 63 39 114 47 152], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 13) 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 114 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 13) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 13) 4 := ⟨[
  .rectangle 4 12 114 20 92,
  .rectangle 7 21 114 29 112,
  .rectangle 10 30 62 47 105], by decide +kernel⟩
private def b1 : PaidBatch (.two6 13) 4 := ⟨[
  .rectangle 63 30 114 38 133,
  .rectangle 63 39 114 47 154], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 13) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 114 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 13) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 13) 5 := ⟨[
  .rectangle 5 15 114 23 97,
  .rectangle 8 24 114 31 111,
  .rectangle 11 32 62 47 102], by decide +kernel⟩
private def b1 : PaidBatch (.two6 13) 5 := ⟨[
  .rectangle 63 32 114 39 131,
  .rectangle 63 40 114 47 151], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 13) 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 114 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 13) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 13) 6 := ⟨[
  .rectangle 6 18 114 32 160,
  .rectangle 11 33 62 47 101,
  .rectangle 63 33 114 40 134], by decide +kernel⟩
private def b1 : PaidBatch (.two6 13) 6 := ⟨[
  .rectangle 63 41 114 47 148], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 13) 6) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 114 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 13) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 13) 7 := ⟨[
  .rectangle 7 21 114 34 153,
  .rectangle 12 35 114 47 174], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 13) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 114 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 13) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 13) 8 := ⟨[
  .rectangle 8 24 114 35 140,
  .rectangle 12 36 114 47 169], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 13) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 114 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 13) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 13) 9 := ⟨[
  .rectangle 9 27 114 37 138,
  .rectangle 13 38 114 47 159], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 13) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 114 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 13) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 13) 10 := ⟨[
  .rectangle 10 30 114 38 129,
  .rectangle 13 39 114 47 154], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 13) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 114 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 13) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 13) 11 := ⟨[
  .rectangle 11 33 62 47 104,
  .rectangle 63 33 114 40 130,
  .rectangle 63 41 114 47 146], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 13) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 114 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 13) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 13)).plus a) (fullCap top)) : Covered top (.two6 13) a := by
  change 15+a.b ≤ 129 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 114 := by omega
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
end Band19


end Low53At2389PriceTableTwoBand19
