import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableTwoBand16
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Band16
namespace Top1
private def b0 : PaidBatch (.two6 10) 1 := ⟨[
  .rectangle 1 3 117 8 39,
  .rectangle 3 9 117 14 43,
  .rectangle 5 15 117 25 83], by decide +kernel⟩
private def b1 : PaidBatch (.two6 10) 1 := ⟨[
  .rectangle 9 26 63 47 73,
  .rectangle 64 26 117 36 96,
  .rectangle 64 37 117 47 111], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 10) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 117 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 10) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 10) 2 := ⟨[
  .rectangle 2 6 117 16 88,
  .rectangle 6 17 117 26 80,
  .rectangle 9 27 63 47 76], by decide +kernel⟩
private def b1 : PaidBatch (.two6 10) 2 := ⟨[
  .rectangle 64 27 117 37 100,
  .rectangle 64 38 117 47 111], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 10) 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 117 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 10) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 10) 3 := ⟨[
  .rectangle 3 9 117 18 73,
  .rectangle 7 19 117 28 84,
  .rectangle 10 29 63 47 75], by decide +kernel⟩
private def b1 : PaidBatch (.two6 10) 3 := ⟨[
  .rectangle 64 29 117 38 100,
  .rectangle 64 39 117 47 110], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 10) 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 117 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 10) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 10) 4 := ⟨[
  .rectangle 4 12 117 20 67,
  .rectangle 7 21 117 29 82,
  .rectangle 10 30 63 47 76], by decide +kernel⟩
private def b1 : PaidBatch (.two6 10) 4 := ⟨[
  .rectangle 64 30 117 38 97,
  .rectangle 64 39 117 47 112], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 10) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 117 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 10) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 10) 5 := ⟨[
  .rectangle 5 15 117 23 71,
  .rectangle 8 24 117 31 81,
  .rectangle 11 32 64 47 75], by decide +kernel⟩
private def b1 : PaidBatch (.two6 10) 5 := ⟨[
  .rectangle 65 32 117 39 96,
  .rectangle 65 40 117 47 111], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 10) 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 117 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 10) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 10) 6 := ⟨[
  .rectangle 6 18 117 25 70,
  .rectangle 9 26 117 32 80,
  .rectangle 11 33 64 47 75], by decide +kernel⟩
private def b1 : PaidBatch (.two6 10) 6 := ⟨[
  .rectangle 65 33 117 40 99,
  .rectangle 65 41 117 47 109], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 10) 6) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 117 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 10) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 10) 7 := ⟨[
  .rectangle 7 21 117 34 113,
  .rectangle 12 35 64 47 72,
  .rectangle 65 35 117 41 98], by decide +kernel⟩
private def b1 : PaidBatch (.two6 10) 7 := ⟨[
  .rectangle 65 42 117 47 107], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 10) 7) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 117 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 10) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 10) 8 := ⟨[
  .rectangle 8 24 117 35 104,
  .rectangle 12 36 64 47 70,
  .rectangle 65 36 117 41 95], by decide +kernel⟩
private def b1 : PaidBatch (.two6 10) 8 := ⟨[
  .rectangle 65 42 117 47 107], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 10) 8) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 117 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 10) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 10) 9 := ⟨[
  .rectangle 9 27 117 37 102,
  .rectangle 13 38 65 47 68,
  .rectangle 66 38 117 42 94], by decide +kernel⟩
private def b1 : PaidBatch (.two6 10) 9 := ⟨[
  .rectangle 66 43 117 47 104], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 10) 9) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 117 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 10) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 10) 10 := ⟨[
  .rectangle 10 30 63 47 85,
  .rectangle 64 30 117 38 97,
  .rectangle 64 39 117 47 115], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 10) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 117 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 10) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 10) 11 := ⟨[
  .rectangle 11 33 64 47 78,
  .rectangle 65 33 117 40 97,
  .rectangle 65 41 117 47 109], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 10) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 117 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 10) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 10)).plus a) (fullCap top)) : Covered top (.two6 10) a := by
  change 12+a.b ≤ 129 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 117 := by omega
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
end Band16


end Low53At2389PriceTableTwoBand16
