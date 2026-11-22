import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableTwoBand15
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Band15
namespace Top1
private def b0 : PaidBatch (.two6 9) 1 := ⟨[
  .rectangle 1 3 118 8 36,
  .rectangle 3 9 118 14 40,
  .rectangle 5 15 118 25 76], by decide +kernel⟩
private def b1 : PaidBatch (.two6 9) 1 := ⟨[
  .rectangle 9 26 63 47 66,
  .rectangle 64 26 118 36 88,
  .rectangle 64 37 118 47 102], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 9) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 118 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 9) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 9) 2 := ⟨[
  .rectangle 2 6 118 16 80,
  .rectangle 6 17 118 26 74,
  .rectangle 9 27 63 47 69], by decide +kernel⟩
private def b1 : PaidBatch (.two6 9) 2 := ⟨[
  .rectangle 64 27 118 37 92,
  .rectangle 64 38 118 47 102], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 9) 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 118 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 9) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 9) 3 := ⟨[
  .rectangle 3 9 118 18 67,
  .rectangle 7 19 118 28 77,
  .rectangle 10 29 64 47 70], by decide +kernel⟩
private def b1 : PaidBatch (.two6 9) 3 := ⟨[
  .rectangle 65 29 118 38 92,
  .rectangle 65 39 118 47 102], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 9) 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 118 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 9) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 9) 4 := ⟨[
  .rectangle 4 12 118 20 62,
  .rectangle 7 21 118 29 75,
  .rectangle 10 30 64 47 71], by decide +kernel⟩
private def b1 : PaidBatch (.two6 9) 4 := ⟨[
  .rectangle 65 30 118 38 90,
  .rectangle 65 39 118 47 103], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 9) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 118 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 9) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 9) 5 := ⟨[
  .rectangle 5 15 118 23 66,
  .rectangle 8 24 118 31 75,
  .rectangle 11 32 64 47 69], by decide +kernel⟩
private def b1 : PaidBatch (.two6 9) 5 := ⟨[
  .rectangle 65 32 118 39 89,
  .rectangle 65 40 118 47 102], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 9) 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 118 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 9) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 9) 6 := ⟨[
  .rectangle 6 18 118 25 64,
  .rectangle 9 26 118 32 74,
  .rectangle 11 33 64 47 68], by decide +kernel⟩
private def b1 : PaidBatch (.two6 9) 6 := ⟨[
  .rectangle 65 33 118 40 91,
  .rectangle 65 41 118 47 100], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 9) 6) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 118 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 9) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 9) 7 := ⟨[
  .rectangle 7 21 118 34 104,
  .rectangle 12 35 65 47 67,
  .rectangle 66 35 118 41 90], by decide +kernel⟩
private def b1 : PaidBatch (.two6 9) 7 := ⟨[
  .rectangle 66 42 118 47 99], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 9) 7) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 118 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 9) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 9) 8 := ⟨[
  .rectangle 8 24 118 35 96,
  .rectangle 12 36 65 47 66,
  .rectangle 66 36 118 41 88], by decide +kernel⟩
private def b1 : PaidBatch (.two6 9) 8 := ⟨[
  .rectangle 66 42 118 47 99], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 9) 8) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 118 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 9) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 9) 9 := ⟨[
  .rectangle 9 27 118 37 95,
  .rectangle 13 38 118 47 110], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 9) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 118 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 9) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 9) 10 := ⟨[
  .rectangle 10 30 118 38 90,
  .rectangle 13 39 118 47 107], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 9) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 118 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 9) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 9) 11 := ⟨[
  .rectangle 11 33 64 47 72,
  .rectangle 65 33 118 40 90,
  .rectangle 65 41 118 47 101], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 9) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 118 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 9) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 9)).plus a) (fullCap top)) : Covered top (.two6 9) a := by
  change 11+a.b ≤ 129 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 118 := by omega
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
end Band15


end Low53At2389PriceTableTwoBand15
