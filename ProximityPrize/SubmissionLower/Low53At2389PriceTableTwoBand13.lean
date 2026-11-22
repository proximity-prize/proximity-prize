import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableTwoBand13
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Band13
namespace Top1
private def b0 : PaidBatch (.two6 7) 1 := ⟨[
  .rectangle 1 3 120 8 31,
  .rectangle 3 9 120 14 34,
  .rectangle 5 15 120 25 66], by decide +kernel⟩
private def b1 : PaidBatch (.two6 7) 1 := ⟨[
  .rectangle 9 26 64 47 57,
  .rectangle 65 26 120 36 76,
  .rectangle 65 37 120 47 88], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 7) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 120 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 7) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 7) 2 := ⟨[
  .rectangle 2 6 120 16 69,
  .rectangle 6 17 120 26 64,
  .rectangle 9 27 64 47 60], by decide +kernel⟩
private def b1 : PaidBatch (.two6 7) 2 := ⟨[
  .rectangle 65 27 120 37 80,
  .rectangle 65 38 120 47 88], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 7) 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 120 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 7) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 7) 3 := ⟨[
  .rectangle 3 9 120 18 58,
  .rectangle 7 19 120 28 67,
  .rectangle 10 29 65 47 61], by decide +kernel⟩
private def b1 : PaidBatch (.two6 7) 3 := ⟨[
  .rectangle 66 29 120 38 79,
  .rectangle 66 39 120 47 88], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 7) 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 120 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 7) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 7) 4 := ⟨[
  .rectangle 4 12 120 20 54,
  .rectangle 7 21 120 29 65,
  .rectangle 10 30 65 47 62], by decide +kernel⟩
private def b1 : PaidBatch (.two6 7) 4 := ⟨[
  .rectangle 66 30 120 38 78,
  .rectangle 66 39 120 47 90], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 7) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 120 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 7) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 7) 5 := ⟨[
  .rectangle 5 15 120 23 57,
  .rectangle 8 24 120 31 65,
  .rectangle 11 32 65 47 60], by decide +kernel⟩
private def b1 : PaidBatch (.two6 7) 5 := ⟨[
  .rectangle 66 32 120 39 77,
  .rectangle 66 40 120 47 89], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 7) 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 120 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 7) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 7) 6 := ⟨[
  .rectangle 6 18 120 32 94,
  .rectangle 11 33 65 47 60,
  .rectangle 66 33 120 40 79], by decide +kernel⟩
private def b1 : PaidBatch (.two6 7) 6 := ⟨[
  .rectangle 66 41 120 47 88], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 7) 6) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 120 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 7) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 7) 7 := ⟨[
  .rectangle 7 21 120 34 91,
  .rectangle 12 35 66 47 58,
  .rectangle 67 35 120 41 79], by decide +kernel⟩
private def b1 : PaidBatch (.two6 7) 7 := ⟨[
  .rectangle 67 42 120 47 86], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 7) 7) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 120 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 7) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 7) 8 := ⟨[
  .rectangle 8 24 120 35 84,
  .rectangle 12 36 66 47 57,
  .rectangle 67 36 120 47 101], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 7) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 120 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 7) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 7) 9 := ⟨[
  .rectangle 9 27 120 37 83,
  .rectangle 13 38 120 47 96], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 7) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 120 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 7) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 7) 10 := ⟨[
  .rectangle 10 30 120 38 78,
  .rectangle 13 39 120 47 93], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 7) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 120 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 7) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 7) 11 := ⟨[
  .rectangle 11 33 65 47 63,
  .rectangle 66 33 120 40 79,
  .rectangle 66 41 120 47 89], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 7) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 120 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 7) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 7)).plus a) (fullCap top)) : Covered top (.two6 7) a := by
  change 9+a.b ≤ 129 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 120 := by omega
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
end Band13


end Low53At2389PriceTableTwoBand13
