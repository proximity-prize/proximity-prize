import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableTwoBand12
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Band12
namespace Top1
private def b0 : PaidBatch (.two6 6) 1 := ⟨[
  .rectangle 1 3 121 8 29,
  .rectangle 3 9 121 14 32,
  .rectangle 5 15 121 25 62], by decide +kernel⟩
private def b1 : PaidBatch (.two6 6) 1 := ⟨[
  .rectangle 9 26 65 47 55,
  .rectangle 66 26 121 36 72,
  .rectangle 66 37 121 47 83], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 6) 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 121 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 6) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 6) 2 := ⟨[
  .rectangle 2 6 121 16 65,
  .rectangle 6 17 121 26 60,
  .rectangle 9 27 65 47 57], by decide +kernel⟩
private def b1 : PaidBatch (.two6 6) 2 := ⟨[
  .rectangle 66 27 121 37 75,
  .rectangle 66 38 121 47 83], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 6) 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 121 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 6) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 6) 3 := ⟨[
  .rectangle 3 9 121 18 55,
  .rectangle 7 19 121 28 63,
  .rectangle 10 29 65 47 57], by decide +kernel⟩
private def b1 : PaidBatch (.two6 6) 3 := ⟨[
  .rectangle 66 29 121 38 75,
  .rectangle 66 39 121 47 83], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 6) 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 121 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 6) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 6) 4 := ⟨[
  .rectangle 4 12 121 20 51,
  .rectangle 7 21 121 29 61,
  .rectangle 10 30 65 47 57], by decide +kernel⟩
private def b1 : PaidBatch (.two6 6) 4 := ⟨[
  .rectangle 66 30 121 38 73,
  .rectangle 66 39 121 47 85], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 6) 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 121 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 6) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 6) 5 := ⟨[
  .rectangle 5 15 121 23 54,
  .rectangle 8 24 121 31 62,
  .rectangle 11 32 66 47 57], by decide +kernel⟩
private def b1 : PaidBatch (.two6 6) 5 := ⟨[
  .rectangle 67 32 121 39 73,
  .rectangle 67 40 121 47 84], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 6) 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 121 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 6) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 6) 6 := ⟨[
  .rectangle 6 18 121 32 88,
  .rectangle 11 33 66 47 57,
  .rectangle 67 33 121 40 75], by decide +kernel⟩
private def b1 : PaidBatch (.two6 6) 6 := ⟨[
  .rectangle 67 41 121 47 82], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 6) 6) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 121 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 6) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 6) 7 := ⟨[
  .rectangle 7 21 121 34 85,
  .rectangle 12 35 66 47 54,
  .rectangle 67 35 121 41 74], by decide +kernel⟩
private def b1 : PaidBatch (.two6 6) 7 := ⟨[
  .rectangle 67 42 121 47 81], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 6) 7) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 121 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 6) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 6) 8 := ⟨[
  .rectangle 8 24 121 35 79,
  .rectangle 12 36 121 47 95], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 6) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 121 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 6) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 6) 9 := ⟨[
  .rectangle 9 27 121 37 78,
  .rectangle 13 38 121 47 90], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 6) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 121 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 6) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 6) 10 := ⟨[
  .rectangle 10 30 65 47 65,
  .rectangle 66 30 121 38 74,
  .rectangle 66 39 121 47 88], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 6) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 121 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 6) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 6) 11 := ⟨[
  .rectangle 11 33 66 47 60,
  .rectangle 67 33 121 40 74,
  .rectangle 67 41 121 47 84], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 6) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 121 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 6) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 6)).plus a) (fullCap top)) : Covered top (.two6 6) a := by
  change 8+a.b ≤ 129 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 121 := by omega
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
end Band12


end Low53At2389PriceTableTwoBand12
