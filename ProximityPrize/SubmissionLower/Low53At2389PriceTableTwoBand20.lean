import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableTwoBand20
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Band20
namespace Top1
private def b0 : PaidBatch (.two6 14) 1 := ⟨[
  .rectangle 1 3 113 14 238,
  .rectangle 5 15 113 25 136,
  .rectangle 9 26 113 47 265], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 14) 1) := [b0]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 113 3 45 = true := by decide +kernel
def receipt : Certificate (.two6 14) 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch (.two6 14) 2 := ⟨[
  .rectangle 2 6 113 16 143,
  .rectangle 6 17 113 26 130,
  .rectangle 9 27 113 47 259], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 14) 2) := [b0]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 113 6 42 = true := by decide +kernel
def receipt : Certificate (.two6 14) 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch (.two6 14) 3 := ⟨[
  .rectangle 3 9 113 18 117,
  .rectangle 7 19 113 28 134,
  .rectangle 10 29 113 47 242], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 14) 3) := [b0]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 113 9 39 = true := by decide +kernel
def receipt : Certificate (.two6 14) 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch (.two6 14) 4 := ⟨[
  .rectangle 4 12 113 29 236,
  .rectangle 10 30 113 47 235], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 14) 4) := [b0]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 113 12 36 = true := by decide +kernel
def receipt : Certificate (.two6 14) 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch (.two6 14) 5 := ⟨[
  .rectangle 5 15 113 31 211,
  .rectangle 11 32 113 47 220], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 14) 5) := [b0]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 113 15 33 = true := by decide +kernel
def receipt : Certificate (.two6 14) 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch (.two6 14) 6 := ⟨[
  .rectangle 6 18 113 32 183,
  .rectangle 11 33 113 47 213], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 14) 6) := [b0]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 113 18 30 = true := by decide +kernel
def receipt : Certificate (.two6 14) 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch (.two6 14) 7 := ⟨[
  .rectangle 7 21 113 34 175,
  .rectangle 12 35 113 47 199], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 14) 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 113 21 27 = true := by decide +kernel
def receipt : Certificate (.two6 14) 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch (.two6 14) 8 := ⟨[
  .rectangle 8 24 113 47 299], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 14) 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 113 24 24 = true := by decide +kernel
def receipt : Certificate (.two6 14) 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch (.two6 14) 9 := ⟨[
  .rectangle 9 27 113 47 262], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 14) 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 113 27 21 = true := by decide +kernel
def receipt : Certificate (.two6 14) 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch (.two6 14) 10 := ⟨[
  .rectangle 10 30 113 47 232], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 14) 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 113 30 18 = true := by decide +kernel
def receipt : Certificate (.two6 14) 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch (.two6 14) 11 := ⟨[
  .rectangle 11 33 113 47 208], by decide +kernel⟩
private def batches : List (PaidBatch (.two6 14) 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 113 33 15 = true := by decide +kernel
def receipt : Certificate (.two6 14) 11 := ⟨batches, i33⟩
end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start (.two6 14)).plus a) (fullCap top)) : Covered top (.two6 14) a := by
  change 16+a.b ≤ 129 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 113 := by omega
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
end Band20


end Low53At2389PriceTableTwoBand20
