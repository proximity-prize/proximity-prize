import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableOne6
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Top1
private def b0 : PaidBatch .one6 1 := ⟨[
  .rectangle 1 3 127 8 24,
  .rectangle 3 9 127 14 27,
  .rectangle 5 15 127 25 51], by decide +kernel⟩
private def b1 : PaidBatch .one6 1 := ⟨[
  .rectangle 9 26 68 47 45,
  .rectangle 69 26 127 36 59,
  .rectangle 69 37 127 47 68], by decide +kernel⟩
private def batches : List (PaidBatch .one6 1) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 127 3 45 = true := by decide +kernel
def receipt : Certificate .one6 1 := ⟨batches, i3⟩
end Top1

namespace Top2
private def b0 : PaidBatch .one6 2 := ⟨[
  .rectangle 2 6 127 11 24,
  .rectangle 4 12 127 16 26,
  .rectangle 6 17 127 26 50], by decide +kernel⟩
private def b1 : PaidBatch .one6 2 := ⟨[
  .rectangle 9 27 68 47 47,
  .rectangle 69 27 127 37 62,
  .rectangle 69 38 127 47 69], by decide +kernel⟩
private def batches : List (PaidBatch .one6 2) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 127 6 42 = true := by decide +kernel
def receipt : Certificate .one6 2 := ⟨batches, i6⟩
end Top2

namespace Top3
private def b0 : PaidBatch .one6 3 := ⟨[
  .rectangle 3 9 127 18 45,
  .rectangle 7 19 127 28 52,
  .rectangle 10 29 68 47 47], by decide +kernel⟩
private def b1 : PaidBatch .one6 3 := ⟨[
  .rectangle 69 29 127 38 62,
  .rectangle 69 39 127 47 69], by decide +kernel⟩
private def batches : List (PaidBatch .one6 3) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 127 9 39 = true := by decide +kernel
def receipt : Certificate .one6 3 := ⟨batches, i9⟩
end Top3

namespace Top4
private def b0 : PaidBatch .one6 4 := ⟨[
  .rectangle 4 12 127 20 42,
  .rectangle 7 21 127 29 51,
  .rectangle 10 30 68 47 47], by decide +kernel⟩
private def b1 : PaidBatch .one6 4 := ⟨[
  .rectangle 69 30 127 38 61,
  .rectangle 69 39 127 47 70], by decide +kernel⟩
private def batches : List (PaidBatch .one6 4) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 127 12 36 = true := by decide +kernel
def receipt : Certificate .one6 4 := ⟨batches, i12⟩
end Top4

namespace Top5
private def b0 : PaidBatch .one6 5 := ⟨[
  .rectangle 5 15 127 23 44,
  .rectangle 8 24 127 31 51,
  .rectangle 11 32 69 47 47], by decide +kernel⟩
private def b1 : PaidBatch .one6 5 := ⟨[
  .rectangle 70 32 127 39 60,
  .rectangle 70 40 127 47 69], by decide +kernel⟩
private def batches : List (PaidBatch .one6 5) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 127 15 33 = true := by decide +kernel
def receipt : Certificate .one6 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch .one6 6 := ⟨[
  .rectangle 6 18 127 32 73,
  .rectangle 11 33 69 47 47,
  .rectangle 70 33 127 40 62], by decide +kernel⟩
private def b1 : PaidBatch .one6 6 := ⟨[
  .rectangle 70 41 127 47 68], by decide +kernel⟩
private def batches : List (PaidBatch .one6 6) := [b0, b1]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 127 18 30 = true := by decide +kernel
def receipt : Certificate .one6 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch .one6 7 := ⟨[
  .rectangle 7 21 127 34 71,
  .rectangle 12 35 69 47 45,
  .rectangle 70 35 127 47 81], by decide +kernel⟩
private def batches : List (PaidBatch .one6 7) := [b0]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 127 21 27 = true := by decide +kernel
def receipt : Certificate .one6 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch .one6 8 := ⟨[
  .rectangle 8 24 127 35 65,
  .rectangle 12 36 127 47 79], by decide +kernel⟩
private def batches : List (PaidBatch .one6 8) := [b0]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 127 24 24 = true := by decide +kernel
def receipt : Certificate .one6 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch .one6 9 := ⟨[
  .rectangle 9 27 127 37 65,
  .rectangle 13 38 127 47 75], by decide +kernel⟩
private def batches : List (PaidBatch .one6 9) := [b0]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 127 27 21 = true := by decide +kernel
def receipt : Certificate .one6 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch .one6 10 := ⟨[
  .rectangle 10 30 68 47 53,
  .rectangle 69 30 127 38 61,
  .rectangle 69 39 127 47 73], by decide +kernel⟩
private def batches : List (PaidBatch .one6 10) := [b0]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 127 30 18 = true := by decide +kernel
def receipt : Certificate .one6 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch .one6 11 := ⟨[
  .rectangle 11 33 69 47 49,
  .rectangle 70 33 127 40 62,
  .rectangle 70 41 127 47 69], by decide +kernel⟩
private def batches : List (PaidBatch .one6 11) := [b0]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 127 33 15 = true := by decide +kernel
def receipt : Certificate .one6 11 := ⟨batches, i33⟩
end Top11

namespace Top12
private def b0 : PaidBatch .one6 12 := ⟨[
  .rectangle 12 36 127 47 79], by decide +kernel⟩
private def batches : List (PaidBatch .one6 12) := [b0]
private abbrev tiles := tilesOf batches
private theorem i36 : checks tiles 127 36 12 = true := by decide +kernel
def receipt : Certificate .one6 12 := ⟨batches, i36⟩
end Top12

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .one6).plus a) (fullCap top)) : Covered top .one6 a := by
  change 2+a.b ≤ 129 ∧ 6+a.j ≤ 53 ∧ 1+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 127 := by omega
  have hj' : a.j ≤ 47 := by omega
  have hcases : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 ∨ a.t = 12 := by omega
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
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
  · exact Certificate.apply Top12.receipt a ha h12 hb' hj' ht htop

end Low53At2389PriceTableOne6
