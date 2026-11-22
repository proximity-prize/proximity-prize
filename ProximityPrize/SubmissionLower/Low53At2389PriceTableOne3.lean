import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableOne3
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Top1
private def b0 : PaidBatch .one3 1 := ⟨[
  .rectangle 1 3 128 3 1,
  .rectangle 2 4 65 4 1,
  .rectangle 2 5 128 5 4], by decide +kernel⟩
private def b1 : PaidBatch .one3 1 := ⟨[
  .rectangle 2 6 128 8 11,
  .rectangle 3 9 128 14 24,
  .rectangle 5 15 66 26 25], by decide +kernel⟩
private def b2 : PaidBatch .one3 1 := ⟨[
  .rectangle 9 27 68 50 44,
  .rectangle 66 4 128 4 2,
  .rectangle 67 15 128 26 50], by decide +kernel⟩
private def b3 : PaidBatch .one3 1 := ⟨[
  .rectangle 69 39 98 50 48,
  .rectangle 69 27 128 32 41,
  .rectangle 69 33 128 38 47], by decide +kernel⟩
private def b4 : PaidBatch .one3 1 := ⟨[
  .rectangle 99 39 128 44 52,
  .rectangle 99 45 128 50 57], by decide +kernel⟩
private def batches : List (PaidBatch .one3 1) := [b0, b1, b2, b3, b4]
private abbrev tiles := tilesOf batches
private theorem i3 : checks tiles 128 3 28 = true := by decide +kernel
private theorem i31 : checks tiles 128 31 20 = true := by decide +kernel
def receipt : Certificate .one3 1 := ⟨batches, checks_join i3 i31⟩
end Top1

namespace Top2
private def b0 : PaidBatch .one3 2 := ⟨[
  .rectangle 2 6 128 8 11,
  .rectangle 3 9 128 11 15,
  .rectangle 4 12 128 17 27], by decide +kernel⟩
private def b1 : PaidBatch .one3 2 := ⟨[
  .rectangle 6 18 67 28 25,
  .rectangle 10 29 69 50 45,
  .rectangle 68 18 128 28 49], by decide +kernel⟩
private def b2 : PaidBatch .one3 2 := ⟨[
  .rectangle 70 40 99 50 50,
  .rectangle 70 29 128 34 45,
  .rectangle 70 35 128 39 48], by decide +kernel⟩
private def b3 : PaidBatch .one3 2 := ⟨[
  .rectangle 100 40 128 45 55,
  .rectangle 100 46 128 50 58], by decide +kernel⟩
private def batches : List (PaidBatch .one3 2) := [b0, b1, b2, b3]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 128 6 36 = true := by decide +kernel
private theorem i42 : checks tiles 128 42 9 = true := by decide +kernel
def receipt : Certificate .one3 2 := ⟨batches, checks_join i6 i42⟩
end Top2

namespace Top3
private def b0 : PaidBatch .one3 3 := ⟨[
  .rectangle 3 9 128 14 24,
  .rectangle 5 15 128 19 28,
  .rectangle 7 20 128 29 48], by decide +kernel⟩
private def b1 : PaidBatch .one3 3 := ⟨[
  .rectangle 10 30 69 50 46,
  .rectangle 70 41 99 50 51,
  .rectangle 70 30 128 35 46], by decide +kernel⟩
private def b2 : PaidBatch .one3 3 := ⟨[
  .rectangle 70 36 128 40 50,
  .rectangle 100 46 114 50 53,
  .rectangle 100 41 128 45 55], by decide +kernel⟩
private def b3 : PaidBatch .one3 3 := ⟨[
  .rectangle 115 46 128 48 55,
  .rectangle 115 49 128 50 56], by decide +kernel⟩
private def batches : List (PaidBatch .one3 3) := [b0, b1, b2, b3]
private abbrev tiles := tilesOf batches
private theorem i9 : checks tiles 128 9 36 = true := by decide +kernel
private theorem i45 : checks tiles 128 45 6 = true := by decide +kernel
def receipt : Certificate .one3 3 := ⟨batches, checks_join i9 i45⟩
end Top3

namespace Top4
private def b0 : PaidBatch .one3 4 := ⟨[
  .rectangle 4 12 128 16 24,
  .rectangle 6 17 128 21 30,
  .rectangle 8 22 68 31 27], by decide +kernel⟩
private def b1 : PaidBatch .one3 4 := ⟨[
  .rectangle 11 32 69 50 46,
  .rectangle 69 22 128 31 51,
  .rectangle 70 42 99 50 51], by decide +kernel⟩
private def b2 : PaidBatch .one3 4 := ⟨[
  .rectangle 70 32 128 36 47,
  .rectangle 70 37 128 41 52,
  .rectangle 100 47 114 50 53], by decide +kernel⟩
private def b3 : PaidBatch .one3 4 := ⟨[
  .rectangle 100 42 128 46 57,
  .rectangle 115 47 128 48 55,
  .rectangle 115 49 128 50 57], by decide +kernel⟩
private def batches : List (PaidBatch .one3 4) := [b0, b1, b2, b3]
private abbrev tiles := tilesOf batches
private theorem i12 : checks tiles 128 12 33 = true := by decide +kernel
private theorem i45 : checks tiles 128 45 6 = true := by decide +kernel
def receipt : Certificate .one3 4 := ⟨batches, checks_join i12 i45⟩
end Top4

namespace Top5
private def b0 : PaidBatch .one3 5 := ⟨[
  .rectangle 5 15 128 23 41,
  .rectangle 8 24 128 32 50,
  .rectangle 11 33 69 50 46], by decide +kernel⟩
private def b1 : PaidBatch .one3 5 := ⟨[
  .rectangle 70 42 99 50 52,
  .rectangle 70 33 128 37 48,
  .rectangle 70 38 128 41 51], by decide +kernel⟩
private def b2 : PaidBatch .one3 5 := ⟨[
  .rectangle 100 47 114 50 54,
  .rectangle 100 42 128 46 58,
  .rectangle 115 47 128 48 56], by decide +kernel⟩
private def b3 : PaidBatch .one3 5 := ⟨[
  .rectangle 115 49 128 50 58], by decide +kernel⟩
private def batches : List (PaidBatch .one3 5) := [b0, b1, b2, b3]
private abbrev tiles := tilesOf batches
private theorem i15 : checks tiles 128 15 36 = true := by decide +kernel
def receipt : Certificate .one3 5 := ⟨batches, i15⟩
end Top5

namespace Top6
private def b0 : PaidBatch .one3 6 := ⟨[
  .rectangle 6 18 128 26 44,
  .rectangle 9 27 128 34 50,
  .rectangle 12 35 70 50 46], by decide +kernel⟩
private def b1 : PaidBatch .one3 6 := ⟨[
  .rectangle 71 35 99 42 46,
  .rectangle 71 43 99 50 52,
  .rectangle 100 47 114 50 55], by decide +kernel⟩
private def b2 : PaidBatch .one3 6 := ⟨[
  .rectangle 100 35 128 38 48,
  .rectangle 100 39 128 42 53,
  .rectangle 100 43 128 46 57], by decide +kernel⟩
private def b3 : PaidBatch .one3 6 := ⟨[
  .rectangle 115 47 128 48 57,
  .rectangle 115 49 128 50 59], by decide +kernel⟩
private def batches : List (PaidBatch .one3 6) := [b0, b1, b2, b3]
private abbrev tiles := tilesOf batches
private theorem i18 : checks tiles 128 18 33 = true := by decide +kernel
def receipt : Certificate .one3 6 := ⟨batches, i18⟩
end Top6

namespace Top7
private def b0 : PaidBatch .one3 7 := ⟨[
  .rectangle 7 21 128 28 43,
  .rectangle 10 29 128 35 50,
  .rectangle 12 36 70 50 45], by decide +kernel⟩
private def b1 : PaidBatch .one3 7 := ⟨[
  .rectangle 71 36 99 43 47,
  .rectangle 71 44 99 50 52,
  .rectangle 100 44 114 47 53], by decide +kernel⟩
private def b2 : PaidBatch .one3 7 := ⟨[
  .rectangle 100 48 114 50 54,
  .rectangle 100 36 128 39 50,
  .rectangle 100 40 128 43 54], by decide +kernel⟩
private def b3 : PaidBatch .one3 7 := ⟨[
  .rectangle 115 48 121 50 58,
  .rectangle 115 44 128 47 59,
  .rectangle 122 48 128 49 58], by decide +kernel⟩
private def b4 : PaidBatch .one3 7 := ⟨[
  .rectangle 122 50 128 50 58], by decide +kernel⟩
private def batches : List (PaidBatch .one3 7) := [b0, b1, b2, b3, b4]
private abbrev tiles := tilesOf batches
private theorem i21 : checks tiles 128 21 30 = true := by decide +kernel
def receipt : Certificate .one3 7 := ⟨batches, i21⟩
end Top7

namespace Top8
private def b0 : PaidBatch .one3 8 := ⟨[
  .rectangle 8 24 68 37 37,
  .rectangle 13 38 70 50 44,
  .rectangle 69 24 128 30 44], by decide +kernel⟩
private def b1 : PaidBatch .one3 8 := ⟨[
  .rectangle 69 31 128 37 52,
  .rectangle 71 38 99 44 47,
  .rectangle 71 45 99 50 51], by decide +kernel⟩
private def b2 : PaidBatch .one3 8 := ⟨[
  .rectangle 100 48 114 50 55,
  .rectangle 100 38 128 41 52,
  .rectangle 100 42 128 44 54], by decide +kernel⟩
private def b3 : PaidBatch .one3 8 := ⟨[
  .rectangle 100 45 128 47 58,
  .rectangle 115 48 121 50 58,
  .rectangle 122 48 128 49 59], by decide +kernel⟩
private def b4 : PaidBatch .one3 8 := ⟨[
  .rectangle 122 50 128 50 59], by decide +kernel⟩
private def batches : List (PaidBatch .one3 8) := [b0, b1, b2, b3, b4]
private abbrev tiles := tilesOf batches
private theorem i24 : checks tiles 128 24 27 = true := by decide +kernel
def receipt : Certificate .one3 8 := ⟨batches, i24⟩
end Top8

namespace Top9
private def b0 : PaidBatch .one3 9 := ⟨[
  .rectangle 9 27 68 38 35,
  .rectangle 13 39 70 50 43,
  .rectangle 69 27 128 32 44], by decide +kernel⟩
private def b1 : PaidBatch .one3 9 := ⟨[
  .rectangle 69 33 128 38 51,
  .rectangle 71 39 99 44 46,
  .rectangle 71 45 99 50 52], by decide +kernel⟩
private def b2 : PaidBatch .one3 9 := ⟨[
  .rectangle 100 48 114 50 55,
  .rectangle 100 39 128 41 51,
  .rectangle 100 42 128 44 54], by decide +kernel⟩
private def b3 : PaidBatch .one3 9 := ⟨[
  .rectangle 100 45 128 47 58,
  .rectangle 115 48 121 50 58,
  .rectangle 122 48 128 49 59], by decide +kernel⟩
private def b4 : PaidBatch .one3 9 := ⟨[
  .rectangle 122 50 128 50 59], by decide +kernel⟩
private def batches : List (PaidBatch .one3 9) := [b0, b1, b2, b3, b4]
private abbrev tiles := tilesOf batches
private theorem i27 : checks tiles 128 27 24 = true := by decide +kernel
def receipt : Certificate .one3 9 := ⟨batches, i27⟩
end Top9

namespace Top10
private def b0 : PaidBatch .one3 10 := ⟨[
  .rectangle 10 30 69 40 35,
  .rectangle 14 41 71 50 42,
  .rectangle 70 30 128 35 48], by decide +kernel⟩
private def b1 : PaidBatch .one3 10 := ⟨[
  .rectangle 70 36 128 40 52,
  .rectangle 72 46 100 50 51,
  .rectangle 72 41 128 45 58], by decide +kernel⟩
private def b2 : PaidBatch .one3 10 := ⟨[
  .rectangle 101 46 114 50 58,
  .rectangle 115 49 121 50 57,
  .rectangle 115 46 128 48 59], by decide +kernel⟩
private def b3 : PaidBatch .one3 10 := ⟨[
  .rectangle 122 49 128 49 58,
  .rectangle 122 50 128 50 59], by decide +kernel⟩
private def batches : List (PaidBatch .one3 10) := [b0, b1, b2, b3]
private abbrev tiles := tilesOf batches
private theorem i30 : checks tiles 128 30 21 = true := by decide +kernel
def receipt : Certificate .one3 10 := ⟨batches, i30⟩
end Top10

namespace Top11
private def b0 : PaidBatch .one3 11 := ⟨[
  .rectangle 11 33 69 50 51,
  .rectangle 70 42 99 50 56,
  .rectangle 70 33 128 37 48], by decide +kernel⟩
private def b1 : PaidBatch .one3 11 := ⟨[
  .rectangle 70 38 128 41 52,
  .rectangle 100 47 114 50 57,
  .rectangle 100 42 128 44 54], by decide +kernel⟩
private def b2 : PaidBatch .one3 11 := ⟨[
  .rectangle 100 45 128 46 56,
  .rectangle 115 49 121 50 57,
  .rectangle 115 47 128 48 58], by decide +kernel⟩
private def b3 : PaidBatch .one3 11 := ⟨[
  .rectangle 122 49 128 49 58,
  .rectangle 122 50 128 50 59], by decide +kernel⟩
private def batches : List (PaidBatch .one3 11) := [b0, b1, b2, b3]
private abbrev tiles := tilesOf batches
private theorem i33 : checks tiles 128 33 18 = true := by decide +kernel
def receipt : Certificate .one3 11 := ⟨batches, i33⟩
end Top11

namespace Top12
private def b0 : PaidBatch .one3 12 := ⟨[
  .rectangle 12 36 70 50 48,
  .rectangle 71 44 99 50 53,
  .rectangle 71 36 128 39 49], by decide +kernel⟩
private def b1 : PaidBatch .one3 12 := ⟨[
  .rectangle 71 40 128 43 54,
  .rectangle 100 44 114 47 53,
  .rectangle 100 48 114 50 56], by decide +kernel⟩
private def b2 : PaidBatch .one3 12 := ⟨[
  .rectangle 115 48 121 50 59,
  .rectangle 115 44 128 47 59,
  .rectangle 122 48 128 49 59], by decide +kernel⟩
private def b3 : PaidBatch .one3 12 := ⟨[
  .rectangle 122 50 128 50 59], by decide +kernel⟩
private def batches : List (PaidBatch .one3 12) := [b0, b1, b2, b3]
private abbrev tiles := tilesOf batches
private theorem i36 : checks tiles 128 36 15 = true := by decide +kernel
def receipt : Certificate .one3 12 := ⟨batches, i36⟩
end Top12

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .one3).plus a) (fullCap top)) : Covered top .one3 a := by
  change 1+a.b ≤ 129 ∧ 3+a.j ≤ 53 ∧ 1+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have hpos := ha.1
  have hb' : a.b ≤ 128 := by omega
  have hj' : a.j ≤ 50 := by omega
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

end Low53At2389PriceTableOne3
