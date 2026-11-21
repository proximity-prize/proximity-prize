import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6thin
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top1

private def batch0 : PaidBatch .two6thin 1 := ⟨[
  .rectangle 1 3 123 5 32,
  .rectangle 2 6 123 8 55,
  .rectangle 3 9 123 13 55,
  .rectangle 5 14 64 24 71,
  .rectangle 9 25 66 46 79,
  .rectangle 65 14 123 19 71], by decide +kernel⟩
private def batch1 : PaidBatch .two6thin 1 := ⟨[
  .rectangle 65 20 123 24 79,
  .rectangle 67 36 95 46 83,
  .rectangle 67 25 123 30 79,
  .rectangle 67 31 123 35 83,
  .rectangle 96 42 109 46 85,
  .rectangle 96 36 123 41 85], by decide +kernel⟩
private def batch2 : PaidBatch .two6thin 1 := ⟨[
  .rectangle 110 42 123 44 85,
  .rectangle 110 45 123 46 85], by decide +kernel⟩

private def batches : List (PaidBatch .two6thin 1) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 123 3 44 = true := by decide +kernel
private theorem covers : checks tiles 123 3 44 = true :=
  index3

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 3 .two6thin a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2

private def batch0 : PaidBatch .two6thin 2 := ⟨[
  .rectangle 2 6 123 11 55,
  .rectangle 4 12 123 16 71,
  .rectangle 6 17 64 26 71,
  .rectangle 9 27 66 46 79,
  .rectangle 65 17 123 26 79,
  .rectangle 67 37 95 46 83], by decide +kernel⟩
private def batch1 : PaidBatch .two6thin 2 := ⟨[
  .rectangle 67 27 123 31 79,
  .rectangle 67 32 123 36 83,
  .rectangle 96 42 109 46 85,
  .rectangle 96 37 123 41 85,
  .rectangle 110 42 123 44 85,
  .rectangle 110 45 123 46 85], by decide +kernel⟩

private def batches : List (PaidBatch .two6thin 2) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 123 6 41 = true := by decide +kernel
private theorem covers : checks tiles 123 6 41 = true :=
  index6

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 4 .two6thin a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3

private def batch0 : PaidBatch .two6thin 3 := ⟨[
  .rectangle 3 9 123 13 55,
  .rectangle 5 14 123 18 71,
  .rectangle 7 19 123 27 78,
  .rectangle 10 28 66 46 79,
  .rectangle 67 38 95 46 83,
  .rectangle 67 28 123 32 79], by decide +kernel⟩
private def batch1 : PaidBatch .two6thin 3 := ⟨[
  .rectangle 67 33 123 37 83,
  .rectangle 96 38 109 42 85,
  .rectangle 96 43 109 46 85,
  .rectangle 110 45 116 46 85,
  .rectangle 110 38 123 40 85,
  .rectangle 110 41 123 42 85], by decide +kernel⟩
private def batch2 : PaidBatch .two6thin 3 := ⟨[
  .rectangle 110 43 123 44 85,
  .rectangle 117 45 123 45 85,
  .rectangle 117 46 123 46 85], by decide +kernel⟩

private def batches : List (PaidBatch .two6thin 3) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 123 9 38 = true := by decide +kernel
private theorem covers : checks tiles 123 9 38 = true :=
  index9

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 5 .two6thin a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

namespace Top4

private def batch0 : PaidBatch .two6thin 4 := ⟨[
  .rectangle 4 12 123 20 71,
  .rectangle 7 21 123 29 79,
  .rectangle 10 30 66 46 79,
  .rectangle 67 39 95 46 85,
  .rectangle 67 30 123 34 83,
  .rectangle 67 35 123 38 83], by decide +kernel⟩
private def batch1 : PaidBatch .two6thin 4 := ⟨[
  .rectangle 96 39 109 42 85,
  .rectangle 96 43 109 46 85,
  .rectangle 110 45 116 46 85,
  .rectangle 110 39 123 40 85,
  .rectangle 110 41 123 42 85,
  .rectangle 110 43 123 44 85], by decide +kernel⟩
private def batch2 : PaidBatch .two6thin 4 := ⟨[
  .rectangle 117 46 120 46 85,
  .rectangle 117 45 123 45 85,
  .rectangle 121 46 122 46 85,
  .point 123 46 85], by decide +kernel⟩

private def batches : List (PaidBatch .two6thin 4) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 123 12 35 = true := by decide +kernel
private theorem covers : checks tiles 123 12 35 = true :=
  index12

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 6 .two6thin a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

namespace Top5

private def batch0 : PaidBatch .two6thin 5 := ⟨[
  .rectangle 5 15 123 22 71,
  .rectangle 8 23 123 30 79,
  .rectangle 11 31 67 46 79,
  .rectangle 68 39 95 46 85,
  .rectangle 68 31 123 34 83,
  .rectangle 68 35 123 38 84], by decide +kernel⟩
private def batch1 : PaidBatch .two6thin 5 := ⟨[
  .rectangle 96 39 109 42 85,
  .rectangle 96 43 109 46 85,
  .rectangle 110 43 116 44 85,
  .rectangle 110 45 116 46 85,
  .rectangle 110 39 123 40 85,
  .rectangle 110 41 123 42 85], by decide +kernel⟩
private def batch2 : PaidBatch .two6thin 5 := ⟨[
  .rectangle 117 46 120 46 85,
  .rectangle 117 43 123 43 85,
  .rectangle 117 44 123 44 85,
  .rectangle 117 45 123 45 85,
  .point 121 46 85,
  .point 122 46 85], by decide +kernel⟩
private def batch3 : PaidBatch .two6thin 5 := ⟨[
  .point 123 46 85], by decide +kernel⟩

private def batches : List (PaidBatch .two6thin 5) := [batch0, batch1, batch2, batch3]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 123 15 32 = true := by decide +kernel
private theorem covers : checks tiles 123 15 32 = true :=
  index15

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 7 .two6thin a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

namespace Top6

private def batch0 : PaidBatch .two6thin 6 := ⟨[
  .rectangle 6 18 123 25 77,
  .rectangle 9 26 123 32 79,
  .rectangle 11 33 67 46 79,
  .rectangle 68 33 95 39 83,
  .rectangle 68 40 95 46 85,
  .rectangle 96 40 109 43 85], by decide +kernel⟩
private def batch1 : PaidBatch .two6thin 6 := ⟨[
  .rectangle 96 44 109 46 85,
  .rectangle 96 33 123 36 83,
  .rectangle 96 37 123 39 85,
  .rectangle 110 44 116 45 85,
  .rectangle 110 46 116 46 85,
  .rectangle 110 40 123 41 85], by decide +kernel⟩
private def batch2 : PaidBatch .two6thin 6 := ⟨[
  .rectangle 110 42 123 43 85,
  .rectangle 117 46 118 46 85,
  .rectangle 117 45 120 45 85,
  .rectangle 117 44 123 44 85,
  .rectangle 119 46 119 46 85,
  .point 120 46 85], by decide +kernel⟩
private def batch3 : PaidBatch .two6thin 6 := ⟨[
  .point 121 46 85,
  .rectangle 121 45 122 45 85,
  .point 122 46 85,
  .point 123 45 85,
  .point 123 46 85], by decide +kernel⟩

private def batches : List (PaidBatch .two6thin 6) := [batch0, batch1, batch2, batch3]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 123 18 29 = true := by decide +kernel
private theorem covers : checks tiles 123 18 29 = true :=
  index18

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 8 .two6thin a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7

private def batch0 : PaidBatch .two6thin 7 := ⟨[
  .rectangle 7 21 65 33 79,
  .rectangle 12 34 67 46 79,
  .rectangle 66 21 123 27 79,
  .rectangle 66 28 123 33 79,
  .rectangle 68 34 95 40 83,
  .rectangle 68 41 95 46 85], by decide +kernel⟩
private def batch1 : PaidBatch .two6thin 7 := ⟨[
  .rectangle 96 41 109 43 85,
  .rectangle 96 44 109 46 85,
  .rectangle 96 34 123 37 83,
  .rectangle 96 38 123 40 85,
  .rectangle 110 44 116 45 85,
  .rectangle 110 46 116 46 85], by decide +kernel⟩
private def batch2 : PaidBatch .two6thin 7 := ⟨[
  .rectangle 110 41 123 42 85,
  .rectangle 110 43 123 43 85,
  .rectangle 117 46 118 46 85,
  .rectangle 117 45 120 45 85,
  .rectangle 117 44 123 44 85,
  .point 119 46 85], by decide +kernel⟩
private def batch3 : PaidBatch .two6thin 7 := ⟨[
  .point 120 46 85,
  .rectangle 121 45 121 45 85,
  .point 121 46 85,
  .point 122 45 85,
  .point 122 46 85,
  .point 123 45 85], by decide +kernel⟩
private def batch4 : PaidBatch .two6thin 7 := ⟨[
  .point 123 46 85], by decide +kernel⟩

private def batches : List (PaidBatch .two6thin 7) := [batch0, batch1, batch2, batch3, batch4]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 123 21 26 = true := by decide +kernel
private theorem covers : checks tiles 123 21 26 = true :=
  index21

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 9 .two6thin a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

namespace Top8

private def batch0 : PaidBatch .two6thin 8 := ⟨[
  .rectangle 8 24 65 35 79,
  .rectangle 12 36 67 46 79,
  .rectangle 66 24 123 29 79,
  .rectangle 66 30 123 35 83,
  .rectangle 68 36 95 41 84,
  .rectangle 68 42 95 46 85], by decide +kernel⟩
private def batch1 : PaidBatch .two6thin 8 := ⟨[
  .rectangle 96 42 109 44 85,
  .rectangle 96 45 109 46 85,
  .rectangle 96 36 123 38 85,
  .rectangle 96 39 123 41 85,
  .rectangle 110 45 116 45 85,
  .rectangle 110 46 116 46 85], by decide +kernel⟩
private def batch2 : PaidBatch .two6thin 8 := ⟨[
  .rectangle 110 42 123 43 85,
  .rectangle 110 44 123 44 85,
  .rectangle 117 46 118 46 85,
  .rectangle 117 45 120 45 85,
  .point 119 46 85,
  .point 120 46 85], by decide +kernel⟩
private def batch3 : PaidBatch .two6thin 8 := ⟨[
  .point 121 45 85,
  .point 121 46 85,
  .point 122 45 85,
  .point 122 46 85,
  .point 123 45 85,
  .point 123 46 85], by decide +kernel⟩

private def batches : List (PaidBatch .two6thin 8) := [batch0, batch1, batch2, batch3]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 123 24 23 = true := by decide +kernel
private theorem covers : checks tiles 123 24 23 = true :=
  index24

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 10 .two6thin a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

namespace Top9

private def batch0 : PaidBatch .two6thin 9 := ⟨[
  .rectangle 9 27 66 36 79,
  .rectangle 13 37 68 46 79,
  .rectangle 67 27 123 31 79,
  .rectangle 67 32 123 36 83,
  .rectangle 69 37 96 41 84,
  .rectangle 69 42 96 46 85], by decide +kernel⟩
private def batch1 : PaidBatch .two6thin 9 := ⟨[
  .rectangle 97 42 110 44 85,
  .rectangle 97 45 110 46 85,
  .rectangle 97 37 123 39 85,
  .rectangle 97 40 123 41 85,
  .rectangle 111 45 117 45 85,
  .rectangle 111 46 117 46 85], by decide +kernel⟩
private def batch2 : PaidBatch .two6thin 9 := ⟨[
  .rectangle 111 42 123 43 85,
  .rectangle 111 44 123 44 85,
  .rectangle 118 46 118 46 85,
  .rectangle 118 45 120 45 85,
  .point 119 46 85,
  .point 120 46 85], by decide +kernel⟩
private def batch3 : PaidBatch .two6thin 9 := ⟨[
  .point 121 45 85,
  .point 121 46 85,
  .point 122 45 85,
  .point 122 46 85,
  .point 123 45 85,
  .point 123 46 85], by decide +kernel⟩

private def batches : List (PaidBatch .two6thin 9) := [batch0, batch1, batch2, batch3]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 123 27 20 = true := by decide +kernel
private theorem covers : checks tiles 123 27 20 = true :=
  index27

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 11 .two6thin a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

namespace Top10

private def batch0 : PaidBatch .two6thin 10 := ⟨[
  .rectangle 10 30 66 46 79,
  .rectangle 67 39 95 46 85,
  .rectangle 67 30 123 34 83,
  .rectangle 67 35 123 38 83,
  .rectangle 96 39 109 42 85,
  .rectangle 96 43 109 46 85], by decide +kernel⟩
private def batch1 : PaidBatch .two6thin 10 := ⟨[
  .rectangle 110 43 116 44 85,
  .rectangle 110 45 116 45 85,
  .rectangle 110 46 116 46 85,
  .rectangle 110 39 123 40 85,
  .rectangle 110 41 123 42 85,
  .rectangle 117 46 118 46 85], by decide +kernel⟩
private def batch2 : PaidBatch .two6thin 10 := ⟨[
  .rectangle 117 45 120 45 85,
  .rectangle 117 43 123 43 85,
  .rectangle 117 44 123 44 85,
  .point 119 46 85,
  .point 120 46 85,
  .point 121 45 85], by decide +kernel⟩
private def batch3 : PaidBatch .two6thin 10 := ⟨[
  .point 121 46 85,
  .point 122 45 85,
  .point 122 46 85,
  .point 123 45 85,
  .point 123 46 85], by decide +kernel⟩

private def batches : List (PaidBatch .two6thin 10) := [batch0, batch1, batch2, batch3]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 123 30 17 = true := by decide +kernel
private theorem covers : checks tiles 123 30 17 = true :=
  index30

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 12 .two6thin a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

namespace Top11

private def batch0 : PaidBatch .two6thin 11 := ⟨[
  .rectangle 11 33 67 46 79,
  .rectangle 68 33 95 39 83,
  .rectangle 68 40 95 46 85,
  .rectangle 96 40 109 43 85,
  .rectangle 96 44 109 46 85,
  .rectangle 96 33 123 36 83], by decide +kernel⟩
private def batch1 : PaidBatch .two6thin 11 := ⟨[
  .rectangle 96 37 123 39 85,
  .rectangle 110 44 116 45 85,
  .rectangle 110 46 116 46 85,
  .rectangle 110 40 123 41 85,
  .rectangle 110 42 123 43 85,
  .rectangle 117 46 118 46 85], by decide +kernel⟩
private def batch2 : PaidBatch .two6thin 11 := ⟨[
  .rectangle 117 45 120 45 85,
  .rectangle 117 44 123 44 85,
  .point 119 46 85,
  .point 120 46 85,
  .rectangle 121 45 121 45 85,
  .point 121 46 85], by decide +kernel⟩
private def batch3 : PaidBatch .two6thin 11 := ⟨[
  .point 122 45 85,
  .point 122 46 85,
  .point 123 45 85,
  .point 123 46 85], by decide +kernel⟩

private def batches : List (PaidBatch .two6thin 11) := [batch0, batch1, batch2, batch3]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 123 33 14 = true := by decide +kernel
private theorem covers : checks tiles 123 33 14 = true :=
  index33

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 13 .two6thin a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

namespace Top12

private def batch0 : PaidBatch .two6thin 12 := ⟨[
  .rectangle 12 36 67 46 79,
  .rectangle 68 36 95 41 84,
  .rectangle 68 42 95 46 85,
  .rectangle 96 42 109 44 85,
  .rectangle 96 45 109 46 85,
  .rectangle 96 36 123 38 85], by decide +kernel⟩
private def batch1 : PaidBatch .two6thin 12 := ⟨[
  .rectangle 96 39 123 41 85,
  .rectangle 110 45 116 45 85,
  .rectangle 110 46 116 46 85,
  .rectangle 110 42 123 43 85,
  .rectangle 110 44 123 44 85,
  .rectangle 117 46 118 46 85], by decide +kernel⟩
private def batch2 : PaidBatch .two6thin 12 := ⟨[
  .rectangle 117 45 120 45 85,
  .point 119 46 85,
  .point 120 46 85,
  .rectangle 121 45 121 45 85,
  .point 121 46 85,
  .point 122 45 85], by decide +kernel⟩
private def batch3 : PaidBatch .two6thin 12 := ⟨[
  .point 122 46 85,
  .point 123 45 85,
  .point 123 46 85], by decide +kernel⟩

private def batches : List (PaidBatch .two6thin 12) := [batch0, batch1, batch2, batch3]
private abbrev tiles := tilesOf batches

private theorem index36 : checks tiles 123 36 11 = true := by decide +kernel
private theorem covers : checks tiles 123 36 11 = true :=
  index36

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 12)
    (hb : a.b ≤ 123) (hj : a.j ≤ 46) : Covered 14 .two6thin a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top12

theorem price (top : ℕ) (htop : top ≤ 14) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .two6thin).plus a) (fullCap top)) : Covered top .two6thin a := by
  change 2+a.b ≤ 125 ∧ 6+a.j ≤ 52 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have ht0 := ha.1
  have hb' : a.b ≤ 123 := by omega
  have hj' : a.j ≤ 46 := by omega
  have casesTop : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 ∨ a.t = 12 := by omega
  rcases casesTop with ht1 | ht2 | ht3 | ht4 | ht5 | ht6 | ht7 | ht8 | ht9 | ht10 | ht11 | ht12
  · exact covered_mono (Top1.exact a ha ht1 hb' hj') (by omega) htop
  · exact covered_mono (Top2.exact a ha ht2 hb' hj') (by omega) htop
  · exact covered_mono (Top3.exact a ha ht3 hb' hj') (by omega) htop
  · exact covered_mono (Top4.exact a ha ht4 hb' hj') (by omega) htop
  · exact covered_mono (Top5.exact a ha ht5 hb' hj') (by omega) htop
  · exact covered_mono (Top6.exact a ha ht6 hb' hj') (by omega) htop
  · exact covered_mono (Top7.exact a ha ht7 hb' hj') (by omega) htop
  · exact covered_mono (Top8.exact a ha ht8 hb' hj') (by omega) htop
  · exact covered_mono (Top9.exact a ha ht9 hb' hj') (by omega) htop
  · exact covered_mono (Top10.exact a ha ht10 hb' hj') (by omega) htop
  · exact covered_mono (Top11.exact a ha ht11 hb' hj') (by omega) htop
  · exact covered_mono (Top12.exact a ha ht12 hb' hj') (by omega) htop
end Compact50PriceTableTwo6thin
