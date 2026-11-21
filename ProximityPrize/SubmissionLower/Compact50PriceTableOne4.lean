import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableOne4
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top1

private def batch0 : PaidBatch .one4 1 := ⟨[
  .rectangle 1 3 123 3 1,
  .rectangle 2 4 123 4 8,
  .rectangle 2 5 123 5 18,
  .rectangle 2 6 123 8 26,
  .rectangle 3 9 123 14 39,
  .rectangle 5 15 123 25 52], by decide +kernel⟩
private def batch1 : PaidBatch .one4 1 := ⟨[
  .rectangle 9 26 66 48 54,
  .rectangle 67 26 123 37 62,
  .rectangle 67 38 123 48 65], by decide +kernel⟩

private def batches : List (PaidBatch .one4 1) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 123 3 46 = true := by decide +kernel
private theorem covers : checks tiles 123 3 46 = true :=
  index3

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 123) (hj : a.j ≤ 48) : Covered 2 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2

private def batch0 : PaidBatch .one4 2 := ⟨[
  .rectangle 2 6 123 11 26,
  .rectangle 4 12 123 16 47,
  .rectangle 6 17 123 27 54,
  .rectangle 10 28 66 48 61,
  .rectangle 67 28 123 38 62,
  .rectangle 67 39 123 48 65], by decide +kernel⟩

private def batches : List (PaidBatch .one4 2) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 123 6 43 = true := by decide +kernel
private theorem covers : checks tiles 123 6 43 = true :=
  index6

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 123) (hj : a.j ≤ 48) : Covered 3 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3

private def batch0 : PaidBatch .one4 3 := ⟨[
  .rectangle 3 9 123 13 39,
  .rectangle 5 14 123 18 47,
  .rectangle 7 19 123 28 54,
  .rectangle 10 29 66 48 61,
  .rectangle 67 29 123 38 62,
  .rectangle 67 39 123 48 65], by decide +kernel⟩

private def batches : List (PaidBatch .one4 3) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 123 9 40 = true := by decide +kernel
private theorem covers : checks tiles 123 9 40 = true :=
  index9

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 123) (hj : a.j ≤ 48) : Covered 4 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

namespace Top4

private def batch0 : PaidBatch .one4 4 := ⟨[
  .rectangle 4 12 123 21 47,
  .rectangle 8 22 123 30 54,
  .rectangle 11 31 67 48 61,
  .rectangle 68 31 123 39 62,
  .rectangle 68 40 123 48 65], by decide +kernel⟩

private def batches : List (PaidBatch .one4 4) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 123 12 37 = true := by decide +kernel
private theorem covers : checks tiles 123 12 37 = true :=
  index12

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 123) (hj : a.j ≤ 48) : Covered 5 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

namespace Top5

private def batch0 : PaidBatch .one4 5 := ⟨[
  .rectangle 5 15 123 23 52,
  .rectangle 8 24 123 31 54,
  .rectangle 11 32 67 48 61,
  .rectangle 68 32 123 40 62,
  .rectangle 68 41 123 48 65], by decide +kernel⟩

private def batches : List (PaidBatch .one4 5) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 123 15 34 = true := by decide +kernel
private theorem covers : checks tiles 123 15 34 = true :=
  index15

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 123) (hj : a.j ≤ 48) : Covered 6 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

namespace Top6

private def batch0 : PaidBatch .one4 6 := ⟨[
  .rectangle 6 18 123 25 54,
  .rectangle 9 26 123 33 54,
  .rectangle 12 34 67 48 61,
  .rectangle 68 34 123 41 62,
  .rectangle 68 42 123 48 65], by decide +kernel⟩

private def batches : List (PaidBatch .one4 6) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 123 18 31 = true := by decide +kernel
private theorem covers : checks tiles 123 18 31 = true :=
  index18

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 123) (hj : a.j ≤ 48) : Covered 7 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7

private def batch0 : PaidBatch .one4 7 := ⟨[
  .rectangle 7 21 123 27 54,
  .rectangle 10 28 123 34 61,
  .rectangle 12 35 67 48 61,
  .rectangle 68 35 123 41 62,
  .rectangle 68 42 123 48 65], by decide +kernel⟩

private def batches : List (PaidBatch .one4 7) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 123 21 28 = true := by decide +kernel
private theorem covers : checks tiles 123 21 28 = true :=
  index21

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 123) (hj : a.j ≤ 48) : Covered 8 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

namespace Top8

private def batch0 : PaidBatch .one4 8 := ⟨[
  .rectangle 8 24 65 36 54,
  .rectangle 13 37 68 48 61,
  .rectangle 66 24 123 30 54,
  .rectangle 66 31 123 36 61,
  .rectangle 69 37 123 42 62,
  .rectangle 69 43 123 48 65], by decide +kernel⟩

private def batches : List (PaidBatch .one4 8) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 123 24 25 = true := by decide +kernel
private theorem covers : checks tiles 123 24 25 = true :=
  index24

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 123) (hj : a.j ≤ 48) : Covered 9 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

namespace Top9

private def batch0 : PaidBatch .one4 9 := ⟨[
  .rectangle 9 27 123 37 61,
  .rectangle 13 38 68 48 61,
  .rectangle 69 38 123 43 65,
  .rectangle 69 44 123 48 65], by decide +kernel⟩

private def batches : List (PaidBatch .one4 9) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 123 27 22 = true := by decide +kernel
private theorem covers : checks tiles 123 27 22 = true :=
  index27

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 123) (hj : a.j ≤ 48) : Covered 10 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

namespace Top10

private def batch0 : PaidBatch .one4 10 := ⟨[
  .rectangle 10 30 66 48 61,
  .rectangle 67 40 95 48 65,
  .rectangle 67 30 123 39 62,
  .rectangle 96 40 123 44 65,
  .rectangle 96 45 123 48 65], by decide +kernel⟩

private def batches : List (PaidBatch .one4 10) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 123 30 19 = true := by decide +kernel
private theorem covers : checks tiles 123 30 19 = true :=
  index30

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 123) (hj : a.j ≤ 48) : Covered 11 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

namespace Top11

private def batch0 : PaidBatch .one4 11 := ⟨[
  .rectangle 11 33 67 48 61,
  .rectangle 68 41 95 48 65,
  .rectangle 68 33 123 40 62,
  .rectangle 96 41 123 44 65,
  .rectangle 96 45 123 48 65], by decide +kernel⟩

private def batches : List (PaidBatch .one4 11) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 123 33 16 = true := by decide +kernel
private theorem covers : checks tiles 123 33 16 = true :=
  index33

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 123) (hj : a.j ≤ 48) : Covered 12 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

namespace Top12

private def batch0 : PaidBatch .one4 12 := ⟨[
  .rectangle 12 36 67 48 61,
  .rectangle 68 36 123 42 62,
  .rectangle 68 43 123 48 65], by decide +kernel⟩

private def batches : List (PaidBatch .one4 12) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index36 : checks tiles 123 36 13 = true := by decide +kernel
private theorem covers : checks tiles 123 36 13 = true :=
  index36

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 12)
    (hb : a.b ≤ 123) (hj : a.j ≤ 48) : Covered 13 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top12

namespace Top13

private def batch0 : PaidBatch .one4 13 := ⟨[
  .rectangle 13 39 68 48 61,
  .rectangle 69 39 123 43 65,
  .rectangle 69 44 123 48 65], by decide +kernel⟩

private def batches : List (PaidBatch .one4 13) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index39 : checks tiles 123 39 10 = true := by decide +kernel
private theorem covers : checks tiles 123 39 10 = true :=
  index39

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 13)
    (hb : a.b ≤ 123) (hj : a.j ≤ 48) : Covered 14 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top13

theorem price (top : ℕ) (htop : top ≤ 14) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .one4).plus a) (fullCap top)) : Covered top .one4 a := by
  change 2+a.b ≤ 125 ∧ 4+a.j ≤ 52 ∧ 1+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have ht0 := ha.1
  have hb' : a.b ≤ 123 := by omega
  have hj' : a.j ≤ 48 := by omega
  have casesTop : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 ∨ a.t = 12 ∨ a.t = 13 := by omega
  rcases casesTop with ht1 | ht2 | ht3 | ht4 | ht5 | ht6 | ht7 | ht8 | ht9 | ht10 | ht11 | ht12 | ht13
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
  · exact covered_mono (Top13.exact a ha ht13 hb' hj') (by omega) htop
end Compact50PriceTableOne4
