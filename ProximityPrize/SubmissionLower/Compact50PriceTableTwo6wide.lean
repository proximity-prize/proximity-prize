import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6wide
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top1

private def batch0 : PaidBatch .two6wide 1 := ⟨[
  .rectangle 1 3 113 8 88,
  .rectangle 3 9 113 13 112,
  .rectangle 5 14 113 24 118,
  .rectangle 9 25 61 46 118,
  .rectangle 62 36 87 46 118,
  .rectangle 62 25 113 30 118], by decide +kernel⟩
private def batch1 : PaidBatch .two6wide 1 := ⟨[
  .rectangle 62 31 113 35 118,
  .rectangle 88 42 100 46 127,
  .rectangle 88 36 113 41 127,
  .rectangle 101 42 113 46 128], by decide +kernel⟩

private def batches : List (PaidBatch .two6wide 1) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 113 3 44 = true := by decide +kernel
private theorem covers : checks tiles 113 3 44 = true :=
  index3

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 113) (hj : a.j ≤ 46) : Covered 3 .two6wide a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2

private def batch0 : PaidBatch .two6wide 2 := ⟨[
  .rectangle 2 6 113 11 88,
  .rectangle 4 12 113 16 112,
  .rectangle 6 17 113 26 118,
  .rectangle 9 27 61 46 118,
  .rectangle 62 37 87 46 118,
  .rectangle 62 27 113 31 118], by decide +kernel⟩
private def batch1 : PaidBatch .two6wide 2 := ⟨[
  .rectangle 62 32 113 36 118,
  .rectangle 88 42 100 46 127,
  .rectangle 88 37 113 41 127,
  .rectangle 101 42 113 44 128,
  .rectangle 101 45 113 46 128], by decide +kernel⟩

private def batches : List (PaidBatch .two6wide 2) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 113 6 41 = true := by decide +kernel
private theorem covers : checks tiles 113 6 41 = true :=
  index6

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 113) (hj : a.j ≤ 46) : Covered 4 .two6wide a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3

private def batch0 : PaidBatch .two6wide 3 := ⟨[
  .rectangle 3 9 113 18 112,
  .rectangle 7 19 113 27 118,
  .rectangle 10 28 61 46 118,
  .rectangle 62 38 87 46 118,
  .rectangle 62 28 113 32 118,
  .rectangle 62 33 113 37 118], by decide +kernel⟩
private def batch1 : PaidBatch .two6wide 3 := ⟨[
  .rectangle 88 43 100 46 127,
  .rectangle 88 38 113 42 127,
  .rectangle 101 43 113 44 128,
  .rectangle 101 45 113 46 128], by decide +kernel⟩

private def batches : List (PaidBatch .two6wide 3) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 113 9 38 = true := by decide +kernel
private theorem covers : checks tiles 113 9 38 = true :=
  index9

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 113) (hj : a.j ≤ 46) : Covered 5 .two6wide a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

namespace Top4

private def batch0 : PaidBatch .two6wide 4 := ⟨[
  .rectangle 4 12 113 20 112,
  .rectangle 7 21 113 29 118,
  .rectangle 10 30 61 46 118,
  .rectangle 62 39 87 46 127,
  .rectangle 62 30 113 34 118,
  .rectangle 62 35 113 38 118], by decide +kernel⟩
private def batch1 : PaidBatch .two6wide 4 := ⟨[
  .rectangle 88 43 100 46 127,
  .rectangle 88 39 113 42 127,
  .rectangle 101 43 113 44 128,
  .rectangle 101 45 113 46 128], by decide +kernel⟩

private def batches : List (PaidBatch .two6wide 4) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 113 12 35 = true := by decide +kernel
private theorem covers : checks tiles 113 12 35 = true :=
  index12

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 113) (hj : a.j ≤ 46) : Covered 6 .two6wide a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

namespace Top5

private def batch0 : PaidBatch .two6wide 5 := ⟨[
  .rectangle 5 15 113 22 118,
  .rectangle 8 23 113 30 118,
  .rectangle 11 31 62 46 118,
  .rectangle 63 39 88 46 127,
  .rectangle 63 31 113 34 118,
  .rectangle 63 35 113 38 126], by decide +kernel⟩
private def batch1 : PaidBatch .two6wide 5 := ⟨[
  .rectangle 89 43 101 46 127,
  .rectangle 89 39 113 42 127,
  .rectangle 102 43 113 44 128,
  .rectangle 102 45 113 46 128], by decide +kernel⟩

private def batches : List (PaidBatch .two6wide 5) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 113 15 32 = true := by decide +kernel
private theorem covers : checks tiles 113 15 32 = true :=
  index15

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 113) (hj : a.j ≤ 46) : Covered 7 .two6wide a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

namespace Top6

private def batch0 : PaidBatch .two6wide 6 := ⟨[
  .rectangle 6 18 113 25 118,
  .rectangle 9 26 113 32 118,
  .rectangle 11 33 62 46 118,
  .rectangle 63 33 88 39 126,
  .rectangle 63 40 88 46 127,
  .rectangle 89 44 101 46 127], by decide +kernel⟩
private def batch1 : PaidBatch .two6wide 6 := ⟨[
  .rectangle 89 33 113 36 126,
  .rectangle 89 37 113 39 127,
  .rectangle 89 40 113 43 127,
  .rectangle 102 44 113 45 128,
  .rectangle 102 46 113 46 128], by decide +kernel⟩

private def batches : List (PaidBatch .two6wide 6) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 113 18 29 = true := by decide +kernel
private theorem covers : checks tiles 113 18 29 = true :=
  index18

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 113) (hj : a.j ≤ 46) : Covered 8 .two6wide a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7

private def batch0 : PaidBatch .two6wide 7 := ⟨[
  .rectangle 7 21 60 33 118,
  .rectangle 12 34 62 46 118,
  .rectangle 61 21 113 27 118,
  .rectangle 61 28 113 33 118,
  .rectangle 63 34 88 40 126,
  .rectangle 63 41 88 46 127], by decide +kernel⟩
private def batch1 : PaidBatch .two6wide 7 := ⟨[
  .rectangle 89 44 101 46 127,
  .rectangle 89 34 113 37 126,
  .rectangle 89 38 113 40 127,
  .rectangle 89 41 113 43 127,
  .rectangle 102 44 113 45 128,
  .rectangle 102 46 113 46 128], by decide +kernel⟩

private def batches : List (PaidBatch .two6wide 7) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 113 21 26 = true := by decide +kernel
private theorem covers : checks tiles 113 21 26 = true :=
  index21

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 113) (hj : a.j ≤ 46) : Covered 9 .two6wide a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

namespace Top8

private def batch0 : PaidBatch .two6wide 8 := ⟨[
  .rectangle 8 24 60 35 118,
  .rectangle 12 36 62 46 118,
  .rectangle 61 24 113 29 118,
  .rectangle 61 30 113 35 118,
  .rectangle 63 36 88 41 127,
  .rectangle 63 42 88 46 127], by decide +kernel⟩
private def batch1 : PaidBatch .two6wide 8 := ⟨[
  .rectangle 89 45 101 46 128,
  .rectangle 89 36 113 38 127,
  .rectangle 89 39 113 41 127,
  .rectangle 89 42 113 44 127,
  .rectangle 102 45 107 46 128,
  .rectangle 108 45 113 45 128], by decide +kernel⟩
private def batch2 : PaidBatch .two6wide 8 := ⟨[
  .rectangle 108 46 113 46 128], by decide +kernel⟩

private def batches : List (PaidBatch .two6wide 8) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 113 24 23 = true := by decide +kernel
private theorem covers : checks tiles 113 24 23 = true :=
  index24

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 113) (hj : a.j ≤ 46) : Covered 10 .two6wide a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

namespace Top9

private def batch0 : PaidBatch .two6wide 9 := ⟨[
  .rectangle 9 27 61 36 118,
  .rectangle 13 37 63 46 118,
  .rectangle 62 27 113 31 118,
  .rectangle 62 32 113 36 118,
  .rectangle 64 42 88 46 127,
  .rectangle 64 37 113 41 127], by decide +kernel⟩
private def batch1 : PaidBatch .two6wide 9 := ⟨[
  .rectangle 89 45 101 46 128,
  .rectangle 89 42 113 44 127,
  .rectangle 102 45 107 46 128,
  .rectangle 108 45 113 45 128,
  .rectangle 108 46 113 46 128], by decide +kernel⟩

private def batches : List (PaidBatch .two6wide 9) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 113 27 20 = true := by decide +kernel
private theorem covers : checks tiles 113 27 20 = true :=
  index27

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 113) (hj : a.j ≤ 46) : Covered 11 .two6wide a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

namespace Top10

private def batch0 : PaidBatch .two6wide 10 := ⟨[
  .rectangle 10 30 61 46 118,
  .rectangle 62 39 87 46 127,
  .rectangle 62 30 113 34 118,
  .rectangle 62 35 113 38 118,
  .rectangle 88 43 100 46 127,
  .rectangle 88 39 113 42 127], by decide +kernel⟩
private def batch1 : PaidBatch .two6wide 10 := ⟨[
  .rectangle 101 45 107 46 128,
  .rectangle 101 43 113 44 128,
  .rectangle 108 45 113 45 128,
  .rectangle 108 46 113 46 128], by decide +kernel⟩

private def batches : List (PaidBatch .two6wide 10) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 113 30 17 = true := by decide +kernel
private theorem covers : checks tiles 113 30 17 = true :=
  index30

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 113) (hj : a.j ≤ 46) : Covered 12 .two6wide a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

namespace Top11

private def batch0 : PaidBatch .two6wide 11 := ⟨[
  .rectangle 11 33 62 46 118,
  .rectangle 63 40 88 46 127,
  .rectangle 63 33 113 39 126,
  .rectangle 89 44 101 46 127,
  .rectangle 89 40 113 43 127,
  .rectangle 102 44 113 45 128], by decide +kernel⟩
private def batch1 : PaidBatch .two6wide 11 := ⟨[
  .rectangle 102 46 113 46 128], by decide +kernel⟩

private def batches : List (PaidBatch .two6wide 11) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 113 33 14 = true := by decide +kernel
private theorem covers : checks tiles 113 33 14 = true :=
  index33

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 113) (hj : a.j ≤ 46) : Covered 13 .two6wide a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

namespace Top12

private def batch0 : PaidBatch .two6wide 12 := ⟨[
  .rectangle 12 36 62 46 118,
  .rectangle 63 42 88 46 127,
  .rectangle 63 36 113 41 127,
  .rectangle 89 42 113 44 127,
  .rectangle 89 45 113 46 128], by decide +kernel⟩

private def batches : List (PaidBatch .two6wide 12) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index36 : checks tiles 113 36 11 = true := by decide +kernel
private theorem covers : checks tiles 113 36 11 = true :=
  index36

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 12)
    (hb : a.b ≤ 113) (hj : a.j ≤ 46) : Covered 14 .two6wide a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top12

theorem price (top : ℕ) (htop : top ≤ 14) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .two6wide).plus a) (fullCap top)) : Covered top .two6wide a := by
  change 12+a.b ≤ 125 ∧ 6+a.j ≤ 52 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have ht0 := ha.1
  have hb' : a.b ≤ 113 := by omega
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
end Compact50PriceTableTwo6wide
