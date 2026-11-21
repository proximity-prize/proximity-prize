import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableOne3
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top1

private def batch0 : PaidBatch .one3 1 := ⟨[
  .rectangle 1 3 124 3 1,
  .rectangle 2 4 63 4 1,
  .rectangle 2 5 63 5 6,
  .rectangle 2 6 124 8 14,
  .rectangle 3 9 124 14 30,
  .rectangle 5 15 64 26 44], by decide +kernel⟩
private def batch1 : PaidBatch .one3 1 := ⟨[
  .rectangle 9 27 66 49 52,
  .rectangle 64 4 124 4 44,
  .rectangle 64 5 124 5 45,
  .rectangle 65 15 124 26 51,
  .rectangle 67 39 95 49 57,
  .rectangle 67 27 124 32 52], by decide +kernel⟩
private def batch2 : PaidBatch .one3 1 := ⟨[
  .rectangle 67 33 124 38 57,
  .rectangle 96 39 124 44 58,
  .rectangle 96 45 124 49 58], by decide +kernel⟩

private def batches : List (PaidBatch .one3 1) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 124 3 47 = true := by decide +kernel
private theorem covers : checks tiles 124 3 47 = true :=
  index3

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 124) (hj : a.j ≤ 49) : Covered 2 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2

private def batch0 : PaidBatch .one3 2 := ⟨[
  .rectangle 2 6 124 8 14,
  .rectangle 3 9 124 11 30,
  .rectangle 4 12 124 16 30,
  .rectangle 6 17 65 27 44,
  .rectangle 10 28 67 49 52,
  .rectangle 66 17 124 27 51], by decide +kernel⟩
private def batch1 : PaidBatch .one3 2 := ⟨[
  .rectangle 68 39 96 49 57,
  .rectangle 68 28 124 38 56,
  .rectangle 97 39 124 44 58,
  .rectangle 97 45 124 49 58], by decide +kernel⟩

private def batches : List (PaidBatch .one3 2) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 124 6 44 = true := by decide +kernel
private theorem covers : checks tiles 124 6 44 = true :=
  index6

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 124) (hj : a.j ≤ 49) : Covered 3 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3

private def batch0 : PaidBatch .one3 3 := ⟨[
  .rectangle 3 9 124 14 30,
  .rectangle 5 15 124 19 44,
  .rectangle 7 20 124 29 49,
  .rectangle 10 30 67 49 52,
  .rectangle 68 40 96 49 57,
  .rectangle 68 30 124 39 56], by decide +kernel⟩
private def batch1 : PaidBatch .one3 3 := ⟨[
  .rectangle 97 40 124 44 58,
  .rectangle 97 45 124 49 58], by decide +kernel⟩

private def batches : List (PaidBatch .one3 3) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 124 9 41 = true := by decide +kernel
private theorem covers : checks tiles 124 9 41 = true :=
  index9

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 124) (hj : a.j ≤ 49) : Covered 4 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

namespace Top4

private def batch0 : PaidBatch .one3 4 := ⟨[
  .rectangle 4 12 124 16 30,
  .rectangle 6 17 124 21 44,
  .rectangle 8 22 124 30 49,
  .rectangle 11 31 67 49 52,
  .rectangle 68 41 96 49 57,
  .rectangle 68 31 124 35 56], by decide +kernel⟩
private def batch1 : PaidBatch .one3 4 := ⟨[
  .rectangle 68 36 124 40 57,
  .rectangle 97 41 124 45 58,
  .rectangle 97 46 124 49 60], by decide +kernel⟩

private def batches : List (PaidBatch .one3 4) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 124 12 38 = true := by decide +kernel
private theorem covers : checks tiles 124 12 38 = true :=
  index12

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 124) (hj : a.j ≤ 49) : Covered 5 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

namespace Top5

private def batch0 : PaidBatch .one3 5 := ⟨[
  .rectangle 5 15 124 23 44,
  .rectangle 8 24 124 32 52,
  .rectangle 11 33 67 49 52,
  .rectangle 68 42 96 49 57,
  .rectangle 68 33 124 37 57,
  .rectangle 68 38 124 41 57], by decide +kernel⟩
private def batch1 : PaidBatch .one3 5 := ⟨[
  .rectangle 97 42 124 45 58,
  .rectangle 97 46 124 49 60], by decide +kernel⟩

private def batches : List (PaidBatch .one3 5) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 124 15 35 = true := by decide +kernel
private theorem covers : checks tiles 124 15 35 = true :=
  index15

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 124) (hj : a.j ≤ 49) : Covered 6 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

namespace Top6

private def batch0 : PaidBatch .one3 6 := ⟨[
  .rectangle 6 18 124 25 44,
  .rectangle 9 26 124 33 52,
  .rectangle 12 34 68 49 52,
  .rectangle 69 42 96 49 58,
  .rectangle 69 34 124 41 58,
  .rectangle 97 42 124 45 58], by decide +kernel⟩
private def batch1 : PaidBatch .one3 6 := ⟨[
  .rectangle 97 46 124 49 60], by decide +kernel⟩

private def batches : List (PaidBatch .one3 6) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 124 18 32 = true := by decide +kernel
private theorem covers : checks tiles 124 18 32 = true :=
  index18

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 124) (hj : a.j ≤ 49) : Covered 7 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7

private def batch0 : PaidBatch .one3 7 := ⟨[
  .rectangle 7 21 124 28 49,
  .rectangle 10 29 124 35 52,
  .rectangle 12 36 68 49 52,
  .rectangle 69 43 96 49 58,
  .rectangle 69 36 124 42 58,
  .rectangle 97 43 124 46 58], by decide +kernel⟩
private def batch1 : PaidBatch .one3 7 := ⟨[
  .rectangle 97 47 124 49 60], by decide +kernel⟩

private def batches : List (PaidBatch .one3 7) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 124 21 29 = true := by decide +kernel
private theorem covers : checks tiles 124 21 29 = true :=
  index21

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 124) (hj : a.j ≤ 49) : Covered 8 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

namespace Top8

private def batch0 : PaidBatch .one3 8 := ⟨[
  .rectangle 8 24 66 36 52,
  .rectangle 13 37 68 49 52,
  .rectangle 67 24 124 30 52,
  .rectangle 67 31 124 36 52,
  .rectangle 69 44 96 49 58,
  .rectangle 69 37 124 43 58], by decide +kernel⟩
private def batch1 : PaidBatch .one3 8 := ⟨[
  .rectangle 97 44 124 46 58,
  .rectangle 97 47 124 49 60], by decide +kernel⟩

private def batches : List (PaidBatch .one3 8) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 124 24 26 = true := by decide +kernel
private theorem covers : checks tiles 124 24 26 = true :=
  index24

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 124) (hj : a.j ≤ 49) : Covered 9 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

namespace Top9

private def batch0 : PaidBatch .one3 9 := ⟨[
  .rectangle 9 27 66 38 52,
  .rectangle 13 39 68 49 52,
  .rectangle 67 27 124 32 52,
  .rectangle 67 33 124 38 57,
  .rectangle 69 45 96 49 58,
  .rectangle 69 39 124 44 58], by decide +kernel⟩
private def batch1 : PaidBatch .one3 9 := ⟨[
  .rectangle 97 45 110 49 58,
  .rectangle 111 45 124 47 58,
  .rectangle 111 48 124 49 60], by decide +kernel⟩

private def batches : List (PaidBatch .one3 9) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 124 27 23 = true := by decide +kernel
private theorem covers : checks tiles 124 27 23 = true :=
  index27

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 124) (hj : a.j ≤ 49) : Covered 10 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

namespace Top10

private def batch0 : PaidBatch .one3 10 := ⟨[
  .rectangle 10 30 67 39 52,
  .rectangle 14 40 69 49 52,
  .rectangle 68 30 124 34 56,
  .rectangle 68 35 124 39 57,
  .rectangle 70 45 97 49 58,
  .rectangle 70 40 124 44 58], by decide +kernel⟩
private def batch1 : PaidBatch .one3 10 := ⟨[
  .rectangle 98 45 124 47 58,
  .rectangle 98 48 124 49 60], by decide +kernel⟩

private def batches : List (PaidBatch .one3 10) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 124 30 20 = true := by decide +kernel
private theorem covers : checks tiles 124 30 20 = true :=
  index30

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 124) (hj : a.j ≤ 49) : Covered 11 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

namespace Top11

private def batch0 : PaidBatch .one3 11 := ⟨[
  .rectangle 11 33 67 49 52,
  .rectangle 68 42 96 49 57,
  .rectangle 68 33 124 37 57,
  .rectangle 68 38 124 41 57,
  .rectangle 97 46 110 49 60,
  .rectangle 97 42 124 45 58], by decide +kernel⟩
private def batch1 : PaidBatch .one3 11 := ⟨[
  .rectangle 111 46 124 47 60,
  .rectangle 111 48 124 49 60], by decide +kernel⟩

private def batches : List (PaidBatch .one3 11) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 124 33 17 = true := by decide +kernel
private theorem covers : checks tiles 124 33 17 = true :=
  index33

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 124) (hj : a.j ≤ 49) : Covered 12 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

namespace Top12

private def batch0 : PaidBatch .one3 12 := ⟨[
  .rectangle 12 36 68 49 52,
  .rectangle 69 43 96 49 58,
  .rectangle 69 36 124 42 58,
  .rectangle 97 43 124 46 58,
  .rectangle 97 47 124 49 60], by decide +kernel⟩

private def batches : List (PaidBatch .one3 12) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index36 : checks tiles 124 36 14 = true := by decide +kernel
private theorem covers : checks tiles 124 36 14 = true :=
  index36

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 12)
    (hb : a.b ≤ 124) (hj : a.j ≤ 49) : Covered 13 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top12

namespace Top13

private def batch0 : PaidBatch .one3 13 := ⟨[
  .rectangle 13 39 68 49 52,
  .rectangle 69 45 96 49 58,
  .rectangle 69 39 124 44 58,
  .rectangle 97 45 110 49 58,
  .rectangle 111 45 124 47 58,
  .rectangle 111 48 124 49 60], by decide +kernel⟩

private def batches : List (PaidBatch .one3 13) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index39 : checks tiles 124 39 11 = true := by decide +kernel
private theorem covers : checks tiles 124 39 11 = true :=
  index39

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 13)
    (hb : a.b ≤ 124) (hj : a.j ≤ 49) : Covered 14 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top13

theorem price (top : ℕ) (htop : top ≤ 14) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .one3).plus a) (fullCap top)) : Covered top .one3 a := by
  change 1+a.b ≤ 125 ∧ 3+a.j ≤ 52 ∧ 1+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have ht0 := ha.1
  have hb' : a.b ≤ 124 := by omega
  have hj' : a.j ≤ 49 := by omega
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
end Compact50PriceTableOne3
