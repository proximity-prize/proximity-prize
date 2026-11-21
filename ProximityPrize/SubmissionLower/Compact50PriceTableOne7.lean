import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableOne7
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top1

private def batch0 : PaidBatch .one7 1 := ⟨[
  .rectangle 1 3 122 8 21,
  .rectangle 3 9 122 13 20,
  .rectangle 5 14 122 24 44,
  .rectangle 9 25 122 45 81], by decide +kernel⟩

private def batches : List (PaidBatch .one7 1) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 122 3 43 = true := by decide +kernel
private theorem covers : checks tiles 122 3 43 = true :=
  index3

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 2 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2

private def batch0 : PaidBatch .one7 2 := ⟨[
  .rectangle 2 6 122 15 40,
  .rectangle 6 16 122 25 42,
  .rectangle 9 26 122 45 80], by decide +kernel⟩

private def batches : List (PaidBatch .one7 2) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 122 6 40 = true := by decide +kernel
private theorem covers : checks tiles 122 6 40 = true :=
  index6

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 3 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3

private def batch0 : PaidBatch .one7 3 := ⟨[
  .rectangle 3 9 122 18 39,
  .rectangle 7 19 122 27 42,
  .rectangle 10 28 122 45 77], by decide +kernel⟩

private def batches : List (PaidBatch .one7 3) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 122 9 37 = true := by decide +kernel
private theorem covers : checks tiles 122 9 37 = true :=
  index9

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 4 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

namespace Top4

private def batch0 : PaidBatch .one7 4 := ⟨[
  .rectangle 4 12 122 28 73,
  .rectangle 10 29 122 45 75], by decide +kernel⟩

private def batches : List (PaidBatch .one7 4) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 122 12 34 = true := by decide +kernel
private theorem covers : checks tiles 122 12 34 = true :=
  index12

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 5 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

namespace Top5

private def batch0 : PaidBatch .one7 5 := ⟨[
  .rectangle 5 15 122 30 67,
  .rectangle 11 31 122 45 72], by decide +kernel⟩

private def batches : List (PaidBatch .one7 5) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 122 15 31 = true := by decide +kernel
private theorem covers : checks tiles 122 15 31 = true :=
  index15

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 6 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

namespace Top6

private def batch0 : PaidBatch .one7 6 := ⟨[
  .rectangle 6 18 122 31 59,
  .rectangle 11 32 122 45 70], by decide +kernel⟩

private def batches : List (PaidBatch .one7 6) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 122 18 28 = true := by decide +kernel
private theorem covers : checks tiles 122 18 28 = true :=
  index18

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 7 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7

private def batch0 : PaidBatch .one7 7 := ⟨[
  .rectangle 7 21 122 33 58,
  .rectangle 12 34 122 45 67], by decide +kernel⟩

private def batches : List (PaidBatch .one7 7) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 122 21 25 = true := by decide +kernel
private theorem covers : checks tiles 122 21 25 = true :=
  index21

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 8 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

namespace Top8

private def batch0 : PaidBatch .one7 8 := ⟨[
  .rectangle 8 24 122 45 95], by decide +kernel⟩

private def batches : List (PaidBatch .one7 8) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 122 24 22 = true := by decide +kernel
private theorem covers : checks tiles 122 24 22 = true :=
  index24

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 9 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

namespace Top9

private def batch0 : PaidBatch .one7 9 := ⟨[
  .rectangle 9 27 122 45 85], by decide +kernel⟩

private def batches : List (PaidBatch .one7 9) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 122 27 19 = true := by decide +kernel
private theorem covers : checks tiles 122 27 19 = true :=
  index27

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 10 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

namespace Top10

private def batch0 : PaidBatch .one7 10 := ⟨[
  .rectangle 10 30 122 45 76], by decide +kernel⟩

private def batches : List (PaidBatch .one7 10) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 122 30 16 = true := by decide +kernel
private theorem covers : checks tiles 122 30 16 = true :=
  index30

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 11 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

namespace Top11

private def batch0 : PaidBatch .one7 11 := ⟨[
  .rectangle 11 33 122 45 69], by decide +kernel⟩

private def batches : List (PaidBatch .one7 11) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 122 33 13 = true := by decide +kernel
private theorem covers : checks tiles 122 33 13 = true :=
  index33

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 12 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

namespace Top12

private def batch0 : PaidBatch .one7 12 := ⟨[
  .rectangle 12 36 122 45 63], by decide +kernel⟩

private def batches : List (PaidBatch .one7 12) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index36 : checks tiles 122 36 10 = true := by decide +kernel
private theorem covers : checks tiles 122 36 10 = true :=
  index36

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 12)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 13 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top12

namespace Top13

private def batch0 : PaidBatch .one7 13 := ⟨[
  .rectangle 13 39 122 45 58], by decide +kernel⟩

private def batches : List (PaidBatch .one7 13) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index39 : checks tiles 122 39 7 = true := by decide +kernel
private theorem covers : checks tiles 122 39 7 = true :=
  index39

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 13)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 14 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top13

theorem price (top : ℕ) (htop : top ≤ 14) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .one7).plus a) (fullCap top)) : Covered top .one7 a := by
  change 3+a.b ≤ 125 ∧ 7+a.j ≤ 52 ∧ 1+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have ht0 := ha.1
  have hb' : a.b ≤ 122 := by omega
  have hj' : a.j ≤ 45 := by omega
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
end Compact50PriceTableOne7
