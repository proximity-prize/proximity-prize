import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableOne5
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top1

private def batch0 : PaidBatch .one5 1 := ⟨[
  .rectangle 1 3 123 4 3,
  .rectangle 2 5 123 5 4,
  .rectangle 2 6 123 8 11,
  .rectangle 3 9 123 14 24,
  .rectangle 5 15 123 25 46,
  .rectangle 9 26 66 47 41], by decide +kernel⟩
private def batch1 : PaidBatch .one5 1 := ⟨[
  .rectangle 67 26 123 36 54,
  .rectangle 67 37 123 47 62], by decide +kernel⟩

private def batches : List (PaidBatch .one5 1) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 123 3 45 = true := by decide +kernel
private theorem covers : checks tiles 123 3 45 = true :=
  index3

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 123) (hj : a.j ≤ 47) : Covered 2 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2

private def batch0 : PaidBatch .one5 2 := ⟨[
  .rectangle 2 6 123 11 22,
  .rectangle 4 12 123 16 24,
  .rectangle 6 17 123 26 45,
  .rectangle 9 27 66 47 43,
  .rectangle 67 27 123 37 56,
  .rectangle 67 38 123 47 62], by decide +kernel⟩

private def batches : List (PaidBatch .one5 2) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 123 6 42 = true := by decide +kernel
private theorem covers : checks tiles 123 6 42 = true :=
  index6

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 123) (hj : a.j ≤ 47) : Covered 3 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3

private def batch0 : PaidBatch .one5 3 := ⟨[
  .rectangle 3 9 123 18 41,
  .rectangle 7 19 123 28 47,
  .rectangle 10 29 66 47 43,
  .rectangle 67 29 123 38 56,
  .rectangle 67 39 123 47 62], by decide +kernel⟩

private def batches : List (PaidBatch .one5 3) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 123 9 39 = true := by decide +kernel
private theorem covers : checks tiles 123 9 39 = true :=
  index9

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 123) (hj : a.j ≤ 47) : Covered 4 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

namespace Top4

private def batch0 : PaidBatch .one5 4 := ⟨[
  .rectangle 4 12 123 20 38,
  .rectangle 7 21 123 29 46,
  .rectangle 10 30 66 47 43,
  .rectangle 67 30 123 38 55,
  .rectangle 67 39 123 47 64], by decide +kernel⟩

private def batches : List (PaidBatch .one5 4) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 123 12 36 = true := by decide +kernel
private theorem covers : checks tiles 123 12 36 = true :=
  index12

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 123) (hj : a.j ≤ 47) : Covered 5 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

namespace Top5

private def batch0 : PaidBatch .one5 5 := ⟨[
  .rectangle 5 15 123 23 41,
  .rectangle 8 24 123 31 47,
  .rectangle 11 32 67 47 43,
  .rectangle 68 32 123 39 55,
  .rectangle 68 40 123 47 63], by decide +kernel⟩

private def batches : List (PaidBatch .one5 5) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 123 15 33 = true := by decide +kernel
private theorem covers : checks tiles 123 15 33 = true :=
  index15

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 123) (hj : a.j ≤ 47) : Covered 6 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

namespace Top6

private def batch0 : PaidBatch .one5 6 := ⟨[
  .rectangle 6 18 123 25 40,
  .rectangle 9 26 123 32 46,
  .rectangle 11 33 67 47 43,
  .rectangle 68 33 123 40 57,
  .rectangle 68 41 123 47 62], by decide +kernel⟩

private def batches : List (PaidBatch .one5 6) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 123 18 30 = true := by decide +kernel
private theorem covers : checks tiles 123 18 30 = true :=
  index18

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 123) (hj : a.j ≤ 47) : Covered 7 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7

private def batch0 : PaidBatch .one5 7 := ⟨[
  .rectangle 7 21 123 27 40,
  .rectangle 10 28 123 34 48,
  .rectangle 12 35 67 47 41,
  .rectangle 68 35 123 41 56,
  .rectangle 68 42 123 47 61], by decide +kernel⟩

private def batches : List (PaidBatch .one5 7) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 123 21 27 = true := by decide +kernel
private theorem covers : checks tiles 123 21 27 = true :=
  index21

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 123) (hj : a.j ≤ 47) : Covered 8 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

namespace Top8

private def batch0 : PaidBatch .one5 8 := ⟨[
  .rectangle 8 24 123 35 60,
  .rectangle 12 36 67 47 41,
  .rectangle 68 36 123 41 55,
  .rectangle 68 42 123 47 62], by decide +kernel⟩

private def batches : List (PaidBatch .one5 8) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 123 24 24 = true := by decide +kernel
private theorem covers : checks tiles 123 24 24 = true :=
  index24

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 123) (hj : a.j ≤ 47) : Covered 9 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

namespace Top9

private def batch0 : PaidBatch .one5 9 := ⟨[
  .rectangle 9 27 123 37 59,
  .rectangle 13 38 68 47 40,
  .rectangle 69 38 123 47 69], by decide +kernel⟩

private def batches : List (PaidBatch .one5 9) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 123 27 21 = true := by decide +kernel
private theorem covers : checks tiles 123 27 21 = true :=
  index27

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 123) (hj : a.j ≤ 47) : Covered 10 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

namespace Top10

private def batch0 : PaidBatch .one5 10 := ⟨[
  .rectangle 10 30 66 47 49,
  .rectangle 67 30 123 38 56,
  .rectangle 67 39 123 47 67], by decide +kernel⟩

private def batches : List (PaidBatch .one5 10) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 123 30 18 = true := by decide +kernel
private theorem covers : checks tiles 123 30 18 = true :=
  index30

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 123) (hj : a.j ≤ 47) : Covered 11 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

namespace Top11

private def batch0 : PaidBatch .one5 11 := ⟨[
  .rectangle 11 33 67 47 45,
  .rectangle 68 33 123 40 57,
  .rectangle 68 41 123 47 64], by decide +kernel⟩

private def batches : List (PaidBatch .one5 11) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 123 33 15 = true := by decide +kernel
private theorem covers : checks tiles 123 33 15 = true :=
  index33

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 123) (hj : a.j ≤ 47) : Covered 12 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

namespace Top12

private def batch0 : PaidBatch .one5 12 := ⟨[
  .rectangle 12 36 67 47 42,
  .rectangle 68 36 123 41 55,
  .rectangle 68 42 123 47 62], by decide +kernel⟩

private def batches : List (PaidBatch .one5 12) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index36 : checks tiles 123 36 12 = true := by decide +kernel
private theorem covers : checks tiles 123 36 12 = true :=
  index36

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 12)
    (hb : a.b ≤ 123) (hj : a.j ≤ 47) : Covered 13 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top12

namespace Top13

private def batch0 : PaidBatch .one5 13 := ⟨[
  .rectangle 13 39 123 47 67], by decide +kernel⟩

private def batches : List (PaidBatch .one5 13) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index39 : checks tiles 123 39 9 = true := by decide +kernel
private theorem covers : checks tiles 123 39 9 = true :=
  index39

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 13)
    (hb : a.b ≤ 123) (hj : a.j ≤ 47) : Covered 14 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top13

theorem price (top : ℕ) (htop : top ≤ 14) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .one5).plus a) (fullCap top)) : Covered top .one5 a := by
  change 2+a.b ≤ 125 ∧ 5+a.j ≤ 52 ∧ 1+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have ht0 := ha.1
  have hb' : a.b ≤ 123 := by omega
  have hj' : a.j ≤ 47 := by omega
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
end Compact50PriceTableOne5
