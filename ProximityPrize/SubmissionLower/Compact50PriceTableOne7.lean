import ProximityPrize.SubmissionLower.Compact50Cover
import ProximityPrize.SubmissionLower.Compact50PriceTableOne6 -- serialize candidate build

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
  .rectangle 1 3 126 10 63,
  .rectangle 4 11 126 18 81,
  .rectangle 7 19 126 26 92,
  .rectangle 9 27 126 34 100,
  .rectangle 12 35 126 42 100,
  .rectangle 15 43 126 46 100], by decide +kernel⟩

private def batches : List (PaidBatch .one7 1) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 126 3 25 = true := by decide +kernel
private theorem index28 : checks tiles 126 28 19 = true := by decide +kernel
private theorem covers : checks tiles 126 3 44 = true :=
  checks_join (index3) index28

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 2 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2
private def batch0 : PaidBatch .one7 2 := ⟨[
  .rectangle 2 6 126 13 81,
  .rectangle 5 14 126 21 92,
  .rectangle 8 22 126 29 92,
  .rectangle 10 30 126 37 100,
  .rectangle 13 38 126 45 100,
  .rectangle 16 46 126 46 100], by decide +kernel⟩

private def batches : List (PaidBatch .one7 2) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 126 6 25 = true := by decide +kernel
private theorem index31 : checks tiles 126 31 16 = true := by decide +kernel
private theorem covers : checks tiles 126 6 41 = true :=
  checks_join (index6) index31

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 3 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3
private def batch0 : PaidBatch .one7 3 := ⟨[
  .rectangle 3 9 126 16 81,
  .rectangle 6 17 126 24 92,
  .rectangle 9 25 126 32 100,
  .rectangle 11 33 126 40 100,
  .rectangle 14 41 126 46 100], by decide +kernel⟩

private def batches : List (PaidBatch .one7 3) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 126 9 25 = true := by decide +kernel
private theorem index34 : checks tiles 126 34 13 = true := by decide +kernel
private theorem covers : checks tiles 126 9 38 = true :=
  checks_join (index9) index34

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 4 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

namespace Top4
private def batch0 : PaidBatch .one7 4 := ⟨[
  .rectangle 4 12 126 19 92,
  .rectangle 7 20 126 27 92,
  .rectangle 10 28 126 35 100,
  .rectangle 12 36 126 43 100,
  .rectangle 15 44 126 46 100], by decide +kernel⟩

private def batches : List (PaidBatch .one7 4) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 126 12 25 = true := by decide +kernel
private theorem index37 : checks tiles 126 37 10 = true := by decide +kernel
private theorem covers : checks tiles 126 12 35 = true :=
  checks_join (index12) index37

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 5 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

namespace Top5
private def batch0 : PaidBatch .one7 5 := ⟨[
  .rectangle 5 15 126 22 92,
  .rectangle 8 23 126 30 92,
  .rectangle 11 31 126 38 100,
  .rectangle 13 39 126 46 100], by decide +kernel⟩

private def batches : List (PaidBatch .one7 5) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 126 15 25 = true := by decide +kernel
private theorem index40 : checks tiles 126 40 7 = true := by decide +kernel
private theorem covers : checks tiles 126 15 32 = true :=
  checks_join (index15) index40

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 6 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

namespace Top6
private def batch0 : PaidBatch .one7 6 := ⟨[
  .rectangle 6 18 126 25 92,
  .rectangle 9 26 126 33 100,
  .rectangle 12 34 126 41 100,
  .rectangle 14 42 126 46 100], by decide +kernel⟩

private def batches : List (PaidBatch .one7 6) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 126 18 25 = true := by decide +kernel
private theorem index43 : checks tiles 126 43 4 = true := by decide +kernel
private theorem covers : checks tiles 126 18 29 = true :=
  checks_join (index18) index43

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 7 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7
private def batch0 : PaidBatch .one7 7 := ⟨[
  .rectangle 7 21 126 28 92,
  .rectangle 10 29 126 36 100,
  .rectangle 13 37 126 44 100,
  .rectangle 15 45 126 46 100], by decide +kernel⟩

private def batches : List (PaidBatch .one7 7) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 126 21 25 = true := by decide +kernel
private theorem index46 : checks tiles 126 46 1 = true := by decide +kernel
private theorem covers : checks tiles 126 21 26 = true :=
  checks_join (index21) index46

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 8 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

namespace Top8
private def batch0 : PaidBatch .one7 8 := ⟨[
  .rectangle 8 24 126 31 100,
  .rectangle 11 32 126 39 100,
  .rectangle 14 40 126 46 100], by decide +kernel⟩

private def batches : List (PaidBatch .one7 8) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 126 24 23 = true := by decide +kernel
private theorem covers : checks tiles 126 24 23 = true :=
  index24

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 9 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

namespace Top9
private def batch0 : PaidBatch .one7 9 := ⟨[
  .rectangle 9 27 126 34 100,
  .rectangle 12 35 126 42 100,
  .rectangle 15 43 126 46 100], by decide +kernel⟩

private def batches : List (PaidBatch .one7 9) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 126 27 20 = true := by decide +kernel
private theorem covers : checks tiles 126 27 20 = true :=
  index27

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 10 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

namespace Top10
private def batch0 : PaidBatch .one7 10 := ⟨[
  .rectangle 10 30 126 37 100,
  .rectangle 13 38 126 45 100,
  .rectangle 16 46 126 46 100], by decide +kernel⟩

private def batches : List (PaidBatch .one7 10) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 126 30 17 = true := by decide +kernel
private theorem covers : checks tiles 126 30 17 = true :=
  index30

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 11 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

namespace Top11
private def batch0 : PaidBatch .one7 11 := ⟨[
  .rectangle 11 33 126 40 100,
  .rectangle 14 41 126 46 100], by decide +kernel⟩

private def batches : List (PaidBatch .one7 11) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 126 33 14 = true := by decide +kernel
private theorem covers : checks tiles 126 33 14 = true :=
  index33

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 12 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

namespace Top12
private def batch0 : PaidBatch .one7 12 := ⟨[
  .rectangle 12 36 126 43 100,
  .rectangle 15 44 126 46 100], by decide +kernel⟩

private def batches : List (PaidBatch .one7 12) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index36 : checks tiles 126 36 11 = true := by decide +kernel
private theorem covers : checks tiles 126 36 11 = true :=
  index36

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 12)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 13 .one7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top12

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .one7).plus a) (fullCap top)) : Covered top .one7 a := by
  change 3+a.b ≤ 129 ∧ 7+a.j ≤ 53 ∧ 1+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have ht0 := ha.1
  have hb' : a.b ≤ 126 := by omega
  have hj' : a.j ≤ 46 := by omega
  have casesTop : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 ∨ a.t = 12 := by omega
  rcases casesTop with ht1 | ht2 | ht3 | ht4 | ht5 | ht6 | ht7 | ht8 | ht9 | ht10 | ht11 | ht12
  · exact covered_mono (Top1.exact a ha ht1 hb' hj') (by omega) (htop.trans (by decide))
  · exact covered_mono (Top2.exact a ha ht2 hb' hj') (by omega) (htop.trans (by decide))
  · exact covered_mono (Top3.exact a ha ht3 hb' hj') (by omega) (htop.trans (by decide))
  · exact covered_mono (Top4.exact a ha ht4 hb' hj') (by omega) (htop.trans (by decide))
  · exact covered_mono (Top5.exact a ha ht5 hb' hj') (by omega) (htop.trans (by decide))
  · exact covered_mono (Top6.exact a ha ht6 hb' hj') (by omega) (htop.trans (by decide))
  · exact covered_mono (Top7.exact a ha ht7 hb' hj') (by omega) (htop.trans (by decide))
  · exact covered_mono (Top8.exact a ha ht8 hb' hj') (by omega) (htop.trans (by decide))
  · exact covered_mono (Top9.exact a ha ht9 hb' hj') (by omega) (htop.trans (by decide))
  · exact covered_mono (Top10.exact a ha ht10 hb' hj') (by omega) (htop.trans (by decide))
  · exact covered_mono (Top11.exact a ha ht11 hb' hj') (by omega) (htop.trans (by decide))
  · exact covered_mono (Top12.exact a ha ht12 hb' hj') (by omega) (htop.trans (by decide))
end Compact50PriceTableOne7
