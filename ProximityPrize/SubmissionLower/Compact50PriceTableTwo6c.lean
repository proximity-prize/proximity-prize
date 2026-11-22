import ProximityPrize.SubmissionLower.Compact50Cover
import ProximityPrize.SubmissionLower.Compact50PriceTableTwo6b -- serialize candidate build

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6c
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top1
private def batch0 : PaidBatch .two6c 1 := ⟨[
  .rectangle 1 3 115 10 72,
  .rectangle 4 11 117 18 99,
  .rectangle 7 19 117 26 105,
  .rectangle 9 27 117 34 105,
  .rectangle 12 35 116 42 105,
  .rectangle 15 43 117 47 105], by decide +kernel⟩
private def batch1 : PaidBatch .two6c 1 := ⟨[
  .rectangle 116 3 117 9 72,
  .rectangle 116 10 117 17 99,
  .rectangle 117 35 117 42 114], by decide +kernel⟩

private def batches : List (PaidBatch .two6c 1) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 117 3 25 = true := by decide +kernel
private theorem index28 : checks tiles 117 28 20 = true := by decide +kernel
private theorem covers : checks tiles 117 3 45 = true :=
  checks_join (index3) index28

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 117) (hj : a.j ≤ 47) : Covered 3 .two6c a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2
private def batch0 : PaidBatch .two6c 2 := ⟨[
  .rectangle 2 6 117 13 72,
  .rectangle 5 14 117 21 105,
  .rectangle 8 22 117 29 105,
  .rectangle 10 30 117 37 105,
  .rectangle 13 38 109 45 105,
  .rectangle 16 46 117 47 105], by decide +kernel⟩
private def batch1 : PaidBatch .two6c 2 := ⟨[
  .rectangle 110 38 117 45 114], by decide +kernel⟩

private def batches : List (PaidBatch .two6c 2) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 117 6 25 = true := by decide +kernel
private theorem index31 : checks tiles 117 31 17 = true := by decide +kernel
private theorem covers : checks tiles 117 6 42 = true :=
  checks_join (index6) index31

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 117) (hj : a.j ≤ 47) : Covered 4 .two6c a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3
private def batch0 : PaidBatch .two6c 3 := ⟨[
  .rectangle 3 9 117 16 99,
  .rectangle 6 17 117 24 105,
  .rectangle 9 25 117 32 105,
  .rectangle 11 33 115 40 105,
  .rectangle 14 41 107 47 105,
  .rectangle 108 41 116 47 115], by decide +kernel⟩
private def batch1 : PaidBatch .two6c 3 := ⟨[
  .rectangle 116 33 117 40 114,
  .rectangle 117 41 117 46 115,
  .rectangle 117 47 117 47 115], by decide +kernel⟩

private def batches : List (PaidBatch .two6c 3) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 117 9 25 = true := by decide +kernel
private theorem index34 : checks tiles 117 34 14 = true := by decide +kernel
private theorem covers : checks tiles 117 9 39 = true :=
  checks_join (index9) index34

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 117) (hj : a.j ≤ 47) : Covered 5 .two6c a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

namespace Top4
private def batch0 : PaidBatch .two6c 4 := ⟨[
  .rectangle 4 12 117 19 99,
  .rectangle 7 20 117 27 105,
  .rectangle 10 28 117 35 105,
  .rectangle 12 36 109 43 105,
  .rectangle 15 44 113 47 105,
  .rectangle 110 36 117 43 114], by decide +kernel⟩
private def batch1 : PaidBatch .two6c 4 := ⟨[
  .rectangle 114 44 117 47 115], by decide +kernel⟩

private def batches : List (PaidBatch .two6c 4) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 117 12 25 = true := by decide +kernel
private theorem index37 : checks tiles 117 37 11 = true := by decide +kernel
private theorem covers : checks tiles 117 12 36 = true :=
  checks_join (index12) index37

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 117) (hj : a.j ≤ 47) : Covered 6 .two6c a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

namespace Top5
private def batch0 : PaidBatch .two6c 5 := ⟨[
  .rectangle 5 15 117 22 105,
  .rectangle 8 23 117 30 105,
  .rectangle 11 31 117 38 105,
  .rectangle 13 39 103 46 105,
  .rectangle 16 47 117 47 105,
  .rectangle 104 39 116 45 114], by decide +kernel⟩
private def batch1 : PaidBatch .two6c 5 := ⟨[
  .rectangle 104 46 117 47 115,
  .rectangle 117 39 117 44 114,
  .rectangle 117 45 117 47 115], by decide +kernel⟩

private def batches : List (PaidBatch .two6c 5) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 117 15 25 = true := by decide +kernel
private theorem index40 : checks tiles 117 40 8 = true := by decide +kernel
private theorem covers : checks tiles 117 15 33 = true :=
  checks_join (index15) index40

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 117) (hj : a.j ≤ 47) : Covered 7 .two6c a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

namespace Top6
private def batch0 : PaidBatch .two6c 6 := ⟨[
  .rectangle 6 18 117 25 105,
  .rectangle 9 26 117 33 105,
  .rectangle 12 34 111 41 105,
  .rectangle 14 42 105 47 105,
  .rectangle 106 42 117 46 115,
  .rectangle 106 47 117 47 115], by decide +kernel⟩
private def batch1 : PaidBatch .two6c 6 := ⟨[
  .rectangle 112 34 117 41 114], by decide +kernel⟩

private def batches : List (PaidBatch .two6c 6) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 117 18 25 = true := by decide +kernel
private theorem index43 : checks tiles 117 43 5 = true := by decide +kernel
private theorem covers : checks tiles 117 18 30 = true :=
  checks_join (index18) index43

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 117) (hj : a.j ≤ 47) : Covered 8 .two6c a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7
private def batch0 : PaidBatch .two6c 7 := ⟨[
  .rectangle 7 21 117 28 105,
  .rectangle 10 29 117 36 105,
  .rectangle 13 37 105 44 105,
  .rectangle 15 45 113 47 105,
  .rectangle 106 37 117 43 114,
  .rectangle 106 44 117 47 115], by decide +kernel⟩

private def batches : List (PaidBatch .two6c 7) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 117 21 25 = true := by decide +kernel
private theorem index46 : checks tiles 117 46 2 = true := by decide +kernel
private theorem covers : checks tiles 117 21 27 = true :=
  checks_join (index21) index46

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 117) (hj : a.j ≤ 47) : Covered 9 .two6c a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

namespace Top8
private def batch0 : PaidBatch .two6c 8 := ⟨[
  .rectangle 8 24 117 31 105,
  .rectangle 11 32 116 39 105,
  .rectangle 14 40 99 47 105,
  .rectangle 100 40 117 45 115,
  .rectangle 100 46 117 47 115,
  .rectangle 117 32 117 38 105], by decide +kernel⟩
private def batch1 : PaidBatch .two6c 8 := ⟨[
  .rectangle 117 39 117 44 114], by decide +kernel⟩

private def batches : List (PaidBatch .two6c 8) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 117 24 24 = true := by decide +kernel
private theorem covers : checks tiles 117 24 24 = true :=
  index24

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 117) (hj : a.j ≤ 47) : Covered 10 .two6c a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

namespace Top9
private def batch0 : PaidBatch .two6c 9 := ⟨[
  .rectangle 9 27 117 34 105,
  .rectangle 12 35 109 42 105,
  .rectangle 15 43 107 47 105,
  .rectangle 108 43 117 47 115,
  .rectangle 110 35 117 42 114], by decide +kernel⟩

private def batches : List (PaidBatch .two6c 9) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 117 27 21 = true := by decide +kernel
private theorem covers : checks tiles 117 27 21 = true :=
  index27

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 117) (hj : a.j ≤ 47) : Covered 11 .two6c a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

namespace Top10
private def batch0 : PaidBatch .two6c 10 := ⟨[
  .rectangle 10 30 117 37 105,
  .rectangle 13 38 103 45 105,
  .rectangle 16 46 115 47 105,
  .rectangle 104 38 117 44 114,
  .rectangle 104 45 117 47 115], by decide +kernel⟩

private def batches : List (PaidBatch .two6c 10) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 117 30 18 = true := by decide +kernel
private theorem covers : checks tiles 117 30 18 = true :=
  index30

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 117) (hj : a.j ≤ 47) : Covered 12 .two6c a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

namespace Top11
private def batch0 : PaidBatch .two6c 11 := ⟨[
  .rectangle 11 33 115 40 105,
  .rectangle 14 41 102 47 105,
  .rectangle 103 41 117 46 115,
  .rectangle 103 47 117 47 115,
  .rectangle 116 33 117 40 114], by decide +kernel⟩

private def batches : List (PaidBatch .two6c 11) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 117 33 15 = true := by decide +kernel
private theorem covers : checks tiles 117 33 15 = true :=
  index33

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 117) (hj : a.j ≤ 47) : Covered 13 .two6c a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .two6c).plus a) (fullCap top)) : Covered top .two6c a := by
  change 12+a.b ≤ 129 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have ht0 := ha.1
  have hb' : a.b ≤ 117 := by omega
  have hj' : a.j ≤ 47 := by omega
  have casesTop : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 := by omega
  rcases casesTop with ht1 | ht2 | ht3 | ht4 | ht5 | ht6 | ht7 | ht8 | ht9 | ht10 | ht11
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
end Compact50PriceTableTwo6c
