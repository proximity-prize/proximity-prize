import ProximityPrize.SubmissionLower.Compact50Cover
import ProximityPrize.SubmissionLower.Compact50PriceTableOne7 -- serialize candidate build

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6a
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top1
private def batch0 : PaidBatch .two6a 1 := ⟨[
  .rectangle 1 3 125 8 26,
  .rectangle 3 9 127 16 51,
  .rectangle 6 17 127 24 66,
  .rectangle 9 25 127 32 74,
  .rectangle 11 33 127 40 74,
  .rectangle 14 41 127 47 74], by decide +kernel⟩
private def batch1 : PaidBatch .two6a 1 := ⟨[
  .rectangle 126 3 127 7 26,
  .rectangle 126 8 127 15 51], by decide +kernel⟩

private def batches : List (PaidBatch .two6a 1) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 127 3 25 = true := by decide +kernel
private theorem index28 : checks tiles 127 28 20 = true := by decide +kernel
private theorem covers : checks tiles 127 3 45 = true :=
  checks_join (index3) index28

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 127) (hj : a.j ≤ 47) : Covered 3 .two6a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2
private def batch0 : PaidBatch .two6a 2 := ⟨[
  .rectangle 2 6 127 13 51,
  .rectangle 5 14 127 21 66,
  .rectangle 8 22 127 29 74,
  .rectangle 10 30 127 37 74,
  .rectangle 13 38 127 45 74,
  .rectangle 16 46 127 47 74], by decide +kernel⟩

private def batches : List (PaidBatch .two6a 2) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 127 6 25 = true := by decide +kernel
private theorem index31 : checks tiles 127 31 17 = true := by decide +kernel
private theorem covers : checks tiles 127 6 42 = true :=
  checks_join (index6) index31

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 127) (hj : a.j ≤ 47) : Covered 4 .two6a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3
private def batch0 : PaidBatch .two6a 3 := ⟨[
  .rectangle 3 9 127 16 51,
  .rectangle 6 17 127 24 66,
  .rectangle 9 25 127 32 74,
  .rectangle 11 33 127 40 74,
  .rectangle 14 41 127 47 74], by decide +kernel⟩

private def batches : List (PaidBatch .two6a 3) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 127 9 25 = true := by decide +kernel
private theorem index34 : checks tiles 127 34 14 = true := by decide +kernel
private theorem covers : checks tiles 127 9 39 = true :=
  checks_join (index9) index34

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 127) (hj : a.j ≤ 47) : Covered 5 .two6a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

namespace Top4
private def batch0 : PaidBatch .two6a 4 := ⟨[
  .rectangle 4 12 127 19 66,
  .rectangle 7 20 127 27 73,
  .rectangle 10 28 127 35 74,
  .rectangle 12 36 127 43 74,
  .rectangle 15 44 127 47 74], by decide +kernel⟩

private def batches : List (PaidBatch .two6a 4) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 127 12 25 = true := by decide +kernel
private theorem index37 : checks tiles 127 37 11 = true := by decide +kernel
private theorem covers : checks tiles 127 12 36 = true :=
  checks_join (index12) index37

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 127) (hj : a.j ≤ 47) : Covered 6 .two6a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

namespace Top5
private def batch0 : PaidBatch .two6a 5 := ⟨[
  .rectangle 5 15 127 22 66,
  .rectangle 8 23 127 30 74,
  .rectangle 11 31 127 38 74,
  .rectangle 13 39 124 46 74,
  .rectangle 16 47 127 47 74,
  .rectangle 125 39 127 46 80], by decide +kernel⟩

private def batches : List (PaidBatch .two6a 5) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 127 15 25 = true := by decide +kernel
private theorem index40 : checks tiles 127 40 8 = true := by decide +kernel
private theorem covers : checks tiles 127 15 33 = true :=
  checks_join (index15) index40

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 127) (hj : a.j ≤ 47) : Covered 7 .two6a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

namespace Top6
private def batch0 : PaidBatch .two6a 6 := ⟨[
  .rectangle 6 18 127 25 73,
  .rectangle 9 26 127 33 74,
  .rectangle 12 34 127 41 74,
  .rectangle 14 42 127 47 74], by decide +kernel⟩

private def batches : List (PaidBatch .two6a 6) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 127 18 25 = true := by decide +kernel
private theorem index43 : checks tiles 127 43 5 = true := by decide +kernel
private theorem covers : checks tiles 127 18 30 = true :=
  checks_join (index18) index43

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 127) (hj : a.j ≤ 47) : Covered 8 .two6a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7
private def batch0 : PaidBatch .two6a 7 := ⟨[
  .rectangle 7 21 127 28 74,
  .rectangle 10 29 127 36 74,
  .rectangle 13 37 126 44 74,
  .rectangle 15 45 127 47 74,
  .rectangle 127 37 127 44 80], by decide +kernel⟩

private def batches : List (PaidBatch .two6a 7) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 127 21 25 = true := by decide +kernel
private theorem index46 : checks tiles 127 46 2 = true := by decide +kernel
private theorem covers : checks tiles 127 21 27 = true :=
  checks_join (index21) index46

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 127) (hj : a.j ≤ 47) : Covered 9 .two6a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

namespace Top8
private def batch0 : PaidBatch .two6a 8 := ⟨[
  .rectangle 8 24 127 31 74,
  .rectangle 11 32 127 39 74,
  .rectangle 14 40 119 47 74,
  .rectangle 120 40 127 47 80], by decide +kernel⟩

private def batches : List (PaidBatch .two6a 8) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 127 24 24 = true := by decide +kernel
private theorem covers : checks tiles 127 24 24 = true :=
  index24

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 127) (hj : a.j ≤ 47) : Covered 10 .two6a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

namespace Top9
private def batch0 : PaidBatch .two6a 9 := ⟨[
  .rectangle 9 27 127 34 74,
  .rectangle 12 35 127 42 74,
  .rectangle 15 43 127 47 74], by decide +kernel⟩

private def batches : List (PaidBatch .two6a 9) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 127 27 21 = true := by decide +kernel
private theorem covers : checks tiles 127 27 21 = true :=
  index27

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 127) (hj : a.j ≤ 47) : Covered 11 .two6a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

namespace Top10
private def batch0 : PaidBatch .two6a 10 := ⟨[
  .rectangle 10 30 127 37 74,
  .rectangle 13 38 123 45 74,
  .rectangle 16 46 127 47 74,
  .rectangle 124 38 127 45 80], by decide +kernel⟩

private def batches : List (PaidBatch .two6a 10) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 127 30 18 = true := by decide +kernel
private theorem covers : checks tiles 127 30 18 = true :=
  index30

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 127) (hj : a.j ≤ 47) : Covered 12 .two6a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

namespace Top11
private def batch0 : PaidBatch .two6a 11 := ⟨[
  .rectangle 11 33 127 40 74,
  .rectangle 14 41 121 47 74,
  .rectangle 122 41 127 47 80], by decide +kernel⟩

private def batches : List (PaidBatch .two6a 11) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 127 33 15 = true := by decide +kernel
private theorem covers : checks tiles 127 33 15 = true :=
  index33

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 127) (hj : a.j ≤ 47) : Covered 13 .two6a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .two6a).plus a) (fullCap top)) : Covered top .two6a a := by
  change 2+a.b ≤ 129 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have ht0 := ha.1
  have hb' : a.b ≤ 127 := by omega
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
end Compact50PriceTableTwo6a
