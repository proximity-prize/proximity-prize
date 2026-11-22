import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo7a
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top1
private def batch0 : PaidBatch .two7a 1 := ⟨[
  .rectangle 1 3 118 10 63,
  .rectangle 4 11 126 18 91,
  .rectangle 7 19 126 26 98,
  .rectangle 9 27 126 34 99,
  .rectangle 12 35 126 42 99,
  .rectangle 15 43 126 46 99], by decide +kernel⟩
private def batch1 : PaidBatch .two7a 1 := ⟨[
  .rectangle 119 3 126 9 63,
  .rectangle 119 10 126 17 63], by decide +kernel⟩

private def batches : List (PaidBatch .two7a 1) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 126 3 25 = true := by decide +kernel
private theorem index28 : checks tiles 126 28 19 = true := by decide +kernel
private theorem covers : checks tiles 126 3 44 = true :=
  checks_join (index3) index28

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 3 .two7a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2
private def batch0 : PaidBatch .two7a 2 := ⟨[
  .rectangle 2 6 126 13 63,
  .rectangle 5 14 126 21 92,
  .rectangle 8 22 126 29 98,
  .rectangle 10 30 126 37 99,
  .rectangle 13 38 119 45 99,
  .rectangle 16 46 126 46 99], by decide +kernel⟩
private def batch1 : PaidBatch .two7a 2 := ⟨[
  .rectangle 120 38 126 44 103,
  .rectangle 120 45 126 46 103], by decide +kernel⟩

private def batches : List (PaidBatch .two7a 2) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 126 6 25 = true := by decide +kernel
private theorem index31 : checks tiles 126 31 16 = true := by decide +kernel
private theorem covers : checks tiles 126 6 41 = true :=
  checks_join (index6) index31

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 4 .two7a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3
private def batch0 : PaidBatch .two7a 3 := ⟨[
  .rectangle 3 9 126 16 63,
  .rectangle 6 17 126 24 92,
  .rectangle 9 25 126 32 99,
  .rectangle 11 33 126 40 99,
  .rectangle 14 41 121 46 99,
  .rectangle 122 41 126 46 103], by decide +kernel⟩

private def batches : List (PaidBatch .two7a 3) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 126 9 25 = true := by decide +kernel
private theorem index34 : checks tiles 126 34 13 = true := by decide +kernel
private theorem covers : checks tiles 126 9 38 = true :=
  checks_join (index9) index34

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 5 .two7a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

namespace Top4
private def batch0 : PaidBatch .two7a 4 := ⟨[
  .rectangle 4 12 126 19 92,
  .rectangle 7 20 126 27 98,
  .rectangle 10 28 126 35 99,
  .rectangle 12 36 119 43 99,
  .rectangle 15 44 126 46 99,
  .rectangle 120 36 126 42 103], by decide +kernel⟩
private def batch1 : PaidBatch .two7a 4 := ⟨[
  .rectangle 120 43 126 46 103], by decide +kernel⟩

private def batches : List (PaidBatch .two7a 4) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 126 12 25 = true := by decide +kernel
private theorem index37 : checks tiles 126 37 10 = true := by decide +kernel
private theorem covers : checks tiles 126 12 35 = true :=
  checks_join (index12) index37

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 6 .two7a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

namespace Top5
private def batch0 : PaidBatch .two7a 5 := ⟨[
  .rectangle 5 15 126 22 92,
  .rectangle 8 23 126 30 99,
  .rectangle 11 31 126 38 99,
  .rectangle 13 39 112 46 99,
  .rectangle 113 39 126 44 103,
  .rectangle 113 45 126 46 103], by decide +kernel⟩

private def batches : List (PaidBatch .two7a 5) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 126 15 25 = true := by decide +kernel
private theorem index40 : checks tiles 126 40 7 = true := by decide +kernel
private theorem covers : checks tiles 126 15 32 = true :=
  checks_join (index15) index40

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 7 .two7a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

namespace Top6
private def batch0 : PaidBatch .two7a 6 := ⟨[
  .rectangle 6 18 126 25 92,
  .rectangle 9 26 126 33 99,
  .rectangle 12 34 122 41 99,
  .rectangle 14 42 120 46 99,
  .rectangle 121 42 125 46 103,
  .rectangle 123 34 126 40 102], by decide +kernel⟩
private def batch1 : PaidBatch .two7a 6 := ⟨[
  .rectangle 123 41 126 45 103,
  .rectangle 126 46 126 46 103], by decide +kernel⟩

private def batches : List (PaidBatch .two7a 6) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 126 18 25 = true := by decide +kernel
private theorem index43 : checks tiles 126 43 4 = true := by decide +kernel
private theorem covers : checks tiles 126 18 29 = true :=
  checks_join (index18) index43

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 8 .two7a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7
private def batch0 : PaidBatch .two7a 7 := ⟨[
  .rectangle 7 21 126 28 98,
  .rectangle 10 29 126 36 99,
  .rectangle 13 37 115 44 99,
  .rectangle 15 45 126 46 99,
  .rectangle 116 37 125 43 103,
  .rectangle 116 44 126 46 103], by decide +kernel⟩
private def batch1 : PaidBatch .two7a 7 := ⟨[
  .rectangle 126 37 126 42 103,
  .rectangle 126 43 126 46 103], by decide +kernel⟩

private def batches : List (PaidBatch .two7a 7) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 126 21 25 = true := by decide +kernel
private theorem index46 : checks tiles 126 46 1 = true := by decide +kernel
private theorem covers : checks tiles 126 21 26 = true :=
  checks_join (index21) index46

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 9 .two7a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

namespace Top8
private def batch0 : PaidBatch .two7a 8 := ⟨[
  .rectangle 8 24 126 31 99,
  .rectangle 11 32 126 39 99,
  .rectangle 14 40 113 46 99,
  .rectangle 114 40 124 45 103,
  .rectangle 114 46 126 46 103,
  .rectangle 125 40 126 44 103], by decide +kernel⟩
private def batch1 : PaidBatch .two7a 8 := ⟨[
  .rectangle 125 45 126 46 103], by decide +kernel⟩

private def batches : List (PaidBatch .two7a 8) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 126 24 23 = true := by decide +kernel
private theorem covers : checks tiles 126 24 23 = true :=
  index24

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 10 .two7a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

namespace Top9
private def batch0 : PaidBatch .two7a 9 := ⟨[
  .rectangle 9 27 126 34 99,
  .rectangle 12 35 120 42 99,
  .rectangle 15 43 123 46 99,
  .rectangle 121 35 126 41 103,
  .rectangle 121 42 126 45 103,
  .rectangle 124 46 126 46 103], by decide +kernel⟩

private def batches : List (PaidBatch .two7a 9) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 126 27 20 = true := by decide +kernel
private theorem covers : checks tiles 126 27 20 = true :=
  index27

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 11 .two7a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

namespace Top10
private def batch0 : PaidBatch .two7a 10 := ⟨[
  .rectangle 10 30 126 37 99,
  .rectangle 13 38 113 45 99,
  .rectangle 16 46 126 46 99,
  .rectangle 114 38 126 43 103,
  .rectangle 114 44 126 46 103], by decide +kernel⟩

private def batches : List (PaidBatch .two7a 10) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 126 30 17 = true := by decide +kernel
private theorem covers : checks tiles 126 30 17 = true :=
  index30

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 12 .two7a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

namespace Top11
private def batch0 : PaidBatch .two7a 11 := ⟨[
  .rectangle 11 33 126 40 99,
  .rectangle 14 41 117 46 99,
  .rectangle 118 41 126 45 103,
  .rectangle 118 46 126 46 103], by decide +kernel⟩

private def batches : List (PaidBatch .two7a 11) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 126 33 14 = true := by decide +kernel
private theorem covers : checks tiles 126 33 14 = true :=
  index33

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 126) (hj : a.j ≤ 46) : Covered 13 .two7a a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .two7a).plus a) (fullCap top)) : Covered top .two7a a := by
  change 3+a.b ≤ 129 ∧ 7+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have ht0 := ha.1
  have hb' : a.b ≤ 126 := by omega
  have hj' : a.j ≤ 46 := by omega
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
end Compact50PriceTableTwo7a
