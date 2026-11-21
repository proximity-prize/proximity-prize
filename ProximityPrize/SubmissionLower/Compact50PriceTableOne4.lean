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
  .rectangle 1 3 127 3 1,
  .rectangle 2 4 103 6 6,
  .rectangle 3 7 127 12 23,
  .rectangle 5 13 127 20 45,
  .rectangle 7 21 127 28 52,
  .rectangle 10 29 127 36 58], by decide +kernel⟩
private def batch1 : PaidBatch .one4 1 := ⟨[
  .rectangle 13 37 127 44 58,
  .rectangle 15 45 127 49 58,
  .rectangle 104 4 127 5 6,
  .rectangle 104 6 127 11 23], by decide +kernel⟩

private def batches : List (PaidBatch .one4 1) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 127 3 25 = true := by decide +kernel
private theorem index28 : checks tiles 127 28 22 = true := by decide +kernel
private theorem covers : checks tiles 127 3 47 = true :=
  checks_join (index3) index28

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 127) (hj : a.j ≤ 49) : Covered 2 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2
private def batch0 : PaidBatch .one4 2 := ⟨[
  .rectangle 2 6 110 12 23,
  .rectangle 5 13 127 20 45,
  .rectangle 7 21 127 28 52,
  .rectangle 10 29 127 36 58,
  .rectangle 13 37 127 44 58,
  .rectangle 15 45 127 49 58], by decide +kernel⟩
private def batch1 : PaidBatch .one4 2 := ⟨[
  .rectangle 111 6 127 11 23,
  .rectangle 111 12 127 19 45], by decide +kernel⟩

private def batches : List (PaidBatch .one4 2) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 127 6 25 = true := by decide +kernel
private theorem index31 : checks tiles 127 31 19 = true := by decide +kernel
private theorem covers : checks tiles 127 6 44 = true :=
  checks_join (index6) index31

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 127) (hj : a.j ≤ 49) : Covered 3 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3
private def batch0 : PaidBatch .one4 3 := ⟨[
  .rectangle 3 9 127 16 37,
  .rectangle 6 17 127 24 52,
  .rectangle 9 25 127 32 52,
  .rectangle 11 33 127 40 58,
  .rectangle 14 41 118 48 58,
  .rectangle 17 49 127 49 58], by decide +kernel⟩
private def batch1 : PaidBatch .one4 3 := ⟨[
  .rectangle 119 41 127 48 63], by decide +kernel⟩

private def batches : List (PaidBatch .one4 3) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 127 9 25 = true := by decide +kernel
private theorem index34 : checks tiles 127 34 16 = true := by decide +kernel
private theorem covers : checks tiles 127 9 41 = true :=
  checks_join (index9) index34

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 127) (hj : a.j ≤ 49) : Covered 4 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

namespace Top4
private def batch0 : PaidBatch .one4 4 := ⟨[
  .rectangle 4 12 127 19 45,
  .rectangle 7 20 127 27 52,
  .rectangle 10 28 127 35 58,
  .rectangle 12 36 124 43 58,
  .rectangle 15 44 119 49 58,
  .rectangle 120 44 127 49 63], by decide +kernel⟩
private def batch1 : PaidBatch .one4 4 := ⟨[
  .rectangle 125 36 127 43 60], by decide +kernel⟩

private def batches : List (PaidBatch .one4 4) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 127 12 25 = true := by decide +kernel
private theorem index37 : checks tiles 127 37 13 = true := by decide +kernel
private theorem covers : checks tiles 127 12 38 = true :=
  checks_join (index12) index37

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 127) (hj : a.j ≤ 49) : Covered 5 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

namespace Top5
private def batch0 : PaidBatch .one4 5 := ⟨[
  .rectangle 5 15 127 22 49,
  .rectangle 8 23 127 30 52,
  .rectangle 11 31 127 38 58,
  .rectangle 13 39 116 46 58,
  .rectangle 16 47 125 49 58,
  .rectangle 117 39 126 46 63], by decide +kernel⟩
private def batch1 : PaidBatch .one4 5 := ⟨[
  .rectangle 126 47 127 49 63,
  .rectangle 127 39 127 45 63,
  .rectangle 127 46 127 49 63], by decide +kernel⟩

private def batches : List (PaidBatch .one4 5) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 127 15 25 = true := by decide +kernel
private theorem index40 : checks tiles 127 40 10 = true := by decide +kernel
private theorem covers : checks tiles 127 15 35 = true :=
  checks_join (index15) index40

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 127) (hj : a.j ≤ 49) : Covered 6 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

namespace Top6
private def batch0 : PaidBatch .one4 6 := ⟨[
  .rectangle 6 18 127 25 52,
  .rectangle 9 26 127 33 52,
  .rectangle 12 34 126 41 58,
  .rectangle 14 42 110 49 58,
  .rectangle 111 42 127 47 63,
  .rectangle 111 48 127 49 63], by decide +kernel⟩
private def batch1 : PaidBatch .one4 6 := ⟨[
  .rectangle 127 34 127 41 60], by decide +kernel⟩

private def batches : List (PaidBatch .one4 6) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 127 18 25 = true := by decide +kernel
private theorem index43 : checks tiles 127 43 7 = true := by decide +kernel
private theorem covers : checks tiles 127 18 32 = true :=
  checks_join (index18) index43

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 127) (hj : a.j ≤ 49) : Covered 7 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7
private def batch0 : PaidBatch .one4 7 := ⟨[
  .rectangle 7 21 127 28 52,
  .rectangle 10 29 127 36 58,
  .rectangle 13 37 118 44 58,
  .rectangle 15 45 116 49 58,
  .rectangle 117 45 126 49 63,
  .rectangle 119 37 127 43 60], by decide +kernel⟩
private def batch1 : PaidBatch .one4 7 := ⟨[
  .rectangle 119 44 127 48 63,
  .rectangle 127 49 127 49 63], by decide +kernel⟩

private def batches : List (PaidBatch .one4 7) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 127 21 25 = true := by decide +kernel
private theorem index46 : checks tiles 127 46 4 = true := by decide +kernel
private theorem covers : checks tiles 127 21 29 = true :=
  checks_join (index21) index46

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 127) (hj : a.j ≤ 49) : Covered 8 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

namespace Top8
private def batch0 : PaidBatch .one4 8 := ⟨[
  .rectangle 8 24 127 31 52,
  .rectangle 11 32 127 39 58,
  .rectangle 14 40 111 47 58,
  .rectangle 16 48 123 49 58,
  .rectangle 112 40 126 46 63,
  .rectangle 112 47 127 49 63], by decide +kernel⟩
private def batch1 : PaidBatch .one4 8 := ⟨[
  .rectangle 127 40 127 45 63,
  .rectangle 127 46 127 49 63], by decide +kernel⟩

private def batches : List (PaidBatch .one4 8) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 127 24 25 = true := by decide +kernel
private theorem index49 : checks tiles 127 49 1 = true := by decide +kernel
private theorem covers : checks tiles 127 24 26 = true :=
  checks_join (index24) index49

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 127) (hj : a.j ≤ 49) : Covered 9 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

namespace Top9
private def batch0 : PaidBatch .one4 9 := ⟨[
  .rectangle 9 27 127 34 58,
  .rectangle 12 35 122 42 58,
  .rectangle 15 43 109 49 58,
  .rectangle 110 43 127 47 63,
  .rectangle 110 48 127 49 63,
  .rectangle 123 35 127 41 60], by decide +kernel⟩
private def batch1 : PaidBatch .one4 9 := ⟨[
  .rectangle 123 42 127 47 63], by decide +kernel⟩

private def batches : List (PaidBatch .one4 9) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 127 27 23 = true := by decide +kernel
private theorem covers : checks tiles 127 27 23 = true :=
  index27

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 127) (hj : a.j ≤ 49) : Covered 10 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

namespace Top10
private def batch0 : PaidBatch .one4 10 := ⟨[
  .rectangle 10 30 127 37 58,
  .rectangle 13 38 115 45 58,
  .rectangle 16 46 117 49 58,
  .rectangle 116 38 127 44 63,
  .rectangle 116 45 125 49 63,
  .rectangle 126 45 127 48 63], by decide +kernel⟩
private def batch1 : PaidBatch .one4 10 := ⟨[
  .rectangle 126 49 127 49 63], by decide +kernel⟩

private def batches : List (PaidBatch .one4 10) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 127 30 20 = true := by decide +kernel
private theorem covers : checks tiles 127 30 20 = true :=
  index30

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 127) (hj : a.j ≤ 49) : Covered 11 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

namespace Top11
private def batch0 : PaidBatch .one4 11 := ⟨[
  .rectangle 11 33 127 40 58,
  .rectangle 14 41 108 48 58,
  .rectangle 17 49 125 49 58,
  .rectangle 109 41 127 46 63,
  .rectangle 109 47 127 49 63], by decide +kernel⟩

private def batches : List (PaidBatch .one4 11) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 127 33 17 = true := by decide +kernel
private theorem covers : checks tiles 127 33 17 = true :=
  index33

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 127) (hj : a.j ≤ 49) : Covered 12 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

namespace Top12
private def batch0 : PaidBatch .one4 12 := ⟨[
  .rectangle 12 36 120 43 58,
  .rectangle 15 44 111 49 58,
  .rectangle 112 44 127 48 63,
  .rectangle 112 49 127 49 63,
  .rectangle 121 36 127 42 60,
  .rectangle 121 43 127 47 63], by decide +kernel⟩

private def batches : List (PaidBatch .one4 12) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index36 : checks tiles 127 36 14 = true := by decide +kernel
private theorem covers : checks tiles 127 36 14 = true :=
  index36

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 12)
    (hb : a.b ≤ 127) (hj : a.j ≤ 49) : Covered 13 .one4 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top12

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .one4).plus a) (fullCap top)) : Covered top .one4 a := by
  change 2+a.b ≤ 129 ∧ 4+a.j ≤ 53 ∧ 1+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have ht0 := ha.1
  have hb' : a.b ≤ 127 := by omega
  have hj' : a.j ≤ 49 := by omega
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
end Compact50PriceTableOne4
