import ProximityPrize.SubmissionLower.Compact50Cover
import ProximityPrize.SubmissionLower.Compact50PriceTableEmpty -- serialize candidate build

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
  .rectangle 1 3 128 3 1,
  .rectangle 2 4 68 4 1,
  .rectangle 2 5 88 6 4,
  .rectangle 3 7 84 11 12,
  .rectangle 4 12 109 19 28,
  .rectangle 7 20 128 27 47], by decide +kernel⟩
private def batch1 : PaidBatch .one3 1 := ⟨[
  .rectangle 10 28 128 35 50,
  .rectangle 12 36 120 43 50,
  .rectangle 15 44 113 50 50,
  .rectangle 69 4 128 11 42,
  .rectangle 110 12 128 19 43,
  .rectangle 114 44 128 49 56], by decide +kernel⟩
private def batch2 : PaidBatch .one3 1 := ⟨[
  .rectangle 114 50 128 50 58,
  .rectangle 121 36 128 43 56], by decide +kernel⟩

private def batches : List (PaidBatch .one3 1) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 128 3 25 = true := by decide +kernel
private theorem index28 : checks tiles 128 28 23 = true := by decide +kernel
private theorem covers : checks tiles 128 3 48 = true :=
  checks_join (index3) index28

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 128) (hj : a.j ≤ 50) : Covered 2 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2
private def batch0 : PaidBatch .one3 2 := ⟨[
  .rectangle 2 6 110 9 12,
  .rectangle 4 10 111 17 28,
  .rectangle 6 18 128 25 42,
  .rectangle 9 26 128 33 50,
  .rectangle 12 34 120 41 50,
  .rectangle 14 42 108 49 50], by decide +kernel⟩
private def batch1 : PaidBatch .one3 2 := ⟨[
  .rectangle 17 50 122 50 50,
  .rectangle 109 42 128 47 56,
  .rectangle 109 48 128 50 58,
  .rectangle 111 6 128 13 43,
  .rectangle 112 14 128 21 43,
  .rectangle 121 34 128 41 56], by decide +kernel⟩

private def batches : List (PaidBatch .one3 2) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 128 6 25 = true := by decide +kernel
private theorem index31 : checks tiles 128 31 20 = true := by decide +kernel
private theorem covers : checks tiles 128 6 45 = true :=
  checks_join (index6) index31

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 128) (hj : a.j ≤ 50) : Covered 3 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3
private def batch0 : PaidBatch .one3 3 := ⟨[
  .rectangle 3 9 113 16 28,
  .rectangle 6 17 128 24 42,
  .rectangle 9 25 128 32 50,
  .rectangle 11 33 119 40 50,
  .rectangle 14 41 106 48 50,
  .rectangle 17 49 116 50 50], by decide +kernel⟩
private def batch1 : PaidBatch .one3 3 := ⟨[
  .rectangle 107 41 126 46 56,
  .rectangle 107 47 128 50 58,
  .rectangle 114 9 128 16 43,
  .rectangle 120 33 128 40 55,
  .rectangle 127 41 128 45 56,
  .rectangle 127 46 128 49 58], by decide +kernel⟩

private def batches : List (PaidBatch .one3 3) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 128 9 25 = true := by decide +kernel
private theorem index34 : checks tiles 128 34 17 = true := by decide +kernel
private theorem covers : checks tiles 128 9 42 = true :=
  checks_join (index9) index34

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 128) (hj : a.j ≤ 50) : Covered 4 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

namespace Top4
private def batch0 : PaidBatch .one3 4 := ⟨[
  .rectangle 4 12 105 19 28,
  .rectangle 7 20 128 27 47,
  .rectangle 10 28 128 35 50,
  .rectangle 12 36 111 43 50,
  .rectangle 15 44 102 50 50,
  .rectangle 103 44 123 48 56], by decide +kernel⟩
private def batch1 : PaidBatch .one3 4 := ⟨[
  .rectangle 103 49 128 50 58,
  .rectangle 106 12 128 19 43,
  .rectangle 112 36 128 42 56,
  .rectangle 112 43 125 47 56,
  .rectangle 124 48 128 50 58,
  .rectangle 126 43 128 46 56], by decide +kernel⟩
private def batch2 : PaidBatch .one3 4 := ⟨[
  .rectangle 126 47 128 49 58], by decide +kernel⟩

private def batches : List (PaidBatch .one3 4) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 128 12 25 = true := by decide +kernel
private theorem index37 : checks tiles 128 37 14 = true := by decide +kernel
private theorem covers : checks tiles 128 12 39 = true :=
  checks_join (index12) index37

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 128) (hj : a.j ≤ 50) : Covered 5 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

namespace Top5
private def batch0 : PaidBatch .one3 5 := ⟨[
  .rectangle 5 15 128 22 42,
  .rectangle 8 23 128 30 47,
  .rectangle 11 31 119 38 50,
  .rectangle 13 39 103 46 50,
  .rectangle 16 47 107 50 50,
  .rectangle 104 39 126 44 56], by decide +kernel⟩
private def batch1 : PaidBatch .one3 5 := ⟨[
  .rectangle 104 45 123 48 56,
  .rectangle 108 49 128 50 58,
  .rectangle 120 31 128 38 54,
  .rectangle 124 45 128 47 56,
  .rectangle 124 48 128 49 58,
  .rectangle 127 39 128 43 56], by decide +kernel⟩
private def batch2 : PaidBatch .one3 5 := ⟨[
  .rectangle 127 44 128 46 56], by decide +kernel⟩

private def batches : List (PaidBatch .one3 5) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 128 15 25 = true := by decide +kernel
private theorem index40 : checks tiles 128 40 11 = true := by decide +kernel
private theorem covers : checks tiles 128 15 36 = true :=
  checks_join (index15) index40

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 128) (hj : a.j ≤ 50) : Covered 6 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

namespace Top6
private def batch0 : PaidBatch .one3 6 := ⟨[
  .rectangle 6 18 128 25 42,
  .rectangle 9 26 128 33 50,
  .rectangle 12 34 111 41 50,
  .rectangle 14 42 97 49 50,
  .rectangle 17 50 112 50 50,
  .rectangle 98 42 123 46 56], by decide +kernel⟩
private def batch1 : PaidBatch .one3 6 := ⟨[
  .rectangle 98 47 122 50 58,
  .rectangle 112 34 128 40 56,
  .rectangle 112 41 126 45 56,
  .rectangle 123 47 128 48 58,
  .rectangle 123 49 127 50 58,
  .rectangle 124 46 128 48 58], by decide +kernel⟩
private def batch2 : PaidBatch .one3 6 := ⟨[
  .rectangle 127 41 128 44 56,
  .rectangle 127 45 128 46 56,
  .rectangle 128 49 128 49 58,
  .rectangle 128 50 128 50 58], by decide +kernel⟩

private def batches : List (PaidBatch .one3 6) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 128 18 25 = true := by decide +kernel
private theorem index43 : checks tiles 128 43 8 = true := by decide +kernel
private theorem covers : checks tiles 128 18 33 = true :=
  checks_join (index18) index43

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 128) (hj : a.j ≤ 50) : Covered 7 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7
private def batch0 : PaidBatch .one3 7 := ⟨[
  .rectangle 7 21 128 28 47,
  .rectangle 10 29 123 36 50,
  .rectangle 13 37 104 44 50,
  .rectangle 15 45 99 50 50,
  .rectangle 100 45 120 48 56,
  .rectangle 100 49 125 50 58], by decide +kernel⟩
private def batch1 : PaidBatch .one3 7 := ⟨[
  .rectangle 105 37 128 42 56,
  .rectangle 105 43 125 46 56,
  .rectangle 121 47 128 48 58,
  .rectangle 124 29 128 36 54,
  .rectangle 126 43 128 45 56,
  .rectangle 126 46 128 48 58], by decide +kernel⟩
private def batch2 : PaidBatch .one3 7 := ⟨[
  .rectangle 126 49 128 49 58,
  .rectangle 126 50 128 50 58], by decide +kernel⟩

private def batches : List (PaidBatch .one3 7) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 128 21 25 = true := by decide +kernel
private theorem index46 : checks tiles 128 46 5 = true := by decide +kernel
private theorem covers : checks tiles 128 21 30 = true :=
  checks_join (index21) index46

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 128) (hj : a.j ≤ 50) : Covered 8 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

namespace Top8
private def batch0 : PaidBatch .one3 8 := ⟨[
  .rectangle 8 24 128 31 50,
  .rectangle 11 32 115 39 50,
  .rectangle 14 40 98 47 50,
  .rectangle 16 48 104 50 50,
  .rectangle 99 40 127 44 56,
  .rectangle 99 45 119 48 56], by decide +kernel⟩
private def batch1 : PaidBatch .one3 8 := ⟨[
  .rectangle 105 49 124 50 58,
  .rectangle 116 32 128 38 54,
  .rectangle 116 39 128 43 56,
  .rectangle 120 45 128 46 56,
  .rectangle 120 47 128 48 58,
  .rectangle 125 49 128 49 58], by decide +kernel⟩
private def batch2 : PaidBatch .one3 8 := ⟨[
  .rectangle 125 50 127 50 58,
  .rectangle 128 44 128 45 56,
  .point 128 50 58], by decide +kernel⟩

private def batches : List (PaidBatch .one3 8) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 128 24 25 = true := by decide +kernel
private theorem index49 : checks tiles 128 49 2 = true := by decide +kernel
private theorem covers : checks tiles 128 24 27 = true :=
  checks_join (index24) index49

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 128) (hj : a.j ≤ 50) : Covered 9 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

namespace Top9
private def batch0 : PaidBatch .one3 9 := ⟨[
  .rectangle 9 27 128 34 50,
  .rectangle 12 35 107 42 50,
  .rectangle 15 43 92 50 50,
  .rectangle 93 43 118 47 56,
  .rectangle 93 48 117 50 56,
  .rectangle 108 35 127 41 56], by decide +kernel⟩
private def batch1 : PaidBatch .one3 9 := ⟨[
  .rectangle 108 42 127 45 56,
  .rectangle 118 48 126 49 58,
  .rectangle 118 50 126 50 58,
  .rectangle 119 46 126 48 58,
  .rectangle 127 46 128 47 58,
  .rectangle 127 48 128 48 58], by decide +kernel⟩
private def batch2 : PaidBatch .one3 9 := ⟨[
  .rectangle 127 49 128 49 58,
  .point 127 50 58,
  .rectangle 128 35 128 40 56,
  .rectangle 128 41 128 44 56,
  .rectangle 128 45 128 46 56,
  .point 128 50 58], by decide +kernel⟩

private def batches : List (PaidBatch .one3 9) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 128 27 24 = true := by decide +kernel
private theorem covers : checks tiles 128 27 24 = true :=
  index27

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 128) (hj : a.j ≤ 50) : Covered 10 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

namespace Top10
private def batch0 : PaidBatch .one3 10 := ⟨[
  .rectangle 10 30 121 37 50,
  .rectangle 13 38 101 45 50,
  .rectangle 16 46 98 50 50,
  .rectangle 99 46 120 49 58,
  .rectangle 99 50 126 50 58,
  .rectangle 102 38 126 43 56], by decide +kernel⟩
private def batch1 : PaidBatch .one3 10 := ⟨[
  .rectangle 102 44 121 47 56,
  .rectangle 121 48 126 49 58,
  .rectangle 122 30 128 37 54,
  .rectangle 122 44 127 46 56,
  .rectangle 122 47 128 48 58,
  .rectangle 127 38 128 42 56], by decide +kernel⟩
private def batch2 : PaidBatch .one3 10 := ⟨[
  .rectangle 127 43 128 45 56,
  .rectangle 127 49 128 49 58,
  .point 127 50 58,
  .rectangle 128 46 128 47 58,
  .point 128 50 58], by decide +kernel⟩

private def batches : List (PaidBatch .one3 10) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 128 30 21 = true := by decide +kernel
private theorem covers : checks tiles 128 30 21 = true :=
  index30

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 128) (hj : a.j ≤ 50) : Covered 11 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

namespace Top11
private def batch0 : PaidBatch .one3 11 := ⟨[
  .rectangle 11 33 113 40 50,
  .rectangle 14 41 95 48 50,
  .rectangle 17 49 105 50 50,
  .rectangle 96 41 123 45 56,
  .rectangle 96 46 116 49 56,
  .rectangle 106 50 126 50 58], by decide +kernel⟩
private def batch1 : PaidBatch .one3 11 := ⟨[
  .rectangle 114 33 128 39 55,
  .rectangle 114 40 126 44 56,
  .rectangle 117 46 126 48 58,
  .rectangle 117 49 123 50 58,
  .rectangle 124 45 128 46 56,
  .rectangle 124 49 128 49 58], by decide +kernel⟩
private def batch2 : PaidBatch .one3 11 := ⟨[
  .rectangle 127 40 128 43 56,
  .rectangle 127 44 128 45 56,
  .rectangle 127 47 128 48 58,
  .point 127 50 58,
  .point 128 50 58], by decide +kernel⟩

private def batches : List (PaidBatch .one3 11) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 128 33 18 = true := by decide +kernel
private theorem covers : checks tiles 128 33 18 = true :=
  index33

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 128) (hj : a.j ≤ 50) : Covered 12 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

namespace Top12
private def batch0 : PaidBatch .one3 12 := ⟨[
  .rectangle 12 36 105 43 50,
  .rectangle 15 44 93 50 50,
  .rectangle 94 44 121 47 56,
  .rectangle 94 48 116 50 56,
  .rectangle 106 36 125 42 56,
  .rectangle 106 43 124 46 56], by decide +kernel⟩
private def batch1 : PaidBatch .one3 12 := ⟨[
  .rectangle 117 48 126 49 58,
  .rectangle 117 50 126 50 58,
  .rectangle 122 47 128 48 58,
  .rectangle 125 43 128 45 56,
  .rectangle 125 46 128 47 58,
  .rectangle 126 36 128 41 56], by decide +kernel⟩
private def batch2 : PaidBatch .one3 12 := ⟨[
  .rectangle 126 42 128 44 56,
  .rectangle 127 49 128 49 58,
  .point 127 50 58,
  .point 128 50 58], by decide +kernel⟩

private def batches : List (PaidBatch .one3 12) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index36 : checks tiles 128 36 15 = true := by decide +kernel
private theorem covers : checks tiles 128 36 15 = true :=
  index36

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 12)
    (hb : a.b ≤ 128) (hj : a.j ≤ 50) : Covered 13 .one3 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top12

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .one3).plus a) (fullCap top)) : Covered top .one3 a := by
  change 1+a.b ≤ 129 ∧ 3+a.j ≤ 53 ∧ 1+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have ht0 := ha.1
  have hb' : a.b ≤ 128 := by omega
  have hj' : a.j ≤ 50 := by omega
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
end Compact50PriceTableOne3
