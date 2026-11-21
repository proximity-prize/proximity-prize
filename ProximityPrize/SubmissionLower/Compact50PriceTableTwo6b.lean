import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6b
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top1
private def batch0 : PaidBatch .two6b 1 := ⟨[
  .rectangle 1 3 105 9 42,
  .rectangle 4 10 122 17 64,
  .rectangle 6 18 122 25 85,
  .rectangle 9 26 122 33 86,
  .rectangle 12 34 118 41 86,
  .rectangle 14 42 115 47 86], by decide +kernel⟩
private def batch1 : PaidBatch .two6b 1 := ⟨[
  .rectangle 106 3 122 8 42,
  .rectangle 106 9 122 16 64,
  .rectangle 116 42 122 47 93,
  .rectangle 119 34 122 41 91], by decide +kernel⟩

private def batches : List (PaidBatch .two6b 1) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 122 3 25 = true := by decide +kernel
private theorem index28 : checks tiles 122 28 20 = true := by decide +kernel
private theorem covers : checks tiles 122 3 45 = true :=
  checks_join (index3) index28

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) : Covered 3 .two6b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2
private def batch0 : PaidBatch .two6b 2 := ⟨[
  .rectangle 2 6 122 13 64,
  .rectangle 5 14 122 21 79,
  .rectangle 8 22 122 29 86,
  .rectangle 10 30 122 37 86,
  .rectangle 13 38 109 45 86,
  .rectangle 16 46 121 47 86], by decide +kernel⟩
private def batch1 : PaidBatch .two6b 2 := ⟨[
  .rectangle 110 38 121 44 92,
  .rectangle 110 45 122 47 93,
  .rectangle 122 38 122 43 92,
  .rectangle 122 44 122 47 93], by decide +kernel⟩

private def batches : List (PaidBatch .two6b 2) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 122 6 25 = true := by decide +kernel
private theorem index31 : checks tiles 122 31 17 = true := by decide +kernel
private theorem covers : checks tiles 122 6 42 = true :=
  checks_join (index6) index31

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) : Covered 4 .two6b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3
private def batch0 : PaidBatch .two6b 3 := ⟨[
  .rectangle 3 9 122 16 64,
  .rectangle 6 17 122 24 79,
  .rectangle 9 25 122 32 86,
  .rectangle 11 33 115 40 86,
  .rectangle 14 41 106 47 86,
  .rectangle 107 41 122 45 92], by decide +kernel⟩
private def batch1 : PaidBatch .two6b 3 := ⟨[
  .rectangle 107 46 122 47 93,
  .rectangle 116 33 122 39 91,
  .rectangle 116 40 122 44 92], by decide +kernel⟩

private def batches : List (PaidBatch .two6b 3) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 122 9 25 = true := by decide +kernel
private theorem index34 : checks tiles 122 34 14 = true := by decide +kernel
private theorem covers : checks tiles 122 9 39 = true :=
  checks_join (index9) index34

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) : Covered 5 .two6b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

namespace Top4
private def batch0 : PaidBatch .two6b 4 := ⟨[
  .rectangle 4 12 122 19 79,
  .rectangle 7 20 122 27 85,
  .rectangle 10 28 122 35 86,
  .rectangle 12 36 108 43 86,
  .rectangle 15 44 112 47 86,
  .rectangle 109 36 122 41 92], by decide +kernel⟩
private def batch1 : PaidBatch .two6b 4 := ⟨[
  .rectangle 109 42 122 45 92,
  .rectangle 113 46 122 47 93], by decide +kernel⟩

private def batches : List (PaidBatch .two6b 4) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 122 12 25 = true := by decide +kernel
private theorem index37 : checks tiles 122 37 11 = true := by decide +kernel
private theorem covers : checks tiles 122 12 36 = true :=
  checks_join (index12) index37

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) : Covered 6 .two6b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

namespace Top5
private def batch0 : PaidBatch .two6b 5 := ⟨[
  .rectangle 5 15 122 22 79,
  .rectangle 8 23 122 30 86,
  .rectangle 11 31 117 38 86,
  .rectangle 13 39 102 46 86,
  .rectangle 16 47 118 47 86,
  .rectangle 103 39 122 43 92], by decide +kernel⟩
private def batch1 : PaidBatch .two6b 5 := ⟨[
  .rectangle 103 44 119 47 93,
  .rectangle 118 31 122 38 91,
  .rectangle 120 44 122 46 93,
  .rectangle 120 47 122 47 93], by decide +kernel⟩

private def batches : List (PaidBatch .two6b 5) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 122 15 25 = true := by decide +kernel
private theorem index40 : checks tiles 122 40 8 = true := by decide +kernel
private theorem covers : checks tiles 122 15 33 = true :=
  checks_join (index15) index40

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) : Covered 7 .two6b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

namespace Top6
private def batch0 : PaidBatch .two6b 6 := ⟨[
  .rectangle 6 18 122 25 85,
  .rectangle 9 26 122 33 86,
  .rectangle 12 34 110 41 86,
  .rectangle 14 42 104 47 86,
  .rectangle 105 42 121 45 92,
  .rectangle 105 46 122 47 93], by decide +kernel⟩
private def batch1 : PaidBatch .two6b 6 := ⟨[
  .rectangle 111 34 122 40 91,
  .rectangle 111 41 122 44 92,
  .rectangle 122 45 122 46 93], by decide +kernel⟩

private def batches : List (PaidBatch .two6b 6) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 122 18 25 = true := by decide +kernel
private theorem index43 : checks tiles 122 43 5 = true := by decide +kernel
private theorem covers : checks tiles 122 18 30 = true :=
  checks_join (index18) index43

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) : Covered 8 .two6b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7
private def batch0 : PaidBatch .two6b 7 := ⟨[
  .rectangle 7 21 122 28 86,
  .rectangle 10 29 121 36 86,
  .rectangle 13 37 103 44 86,
  .rectangle 15 45 111 47 86,
  .rectangle 104 37 122 42 92,
  .rectangle 104 43 119 46 93], by decide +kernel⟩
private def batch1 : PaidBatch .two6b 7 := ⟨[
  .rectangle 112 47 122 47 93,
  .rectangle 120 43 122 45 93,
  .rectangle 120 46 122 47 93,
  .rectangle 122 29 122 36 87], by decide +kernel⟩

private def batches : List (PaidBatch .two6b 7) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 122 21 25 = true := by decide +kernel
private theorem index46 : checks tiles 122 46 2 = true := by decide +kernel
private theorem covers : checks tiles 122 21 27 = true :=
  checks_join (index21) index46

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) : Covered 9 .two6b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

namespace Top8
private def batch0 : PaidBatch .two6b 8 := ⟨[
  .rectangle 8 24 122 31 86,
  .rectangle 11 32 114 39 86,
  .rectangle 14 40 97 47 86,
  .rectangle 98 40 120 44 92,
  .rectangle 98 45 120 47 93,
  .rectangle 115 32 122 38 91], by decide +kernel⟩
private def batch1 : PaidBatch .two6b 8 := ⟨[
  .rectangle 115 39 122 43 92,
  .rectangle 121 44 122 46 93,
  .rectangle 121 47 122 47 93], by decide +kernel⟩

private def batches : List (PaidBatch .two6b 8) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 122 24 24 = true := by decide +kernel
private theorem covers : checks tiles 122 24 24 = true :=
  index24

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) : Covered 10 .two6b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

namespace Top9
private def batch0 : PaidBatch .two6b 9 := ⟨[
  .rectangle 9 27 122 34 86,
  .rectangle 12 35 107 42 86,
  .rectangle 15 43 105 47 86,
  .rectangle 106 43 119 46 93,
  .rectangle 106 47 122 47 93,
  .rectangle 108 35 121 41 92], by decide +kernel⟩
private def batch1 : PaidBatch .two6b 9 := ⟨[
  .rectangle 108 42 120 45 92,
  .rectangle 120 46 122 47 93,
  .rectangle 121 42 122 45 93,
  .rectangle 122 35 122 40 92,
  .rectangle 122 41 122 44 92], by decide +kernel⟩

private def batches : List (PaidBatch .two6b 9) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 122 27 21 = true := by decide +kernel
private theorem covers : checks tiles 122 27 21 = true :=
  index27

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) : Covered 11 .two6b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

namespace Top10
private def batch0 : PaidBatch .two6b 10 := ⟨[
  .rectangle 10 30 120 37 86,
  .rectangle 13 38 101 45 86,
  .rectangle 16 46 113 47 86,
  .rectangle 102 38 120 43 92,
  .rectangle 102 44 117 47 93,
  .rectangle 118 44 122 46 93], by decide +kernel⟩
private def batch1 : PaidBatch .two6b 10 := ⟨[
  .rectangle 118 47 122 47 93,
  .rectangle 121 30 122 37 91,
  .rectangle 121 38 122 42 92,
  .rectangle 121 43 122 45 93], by decide +kernel⟩

private def batches : List (PaidBatch .two6b 10) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 122 30 18 = true := by decide +kernel
private theorem covers : checks tiles 122 30 18 = true :=
  index30

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) : Covered 12 .two6b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

namespace Top11
private def batch0 : PaidBatch .two6b 11 := ⟨[
  .rectangle 11 33 113 40 86,
  .rectangle 14 41 100 47 86,
  .rectangle 101 41 118 45 92,
  .rectangle 101 46 122 47 93,
  .rectangle 114 33 122 39 91,
  .rectangle 114 40 121 44 92], by decide +kernel⟩
private def batch1 : PaidBatch .two6b 11 := ⟨[
  .rectangle 119 45 122 46 93,
  .rectangle 122 40 122 43 92,
  .rectangle 122 44 122 46 93], by decide +kernel⟩

private def batches : List (PaidBatch .two6b 11) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 122 33 15 = true := by decide +kernel
private theorem covers : checks tiles 122 33 15 = true :=
  index33

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 122) (hj : a.j ≤ 47) : Covered 13 .two6b a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .two6b).plus a) (fullCap top)) : Covered top .two6b a := by
  change 7+a.b ≤ 129 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have ht0 := ha.1
  have hb' : a.b ≤ 122 := by omega
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
end Compact50PriceTableTwo6b
