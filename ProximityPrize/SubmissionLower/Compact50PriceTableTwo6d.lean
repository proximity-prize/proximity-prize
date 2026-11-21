import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo6d
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top1
private def batch0 : PaidBatch .two6d 1 := ⟨[
  .rectangle 1 3 115 10 99,
  .rectangle 4 11 115 18 121,
  .rectangle 7 19 115 26 127,
  .rectangle 9 27 115 34 127,
  .rectangle 12 35 110 42 127,
  .rectangle 15 43 110 47 127], by decide +kernel⟩
private def batch1 : PaidBatch .two6d 1 := ⟨[
  .rectangle 111 35 115 42 134,
  .rectangle 111 43 115 47 136], by decide +kernel⟩

private def batches : List (PaidBatch .two6d 1) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 115 3 25 = true := by decide +kernel
private theorem index28 : checks tiles 115 28 20 = true := by decide +kernel
private theorem covers : checks tiles 115 3 45 = true :=
  checks_join (index3) index28

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 115) (hj : a.j ≤ 47) : Covered 3 .two6d a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2
private def batch0 : PaidBatch .two6d 2 := ⟨[
  .rectangle 2 6 115 13 99,
  .rectangle 5 14 115 21 127,
  .rectangle 8 22 115 29 127,
  .rectangle 10 30 115 37 127,
  .rectangle 13 38 103 45 127,
  .rectangle 16 46 115 47 127], by decide +kernel⟩
private def batch1 : PaidBatch .two6d 2 := ⟨[
  .rectangle 104 38 115 43 135,
  .rectangle 104 44 115 47 136], by decide +kernel⟩

private def batches : List (PaidBatch .two6d 2) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 115 6 25 = true := by decide +kernel
private theorem index31 : checks tiles 115 31 17 = true := by decide +kernel
private theorem covers : checks tiles 115 6 42 = true :=
  checks_join (index6) index31

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 115) (hj : a.j ≤ 47) : Covered 4 .two6d a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3
private def batch0 : PaidBatch .two6d 3 := ⟨[
  .rectangle 3 9 115 16 121,
  .rectangle 6 17 115 24 127,
  .rectangle 9 25 115 32 127,
  .rectangle 11 33 109 40 127,
  .rectangle 14 41 101 47 127,
  .rectangle 102 41 115 45 135], by decide +kernel⟩
private def batch1 : PaidBatch .two6d 3 := ⟨[
  .rectangle 102 46 115 47 136,
  .rectangle 110 33 115 40 134], by decide +kernel⟩

private def batches : List (PaidBatch .two6d 3) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 115 9 25 = true := by decide +kernel
private theorem index34 : checks tiles 115 34 14 = true := by decide +kernel
private theorem covers : checks tiles 115 9 39 = true :=
  checks_join (index9) index34

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 115) (hj : a.j ≤ 47) : Covered 5 .two6d a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

namespace Top4
private def batch0 : PaidBatch .two6d 4 := ⟨[
  .rectangle 4 12 115 19 121,
  .rectangle 7 20 115 27 127,
  .rectangle 10 28 115 35 127,
  .rectangle 12 36 103 43 127,
  .rectangle 15 44 107 47 127,
  .rectangle 104 36 114 42 135], by decide +kernel⟩
private def batch1 : PaidBatch .two6d 4 := ⟨[
  .rectangle 104 43 115 46 136,
  .rectangle 108 47 115 47 136,
  .rectangle 115 36 115 41 135,
  .rectangle 115 42 115 45 136], by decide +kernel⟩

private def batches : List (PaidBatch .two6d 4) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 115 12 25 = true := by decide +kernel
private theorem index37 : checks tiles 115 37 11 = true := by decide +kernel
private theorem covers : checks tiles 115 12 36 = true :=
  checks_join (index12) index37

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 115) (hj : a.j ≤ 47) : Covered 6 .two6d a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

namespace Top5
private def batch0 : PaidBatch .two6d 5 := ⟨[
  .rectangle 5 15 115 22 127,
  .rectangle 8 23 115 30 127,
  .rectangle 11 31 112 38 127,
  .rectangle 13 39 98 46 127,
  .rectangle 16 47 114 47 127,
  .rectangle 99 39 113 44 135], by decide +kernel⟩
private def batch1 : PaidBatch .two6d 5 := ⟨[
  .rectangle 99 45 115 47 136,
  .rectangle 113 31 115 37 127,
  .rectangle 113 38 115 43 135,
  .rectangle 114 44 115 46 136], by decide +kernel⟩

private def batches : List (PaidBatch .two6d 5) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 115 15 25 = true := by decide +kernel
private theorem index40 : checks tiles 115 40 8 = true := by decide +kernel
private theorem covers : checks tiles 115 15 33 = true :=
  checks_join (index15) index40

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 115) (hj : a.j ≤ 47) : Covered 7 .two6d a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

namespace Top6
private def batch0 : PaidBatch .two6d 6 := ⟨[
  .rectangle 6 18 115 25 127,
  .rectangle 9 26 115 33 127,
  .rectangle 12 34 106 41 127,
  .rectangle 14 42 101 47 127,
  .rectangle 102 42 115 45 136,
  .rectangle 102 46 115 47 136], by decide +kernel⟩
private def batch1 : PaidBatch .two6d 6 := ⟨[
  .rectangle 107 34 115 40 134,
  .rectangle 107 41 114 45 135,
  .rectangle 115 41 115 44 135], by decide +kernel⟩

private def batches : List (PaidBatch .two6d 6) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 115 18 25 = true := by decide +kernel
private theorem index43 : checks tiles 115 43 5 = true := by decide +kernel
private theorem covers : checks tiles 115 18 30 = true :=
  checks_join (index18) index43

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 115) (hj : a.j ≤ 47) : Covered 8 .two6d a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7
private def batch0 : PaidBatch .two6d 7 := ⟨[
  .rectangle 7 21 115 28 127,
  .rectangle 10 29 115 36 127,
  .rectangle 13 37 100 44 127,
  .rectangle 15 45 108 47 127,
  .rectangle 101 37 115 42 135,
  .rectangle 101 43 115 46 136], by decide +kernel⟩
private def batch1 : PaidBatch .two6d 7 := ⟨[
  .rectangle 109 47 115 47 136], by decide +kernel⟩

private def batches : List (PaidBatch .two6d 7) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 115 21 25 = true := by decide +kernel
private theorem index46 : checks tiles 115 46 2 = true := by decide +kernel
private theorem covers : checks tiles 115 21 27 = true :=
  checks_join (index21) index46

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 115) (hj : a.j ≤ 47) : Covered 9 .two6d a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

namespace Top8
private def batch0 : PaidBatch .two6d 8 := ⟨[
  .rectangle 8 24 115 31 127,
  .rectangle 11 32 111 39 127,
  .rectangle 14 40 95 47 127,
  .rectangle 96 40 115 44 135,
  .rectangle 96 45 115 47 136,
  .rectangle 112 32 115 38 127], by decide +kernel⟩
private def batch1 : PaidBatch .two6d 8 := ⟨[
  .rectangle 112 39 115 43 135], by decide +kernel⟩

private def batches : List (PaidBatch .two6d 8) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 115 24 24 = true := by decide +kernel
private theorem covers : checks tiles 115 24 24 = true :=
  index24

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 115) (hj : a.j ≤ 47) : Covered 10 .two6d a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

namespace Top9
private def batch0 : PaidBatch .two6d 9 := ⟨[
  .rectangle 9 27 115 34 127,
  .rectangle 12 35 105 42 127,
  .rectangle 15 43 103 47 127,
  .rectangle 104 43 115 46 136,
  .rectangle 104 47 115 47 136,
  .rectangle 106 35 115 41 134], by decide +kernel⟩
private def batch1 : PaidBatch .two6d 9 := ⟨[
  .rectangle 106 42 115 45 136], by decide +kernel⟩

private def batches : List (PaidBatch .two6d 9) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 115 27 21 = true := by decide +kernel
private theorem covers : checks tiles 115 27 21 = true :=
  index27

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 115) (hj : a.j ≤ 47) : Covered 11 .two6d a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

namespace Top10
private def batch0 : PaidBatch .two6d 10 := ⟨[
  .rectangle 10 30 115 37 127,
  .rectangle 13 38 99 45 127,
  .rectangle 16 46 111 47 127,
  .rectangle 100 38 115 43 135,
  .rectangle 100 44 113 47 135,
  .rectangle 114 44 115 46 136], by decide +kernel⟩
private def batch1 : PaidBatch .two6d 10 := ⟨[
  .rectangle 114 47 115 47 136], by decide +kernel⟩

private def batches : List (PaidBatch .two6d 10) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 115 30 18 = true := by decide +kernel
private theorem covers : checks tiles 115 30 18 = true :=
  index30

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 115) (hj : a.j ≤ 47) : Covered 12 .two6d a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

namespace Top11
private def batch0 : PaidBatch .two6d 11 := ⟨[
  .rectangle 11 33 112 40 127,
  .rectangle 14 41 99 47 127,
  .rectangle 100 41 115 45 135,
  .rectangle 100 46 115 47 136,
  .rectangle 113 33 115 40 134], by decide +kernel⟩

private def batches : List (PaidBatch .two6d 11) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 115 33 15 = true := by decide +kernel
private theorem covers : checks tiles 115 33 15 = true :=
  index33

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 115) (hj : a.j ≤ 47) : Covered 13 .two6d a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .two6d).plus a) (fullCap top)) : Covered top .two6d a := by
  change 14+a.b ≤ 129 ∧ 6+a.j ≤ 53 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have ht0 := ha.1
  have hb' : a.b ≤ 115 := by omega
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
end Compact50PriceTableTwo6d
