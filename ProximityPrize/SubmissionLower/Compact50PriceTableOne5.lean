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
  .rectangle 1 3 127 5 6,
  .rectangle 2 6 127 13 35,
  .rectangle 5 14 127 21 47,
  .rectangle 8 22 127 29 62,
  .rectangle 10 30 127 37 65,
  .rectangle 13 38 127 45 65], by decide +kernel⟩
private def batch1 : PaidBatch .one5 1 := ⟨[
  .rectangle 16 46 127 48 69], by decide +kernel⟩

private def batches : List (PaidBatch .one5 1) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 127 3 25 = true := by decide +kernel
private theorem index28 : checks tiles 127 28 21 = true := by decide +kernel
private theorem covers : checks tiles 127 3 46 = true :=
  checks_join (index3) index28

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 127) (hj : a.j ≤ 48) : Covered 2 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2
private def batch0 : PaidBatch .one5 2 := ⟨[
  .rectangle 2 6 127 13 35,
  .rectangle 5 14 127 21 47,
  .rectangle 8 22 127 29 62,
  .rectangle 10 30 127 37 65,
  .rectangle 13 38 127 45 65,
  .rectangle 16 46 127 48 69], by decide +kernel⟩

private def batches : List (PaidBatch .one5 2) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 127 6 25 = true := by decide +kernel
private theorem index31 : checks tiles 127 31 18 = true := by decide +kernel
private theorem covers : checks tiles 127 6 43 = true :=
  checks_join (index6) index31

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 127) (hj : a.j ≤ 48) : Covered 3 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3
private def batch0 : PaidBatch .one5 3 := ⟨[
  .rectangle 3 9 127 16 47,
  .rectangle 6 17 127 24 58,
  .rectangle 9 25 127 32 65,
  .rectangle 11 33 127 40 65,
  .rectangle 14 41 127 48 69], by decide +kernel⟩

private def batches : List (PaidBatch .one5 3) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 127 9 25 = true := by decide +kernel
private theorem index34 : checks tiles 127 34 15 = true := by decide +kernel
private theorem covers : checks tiles 127 9 40 = true :=
  checks_join (index9) index34

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 127) (hj : a.j ≤ 48) : Covered 4 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

namespace Top4
private def batch0 : PaidBatch .one5 4 := ⟨[
  .rectangle 4 12 127 19 47,
  .rectangle 7 20 127 27 62,
  .rectangle 10 28 127 35 65,
  .rectangle 12 36 127 43 65,
  .rectangle 15 44 127 48 69], by decide +kernel⟩

private def batches : List (PaidBatch .one5 4) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 127 12 25 = true := by decide +kernel
private theorem index37 : checks tiles 127 37 12 = true := by decide +kernel
private theorem covers : checks tiles 127 12 37 = true :=
  checks_join (index12) index37

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 127) (hj : a.j ≤ 48) : Covered 5 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

namespace Top5
private def batch0 : PaidBatch .one5 5 := ⟨[
  .rectangle 5 15 127 22 58,
  .rectangle 8 23 127 30 62,
  .rectangle 11 31 127 38 65,
  .rectangle 13 39 127 46 69,
  .rectangle 16 47 127 48 69], by decide +kernel⟩

private def batches : List (PaidBatch .one5 5) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 127 15 25 = true := by decide +kernel
private theorem index40 : checks tiles 127 40 9 = true := by decide +kernel
private theorem covers : checks tiles 127 15 34 = true :=
  checks_join (index15) index40

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 127) (hj : a.j ≤ 48) : Covered 6 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

namespace Top6
private def batch0 : PaidBatch .one5 6 := ⟨[
  .rectangle 6 18 127 25 58,
  .rectangle 9 26 127 33 65,
  .rectangle 12 34 127 41 65,
  .rectangle 14 42 127 48 69], by decide +kernel⟩

private def batches : List (PaidBatch .one5 6) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 127 18 25 = true := by decide +kernel
private theorem index43 : checks tiles 127 43 6 = true := by decide +kernel
private theorem covers : checks tiles 127 18 31 = true :=
  checks_join (index18) index43

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 127) (hj : a.j ≤ 48) : Covered 7 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7
private def batch0 : PaidBatch .one5 7 := ⟨[
  .rectangle 7 21 127 28 62,
  .rectangle 10 29 127 36 65,
  .rectangle 13 37 127 44 65,
  .rectangle 15 45 127 48 69], by decide +kernel⟩

private def batches : List (PaidBatch .one5 7) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 127 21 25 = true := by decide +kernel
private theorem index46 : checks tiles 127 46 3 = true := by decide +kernel
private theorem covers : checks tiles 127 21 28 = true :=
  checks_join (index21) index46

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 127) (hj : a.j ≤ 48) : Covered 8 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

namespace Top8
private def batch0 : PaidBatch .one5 8 := ⟨[
  .rectangle 8 24 127 31 65,
  .rectangle 11 32 127 39 65,
  .rectangle 14 40 127 47 69,
  .rectangle 16 48 127 48 69], by decide +kernel⟩

private def batches : List (PaidBatch .one5 8) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 127 24 25 = true := by decide +kernel
private theorem covers : checks tiles 127 24 25 = true :=
  index24

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 127) (hj : a.j ≤ 48) : Covered 9 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

namespace Top9
private def batch0 : PaidBatch .one5 9 := ⟨[
  .rectangle 9 27 127 34 65,
  .rectangle 12 35 127 42 65,
  .rectangle 15 43 127 48 69], by decide +kernel⟩

private def batches : List (PaidBatch .one5 9) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 127 27 22 = true := by decide +kernel
private theorem covers : checks tiles 127 27 22 = true :=
  index27

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 127) (hj : a.j ≤ 48) : Covered 10 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

namespace Top10
private def batch0 : PaidBatch .one5 10 := ⟨[
  .rectangle 10 30 127 37 65,
  .rectangle 13 38 124 45 65,
  .rectangle 16 46 127 48 69,
  .rectangle 125 38 127 45 70], by decide +kernel⟩

private def batches : List (PaidBatch .one5 10) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 127 30 19 = true := by decide +kernel
private theorem covers : checks tiles 127 30 19 = true :=
  index30

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 127) (hj : a.j ≤ 48) : Covered 11 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

namespace Top11
private def batch0 : PaidBatch .one5 11 := ⟨[
  .rectangle 11 33 127 40 65,
  .rectangle 14 41 124 48 69,
  .rectangle 125 41 127 47 70,
  .rectangle 125 48 127 48 70], by decide +kernel⟩

private def batches : List (PaidBatch .one5 11) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 127 33 16 = true := by decide +kernel
private theorem covers : checks tiles 127 33 16 = true :=
  index33

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 127) (hj : a.j ≤ 48) : Covered 12 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

namespace Top12
private def batch0 : PaidBatch .one5 12 := ⟨[
  .rectangle 12 36 127 43 65,
  .rectangle 15 44 127 48 69], by decide +kernel⟩

private def batches : List (PaidBatch .one5 12) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index36 : checks tiles 127 36 13 = true := by decide +kernel
private theorem covers : checks tiles 127 36 13 = true :=
  index36

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 12)
    (hb : a.b ≤ 127) (hj : a.j ≤ 48) : Covered 13 .one5 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top12

theorem price (top : ℕ) (htop : top ≤ 13) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .one5).plus a) (fullCap top)) : Covered top .one5 a := by
  change 2+a.b ≤ 129 ∧ 5+a.j ≤ 53 ∧ 1+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have ht0 := ha.1
  have hb' : a.b ≤ 127 := by omega
  have hj' : a.j ≤ 48 := by omega
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
end Compact50PriceTableOne5
