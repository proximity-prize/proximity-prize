import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered)

namespace Compact50PriceTableTwo1
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top1

private def batch0 : PaidBatch .two 1 := ⟨[
  .rectangle 1 3 30 13 26,
  .rectangle 1 14 30 23 16,
  .rectangle 1 24 60 44 61,
  .rectangle 31 3 60 13 53,
  .rectangle 31 14 60 23 34,
  .rectangle 61 3 75 13 67], by decide +kernel⟩
private def batch1 : PaidBatch .two 1 := ⟨[
  .rectangle 61 14 90 23 53,
  .rectangle 61 24 90 34 64,
  .rectangle 61 35 90 44 70,
  .rectangle 76 3 90 8 28,
  .rectangle 76 9 90 13 26,
  .rectangle 91 3 105 8 32], by decide +kernel⟩
private def batch2 : PaidBatch .two 1 := ⟨[
  .rectangle 91 9 105 13 31,
  .rectangle 91 14 120 23 72,
  .rectangle 91 24 120 34 89,
  .rectangle 91 35 105 44 84,
  .rectangle 106 3 120 8 37,
  .rectangle 106 9 120 13 35], by decide +kernel⟩
private def batch3 : PaidBatch .two 1 := ⟨[
  .rectangle 106 35 120 39 78,
  .rectangle 106 40 120 44 86], by decide +kernel⟩

private def batches : List (PaidBatch .two 1) := [batch0, batch1, batch2, batch3]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 120 3 8 = true := by decide +kernel
private theorem index11 : checks tiles 120 11 8 = true := by decide +kernel
private theorem index19 : checks tiles 120 19 8 = true := by decide +kernel
private theorem index27 : checks tiles 120 27 8 = true := by decide +kernel
private theorem index35 : checks tiles 120 35 8 = true := by decide +kernel
private theorem index43 : checks tiles 120 43 2 = true := by decide +kernel
private theorem covers : checks tiles 120 3 42 = true :=
  (checks_join (checks_join (checks_join (checks_join (checks_join index3 index11) index19) index27) index35) index43)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 120) (hj : a.j ≤ 44) : Covered 3 .two a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2

private def batch0 : PaidBatch .two 2 := ⟨[
  .rectangle 2 6 31 25 49,
  .rectangle 2 26 61 44 63,
  .rectangle 32 6 61 15 36,
  .rectangle 32 16 61 25 37,
  .rectangle 62 6 91 15 54,
  .rectangle 62 16 91 25 56], by decide +kernel⟩
private def batch1 : PaidBatch .two 2 := ⟨[
  .rectangle 62 26 91 35 66,
  .rectangle 62 36 91 44 72,
  .rectangle 92 6 120 15 72,
  .rectangle 92 16 120 25 75,
  .rectangle 92 26 120 35 89,
  .rectangle 92 36 106 44 86], by decide +kernel⟩
private def batch2 : PaidBatch .two 2 := ⟨[
  .rectangle 107 36 120 40 82,
  .rectangle 107 41 120 44 86], by decide +kernel⟩

private def batches : List (PaidBatch .two 2) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 120 6 8 = true := by decide +kernel
private theorem index14 : checks tiles 120 14 8 = true := by decide +kernel
private theorem index22 : checks tiles 120 22 8 = true := by decide +kernel
private theorem index30 : checks tiles 120 30 8 = true := by decide +kernel
private theorem index38 : checks tiles 120 38 7 = true := by decide +kernel
private theorem covers : checks tiles 120 6 39 = true :=
  (checks_join (checks_join (checks_join (checks_join index6 index14) index22) index30) index38)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 120) (hj : a.j ≤ 44) : Covered 4 .two a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3

private def batch0 : PaidBatch .two 3 := ⟨[
  .rectangle 3 9 32 26 39,
  .rectangle 3 27 61 44 65,
  .rectangle 33 9 61 26 75,
  .rectangle 62 9 91 17 47,
  .rectangle 62 18 91 26 55,
  .rectangle 62 27 91 35 65], by decide +kernel⟩
private def batch1 : PaidBatch .two 3 := ⟨[
  .rectangle 62 36 91 44 75,
  .rectangle 92 9 120 17 61,
  .rectangle 92 18 120 26 73,
  .rectangle 92 27 120 35 87,
  .rectangle 92 36 106 44 88,
  .rectangle 107 36 120 40 84], by decide +kernel⟩
private def batch2 : PaidBatch .two 3 := ⟨[
  .rectangle 107 41 120 44 88], by decide +kernel⟩

private def batches : List (PaidBatch .two 3) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 120 9 8 = true := by decide +kernel
private theorem index17 : checks tiles 120 17 8 = true := by decide +kernel
private theorem index25 : checks tiles 120 25 8 = true := by decide +kernel
private theorem index33 : checks tiles 120 33 8 = true := by decide +kernel
private theorem index41 : checks tiles 120 41 4 = true := by decide +kernel
private theorem covers : checks tiles 120 9 36 = true :=
  (checks_join (checks_join (checks_join (checks_join index9 index17) index25) index33) index41)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 120) (hj : a.j ≤ 44) : Covered 5 .two a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

namespace Top4

private def batch0 : PaidBatch .two 4 := ⟨[
  .rectangle 4 12 62 28 67,
  .rectangle 4 29 62 44 64,
  .rectangle 63 12 91 20 49,
  .rectangle 63 21 91 28 55,
  .rectangle 63 29 91 36 65,
  .rectangle 63 37 91 44 74], by decide +kernel⟩
private def batch1 : PaidBatch .two 4 := ⟨[
  .rectangle 92 12 120 20 64,
  .rectangle 92 21 120 28 72,
  .rectangle 92 29 120 36 86,
  .rectangle 92 37 106 44 87,
  .rectangle 107 37 120 40 82,
  .rectangle 107 41 120 44 89], by decide +kernel⟩

private def batches : List (PaidBatch .two 4) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 120 12 8 = true := by decide +kernel
private theorem index20 : checks tiles 120 20 8 = true := by decide +kernel
private theorem index28 : checks tiles 120 28 8 = true := by decide +kernel
private theorem index36 : checks tiles 120 36 8 = true := by decide +kernel
private theorem index44 : checks tiles 120 44 1 = true := by decide +kernel
private theorem covers : checks tiles 120 12 33 = true :=
  (checks_join (checks_join (checks_join (checks_join index12 index20) index28) index36) index44)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 120) (hj : a.j ≤ 44) : Covered 6 .two a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

namespace Top5

private def batch0 : PaidBatch .two 5 := ⟨[
  .rectangle 5 15 62 29 58,
  .rectangle 5 30 62 44 64,
  .rectangle 63 15 91 29 84,
  .rectangle 63 30 77 44 79,
  .rectangle 78 30 91 37 67,
  .rectangle 78 38 91 44 74], by decide +kernel⟩
private def batch1 : PaidBatch .two 5 := ⟨[
  .rectangle 92 15 106 22 55,
  .rectangle 92 23 106 29 63,
  .rectangle 92 30 106 37 78,
  .rectangle 92 38 106 44 86,
  .rectangle 107 15 120 22 62,
  .rectangle 107 23 120 29 71], by decide +kernel⟩
private def batch2 : PaidBatch .two 5 := ⟨[
  .rectangle 107 30 120 37 88,
  .rectangle 107 38 113 41 80,
  .rectangle 107 42 113 44 83,
  .rectangle 114 38 120 41 85,
  .rectangle 114 42 120 44 88], by decide +kernel⟩

private def batches : List (PaidBatch .two 5) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 120 15 8 = true := by decide +kernel
private theorem index23 : checks tiles 120 23 8 = true := by decide +kernel
private theorem index31 : checks tiles 120 31 8 = true := by decide +kernel
private theorem index39 : checks tiles 120 39 6 = true := by decide +kernel
private theorem covers : checks tiles 120 15 30 = true :=
  (checks_join (checks_join (checks_join index15 index23) index31) index39)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 120) (hj : a.j ≤ 44) : Covered 7 .two a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

end Compact50PriceTableTwo1
