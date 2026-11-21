import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered)

namespace Compact50PriceTableEmpty1
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top1

private def batch0 : PaidBatch .empty 1 := ⟨[
  .rectangle 1 3 8 5 1,
  .rectangle 1 6 8 8 1,
  .rectangle 1 9 16 14 3,
  .rectangle 1 15 31 26 10,
  .rectangle 1 27 61 50 35,
  .rectangle 9 3 16 5 1], by decide +kernel⟩
private def batch1 : PaidBatch .empty 1 := ⟨[
  .rectangle 9 6 12 8 1,
  .rectangle 13 6 16 7 1,
  .rectangle 13 8 16 8 1,
  .rectangle 17 3 24 5 1,
  .rectangle 17 6 24 8 2,
  .rectangle 17 9 31 14 6], by decide +kernel⟩
private def batch2 : PaidBatch .empty 1 := ⟨[
  .rectangle 25 3 31 5 2,
  .rectangle 25 6 31 8 3,
  .rectangle 32 3 46 8 7,
  .rectangle 32 9 46 14 8,
  .rectangle 32 15 61 26 21,
  .rectangle 47 3 61 8 10], by decide +kernel⟩
private def batch3 : PaidBatch .empty 1 := ⟨[
  .rectangle 47 9 61 14 11,
  .rectangle 62 3 77 8 12,
  .rectangle 62 9 77 14 14,
  .rectangle 62 15 92 26 33,
  .rectangle 62 27 92 38 37,
  .rectangle 62 39 92 50 41], by decide +kernel⟩
private def batch4 : PaidBatch .empty 1 := ⟨[
  .rectangle 78 3 92 8 15,
  .rectangle 78 9 92 14 16,
  .rectangle 93 3 107 8 17,
  .rectangle 93 9 107 14 19,
  .rectangle 93 15 122 26 44,
  .rectangle 93 27 107 38 44], by decide +kernel⟩
private def batch5 : PaidBatch .empty 1 := ⟨[
  .rectangle 93 39 107 44 40,
  .rectangle 93 45 107 50 43,
  .rectangle 108 3 122 8 19,
  .rectangle 108 9 122 14 21,
  .rectangle 108 27 122 32 37,
  .rectangle 108 33 122 38 41], by decide +kernel⟩
private def batch6 : PaidBatch .empty 1 := ⟨[
  .rectangle 108 39 122 44 46,
  .rectangle 108 45 122 50 50], by decide +kernel⟩

private def batches : List (PaidBatch .empty 1) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 122 3 8 = true := by decide +kernel
private theorem index11 : checks tiles 122 11 8 = true := by decide +kernel
private theorem index19 : checks tiles 122 19 8 = true := by decide +kernel
private theorem index27 : checks tiles 122 27 8 = true := by decide +kernel
private theorem index35 : checks tiles 122 35 8 = true := by decide +kernel
private theorem index43 : checks tiles 122 43 8 = true := by decide +kernel
private theorem covers : checks tiles 122 3 48 = true :=
  (checks_join (checks_join (checks_join (checks_join (checks_join index3 index11) index19) index27) index35) index43)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 122) (hj : a.j ≤ 50) : Covered 1 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2

private def batch0 : PaidBatch .empty 2 := ⟨[
  .rectangle 2 6 9 8 1,
  .rectangle 2 9 9 11 2,
  .rectangle 2 12 17 17 4,
  .rectangle 2 18 32 28 11,
  .rectangle 2 29 62 50 37,
  .rectangle 10 6 13 7 1], by decide +kernel⟩
private def batch1 : PaidBatch .empty 2 := ⟨[
  .rectangle 10 8 13 8 1,
  .rectangle 10 9 17 11 2,
  .rectangle 14 6 17 8 2,
  .rectangle 18 6 32 11 6,
  .rectangle 18 12 32 17 7,
  .rectangle 33 6 47 17 19], by decide +kernel⟩
private def batch2 : PaidBatch .empty 2 := ⟨[
  .rectangle 33 18 62 28 22,
  .rectangle 48 6 62 17 25,
  .rectangle 63 6 77 17 31,
  .rectangle 63 18 92 28 33,
  .rectangle 63 29 92 39 38,
  .rectangle 63 40 92 50 43], by decide +kernel⟩
private def batch3 : PaidBatch .empty 2 := ⟨[
  .rectangle 78 6 92 17 37,
  .rectangle 93 6 107 11 17,
  .rectangle 93 12 107 17 21,
  .rectangle 93 18 122 28 44,
  .rectangle 93 29 107 39 44,
  .rectangle 93 40 107 45 42], by decide +kernel⟩
private def batch4 : PaidBatch .empty 2 := ⟨[
  .rectangle 93 46 107 50 44,
  .rectangle 108 6 122 11 20,
  .rectangle 108 12 122 17 24,
  .rectangle 108 29 122 34 39,
  .rectangle 108 35 122 39 42,
  .rectangle 108 40 122 45 48], by decide +kernel⟩
private def batch5 : PaidBatch .empty 2 := ⟨[
  .rectangle 108 46 122 50 51], by decide +kernel⟩

private def batches : List (PaidBatch .empty 2) := [batch0, batch1, batch2, batch3, batch4, batch5]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 122 6 8 = true := by decide +kernel
private theorem index14 : checks tiles 122 14 8 = true := by decide +kernel
private theorem index22 : checks tiles 122 22 8 = true := by decide +kernel
private theorem index30 : checks tiles 122 30 8 = true := by decide +kernel
private theorem index38 : checks tiles 122 38 8 = true := by decide +kernel
private theorem index46 : checks tiles 122 46 5 = true := by decide +kernel
private theorem covers : checks tiles 122 6 45 = true :=
  (checks_join (checks_join (checks_join (checks_join (checks_join index6 index14) index22) index30) index38) index46)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 122) (hj : a.j ≤ 50) : Covered 2 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3

private def batch0 : PaidBatch .empty 3 := ⟨[
  .rectangle 3 9 32 19 11,
  .rectangle 3 20 32 29 11,
  .rectangle 3 30 62 50 38,
  .rectangle 33 9 62 19 21,
  .rectangle 33 20 62 29 22,
  .rectangle 63 9 92 19 31], by decide +kernel⟩
private def batch1 : PaidBatch .empty 3 := ⟨[
  .rectangle 63 20 92 29 32,
  .rectangle 63 30 92 40 40,
  .rectangle 63 41 92 50 43,
  .rectangle 93 9 122 19 41,
  .rectangle 93 20 122 29 43,
  .rectangle 93 30 107 40 46], by decide +kernel⟩
private def batch2 : PaidBatch .empty 3 := ⟨[
  .rectangle 93 41 107 45 42,
  .rectangle 93 46 107 50 46,
  .rectangle 108 30 122 35 41,
  .rectangle 108 36 122 40 44,
  .rectangle 108 41 122 45 49,
  .rectangle 108 46 115 50 49], by decide +kernel⟩
private def batch3 : PaidBatch .empty 3 := ⟨[
  .rectangle 116 46 122 48 49,
  .rectangle 116 49 122 50 49], by decide +kernel⟩

private def batches : List (PaidBatch .empty 3) := [batch0, batch1, batch2, batch3]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 122 9 8 = true := by decide +kernel
private theorem index17 : checks tiles 122 17 8 = true := by decide +kernel
private theorem index25 : checks tiles 122 25 8 = true := by decide +kernel
private theorem index33 : checks tiles 122 33 8 = true := by decide +kernel
private theorem index41 : checks tiles 122 41 8 = true := by decide +kernel
private theorem index49 : checks tiles 122 49 2 = true := by decide +kernel
private theorem covers : checks tiles 122 9 42 = true :=
  (checks_join (checks_join (checks_join (checks_join (checks_join index9 index17) index25) index33) index41) index49)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 122) (hj : a.j ≤ 50) : Covered 3 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

namespace Top4

private def batch0 : PaidBatch .empty 4 := ⟨[
  .rectangle 4 12 33 31 23,
  .rectangle 4 32 63 50 39,
  .rectangle 34 12 63 21 20,
  .rectangle 34 22 63 31 24,
  .rectangle 64 12 93 21 29,
  .rectangle 64 22 93 31 34], by decide +kernel⟩
private def batch1 : PaidBatch .empty 4 := ⟨[
  .rectangle 64 32 93 41 41,
  .rectangle 64 42 93 50 45,
  .rectangle 94 12 122 21 38,
  .rectangle 94 22 122 31 45,
  .rectangle 94 32 108 41 47,
  .rectangle 94 42 108 46 45], by decide +kernel⟩
private def batch2 : PaidBatch .empty 4 := ⟨[
  .rectangle 94 47 108 50 47,
  .rectangle 109 32 122 36 41,
  .rectangle 109 37 122 41 46,
  .rectangle 109 42 115 46 48,
  .rectangle 109 47 115 50 50,
  .rectangle 116 42 122 44 46], by decide +kernel⟩
private def batch3 : PaidBatch .empty 4 := ⟨[
  .rectangle 116 45 122 46 47,
  .rectangle 116 47 119 50 51,
  .rectangle 120 47 122 48 49,
  .rectangle 120 49 122 50 51], by decide +kernel⟩

private def batches : List (PaidBatch .empty 4) := [batch0, batch1, batch2, batch3]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 122 12 8 = true := by decide +kernel
private theorem index20 : checks tiles 122 20 8 = true := by decide +kernel
private theorem index28 : checks tiles 122 28 8 = true := by decide +kernel
private theorem index36 : checks tiles 122 36 8 = true := by decide +kernel
private theorem index44 : checks tiles 122 44 7 = true := by decide +kernel
private theorem covers : checks tiles 122 12 39 = true :=
  (checks_join (checks_join (checks_join (checks_join index12 index20) index28) index36) index44)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 122) (hj : a.j ≤ 50) : Covered 4 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

end Compact50PriceTableEmpty1
