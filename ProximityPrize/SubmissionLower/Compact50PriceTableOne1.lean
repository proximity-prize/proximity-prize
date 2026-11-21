import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered)

namespace Compact50PriceTableOne1
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top1

private def batch0 : PaidBatch .one 1 := ⟨[
  .rectangle 1 3 8 5 1,
  .rectangle 1 6 8 8 1,
  .rectangle 1 9 16 14 3,
  .rectangle 1 15 31 25 10,
  .rectangle 1 26 61 47 36,
  .rectangle 9 3 16 5 1], by decide +kernel⟩
private def batch1 : PaidBatch .one 1 := ⟨[
  .rectangle 9 6 16 8 2,
  .rectangle 17 3 31 8 6,
  .rectangle 17 9 31 14 6,
  .rectangle 32 3 46 14 26,
  .rectangle 32 15 61 25 22,
  .rectangle 47 3 61 14 35], by decide +kernel⟩
private def batch2 : PaidBatch .one 1 := ⟨[
  .rectangle 62 3 76 14 44,
  .rectangle 62 15 91 25 33,
  .rectangle 62 26 91 36 38,
  .rectangle 62 37 91 47 43,
  .rectangle 77 3 91 8 16,
  .rectangle 77 9 91 14 18], by decide +kernel⟩
private def batch3 : PaidBatch .one 1 := ⟨[
  .rectangle 92 3 106 8 19,
  .rectangle 92 9 106 14 21,
  .rectangle 92 15 121 25 45,
  .rectangle 92 26 121 36 52,
  .rectangle 92 37 121 47 60,
  .rectangle 107 3 121 8 21], by decide +kernel⟩
private def batch4 : PaidBatch .one 1 := ⟨[
  .rectangle 107 9 121 14 23], by decide +kernel⟩

private def batches : List (PaidBatch .one 1) := [batch0, batch1, batch2, batch3, batch4]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 121 3 8 = true := by decide +kernel
private theorem index11 : checks tiles 121 11 8 = true := by decide +kernel
private theorem index19 : checks tiles 121 19 8 = true := by decide +kernel
private theorem index27 : checks tiles 121 27 8 = true := by decide +kernel
private theorem index35 : checks tiles 121 35 8 = true := by decide +kernel
private theorem index43 : checks tiles 121 43 5 = true := by decide +kernel
private theorem covers : checks tiles 121 3 45 = true :=
  (checks_join (checks_join (checks_join (checks_join (checks_join index3 index11) index19) index27) index35) index43)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 121) (hj : a.j ≤ 47) : Covered 2 .one a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2

private def batch0 : PaidBatch .one 2 := ⟨[
  .rectangle 2 6 31 16 12,
  .rectangle 2 17 31 26 11,
  .rectangle 2 27 61 47 39,
  .rectangle 32 6 61 16 24,
  .rectangle 32 17 61 26 22,
  .rectangle 62 6 91 16 35], by decide +kernel⟩
private def batch1 : PaidBatch .one 2 := ⟨[
  .rectangle 62 17 91 26 33,
  .rectangle 62 27 91 37 40,
  .rectangle 62 38 91 47 44,
  .rectangle 92 6 121 16 47,
  .rectangle 92 17 121 26 44,
  .rectangle 92 27 121 37 55], by decide +kernel⟩
private def batch2 : PaidBatch .one 2 := ⟨[
  .rectangle 92 38 121 47 61], by decide +kernel⟩

private def batches : List (PaidBatch .one 2) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 121 6 8 = true := by decide +kernel
private theorem index14 : checks tiles 121 14 8 = true := by decide +kernel
private theorem index22 : checks tiles 121 22 8 = true := by decide +kernel
private theorem index30 : checks tiles 121 30 8 = true := by decide +kernel
private theorem index38 : checks tiles 121 38 8 = true := by decide +kernel
private theorem index46 : checks tiles 121 46 2 = true := by decide +kernel
private theorem covers : checks tiles 121 6 42 = true :=
  (checks_join (checks_join (checks_join (checks_join (checks_join index6 index14) index22) index30) index38) index46)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 121) (hj : a.j ≤ 47) : Covered 3 .one a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3

private def batch0 : PaidBatch .one 3 := ⟨[
  .rectangle 3 9 32 28 26,
  .rectangle 3 29 62 47 39,
  .rectangle 33 9 62 18 21,
  .rectangle 33 19 62 28 24,
  .rectangle 63 9 92 18 31,
  .rectangle 63 19 92 28 35], by decide +kernel⟩
private def batch1 : PaidBatch .one 3 := ⟨[
  .rectangle 63 29 92 38 41,
  .rectangle 63 39 92 47 45,
  .rectangle 93 9 121 18 40,
  .rectangle 93 19 121 28 46,
  .rectangle 93 29 121 38 55,
  .rectangle 93 39 121 47 61], by decide +kernel⟩

private def batches : List (PaidBatch .one 3) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 121 9 8 = true := by decide +kernel
private theorem index17 : checks tiles 121 17 8 = true := by decide +kernel
private theorem index25 : checks tiles 121 25 8 = true := by decide +kernel
private theorem index33 : checks tiles 121 33 8 = true := by decide +kernel
private theorem index41 : checks tiles 121 41 7 = true := by decide +kernel
private theorem covers : checks tiles 121 9 39 = true :=
  (checks_join (checks_join (checks_join (checks_join index9 index17) index25) index33) index41)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 121) (hj : a.j ≤ 47) : Covered 4 .one a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

namespace Top4

private def batch0 : PaidBatch .one 4 := ⟨[
  .rectangle 4 12 62 29 41,
  .rectangle 4 30 62 47 40,
  .rectangle 63 12 92 20 29,
  .rectangle 63 21 92 29 35,
  .rectangle 63 30 92 38 41,
  .rectangle 63 39 92 47 47], by decide +kernel⟩
private def batch1 : PaidBatch .one 4 := ⟨[
  .rectangle 93 12 121 20 37,
  .rectangle 93 21 121 29 45,
  .rectangle 93 30 121 38 54,
  .rectangle 93 39 121 47 62], by decide +kernel⟩

private def batches : List (PaidBatch .one 4) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 121 12 8 = true := by decide +kernel
private theorem index20 : checks tiles 121 20 8 = true := by decide +kernel
private theorem index28 : checks tiles 121 28 8 = true := by decide +kernel
private theorem index36 : checks tiles 121 36 8 = true := by decide +kernel
private theorem index44 : checks tiles 121 44 4 = true := by decide +kernel
private theorem covers : checks tiles 121 12 36 = true :=
  (checks_join (checks_join (checks_join (checks_join index12 index20) index28) index36) index44)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 121) (hj : a.j ≤ 47) : Covered 5 .one a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

namespace Top5

private def batch0 : PaidBatch .one 5 := ⟨[
  .rectangle 5 15 63 31 39,
  .rectangle 5 32 63 47 40,
  .rectangle 64 15 92 23 30,
  .rectangle 64 24 92 31 35,
  .rectangle 64 32 92 47 59,
  .rectangle 93 15 121 23 40], by decide +kernel⟩
private def batch1 : PaidBatch .one 5 := ⟨[
  .rectangle 93 24 121 31 45,
  .rectangle 93 32 121 39 54,
  .rectangle 93 40 121 47 62], by decide +kernel⟩

private def batches : List (PaidBatch .one 5) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 121 15 8 = true := by decide +kernel
private theorem index23 : checks tiles 121 23 8 = true := by decide +kernel
private theorem index31 : checks tiles 121 31 8 = true := by decide +kernel
private theorem index39 : checks tiles 121 39 8 = true := by decide +kernel
private theorem index47 : checks tiles 121 47 1 = true := by decide +kernel
private theorem covers : checks tiles 121 15 33 = true :=
  (checks_join (checks_join (checks_join (checks_join index15 index23) index31) index39) index47)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 121) (hj : a.j ≤ 47) : Covered 6 .one a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

end Compact50PriceTableOne1
