import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered)

namespace Compact50PriceTableEmpty5
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top5

private def batch0 : PaidBatch .empty 5 := ⟨[
  .rectangle 5 15 34 32 21,
  .rectangle 5 33 63 50 39,
  .rectangle 35 15 63 23 19,
  .rectangle 35 24 63 32 23,
  .rectangle 64 15 93 23 28,
  .rectangle 64 24 93 32 34], by decide +kernel⟩
private def batch1 : PaidBatch .empty 5 := ⟨[
  .rectangle 64 33 93 41 40,
  .rectangle 64 42 93 50 46,
  .rectangle 94 15 122 23 36,
  .rectangle 94 24 122 32 44,
  .rectangle 94 33 108 41 47,
  .rectangle 94 42 108 46 46], by decide +kernel⟩
private def batch2 : PaidBatch .empty 5 := ⟨[
  .rectangle 94 47 108 50 48,
  .rectangle 109 33 122 37 43,
  .rectangle 109 38 122 41 46,
  .rectangle 109 42 115 46 49,
  .rectangle 109 47 115 50 51,
  .rectangle 116 42 122 44 47], by decide +kernel⟩
private def batch3 : PaidBatch .empty 5 := ⟨[
  .rectangle 116 45 122 46 48,
  .rectangle 116 47 119 48 49,
  .rectangle 116 49 119 50 50,
  .rectangle 120 47 122 48 50,
  .rectangle 120 49 121 50 51,
  .point 122 49 46], by decide +kernel⟩
private def batch4 : PaidBatch .empty 5 := ⟨[
  .point 122 50 47], by decide +kernel⟩

private def batches : List (PaidBatch .empty 5) := [batch0, batch1, batch2, batch3, batch4]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 122 15 8 = true := by decide +kernel
private theorem index23 : checks tiles 122 23 8 = true := by decide +kernel
private theorem index31 : checks tiles 122 31 8 = true := by decide +kernel
private theorem index39 : checks tiles 122 39 8 = true := by decide +kernel
private theorem index47 : checks tiles 122 47 4 = true := by decide +kernel
private theorem covers : checks tiles 122 15 36 = true :=
  (checks_join (checks_join (checks_join (checks_join index15 index23) index31) index39) index47)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 122) (hj : a.j ≤ 50) : Covered 5 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

namespace Top6

private def batch0 : PaidBatch .empty 6 := ⟨[
  .rectangle 6 18 35 34 21,
  .rectangle 6 35 64 50 39,
  .rectangle 36 18 64 34 36,
  .rectangle 65 18 93 26 30,
  .rectangle 65 27 93 34 34,
  .rectangle 65 35 93 42 40], by decide +kernel⟩
private def batch1 : PaidBatch .empty 6 := ⟨[
  .rectangle 65 43 93 50 46,
  .rectangle 94 18 122 26 39,
  .rectangle 94 27 122 34 45,
  .rectangle 94 35 108 42 47,
  .rectangle 94 43 101 50 50,
  .rectangle 102 43 108 46 45], by decide +kernel⟩
private def batch2 : PaidBatch .empty 6 := ⟨[
  .rectangle 102 47 108 50 49,
  .rectangle 109 35 122 38 43,
  .rectangle 109 39 122 42 47,
  .rectangle 109 43 115 46 48,
  .rectangle 109 47 112 50 50,
  .rectangle 113 47 115 48 48], by decide +kernel⟩
private def batch3 : PaidBatch .empty 6 := ⟨[
  .rectangle 113 49 115 50 50,
  .rectangle 116 43 119 46 50,
  .rectangle 116 47 119 48 49,
  .rectangle 116 49 119 50 51,
  .rectangle 120 43 122 46 51,
  .rectangle 120 47 122 48 51], by decide +kernel⟩
private def batch4 : PaidBatch .empty 6 := ⟨[
  .rectangle 120 49 121 49 50,
  .rectangle 120 50 121 50 51,
  .point 122 49 47,
  .point 122 50 48], by decide +kernel⟩

private def batches : List (PaidBatch .empty 6) := [batch0, batch1, batch2, batch3, batch4]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 122 18 8 = true := by decide +kernel
private theorem index26 : checks tiles 122 26 8 = true := by decide +kernel
private theorem index34 : checks tiles 122 34 8 = true := by decide +kernel
private theorem index42 : checks tiles 122 42 8 = true := by decide +kernel
private theorem index50 : checks tiles 122 50 1 = true := by decide +kernel
private theorem covers : checks tiles 122 18 33 = true :=
  (checks_join (checks_join (checks_join (checks_join index18 index26) index34) index42) index50)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 122) (hj : a.j ≤ 50) : Covered 6 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7

private def batch0 : PaidBatch .empty 7 := ⟨[
  .rectangle 7 21 64 35 33,
  .rectangle 7 36 64 50 39,
  .rectangle 65 21 79 35 40,
  .rectangle 65 36 79 50 48,
  .rectangle 80 21 93 28 30,
  .rectangle 80 29 93 35 34], by decide +kernel⟩
private def batch1 : PaidBatch .empty 7 := ⟨[
  .rectangle 80 36 93 43 42,
  .rectangle 80 44 93 50 46,
  .rectangle 94 21 108 28 34,
  .rectangle 94 29 108 35 39,
  .rectangle 94 36 108 43 48,
  .rectangle 94 44 101 50 49], by decide +kernel⟩
private def batch2 : PaidBatch .empty 7 := ⟨[
  .rectangle 102 44 108 47 47,
  .rectangle 102 48 108 50 48,
  .rectangle 109 21 122 28 39,
  .rectangle 109 29 122 35 44,
  .rectangle 109 36 122 39 44,
  .rectangle 109 40 122 43 48], by decide +kernel⟩
private def batch3 : PaidBatch .empty 7 := ⟨[
  .rectangle 109 44 115 47 50,
  .rectangle 109 48 115 50 51,
  .rectangle 116 44 119 47 51,
  .rectangle 116 48 119 49 51,
  .rectangle 116 50 119 50 51,
  .rectangle 120 44 122 45 48], by decide +kernel⟩
private def batch4 : PaidBatch .empty 7 := ⟨[
  .rectangle 120 46 122 47 50,
  .rectangle 120 48 121 48 50,
  .rectangle 120 49 121 49 51,
  .point 120 50 48,
  .point 121 50 48,
  .point 122 48 47], by decide +kernel⟩
private def batch5 : PaidBatch .empty 7 := ⟨[
  .point 122 49 48,
  .point 122 50 49], by decide +kernel⟩

private def batches : List (PaidBatch .empty 7) := [batch0, batch1, batch2, batch3, batch4, batch5]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 122 21 8 = true := by decide +kernel
private theorem index29 : checks tiles 122 29 8 = true := by decide +kernel
private theorem index37 : checks tiles 122 37 8 = true := by decide +kernel
private theorem index45 : checks tiles 122 45 6 = true := by decide +kernel
private theorem covers : checks tiles 122 21 30 = true :=
  (checks_join (checks_join (checks_join index21 index29) index37) index45)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 122) (hj : a.j ≤ 50) : Covered 7 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

namespace Top8

private def batch0 : PaidBatch .empty 8 := ⟨[
  .rectangle 8 24 36 37 20,
  .rectangle 8 38 36 50 30,
  .rectangle 37 24 65 37 33,
  .rectangle 37 38 65 50 38,
  .rectangle 66 24 80 37 40,
  .rectangle 66 38 80 50 46], by decide +kernel⟩
private def batch1 : PaidBatch .empty 8 := ⟨[
  .rectangle 81 24 94 30 30,
  .rectangle 81 31 94 37 36,
  .rectangle 81 38 94 44 42,
  .rectangle 81 45 94 50 46,
  .rectangle 95 24 108 30 35,
  .rectangle 95 31 108 37 41], by decide +kernel⟩
private def batch2 : PaidBatch .empty 8 := ⟨[
  .rectangle 95 38 108 44 48,
  .rectangle 95 45 101 50 49,
  .rectangle 102 45 108 47 46,
  .rectangle 102 48 108 50 49,
  .rectangle 109 24 122 30 39,
  .rectangle 109 31 122 37 46], by decide +kernel⟩
private def batch3 : PaidBatch .empty 8 := ⟨[
  .rectangle 109 38 115 41 44,
  .rectangle 109 42 115 44 46,
  .rectangle 109 45 115 47 49,
  .rectangle 109 48 112 50 50,
  .rectangle 113 48 115 49 50,
  .rectangle 113 50 115 50 50], by decide +kernel⟩
private def batch4 : PaidBatch .empty 8 := ⟨[
  .rectangle 116 38 122 41 47,
  .rectangle 116 42 122 44 49,
  .rectangle 116 45 119 47 50,
  .rectangle 116 48 119 49 51,
  .rectangle 116 50 119 50 51,
  .rectangle 120 45 122 46 50], by decide +kernel⟩
private def batch5 : PaidBatch .empty 8 := ⟨[
  .rectangle 120 47 122 47 49,
  .rectangle 120 48 121 48 50,
  .rectangle 120 49 121 49 51,
  .point 120 50 48,
  .point 121 50 49,
  .point 122 48 47], by decide +kernel⟩
private def batch6 : PaidBatch .empty 8 := ⟨[
  .point 122 49 48,
  .point 122 50 49], by decide +kernel⟩

private def batches : List (PaidBatch .empty 8) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 122 24 8 = true := by decide +kernel
private theorem index32 : checks tiles 122 32 8 = true := by decide +kernel
private theorem index40 : checks tiles 122 40 8 = true := by decide +kernel
private theorem index48 : checks tiles 122 48 3 = true := by decide +kernel
private theorem covers : checks tiles 122 24 27 = true :=
  (checks_join (checks_join (checks_join index24 index32) index40) index48)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 122) (hj : a.j ≤ 50) : Covered 8 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

end Compact50PriceTableEmpty5
