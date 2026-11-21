import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered)

namespace Compact50PriceTableEmpty9
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top9

private def batch0 : PaidBatch .empty 9 := ⟨[
  .rectangle 9 27 37 38 20,
  .rectangle 9 39 37 50 30,
  .rectangle 38 27 65 38 31,
  .rectangle 38 39 65 50 38,
  .rectangle 66 27 94 38 44,
  .rectangle 66 39 80 50 46], by decide +kernel⟩
private def batch1 : PaidBatch .empty 9 := ⟨[
  .rectangle 81 39 94 44 41,
  .rectangle 81 45 94 50 46,
  .rectangle 95 27 108 32 35,
  .rectangle 95 33 108 38 41,
  .rectangle 95 39 108 44 47,
  .rectangle 95 45 101 50 49], by decide +kernel⟩
private def batch2 : PaidBatch .empty 9 := ⟨[
  .rectangle 102 45 108 47 46,
  .rectangle 102 48 108 50 49,
  .rectangle 109 27 122 32 39,
  .rectangle 109 33 122 38 46,
  .rectangle 109 39 115 44 50,
  .rectangle 109 45 115 47 49], by decide +kernel⟩
private def batch3 : PaidBatch .empty 9 := ⟨[
  .rectangle 109 48 112 50 51,
  .rectangle 113 48 115 49 50,
  .rectangle 113 50 115 50 50,
  .rectangle 116 39 122 41 45,
  .rectangle 116 42 122 44 49,
  .rectangle 116 45 119 47 51], by decide +kernel⟩
private def batch4 : PaidBatch .empty 9 := ⟨[
  .rectangle 116 48 117 49 51,
  .rectangle 116 50 117 50 51,
  .rectangle 118 48 119 48 50,
  .rectangle 118 49 119 49 51,
  .point 118 50 48,
  .point 119 50 48], by decide +kernel⟩
private def batch5 : PaidBatch .empty 9 := ⟨[
  .rectangle 120 45 122 46 50,
  .rectangle 120 47 122 47 50,
  .rectangle 120 48 121 48 50,
  .rectangle 120 49 121 49 51,
  .point 120 50 49,
  .point 121 50 49], by decide +kernel⟩
private def batch6 : PaidBatch .empty 9 := ⟨[
  .point 122 48 48,
  .point 122 49 49,
  .point 122 50 50], by decide +kernel⟩

private def batches : List (PaidBatch .empty 9) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 122 27 8 = true := by decide +kernel
private theorem index35 : checks tiles 122 35 8 = true := by decide +kernel
private theorem index43 : checks tiles 122 43 8 = true := by decide +kernel
private theorem covers : checks tiles 122 27 24 = true :=
  (checks_join (checks_join index27 index35) index43)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 122) (hj : a.j ≤ 50) : Covered 9 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

namespace Top10

private def batch0 : PaidBatch .empty 10 := ⟨[
  .rectangle 10 30 38 50 40,
  .rectangle 39 30 66 40 32,
  .rectangle 39 41 66 50 37,
  .rectangle 67 30 94 40 44,
  .rectangle 67 41 80 50 44,
  .rectangle 81 41 94 45 41], by decide +kernel⟩
private def batch1 : PaidBatch .empty 10 := ⟨[
  .rectangle 81 46 94 50 45,
  .rectangle 95 30 108 35 38,
  .rectangle 95 36 108 40 42,
  .rectangle 95 41 108 45 47,
  .rectangle 95 46 101 50 48,
  .rectangle 102 46 108 48 47], by decide +kernel⟩
private def batch2 : PaidBatch .empty 10 := ⟨[
  .rectangle 102 49 108 50 48,
  .rectangle 109 30 122 35 43,
  .rectangle 109 36 122 40 47,
  .rectangle 109 41 115 45 49,
  .rectangle 109 46 115 48 50,
  .rectangle 109 49 115 50 51], by decide +kernel⟩
private def batch3 : PaidBatch .empty 10 := ⟨[
  .rectangle 116 41 122 43 48,
  .rectangle 116 44 122 45 49,
  .rectangle 116 46 119 47 50,
  .rectangle 116 48 119 48 50,
  .rectangle 116 49 117 49 50,
  .rectangle 116 50 117 50 51], by decide +kernel⟩
private def batch4 : PaidBatch .empty 10 := ⟨[
  .rectangle 118 49 119 49 51,
  .point 118 50 48,
  .point 119 50 49,
  .rectangle 120 46 122 47 51,
  .rectangle 120 48 122 48 51,
  .point 120 49 48], by decide +kernel⟩
private def batch5 : PaidBatch .empty 10 := ⟨[
  .point 120 50 49,
  .point 121 49 48,
  .point 121 50 50,
  .point 122 49 49,
  .point 122 50 50], by decide +kernel⟩

private def batches : List (PaidBatch .empty 10) := [batch0, batch1, batch2, batch3, batch4, batch5]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 122 30 8 = true := by decide +kernel
private theorem index38 : checks tiles 122 38 8 = true := by decide +kernel
private theorem index46 : checks tiles 122 46 5 = true := by decide +kernel
private theorem covers : checks tiles 122 30 21 = true :=
  (checks_join (checks_join index30 index38) index46)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 122) (hj : a.j ≤ 50) : Covered 10 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

namespace Top11

private def batch0 : PaidBatch .empty 11 := ⟨[
  .rectangle 11 33 38 50 36,
  .rectangle 39 33 66 50 46,
  .rectangle 67 33 94 41 42,
  .rectangle 67 42 80 50 43,
  .rectangle 81 42 94 46 42,
  .rectangle 81 47 94 50 44], by decide +kernel⟩
private def batch1 : PaidBatch .empty 11 := ⟨[
  .rectangle 95 33 108 41 48,
  .rectangle 95 42 108 46 48,
  .rectangle 95 47 101 50 47,
  .rectangle 102 47 108 50 51,
  .rectangle 109 33 122 37 43,
  .rectangle 109 38 122 41 47], by decide +kernel⟩
private def batch2 : PaidBatch .empty 11 := ⟨[
  .rectangle 109 42 115 44 46,
  .rectangle 109 45 115 46 47,
  .rectangle 109 47 112 48 48,
  .rectangle 109 49 112 50 50,
  .rectangle 113 47 115 48 49,
  .rectangle 113 49 115 50 51], by decide +kernel⟩
private def batch3 : PaidBatch .empty 11 := ⟨[
  .rectangle 116 42 122 44 49,
  .rectangle 116 45 122 46 50,
  .rectangle 116 47 119 48 51,
  .rectangle 116 49 117 49 50,
  .rectangle 116 50 117 50 51,
  .rectangle 118 49 119 49 51], by decide +kernel⟩
private def batch4 : PaidBatch .empty 11 := ⟨[
  .point 118 50 49,
  .point 119 50 49,
  .rectangle 120 47 121 47 49,
  .rectangle 120 48 121 48 51,
  .point 120 49 48,
  .point 120 50 49], by decide +kernel⟩
private def batch5 : PaidBatch .empty 11 := ⟨[
  .point 121 49 49,
  .point 121 50 50,
  .point 122 47 47,
  .point 122 48 48,
  .point 122 49 49,
  .point 122 50 50], by decide +kernel⟩

private def batches : List (PaidBatch .empty 11) := [batch0, batch1, batch2, batch3, batch4, batch5]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 122 33 8 = true := by decide +kernel
private theorem index41 : checks tiles 122 41 8 = true := by decide +kernel
private theorem index49 : checks tiles 122 49 2 = true := by decide +kernel
private theorem covers : checks tiles 122 33 18 = true :=
  (checks_join (checks_join index33 index41) index49)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 122) (hj : a.j ≤ 50) : Covered 11 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

namespace Top12

private def batch0 : PaidBatch .empty 12 := ⟨[
  .rectangle 12 36 67 50 43,
  .rectangle 68 36 95 43 43,
  .rectangle 68 44 95 50 48,
  .rectangle 96 36 109 43 49,
  .rectangle 96 44 102 47 45,
  .rectangle 96 48 102 50 47], by decide +kernel⟩
private def batch1 : PaidBatch .empty 12 := ⟨[
  .rectangle 103 44 109 47 48,
  .rectangle 103 48 109 50 50,
  .rectangle 110 36 122 39 44,
  .rectangle 110 40 122 43 49,
  .rectangle 110 44 113 47 50,
  .rectangle 110 48 113 49 50], by decide +kernel⟩
private def batch2 : PaidBatch .empty 12 := ⟨[
  .rectangle 110 50 113 50 50,
  .rectangle 114 44 116 45 46,
  .rectangle 114 46 116 47 49,
  .rectangle 114 48 116 49 51,
  .rectangle 114 50 116 50 51,
  .rectangle 117 44 122 45 49], by decide +kernel⟩
private def batch3 : PaidBatch .empty 12 := ⟨[
  .rectangle 117 46 122 47 51,
  .rectangle 117 48 118 48 49,
  .rectangle 117 49 118 49 51,
  .point 117 50 48,
  .point 118 50 49,
  .point 119 48 47], by decide +kernel⟩
private def batch4 : PaidBatch .empty 12 := ⟨[
  .point 119 49 48,
  .point 119 50 49,
  .rectangle 120 48 121 48 51,
  .point 120 49 48,
  .point 120 50 49,
  .point 121 49 49], by decide +kernel⟩
private def batch5 : PaidBatch .empty 12 := ⟨[
  .point 121 50 50,
  .point 122 48 48,
  .point 122 49 49,
  .point 122 50 50], by decide +kernel⟩

private def batches : List (PaidBatch .empty 12) := [batch0, batch1, batch2, batch3, batch4, batch5]
private abbrev tiles := tilesOf batches

private theorem index36 : checks tiles 122 36 8 = true := by decide +kernel
private theorem index44 : checks tiles 122 44 7 = true := by decide +kernel
private theorem covers : checks tiles 122 36 15 = true :=
  (checks_join index36 index44)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 12)
    (hb : a.b ≤ 122) (hj : a.j ≤ 50) : Covered 12 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top12

namespace Top13

private def batch0 : PaidBatch .empty 13 := ⟨[
  .rectangle 13 39 67 50 40,
  .rectangle 68 39 81 50 47,
  .rectangle 82 39 95 44 41,
  .rectangle 82 45 95 50 47,
  .rectangle 96 39 109 44 47,
  .rectangle 96 45 102 50 50], by decide +kernel⟩
private def batch1 : PaidBatch .empty 13 := ⟨[
  .rectangle 103 45 109 47 47,
  .rectangle 103 48 109 50 50,
  .rectangle 110 39 116 44 50,
  .rectangle 110 45 116 47 50,
  .rectangle 110 48 113 49 50,
  .rectangle 110 50 113 50 50], by decide +kernel⟩
private def batch2 : PaidBatch .empty 13 := ⟨[
  .rectangle 114 48 116 49 51,
  .rectangle 114 50 116 50 51,
  .rectangle 117 39 122 41 45,
  .rectangle 117 42 122 44 49,
  .rectangle 117 45 119 47 51,
  .rectangle 117 48 118 48 49], by decide +kernel⟩
private def batch3 : PaidBatch .empty 13 := ⟨[
  .rectangle 117 49 118 49 51,
  .point 117 50 48,
  .point 118 50 49,
  .point 119 48 47,
  .point 119 49 48,
  .point 119 50 49], by decide +kernel⟩
private def batch4 : PaidBatch .empty 13 := ⟨[
  .rectangle 120 45 122 46 50,
  .rectangle 120 47 122 47 50,
  .rectangle 120 48 121 48 51,
  .point 120 49 48,
  .point 120 50 49,
  .point 121 49 49], by decide +kernel⟩
private def batch5 : PaidBatch .empty 13 := ⟨[
  .point 121 50 50,
  .point 122 48 48,
  .point 122 49 49,
  .point 122 50 50], by decide +kernel⟩

private def batches : List (PaidBatch .empty 13) := [batch0, batch1, batch2, batch3, batch4, batch5]
private abbrev tiles := tilesOf batches

private theorem index39 : checks tiles 122 39 8 = true := by decide +kernel
private theorem index47 : checks tiles 122 47 4 = true := by decide +kernel
private theorem covers : checks tiles 122 39 12 = true :=
  (checks_join index39 index47)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 13)
    (hb : a.b ≤ 122) (hj : a.j ≤ 50) : Covered 13 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top13

end Compact50PriceTableEmpty9
