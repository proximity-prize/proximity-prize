import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered)

namespace Compact50PriceTableTwo6
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top6

private def batch0 : PaidBatch .two 6 := ⟨[
  .rectangle 6 18 34 44 80,
  .rectangle 35 18 63 31 56,
  .rectangle 35 32 63 44 62,
  .rectangle 64 18 92 31 80,
  .rectangle 64 32 92 44 90,
  .rectangle 93 18 106 24 54], by decide +kernel⟩
private def batch1 : PaidBatch .two 6 := ⟨[
  .rectangle 93 25 106 31 66,
  .rectangle 93 32 106 38 77,
  .rectangle 93 39 106 44 85,
  .rectangle 107 18 120 24 61,
  .rectangle 107 25 120 31 74,
  .rectangle 107 32 120 38 88], by decide +kernel⟩
private def batch2 : PaidBatch .two 6 := ⟨[
  .rectangle 107 39 113 44 90,
  .rectangle 114 39 120 41 83,
  .rectangle 114 42 120 44 89], by decide +kernel⟩

private def batches : List (PaidBatch .two 6) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 120 18 8 = true := by decide +kernel
private theorem index26 : checks tiles 120 26 8 = true := by decide +kernel
private theorem index34 : checks tiles 120 34 8 = true := by decide +kernel
private theorem index42 : checks tiles 120 42 3 = true := by decide +kernel
private theorem covers : checks tiles 120 18 27 = true :=
  (checks_join (checks_join (checks_join index18 index26) index34) index42)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 120) (hj : a.j ≤ 44) : Covered 8 .two a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7

private def batch0 : PaidBatch .two 7 := ⟨[
  .rectangle 7 21 35 44 70,
  .rectangle 36 21 63 32 51,
  .rectangle 36 33 63 44 61,
  .rectangle 64 21 92 32 73,
  .rectangle 64 33 92 44 88,
  .rectangle 93 21 106 32 84], by decide +kernel⟩
private def batch1 : PaidBatch .two 7 := ⟨[
  .rectangle 93 33 106 38 75,
  .rectangle 93 39 106 44 85,
  .rectangle 107 21 120 26 61,
  .rectangle 107 27 120 32 73,
  .rectangle 107 33 120 38 85,
  .rectangle 107 39 113 44 91], by decide +kernel⟩
private def batch2 : PaidBatch .two 7 := ⟨[
  .rectangle 114 39 120 41 83,
  .rectangle 114 42 120 44 89], by decide +kernel⟩

private def batches : List (PaidBatch .two 7) := [batch0, batch1, batch2]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 120 21 8 = true := by decide +kernel
private theorem index29 : checks tiles 120 29 8 = true := by decide +kernel
private theorem index37 : checks tiles 120 37 8 = true := by decide +kernel
private theorem covers : checks tiles 120 21 24 = true :=
  (checks_join (checks_join index21 index29) index37)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 120) (hj : a.j ≤ 44) : Covered 9 .two a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

namespace Top8

private def batch0 : PaidBatch .two 8 := ⟨[
  .rectangle 8 24 64 44 87,
  .rectangle 65 24 92 34 72,
  .rectangle 65 35 92 44 83,
  .rectangle 93 24 106 34 83,
  .rectangle 93 35 106 39 75,
  .rectangle 93 40 106 44 83], by decide +kernel⟩
private def batch1 : PaidBatch .two 8 := ⟨[
  .rectangle 107 24 120 29 67,
  .rectangle 107 30 120 34 74,
  .rectangle 107 35 120 39 84,
  .rectangle 107 40 113 44 89,
  .rectangle 114 40 120 42 85,
  .rectangle 114 43 120 44 87], by decide +kernel⟩

private def batches : List (PaidBatch .two 8) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 120 24 8 = true := by decide +kernel
private theorem index32 : checks tiles 120 32 8 = true := by decide +kernel
private theorem index40 : checks tiles 120 40 5 = true := by decide +kernel
private theorem covers : checks tiles 120 24 21 = true :=
  (checks_join (checks_join index24 index32) index40)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 120) (hj : a.j ≤ 44) : Covered 10 .two a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

namespace Top9

private def batch0 : PaidBatch .two 9 := ⟨[
  .rectangle 9 27 64 44 78,
  .rectangle 65 27 92 35 68,
  .rectangle 65 36 92 44 81,
  .rectangle 93 27 120 35 87,
  .rectangle 93 36 106 40 76,
  .rectangle 93 41 106 44 81], by decide +kernel⟩
private def batch1 : PaidBatch .two 9 := ⟨[
  .rectangle 107 36 120 40 86,
  .rectangle 107 41 120 44 92], by decide +kernel⟩

private def batches : List (PaidBatch .two 9) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 120 27 8 = true := by decide +kernel
private theorem index35 : checks tiles 120 35 8 = true := by decide +kernel
private theorem index43 : checks tiles 120 43 2 = true := by decide +kernel
private theorem covers : checks tiles 120 27 18 = true :=
  (checks_join (checks_join index27 index35) index43)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 120) (hj : a.j ≤ 44) : Covered 11 .two a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

namespace Top10

private def batch0 : PaidBatch .two 10 := ⟨[
  .rectangle 10 30 65 44 71,
  .rectangle 66 30 93 37 69,
  .rectangle 66 38 93 44 78,
  .rectangle 94 30 120 37 88,
  .rectangle 94 38 107 44 89,
  .rectangle 108 38 114 41 81], by decide +kernel⟩
private def batch1 : PaidBatch .two 10 := ⟨[
  .rectangle 108 42 114 44 85,
  .rectangle 115 38 120 41 85,
  .rectangle 115 42 120 44 89], by decide +kernel⟩

private def batches : List (PaidBatch .two 10) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 120 30 8 = true := by decide +kernel
private theorem index38 : checks tiles 120 38 7 = true := by decide +kernel
private theorem covers : checks tiles 120 30 15 = true :=
  (checks_join index30 index38)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 120) (hj : a.j ≤ 44) : Covered 12 .two a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

namespace Top11

private def batch0 : PaidBatch .two 11 := ⟨[
  .rectangle 11 33 65 44 65,
  .rectangle 66 33 93 44 90,
  .rectangle 94 33 107 38 75,
  .rectangle 94 39 107 44 86,
  .rectangle 108 33 120 38 84,
  .rectangle 108 39 114 41 79], by decide +kernel⟩
private def batch1 : PaidBatch .two 11 := ⟨[
  .rectangle 108 42 114 44 85,
  .rectangle 115 39 120 41 83,
  .rectangle 115 42 120 44 89], by decide +kernel⟩

private def batches : List (PaidBatch .two 11) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 120 33 8 = true := by decide +kernel
private theorem index41 : checks tiles 120 41 4 = true := by decide +kernel
private theorem covers : checks tiles 120 33 12 = true :=
  (checks_join index33 index41)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 120) (hj : a.j ≤ 44) : Covered 13 .two a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

end Compact50PriceTableTwo6
