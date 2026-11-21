import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered)

namespace Compact50PriceTableOne6
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top6

private def batch0 : PaidBatch .one 6 := ⟨[
  .rectangle 6 18 63 32 35,
  .rectangle 6 33 63 47 40,
  .rectangle 64 18 92 32 50,
  .rectangle 64 33 92 47 58,
  .rectangle 93 18 107 25 35,
  .rectangle 93 26 107 32 40], by decide +kernel⟩
private def batch1 : PaidBatch .one 6 := ⟨[
  .rectangle 93 33 107 40 49,
  .rectangle 93 41 107 47 54,
  .rectangle 108 18 121 25 39,
  .rectangle 108 26 121 32 45,
  .rectangle 108 33 121 40 55,
  .rectangle 108 41 121 47 61], by decide +kernel⟩

private def batches : List (PaidBatch .one 6) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 121 18 8 = true := by decide +kernel
private theorem index26 : checks tiles 121 26 8 = true := by decide +kernel
private theorem index34 : checks tiles 121 34 8 = true := by decide +kernel
private theorem index42 : checks tiles 121 42 6 = true := by decide +kernel
private theorem covers : checks tiles 121 18 30 = true :=
  (checks_join (checks_join (checks_join index18 index26) index34) index42)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 121) (hj : a.j ≤ 47) : Covered 7 .one a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7

private def batch0 : PaidBatch .one 7 := ⟨[
  .rectangle 7 21 35 47 49,
  .rectangle 36 21 64 34 35,
  .rectangle 36 35 64 47 39,
  .rectangle 65 21 93 34 49,
  .rectangle 65 35 93 47 56,
  .rectangle 94 21 107 34 56], by decide +kernel⟩
private def batch1 : PaidBatch .one 7 := ⟨[
  .rectangle 94 35 107 41 49,
  .rectangle 94 42 107 47 53,
  .rectangle 108 21 121 27 39,
  .rectangle 108 28 121 34 47,
  .rectangle 108 35 121 41 55,
  .rectangle 108 42 121 47 60], by decide +kernel⟩

private def batches : List (PaidBatch .one 7) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 121 21 8 = true := by decide +kernel
private theorem index29 : checks tiles 121 29 8 = true := by decide +kernel
private theorem index37 : checks tiles 121 37 8 = true := by decide +kernel
private theorem index45 : checks tiles 121 45 3 = true := by decide +kernel
private theorem covers : checks tiles 121 21 27 = true :=
  (checks_join (checks_join (checks_join index21 index29) index37) index45)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 121) (hj : a.j ≤ 47) : Covered 8 .one a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

namespace Top8

private def batch0 : PaidBatch .one 8 := ⟨[
  .rectangle 8 24 36 47 44,
  .rectangle 37 24 64 35 32,
  .rectangle 37 36 64 47 39,
  .rectangle 65 24 93 35 46,
  .rectangle 65 36 93 47 55,
  .rectangle 94 24 121 35 59], by decide +kernel⟩
private def batch1 : PaidBatch .one 8 := ⟨[
  .rectangle 94 36 107 41 48,
  .rectangle 94 42 107 47 54,
  .rectangle 108 36 121 41 54,
  .rectangle 108 42 121 47 61], by decide +kernel⟩

private def batches : List (PaidBatch .one 8) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 121 24 8 = true := by decide +kernel
private theorem index32 : checks tiles 121 32 8 = true := by decide +kernel
private theorem index40 : checks tiles 121 40 8 = true := by decide +kernel
private theorem covers : checks tiles 121 24 24 = true :=
  (checks_join (checks_join index24 index32) index40)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 121) (hj : a.j ≤ 47) : Covered 9 .one a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

namespace Top9

private def batch0 : PaidBatch .one 9 := ⟨[
  .rectangle 9 27 65 47 53,
  .rectangle 66 27 93 37 45,
  .rectangle 66 38 93 47 52,
  .rectangle 94 27 121 37 58,
  .rectangle 94 38 107 47 60,
  .rectangle 108 38 121 42 54], by decide +kernel⟩
private def batch1 : PaidBatch .one 9 := ⟨[
  .rectangle 108 43 121 47 59], by decide +kernel⟩

private def batches : List (PaidBatch .one 9) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 121 27 8 = true := by decide +kernel
private theorem index35 : checks tiles 121 35 8 = true := by decide +kernel
private theorem index43 : checks tiles 121 43 5 = true := by decide +kernel
private theorem covers : checks tiles 121 27 21 = true :=
  (checks_join (checks_join index27 index35) index43)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 121) (hj : a.j ≤ 47) : Covered 10 .one a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

namespace Top10

private def batch0 : PaidBatch .one 10 := ⟨[
  .rectangle 10 30 65 47 48,
  .rectangle 66 30 93 38 43,
  .rectangle 66 39 93 47 51,
  .rectangle 94 30 121 38 55,
  .rectangle 94 39 107 47 59,
  .rectangle 108 39 121 43 55], by decide +kernel⟩
private def batch1 : PaidBatch .one 10 := ⟨[
  .rectangle 108 44 121 47 58], by decide +kernel⟩

private def batches : List (PaidBatch .one 10) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 121 30 8 = true := by decide +kernel
private theorem index38 : checks tiles 121 38 8 = true := by decide +kernel
private theorem index46 : checks tiles 121 46 2 = true := by decide +kernel
private theorem covers : checks tiles 121 30 18 = true :=
  (checks_join (checks_join index30 index38) index46)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 121) (hj : a.j ≤ 47) : Covered 11 .one a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

namespace Top11

private def batch0 : PaidBatch .one 11 := ⟨[
  .rectangle 11 33 66 47 45,
  .rectangle 67 33 94 40 44,
  .rectangle 67 41 94 47 49,
  .rectangle 95 33 121 40 56,
  .rectangle 95 41 108 47 56,
  .rectangle 109 41 115 47 60], by decide +kernel⟩
private def batch1 : PaidBatch .one 11 := ⟨[
  .rectangle 116 41 121 44 55,
  .rectangle 116 45 121 47 57], by decide +kernel⟩

private def batches : List (PaidBatch .one 11) := [batch0, batch1]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 121 33 8 = true := by decide +kernel
private theorem index41 : checks tiles 121 41 7 = true := by decide +kernel
private theorem covers : checks tiles 121 33 15 = true :=
  (checks_join index33 index41)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 121) (hj : a.j ≤ 47) : Covered 12 .one a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

namespace Top12

private def batch0 : PaidBatch .one 12 := ⟨[
  .rectangle 12 36 66 47 41,
  .rectangle 67 36 94 47 56,
  .rectangle 95 36 108 41 48,
  .rectangle 95 42 108 47 55,
  .rectangle 109 36 121 41 54,
  .rectangle 109 42 121 47 61], by decide +kernel⟩

private def batches : List (PaidBatch .one 12) := [batch0]
private abbrev tiles := tilesOf batches

private theorem index36 : checks tiles 121 36 8 = true := by decide +kernel
private theorem index44 : checks tiles 121 44 4 = true := by decide +kernel
private theorem covers : checks tiles 121 36 12 = true :=
  (checks_join index36 index44)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 12)
    (hb : a.b ≤ 121) (hj : a.j ≤ 47) : Covered 13 .one a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top12

end Compact50PriceTableOne6
