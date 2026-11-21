import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableTwo7
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top1

private def batch0 : PaidBatch .two7 1 := ⟨[
  .rectangle 1 3 122 8 74,
  .rectangle 3 9 122 13 74,
  .rectangle 5 14 63 24 102,
  .rectangle 9 25 65 45 109,
  .rectangle 64 14 122 19 102,
  .rectangle 64 20 122 24 107], by decide +kernel⟩
private def batch1 : PaidBatch .two7 1 := ⟨[
  .rectangle 66 36 94 45 112,
  .rectangle 66 25 122 30 109,
  .rectangle 66 31 122 35 109,
  .rectangle 95 36 108 40 112,
  .rectangle 95 41 108 45 112,
  .rectangle 109 41 115 43 112], by decide +kernel⟩
private def batch2 : PaidBatch .two7 1 := ⟨[
  .rectangle 109 44 115 45 112,
  .rectangle 109 36 122 38 112,
  .rectangle 109 39 122 40 112,
  .rectangle 116 45 119 45 112,
  .rectangle 116 41 122 42 112,
  .rectangle 116 43 122 43 112], by decide +kernel⟩
private def batch3 : PaidBatch .two7 1 := ⟨[
  .rectangle 116 44 122 44 112,
  .rectangle 120 45 121 45 112,
  .point 122 45 112], by decide +kernel⟩

private def batches : List (PaidBatch .two7 1) := [batch0, batch1, batch2, batch3]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 122 3 43 = true := by decide +kernel
private theorem covers : checks tiles 122 3 43 = true :=
  index3

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 3 .two7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2

private def batch0 : PaidBatch .two7 2 := ⟨[
  .rectangle 2 6 122 10 74,
  .rectangle 4 11 122 15 101,
  .rectangle 6 16 64 25 102,
  .rectangle 9 26 65 45 109,
  .rectangle 65 16 122 20 102,
  .rectangle 65 21 122 25 107], by decide +kernel⟩
private def batch1 : PaidBatch .two7 2 := ⟨[
  .rectangle 66 36 94 45 112,
  .rectangle 66 26 122 30 109,
  .rectangle 66 31 122 35 109,
  .rectangle 95 36 108 40 112,
  .rectangle 95 41 108 45 112,
  .rectangle 109 41 115 43 112], by decide +kernel⟩
private def batch2 : PaidBatch .two7 2 := ⟨[
  .rectangle 109 44 115 45 112,
  .rectangle 109 36 122 38 112,
  .rectangle 109 39 122 40 112,
  .rectangle 116 44 119 44 112,
  .rectangle 116 45 119 45 112,
  .rectangle 116 41 122 42 112], by decide +kernel⟩
private def batch3 : PaidBatch .two7 2 := ⟨[
  .rectangle 116 43 122 43 112,
  .point 120 45 112,
  .rectangle 120 44 121 44 112,
  .point 121 45 112,
  .point 122 44 112,
  .point 122 45 112], by decide +kernel⟩

private def batches : List (PaidBatch .two7 2) := [batch0, batch1, batch2, batch3]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 122 6 40 = true := by decide +kernel
private theorem covers : checks tiles 122 6 40 = true :=
  index6

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 4 .two7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3

private def batch0 : PaidBatch .two7 3 := ⟨[
  .rectangle 3 9 122 13 74,
  .rectangle 5 14 122 18 102,
  .rectangle 7 19 122 27 107,
  .rectangle 10 28 66 45 109,
  .rectangle 67 37 94 45 112,
  .rectangle 67 28 122 32 109], by decide +kernel⟩
private def batch1 : PaidBatch .two7 3 := ⟨[
  .rectangle 67 33 122 36 111,
  .rectangle 95 37 108 41 112,
  .rectangle 95 42 108 45 112,
  .rectangle 109 42 115 43 112,
  .rectangle 109 44 115 44 112,
  .rectangle 109 45 115 45 112], by decide +kernel⟩
private def batch2 : PaidBatch .two7 3 := ⟨[
  .rectangle 109 37 122 39 112,
  .rectangle 109 40 122 41 112,
  .rectangle 116 45 117 45 112,
  .rectangle 116 43 119 43 112,
  .rectangle 116 44 119 44 112,
  .rectangle 116 42 122 42 112], by decide +kernel⟩
private def batch3 : PaidBatch .two7 3 := ⟨[
  .point 118 45 112,
  .point 119 45 112,
  .point 120 44 112,
  .point 120 45 112,
  .rectangle 120 43 121 43 112,
  .point 121 44 112], by decide +kernel⟩
private def batch4 : PaidBatch .two7 3 := ⟨[
  .point 121 45 112,
  .point 122 43 112,
  .point 122 44 112,
  .point 122 45 112], by decide +kernel⟩

private def batches : List (PaidBatch .two7 3) := [batch0, batch1, batch2, batch3, batch4]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 122 9 37 = true := by decide +kernel
private theorem covers : checks tiles 122 9 37 = true :=
  index9

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 5 .two7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

namespace Top4

private def batch0 : PaidBatch .two7 4 := ⟨[
  .rectangle 4 12 122 20 102,
  .rectangle 7 21 122 28 107,
  .rectangle 10 29 66 45 109,
  .rectangle 67 38 94 45 112,
  .rectangle 67 29 122 33 109,
  .rectangle 67 34 122 37 112], by decide +kernel⟩
private def batch1 : PaidBatch .two7 4 := ⟨[
  .rectangle 95 38 108 41 112,
  .rectangle 95 42 108 45 112,
  .rectangle 109 42 115 43 112,
  .rectangle 109 44 115 44 112,
  .rectangle 109 45 115 45 112,
  .rectangle 109 38 122 39 112], by decide +kernel⟩
private def batch2 : PaidBatch .two7 4 := ⟨[
  .rectangle 109 40 122 41 112,
  .point 116 45 112,
  .rectangle 116 44 117 44 112,
  .rectangle 116 43 119 43 112,
  .rectangle 116 42 122 42 112,
  .point 117 45 112], by decide +kernel⟩
private def batch3 : PaidBatch .two7 4 := ⟨[
  .rectangle 118 44 118 44 112,
  .point 118 45 112,
  .point 119 44 112,
  .point 119 45 112,
  .rectangle 120 43 120 43 112,
  .point 120 44 112], by decide +kernel⟩
private def batch4 : PaidBatch .two7 4 := ⟨[
  .point 120 45 112,
  .point 121 43 112,
  .point 121 44 112,
  .point 121 45 112,
  .point 122 43 112,
  .point 122 44 112], by decide +kernel⟩
private def batch5 : PaidBatch .two7 4 := ⟨[
  .point 122 45 112], by decide +kernel⟩

private def batches : List (PaidBatch .two7 4) := [batch0, batch1, batch2, batch3, batch4, batch5]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 122 12 34 = true := by decide +kernel
private theorem covers : checks tiles 122 12 34 = true :=
  index12

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 6 .two7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

namespace Top5

private def batch0 : PaidBatch .two7 5 := ⟨[
  .rectangle 5 15 122 22 102,
  .rectangle 8 23 122 30 109,
  .rectangle 11 31 66 45 109,
  .rectangle 67 39 94 45 112,
  .rectangle 67 31 122 34 109,
  .rectangle 67 35 122 38 112], by decide +kernel⟩
private def batch1 : PaidBatch .two7 5 := ⟨[
  .rectangle 95 39 108 42 112,
  .rectangle 95 43 108 45 112,
  .rectangle 109 45 112 45 112,
  .rectangle 109 41 115 42 112,
  .rectangle 109 43 115 43 112,
  .rectangle 109 44 115 44 112], by decide +kernel⟩
private def batch2 : PaidBatch .two7 5 := ⟨[
  .rectangle 109 39 122 40 112,
  .rectangle 113 45 114 45 112,
  .point 115 45 112,
  .point 116 45 112,
  .rectangle 116 44 117 44 112,
  .rectangle 116 43 119 43 112], by decide +kernel⟩
private def batch3 : PaidBatch .two7 5 := ⟨[
  .rectangle 116 41 122 41 112,
  .rectangle 116 42 122 42 112,
  .point 117 45 112,
  .point 118 44 112,
  .point 118 45 112,
  .point 119 44 112], by decide +kernel⟩
private def batch4 : PaidBatch .two7 5 := ⟨[
  .point 119 45 112,
  .point 120 43 112,
  .point 120 44 112,
  .point 120 45 112,
  .point 121 43 112,
  .point 121 44 112], by decide +kernel⟩
private def batch5 : PaidBatch .two7 5 := ⟨[
  .point 121 45 112,
  .point 122 43 112,
  .point 122 44 112,
  .point 122 45 112], by decide +kernel⟩

private def batches : List (PaidBatch .two7 5) := [batch0, batch1, batch2, batch3, batch4, batch5]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 122 15 31 = true := by decide +kernel
private theorem covers : checks tiles 122 15 31 = true :=
  index15

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 7 .two7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

namespace Top6

private def batch0 : PaidBatch .two7 6 := ⟨[
  .rectangle 6 18 122 24 102,
  .rectangle 9 25 122 31 109,
  .rectangle 11 32 66 45 109,
  .rectangle 67 32 94 38 111,
  .rectangle 67 39 94 45 112,
  .rectangle 95 39 108 42 112], by decide +kernel⟩
private def batch1 : PaidBatch .two7 6 := ⟨[
  .rectangle 95 43 108 45 112,
  .rectangle 95 32 122 35 111,
  .rectangle 95 36 122 38 112,
  .rectangle 109 45 112 45 112,
  .rectangle 109 41 115 42 112,
  .rectangle 109 43 115 43 112], by decide +kernel⟩
private def batch2 : PaidBatch .two7 6 := ⟨[
  .rectangle 109 44 115 44 112,
  .rectangle 109 39 122 40 112,
  .rectangle 113 45 114 45 112,
  .point 115 45 112,
  .rectangle 116 44 116 44 112,
  .point 116 45 112], by decide +kernel⟩
private def batch3 : PaidBatch .two7 6 := ⟨[
  .rectangle 116 42 119 42 112,
  .rectangle 116 43 119 43 112,
  .rectangle 116 41 122 41 112,
  .point 117 44 112,
  .point 117 45 112,
  .point 118 44 112], by decide +kernel⟩
private def batch4 : PaidBatch .two7 6 := ⟨[
  .point 118 45 112,
  .point 119 44 112,
  .point 119 45 112,
  .point 120 43 112,
  .point 120 44 112,
  .point 120 45 112], by decide +kernel⟩
private def batch5 : PaidBatch .two7 6 := ⟨[
  .rectangle 120 42 121 42 112,
  .point 121 43 112,
  .point 121 44 112,
  .point 121 45 112,
  .point 122 42 112,
  .point 122 43 112], by decide +kernel⟩
private def batch6 : PaidBatch .two7 6 := ⟨[
  .point 122 44 112,
  .point 122 45 112], by decide +kernel⟩

private def batches : List (PaidBatch .two7 6) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 122 18 28 = true := by decide +kernel
private theorem covers : checks tiles 122 18 28 = true :=
  index18

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 8 .two7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7

private def batch0 : PaidBatch .two7 7 := ⟨[
  .rectangle 7 21 64 33 107,
  .rectangle 12 34 67 45 109,
  .rectangle 65 21 122 27 107,
  .rectangle 65 28 122 33 109,
  .rectangle 68 34 95 39 112,
  .rectangle 68 40 95 45 112], by decide +kernel⟩
private def batch1 : PaidBatch .two7 7 := ⟨[
  .rectangle 96 43 102 45 112,
  .rectangle 96 40 109 42 112,
  .rectangle 96 34 122 36 112,
  .rectangle 96 37 122 39 112,
  .rectangle 103 43 109 44 112,
  .rectangle 103 45 109 45 112], by decide +kernel⟩
private def batch2 : PaidBatch .two7 7 := ⟨[
  .rectangle 110 45 113 45 112,
  .rectangle 110 42 116 42 112,
  .rectangle 110 43 116 43 112,
  .rectangle 110 44 116 44 112,
  .rectangle 110 40 122 40 112,
  .rectangle 110 41 122 41 112], by decide +kernel⟩
private def batch3 : PaidBatch .two7 7 := ⟨[
  .point 114 45 112,
  .point 115 45 112,
  .point 116 45 112,
  .point 117 44 112,
  .point 117 45 112,
  .rectangle 117 42 119 42 112], by decide +kernel⟩
private def batch4 : PaidBatch .two7 7 := ⟨[
  .rectangle 117 43 119 43 112,
  .point 118 44 112,
  .point 118 45 112,
  .point 119 44 112,
  .point 119 45 112,
  .point 120 43 112], by decide +kernel⟩
private def batch5 : PaidBatch .two7 7 := ⟨[
  .point 120 44 112,
  .point 120 45 112,
  .rectangle 120 42 121 42 112,
  .point 121 43 112,
  .point 121 44 112,
  .point 121 45 112], by decide +kernel⟩
private def batch6 : PaidBatch .two7 7 := ⟨[
  .point 122 42 112,
  .point 122 43 112,
  .point 122 44 112,
  .point 122 45 112], by decide +kernel⟩

private def batches : List (PaidBatch .two7 7) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 122 21 25 = true := by decide +kernel
private theorem covers : checks tiles 122 21 25 = true :=
  index21

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 9 .two7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

namespace Top8

private def batch0 : PaidBatch .two7 8 := ⟨[
  .rectangle 8 24 65 34 109,
  .rectangle 12 35 67 45 109,
  .rectangle 66 24 122 29 109,
  .rectangle 66 30 122 34 109,
  .rectangle 68 35 95 40 112,
  .rectangle 68 41 95 45 112], by decide +kernel⟩
private def batch1 : PaidBatch .two7 8 := ⟨[
  .rectangle 96 38 109 40 112,
  .rectangle 96 41 109 43 112,
  .rectangle 96 44 109 45 112,
  .rectangle 96 35 122 37 112,
  .rectangle 110 45 113 45 112,
  .rectangle 110 43 116 43 112], by decide +kernel⟩
private def batch2 : PaidBatch .two7 8 := ⟨[
  .rectangle 110 44 116 44 112,
  .rectangle 110 38 122 39 112,
  .rectangle 110 40 122 40 112,
  .rectangle 110 41 122 41 112,
  .rectangle 110 42 122 42 112,
  .point 114 45 112], by decide +kernel⟩
private def batch3 : PaidBatch .two7 8 := ⟨[
  .point 115 45 112,
  .point 116 45 112,
  .point 117 44 112,
  .point 117 45 112,
  .rectangle 117 43 119 43 112,
  .point 118 44 112], by decide +kernel⟩
private def batch4 : PaidBatch .two7 8 := ⟨[
  .point 118 45 112,
  .point 119 44 112,
  .point 119 45 112,
  .point 120 43 112,
  .point 120 44 112,
  .point 120 45 112], by decide +kernel⟩
private def batch5 : PaidBatch .two7 8 := ⟨[
  .point 121 43 112,
  .point 121 44 112,
  .point 121 45 112,
  .point 122 43 112,
  .point 122 44 112,
  .point 122 45 112], by decide +kernel⟩

private def batches : List (PaidBatch .two7 8) := [batch0, batch1, batch2, batch3, batch4, batch5]
private abbrev tiles := tilesOf batches

private theorem index24 : checks tiles 122 24 22 = true := by decide +kernel
private theorem covers : checks tiles 122 24 22 = true :=
  index24

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 8)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 10 .two7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top8

namespace Top9

private def batch0 : PaidBatch .two7 9 := ⟨[
  .rectangle 9 27 65 36 109,
  .rectangle 13 37 67 45 109,
  .rectangle 66 27 122 31 109,
  .rectangle 66 32 122 36 111,
  .rectangle 68 37 95 41 112,
  .rectangle 68 42 95 45 112], by decide +kernel⟩
private def batch1 : PaidBatch .two7 9 := ⟨[
  .rectangle 96 42 109 43 112,
  .rectangle 96 44 109 45 112,
  .rectangle 96 37 122 39 112,
  .rectangle 96 40 122 41 112,
  .rectangle 110 45 113 45 112,
  .rectangle 110 43 116 43 112], by decide +kernel⟩
private def batch2 : PaidBatch .two7 9 := ⟨[
  .rectangle 110 44 116 44 112,
  .rectangle 110 42 122 42 112,
  .point 114 45 112,
  .point 115 45 112,
  .point 116 45 112,
  .point 117 44 112], by decide +kernel⟩
private def batch3 : PaidBatch .two7 9 := ⟨[
  .point 117 45 112,
  .rectangle 117 43 119 43 112,
  .point 118 44 112,
  .point 118 45 112,
  .point 119 44 112,
  .point 119 45 112], by decide +kernel⟩
private def batch4 : PaidBatch .two7 9 := ⟨[
  .point 120 43 112,
  .point 120 44 112,
  .point 120 45 112,
  .point 121 43 112,
  .point 121 44 112,
  .point 121 45 112], by decide +kernel⟩
private def batch5 : PaidBatch .two7 9 := ⟨[
  .point 122 43 112,
  .point 122 44 112,
  .point 122 45 112], by decide +kernel⟩

private def batches : List (PaidBatch .two7 9) := [batch0, batch1, batch2, batch3, batch4, batch5]
private abbrev tiles := tilesOf batches

private theorem index27 : checks tiles 122 27 19 = true := by decide +kernel
private theorem covers : checks tiles 122 27 19 = true :=
  index27

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 9)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 11 .two7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top9

namespace Top10

private def batch0 : PaidBatch .two7 10 := ⟨[
  .rectangle 10 30 66 45 109,
  .rectangle 67 38 94 45 112,
  .rectangle 67 30 122 33 109,
  .rectangle 67 34 122 37 112,
  .rectangle 95 42 108 43 112,
  .rectangle 95 44 108 45 112], by decide +kernel⟩
private def batch1 : PaidBatch .two7 10 := ⟨[
  .rectangle 95 38 122 39 112,
  .rectangle 95 40 122 41 112,
  .rectangle 109 45 112 45 112,
  .rectangle 109 42 115 43 112,
  .rectangle 109 44 115 44 112,
  .rectangle 113 45 114 45 112], by decide +kernel⟩
private def batch2 : PaidBatch .two7 10 := ⟨[
  .point 115 45 112,
  .point 116 45 112,
  .rectangle 116 44 117 44 112,
  .rectangle 116 43 119 43 112,
  .rectangle 116 42 122 42 112,
  .point 117 45 112], by decide +kernel⟩
private def batch3 : PaidBatch .two7 10 := ⟨[
  .point 118 44 112,
  .point 118 45 112,
  .point 119 44 112,
  .point 119 45 112,
  .rectangle 120 43 120 43 112,
  .point 120 44 112], by decide +kernel⟩
private def batch4 : PaidBatch .two7 10 := ⟨[
  .point 120 45 112,
  .point 121 43 112,
  .point 121 44 112,
  .point 121 45 112,
  .point 122 43 112,
  .point 122 44 112], by decide +kernel⟩
private def batch5 : PaidBatch .two7 10 := ⟨[
  .point 122 45 112], by decide +kernel⟩

private def batches : List (PaidBatch .two7 10) := [batch0, batch1, batch2, batch3, batch4, batch5]
private abbrev tiles := tilesOf batches

private theorem index30 : checks tiles 122 30 16 = true := by decide +kernel
private theorem covers : checks tiles 122 30 16 = true :=
  index30

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 10)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 12 .two7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top10

namespace Top11

private def batch0 : PaidBatch .two7 11 := ⟨[
  .rectangle 11 33 66 45 109,
  .rectangle 67 33 94 39 111,
  .rectangle 67 40 94 45 112,
  .rectangle 95 40 108 42 112,
  .rectangle 95 43 108 45 112,
  .rectangle 95 33 122 36 111], by decide +kernel⟩
private def batch1 : PaidBatch .two7 11 := ⟨[
  .rectangle 95 37 122 39 112,
  .rectangle 109 45 112 45 112,
  .rectangle 109 43 115 43 112,
  .rectangle 109 44 115 44 112,
  .rectangle 109 40 122 41 112,
  .rectangle 109 42 122 42 112], by decide +kernel⟩
private def batch2 : PaidBatch .two7 11 := ⟨[
  .rectangle 113 45 114 45 112,
  .point 115 45 112,
  .point 116 45 112,
  .rectangle 116 44 117 44 112,
  .rectangle 116 43 119 43 112,
  .point 117 45 112], by decide +kernel⟩
private def batch3 : PaidBatch .two7 11 := ⟨[
  .point 118 44 112,
  .point 118 45 112,
  .point 119 44 112,
  .point 119 45 112,
  .rectangle 120 43 120 43 112,
  .point 120 44 112], by decide +kernel⟩
private def batch4 : PaidBatch .two7 11 := ⟨[
  .point 120 45 112,
  .point 121 43 112,
  .point 121 44 112,
  .point 121 45 112,
  .point 122 43 112,
  .point 122 44 112], by decide +kernel⟩
private def batch5 : PaidBatch .two7 11 := ⟨[
  .point 122 45 112], by decide +kernel⟩

private def batches : List (PaidBatch .two7 11) := [batch0, batch1, batch2, batch3, batch4, batch5]
private abbrev tiles := tilesOf batches

private theorem index33 : checks tiles 122 33 13 = true := by decide +kernel
private theorem covers : checks tiles 122 33 13 = true :=
  index33

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 11)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 13 .two7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top11

namespace Top12

private def batch0 : PaidBatch .two7 12 := ⟨[
  .rectangle 12 36 67 45 109,
  .rectangle 68 36 95 40 112,
  .rectangle 68 41 95 45 112,
  .rectangle 96 41 109 43 112,
  .rectangle 96 44 109 45 112,
  .rectangle 96 36 122 38 112], by decide +kernel⟩
private def batch1 : PaidBatch .two7 12 := ⟨[
  .rectangle 96 39 122 40 112,
  .rectangle 110 45 113 45 112,
  .rectangle 110 43 116 43 112,
  .rectangle 110 44 116 44 112,
  .rectangle 110 41 122 41 112,
  .rectangle 110 42 122 42 112], by decide +kernel⟩
private def batch2 : PaidBatch .two7 12 := ⟨[
  .rectangle 114 45 114 45 112,
  .point 115 45 112,
  .point 116 45 112,
  .rectangle 117 44 117 44 112,
  .point 117 45 112,
  .rectangle 117 43 119 43 112], by decide +kernel⟩
private def batch3 : PaidBatch .two7 12 := ⟨[
  .point 118 44 112,
  .point 118 45 112,
  .point 119 44 112,
  .point 119 45 112,
  .point 120 44 112,
  .point 120 45 112], by decide +kernel⟩
private def batch4 : PaidBatch .two7 12 := ⟨[
  .rectangle 120 43 121 43 112,
  .point 121 44 112,
  .point 121 45 112,
  .point 122 43 112,
  .point 122 44 112,
  .point 122 45 112], by decide +kernel⟩

private def batches : List (PaidBatch .two7 12) := [batch0, batch1, batch2, batch3, batch4]
private abbrev tiles := tilesOf batches

private theorem index36 : checks tiles 122 36 10 = true := by decide +kernel
private theorem covers : checks tiles 122 36 10 = true :=
  index36

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 12)
    (hb : a.b ≤ 122) (hj : a.j ≤ 45) : Covered 14 .two7 a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top12

theorem price (top : ℕ) (htop : top ≤ 14) (a : Shape) (ha : Valid a)
    (hc : InBox ((start .two7).plus a) (fullCap top)) : Covered top .two7 a := by
  change 3+a.b ≤ 125 ∧ 7+a.j ≤ 52 ∧ 2+a.t ≤ top at hc
  obtain ⟨hb,hj,ht⟩ := hc
  have ht0 := ha.1
  have hb' : a.b ≤ 122 := by omega
  have hj' : a.j ≤ 45 := by omega
  have casesTop : a.t = 1 ∨ a.t = 2 ∨ a.t = 3 ∨ a.t = 4 ∨ a.t = 5 ∨ a.t = 6 ∨ a.t = 7 ∨ a.t = 8 ∨ a.t = 9 ∨ a.t = 10 ∨ a.t = 11 ∨ a.t = 12 := by omega
  rcases casesTop with ht1 | ht2 | ht3 | ht4 | ht5 | ht6 | ht7 | ht8 | ht9 | ht10 | ht11 | ht12
  · exact covered_mono (Top1.exact a ha ht1 hb' hj') (by omega) htop
  · exact covered_mono (Top2.exact a ha ht2 hb' hj') (by omega) htop
  · exact covered_mono (Top3.exact a ha ht3 hb' hj') (by omega) htop
  · exact covered_mono (Top4.exact a ha ht4 hb' hj') (by omega) htop
  · exact covered_mono (Top5.exact a ha ht5 hb' hj') (by omega) htop
  · exact covered_mono (Top6.exact a ha ht6 hb' hj') (by omega) htop
  · exact covered_mono (Top7.exact a ha ht7 hb' hj') (by omega) htop
  · exact covered_mono (Top8.exact a ha ht8 hb' hj') (by omega) htop
  · exact covered_mono (Top9.exact a ha ht9 hb' hj') (by omega) htop
  · exact covered_mono (Top10.exact a ha ht10 hb' hj') (by omega) htop
  · exact covered_mono (Top11.exact a ha ht11 hb' hj') (by omega) htop
  · exact covered_mono (Top12.exact a ha ht12 hb' hj') (by omega) htop
end Compact50PriceTableTwo7
