import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace Compact50PriceTableEmpty1
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Final50Price (fullCap)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered covered_mono)
open Compact50Cover (PaidBatch tilesOf checks checks_join apply_batches)

namespace Top1

private def batch0 : PaidBatch .empty 1 := ⟨[
  .rectangle 1 3 125 3 1,
  .rectangle 2 5 17 6 1,
  .rectangle 2 4 63 4 1,
  .rectangle 3 7 10 9 1,
  .rectangle 4 10 64 15 14,
  .rectangle 6 16 65 27 28], by decide +kernel⟩
private def batch1 : PaidBatch .empty 1 := ⟨[
  .rectangle 10 28 67 40 39,
  .rectangle 11 7 18 9 3,
  .rectangle 14 41 67 52 45,
  .rectangle 18 5 32 5 1,
  .rectangle 18 6 32 6 5,
  .rectangle 19 7 33 9 5], by decide +kernel⟩
private def batch2 : PaidBatch .empty 1 := ⟨[
  .rectangle 33 5 63 6 17,
  .rectangle 34 7 64 9 19,
  .rectangle 64 4 125 4 33,
  .rectangle 64 5 125 6 33,
  .rectangle 65 7 125 9 35,
  .rectangle 65 10 125 15 36], by decide +kernel⟩
private def batch3 : PaidBatch .empty 1 := ⟨[
  .rectangle 66 16 125 21 40,
  .rectangle 66 22 125 27 42,
  .rectangle 68 28 96 34 44,
  .rectangle 68 35 96 40 46,
  .rectangle 68 41 96 46 46,
  .rectangle 68 47 96 52 46], by decide +kernel⟩
private def batch4 : PaidBatch .empty 1 := ⟨[
  .rectangle 97 44 111 46 48,
  .rectangle 97 47 111 49 48,
  .rectangle 97 50 111 52 48,
  .rectangle 97 28 125 34 46,
  .rectangle 97 35 125 37 46,
  .rectangle 97 38 125 40 47], by decide +kernel⟩
private def batch5 : PaidBatch .empty 1 := ⟨[
  .rectangle 97 41 125 43 47,
  .rectangle 112 44 118 46 48,
  .rectangle 112 47 118 49 48,
  .rectangle 112 50 118 51 49,
  .rectangle 112 52 118 52 49,
  .rectangle 119 52 120 52 49], by decide +kernel⟩
private def batch6 : PaidBatch .empty 1 := ⟨[
  .rectangle 119 50 122 50 49,
  .rectangle 119 51 122 51 49,
  .rectangle 119 44 125 45 48,
  .rectangle 119 46 125 46 48,
  .rectangle 119 47 125 47 48,
  .rectangle 119 48 125 48 48], by decide +kernel⟩
private def batch7 : PaidBatch .empty 1 := ⟨[
  .rectangle 119 49 125 49 49,
  .rectangle 121 52 121 52 49,
  .point 122 52 49,
  .point 123 51 49,
  .point 123 52 49,
  .rectangle 123 50 124 50 49], by decide +kernel⟩
private def batch8 : PaidBatch .empty 1 := ⟨[
  .point 124 51 49,
  .point 124 52 49,
  .point 125 50 49,
  .point 125 51 49,
  .point 125 52 49], by decide +kernel⟩

private def batches : List (PaidBatch .empty 1) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 125 3 30 = true := by decide +kernel
private theorem index33 : checks tiles 125 33 20 = true := by decide +kernel
private theorem covers : checks tiles 125 3 50 = true :=
  checks_join index3 index33

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 125) (hj : a.j ≤ 52) : Covered 1 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2

private def batch0 : PaidBatch .empty 2 := ⟨[
  .rectangle 2 6 9 8 1,
  .rectangle 3 9 64 11 9,
  .rectangle 4 12 64 17 21,
  .rectangle 6 18 65 29 33,
  .rectangle 10 6 17 7 1,
  .rectangle 10 8 17 8 8], by decide +kernel⟩
private def batch1 : PaidBatch .empty 2 := ⟨[
  .rectangle 10 30 67 41 39,
  .rectangle 14 42 67 52 45,
  .rectangle 18 6 32 8 5,
  .rectangle 33 6 63 8 19,
  .rectangle 64 6 125 8 34,
  .rectangle 65 9 125 11 36], by decide +kernel⟩
private def batch2 : PaidBatch .empty 2 := ⟨[
  .rectangle 65 12 125 17 37,
  .rectangle 66 18 125 23 40,
  .rectangle 66 24 125 29 43,
  .rectangle 68 36 96 41 46,
  .rectangle 68 42 96 47 46,
  .rectangle 68 48 96 52 46], by decide +kernel⟩
private def batch3 : PaidBatch .empty 2 := ⟨[
  .rectangle 68 30 125 35 45,
  .rectangle 97 42 111 44 47,
  .rectangle 97 45 111 47 48,
  .rectangle 97 48 111 50 48,
  .rectangle 97 51 111 52 48,
  .rectangle 97 36 125 38 47], by decide +kernel⟩
private def batch4 : PaidBatch .empty 2 := ⟨[
  .rectangle 97 39 125 41 47,
  .rectangle 112 52 115 52 49,
  .rectangle 112 42 118 44 48,
  .rectangle 112 45 118 47 48,
  .rectangle 112 48 118 48 48,
  .rectangle 112 49 118 49 48], by decide +kernel⟩
private def batch5 : PaidBatch .empty 2 := ⟨[
  .rectangle 112 50 118 50 49,
  .rectangle 112 51 118 51 49,
  .rectangle 116 52 117 52 49,
  .point 118 52 49,
  .point 119 51 49,
  .point 119 52 49], by decide +kernel⟩
private def batch6 : PaidBatch .empty 2 := ⟨[
  .rectangle 119 48 120 48 48,
  .rectangle 119 50 120 50 49,
  .rectangle 119 47 122 47 48,
  .rectangle 119 49 122 49 49,
  .rectangle 119 42 125 43 48,
  .rectangle 119 44 125 44 48], by decide +kernel⟩
private def batch7 : PaidBatch .empty 2 := ⟨[
  .rectangle 119 45 125 45 48,
  .rectangle 119 46 125 46 48,
  .point 120 51 49,
  .point 120 52 49,
  .rectangle 121 48 121 48 48,
  .point 121 50 49], by decide +kernel⟩
private def batch8 : PaidBatch .empty 2 := ⟨[
  .point 121 51 49,
  .point 121 52 49,
  .rectangle 122 48 122 48 49,
  .point 122 50 49,
  .point 122 51 49,
  .point 122 52 49], by decide +kernel⟩
private def batch9 : PaidBatch .empty 2 := ⟨[
  .rectangle 123 47 123 47 48,
  .point 123 49 49,
  .point 123 50 49,
  .point 123 51 49,
  .point 123 52 49,
  .rectangle 123 48 124 48 49], by decide +kernel⟩
private def batch10 : PaidBatch .empty 2 := ⟨[
  .point 124 47 48,
  .point 124 49 49,
  .point 124 50 49,
  .point 124 51 49,
  .point 124 52 49,
  .point 125 47 48], by decide +kernel⟩
private def batch11 : PaidBatch .empty 2 := ⟨[
  .point 125 48 49,
  .point 125 49 49,
  .point 125 50 49,
  .point 125 51 49,
  .point 125 52 49], by decide +kernel⟩

private def batches : List (PaidBatch .empty 2) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 125 6 22 = true := by decide +kernel
theorem index28 : checks tiles 125 28 22 = true := by decide +kernel
private theorem index50 : checks tiles 125 50 3 = true := by decide +kernel
private theorem covers : checks tiles 125 6 47 = true :=
  checks_join index6 (checks_join index28 index50)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 125) (hj : a.j ≤ 52) : Covered 2 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3

private def batch0 : PaidBatch .empty 3 := ⟨[
  .rectangle 3 9 33 14 9,
  .rectangle 5 15 125 19 28,
  .rectangle 7 20 66 30 33,
  .rectangle 11 31 68 41 39,
  .rectangle 14 42 68 52 45,
  .rectangle 34 9 64 14 25], by decide +kernel⟩
private def batch1 : PaidBatch .empty 3 := ⟨[
  .rectangle 65 9 125 14 36,
  .rectangle 67 20 125 25 41,
  .rectangle 67 26 125 30 43,
  .rectangle 69 31 97 36 45,
  .rectangle 69 37 97 41 46,
  .rectangle 69 42 97 47 46], by decide +kernel⟩
private def batch2 : PaidBatch .empty 3 := ⟨[
  .rectangle 69 48 97 52 48,
  .rectangle 98 48 104 50 48,
  .rectangle 98 51 104 52 48,
  .rectangle 98 37 111 41 47,
  .rectangle 98 42 111 44 47,
  .rectangle 98 45 111 47 48], by decide +kernel⟩
private def batch3 : PaidBatch .empty 3 := ⟨[
  .rectangle 98 31 125 36 46,
  .rectangle 105 48 111 49 48,
  .rectangle 105 50 111 50 48,
  .rectangle 105 51 111 52 49,
  .rectangle 112 52 113 52 49,
  .rectangle 112 49 115 49 48], by decide +kernel⟩
private def batch4 : PaidBatch .empty 3 := ⟨[
  .rectangle 112 50 115 50 49,
  .rectangle 112 51 115 51 49,
  .rectangle 112 42 118 44 48,
  .rectangle 112 45 118 46 48,
  .rectangle 112 47 118 47 48,
  .rectangle 112 48 118 48 48], by decide +kernel⟩
private def batch5 : PaidBatch .empty 3 := ⟨[
  .rectangle 112 37 125 39 47,
  .rectangle 112 40 125 41 47,
  .point 114 52 49,
  .point 115 52 49,
  .point 116 51 49,
  .point 116 52 49], by decide +kernel⟩
private def batch6 : PaidBatch .empty 3 := ⟨[
  .rectangle 116 50 117 50 49,
  .rectangle 116 49 118 49 49,
  .point 117 51 49,
  .point 117 52 49,
  .point 118 50 49,
  .point 118 51 49], by decide +kernel⟩
private def batch7 : PaidBatch .empty 3 := ⟨[
  .point 118 52 49,
  .point 119 48 48,
  .point 119 49 49,
  .point 119 50 49,
  .point 119 51 49,
  .point 119 52 49], by decide +kernel⟩
private def batch8 : PaidBatch .empty 3 := ⟨[
  .rectangle 119 47 120 47 48,
  .rectangle 119 45 122 45 48,
  .rectangle 119 46 122 46 48,
  .rectangle 119 42 125 43 48,
  .rectangle 119 44 125 44 48,
  .point 120 48 48], by decide +kernel⟩
private def batch9 : PaidBatch .empty 3 := ⟨[
  .point 120 49 49,
  .point 120 50 49,
  .point 120 51 49,
  .point 120 52 49,
  .point 121 47 48,
  .point 121 48 48], by decide +kernel⟩
private def batch10 : PaidBatch .empty 3 := ⟨[
  .point 121 49 49,
  .point 121 50 49,
  .point 121 51 49,
  .point 121 52 49,
  .point 122 47 48,
  .point 122 48 49], by decide +kernel⟩
private def batch11 : PaidBatch .empty 3 := ⟨[
  .point 122 49 49,
  .point 122 50 49,
  .point 122 51 49,
  .shared 122 52 49 ⟨.tilted, 1, 1, false, 150459072624832372⟩,
  .point 123 46 48,
  .point 123 47 48], by decide +kernel⟩
private def batch12 : PaidBatch .empty 3 := ⟨[
  .point 123 48 49,
  .point 123 49 49,
  .point 123 50 49,
  .point 123 51 49,
  .shared 123 52 49 ⟨.tilted, 1, 1, false, 151792867842807181⟩,
  .rectangle 123 45 124 45 48], by decide +kernel⟩
private def batch13 : PaidBatch .empty 3 := ⟨[
  .point 124 46 48,
  .point 124 47 48,
  .point 124 48 49,
  .point 124 49 49,
  .point 124 50 49,
  .shared 124 51 49 ⟨.tilted, 0, 1, false, 147866079173647548⟩], by decide +kernel⟩
private def batch14 : PaidBatch .empty 3 := ⟨[
  .shared 124 52 49 ⟨.tilted, 1, 1, false, 153126663060781991⟩,
  .point 125 45 48,
  .point 125 46 48,
  .point 125 47 48,
  .point 125 48 49,
  .point 125 49 49], by decide +kernel⟩
private def batch15 : PaidBatch .empty 3 := ⟨[
  .point 125 50 49,
  .shared 125 51 49 ⟨.tilted, 0, 1, false, 149149407101167358⟩,
  .shared 125 52 49 ⟨.tilted, 0, 1, false, 154460458278756800⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 3) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 125 9 17 = true := by decide +kernel
theorem index26 : checks tiles 125 26 17 = true := by decide +kernel
private theorem index43 : checks tiles 125 43 10 = true := by decide +kernel
private theorem covers : checks tiles 125 9 44 = true :=
  checks_join index9 (checks_join index26 index43)

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 125) (hj : a.j ≤ 52) : Covered 3 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

namespace Top4

private def batch0 : PaidBatch .empty 4 := ⟨[
  .rectangle 4 12 64 17 21,
  .rectangle 6 18 125 22 33,
  .rectangle 8 23 66 32 33,
  .rectangle 11 33 68 42 39,
  .rectangle 15 43 68 52 45,
  .rectangle 65 12 125 17 37], by decide +kernel⟩
private def batch1 : PaidBatch .empty 4 := ⟨[
  .rectangle 67 23 125 27 42,
  .rectangle 67 28 125 32 44,
  .rectangle 69 33 97 37 46,
  .rectangle 69 38 97 42 46,
  .rectangle 69 43 97 47 46,
  .rectangle 69 48 97 52 48], by decide +kernel⟩
private def batch2 : PaidBatch .empty 4 := ⟨[
  .rectangle 98 48 104 50 48,
  .rectangle 98 51 104 52 48,
  .rectangle 98 38 111 42 47,
  .rectangle 98 43 111 45 48,
  .rectangle 98 46 111 47 48,
  .rectangle 98 33 125 35 46], by decide +kernel⟩
private def batch3 : PaidBatch .empty 4 := ⟨[
  .rectangle 98 36 125 37 47,
  .rectangle 105 52 108 52 49,
  .rectangle 105 48 111 49 48,
  .rectangle 105 50 111 50 48,
  .rectangle 105 51 111 51 49,
  .rectangle 109 52 110 52 49], by decide +kernel⟩
private def batch4 : PaidBatch .empty 4 := ⟨[
  .point 111 52 49,
  .rectangle 112 51 112 51 49,
  .point 112 52 49,
  .rectangle 112 49 113 49 48,
  .rectangle 112 50 113 50 49,
  .rectangle 112 47 115 47 48], by decide +kernel⟩
private def batch5 : PaidBatch .empty 4 := ⟨[
  .rectangle 112 48 115 48 48,
  .rectangle 112 43 118 44 48,
  .rectangle 112 45 118 45 48,
  .rectangle 112 46 118 46 48,
  .rectangle 112 38 125 40 47,
  .rectangle 112 41 125 42 48], by decide +kernel⟩
private def batch6 : PaidBatch .empty 4 := ⟨[
  .point 113 51 49,
  .point 113 52 49,
  .point 114 49 48,
  .rectangle 114 50 114 50 49,
  .point 114 51 49,
  .point 114 52 49], by decide +kernel⟩
private def batch7 : PaidBatch .empty 4 := ⟨[
  .point 115 49 48,
  .point 115 50 49,
  .point 115 51 49,
  .point 115 52 49,
  .point 116 48 48,
  .rectangle 116 49 116 49 49], by decide +kernel⟩
private def batch8 : PaidBatch .empty 4 := ⟨[
  .point 116 50 49,
  .point 116 51 49,
  .point 116 52 49,
  .rectangle 116 47 117 47 48,
  .point 117 48 48,
  .point 117 49 49], by decide +kernel⟩
private def batch9 : PaidBatch .empty 4 := ⟨[
  .point 117 50 49,
  .point 117 51 49,
  .point 117 52 49,
  .point 118 47 48,
  .point 118 48 48,
  .point 118 49 49], by decide +kernel⟩
private def batch10 : PaidBatch .empty 4 := ⟨[
  .point 118 50 49,
  .point 118 51 49,
  .point 118 52 49,
  .point 119 47 48,
  .point 119 48 48,
  .point 119 49 49], by decide +kernel⟩
private def batch11 : PaidBatch .empty 4 := ⟨[
  .point 119 50 49,
  .point 119 51 49,
  .shared 119 52 49 ⟨.tilted, 1, 1, false, 157548640063165145⟩,
  .rectangle 119 46 120 46 48,
  .rectangle 119 44 122 44 48,
  .rectangle 119 45 122 45 48], by decide +kernel⟩
private def batch12 : PaidBatch .empty 4 := ⟨[
  .rectangle 119 43 125 43 48,
  .point 120 47 48,
  .point 120 48 48,
  .point 120 49 49,
  .point 120 50 49,
  .point 120 51 49], by decide +kernel⟩
private def batch13 : PaidBatch .empty 4 := ⟨[
  .shared 120 52 49 ⟨.tilted, 1, 1, false, 158928245818294074⟩,
  .point 121 46 48,
  .point 121 47 48,
  .point 121 48 48,
  .point 121 49 49,
  .point 121 50 49], by decide +kernel⟩
private def batch14 : PaidBatch .empty 4 := ⟨[
  .shared 121 51 49 ⟨.tilted, 1, 1, false, 154786027462812482⟩,
  .shared 121 52 49 ⟨.tilted, 1, 1, false, 160307851573423003⟩,
  .point 122 46 48,
  .point 122 47 48,
  .point 122 48 49,
  .point 122 49 49], by decide +kernel⟩
private def batch15 : PaidBatch .empty 4 := ⟨[
  .point 122 50 49,
  .shared 122 51 49 ⟨.tilted, 1, 1, false, 156114044036689091⟩,
  .shared 122 52 49 ⟨.tilted, 1, 1, false, 161687457328551932⟩,
  .point 123 45 48,
  .point 123 46 48,
  .point 123 47 48], by decide +kernel⟩
private def batch16 : PaidBatch .empty 4 := ⟨[
  .point 123 48 49,
  .point 123 49 49,
  .shared 123 50 49 ⟨.tilted, 0, 1, false, 151888698895579705⟩,
  .shared 123 51 49 ⟨.tilted, 0, 1, false, 157442060610565700⟩,
  .shared 123 52 49 ⟨.tilted, 1, 1, false, 163067063083680861⟩,
  .rectangle 123 44 124 44 48], by decide +kernel⟩
private def batch17 : PaidBatch .empty 4 := ⟨[
  .point 124 45 48,
  .point 124 46 48,
  .point 124 47 48,
  .point 124 48 49,
  .point 124 49 49,
  .shared 124 50 49 ⟨.tilted, 0, 1, false, 153166087908887412⟩], by decide +kernel⟩
private def batch18 : PaidBatch .empty 4 := ⟨[
  .shared 124 51 49 ⟨.tilted, 0, 1, false, 158770077184442309⟩,
  .shared 124 52 49 ⟨.tilted, 1, 1, false, 164446668838809790⟩,
  .point 125 44 48,
  .point 125 45 48,
  .point 125 46 48,
  .point 125 47 48], by decide +kernel⟩
private def batch19 : PaidBatch .empty 4 := ⟨[
  .point 125 48 49,
  .shared 125 49 49 ⟨.tilted, 0, 1, false, 148863866516592452⟩,
  .shared 125 50 49 ⟨.tilted, 0, 1, false, 154443476922195119⟩,
  .shared 125 51 49 ⟨.tilted, 0, 1, false, 160098093758318918⟩,
  .shared 125 52 49 ⟨.tilted, 0, 1, false, 165826274593938719⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 4) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 125 12 13 = true := by decide +kernel
theorem index25 : checks tiles 125 25 13 = true := by decide +kernel
private theorem index38 : checks tiles 125 38 13 = true := by decide +kernel
private theorem index51 : checks tiles 125 51 2 = true := by decide +kernel
private theorem covers : checks tiles 125 12 41 = true :=
  checks_join index12 (checks_join index25 (checks_join index38 index51))

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 4)
    (hb : a.b ≤ 125) (hj : a.j ≤ 52) : Covered 4 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top4

namespace Top5

private def batch0 : PaidBatch .empty 5 := ⟨[
  .rectangle 5 15 65 24 28,
  .rectangle 9 25 67 33 39,
  .rectangle 12 34 68 43 39,
  .rectangle 15 44 68 52 45,
  .rectangle 66 15 125 19 37,
  .rectangle 66 20 125 24 40], by decide +kernel⟩
private def batch1 : PaidBatch .empty 5 := ⟨[
  .rectangle 68 25 125 29 43,
  .rectangle 68 30 125 33 45,
  .rectangle 69 34 97 38 46,
  .rectangle 69 39 97 43 46,
  .rectangle 69 44 97 48 46,
  .rectangle 69 49 97 52 48], by decide +kernel⟩
private def batch2 : PaidBatch .empty 5 := ⟨[
  .rectangle 98 49 104 50 48,
  .rectangle 98 51 104 51 48,
  .rectangle 98 52 104 52 49,
  .rectangle 98 39 111 43 47,
  .rectangle 98 44 111 46 48,
  .rectangle 98 47 111 48 48], by decide +kernel⟩
private def batch3 : PaidBatch .empty 5 := ⟨[
  .rectangle 98 34 125 36 46,
  .rectangle 98 37 125 38 47,
  .rectangle 105 50 108 50 48,
  .rectangle 105 51 108 51 49,
  .rectangle 105 52 108 52 49,
  .rectangle 105 49 111 49 48], by decide +kernel⟩
private def batch4 : PaidBatch .empty 5 := ⟨[
  .rectangle 109 50 109 50 48,
  .rectangle 109 51 109 51 49,
  .point 109 52 49,
  .point 110 50 48,
  .point 110 51 49,
  .point 110 52 49], by decide +kernel⟩
private def batch5 : PaidBatch .empty 5 := ⟨[
  .rectangle 111 50 111 50 49,
  .point 111 51 49,
  .point 111 52 49,
  .point 112 49 48,
  .point 112 50 49,
  .point 112 51 49], by decide +kernel⟩
private def batch6 : PaidBatch .empty 5 := ⟨[
  .point 112 52 49,
  .rectangle 112 48 113 48 48,
  .rectangle 112 46 115 46 48,
  .rectangle 112 47 115 47 48,
  .rectangle 112 42 118 43 48,
  .rectangle 112 44 118 44 48], by decide +kernel⟩
private def batch7 : PaidBatch .empty 5 := ⟨[
  .rectangle 112 45 118 45 48,
  .rectangle 112 39 125 40 47,
  .rectangle 112 41 125 41 48,
  .point 113 49 48,
  .point 113 50 49,
  .point 113 51 49], by decide +kernel⟩
private def batch8 : PaidBatch .empty 5 := ⟨[
  .point 113 52 49,
  .point 114 48 48,
  .point 114 49 48,
  .point 114 50 49,
  .point 114 51 49,
  .point 114 52 49], by decide +kernel⟩
private def batch9 : PaidBatch .empty 5 := ⟨[
  .point 115 48 48,
  .point 115 49 48,
  .point 115 50 49,
  .point 115 51 49,
  .point 115 52 49,
  .point 116 47 48], by decide +kernel⟩
private def batch10 : PaidBatch .empty 5 := ⟨[
  .point 116 48 48,
  .point 116 49 49,
  .point 116 50 49,
  .point 116 51 49,
  .shared 116 52 49 ⟨.tilted, 1, 2, true, 185953112038074295⟩,
  .rectangle 116 46 117 46 48], by decide +kernel⟩
private def batch11 : PaidBatch .empty 5 := ⟨[
  .point 117 47 48,
  .point 117 48 48,
  .point 117 49 49,
  .point 117 50 49,
  .point 117 51 49,
  .shared 117 52 49 ⟨.tilted, 1, 2, true, 187621999363878486⟩], by decide +kernel⟩
private def batch12 : PaidBatch .empty 5 := ⟨[
  .point 118 46 48,
  .point 118 47 48,
  .point 118 48 48,
  .point 118 49 49,
  .point 118 50 49,
  .shared 118 51 49 ⟨.tilted, 1, 2, true, 182386974893693593⟩], by decide +kernel⟩
private def batch13 : PaidBatch .empty 5 := ⟨[
  .shared 118 52 49 ⟨.tilted, 1, 2, true, 189290886689682678⟩,
  .point 119 46 48,
  .point 119 47 48,
  .point 119 48 48,
  .point 119 49 49,
  .point 119 50 49], by decide +kernel⟩
private def batch14 : PaidBatch .empty 5 := ⟨[
  .shared 119 51 49 ⟨.tilted, 1, 2, true, 183989750786392305⟩,
  .shared 119 52 49 ⟨.tilted, 1, 2, true, 190959774015486870⟩,
  .rectangle 119 45 120 45 48,
  .rectangle 119 44 122 44 48,
  .rectangle 119 42 125 42 48,
  .rectangle 119 43 125 43 48], by decide +kernel⟩
private def batch15 : PaidBatch .empty 5 := ⟨[
  .point 120 46 48,
  .point 120 47 48,
  .point 120 48 48,
  .point 120 49 49,
  .shared 120 50 49 ⟨.tilted, 0, 1, false, 157165210881229422⟩,
  .shared 120 51 49 ⟨.tilted, 1, 2, true, 185592526679091018⟩], by decide +kernel⟩
private def batch16 : PaidBatch .empty 5 := ⟨[
  .shared 120 52 49 ⟨.tilted, 1, 2, true, 192628661341291061⟩,
  .point 121 45 48,
  .point 121 46 48,
  .point 121 47 48,
  .point 121 48 48,
  .point 121 49 49], by decide +kernel⟩
private def batch17 : PaidBatch .empty 5 := ⟨[
  .shared 121 50 49 ⟨.tilted, 0, 2, true, 180193180796657521⟩,
  .shared 121 51 49 ⟨.tilted, 1, 2, true, 187195302571789730⟩,
  .shared 121 52 49 ⟨.tilted, 1, 2, true, 194297548667095253⟩,
  .point 122 45 48,
  .point 122 46 48,
  .point 122 47 48], by decide +kernel⟩
private def batch18 : PaidBatch .empty 5 := ⟨[
  .point 122 48 49,
  .point 122 49 49,
  .shared 122 50 49 ⟨.tilted, 0, 2, true, 181731180840533280⟩,
  .shared 122 51 49 ⟨.tilted, 1, 2, true, 188798078464488443⟩,
  .shared 122 52 49 ⟨.tilted, 1, 2, true, 195966435992899445⟩,
  .point 123 44 48], by decide +kernel⟩
private def batch19 : PaidBatch .empty 5 := ⟨[
  .point 123 45 48,
  .point 123 46 48,
  .point 123 47 48,
  .point 123 48 49,
  .shared 123 49 49 ⟨.tilted, 0, 1, false, 155258797408958892⟩,
  .shared 123 50 49 ⟨.tilted, 0, 2, true, 183269180884409038⟩], by decide +kernel⟩
private def batch20 : PaidBatch .empty 5 := ⟨[
  .shared 123 51 49 ⟨.tilted, 0, 2, true, 190400854357187155⟩,
  .shared 123 52 49 ⟨.tilted, 1, 2, true, 197635323318703636⟩,
  .point 124 44 48,
  .point 124 45 48,
  .point 124 46 48,
  .point 124 47 48], by decide +kernel⟩
private def batch21 : PaidBatch .empty 5 := ⟨[
  .point 124 48 49,
  .shared 124 49 49 ⟨.tilted, 0, 1, false, 156525599674751308⟩,
  .shared 124 50 49 ⟨.tilted, 0, 2, true, 184807180928284796⟩,
  .shared 124 51 49 ⟨.tilted, 0, 2, true, 192003630249885868⟩,
  .shared 124 52 49 ⟨.tilted, 1, 2, true, 199304210644507828⟩,
  .point 125 44 48], by decide +kernel⟩
private def batch22 : PaidBatch .empty 5 := ⟨[
  .point 125 45 48,
  .point 125 46 48,
  .shared 125 47 48 ⟨.tilted, 0, 1, false, 146122587359948357⟩,
  .shared 125 48 49 ⟨.tilted, 0, 1, false, 151915063128982959⟩,
  .shared 125 49 49 ⟨.tilted, 0, 1, false, 157792401940543725⟩,
  .shared 125 50 49 ⟨.tilted, 0, 2, true, 186345180972160555⟩], by decide +kernel⟩
private def batch23 : PaidBatch .empty 5 := ⟨[
  .shared 125 51 49 ⟨.tilted, 0, 2, true, 193606406142584580⟩,
  .shared 125 52 49 ⟨.tilted, 0, 2, true, 200973097970312020⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 5) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 125 15 11 = true := by decide +kernel
theorem index26 : checks tiles 125 26 11 = true := by decide +kernel
theorem index37 : checks tiles 125 37 11 = true := by decide +kernel
private theorem index48 : checks tiles 125 48 5 = true := by decide +kernel
private theorem covers : checks tiles 125 15 38 = true :=
  checks_join index15 (checks_join index26 (checks_join index37 index48))

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 5)
    (hb : a.b ≤ 125) (hj : a.j ≤ 52) : Covered 5 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top5

namespace Top6

private def batch0 : PaidBatch .empty 6 := ⟨[
  .rectangle 6 18 65 26 33,
  .rectangle 9 27 67 35 39,
  .rectangle 12 36 68 44 39,
  .rectangle 15 45 68 52 45,
  .rectangle 66 18 125 22 40,
  .rectangle 66 23 125 26 42], by decide +kernel⟩
private def batch1 : PaidBatch .empty 6 := ⟨[
  .rectangle 68 27 125 31 44,
  .rectangle 68 32 125 35 45,
  .rectangle 69 36 97 40 46,
  .rectangle 69 41 97 44 46,
  .rectangle 69 45 97 48 48,
  .rectangle 69 49 97 52 48], by decide +kernel⟩
private def batch2 : PaidBatch .empty 6 := ⟨[
  .rectangle 98 47 104 48 48,
  .rectangle 98 49 104 50 48,
  .rectangle 98 51 104 51 48,
  .rectangle 98 52 104 52 49,
  .rectangle 98 41 111 42 47,
  .rectangle 98 43 111 44 48], by decide +kernel⟩
private def batch3 : PaidBatch .empty 6 := ⟨[
  .rectangle 98 45 111 46 48,
  .rectangle 98 36 125 38 47,
  .rectangle 98 39 125 40 47,
  .rectangle 105 50 106 50 48,
  .rectangle 105 51 106 51 49,
  .rectangle 105 52 106 52 49], by decide +kernel⟩
private def batch4 : PaidBatch .empty 6 := ⟨[
  .rectangle 105 49 108 49 48,
  .rectangle 105 47 111 47 48,
  .rectangle 105 48 111 48 48,
  .rectangle 107 50 107 50 48,
  .rectangle 107 51 107 51 49,
  .point 107 52 49], by decide +kernel⟩
private def batch5 : PaidBatch .empty 6 := ⟨[
  .point 108 50 48,
  .point 108 51 49,
  .point 108 52 49,
  .rectangle 109 49 109 49 48,
  .point 109 50 48,
  .point 109 51 49], by decide +kernel⟩
private def batch6 : PaidBatch .empty 6 := ⟨[
  .point 109 52 49,
  .point 110 49 48,
  .point 110 50 48,
  .point 110 51 49,
  .point 110 52 49,
  .point 111 49 48], by decide +kernel⟩
private def batch7 : PaidBatch .empty 6 := ⟨[
  .point 111 50 49,
  .point 111 51 49,
  .point 111 52 49,
  .point 112 48 48,
  .point 112 49 48,
  .point 112 50 49], by decide +kernel⟩
private def batch8 : PaidBatch .empty 6 := ⟨[
  .point 112 51 49,
  .point 112 52 49,
  .rectangle 112 47 113 47 48,
  .rectangle 112 46 115 46 48,
  .rectangle 112 41 118 42 48,
  .rectangle 112 43 118 44 48], by decide +kernel⟩
private def batch9 : PaidBatch .empty 6 := ⟨[
  .rectangle 112 45 118 45 48,
  .point 113 48 48,
  .point 113 49 48,
  .point 113 50 49,
  .point 113 51 49,
  .point 113 52 49], by decide +kernel⟩
private def batch10 : PaidBatch .empty 6 := ⟨[
  .point 114 47 48,
  .point 114 48 48,
  .point 114 49 48,
  .point 114 50 49,
  .point 114 51 49,
  .shared 114 52 49 ⟨.tilted, 1, 2, true, 187642134349243807⟩], by decide +kernel⟩
private def batch11 : PaidBatch .empty 6 := ⟨[
  .point 115 47 48,
  .point 115 48 48,
  .point 115 49 48,
  .point 115 50 49,
  .point 115 51 49,
  .shared 115 52 49 ⟨.tilted, 1, 2, true, 189311021675047999⟩], by decide +kernel⟩
private def batch12 : PaidBatch .empty 6 := ⟨[
  .rectangle 116 46 116 46 48,
  .point 116 47 48,
  .point 116 48 48,
  .point 116 49 49,
  .point 116 50 49,
  .shared 116 51 49 ⟨.tilted, 1, 2, true, 183923918724379415⟩], by decide +kernel⟩
private def batch13 : PaidBatch .empty 6 := ⟨[
  .shared 116 52 49 ⟨.tilted, 1, 2, true, 190979909000852190⟩,
  .point 117 46 48,
  .point 117 47 48,
  .point 117 48 48,
  .point 117 49 49,
  .point 117 50 49], by decide +kernel⟩
private def batch14 : PaidBatch .empty 6 := ⟨[
  .shared 117 51 49 ⟨.tilted, 1, 2, true, 185526694617078128⟩,
  .shared 117 52 49 ⟨.tilted, 1, 2, true, 192648796326656382⟩,
  .point 118 46 48,
  .point 118 47 48,
  .point 118 48 48,
  .point 118 49 49], by decide +kernel⟩
private def batch15 : PaidBatch .empty 6 := ⟨[
  .shared 118 50 49 ⟨.tilted, 1, 1, false, 162422500040971908⟩,
  .shared 118 51 49 ⟨.tilted, 1, 2, true, 187129470509776840⟩,
  .shared 118 52 49 ⟨.tilted, 1, 2, true, 194317683652460574⟩,
  .point 119 45 48,
  .point 119 46 48,
  .point 119 47 48], by decide +kernel⟩
private def batch16 : PaidBatch .empty 6 := ⟨[
  .point 119 48 48,
  .point 119 49 49,
  .shared 119 50 49 ⟨.tilted, 1, 1, false, 163776925548222681⟩,
  .shared 119 51 49 ⟨.tilted, 1, 2, true, 188732246402475553⟩,
  .shared 119 52 49 ⟨.tilted, 1, 2, true, 195986570978264765⟩,
  .rectangle 119 44 120 44 48], by decide +kernel⟩
private def batch17 : PaidBatch .empty 6 := ⟨[
  .rectangle 119 43 122 43 48,
  .rectangle 119 41 125 41 48,
  .rectangle 119 42 125 42 48,
  .point 120 45 48,
  .point 120 46 48,
  .point 120 47 48], by decide +kernel⟩
private def batch18 : PaidBatch .empty 6 := ⟨[
  .point 120 48 48,
  .point 120 49 49,
  .shared 120 50 49 ⟨.tilted, 0, 1, false, 165131351055473454⟩,
  .shared 120 51 49 ⟨.tilted, 1, 2, true, 190335022295174265⟩,
  .shared 120 52 49 ⟨.tilted, 1, 2, true, 197655458304068957⟩,
  .rectangle 121 44 121 44 48], by decide +kernel⟩
private def batch19 : PaidBatch .empty 6 := ⟨[
  .point 121 45 48,
  .point 121 46 48,
  .point 121 47 48,
  .shared 121 48 48 ⟨.tilted, 0, 1, false, 154347857613568825⟩,
  .shared 121 49 49 ⟨.tilted, 0, 1, false, 160373544148785453⟩,
  .shared 121 50 49 ⟨.tilted, 0, 2, true, 184659655688597775⟩], by decide +kernel⟩
private def batch20 : PaidBatch .empty 6 := ⟨[
  .shared 121 51 49 ⟨.tilted, 1, 2, true, 191937798187872978⟩,
  .shared 121 52 49 ⟨.tilted, 1, 2, true, 199324345629873149⟩,
  .point 122 44 48,
  .point 122 45 48,
  .point 122 46 48,
  .point 122 47 48], by decide +kernel⟩
private def batch21 : PaidBatch .empty 6 := ⟨[
  .point 122 48 49,
  .shared 122 49 49 ⟨.tilted, 0, 1, false, 161676059934556100⟩,
  .shared 122 50 49 ⟨.tilted, 0, 2, true, 186197655732473534⟩,
  .shared 122 51 49 ⟨.tilted, 1, 2, true, 193540574080571690⟩,
  .shared 122 52 49 ⟨.tilted, 1, 2, true, 200993232955677340⟩,
  .point 123 44 48], by decide +kernel⟩
private def batch22 : PaidBatch .empty 6 := ⟨[
  .point 123 45 48,
  .point 123 46 48,
  .shared 123 47 48 ⟨.tilted, 0, 1, false, 150813321797820769⟩,
  .shared 123 48 49 ⟨.tilted, 0, 1, false, 156850992983516703⟩,
  .shared 123 49 49 ⟨.tilted, 0, 1, false, 162978575720326747⟩,
  .shared 123 50 49 ⟨.tilted, 0, 2, true, 187735655776349292⟩], by decide +kernel⟩
private def batch23 : PaidBatch .empty 6 := ⟨[
  .shared 123 51 49 ⟨.tilted, 0, 2, true, 195143349973270403⟩,
  .shared 123 52 49 ⟨.tilted, 1, 2, true, 202662120281481532⟩,
  .rectangle 123 43 124 43 48,
  .point 124 44 48,
  .point 124 45 48,
  .point 124 46 48], by decide +kernel⟩
private def batch24 : PaidBatch .empty 6 := ⟨[
  .shared 124 47 48 ⟨.tilted, 0, 1, false, 152014903002681418⟩,
  .shared 124 48 49 ⟨.tilted, 0, 1, false, 158102560668490642⟩,
  .shared 124 49 49 ⟨.tilted, 0, 1, false, 164281091506097394⟩,
  .shared 124 50 49 ⟨.tilted, 0, 2, true, 189273655820225050⟩,
  .shared 124 51 49 ⟨.tilted, 0, 2, true, 196746125865969115⟩,
  .shared 124 52 49 ⟨.tilted, 1, 2, true, 204331007607285724⟩], by decide +kernel⟩
private def batch25 : PaidBatch .empty 6 := ⟨[
  .point 125 43 48,
  .point 125 44 48,
  .point 125 45 48,
  .point 125 46 48,
  .shared 125 47 48 ⟨.tilted, 0, 1, false, 153216484207542067⟩,
  .shared 125 48 49 ⟨.tilted, 0, 1, false, 159354128353464581⟩], by decide +kernel⟩
private def batch26 : PaidBatch .empty 6 := ⟨[
  .shared 125 49 49 ⟨.tilted, 0, 1, false, 165583607291868041⟩,
  .shared 125 50 49 ⟨.tilted, 0, 2, true, 190811655864100809⟩,
  .shared 125 51 49 ⟨.tilted, 0, 2, true, 198348901758667828⟩,
  .shared 125 52 49 ⟨.tilted, 0, 2, true, 205999894933089915⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 6) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 125 18 10 = true := by decide +kernel
theorem index28 : checks tiles 125 28 10 = true := by decide +kernel
private theorem index38 : checks tiles 125 38 10 = true := by decide +kernel
private theorem index48 : checks tiles 125 48 5 = true := by decide +kernel
private theorem covers : checks tiles 125 18 35 = true :=
  checks_join index18 (checks_join index28 (checks_join index38 index48))

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 6)
    (hb : a.b ≤ 125) (hj : a.j ≤ 52) : Covered 6 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top6

namespace Top7

private def batch0 : PaidBatch .empty 7 := ⟨[
  .rectangle 7 21 66 28 33,
  .rectangle 10 29 67 36 39,
  .rectangle 13 37 69 44 39,
  .rectangle 15 45 69 52 45,
  .rectangle 67 21 125 24 41,
  .rectangle 67 25 125 28 43], by decide +kernel⟩
private def batch1 : PaidBatch .empty 7 := ⟨[
  .rectangle 68 29 125 32 44,
  .rectangle 68 33 125 36 46,
  .rectangle 70 49 83 52 48,
  .rectangle 70 37 97 40 46,
  .rectangle 70 41 97 44 46,
  .rectangle 70 45 97 48 48], by decide +kernel⟩
private def batch2 : PaidBatch .empty 7 := ⟨[
  .rectangle 84 49 97 50 48,
  .rectangle 84 51 97 52 48,
  .rectangle 98 47 104 48 48,
  .rectangle 98 49 104 49 48,
  .rectangle 98 50 104 50 48,
  .rectangle 98 51 104 51 48], by decide +kernel⟩
private def batch3 : PaidBatch .empty 7 := ⟨[
  .rectangle 98 52 104 52 49,
  .rectangle 98 41 111 42 47,
  .rectangle 98 43 111 44 48,
  .rectangle 98 45 111 46 48,
  .rectangle 98 37 125 38 47,
  .rectangle 98 39 125 40 47], by decide +kernel⟩
private def batch4 : PaidBatch .empty 7 := ⟨[
  .point 105 52 49,
  .rectangle 105 50 106 50 48,
  .rectangle 105 51 106 51 49,
  .rectangle 105 48 108 48 48,
  .rectangle 105 49 108 49 48,
  .rectangle 105 47 111 47 48], by decide +kernel⟩
private def batch5 : PaidBatch .empty 7 := ⟨[
  .point 106 52 49,
  .point 107 50 48,
  .point 107 51 49,
  .point 107 52 49,
  .point 108 50 48,
  .point 108 51 49], by decide +kernel⟩
private def batch6 : PaidBatch .empty 7 := ⟨[
  .point 108 52 49,
  .point 109 49 48,
  .point 109 50 48,
  .point 109 51 49,
  .point 109 52 49,
  .rectangle 109 48 110 48 48], by decide +kernel⟩
private def batch7 : PaidBatch .empty 7 := ⟨[
  .point 110 49 48,
  .point 110 50 48,
  .point 110 51 49,
  .point 110 52 49,
  .point 111 48 48,
  .point 111 49 48], by decide +kernel⟩
private def batch8 : PaidBatch .empty 7 := ⟨[
  .point 111 50 49,
  .point 111 51 49,
  .point 111 52 49,
  .rectangle 112 47 112 47 48,
  .point 112 48 48,
  .point 112 49 48], by decide +kernel⟩
private def batch9 : PaidBatch .empty 7 := ⟨[
  .point 112 50 49,
  .point 112 51 49,
  .shared 112 52 49 ⟨.tilted, 1, 2, true, 188503094487984340⟩,
  .rectangle 112 45 115 45 48,
  .rectangle 112 46 115 46 48,
  .rectangle 112 41 118 42 48], by decide +kernel⟩
private def batch10 : PaidBatch .empty 7 := ⟨[
  .rectangle 112 43 118 43 48,
  .rectangle 112 44 118 44 48,
  .point 113 47 48,
  .point 113 48 48,
  .point 113 49 48,
  .point 113 50 49], by decide +kernel⟩
private def batch11 : PaidBatch .empty 7 := ⟨[
  .point 113 51 49,
  .shared 113 52 49 ⟨.tilted, 1, 2, true, 190171981813788531⟩,
  .point 114 47 48,
  .point 114 48 48,
  .point 114 49 48,
  .point 114 50 49], by decide +kernel⟩
private def batch12 : PaidBatch .empty 7 := ⟨[
  .shared 114 51 49 ⟨.tilted, 1, 2, true, 184657642250291223⟩,
  .shared 114 52 49 ⟨.tilted, 1, 2, true, 191840869139592723⟩,
  .point 115 47 48,
  .point 115 48 48,
  .point 115 49 48,
  .point 115 50 49], by decide +kernel⟩
private def batch13 : PaidBatch .empty 7 := ⟨[
  .shared 115 51 49 ⟨.tilted, 1, 2, true, 186260418142989935⟩,
  .shared 115 52 49 ⟨.tilted, 1, 2, true, 193509756465396915⟩,
  .point 116 46 48,
  .point 116 47 48,
  .point 116 48 48,
  .point 116 49 49], by decide +kernel⟩
private def batch14 : PaidBatch .empty 7 := ⟨[
  .point 116 50 49,
  .shared 116 51 49 ⟨.tilted, 1, 2, true, 187863194035688648⟩,
  .shared 116 52 49 ⟨.tilted, 1, 2, true, 195178643791201106⟩,
  .rectangle 116 45 117 45 48,
  .point 117 46 48,
  .point 117 47 48], by decide +kernel⟩
private def batch15 : PaidBatch .empty 7 := ⟨[
  .point 117 48 48,
  .point 117 49 49,
  .shared 117 50 49 ⟨.tilted, 1, 1, false, 167860743735862549⟩,
  .shared 117 51 49 ⟨.tilted, 1, 2, true, 189465969928387360⟩,
  .shared 117 52 49 ⟨.tilted, 1, 2, true, 196847531117005298⟩,
  .point 118 45 48], by decide +kernel⟩
private def batch16 : PaidBatch .empty 7 := ⟨[
  .point 118 46 48,
  .point 118 47 48,
  .point 118 48 48,
  .point 118 49 49,
  .shared 118 50 49 ⟨.tilted, 1, 1, false, 169248638981496910⟩,
  .shared 118 51 49 ⟨.tilted, 1, 2, true, 191068745821086073⟩], by decide +kernel⟩
private def batch17 : PaidBatch .empty 7 := ⟨[
  .shared 118 52 49 ⟨.tilted, 1, 2, true, 198516418442809490⟩,
  .point 119 45 48,
  .point 119 46 48,
  .point 119 47 48,
  .shared 119 48 48 ⟨.tilted, 0, 1, false, 158050615889780547⟩,
  .shared 119 49 49 ⟨.tilted, 0, 1, false, 164297777864800864⟩], by decide +kernel⟩
private def batch18 : PaidBatch .empty 7 := ⟨[
  .shared 119 50 49 ⟨.tilted, 1, 1, false, 170636534227131272⟩,
  .shared 119 51 49 ⟨.tilted, 1, 2, true, 192671521713784785⟩,
  .shared 119 52 49 ⟨.tilted, 1, 2, true, 200185305768613681⟩,
  .rectangle 119 44 120 44 48,
  .rectangle 119 43 122 43 48,
  .rectangle 119 41 125 41 48], by decide +kernel⟩
private def batch19 : PaidBatch .empty 7 := ⟨[
  .rectangle 119 42 125 42 48,
  .point 120 45 48,
  .point 120 46 48,
  .point 120 47 48,
  .shared 120 48 48 ⟨.tilted, 0, 1, false, 159333409531543433⟩,
  .shared 120 49 49 ⟨.tilted, 0, 1, false, 165632641498157778⟩], by decide +kernel⟩
private def batch20 : PaidBatch .empty 7 := ⟨[
  .shared 120 50 49 ⟨.tilted, 0, 1, false, 172024429472765633⟩,
  .shared 120 51 49 ⟨.tilted, 1, 2, true, 194274297606483498⟩,
  .shared 120 52 49 ⟨.tilted, 1, 2, true, 201854193094417873⟩,
  .point 121 44 48,
  .point 121 45 48,
  .point 121 46 48], by decide +kernel⟩
private def batch21 : PaidBatch .empty 7 := ⟨[
  .point 121 47 48,
  .shared 121 48 48 ⟨.tilted, 0, 1, false, 160616203173306318⟩,
  .shared 121 49 49 ⟨.tilted, 0, 1, false, 166967505131514693⟩,
  .shared 121 50 49 ⟨.tilted, 0, 2, true, 188347752143418980⟩,
  .shared 121 51 49 ⟨.tilted, 1, 2, true, 195877073499182210⟩,
  .shared 121 52 49 ⟨.tilted, 1, 2, true, 203523080420222065⟩], by decide +kernel⟩
private def batch22 : PaidBatch .empty 7 := ⟨[
  .point 122 44 48,
  .point 122 45 48,
  .point 122 46 48,
  .shared 122 47 48 ⟨.tilted, 0, 1, false, 155591546545652272⟩,
  .shared 122 48 49 ⟨.tilted, 0, 1, false, 161898996815069204⟩,
  .shared 122 49 49 ⟨.tilted, 0, 1, false, 168302368764871607⟩], by decide +kernel⟩
private def batch23 : PaidBatch .empty 7 := ⟨[
  .shared 122 50 49 ⟨.tilted, 0, 2, true, 189885752187294738⟩,
  .shared 122 51 49 ⟨.tilted, 1, 2, true, 197479849391880923⟩,
  .shared 122 52 49 ⟨.tilted, 1, 2, true, 205191967746026256⟩,
  .rectangle 123 43 123 43 48,
  .point 123 44 48,
  .point 123 45 48], by decide +kernel⟩
private def batch24 : PaidBatch .empty 7 := ⟨[
  .point 123 46 48,
  .shared 123 47 48 ⟨.tilted, 0, 1, false, 156823231816504546⟩,
  .shared 123 48 49 ⟨.tilted, 0, 1, false, 163181790456832089⟩,
  .shared 123 49 49 ⟨.tilted, 0, 1, false, 169637232398228522⟩,
  .shared 123 50 49 ⟨.tilted, 0, 2, true, 191423752231170496⟩,
  .shared 123 51 49 ⟨.tilted, 0, 2, true, 199082625284579635⟩], by decide +kernel⟩
private def batch25 : PaidBatch .empty 7 := ⟨[
  .shared 123 52 49 ⟨.tilted, 1, 2, true, 206860855071830448⟩,
  .point 124 43 48,
  .point 124 44 48,
  .point 124 45 48,
  .shared 124 46 48 ⟨.tilted, 0, 1, false, 151744537428896102⟩,
  .shared 124 47 48 ⟨.tilted, 0, 1, false, 158054917087356821⟩], by decide +kernel⟩
private def batch26 : PaidBatch .empty 7 := ⟨[
  .shared 124 48 49 ⟨.tilted, 0, 1, false, 164464584098594975⟩,
  .shared 124 49 49 ⟨.tilted, 0, 1, false, 170972096031585436⟩,
  .shared 124 50 49 ⟨.tilted, 0, 2, true, 192961752275046255⟩,
  .shared 124 51 49 ⟨.tilted, 0, 2, true, 200685401177278348⟩,
  .shared 124 52 49 ⟨.tilted, 1, 2, true, 208529742397634640⟩,
  .point 125 43 48], by decide +kernel⟩
private def batch27 : PaidBatch .empty 7 := ⟨[
  .point 125 44 48,
  .point 125 45 48,
  .shared 125 46 48 ⟨.tilted, 0, 1, false, 152926075949521184⟩,
  .shared 125 47 48 ⟨.tilted, 0, 1, false, 159286602358209095⟩,
  .shared 125 48 49 ⟨.tilted, 0, 1, false, 165747377740357860⟩,
  .shared 125 49 49 ⟨.tilted, 0, 1, false, 172306959664942351⟩], by decide +kernel⟩
private def batch28 : PaidBatch .empty 7 := ⟨[
  .shared 125 50 49 ⟨.tilted, 0, 2, true, 194499752318922013⟩,
  .shared 125 51 49 ⟨.tilted, 0, 2, true, 202288177069977060⟩,
  .shared 125 52 49 ⟨.tilted, 0, 2, true, 210198629723438831⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 7) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28]
private abbrev tiles := tilesOf batches

private theorem index21 : checks tiles 125 21 9 = true := by decide +kernel
private theorem index30 : checks tiles 125 30 9 = true := by decide +kernel
private theorem index39 : checks tiles 125 39 9 = true := by decide +kernel
private theorem index48 : checks tiles 125 48 5 = true := by decide +kernel
private theorem covers : checks tiles 125 21 32 = true :=
  checks_join index21 (checks_join index30 (checks_join index39 index48))

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 7)
    (hb : a.b ≤ 125) (hj : a.j ≤ 52) : Covered 7 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top7

end Compact50PriceTableEmpty1
