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
  .rectangle 4 10 64 15 12,
  .rectangle 6 16 65 27 24], by decide +kernel⟩
private def batch1 : PaidBatch .empty 1 := ⟨[
  .rectangle 10 28 67 40 28,
  .rectangle 11 7 18 9 2,
  .rectangle 14 41 67 52 29,
  .rectangle 18 5 32 5 1,
  .rectangle 18 6 32 6 2,
  .rectangle 19 7 33 9 3], by decide +kernel⟩
private def batch2 : PaidBatch .empty 1 := ⟨[
  .rectangle 33 5 63 6 3,
  .rectangle 34 7 64 9 6,
  .rectangle 64 4 125 4 2,
  .rectangle 64 5 125 6 6,
  .rectangle 65 7 125 9 12,
  .rectangle 65 10 125 15 24], by decide +kernel⟩
private def batch3 : PaidBatch .empty 1 := ⟨[
  .rectangle 66 16 125 21 29,
  .rectangle 66 22 125 27 35,
  .rectangle 68 28 96 34 32,
  .rectangle 68 35 96 40 34,
  .rectangle 68 41 96 46 38,
  .rectangle 68 47 96 52 40], by decide +kernel⟩
private def batch4 : PaidBatch .empty 1 := ⟨[
  .rectangle 97 44 111 46 41,
  .rectangle 97 47 111 49 43,
  .rectangle 97 50 111 52 45,
  .rectangle 97 28 125 34 43,
  .rectangle 97 35 125 37 40,
  .rectangle 97 38 125 40 43], by decide +kernel⟩
private def batch5 : PaidBatch .empty 1 := ⟨[
  .rectangle 97 41 125 43 45,
  .rectangle 112 44 118 46 45,
  .rectangle 112 47 118 49 47,
  .rectangle 112 50 118 51 47,
  .rectangle 112 52 118 52 47,
  .rectangle 119 52 120 52 48], by decide +kernel⟩
private def batch6 : PaidBatch .empty 1 := ⟨[
  .rectangle 119 50 122 50 47,
  .rectangle 119 51 122 51 48,
  .rectangle 119 44 125 45 46,
  .rectangle 119 46 125 46 45,
  .rectangle 119 47 125 47 46,
  .rectangle 119 48 125 48 47], by decide +kernel⟩
private def batch7 : PaidBatch .empty 1 := ⟨[
  .rectangle 119 49 125 49 48,
  .rectangle 121 52 121 52 48,
  .point 122 52 31,
  .point 123 51 31,
  .point 123 52 31,
  .rectangle 123 50 124 50 48], by decide +kernel⟩
private def batch8 : PaidBatch .empty 1 := ⟨[
  .point 124 51 31,
  .point 124 52 31,
  .point 125 50 31,
  .point 125 51 31,
  .point 125 52 32], by decide +kernel⟩

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
  .rectangle 3 9 64 11 7,
  .rectangle 4 12 64 17 14,
  .rectangle 6 18 65 29 25,
  .rectangle 10 6 17 7 1,
  .rectangle 10 8 17 8 2], by decide +kernel⟩
private def batch1 : PaidBatch .empty 2 := ⟨[
  .rectangle 10 30 67 41 29,
  .rectangle 14 42 67 52 31,
  .rectangle 18 6 32 8 3,
  .rectangle 33 6 63 8 6,
  .rectangle 64 6 125 8 11,
  .rectangle 65 9 125 11 14], by decide +kernel⟩
private def batch2 : PaidBatch .empty 2 := ⟨[
  .rectangle 65 12 125 17 26,
  .rectangle 66 18 125 23 32,
  .rectangle 66 24 125 29 38,
  .rectangle 68 36 96 41 37,
  .rectangle 68 42 96 47 40,
  .rectangle 68 48 96 52 42], by decide +kernel⟩
private def batch3 : PaidBatch .empty 2 := ⟨[
  .rectangle 68 30 125 35 43,
  .rectangle 97 42 111 44 42,
  .rectangle 97 45 111 47 44,
  .rectangle 97 48 111 50 46,
  .rectangle 97 51 111 52 46,
  .rectangle 97 36 125 38 42], by decide +kernel⟩
private def batch4 : PaidBatch .empty 2 := ⟨[
  .rectangle 97 39 125 41 45,
  .rectangle 112 52 115 52 47,
  .rectangle 112 42 118 44 45,
  .rectangle 112 45 118 47 47,
  .rectangle 112 48 118 48 46,
  .rectangle 112 49 118 49 47], by decide +kernel⟩
private def batch5 : PaidBatch .empty 2 := ⟨[
  .rectangle 112 50 118 50 47,
  .rectangle 112 51 118 51 48,
  .rectangle 116 52 117 52 48,
  .point 118 52 45,
  .point 119 51 45,
  .point 119 52 45], by decide +kernel⟩
private def batch6 : PaidBatch .empty 2 := ⟨[
  .rectangle 119 48 120 48 47,
  .rectangle 119 50 120 50 48,
  .rectangle 119 47 122 47 47,
  .rectangle 119 49 122 49 48,
  .rectangle 119 42 125 43 46,
  .rectangle 119 44 125 44 45], by decide +kernel⟩
private def batch7 : PaidBatch .empty 2 := ⟨[
  .rectangle 119 45 125 45 46,
  .rectangle 119 46 125 46 47,
  .point 120 51 45,
  .point 120 52 46,
  .rectangle 121 48 121 48 47,
  .point 121 50 45], by decide +kernel⟩
private def batch8 : PaidBatch .empty 2 := ⟨[
  .point 121 51 46,
  .point 121 52 46,
  .rectangle 122 48 122 48 48,
  .point 122 50 45,
  .point 122 51 46,
  .point 122 52 47], by decide +kernel⟩
private def batch9 : PaidBatch .empty 2 := ⟨[
  .rectangle 123 47 123 47 47,
  .point 123 49 45,
  .point 123 50 46,
  .point 123 51 46,
  .point 123 52 47,
  .rectangle 123 48 124 48 48], by decide +kernel⟩
private def batch10 : PaidBatch .empty 2 := ⟨[
  .point 124 47 44,
  .point 124 49 45,
  .point 124 50 46,
  .point 124 51 47,
  .point 124 52 48,
  .point 125 47 44], by decide +kernel⟩
private def batch11 : PaidBatch .empty 2 := ⟨[
  .point 125 48 45,
  .point 125 49 46,
  .point 125 50 47,
  .point 125 51 47,
  .point 125 52 48], by decide +kernel⟩

private def batches : List (PaidBatch .empty 2) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 125 6 22 = true := by decide +kernel
private theorem index28 : checks tiles 125 28 22 = true := by decide +kernel
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
  .rectangle 3 9 33 14 7,
  .rectangle 5 15 125 19 26,
  .rectangle 7 20 66 30 26,
  .rectangle 11 31 68 41 31,
  .rectangle 14 42 68 52 34,
  .rectangle 34 9 64 14 12], by decide +kernel⟩
private def batch1 : PaidBatch .empty 3 := ⟨[
  .rectangle 65 9 125 14 23,
  .rectangle 67 20 125 25 34,
  .rectangle 67 26 125 30 38,
  .rectangle 69 31 97 36 35,
  .rectangle 69 37 97 41 37,
  .rectangle 69 42 97 47 42], by decide +kernel⟩
private def batch2 : PaidBatch .empty 3 := ⟨[
  .rectangle 69 48 97 52 44,
  .rectangle 98 48 104 50 44,
  .rectangle 98 51 104 52 45,
  .rectangle 98 37 111 41 43,
  .rectangle 98 42 111 44 43,
  .rectangle 98 45 111 47 45], by decide +kernel⟩
private def batch3 : PaidBatch .empty 3 := ⟨[
  .rectangle 98 31 125 36 45,
  .rectangle 105 48 111 49 46,
  .rectangle 105 50 111 50 46,
  .rectangle 105 51 111 52 48,
  .rectangle 112 52 113 52 48,
  .rectangle 112 49 115 49 47], by decide +kernel⟩
private def batch4 : PaidBatch .empty 3 := ⟨[
  .rectangle 112 50 115 50 48,
  .rectangle 112 51 115 51 48,
  .rectangle 112 42 118 44 46,
  .rectangle 112 45 118 46 47,
  .rectangle 112 47 118 47 46,
  .rectangle 112 48 118 48 47], by decide +kernel⟩
private def batch5 : PaidBatch .empty 3 := ⟨[
  .rectangle 112 37 125 39 44,
  .rectangle 112 40 125 41 45,
  .point 114 52 45,
  .point 115 52 45,
  .point 116 51 45,
  .point 116 52 46], by decide +kernel⟩
private def batch6 : PaidBatch .empty 3 := ⟨[
  .rectangle 116 50 117 50 48,
  .rectangle 116 49 118 49 48,
  .point 117 51 46,
  .point 117 52 46,
  .point 118 50 45,
  .point 118 51 46], by decide +kernel⟩
private def batch7 : PaidBatch .empty 3 := ⟨[
  .point 118 52 47,
  .point 119 48 44,
  .point 119 49 45,
  .point 119 50 46,
  .point 119 51 46,
  .point 119 52 47], by decide +kernel⟩
private def batch8 : PaidBatch .empty 3 := ⟨[
  .rectangle 119 47 120 47 47,
  .rectangle 119 45 122 45 46,
  .rectangle 119 46 122 46 47,
  .rectangle 119 42 125 43 47,
  .rectangle 119 44 125 44 47,
  .point 120 48 44], by decide +kernel⟩
private def batch9 : PaidBatch .empty 3 := ⟨[
  .point 120 49 45,
  .point 120 50 46,
  .point 120 51 47,
  .point 120 52 48,
  .point 121 47 44,
  .point 121 48 45], by decide +kernel⟩
private def batch10 : PaidBatch .empty 3 := ⟨[
  .point 121 49 46,
  .point 121 50 46,
  .point 121 51 47,
  .point 121 52 48,
  .point 122 47 44,
  .point 122 48 45], by decide +kernel⟩
private def batch11 : PaidBatch .empty 3 := ⟨[
  .point 122 49 46,
  .point 122 50 47,
  .point 122 51 48,
  .shared 122 52 48 ⟨.tilted, 1, 1, false, 150519963318229627⟩,
  .point 123 46 44,
  .point 123 47 45], by decide +kernel⟩
private def batch12 : PaidBatch .empty 3 := ⟨[
  .point 123 48 46,
  .point 123 49 46,
  .point 123 50 47,
  .point 123 51 48,
  .shared 123 52 48 ⟨.tilted, 1, 1, false, 151854298322345752⟩,
  .rectangle 123 45 124 45 47], by decide +kernel⟩
private def batch13 : PaidBatch .empty 3 := ⟨[
  .point 124 46 44,
  .point 124 47 45,
  .point 124 48 46,
  .point 124 49 47,
  .point 124 50 48,
  .shared 124 51 48 ⟨.tilted, 0, 1, false, 147925920484094605⟩], by decide +kernel⟩
private def batch14 : PaidBatch .empty 3 := ⟨[
  .shared 124 52 48 ⟨.tilted, 1, 1, false, 153188633326461878⟩,
  .point 125 45 44,
  .point 125 46 45,
  .point 125 47 46,
  .point 125 48 46,
  .point 125 49 47], by decide +kernel⟩
private def batch15 : PaidBatch .empty 3 := ⟨[
  .point 125 50 48,
  .shared 125 51 48 ⟨.tilted, 0, 1, false, 149209767773670694⟩,
  .shared 125 52 48 ⟨.tilted, 0, 1, false, 154522968330578003⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 3) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 125 9 17 = true := by decide +kernel
private theorem index26 : checks tiles 125 26 17 = true := by decide +kernel
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
  .rectangle 4 12 64 17 14,
  .rectangle 6 18 125 22 30,
  .rectangle 8 23 66 32 26,
  .rectangle 11 33 68 42 31,
  .rectangle 15 43 68 52 35,
  .rectangle 65 12 125 17 26], by decide +kernel⟩
private def batch1 : PaidBatch .empty 4 := ⟨[
  .rectangle 67 23 125 27 35,
  .rectangle 67 28 125 32 40,
  .rectangle 69 33 97 37 35,
  .rectangle 69 38 97 42 39,
  .rectangle 69 43 97 47 42,
  .rectangle 69 48 97 52 46], by decide +kernel⟩
private def batch2 : PaidBatch .empty 4 := ⟨[
  .rectangle 98 48 104 50 46,
  .rectangle 98 51 104 52 46,
  .rectangle 98 38 111 42 45,
  .rectangle 98 43 111 45 45,
  .rectangle 98 46 111 47 46,
  .rectangle 98 33 125 35 41], by decide +kernel⟩
private def batch3 : PaidBatch .empty 4 := ⟨[
  .rectangle 98 36 125 37 42,
  .rectangle 105 52 108 52 47,
  .rectangle 105 48 111 49 47,
  .rectangle 105 50 111 50 47,
  .rectangle 105 51 111 51 48,
  .rectangle 109 52 110 52 48], by decide +kernel⟩
private def batch4 : PaidBatch .empty 4 := ⟨[
  .point 111 52 45,
  .rectangle 112 51 112 51 48,
  .point 112 52 46,
  .rectangle 112 49 113 49 47,
  .rectangle 112 50 113 50 48,
  .rectangle 112 47 115 47 46], by decide +kernel⟩
private def batch5 : PaidBatch .empty 4 := ⟨[
  .rectangle 112 48 115 48 47,
  .rectangle 112 43 118 44 46,
  .rectangle 112 45 118 45 46,
  .rectangle 112 46 118 46 47,
  .rectangle 112 38 125 40 46,
  .rectangle 112 41 125 42 47], by decide +kernel⟩
private def batch6 : PaidBatch .empty 4 := ⟨[
  .point 113 51 45,
  .point 113 52 46,
  .point 114 49 44,
  .rectangle 114 50 114 50 48,
  .point 114 51 46,
  .point 114 52 46], by decide +kernel⟩
private def batch7 : PaidBatch .empty 4 := ⟨[
  .point 115 49 45,
  .point 115 50 45,
  .point 115 51 46,
  .point 115 52 47,
  .point 116 48 44,
  .rectangle 116 49 116 49 48], by decide +kernel⟩
private def batch8 : PaidBatch .empty 4 := ⟨[
  .point 116 50 46,
  .point 116 51 47,
  .point 116 52 47,
  .rectangle 116 47 117 47 47,
  .point 117 48 44,
  .point 117 49 45], by decide +kernel⟩
private def batch9 : PaidBatch .empty 4 := ⟨[
  .point 117 50 46,
  .point 117 51 47,
  .point 117 52 48,
  .point 118 47 44,
  .point 118 48 45,
  .point 118 49 46], by decide +kernel⟩
private def batch10 : PaidBatch .empty 4 := ⟨[
  .point 118 50 47,
  .point 118 51 47,
  .point 118 52 48,
  .point 119 47 44,
  .point 119 48 45,
  .point 119 49 46], by decide +kernel⟩
private def batch11 : PaidBatch .empty 4 := ⟨[
  .point 119 50 47,
  .point 119 51 48,
  .shared 119 52 48 ⟨.tilted, 1, 1, false, 157612399901675675⟩,
  .rectangle 119 46 120 46 47,
  .rectangle 119 44 122 44 46,
  .rectangle 119 45 122 45 47], by decide +kernel⟩
private def batch12 : PaidBatch .empty 4 := ⟨[
  .rectangle 119 43 125 43 47,
  .point 120 47 45,
  .point 120 48 46,
  .point 120 49 47,
  .point 120 50 47,
  .point 120 51 48], by decide +kernel⟩
private def batch13 : PaidBatch .empty 4 := ⟨[
  .shared 120 52 48 ⟨.tilted, 1, 1, false, 158992563982448454⟩,
  .point 121 46 44,
  .point 121 47 45,
  .point 121 48 46,
  .point 121 49 47,
  .point 121 50 48], by decide +kernel⟩
private def batch14 : PaidBatch .empty 4 := ⟨[
  .shared 121 51 48 ⟨.tilted, 1, 1, false, 154848669273575784⟩,
  .shared 121 52 48 ⟨.tilted, 1, 1, false, 160372728063221233⟩,
  .point 122 46 45,
  .point 122 47 46,
  .point 122 48 46,
  .point 122 49 47], by decide +kernel⟩
private def batch15 : PaidBatch .empty 4 := ⟨[
  .point 122 50 48,
  .shared 122 51 48 ⟨.tilted, 1, 1, false, 156177223294982553⟩,
  .shared 122 52 48 ⟨.tilted, 1, 1, false, 161752892143994012⟩,
  .point 123 45 44,
  .point 123 46 45,
  .point 123 47 46], by decide +kernel⟩
private def batch16 : PaidBatch .empty 4 := ⟨[
  .point 123 48 47,
  .point 123 49 48,
  .shared 123 50 48 ⟨.tilted, 0, 1, false, 151950168159116995⟩,
  .shared 123 51 48 ⟨.tilted, 0, 1, false, 157505777316389322⟩,
  .shared 123 52 48 ⟨.tilted, 1, 1, false, 163133056224766791⟩,
  .rectangle 123 44 124 44 47], by decide +kernel⟩
private def batch17 : PaidBatch .empty 4 := ⟨[
  .point 124 45 45,
  .point 124 46 45,
  .point 124 47 46,
  .point 124 48 47,
  .point 124 49 48,
  .shared 124 50 48 ⟨.tilted, 0, 1, false, 153228074131008588⟩], by decide +kernel⟩
private def batch18 : PaidBatch .empty 4 := ⟨[
  .shared 124 51 48 ⟨.tilted, 0, 1, false, 158834331337796091⟩,
  .shared 124 52 48 ⟨.tilted, 1, 1, false, 164513220305539570⟩,
  .point 125 44 44,
  .point 125 45 45,
  .point 125 46 46,
  .point 125 47 47], by decide +kernel⟩
private def batch19 : PaidBatch .empty 4 := ⟨[
  .point 125 48 48,
  .shared 125 49 48 ⟨.tilted, 0, 1, false, 148924111632180564⟩,
  .shared 125 50 48 ⟨.tilted, 0, 1, false, 154505980102900181⟩,
  .shared 125 51 48 ⟨.tilted, 0, 1, false, 160162885359202860⟩,
  .shared 125 52 48 ⟨.tilted, 0, 1, false, 165893384386312349⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 4) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19]
private abbrev tiles := tilesOf batches

private theorem index12 : checks tiles 125 12 13 = true := by decide +kernel
private theorem index25 : checks tiles 125 25 13 = true := by decide +kernel
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
  .rectangle 5 15 65 24 23,
  .rectangle 9 25 67 33 27,
  .rectangle 12 34 68 43 33,
  .rectangle 15 44 68 52 36,
  .rectangle 66 15 125 19 26,
  .rectangle 66 20 125 24 32], by decide +kernel⟩
private def batch1 : PaidBatch .empty 5 := ⟨[
  .rectangle 68 25 125 29 37,
  .rectangle 68 30 125 33 40,
  .rectangle 69 34 97 38 37,
  .rectangle 69 39 97 43 41,
  .rectangle 69 44 97 48 44,
  .rectangle 69 49 97 52 46], by decide +kernel⟩
private def batch2 : PaidBatch .empty 5 := ⟨[
  .rectangle 98 49 104 50 46,
  .rectangle 98 51 104 51 46,
  .rectangle 98 52 104 52 47,
  .rectangle 98 39 111 43 46,
  .rectangle 98 44 111 46 47,
  .rectangle 98 47 111 48 47], by decide +kernel⟩
private def batch3 : PaidBatch .empty 5 := ⟨[
  .rectangle 98 34 125 36 42,
  .rectangle 98 37 125 38 43,
  .rectangle 105 50 108 50 47,
  .rectangle 105 51 108 51 48,
  .rectangle 105 52 108 52 48,
  .rectangle 105 49 111 49 47], by decide +kernel⟩
private def batch4 : PaidBatch .empty 5 := ⟨[
  .rectangle 109 50 109 50 47,
  .rectangle 109 51 109 51 48,
  .point 109 52 46,
  .point 110 50 44,
  .point 110 51 45,
  .point 110 52 46], by decide +kernel⟩
private def batch5 : PaidBatch .empty 5 := ⟨[
  .rectangle 111 50 111 50 48,
  .point 111 51 46,
  .point 111 52 46,
  .point 112 49 44,
  .point 112 50 45,
  .point 112 51 46], by decide +kernel⟩
private def batch6 : PaidBatch .empty 5 := ⟨[
  .point 112 52 47,
  .rectangle 112 48 113 48 47,
  .rectangle 112 46 115 46 46,
  .rectangle 112 47 115 47 47,
  .rectangle 112 42 118 43 46,
  .rectangle 112 44 118 44 46], by decide +kernel⟩
private def batch7 : PaidBatch .empty 5 := ⟨[
  .rectangle 112 45 118 45 47,
  .rectangle 112 39 125 40 45,
  .rectangle 112 41 125 41 45,
  .point 113 49 45,
  .point 113 50 46,
  .point 113 51 46], by decide +kernel⟩
private def batch8 : PaidBatch .empty 5 := ⟨[
  .point 113 52 47,
  .point 114 48 44,
  .point 114 49 45,
  .point 114 50 46,
  .point 114 51 47,
  .point 114 52 48], by decide +kernel⟩
private def batch9 : PaidBatch .empty 5 := ⟨[
  .point 115 48 45,
  .point 115 49 46,
  .point 115 50 46,
  .point 115 51 47,
  .point 115 52 48,
  .point 116 47 44], by decide +kernel⟩
private def batch10 : PaidBatch .empty 5 := ⟨[
  .point 116 48 45,
  .point 116 49 46,
  .point 116 50 47,
  .point 116 51 48,
  .shared 116 52 48 ⟨.tilted, 1, 2, true, 186028367153871295⟩,
  .rectangle 116 46 117 46 47], by decide +kernel⟩
private def batch11 : PaidBatch .empty 5 := ⟨[
  .point 117 47 45,
  .point 117 48 46,
  .point 117 49 46,
  .point 117 50 47,
  .point 117 51 48,
  .shared 117 52 48 ⟨.tilted, 1, 2, true, 187697929877438136⟩], by decide +kernel⟩
private def batch12 : PaidBatch .empty 5 := ⟨[
  .point 118 46 44,
  .point 118 47 45,
  .point 118 48 46,
  .point 118 49 47,
  .point 118 50 48,
  .shared 118 51 48 ⟨.tilted, 1, 2, true, 182460786795744830⟩], by decide +kernel⟩
private def batch13 : PaidBatch .empty 5 := ⟨[
  .shared 118 52 48 ⟨.tilted, 1, 2, true, 189367492601004978⟩,
  .point 119 46 44,
  .point 119 47 45,
  .point 119 48 46,
  .point 119 49 47,
  .point 119 50 48], by decide +kernel⟩
private def batch14 : PaidBatch .empty 5 := ⟨[
  .shared 119 51 48 ⟨.tilted, 1, 2, true, 184064211330944093⟩,
  .shared 119 52 48 ⟨.tilted, 1, 2, true, 191037055324571820⟩,
  .rectangle 119 45 120 45 47,
  .rectangle 119 44 122 44 47,
  .rectangle 119 42 125 42 46,
  .rectangle 119 43 125 43 47], by decide +kernel⟩
private def batch15 : PaidBatch .empty 5 := ⟨[
  .point 120 46 45,
  .point 120 47 46,
  .point 120 48 47,
  .point 120 49 48,
  .shared 120 50 48 ⟨.tilted, 0, 1, false, 157228815547190397⟩,
  .shared 120 51 48 ⟨.tilted, 1, 2, true, 185667635866143355⟩], by decide +kernel⟩
private def batch16 : PaidBatch .empty 5 := ⟨[
  .shared 120 52 48 ⟨.tilted, 1, 2, true, 192706618048138661⟩,
  .point 121 45 44,
  .point 121 46 45,
  .point 121 47 46,
  .point 121 48 47,
  .point 121 49 48], by decide +kernel⟩
private def batch17 : PaidBatch .empty 5 := ⟨[
  .shared 121 50 48 ⟨.tilted, 0, 2, true, 180266104871412271⟩,
  .shared 121 51 48 ⟨.tilted, 1, 2, true, 187271060401342618⟩,
  .shared 121 52 48 ⟨.tilted, 1, 2, true, 194376180771705503⟩,
  .point 122 45 45,
  .point 122 46 46,
  .point 122 47 47], by decide +kernel⟩
private def batch18 : PaidBatch .empty 5 := ⟨[
  .point 122 48 47,
  .point 122 49 48,
  .shared 122 50 48 ⟨.tilted, 0, 2, true, 181804727343036780⟩,
  .shared 122 51 48 ⟨.tilted, 1, 2, true, 188874484936541880⟩,
  .shared 122 52 48 ⟨.tilted, 1, 2, true, 196045743495272345⟩,
  .point 123 44 44], by decide +kernel⟩
private def batch19 : PaidBatch .empty 5 := ⟨[
  .point 123 45 45,
  .point 123 46 46,
  .point 123 47 47,
  .point 123 48 48,
  .shared 123 49 48 ⟨.tilted, 0, 1, false, 155321630550423079⟩,
  .shared 123 50 48 ⟨.tilted, 0, 2, true, 183343349814661288⟩], by decide +kernel⟩
private def batch20 : PaidBatch .empty 5 := ⟨[
  .shared 123 51 48 ⟨.tilted, 0, 2, true, 190477909471741143⟩,
  .shared 123 52 48 ⟨.tilted, 1, 2, true, 197715306218839186⟩,
  .point 124 44 44,
  .point 124 45 45,
  .point 124 46 46,
  .point 124 47 47], by decide +kernel⟩
private def batch21 : PaidBatch .empty 5 := ⟨[
  .point 124 48 48,
  .shared 124 49 48 ⟨.tilted, 0, 1, false, 156588945490351146⟩,
  .shared 124 50 48 ⟨.tilted, 0, 2, true, 184881972286285796⟩,
  .shared 124 51 48 ⟨.tilted, 0, 2, true, 192081334006940405⟩,
  .shared 124 52 48 ⟨.tilted, 1, 2, true, 199384868942406028⟩,
  .point 125 44 45], by decide +kernel⟩
private def batch22 : PaidBatch .empty 5 := ⟨[
  .point 125 45 46,
  .point 125 46 47,
  .shared 125 47 47 ⟨.tilted, 0, 1, false, 146181723082382857⟩,
  .shared 125 48 48 ⟨.tilted, 0, 1, false, 151976543063053980⟩,
  .shared 125 49 48 ⟨.tilted, 0, 1, false, 157856260430279212⟩,
  .shared 125 50 48 ⟨.tilted, 0, 2, true, 186420594757910305⟩], by decide +kernel⟩
private def batch23 : PaidBatch .empty 5 := ⟨[
  .shared 125 51 48 ⟨.tilted, 0, 2, true, 193684758542139668⟩,
  .shared 125 52 48 ⟨.tilted, 0, 2, true, 201054431665972870⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 5) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23]
private abbrev tiles := tilesOf batches

private theorem index15 : checks tiles 125 15 11 = true := by decide +kernel
private theorem index26 : checks tiles 125 26 11 = true := by decide +kernel
private theorem index37 : checks tiles 125 37 11 = true := by decide +kernel
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
  .rectangle 6 18 65 26 22,
  .rectangle 9 27 67 35 28,
  .rectangle 12 36 68 44 33,
  .rectangle 15 45 68 52 36,
  .rectangle 66 18 125 22 29,
  .rectangle 66 23 125 26 32], by decide +kernel⟩
private def batch1 : PaidBatch .empty 6 := ⟨[
  .rectangle 68 27 125 31 40,
  .rectangle 68 32 125 35 43,
  .rectangle 69 36 97 40 39,
  .rectangle 69 41 97 44 41,
  .rectangle 69 45 97 48 44,
  .rectangle 69 49 97 52 47], by decide +kernel⟩
private def batch2 : PaidBatch .empty 6 := ⟨[
  .rectangle 98 47 104 48 45,
  .rectangle 98 49 104 50 47,
  .rectangle 98 51 104 51 47,
  .rectangle 98 52 104 52 48,
  .rectangle 98 41 111 42 43,
  .rectangle 98 43 111 44 45], by decide +kernel⟩
private def batch3 : PaidBatch .empty 6 := ⟨[
  .rectangle 98 45 111 46 46,
  .rectangle 98 36 125 38 45,
  .rectangle 98 39 125 40 46,
  .rectangle 105 50 106 50 47,
  .rectangle 105 51 106 51 48,
  .rectangle 105 52 106 52 48], by decide +kernel⟩
private def batch4 : PaidBatch .empty 6 := ⟨[
  .rectangle 105 49 108 49 47,
  .rectangle 105 47 111 47 46,
  .rectangle 105 48 111 48 47,
  .rectangle 107 50 107 50 47,
  .rectangle 107 51 107 51 48,
  .point 107 52 46], by decide +kernel⟩
private def batch5 : PaidBatch .empty 6 := ⟨[
  .point 108 50 44,
  .point 108 51 45,
  .point 108 52 46,
  .rectangle 109 49 109 49 47,
  .point 109 50 45,
  .point 109 51 46], by decide +kernel⟩
private def batch6 : PaidBatch .empty 6 := ⟨[
  .point 109 52 47,
  .point 110 49 44,
  .point 110 50 45,
  .point 110 51 46,
  .point 110 52 47,
  .point 111 49 45], by decide +kernel⟩
private def batch7 : PaidBatch .empty 6 := ⟨[
  .point 111 50 46,
  .point 111 51 47,
  .point 111 52 47,
  .point 112 48 44,
  .point 112 49 45,
  .point 112 50 46], by decide +kernel⟩
private def batch8 : PaidBatch .empty 6 := ⟨[
  .point 112 51 47,
  .point 112 52 48,
  .rectangle 112 47 113 47 47,
  .rectangle 112 46 115 46 47,
  .rectangle 112 41 118 42 45,
  .rectangle 112 43 118 44 47], by decide +kernel⟩
private def batch9 : PaidBatch .empty 6 := ⟨[
  .rectangle 112 45 118 45 47,
  .point 113 48 45,
  .point 113 49 46,
  .point 113 50 47,
  .point 113 51 47,
  .point 113 52 48], by decide +kernel⟩
private def batch10 : PaidBatch .empty 6 := ⟨[
  .point 114 47 44,
  .point 114 48 45,
  .point 114 49 46,
  .point 114 50 47,
  .point 114 51 48,
  .shared 114 52 48 ⟨.tilted, 1, 2, true, 187718073011959927⟩], by decide +kernel⟩
private def batch11 : PaidBatch .empty 6 := ⟨[
  .point 115 47 45,
  .point 115 48 46,
  .point 115 49 46,
  .point 115 50 47,
  .point 115 51 48,
  .shared 115 52 48 ⟨.tilted, 1, 2, true, 189387635735526769⟩], by decide +kernel⟩
private def batch12 : PaidBatch .empty 6 := ⟨[
  .rectangle 116 46 116 46 47,
  .point 116 47 45,
  .point 116 48 46,
  .point 116 49 47,
  .point 116 50 48,
  .shared 116 51 48 ⟨.tilted, 1, 2, true, 183998352627253693⟩], by decide +kernel⟩
private def batch13 : PaidBatch .empty 6 := ⟨[
  .shared 116 52 48 ⟨.tilted, 1, 2, true, 191057198459093610⟩,
  .point 117 46 44,
  .point 117 47 45,
  .point 117 48 46,
  .point 117 49 47,
  .point 117 50 48], by decide +kernel⟩
private def batch14 : PaidBatch .empty 6 := ⟨[
  .shared 117 51 48 ⟨.tilted, 1, 2, true, 185601777162452955⟩,
  .shared 117 52 48 ⟨.tilted, 1, 2, true, 192726761182660452⟩,
  .point 118 46 45,
  .point 118 47 46,
  .point 118 48 47,
  .point 118 49 48], by decide +kernel⟩
private def batch15 : PaidBatch .empty 6 := ⟨[
  .shared 118 50 48 ⟨.tilted, 1, 1, false, 162488232329750016⟩,
  .shared 118 51 48 ⟨.tilted, 1, 2, true, 187205201697652218⟩,
  .shared 118 52 48 ⟨.tilted, 1, 2, true, 194396323906227294⟩,
  .point 119 45 44,
  .point 119 46 45,
  .point 119 47 46], by decide +kernel⟩
private def batch16 : PaidBatch .empty 6 := ⟨[
  .point 119 48 47,
  .point 119 49 48,
  .shared 119 50 48 ⟨.tilted, 1, 1, false, 163843205972217267⟩,
  .shared 119 51 48 ⟨.tilted, 1, 2, true, 188808626232851480⟩,
  .shared 119 52 48 ⟨.tilted, 1, 2, true, 196065886629794135⟩,
  .rectangle 119 44 120 44 47], by decide +kernel⟩
private def batch17 : PaidBatch .empty 6 := ⟨[
  .rectangle 119 43 122 43 47,
  .rectangle 119 41 125 41 46,
  .rectangle 119 42 125 42 47,
  .point 120 45 45,
  .point 120 46 46,
  .point 120 47 47], by decide +kernel⟩
private def batch18 : PaidBatch .empty 6 := ⟨[
  .point 120 48 47,
  .point 120 49 48,
  .shared 120 50 48 ⟨.tilted, 0, 1, false, 165198179614684518⟩,
  .shared 120 51 48 ⟨.tilted, 1, 2, true, 190412050768050743⟩,
  .shared 120 52 48 ⟨.tilted, 1, 2, true, 197735449353360977⟩,
  .rectangle 121 44 121 44 47], by decide +kernel⟩
private def batch19 : PaidBatch .empty 6 := ⟨[
  .point 121 45 45,
  .point 121 46 46,
  .point 121 47 47,
  .shared 121 48 47 ⟨.tilted, 0, 1, false, 154410322099065235⟩,
  .shared 121 49 48 ⟨.tilted, 0, 1, false, 160438447226211968⟩,
  .shared 121 50 48 ⟨.tilted, 0, 2, true, 184734387343720245⟩], by decide +kernel⟩
private def batch20 : PaidBatch .empty 6 := ⟨[
  .shared 121 51 48 ⟨.tilted, 1, 2, true, 192015475303250005⟩,
  .shared 121 52 48 ⟨.tilted, 1, 2, true, 199405012076927819⟩,
  .point 122 44 44,
  .point 122 45 45,
  .point 122 46 46,
  .point 122 47 47], by decide +kernel⟩
private def batch21 : PaidBatch .empty 6 := ⟨[
  .point 122 48 48,
  .shared 122 49 48 ⟨.tilted, 0, 1, false, 161741490139362931⟩,
  .shared 122 50 48 ⟨.tilted, 0, 2, true, 186273009815344754⟩,
  .shared 122 51 48 ⟨.tilted, 1, 2, true, 193618899838449268⟩,
  .shared 122 52 48 ⟨.tilted, 1, 2, true, 201074574800494660⟩,
  .point 123 44 45], by decide +kernel⟩
private def batch22 : PaidBatch .empty 6 := ⟨[
  .point 123 45 46,
  .point 123 46 47,
  .shared 123 47 47 ⟨.tilted, 0, 1, false, 150874355858629602⟩,
  .shared 123 48 48 ⟨.tilted, 0, 1, false, 156914470486436253⟩,
  .shared 123 49 48 ⟨.tilted, 0, 1, false, 163044533052513894⟩,
  .shared 123 50 48 ⟨.tilted, 0, 2, true, 187811632286969262⟩], by decide +kernel⟩
private def batch23 : PaidBatch .empty 6 := ⟨[
  .shared 123 51 48 ⟨.tilted, 0, 2, true, 195222324373648530⟩,
  .shared 123 52 48 ⟨.tilted, 1, 2, true, 202744137524061502⟩,
  .rectangle 123 43 124 43 47,
  .point 124 44 45,
  .point 124 45 46,
  .point 124 46 47], by decide +kernel⟩
private def batch24 : PaidBatch .empty 6 := ⟨[
  .shared 124 47 47 ⟨.tilted, 0, 1, false, 152076423342700491⟩,
  .shared 124 48 48 ⟨.tilted, 0, 1, false, 158166544680121762⟩,
  .shared 124 49 48 ⟨.tilted, 0, 1, false, 164347575965664857⟩,
  .shared 124 50 48 ⟨.tilted, 0, 2, true, 189350254758593770⟩,
  .shared 124 51 48 ⟨.tilted, 0, 2, true, 196825748908847793⟩,
  .shared 124 52 48 ⟨.tilted, 1, 2, true, 204413700247628344⟩], by decide +kernel⟩
private def batch25 : PaidBatch .empty 6 := ⟨[
  .point 125 43 44,
  .point 125 44 45,
  .point 125 45 46,
  .point 125 46 47,
  .shared 125 47 47 ⟨.tilted, 0, 1, false, 153278490826771380⟩,
  .shared 125 48 48 ⟨.tilted, 0, 1, false, 159418618873807271⟩], by decide +kernel⟩
private def batch26 : PaidBatch .empty 6 := ⟨[
  .shared 125 49 48 ⟨.tilted, 0, 1, false, 165650618878815820⟩,
  .shared 125 50 48 ⟨.tilted, 0, 2, true, 190888877230218279⟩,
  .shared 125 51 48 ⟨.tilted, 0, 2, true, 198429173444047055⟩,
  .shared 125 52 48 ⟨.tilted, 0, 2, true, 206083262971195185⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 6) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26]
private abbrev tiles := tilesOf batches

private theorem index18 : checks tiles 125 18 10 = true := by decide +kernel
private theorem index28 : checks tiles 125 28 10 = true := by decide +kernel
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
  .rectangle 7 21 66 28 23,
  .rectangle 10 29 67 36 28,
  .rectangle 13 37 69 44 33,
  .rectangle 15 45 69 52 38,
  .rectangle 67 21 125 24 30,
  .rectangle 67 25 125 28 35], by decide +kernel⟩
private def batch1 : PaidBatch .empty 7 := ⟨[
  .rectangle 68 29 125 32 39,
  .rectangle 68 33 125 36 44,
  .rectangle 70 49 83 52 41,
  .rectangle 70 37 97 40 38,
  .rectangle 70 41 97 44 41,
  .rectangle 70 45 97 48 45], by decide +kernel⟩
private def batch2 : PaidBatch .empty 7 := ⟨[
  .rectangle 84 49 97 50 44,
  .rectangle 84 51 97 52 46,
  .rectangle 98 47 104 48 46,
  .rectangle 98 49 104 49 46,
  .rectangle 98 50 104 50 47,
  .rectangle 98 51 104 51 47], by decide +kernel⟩
private def batch3 : PaidBatch .empty 7 := ⟨[
  .rectangle 98 52 104 52 48,
  .rectangle 98 41 111 42 43,
  .rectangle 98 43 111 44 45,
  .rectangle 98 45 111 46 47,
  .rectangle 98 37 125 38 44,
  .rectangle 98 39 125 40 46], by decide +kernel⟩
private def batch4 : PaidBatch .empty 7 := ⟨[
  .point 105 52 46,
  .rectangle 105 50 106 50 47,
  .rectangle 105 51 106 51 48,
  .rectangle 105 48 108 48 47,
  .rectangle 105 49 108 49 47,
  .rectangle 105 47 111 47 47], by decide +kernel⟩
private def batch5 : PaidBatch .empty 7 := ⟨[
  .point 106 52 46,
  .point 107 50 45,
  .point 107 51 46,
  .point 107 52 46,
  .point 108 50 45,
  .point 108 51 46], by decide +kernel⟩
private def batch6 : PaidBatch .empty 7 := ⟨[
  .point 108 52 47,
  .point 109 49 45,
  .point 109 50 46,
  .point 109 51 46,
  .point 109 52 47,
  .rectangle 109 48 110 48 47], by decide +kernel⟩
private def batch7 : PaidBatch .empty 7 := ⟨[
  .point 110 49 45,
  .point 110 50 46,
  .point 110 51 47,
  .point 110 52 48,
  .point 111 48 45,
  .point 111 49 46], by decide +kernel⟩
private def batch8 : PaidBatch .empty 7 := ⟨[
  .point 111 50 46,
  .point 111 51 47,
  .point 111 52 48,
  .rectangle 112 47 112 47 47,
  .point 112 48 45,
  .point 112 49 46], by decide +kernel⟩
private def batch9 : PaidBatch .empty 7 := ⟨[
  .point 112 50 47,
  .point 112 51 48,
  .shared 112 52 48 ⟨.tilted, 1, 2, true, 188579381581250320⟩,
  .rectangle 112 45 115 45 46,
  .rectangle 112 46 115 46 47,
  .rectangle 112 41 118 42 46], by decide +kernel⟩
private def batch10 : PaidBatch .empty 7 := ⟨[
  .rectangle 112 43 118 43 46,
  .rectangle 112 44 118 44 47,
  .point 113 47 44,
  .point 113 48 45,
  .point 113 49 46,
  .point 113 50 47], by decide +kernel⟩
private def batch11 : PaidBatch .empty 7 := ⟨[
  .point 113 51 48,
  .shared 113 52 48 ⟨.tilted, 1, 2, true, 190248944304817161⟩,
  .point 114 47 45,
  .point 114 48 46,
  .point 114 49 47,
  .point 114 50 48], by decide +kernel⟩
private def batch12 : PaidBatch .empty 7 := ⟨[
  .shared 114 51 48 ⟨.tilted, 1, 2, true, 184732373091110860⟩,
  .shared 114 52 48 ⟨.tilted, 1, 2, true, 191918507028384003⟩,
  .point 115 47 45,
  .point 115 48 46,
  .point 115 49 47,
  .point 115 50 48], by decide +kernel⟩
private def batch13 : PaidBatch .empty 7 := ⟨[
  .shared 115 51 48 ⟨.tilted, 1, 2, true, 186335797626310123⟩,
  .shared 115 52 48 ⟨.tilted, 1, 2, true, 193588069751950845⟩,
  .point 116 46 45,
  .point 116 47 46,
  .point 116 48 47,
  .point 116 49 48], by decide +kernel⟩
private def batch14 : PaidBatch .empty 7 := ⟨[
  .point 116 50 48,
  .shared 116 51 48 ⟨.tilted, 1, 2, true, 187939222161509385⟩,
  .shared 116 52 48 ⟨.tilted, 1, 2, true, 195257632475517686⟩,
  .rectangle 116 45 117 45 47,
  .point 117 46 45,
  .point 117 47 46], by decide +kernel⟩
private def batch15 : PaidBatch .empty 7 := ⟨[
  .point 117 48 47,
  .point 117 49 48,
  .shared 117 50 48 ⟨.tilted, 1, 1, false, 167928676879532734⟩,
  .shared 117 51 48 ⟨.tilted, 1, 2, true, 189542646696708648⟩,
  .shared 117 52 48 ⟨.tilted, 1, 2, true, 196927195199084528⟩,
  .point 118 45 44], by decide +kernel⟩
private def batch16 : PaidBatch .empty 7 := ⟨[
  .point 118 46 45,
  .point 118 47 46,
  .point 118 48 47,
  .point 118 49 48,
  .shared 118 50 48 ⟨.tilted, 1, 1, false, 169317133805570935⟩,
  .shared 118 51 48 ⟨.tilted, 1, 2, true, 191146071231907910⟩], by decide +kernel⟩
private def batch17 : PaidBatch .empty 7 := ⟨[
  .shared 118 52 48 ⟨.tilted, 1, 2, true, 198596757922651370⟩,
  .point 119 45 45,
  .point 119 46 46,
  .point 119 47 47,
  .shared 119 48 47 ⟨.tilted, 0, 1, false, 158114578880175810⟩,
  .shared 119 49 48 ⟨.tilted, 0, 1, false, 164364269078137499⟩], by decide +kernel⟩
private def batch18 : PaidBatch .empty 7 := ⟨[
  .shared 119 50 48 ⟨.tilted, 1, 1, false, 170705590731609137⟩,
  .shared 119 51 48 ⟨.tilted, 1, 2, true, 192749495767107173⟩,
  .shared 119 52 48 ⟨.tilted, 1, 2, true, 200266320646218211⟩,
  .rectangle 119 44 120 44 47,
  .rectangle 119 43 122 43 47,
  .rectangle 119 41 125 41 46], by decide +kernel⟩
private def batch19 : PaidBatch .empty 7 := ⟨[
  .rectangle 119 42 125 42 47,
  .point 120 45 45,
  .point 120 46 46,
  .point 120 47 47,
  .shared 120 48 47 ⟨.tilted, 0, 1, false, 159397891667780324⟩,
  .shared 120 49 48 ⟨.tilted, 0, 1, false, 165699672930033440⟩], by decide +kernel⟩
private def batch20 : PaidBatch .empty 7 := ⟨[
  .shared 120 50 48 ⟨.tilted, 0, 1, false, 172094047657647338⟩,
  .shared 120 51 48 ⟨.tilted, 1, 2, true, 194352920302306435⟩,
  .shared 120 52 48 ⟨.tilted, 1, 2, true, 201935883369785053⟩,
  .point 121 44 44,
  .point 121 45 45,
  .point 121 46 46], by decide +kernel⟩
private def batch21 : PaidBatch .empty 7 := ⟨[
  .point 121 47 47,
  .shared 121 48 47 ⟨.tilted, 0, 1, false, 160681204455384837⟩,
  .shared 121 49 48 ⟨.tilted, 0, 1, false, 167035076781929380⟩,
  .shared 121 50 48 ⟨.tilted, 0, 2, true, 188423976369523070⟩,
  .shared 121 51 48 ⟨.tilted, 1, 2, true, 195956344837505698⟩,
  .shared 121 52 48 ⟨.tilted, 1, 2, true, 203605446093351895⟩], by decide +kernel⟩
private def batch22 : PaidBatch .empty 7 := ⟨[
  .point 122 44 45,
  .point 122 45 46,
  .point 122 46 47,
  .shared 122 47 47 ⟨.tilted, 0, 1, false, 155654514351992081⟩,
  .shared 122 48 48 ⟨.tilted, 0, 1, false, 161964517242989351⟩,
  .shared 122 49 48 ⟨.tilted, 0, 1, false, 168370480633825321⟩], by decide +kernel⟩
private def batch23 : PaidBatch .empty 7 := ⟨[
  .shared 122 50 48 ⟨.tilted, 0, 2, true, 189962598841147578⟩,
  .shared 122 51 48 ⟨.tilted, 1, 2, true, 197559769372704960⟩,
  .shared 122 52 48 ⟨.tilted, 1, 2, true, 205275008816918736⟩,
  .rectangle 123 43 123 43 47,
  .point 123 44 45,
  .point 123 45 46], by decide +kernel⟩
private def batch24 : PaidBatch .empty 7 := ⟨[
  .point 123 46 47,
  .shared 123 47 47 ⟨.tilted, 0, 1, false, 156886698085156002⟩,
  .shared 123 48 48 ⟨.tilted, 0, 1, false, 163247830030593864⟩,
  .shared 123 49 48 ⟨.tilted, 0, 1, false, 169705884485721261⟩,
  .shared 123 50 48 ⟨.tilted, 0, 2, true, 191501221312772086⟩,
  .shared 123 51 48 ⟨.tilted, 0, 2, true, 199163193907904223⟩], by decide +kernel⟩
private def batch25 : PaidBatch .empty 7 := ⟨[
  .shared 123 52 48 ⟨.tilted, 1, 2, true, 206944571540485578⟩,
  .point 124 43 44,
  .point 124 44 45,
  .point 124 45 47,
  .shared 124 46 47 ⟨.tilted, 0, 1, false, 151805948352758087⟩,
  .shared 124 47 47 ⟨.tilted, 0, 1, false, 158118881818319922⟩], by decide +kernel⟩
private def batch26 : PaidBatch .empty 7 := ⟨[
  .shared 124 48 48 ⟨.tilted, 0, 1, false, 164531142818198378⟩,
  .shared 124 49 48 ⟨.tilted, 0, 1, false, 171041288337617202⟩,
  .shared 124 50 48 ⟨.tilted, 0, 2, true, 193039843784396595⟩,
  .shared 124 51 48 ⟨.tilted, 0, 2, true, 200766618443103485⟩,
  .shared 124 52 48 ⟨.tilted, 1, 2, true, 208614134264052420⟩,
  .point 125 43 45], by decide +kernel⟩
private def batch27 : PaidBatch .empty 7 := ⟨[
  .point 125 44 46,
  .point 125 45 47,
  .shared 125 46 47 ⟨.tilted, 0, 1, false, 152987965041332249⟩,
  .shared 125 47 47 ⟨.tilted, 0, 1, false, 159351065551483843⟩,
  .shared 125 48 48 ⟨.tilted, 0, 1, false, 165814455605802891⟩,
  .shared 125 49 48 ⟨.tilted, 0, 1, false, 172376692189513142⟩], by decide +kernel⟩
private def batch28 : PaidBatch .empty 7 := ⟨[
  .shared 125 50 48 ⟨.tilted, 0, 2, true, 194578466256021103⟩,
  .shared 125 51 48 ⟨.tilted, 0, 2, true, 202370042978302748⟩,
  .shared 125 52 48 ⟨.tilted, 0, 2, true, 210283696987619261⟩], by decide +kernel⟩

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
