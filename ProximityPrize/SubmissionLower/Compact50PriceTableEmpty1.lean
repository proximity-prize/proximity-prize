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
  .rectangle 1 3 129 3 1,
  .rectangle 2 4 68 4 1,
  .rectangle 2 5 22 6 1,
  .rectangle 3 7 11 9 1,
  .rectangle 4 10 54 17 13,
  .rectangle 6 18 105 25 31], by decide +kernel⟩
private def batch1 : PaidBatch .empty 1 := ⟨[
  .rectangle 9 26 107 33 37,
  .rectangle 12 7 29 8 2,
  .rectangle 12 9 51 13 8,
  .rectangle 12 34 95 41 37,
  .rectangle 14 42 101 49 44,
  .rectangle 17 50 104 53 44], by decide +kernel⟩
private def batch2 : PaidBatch .empty 1 := ⟨[
  .rectangle 23 5 38 5 1,
  .rectangle 23 6 52 7 3,
  .rectangle 30 8 69 10 7,
  .rectangle 39 5 122 9 16,
  .rectangle 55 11 121 16 24,
  .rectangle 55 17 111 22 27], by decide +kernel⟩
private def batch3 : PaidBatch .empty 1 := ⟨[
  .rectangle 69 4 129 10 31,
  .rectangle 96 34 125 38 44,
  .rectangle 96 39 120 42 44,
  .rectangle 102 43 117 46 46,
  .rectangle 102 47 117 49 47,
  .rectangle 105 50 113 52 47], by decide +kernel⟩
private def batch4 : PaidBatch .empty 1 := ⟨[
  .rectangle 105 53 117 53 48,
  .rectangle 106 23 129 29 41,
  .rectangle 108 30 128 35 44,
  .rectangle 112 17 129 24 38,
  .rectangle 114 50 118 51 48,
  .rectangle 114 52 119 52 48], by decide +kernel⟩
private def batch5 : PaidBatch .empty 1 := ⟨[
  .rectangle 118 43 128 44 47,
  .rectangle 118 45 124 46 47,
  .rectangle 118 47 125 47 47,
  .rectangle 118 48 123 48 47,
  .rectangle 118 49 123 49 48,
  .point 118 53 48], by decide +kernel⟩
private def batch6 : PaidBatch .empty 1 := ⟨[
  .rectangle 119 50 122 50 48,
  .rectangle 119 51 120 51 48,
  .point 119 53 48,
  .point 120 52 48,
  .point 120 53 48,
  .rectangle 121 39 129 41 46], by decide +kernel⟩
private def batch7 : PaidBatch .empty 1 := ⟨[
  .rectangle 121 42 129 43 47,
  .point 121 51 48,
  .point 121 52 48,
  .point 121 53 48,
  .rectangle 122 11 129 18 35,
  .point 122 51 48], by decide +kernel⟩
private def batch8 : PaidBatch .empty 1 := ⟨[
  .point 122 52 48,
  .point 122 53 48,
  .point 123 50 48,
  .point 123 51 48,
  .point 123 52 48,
  .point 123 53 48], by decide +kernel⟩
private def batch9 : PaidBatch .empty 1 := ⟨[
  .rectangle 124 48 125 48 48,
  .point 124 49 48,
  .point 124 50 48,
  .point 124 51 48,
  .point 124 52 48,
  .point 124 53 48], by decide +kernel⟩
private def batch10 : PaidBatch .empty 1 := ⟨[
  .rectangle 125 45 129 45 47,
  .rectangle 125 46 127 46 47,
  .point 125 49 48,
  .point 125 50 48,
  .point 125 51 48,
  .point 125 52 48], by decide +kernel⟩
private def batch11 : PaidBatch .empty 1 := ⟨[
  .point 125 53 48,
  .rectangle 126 36 129 39 46,
  .point 126 47 47,
  .point 126 48 48,
  .point 126 49 48,
  .point 126 50 48], by decide +kernel⟩
private def batch12 : PaidBatch .empty 1 := ⟨[
  .point 126 51 48,
  .point 126 52 48,
  .point 126 53 48,
  .point 127 47 47,
  .point 127 48 48,
  .point 127 49 48], by decide +kernel⟩
private def batch13 : PaidBatch .empty 1 := ⟨[
  .point 127 50 48,
  .point 127 51 48,
  .point 127 52 48,
  .point 127 53 48,
  .point 128 46 47,
  .point 128 47 47], by decide +kernel⟩
private def batch14 : PaidBatch .empty 1 := ⟨[
  .point 128 48 48,
  .point 128 49 48,
  .point 128 50 48,
  .point 128 51 48,
  .point 128 52 48,
  .point 128 53 48], by decide +kernel⟩
private def batch15 : PaidBatch .empty 1 := ⟨[
  .rectangle 129 30 129 34 44,
  .rectangle 129 35 129 38 45,
  .rectangle 129 44 129 44 47,
  .point 129 46 47,
  .point 129 47 47,
  .point 129 48 48], by decide +kernel⟩
private def batch16 : PaidBatch .empty 1 := ⟨[
  .point 129 49 48,
  .point 129 50 48,
  .point 129 51 48,
  .point 129 52 48,
  .point 129 53 49], by decide +kernel⟩

private def batches : List (PaidBatch .empty 1) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16]
private abbrev tiles := tilesOf batches

private theorem index3 : checks tiles 129 3 10 = true := by decide +kernel
theorem index13 : checks tiles 129 13 10 = true := by decide +kernel
theorem index23 : checks tiles 129 23 10 = true := by decide +kernel
private theorem index33 : checks tiles 129 33 10 = true := by decide +kernel
private theorem index43 : checks tiles 129 43 10 = true := by decide +kernel
private theorem index53 : checks tiles 129 53 1 = true := by decide +kernel
private theorem covers : checks tiles 129 3 51 = true :=
  checks_join (checks_join (checks_join (checks_join (checks_join (index3) index13) index23) index33) index43) index53

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 1)
    (hb : a.b ≤ 129) (hj : a.j ≤ 53) : Covered 1 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top1

namespace Top2
private def batch0 : PaidBatch .empty 2 := ⟨[
  .rectangle 2 6 17 7 1,
  .rectangle 3 8 11 9 1,
  .rectangle 4 10 52 17 13,
  .rectangle 6 18 102 25 31,
  .rectangle 9 26 103 33 37,
  .rectangle 12 8 55 11 7], by decide +kernel⟩
private def batch1 : PaidBatch .empty 2 := ⟨[
  .rectangle 12 34 91 41 37,
  .rectangle 14 42 96 49 44,
  .rectangle 17 50 100 53 44,
  .rectangle 18 6 52 7 3,
  .rectangle 53 6 129 10 18,
  .rectangle 53 12 129 16 24], by decide +kernel⟩
private def batch2 : PaidBatch .empty 2 := ⟨[
  .rectangle 53 17 108 22 27,
  .rectangle 56 11 119 16 24,
  .rectangle 92 34 121 38 44,
  .rectangle 92 39 116 42 44,
  .rectangle 97 43 113 46 46,
  .rectangle 97 47 109 50 47], by decide +kernel⟩
private def batch3 : PaidBatch .empty 2 := ⟨[
  .rectangle 101 51 107 53 47,
  .rectangle 103 23 128 29 41,
  .rectangle 104 30 125 35 44,
  .rectangle 108 51 112 52 48,
  .rectangle 108 53 113 53 48,
  .rectangle 109 17 128 24 38], by decide +kernel⟩
private def batch4 : PaidBatch .empty 2 := ⟨[
  .rectangle 110 47 117 48 47,
  .rectangle 110 49 117 49 47,
  .rectangle 110 50 115 50 47,
  .rectangle 113 51 116 51 48,
  .rectangle 113 52 114 52 48,
  .rectangle 114 43 124 44 47], by decide +kernel⟩
private def batch5 : PaidBatch .empty 2 := ⟨[
  .rectangle 114 45 120 46 47,
  .point 114 53 48,
  .point 115 52 48,
  .point 115 53 48,
  .rectangle 116 50 118 50 48,
  .point 116 52 48], by decide +kernel⟩
private def batch6 : PaidBatch .empty 2 := ⟨[
  .point 116 53 48,
  .rectangle 117 39 126 41 46,
  .rectangle 117 42 127 43 47,
  .point 117 51 48,
  .point 117 52 48,
  .point 117 53 48], by decide +kernel⟩
private def batch7 : PaidBatch .empty 2 := ⟨[
  .rectangle 118 47 121 47 47,
  .rectangle 118 48 119 48 47,
  .rectangle 118 49 119 49 48,
  .point 118 51 48,
  .point 118 52 48,
  .point 118 53 48], by decide +kernel⟩
private def batch8 : PaidBatch .empty 2 := ⟨[
  .point 119 50 48,
  .point 119 51 48,
  .point 119 52 48,
  .point 119 53 48,
  .rectangle 120 11 129 18 35,
  .point 120 48 47], by decide +kernel⟩
private def batch9 : PaidBatch .empty 2 := ⟨[
  .point 120 49 48,
  .point 120 50 48,
  .point 120 51 48,
  .point 120 52 48,
  .point 120 53 48,
  .rectangle 121 45 125 45 47], by decide +kernel⟩
private def batch10 : PaidBatch .empty 2 := ⟨[
  .rectangle 121 46 123 46 47,
  .point 121 48 47,
  .point 121 49 48,
  .point 121 50 48,
  .point 121 51 48,
  .point 121 52 48], by decide +kernel⟩
private def batch11 : PaidBatch .empty 2 := ⟨[
  .point 121 53 48,
  .rectangle 122 36 128 39 46,
  .point 122 47 47,
  .point 122 48 48,
  .point 122 49 48,
  .point 122 50 48], by decide +kernel⟩
private def batch12 : PaidBatch .empty 2 := ⟨[
  .point 122 51 48,
  .point 122 52 48,
  .shared 122 53 48 ⟨.tilted, 1, 2, true, 175191557609300652⟩,
  .point 123 47 47,
  .point 123 48 48,
  .point 123 49 48], by decide +kernel⟩
private def batch13 : PaidBatch .empty 2 := ⟨[
  .point 123 50 48,
  .point 123 51 48,
  .point 123 52 48,
  .shared 123 53 48 ⟨.tilted, 1, 2, true, 176858763362296544⟩,
  .point 124 46 47,
  .point 124 47 47], by decide +kernel⟩
private def batch14 : PaidBatch .empty 2 := ⟨[
  .point 124 48 48,
  .point 124 49 48,
  .point 124 50 48,
  .point 124 51 48,
  .shared 124 52 48 ⟨.tilted, 1, 2, true, 172363146123658756⟩,
  .shared 124 53 48 ⟨.tilted, 1, 2, true, 178525969115292436⟩], by decide +kernel⟩
private def batch15 : PaidBatch .empty 2 := ⟨[
  .rectangle 125 44 127 44 47,
  .point 125 46 47,
  .point 125 47 47,
  .point 125 48 48,
  .point 125 49 48,
  .point 125 50 48], by decide +kernel⟩
private def batch16 : PaidBatch .empty 2 := ⟨[
  .point 125 51 48,
  .shared 125 52 48 ⟨.tilted, 1, 2, true, 173965590123911340⟩,
  .shared 125 53 48 ⟨.tilted, 1, 2, true, 180193174868288328⟩,
  .rectangle 126 30 129 34 44,
  .rectangle 126 35 129 37 45,
  .point 126 45 47], by decide +kernel⟩
private def batch17 : PaidBatch .empty 2 := ⟨[
  .point 126 46 47,
  .point 126 47 47,
  .point 126 48 48,
  .point 126 49 48,
  .point 126 50 48,
  .shared 126 51 48 ⟨.tilted, 1, 2, true, 169353309118811430⟩], by decide +kernel⟩
private def batch18 : PaidBatch .empty 2 := ⟨[
  .shared 126 52 48 ⟨.tilted, 1, 2, true, 175568034124163924⟩,
  .shared 126 53 48 ⟨.tilted, 1, 2, true, 181860380621284220⟩,
  .rectangle 127 40 129 41 47,
  .point 127 45 47,
  .point 127 46 47,
  .point 127 47 47], by decide +kernel⟩
private def batch19 : PaidBatch .empty 2 := ⟨[
  .point 127 48 48,
  .point 127 49 48,
  .shared 127 50 48 ⟨.tilted, 1, 2, true, 164694896948295668⟩,
  .shared 127 51 48 ⟨.tilted, 1, 2, true, 170892273777054698⟩,
  .shared 127 52 48 ⟨.tilted, 1, 2, true, 177170478124416508⟩,
  .shared 127 53 48 ⟨.tilted, 1, 2, true, 183527586374280112⟩], by decide +kernel⟩
private def batch20 : PaidBatch .empty 2 := ⟨[
  .rectangle 128 42 129 42 47,
  .rectangle 128 43 129 43 47,
  .point 128 44 47,
  .point 128 45 47,
  .point 128 46 47,
  .point 128 47 47], by decide +kernel⟩
private def batch21 : PaidBatch .empty 2 := ⟨[
  .point 128 48 48,
  .point 128 49 48,
  .shared 128 50 48 ⟨.tilted, 0, 2, true, 166171664675263612⟩,
  .shared 128 51 48 ⟨.tilted, 1, 2, true, 172431238435297966⟩,
  .shared 128 52 48 ⟨.tilted, 1, 2, true, 178772922124669092⟩,
  .shared 128 53 48 ⟨.tilted, 1, 2, true, 185194792127276004⟩], by decide +kernel⟩
private def batch22 : PaidBatch .empty 2 := ⟨[
  .rectangle 129 19 129 25 39,
  .rectangle 129 26 129 31 42,
  .rectangle 129 38 129 39 46,
  .point 129 44 47,
  .point 129 45 47,
  .point 129 46 47], by decide +kernel⟩
private def batch23 : PaidBatch .empty 2 := ⟨[
  .point 129 47 47,
  .point 129 48 48,
  .shared 129 49 48 ⟨.tilted, 0, 2, true, 161411977667093632⟩,
  .shared 129 50 48 ⟨.tilted, 0, 2, true, 167648432402231556⟩,
  .shared 129 51 48 ⟨.tilted, 1, 2, true, 173970203093541234⟩,
  .shared 129 52 48 ⟨.tilted, 1, 2, true, 180375366124921676⟩], by decide +kernel⟩
private def batch24 : PaidBatch .empty 2 := ⟨[
  .shared 129 53 49 ⟨.tilted, 1, 2, true, 186861997880271896⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 2) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24]
private abbrev tiles := tilesOf batches

private theorem index6 : checks tiles 129 6 10 = true := by decide +kernel
theorem index16 : checks tiles 129 16 10 = true := by decide +kernel
theorem index26 : checks tiles 129 26 10 = true := by decide +kernel
private theorem index36 : checks tiles 129 36 10 = true := by decide +kernel
private theorem index46 : checks tiles 129 46 8 = true := by decide +kernel
private theorem covers : checks tiles 129 6 48 = true :=
  checks_join (checks_join (checks_join (checks_join (index6) index16) index26) index36) index46

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 2)
    (hb : a.b ≤ 129) (hj : a.j ≤ 53) : Covered 2 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top2

namespace Top3
private def batch0 : PaidBatch .empty 3 := ⟨[
  .rectangle 3 9 42 14 8,
  .rectangle 5 15 94 22 27,
  .rectangle 8 23 90 30 31,
  .rectangle 11 31 92 38 37,
  .rectangle 13 39 96 46 44,
  .rectangle 16 47 91 53 44], by decide +kernel⟩
private def batch1 : PaidBatch .empty 3 := ⟨[
  .rectangle 43 9 128 14 24,
  .rectangle 91 23 126 29 41,
  .rectangle 91 30 127 34 43,
  .rectangle 92 47 106 50 47,
  .rectangle 92 51 104 53 47,
  .rectangle 93 35 122 38 44], by decide +kernel⟩
private def batch2 : PaidBatch .empty 3 := ⟨[
  .rectangle 95 15 126 22 36,
  .rectangle 97 39 118 42 46,
  .rectangle 97 43 110 46 46,
  .rectangle 105 51 109 52 48,
  .rectangle 105 53 109 53 48,
  .rectangle 107 47 113 48 47], by decide +kernel⟩
private def batch3 : PaidBatch .empty 3 := ⟨[
  .rectangle 107 49 114 49 47,
  .rectangle 107 50 112 50 47,
  .rectangle 110 51 113 51 48,
  .rectangle 110 52 111 52 48,
  .point 110 53 48,
  .rectangle 111 43 121 44 47], by decide +kernel⟩
private def batch4 : PaidBatch .empty 3 := ⟨[
  .rectangle 111 45 117 46 47,
  .point 111 53 48,
  .point 112 52 48,
  .point 112 53 48,
  .rectangle 113 50 114 50 48,
  .point 113 52 48], by decide +kernel⟩
private def batch5 : PaidBatch .empty 3 := ⟨[
  .point 113 53 48,
  .rectangle 114 47 118 47 47,
  .rectangle 114 48 116 48 47,
  .point 114 51 48,
  .point 114 52 48,
  .point 114 53 48], by decide +kernel⟩
private def batch6 : PaidBatch .empty 3 := ⟨[
  .point 115 49 47,
  .point 115 50 48,
  .point 115 51 48,
  .point 115 52 48,
  .point 115 53 48,
  .rectangle 116 49 116 49 48], by decide +kernel⟩
private def batch7 : PaidBatch .empty 3 := ⟨[
  .point 116 50 48,
  .point 116 51 48,
  .point 116 52 48,
  .point 116 53 48,
  .point 117 48 47,
  .point 117 49 48], by decide +kernel⟩
private def batch8 : PaidBatch .empty 3 := ⟨[
  .point 117 50 48,
  .point 117 51 48,
  .point 117 52 48,
  .point 117 53 48,
  .rectangle 118 45 122 45 47,
  .rectangle 118 46 120 46 47], by decide +kernel⟩
private def batch9 : PaidBatch .empty 3 := ⟨[
  .point 118 48 47,
  .point 118 49 48,
  .point 118 50 48,
  .point 118 51 48,
  .point 118 52 48,
  .shared 118 53 48 ⟨.tilted, 1, 2, true, 177064488285860344⟩], by decide +kernel⟩
private def batch10 : PaidBatch .empty 3 := ⟨[
  .rectangle 119 39 129 40 46,
  .rectangle 119 41 126 42 47,
  .point 119 47 47,
  .point 119 48 47,
  .point 119 49 48,
  .point 119 50 48], by decide +kernel⟩
private def batch11 : PaidBatch .empty 3 := ⟨[
  .point 119 51 48,
  .point 119 52 48,
  .shared 119 53 48 ⟨.tilted, 1, 2, true, 178731694038856236⟩,
  .point 120 47 47,
  .point 120 48 47,
  .point 120 49 48], by decide +kernel⟩
private def batch12 : PaidBatch .empty 3 := ⟨[
  .point 120 50 48,
  .point 120 51 48,
  .shared 120 52 48 ⟨.tilted, 1, 2, true, 174118469120155422⟩,
  .shared 120 53 48 ⟨.tilted, 1, 2, true, 180398899791852128⟩,
  .point 121 46 47,
  .point 121 47 47], by decide +kernel⟩
private def batch13 : PaidBatch .empty 3 := ⟨[
  .point 121 48 47,
  .point 121 49 48,
  .point 121 50 48,
  .point 121 51 48,
  .shared 121 52 48 ⟨.tilted, 1, 2, true, 175720913120408006⟩,
  .shared 121 53 48 ⟨.tilted, 1, 2, true, 182066105544848020⟩], by decide +kernel⟩
private def batch14 : PaidBatch .empty 3 := ⟨[
  .rectangle 122 43 127 43 47,
  .rectangle 122 44 124 44 47,
  .point 122 46 47,
  .point 122 47 47,
  .point 122 48 48,
  .point 122 49 48], by decide +kernel⟩
private def batch15 : PaidBatch .empty 3 := ⟨[
  .point 122 50 48,
  .shared 122 51 48 ⟨.tilted, 1, 2, true, 170994390763421797⟩,
  .shared 122 52 48 ⟨.tilted, 1, 2, true, 177323357120660590⟩,
  .shared 122 53 48 ⟨.tilted, 1, 2, true, 183733311297843912⟩,
  .rectangle 123 35 129 37 45,
  .rectangle 123 38 129 39 46], by decide +kernel⟩
private def batch16 : PaidBatch .empty 3 := ⟨[
  .point 123 45 47,
  .point 123 46 47,
  .point 123 47 47,
  .point 123 48 48,
  .point 123 49 48,
  .point 123 50 48], by decide +kernel⟩
private def batch17 : PaidBatch .empty 3 := ⟨[
  .shared 123 51 48 ⟨.tilted, 1, 2, true, 172533355421665065⟩,
  .shared 123 52 48 ⟨.tilted, 1, 2, true, 178925801120913174⟩,
  .shared 123 53 48 ⟨.tilted, 1, 2, true, 185400517050839804⟩,
  .point 124 45 47,
  .point 124 46 47,
  .point 124 47 47], by decide +kernel⟩
private def batch18 : PaidBatch .empty 3 := ⟨[
  .point 124 48 48,
  .point 124 49 48,
  .shared 124 50 48 ⟨.tilted, 1, 2, true, 167701871296164411⟩,
  .shared 124 51 48 ⟨.tilted, 1, 2, true, 174072320079908333⟩,
  .shared 124 52 48 ⟨.tilted, 1, 2, true, 180528245121165758⟩,
  .shared 124 53 48 ⟨.tilted, 1, 2, true, 187067722803835696⟩], by decide +kernel⟩
private def batch19 : PaidBatch .empty 3 := ⟨[
  .point 125 44 47,
  .point 125 45 47,
  .point 125 46 47,
  .point 125 47 47,
  .point 125 48 48,
  .point 125 49 48], by decide +kernel⟩
private def batch20 : PaidBatch .empty 3 := ⟨[
  .shared 125 50 48 ⟨.tilted, 1, 2, true, 169178639023132355⟩,
  .shared 125 51 48 ⟨.tilted, 1, 2, true, 175611284738151601⟩,
  .shared 125 52 48 ⟨.tilted, 1, 2, true, 182130689121418342⟩,
  .shared 125 53 48 ⟨.tilted, 1, 2, true, 188734928556831588⟩,
  .point 126 44 47,
  .point 126 45 47], by decide +kernel⟩
private def batch21 : PaidBatch .empty 3 := ⟨[
  .point 126 46 47,
  .point 126 47 47,
  .point 126 48 48,
  .shared 126 49 48 ⟨.tilted, 0, 2, true, 164250528798888202⟩,
  .shared 126 50 48 ⟨.tilted, 1, 2, true, 170655406750100299⟩,
  .shared 126 51 48 ⟨.tilted, 1, 2, true, 177150249396394869⟩], by decide +kernel⟩
private def batch22 : PaidBatch .empty 3 := ⟨[
  .shared 126 52 48 ⟨.tilted, 1, 2, true, 183733133121670926⟩,
  .shared 126 53 48 ⟨.tilted, 1, 2, true, 190402134309827480⟩,
  .rectangle 127 15 129 21 36,
  .rectangle 127 22 129 28 41,
  .rectangle 127 29 129 33 44,
  .rectangle 127 41 129 41 47], by decide +kernel⟩
private def batch23 : PaidBatch .empty 3 := ⟨[
  .rectangle 127 42 129 42 47,
  .point 127 44 47,
  .point 127 45 47,
  .point 127 46 47,
  .point 127 47 47,
  .point 127 48 48], by decide +kernel⟩
private def batch24 : PaidBatch .empty 3 := ⟨[
  .shared 127 49 48 ⟨.tilted, 0, 2, true, 165666382005314814⟩,
  .shared 127 50 48 ⟨.tilted, 1, 2, true, 172132174477068243⟩,
  .shared 127 51 48 ⟨.tilted, 1, 2, true, 178689214054638137⟩,
  .shared 127 52 48 ⟨.tilted, 1, 2, true, 185335577121923510⟩,
  .shared 127 53 48 ⟨.tilted, 1, 2, true, 192069340062823372⟩,
  .rectangle 128 34 129 36 45], by decide +kernel⟩
private def batch25 : PaidBatch .empty 3 := ⟨[
  .point 128 43 47,
  .point 128 44 47,
  .point 128 45 47,
  .point 128 46 47,
  .shared 128 47 47 ⟨.tilted, 0, 1, false, 142472610616255139⟩,
  .shared 128 48 48 ⟨.tilted, 0, 2, true, 160649981352098112⟩], by decide +kernel⟩
private def batch26 : PaidBatch .empty 3 := ⟨[
  .shared 128 49 48 ⟨.tilted, 0, 2, true, 167082235211741426⟩,
  .shared 128 50 48 ⟨.tilted, 0, 2, true, 173608942204036187⟩,
  .shared 128 51 48 ⟨.tilted, 1, 2, true, 180228178712881405⟩,
  .shared 128 52 48 ⟨.tilted, 1, 2, true, 186938021122176094⟩,
  .shared 128 53 48 ⟨.tilted, 1, 2, true, 193736545815819264⟩,
  .rectangle 129 9 129 16 35], by decide +kernel⟩
private def batch27 : PaidBatch .empty 3 := ⟨[
  .point 129 43 47,
  .point 129 44 47,
  .point 129 45 47,
  .point 129 46 47,
  .shared 129 47 47 ⟨.tilted, 0, 1, false, 143658769809792081⟩,
  .shared 129 48 48 ⟨.tilted, 0, 2, true, 162006202448717384⟩], by decide +kernel⟩
private def batch28 : PaidBatch .empty 3 := ⟨[
  .shared 129 49 48 ⟨.tilted, 0, 2, true, 168498088418168038⟩,
  .shared 129 50 48 ⟨.tilted, 0, 2, true, 175085709931004131⟩,
  .shared 129 51 48 ⟨.tilted, 1, 2, true, 181767143371124673⟩,
  .shared 129 52 48 ⟨.tilted, 1, 2, true, 188540465122428678⟩,
  .shared 129 53 49 ⟨.tilted, 1, 2, true, 195403751568815156⟩], by decide +kernel⟩

private def batches : List (PaidBatch .empty 3) := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28]
private abbrev tiles := tilesOf batches

private theorem index9 : checks tiles 129 9 10 = true := by decide +kernel
theorem index19 : checks tiles 129 19 10 = true := by decide +kernel
theorem index29 : checks tiles 129 29 10 = true := by decide +kernel
private theorem index39 : checks tiles 129 39 10 = true := by decide +kernel
private theorem index49 : checks tiles 129 49 5 = true := by decide +kernel
private theorem covers : checks tiles 129 9 45 = true :=
  checks_join (checks_join (checks_join (checks_join (index9) index19) index29) index39) index49

theorem exact (a : Shape) (ha : Valid a) (ht : a.t = 3)
    (hb : a.b ≤ 129) (hj : a.j ≤ 53) : Covered 3 .empty a := by
  have hi := ha.2.1
  exact apply_batches covers a ha ht hb (by omega) (by omega)

end Top3

end Compact50PriceTableEmpty1
