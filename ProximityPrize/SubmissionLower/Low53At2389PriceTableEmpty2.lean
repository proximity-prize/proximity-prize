import ProximityPrize.SubmissionLower.Low53At2389PriceTableCover

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000

namespace Low53At2389PriceTableEmpty2
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Low53At2389Price (fullCap)
open Low53At2389PriceCaps (Band start)
open Low53At2389PriceTableBase (Covered)
open Low53At2389PriceTableCover (PaidBatch tilesOf checks checks_join Certificate)

namespace Top2
private def b0 : PaidBatch .empty 2 := ⟨[
  .rectangle 2 6 9 8 1,
  .rectangle 3 9 66 11 8,
  .rectangle 4 12 66 17 14], by decide +kernel⟩
private def b1 : PaidBatch .empty 2 := ⟨[
  .rectangle 6 18 67 29 27,
  .rectangle 10 6 17 7 1,
  .rectangle 10 8 17 8 2], by decide +kernel⟩
private def b2 : PaidBatch .empty 2 := ⟨[
  .rectangle 10 30 69 41 31,
  .rectangle 14 42 69 53 34,
  .rectangle 18 6 33 8 3], by decide +kernel⟩
private def b3 : PaidBatch .empty 2 := ⟨[
  .rectangle 34 6 65 8 6,
  .rectangle 66 6 129 8 11,
  .rectangle 67 9 129 11 15], by decide +kernel⟩
private def b4 : PaidBatch .empty 2 := ⟨[
  .rectangle 67 12 129 17 27,
  .rectangle 68 18 129 23 34,
  .rectangle 68 24 129 29 40], by decide +kernel⟩
private def b5 : PaidBatch .empty 2 := ⟨[
  .rectangle 70 30 99 35 35,
  .rectangle 70 36 99 41 39,
  .rectangle 70 42 99 47 42], by decide +kernel⟩
private def b6 : PaidBatch .empty 2 := ⟨[
  .rectangle 70 48 99 53 46,
  .rectangle 100 48 107 50 45,
  .rectangle 100 51 107 53 47], by decide +kernel⟩
private def b7 : PaidBatch .empty 2 := ⟨[
  .rectangle 100 39 114 41 42,
  .rectangle 100 42 114 44 44,
  .rectangle 100 45 114 47 46], by decide +kernel⟩
private def b8 : PaidBatch .empty 2 := ⟨[
  .rectangle 100 30 129 32 39,
  .rectangle 100 33 129 35 42,
  .rectangle 100 36 129 38 45], by decide +kernel⟩
private def b9 : PaidBatch .empty 2 := ⟨[
  .rectangle 108 48 114 49 47,
  .rectangle 108 50 114 50 47,
  .rectangle 108 51 114 51 47], by decide +kernel⟩
private def b10 : PaidBatch .empty 2 := ⟨[
  .rectangle 108 52 114 52 48,
  .rectangle 108 53 114 53 49,
  .rectangle 115 53 115 53 49], by decide +kernel⟩
private def b11 : PaidBatch .empty 2 := ⟨[
  .rectangle 115 50 116 50 48,
  .rectangle 115 51 116 51 48,
  .rectangle 115 52 116 52 49], by decide +kernel⟩
private def b12 : PaidBatch .empty 2 := ⟨[
  .rectangle 115 48 118 48 47,
  .rectangle 115 49 118 49 48,
  .rectangle 115 39 122 41 45], by decide +kernel⟩
private def b13 : PaidBatch .empty 2 := ⟨[
  .rectangle 115 42 122 44 47,
  .rectangle 115 45 122 46 48,
  .rectangle 115 47 122 47 48], by decide +kernel⟩
private def b14 : PaidBatch .empty 2 := ⟨[
  .point 116 53 46,
  .rectangle 117 50 117 50 48,
  .point 117 52 46], by decide +kernel⟩
private def b15 : PaidBatch .empty 2 := ⟨[
  .point 117 53 46,
  .rectangle 117 51 118 51 49,
  .point 118 50 45], by decide +kernel⟩
private def b16 : PaidBatch .empty 2 := ⟨[
  .point 118 52 46,
  .point 118 53 47,
  .rectangle 119 49 119 49 48], by decide +kernel⟩
private def b17 : PaidBatch .empty 2 := ⟨[
  .point 119 50 45,
  .point 119 51 46,
  .point 119 52 47], by decide +kernel⟩
private def b18 : PaidBatch .empty 2 := ⟨[
  .point 119 53 47,
  .rectangle 119 48 120 48 48,
  .point 120 49 45], by decide +kernel⟩
private def b19 : PaidBatch .empty 2 := ⟨[
  .point 120 50 46,
  .point 120 51 46,
  .point 120 52 47], by decide +kernel⟩
private def b20 : PaidBatch .empty 2 := ⟨[
  .point 120 53 48,
  .rectangle 121 48 121 48 48,
  .point 121 49 45], by decide +kernel⟩
private def b21 : PaidBatch .empty 2 := ⟨[
  .point 121 50 46,
  .point 121 51 47,
  .point 121 52 48], by decide +kernel⟩
private def b22 : PaidBatch .empty 2 := ⟨[
  .point 121 53 48,
  .point 122 48 45,
  .point 122 49 46], by decide +kernel⟩
private def b23 : PaidBatch .empty 2 := ⟨[
  .point 122 50 46,
  .point 122 51 47,
  .point 122 52 48], by decide +kernel⟩
private def b24 : PaidBatch .empty 2 := ⟨[
  .point 122 53 49,
  .rectangle 123 47 123 47 48,
  .point 123 48 45], by decide +kernel⟩
private def b25 : PaidBatch .empty 2 := ⟨[
  .point 123 49 46,
  .point 123 50 47,
  .point 123 51 48], by decide +kernel⟩
private def b26 : PaidBatch .empty 2 := ⟨[
  .point 123 52 48,
  .point 123 53 49,
  .rectangle 123 46 124 46 48], by decide +kernel⟩
private def b27 : PaidBatch .empty 2 := ⟨[
  .rectangle 123 45 126 45 48,
  .rectangle 123 39 129 40 45,
  .rectangle 123 41 129 41 45], by decide +kernel⟩
private def b28 : PaidBatch .empty 2 := ⟨[
  .rectangle 123 42 129 43 48,
  .rectangle 123 44 129 44 48,
  .point 124 47 45], by decide +kernel⟩
private def b29 : PaidBatch .empty 2 := ⟨[
  .point 124 48 46,
  .point 124 49 46,
  .point 124 50 47], by decide +kernel⟩
private def b30 : PaidBatch .empty 2 := ⟨[
  .point 124 51 48,
  .point 124 52 49,
  .shared 124 53 33 ⟨.tilted, 1, 2, true, 178523293754665243⟩], by decide +kernel⟩
private def b31 : PaidBatch .empty 2 := ⟨[
  .rectangle 125 46 125 46 48,
  .point 125 47 45,
  .point 125 48 46], by decide +kernel⟩
private def b32 : PaidBatch .empty 2 := ⟨[
  .point 125 49 47,
  .point 125 50 48,
  .point 125 51 49], by decide +kernel⟩
private def b33 : PaidBatch .empty 2 := ⟨[
  .point 125 52 49,
  .shared 125 53 34 ⟨.tilted, 1, 2, true, 180190474523189319⟩,
  .point 126 46 45], by decide +kernel⟩
private def b34 : PaidBatch .empty 2 := ⟨[
  .point 126 47 46,
  .point 126 48 46,
  .point 126 49 47], by decide +kernel⟩
private def b35 : PaidBatch .empty 2 := ⟨[
  .point 126 50 48,
  .point 126 51 49,
  .shared 126 52 33 ⟨.tilted, 1, 2, true, 175565403090663468⟩], by decide +kernel⟩
private def b36 : PaidBatch .empty 2 := ⟨[
  .shared 126 53 34 ⟨.tilted, 1, 2, true, 181857655291713395⟩,
  .rectangle 127 45 127 45 48,
  .point 127 46 45], by decide +kernel⟩
private def b37 : PaidBatch .empty 2 := ⟨[
  .point 127 47 46,
  .point 127 48 47,
  .point 127 49 48], by decide +kernel⟩
private def b38 : PaidBatch .empty 2 := ⟨[
  .point 127 50 49,
  .point 127 51 49,
  .shared 127 52 34 ⟨.tilted, 1, 2, true, 177167823076953316⟩], by decide +kernel⟩
private def b39 : PaidBatch .empty 2 := ⟨[
  .shared 127 53 35 ⟨.tilted, 1, 2, true, 183524836060237471⟩,
  .point 128 45 45,
  .point 128 46 46], by decide +kernel⟩
private def b40 : PaidBatch .empty 2 := ⟨[
  .point 128 47 46,
  .point 128 48 47,
  .point 128 49 48], by decide +kernel⟩
private def b41 : PaidBatch .empty 2 := ⟨[
  .point 128 50 49,
  .shared 128 51 33 ⟨.tilted, 1, 2, true, 172428654409301585⟩,
  .shared 128 52 34 ⟨.tilted, 1, 2, true, 178770243063243164⟩], by decide +kernel⟩
private def b42 : PaidBatch .empty 2 := ⟨[
  .shared 128 53 35 ⟨.tilted, 1, 2, true, 185192016828761547⟩,
  .point 129 45 45,
  .point 129 46 46], by decide +kernel⟩
private def b43 : PaidBatch .empty 2 := ⟨[
  .point 129 47 47,
  .point 129 48 48,
  .point 129 49 49], by decide +kernel⟩
private def b44 : PaidBatch .empty 2 := ⟨[
  .point 129 50 49,
  .shared 129 51 34 ⟨.tilted, 1, 2, true, 173967596004873197⟩,
  .shared 129 52 35 ⟨.tilted, 1, 2, true, 180372663049533012⟩], by decide +kernel⟩
private def b45 : PaidBatch .empty 2 := ⟨[
  .shared 129 53 36 ⟨.tilted, 1, 2, true, 186859197597285623⟩], by decide +kernel⟩
private def batches : List (PaidBatch .empty 2) := [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45]
private abbrev tiles := tilesOf batches
private theorem i6 : checks tiles 129 6 2 = true := by decide +kernel
private theorem i8 : checks tiles 129 8 2 = true := by decide +kernel
private theorem i10 : checks tiles 129 10 2 = true := by decide +kernel
private theorem i12 : checks tiles 129 12 2 = true := by decide +kernel
private theorem i14 : checks tiles 129 14 2 = true := by decide +kernel
private theorem i16 : checks tiles 129 16 2 = true := by decide +kernel
private theorem i18 : checks tiles 129 18 2 = true := by decide +kernel
private theorem i20 : checks tiles 129 20 2 = true := by decide +kernel
private theorem i22 : checks tiles 129 22 2 = true := by decide +kernel
private theorem i24 : checks tiles 129 24 2 = true := by decide +kernel
private theorem i26 : checks tiles 129 26 2 = true := by decide +kernel
private theorem i28 : checks tiles 129 28 2 = true := by decide +kernel
private theorem i30 : checks tiles 129 30 2 = true := by decide +kernel
private theorem i32 : checks tiles 129 32 2 = true := by decide +kernel
private theorem i34 : checks tiles 129 34 2 = true := by decide +kernel
private theorem i36 : checks tiles 129 36 2 = true := by decide +kernel
private theorem i38 : checks tiles 129 38 2 = true := by decide +kernel
private theorem i40 : checks tiles 129 40 2 = true := by decide +kernel
private theorem i42 : checks tiles 129 42 2 = true := by decide +kernel
private theorem i44 : checks tiles 129 44 2 = true := by decide +kernel
private theorem i46 : checks tiles 129 46 2 = true := by decide +kernel
private theorem i48 : checks tiles 129 48 2 = true := by decide +kernel
private theorem i50 : checks tiles 129 50 2 = true := by decide +kernel
private theorem i52 : checks tiles 129 52 2 = true := by decide +kernel
def receipt : Certificate .empty 2 := ⟨batches, checks_join i6 (checks_join i8 (checks_join i10 (checks_join i12 (checks_join i14 (checks_join i16 (checks_join i18 (checks_join i20 (checks_join i22 (checks_join i24 (checks_join i26 (checks_join i28 (checks_join i30 (checks_join i32 (checks_join i34 (checks_join i36 (checks_join i38 (checks_join i40 (checks_join i42 (checks_join i44 (checks_join i46 (checks_join i48 (checks_join i50 i52))))))))))))))))))))))⟩
end Top2


end Low53At2389PriceTableEmpty2
