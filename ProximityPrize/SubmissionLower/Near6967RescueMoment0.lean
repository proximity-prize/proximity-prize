import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.R6960ChartImage

section Merged6967_Near6967RescueMoment0
set_option Elab.async false


set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem cost_225_50_block0 : P1_7_1_3.blockEstimate 225 50 50 128 = 37167117 := by decide +kernel

private theorem cost_225_50_block1 : P1_7_1_3.blockEstimate 225 50 178 128 = 37016339 := by decide +kernel

private theorem cost_225_50_block2 : P1_7_1_3.blockEstimate 225 50 306 19 = 154965 := by decide +kernel

private theorem cost_225_50_join0_0 : P1_7_1_3.blockEstimate 225 50 50 256 = 74183456 :=
  @P1_7_1_3.block_append 225 50 50 178 128 128 256 37167117 37016339 74183456 cost_225_50_block0 cost_225_50_block1 rfl rfl rfl

private theorem cost_225_50_join1_0 : P1_7_1_3.blockEstimate 225 50 50 275 = 74338421 :=
  @P1_7_1_3.block_append 225 50 50 306 256 19 275 74183456 154965 74338421 cost_225_50_join0_0 cost_225_50_block2 rfl rfl rfl

private theorem cost_225_50_total : P1_7_1_3.momentEstimate 225 50 = 74338421 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 225 + 50 = 275 by decide]
  exact cost_225_50_join1_0

theorem moment225_50 : P1_7_1.groupedPoleMoment 225 50 ≤ 74338421 :=
  (P1_7_1_3.grouped_bound 225 50).trans_eq cost_225_50_total
private theorem cost_235_51_block0 : P1_7_1_3.blockEstimate 235 51 51 128 = 40354327 := by decide +kernel

private theorem cost_235_51_block1 : P1_7_1_3.blockEstimate 235 51 179 128 = 45811588 := by decide +kernel

private theorem cost_235_51_block2 : P1_7_1_3.blockEstimate 235 51 307 30 = 576132 := by decide +kernel

private theorem cost_235_51_join0_0 : P1_7_1_3.blockEstimate 235 51 51 256 = 86165915 :=
  @P1_7_1_3.block_append 235 51 51 179 128 128 256 40354327 45811588 86165915 cost_235_51_block0 cost_235_51_block1 rfl rfl rfl

private theorem cost_235_51_join1_0 : P1_7_1_3.blockEstimate 235 51 51 286 = 86742047 :=
  @P1_7_1_3.block_append 235 51 51 307 256 30 286 86165915 576132 86742047 cost_235_51_join0_0 cost_235_51_block2 rfl rfl rfl

private theorem cost_235_51_total : P1_7_1_3.momentEstimate 235 51 = 86742047 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 235 + 51 = 286 by decide]
  exact cost_235_51_join1_0

theorem moment235_51 : P1_7_1.groupedPoleMoment 235 51 ≤ 86742047 :=
  (P1_7_1_3.grouped_bound 235 51).trans_eq cost_235_51_total
private theorem cost_237_53_block0 : P1_7_1_3.blockEstimate 237 53 53 128 = 41696505 := by decide +kernel

private theorem cost_237_53_block1 : P1_7_1_3.blockEstimate 237 53 181 128 = 49261334 := by decide +kernel

private theorem cost_237_53_block2 : P1_7_1_3.blockEstimate 237 53 309 34 = 825450 := by decide +kernel

private theorem cost_237_53_join0_0 : P1_7_1_3.blockEstimate 237 53 53 256 = 90957839 :=
  @P1_7_1_3.block_append 237 53 53 181 128 128 256 41696505 49261334 90957839 cost_237_53_block0 cost_237_53_block1 rfl rfl rfl

private theorem cost_237_53_join1_0 : P1_7_1_3.blockEstimate 237 53 53 290 = 91783289 :=
  @P1_7_1_3.block_append 237 53 53 309 256 34 290 90957839 825450 91783289 cost_237_53_join0_0 cost_237_53_block2 rfl rfl rfl

private theorem cost_237_53_total : P1_7_1_3.momentEstimate 237 53 = 91783289 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 237 + 53 = 290 by decide]
  exact cost_237_53_join1_0

theorem moment237_53 : P1_7_1.groupedPoleMoment 237 53 ≤ 91783289 :=
  (P1_7_1_3.grouped_bound 237 53).trans_eq cost_237_53_total
private theorem cost_254_55_block0 : P1_7_1_3.blockEstimate 254 55 55 128 = 47411126 := by decide +kernel

private theorem cost_254_55_block1 : P1_7_1_3.blockEstimate 254 55 183 128 = 67359770 := by decide +kernel

private theorem cost_254_55_block2 : P1_7_1_3.blockEstimate 254 55 311 53 = 3098375 := by decide +kernel

private theorem cost_254_55_join0_0 : P1_7_1_3.blockEstimate 254 55 55 256 = 114770896 :=
  @P1_7_1_3.block_append 254 55 55 183 128 128 256 47411126 67359770 114770896 cost_254_55_block0 cost_254_55_block1 rfl rfl rfl

private theorem cost_254_55_join1_0 : P1_7_1_3.blockEstimate 254 55 55 309 = 117869271 :=
  @P1_7_1_3.block_append 254 55 55 311 256 53 309 114770896 3098375 117869271 cost_254_55_join0_0 cost_254_55_block2 rfl rfl rfl

private theorem cost_254_55_total : P1_7_1_3.momentEstimate 254 55 = 117869271 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 254 + 55 = 309 by decide]
  exact cost_254_55_join1_0

theorem moment254_55 : P1_7_1.groupedPoleMoment 254 55 ≤ 117869271 :=
  (P1_7_1_3.grouped_bound 254 55).trans_eq cost_254_55_total
private theorem cost_254_57_block0 : P1_7_1_3.blockEstimate 254 57 57 128 = 48191330 := by decide +kernel

private theorem cost_254_57_block1 : P1_7_1_3.blockEstimate 254 57 185 128 = 69501528 := by decide +kernel

private theorem cost_254_57_block2 : P1_7_1_3.blockEstimate 254 57 313 55 = 3438218 := by decide +kernel

private theorem cost_254_57_join0_0 : P1_7_1_3.blockEstimate 254 57 57 256 = 117692858 :=
  @P1_7_1_3.block_append 254 57 57 185 128 128 256 48191330 69501528 117692858 cost_254_57_block0 cost_254_57_block1 rfl rfl rfl

private theorem cost_254_57_join1_0 : P1_7_1_3.blockEstimate 254 57 57 311 = 121131076 :=
  @P1_7_1_3.block_append 254 57 57 313 256 55 311 117692858 3438218 121131076 cost_254_57_join0_0 cost_254_57_block2 rfl rfl rfl

private theorem cost_254_57_total : P1_7_1_3.momentEstimate 254 57 = 121131076 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 254 + 57 = 311 by decide]
  exact cost_254_57_join1_0

theorem moment254_57 : P1_7_1.groupedPoleMoment 254 57 ≤ 121131076 :=
  (P1_7_1_3.grouped_bound 254 57).trans_eq cost_254_57_total
private theorem cost_264_57_block0 : P1_7_1_3.blockEstimate 264 57 57 128 = 51172530 := by decide +kernel

private theorem cost_264_57_block1 : P1_7_1_3.blockEstimate 264 57 185 128 = 80175978 := by decide +kernel

private theorem cost_264_57_block2 : P1_7_1_3.blockEstimate 264 57 313 65 = 5733003 := by decide +kernel

private theorem cost_264_57_join0_0 : P1_7_1_3.blockEstimate 264 57 57 256 = 131348508 :=
  @P1_7_1_3.block_append 264 57 57 185 128 128 256 51172530 80175978 131348508 cost_264_57_block0 cost_264_57_block1 rfl rfl rfl

private theorem cost_264_57_join1_0 : P1_7_1_3.blockEstimate 264 57 57 321 = 137081511 :=
  @P1_7_1_3.block_append 264 57 57 313 256 65 321 131348508 5733003 137081511 cost_264_57_join0_0 cost_264_57_block2 rfl rfl rfl

private theorem cost_264_57_total : P1_7_1_3.momentEstimate 264 57 = 137081511 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 264 + 57 = 321 by decide]
  exact cost_264_57_join1_0

theorem moment264_57 : P1_7_1.groupedPoleMoment 264 57 ≤ 137081511 :=
  (P1_7_1_3.grouped_bound 264 57).trans_eq cost_264_57_total
private theorem cost_264_58_block0 : P1_7_1_3.blockEstimate 264 58 58 128 = 51570130 := by decide +kernel

private theorem cost_264_58_block1 : P1_7_1_3.blockEstimate 264 58 186 128 = 81365468 := by decide +kernel

private theorem cost_264_58_block2 : P1_7_1_3.blockEstimate 264 58 314 66 = 5983647 := by decide +kernel

private theorem cost_264_58_join0_0 : P1_7_1_3.blockEstimate 264 58 58 256 = 132935598 :=
  @P1_7_1_3.block_append 264 58 58 186 128 128 256 51570130 81365468 132935598 cost_264_58_block0 cost_264_58_block1 rfl rfl rfl

private theorem cost_264_58_join1_0 : P1_7_1_3.blockEstimate 264 58 58 322 = 138919245 :=
  @P1_7_1_3.block_append 264 58 58 314 256 66 322 132935598 5983647 138919245 cost_264_58_join0_0 cost_264_58_block2 rfl rfl rfl

private theorem cost_264_58_total : P1_7_1_3.momentEstimate 264 58 = 138919245 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 264 + 58 = 322 by decide]
  exact cost_264_58_join1_0

theorem moment264_58 : P1_7_1.groupedPoleMoment 264 58 ≤ 138919245 :=
  (P1_7_1_3.grouped_bound 264 58).trans_eq cost_264_58_total
private theorem cost_264_59_block0 : P1_7_1_3.blockEstimate 264 59 59 128 = 51955725 := by decide +kernel

private theorem cost_264_59_block1 : P1_7_1_3.blockEstimate 264 59 187 128 = 82549506 := by decide +kernel

private theorem cost_264_59_block2 : P1_7_1_3.blockEstimate 264 59 315 67 = 6241160 := by decide +kernel

private theorem cost_264_59_join0_0 : P1_7_1_3.blockEstimate 264 59 59 256 = 134505231 :=
  @P1_7_1_3.block_append 264 59 59 187 128 128 256 51955725 82549506 134505231 cost_264_59_block0 cost_264_59_block1 rfl rfl rfl

private theorem cost_264_59_join1_0 : P1_7_1_3.blockEstimate 264 59 59 323 = 140746391 :=
  @P1_7_1_3.block_append 264 59 59 315 256 67 323 134505231 6241160 140746391 cost_264_59_join0_0 cost_264_59_block2 rfl rfl rfl

private theorem cost_264_59_total : P1_7_1_3.momentEstimate 264 59 = 140746391 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 264 + 59 = 323 by decide]
  exact cost_264_59_join1_0

theorem moment264_59 : P1_7_1.groupedPoleMoment 264 59 ≤ 140746391 :=
  (P1_7_1_3.grouped_bound 264 59).trans_eq cost_264_59_total
private theorem cost_278_60_block0 : P1_7_1_3.blockEstimate 278 60 60 128 = 56604645 := by decide +kernel

private theorem cost_278_60_block1 : P1_7_1_3.blockEstimate 278 60 188 128 = 100036394 := by decide +kernel

private theorem cost_278_60_block2 : P1_7_1_3.blockEstimate 278 60 316 82 = 11597695 := by decide +kernel

private theorem cost_278_60_join0_0 : P1_7_1_3.blockEstimate 278 60 60 256 = 156641039 :=
  @P1_7_1_3.block_append 278 60 60 188 128 128 256 56604645 100036394 156641039 cost_278_60_block0 cost_278_60_block1 rfl rfl rfl

private theorem cost_278_60_join1_0 : P1_7_1_3.blockEstimate 278 60 60 338 = 168238734 :=
  @P1_7_1_3.block_append 278 60 60 316 256 82 338 156641039 11597695 168238734 cost_278_60_join0_0 cost_278_60_block2 rfl rfl rfl

private theorem cost_278_60_total : P1_7_1_3.momentEstimate 278 60 = 168238734 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 278 + 60 = 338 by decide]
  exact cost_278_60_join1_0

theorem moment278_60 : P1_7_1.groupedPoleMoment 278 60 ≤ 168238734 :=
  (P1_7_1_3.grouped_bound 278 60).trans_eq cost_278_60_total
private theorem cost_278_61_block0 : P1_7_1_3.blockEstimate 278 61 61 128 = 56998739 := by decide +kernel

private theorem cost_278_61_block1 : P1_7_1_3.blockEstimate 278 61 189 128 = 101388394 := by decide +kernel

private theorem cost_278_61_block2 : P1_7_1_3.blockEstimate 278 61 317 83 = 11996678 := by decide +kernel

private theorem cost_278_61_join0_0 : P1_7_1_3.blockEstimate 278 61 61 256 = 158387133 :=
  @P1_7_1_3.block_append 278 61 61 189 128 128 256 56998739 101388394 158387133 cost_278_61_block0 cost_278_61_block1 rfl rfl rfl

private theorem cost_278_61_join1_0 : P1_7_1_3.blockEstimate 278 61 61 339 = 170383811 :=
  @P1_7_1_3.block_append 278 61 61 317 256 83 339 158387133 11996678 170383811 cost_278_61_join0_0 cost_278_61_block2 rfl rfl rfl

private theorem cost_278_61_total : P1_7_1_3.momentEstimate 278 61 = 170383811 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 278 + 61 = 339 by decide]
  exact cost_278_61_join1_0

theorem moment278_61 : P1_7_1.groupedPoleMoment 278 61 ≤ 170383811 :=
  (P1_7_1_3.grouped_bound 278 61).trans_eq cost_278_61_total
private theorem cost_278_62_block0 : P1_7_1_3.blockEstimate 278 62 62 128 = 57380505 := by decide +kernel

private theorem cost_278_62_block1 : P1_7_1_3.blockEstimate 278 62 190 128 = 102732553 := by decide +kernel

private theorem cost_278_62_block2 : P1_7_1_3.blockEstimate 278 62 318 84 = 12404052 := by decide +kernel

private theorem cost_278_62_join0_0 : P1_7_1_3.blockEstimate 278 62 62 256 = 160113058 :=
  @P1_7_1_3.block_append 278 62 62 190 128 128 256 57380505 102732553 160113058 cost_278_62_block0 cost_278_62_block1 rfl rfl rfl

private theorem cost_278_62_join1_0 : P1_7_1_3.blockEstimate 278 62 62 340 = 172517110 :=
  @P1_7_1_3.block_append 278 62 62 318 256 84 340 160113058 12404052 172517110 cost_278_62_join0_0 cost_278_62_block2 rfl rfl rfl

private theorem cost_278_62_total : P1_7_1_3.momentEstimate 278 62 = 172517110 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 278 + 62 = 340 by decide]
  exact cost_278_62_join1_0

theorem moment278_62 : P1_7_1.groupedPoleMoment 278 62 ≤ 172517110 :=
  (P1_7_1_3.grouped_bound 278 62).trans_eq cost_278_62_total
private theorem cost_291_65_block0 : P1_7_1_3.blockEstimate 291 65 65 128 = 62563248 := by decide +kernel

private theorem cost_291_65_block1 : P1_7_1_3.blockEstimate 291 65 193 128 = 123415667 := by decide +kernel

private theorem cost_291_65_block2 : P1_7_1_3.blockEstimate 291 65 321 100 = 21114780 := by decide +kernel

private theorem cost_291_65_join0_0 : P1_7_1_3.blockEstimate 291 65 65 256 = 185978915 :=
  @P1_7_1_3.block_append 291 65 65 193 128 128 256 62563248 123415667 185978915 cost_291_65_block0 cost_291_65_block1 rfl rfl rfl

private theorem cost_291_65_join1_0 : P1_7_1_3.blockEstimate 291 65 65 356 = 207093695 :=
  @P1_7_1_3.block_append 291 65 65 321 256 100 356 185978915 21114780 207093695 cost_291_65_join0_0 cost_291_65_block2 rfl rfl rfl

private theorem cost_291_65_total : P1_7_1_3.momentEstimate 291 65 = 207093695 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 291 + 65 = 356 by decide]
  exact cost_291_65_join1_0

theorem moment291_65 : P1_7_1.groupedPoleMoment 291 65 ≤ 207093695 :=
  (P1_7_1_3.grouped_bound 291 65).trans_eq cost_291_65_total

end Research6966.HelperRescueCatalogue

end Merged6967_Near6967RescueMoment0

section Merged6967_Near6967RescueMoment1
set_option Elab.async false


set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem cost_293_62_block0 : P1_7_1_3.blockEstimate 293 62 62 128 = 62028330 := by decide +kernel

private theorem cost_293_62_block1 : P1_7_1_3.blockEstimate 293 62 190 128 = 121448284 := by decide +kernel

private theorem cost_293_62_block2 : P1_7_1_3.blockEstimate 293 62 318 99 = 20675316 := by decide +kernel

private theorem cost_293_62_join0_0 : P1_7_1_3.blockEstimate 293 62 62 256 = 183476614 :=
  @P1_7_1_3.block_append 293 62 62 190 128 128 256 62028330 121448284 183476614 cost_293_62_block0 cost_293_62_block1 rfl rfl rfl

private theorem cost_293_62_join1_0 : P1_7_1_3.blockEstimate 293 62 62 355 = 204151930 :=
  @P1_7_1_3.block_append 293 62 62 318 256 99 355 183476614 20675316 204151930 cost_293_62_join0_0 cost_293_62_block2 rfl rfl rfl

private theorem cost_293_62_total : P1_7_1_3.momentEstimate 293 62 = 204151930 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 293 + 62 = 355 by decide]
  exact cost_293_62_join1_0

theorem moment293_62 : P1_7_1.groupedPoleMoment 293 62 ≤ 204151930 :=
  (P1_7_1_3.grouped_bound 293 62).trans_eq cost_293_62_total
private theorem cost_293_63_block0 : P1_7_1_3.blockEstimate 293 63 63 128 = 62430160 := by decide +kernel

private theorem cost_293_63_block1 : P1_7_1_3.blockEstimate 293 63 191 128 = 122987755 := by decide +kernel

private theorem cost_293_63_block2 : P1_7_1_3.blockEstimate 293 63 319 100 = 21260869 := by decide +kernel

private theorem cost_293_63_join0_0 : P1_7_1_3.blockEstimate 293 63 63 256 = 185417915 :=
  @P1_7_1_3.block_append 293 63 63 191 128 128 256 62430160 122987755 185417915 cost_293_63_block0 cost_293_63_block1 rfl rfl rfl

private theorem cost_293_63_join1_0 : P1_7_1_3.blockEstimate 293 63 63 356 = 206678784 :=
  @P1_7_1_3.block_append 293 63 63 319 256 100 356 185417915 21260869 206678784 cost_293_63_join0_0 cost_293_63_block2 rfl rfl rfl

private theorem cost_293_63_total : P1_7_1_3.momentEstimate 293 63 = 206678784 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 293 + 63 = 356 by decide]
  exact cost_293_63_join1_0

theorem moment293_63 : P1_7_1.groupedPoleMoment 293 63 ≤ 206678784 :=
  (P1_7_1_3.grouped_bound 293 63).trans_eq cost_293_63_total
private theorem cost_293_65_block0 : P1_7_1_3.blockEstimate 293 65 65 128 = 63195440 := by decide +kernel

private theorem cost_293_65_block1 : P1_7_1_3.blockEstimate 293 65 193 128 = 126034530 := by decide +kernel

private theorem cost_293_65_block2 : P1_7_1_3.blockEstimate 293 65 321 102 = 22462264 := by decide +kernel

private theorem cost_293_65_join0_0 : P1_7_1_3.blockEstimate 293 65 65 256 = 189229970 :=
  @P1_7_1_3.block_append 293 65 65 193 128 128 256 63195440 126034530 189229970 cost_293_65_block0 cost_293_65_block1 rfl rfl rfl

private theorem cost_293_65_join1_0 : P1_7_1_3.blockEstimate 293 65 65 358 = 211692234 :=
  @P1_7_1_3.block_append 293 65 65 321 256 102 358 189229970 22462264 211692234 cost_293_65_join0_0 cost_293_65_block2 rfl rfl rfl

private theorem cost_293_65_total : P1_7_1_3.momentEstimate 293 65 = 211692234 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 293 + 65 = 358 by decide]
  exact cost_293_65_join1_0

theorem moment293_65 : P1_7_1.groupedPoleMoment 293 65 ≤ 211692234 :=
  (P1_7_1_3.grouped_bound 293 65).trans_eq cost_293_65_total
private theorem cost_313_68_block0 : P1_7_1_3.blockEstimate 313 68 68 128 = 70686245 := by decide +kernel

private theorem cost_313_68_block1 : P1_7_1_3.blockEstimate 313 68 196 128 = 158050180 := by decide +kernel

private theorem cost_313_68_block2 : P1_7_1_3.blockEstimate 313 68 324 125 = 42072670 := by decide +kernel

private theorem cost_313_68_join0_0 : P1_7_1_3.blockEstimate 313 68 68 256 = 228736425 :=
  @P1_7_1_3.block_append 313 68 68 196 128 128 256 70686245 158050180 228736425 cost_313_68_block0 cost_313_68_block1 rfl rfl rfl

private theorem cost_313_68_join1_0 : P1_7_1_3.blockEstimate 313 68 68 381 = 270809095 :=
  @P1_7_1_3.block_append 313 68 68 324 256 125 381 228736425 42072670 270809095 cost_313_68_join0_0 cost_313_68_block2 rfl rfl rfl

private theorem cost_313_68_total : P1_7_1_3.momentEstimate 313 68 = 270809095 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 313 + 68 = 381 by decide]
  exact cost_313_68_join1_0

theorem moment313_68 : P1_7_1.groupedPoleMoment 313 68 ≤ 270809095 :=
  (P1_7_1_3.grouped_bound 313 68).trans_eq cost_313_68_total
private theorem cost_313_69_block0 : P1_7_1_3.blockEstimate 313 69 69 128 = 71049685 := by decide +kernel

private theorem cost_313_69_block1 : P1_7_1_3.blockEstimate 313 69 197 128 = 159802762 := by decide +kernel

private theorem cost_313_69_block2 : P1_7_1_3.blockEstimate 313 69 325 126 = 43008236 := by decide +kernel

private theorem cost_313_69_join0_0 : P1_7_1_3.blockEstimate 313 69 69 256 = 230852447 :=
  @P1_7_1_3.block_append 313 69 69 197 128 128 256 71049685 159802762 230852447 cost_313_69_block0 cost_313_69_block1 rfl rfl rfl

private theorem cost_313_69_join1_0 : P1_7_1_3.blockEstimate 313 69 69 382 = 273860683 :=
  @P1_7_1_3.block_append 313 69 69 325 256 126 382 230852447 43008236 273860683 cost_313_69_join0_0 cost_313_69_block2 rfl rfl rfl

private theorem cost_313_69_total : P1_7_1_3.momentEstimate 313 69 = 273860683 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 313 + 69 = 382 by decide]
  exact cost_313_69_join1_0

theorem moment313_69 : P1_7_1.groupedPoleMoment 313 69 ≤ 273860683 :=
  (P1_7_1_3.grouped_bound 313 69).trans_eq cost_313_69_total
private theorem cost_313_70_block0 : P1_7_1_3.blockEstimate 313 70 70 128 = 71400440 := by decide +kernel

private theorem cost_313_70_block1 : P1_7_1_3.blockEstimate 313 70 198 128 = 161540851 := by decide +kernel

private theorem cost_313_70_block2 : P1_7_1_3.blockEstimate 313 70 326 127 = 43956136 := by decide +kernel

private theorem cost_313_70_join0_0 : P1_7_1_3.blockEstimate 313 70 70 256 = 232941291 :=
  @P1_7_1_3.block_append 313 70 70 198 128 128 256 71400440 161540851 232941291 cost_313_70_block0 cost_313_70_block1 rfl rfl rfl

private theorem cost_313_70_join1_0 : P1_7_1_3.blockEstimate 313 70 70 383 = 276897427 :=
  @P1_7_1_3.block_append 313 70 70 326 256 127 383 232941291 43956136 276897427 cost_313_70_join0_0 cost_313_70_block2 rfl rfl rfl

private theorem cost_313_70_total : P1_7_1_3.momentEstimate 313 70 = 276897427 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 313 + 70 = 383 by decide]
  exact cost_313_70_join1_0

theorem moment313_70 : P1_7_1.groupedPoleMoment 313 70 ≤ 276897427 :=
  (P1_7_1_3.grouped_bound 313 70).trans_eq cost_313_70_total
private theorem cost_314_68_block0 : P1_7_1_3.blockEstimate 314 68 68 128 = 71008015 := by decide +kernel

private theorem cost_314_68_block1 : P1_7_1_3.blockEstimate 314 68 196 128 = 159444372 := by decide +kernel

private theorem cost_314_68_block2 : P1_7_1_3.blockEstimate 314 68 324 126 = 43139593 := by decide +kernel

private theorem cost_314_68_join0_0 : P1_7_1_3.blockEstimate 314 68 68 256 = 230452387 :=
  @P1_7_1_3.block_append 314 68 68 196 128 128 256 71008015 159444372 230452387 cost_314_68_block0 cost_314_68_block1 rfl rfl rfl

private theorem cost_314_68_join1_0 : P1_7_1_3.blockEstimate 314 68 68 382 = 273591980 :=
  @P1_7_1_3.block_append 314 68 68 324 256 126 382 230452387 43139593 273591980 cost_314_68_join0_0 cost_314_68_block2 rfl rfl rfl

private theorem cost_314_68_total : P1_7_1_3.momentEstimate 314 68 = 273591980 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 314 + 68 = 382 by decide]
  exact cost_314_68_join1_0

theorem moment314_68 : P1_7_1.groupedPoleMoment 314 68 ≤ 273591980 :=
  (P1_7_1_3.grouped_bound 314 68).trans_eq cost_314_68_total
private theorem cost_314_70_block0 : P1_7_1_3.blockEstimate 314 70 70 128 = 71725691 := by decide +kernel

private theorem cost_314_70_block1 : P1_7_1_3.blockEstimate 314 70 198 128 = 162964329 := by decide +kernel

private theorem cost_314_70_block2 : P1_7_1_3.blockEstimate 314 70 326 128 = 45055217 := by decide +kernel

private theorem cost_314_70_join0_0 : P1_7_1_3.blockEstimate 314 70 70 256 = 234690020 :=
  @P1_7_1_3.block_append 314 70 70 198 128 128 256 71725691 162964329 234690020 cost_314_70_block0 cost_314_70_block1 rfl rfl rfl

private theorem cost_314_70_join1_0 : P1_7_1_3.blockEstimate 314 70 70 384 = 279745237 :=
  @P1_7_1_3.block_append 314 70 70 326 256 128 384 234690020 45055217 279745237 cost_314_70_join0_0 cost_314_70_block2 rfl rfl rfl

private theorem cost_314_70_total : P1_7_1_3.momentEstimate 314 70 = 279745237 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 314 + 70 = 384 by decide]
  exact cost_314_70_join1_0

theorem moment314_70 : P1_7_1.groupedPoleMoment 314 70 ≤ 279745237 :=
  (P1_7_1_3.grouped_bound 314 70).trans_eq cost_314_70_total
private theorem cost_331_74_block0 : P1_7_1_3.blockEstimate 331 74 74 128 = 78648925 := by decide +kernel

private theorem cost_331_74_block1 : P1_7_1_3.blockEstimate 331 74 202 128 = 195139200 := by decide +kernel

private theorem cost_331_74_block2 : P1_7_1_3.blockEstimate 331 74 330 128 = 71622738 := by decide +kernel

private theorem cost_331_74_block3 : P1_7_1_3.blockEstimate 331 74 458 21 = 304421 := by decide +kernel

private theorem cost_331_74_join0_0 : P1_7_1_3.blockEstimate 331 74 74 256 = 273788125 :=
  @P1_7_1_3.block_append 331 74 74 202 128 128 256 78648925 195139200 273788125 cost_331_74_block0 cost_331_74_block1 rfl rfl rfl

private theorem cost_331_74_join0_2 : P1_7_1_3.blockEstimate 331 74 330 149 = 71927159 :=
  @P1_7_1_3.block_append 331 74 330 458 128 21 149 71622738 304421 71927159 cost_331_74_block2 cost_331_74_block3 rfl rfl rfl

private theorem cost_331_74_join1_0 : P1_7_1_3.blockEstimate 331 74 74 405 = 345715284 :=
  @P1_7_1_3.block_append 331 74 74 330 256 149 405 273788125 71927159 345715284 cost_331_74_join0_0 cost_331_74_join0_2 rfl rfl rfl

private theorem cost_331_74_total : P1_7_1_3.momentEstimate 331 74 = 345715284 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 331 + 74 = 405 by decide]
  exact cost_331_74_join1_0

theorem moment331_74 : P1_7_1.groupedPoleMoment 331 74 ≤ 345715284 :=
  (P1_7_1_3.grouped_bound 331 74).trans_eq cost_331_74_total
private theorem cost_332_74_block0 : P1_7_1_3.blockEstimate 332 74 74 128 = 78980450 := by decide +kernel

private theorem cost_332_74_block1 : P1_7_1_3.blockEstimate 332 74 202 128 = 196632000 := by decide +kernel

private theorem cost_332_74_block2 : P1_7_1_3.blockEstimate 332 74 330 128 = 73117734 := by decide +kernel

private theorem cost_332_74_block3 : P1_7_1_3.blockEstimate 332 74 458 22 = 347475 := by decide +kernel

private theorem cost_332_74_join0_0 : P1_7_1_3.blockEstimate 332 74 74 256 = 275612450 :=
  @P1_7_1_3.block_append 332 74 74 202 128 128 256 78980450 196632000 275612450 cost_332_74_block0 cost_332_74_block1 rfl rfl rfl

private theorem cost_332_74_join0_2 : P1_7_1_3.blockEstimate 332 74 330 150 = 73465209 :=
  @P1_7_1_3.block_append 332 74 330 458 128 22 150 73117734 347475 73465209 cost_332_74_block2 cost_332_74_block3 rfl rfl rfl

private theorem cost_332_74_join1_0 : P1_7_1_3.blockEstimate 332 74 74 406 = 349077659 :=
  @P1_7_1_3.block_append 332 74 74 330 256 150 406 275612450 73465209 349077659 cost_332_74_join0_0 cost_332_74_join0_2 rfl rfl rfl

private theorem cost_332_74_total : P1_7_1_3.momentEstimate 332 74 = 349077659 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 332 + 74 = 406 by decide]
  exact cost_332_74_join1_0

theorem moment332_74 : P1_7_1.groupedPoleMoment 332 74 ≤ 349077659 :=
  (P1_7_1_3.grouped_bound 332 74).trans_eq cost_332_74_total
private theorem cost_346_76_block0 : P1_7_1_3.blockEstimate 346 76 76 128 = 84285201 := by decide +kernel

private theorem cost_346_76_block1 : P1_7_1_3.blockEstimate 346 76 204 128 = 221809280 := by decide +kernel

private theorem cost_346_76_block2 : P1_7_1_3.blockEstimate 346 76 332 128 = 98997050 := by decide +kernel

private theorem cost_346_76_block3 : P1_7_1_3.blockEstimate 346 76 460 38 = 1686965 := by decide +kernel

private theorem cost_346_76_join0_0 : P1_7_1_3.blockEstimate 346 76 76 256 = 306094481 :=
  @P1_7_1_3.block_append 346 76 76 204 128 128 256 84285201 221809280 306094481 cost_346_76_block0 cost_346_76_block1 rfl rfl rfl

private theorem cost_346_76_join0_2 : P1_7_1_3.blockEstimate 346 76 332 166 = 100684015 :=
  @P1_7_1_3.block_append 346 76 332 460 128 38 166 98997050 1686965 100684015 cost_346_76_block2 cost_346_76_block3 rfl rfl rfl

private theorem cost_346_76_join1_0 : P1_7_1_3.blockEstimate 346 76 76 422 = 406778496 :=
  @P1_7_1_3.block_append 346 76 76 332 256 166 422 306094481 100684015 406778496 cost_346_76_join0_0 cost_346_76_join0_2 rfl rfl rfl

private theorem cost_346_76_total : P1_7_1_3.momentEstimate 346 76 = 406778496 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 346 + 76 = 422 by decide]
  exact cost_346_76_join1_0

theorem moment346_76 : P1_7_1.groupedPoleMoment 346 76 ≤ 406778496 :=
  (P1_7_1_3.grouped_bound 346 76).trans_eq cost_346_76_total
private theorem cost_347_76_block0 : P1_7_1_3.blockEstimate 347 76 76 128 = 84619535 := by decide +kernel

private theorem cost_347_76_block1 : P1_7_1_3.blockEstimate 347 76 204 128 = 223332032 := by decide +kernel

private theorem cost_347_76_block2 : P1_7_1_3.blockEstimate 347 76 332 128 = 100788499 := by decide +kernel

private theorem cost_347_76_block3 : P1_7_1_3.blockEstimate 347 76 460 39 = 1821440 := by decide +kernel

private theorem cost_347_76_join0_0 : P1_7_1_3.blockEstimate 347 76 76 256 = 307951567 :=
  @P1_7_1_3.block_append 347 76 76 204 128 128 256 84619535 223332032 307951567 cost_347_76_block0 cost_347_76_block1 rfl rfl rfl

private theorem cost_347_76_join0_2 : P1_7_1_3.blockEstimate 347 76 332 167 = 102609939 :=
  @P1_7_1_3.block_append 347 76 332 460 128 39 167 100788499 1821440 102609939 cost_347_76_block2 cost_347_76_block3 rfl rfl rfl

private theorem cost_347_76_join1_0 : P1_7_1_3.blockEstimate 347 76 76 423 = 410561506 :=
  @P1_7_1_3.block_append 347 76 76 332 256 167 423 307951567 102609939 410561506 cost_347_76_join0_0 cost_347_76_join0_2 rfl rfl rfl

private theorem cost_347_76_total : P1_7_1_3.momentEstimate 347 76 = 410561506 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 347 + 76 = 423 by decide]
  exact cost_347_76_join1_0

theorem moment347_76 : P1_7_1.groupedPoleMoment 347 76 ≤ 410561506 :=
  (P1_7_1_3.grouped_bound 347 76).trans_eq cost_347_76_total

end Research6966.HelperRescueCatalogue

end Merged6967_Near6967RescueMoment1

section Merged6967_Near6967RescueMoment10
set_option Elab.async false


set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem cost_1046_228_block0 : P1_7_1_3.blockEstimate 1046 228 228 128 = 340140320 := by decide +kernel

private theorem cost_1046_228_block1 : P1_7_1_3.blockEstimate 1046 228 356 128 = 2075081231 := by decide +kernel

private theorem cost_1046_228_block2 : P1_7_1_3.blockEstimate 1046 228 484 128 = 4357433984 := by decide +kernel

private theorem cost_1046_228_block3 : P1_7_1_3.blockEstimate 1046 228 612 128 = 5828192896 := by decide +kernel

private theorem cost_1046_228_block4 : P1_7_1_3.blockEstimate 1046 228 740 128 = 6338456192 := by decide +kernel

private theorem cost_1046_228_block5 : P1_7_1_3.blockEstimate 1046 228 868 128 = 5888223872 := by decide +kernel

private theorem cost_1046_228_block6 : P1_7_1_3.blockEstimate 1046 228 996 128 = 4504729210 := by decide +kernel

private theorem cost_1046_228_block7 : P1_7_1_3.blockEstimate 1046 228 1124 128 = 2671811764 := by decide +kernel

private theorem cost_1046_228_block8 : P1_7_1_3.blockEstimate 1046 228 1252 128 = 1076380168 := by decide +kernel

private theorem cost_1046_228_block9 : P1_7_1_3.blockEstimate 1046 228 1380 122 = 155301692 := by decide +kernel

private theorem cost_1046_228_join0_0 : P1_7_1_3.blockEstimate 1046 228 228 256 = 2415221551 :=
  @P1_7_1_3.block_append 1046 228 228 356 128 128 256 340140320 2075081231 2415221551 cost_1046_228_block0 cost_1046_228_block1 rfl rfl rfl

private theorem cost_1046_228_join0_2 : P1_7_1_3.blockEstimate 1046 228 484 256 = 10185626880 :=
  @P1_7_1_3.block_append 1046 228 484 612 128 128 256 4357433984 5828192896 10185626880 cost_1046_228_block2 cost_1046_228_block3 rfl rfl rfl

private theorem cost_1046_228_join0_4 : P1_7_1_3.blockEstimate 1046 228 740 256 = 12226680064 :=
  @P1_7_1_3.block_append 1046 228 740 868 128 128 256 6338456192 5888223872 12226680064 cost_1046_228_block4 cost_1046_228_block5 rfl rfl rfl

private theorem cost_1046_228_join0_6 : P1_7_1_3.blockEstimate 1046 228 996 256 = 7176540974 :=
  @P1_7_1_3.block_append 1046 228 996 1124 128 128 256 4504729210 2671811764 7176540974 cost_1046_228_block6 cost_1046_228_block7 rfl rfl rfl

private theorem cost_1046_228_join0_8 : P1_7_1_3.blockEstimate 1046 228 1252 250 = 1231681860 :=
  @P1_7_1_3.block_append 1046 228 1252 1380 128 122 250 1076380168 155301692 1231681860 cost_1046_228_block8 cost_1046_228_block9 rfl rfl rfl

private theorem cost_1046_228_join1_0 : P1_7_1_3.blockEstimate 1046 228 228 512 = 12600848431 :=
  @P1_7_1_3.block_append 1046 228 228 484 256 256 512 2415221551 10185626880 12600848431 cost_1046_228_join0_0 cost_1046_228_join0_2 rfl rfl rfl

private theorem cost_1046_228_join1_2 : P1_7_1_3.blockEstimate 1046 228 740 512 = 19403221038 :=
  @P1_7_1_3.block_append 1046 228 740 996 256 256 512 12226680064 7176540974 19403221038 cost_1046_228_join0_4 cost_1046_228_join0_6 rfl rfl rfl

private theorem cost_1046_228_join2_0 : P1_7_1_3.blockEstimate 1046 228 228 1024 = 32004069469 :=
  @P1_7_1_3.block_append 1046 228 228 740 512 512 1024 12600848431 19403221038 32004069469 cost_1046_228_join1_0 cost_1046_228_join1_2 rfl rfl rfl

private theorem cost_1046_228_join3_0 : P1_7_1_3.blockEstimate 1046 228 228 1274 = 33235751329 :=
  @P1_7_1_3.block_append 1046 228 228 1252 1024 250 1274 32004069469 1231681860 33235751329 cost_1046_228_join2_0 cost_1046_228_join0_8 rfl rfl rfl

private theorem cost_1046_228_total : P1_7_1_3.momentEstimate 1046 228 = 33235751329 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1046 + 228 = 1274 by decide]
  exact cost_1046_228_join3_0

theorem moment1046_228 : P1_7_1.groupedPoleMoment 1046 228 ≤ 33235751329 :=
  (P1_7_1_3.grouped_bound 1046 228).trans_eq cost_1046_228_total
private theorem cost_1046_232_block0 : P1_7_1_3.blockEstimate 1046 232 232 128 = 340140320 := by decide +kernel

private theorem cost_1046_232_block1 : P1_7_1_3.blockEstimate 1046 232 360 128 = 2076163346 := by decide +kernel

private theorem cost_1046_232_block2 : P1_7_1_3.blockEstimate 1046 232 488 128 = 4390212096 := by decide +kernel

private theorem cost_1046_232_block3 : P1_7_1_3.blockEstimate 1046 232 616 128 = 5894296064 := by decide +kernel

private theorem cost_1046_232_block4 : P1_7_1_3.blockEstimate 1046 232 744 128 = 6421107200 := by decide +kernel

private theorem cost_1046_232_block5 : P1_7_1_3.blockEstimate 1046 232 872 128 = 5970645504 := by decide +kernel

private theorem cost_1046_232_block6 : P1_7_1_3.blockEstimate 1046 232 1000 128 = 4574352202 := by decide +kernel

private theorem cost_1046_232_block7 : P1_7_1_3.blockEstimate 1046 232 1128 128 = 2731403127 := by decide +kernel

private theorem cost_1046_232_block8 : P1_7_1_3.blockEstimate 1046 232 1256 128 = 1118229280 := by decide +kernel

private theorem cost_1046_232_block9 : P1_7_1_3.blockEstimate 1046 232 1384 126 = 170563184 := by decide +kernel

private theorem cost_1046_232_join0_0 : P1_7_1_3.blockEstimate 1046 232 232 256 = 2416303666 :=
  @P1_7_1_3.block_append 1046 232 232 360 128 128 256 340140320 2076163346 2416303666 cost_1046_232_block0 cost_1046_232_block1 rfl rfl rfl

private theorem cost_1046_232_join0_2 : P1_7_1_3.blockEstimate 1046 232 488 256 = 10284508160 :=
  @P1_7_1_3.block_append 1046 232 488 616 128 128 256 4390212096 5894296064 10284508160 cost_1046_232_block2 cost_1046_232_block3 rfl rfl rfl

private theorem cost_1046_232_join0_4 : P1_7_1_3.blockEstimate 1046 232 744 256 = 12391752704 :=
  @P1_7_1_3.block_append 1046 232 744 872 128 128 256 6421107200 5970645504 12391752704 cost_1046_232_block4 cost_1046_232_block5 rfl rfl rfl

private theorem cost_1046_232_join0_6 : P1_7_1_3.blockEstimate 1046 232 1000 256 = 7305755329 :=
  @P1_7_1_3.block_append 1046 232 1000 1128 128 128 256 4574352202 2731403127 7305755329 cost_1046_232_block6 cost_1046_232_block7 rfl rfl rfl

private theorem cost_1046_232_join0_8 : P1_7_1_3.blockEstimate 1046 232 1256 254 = 1288792464 :=
  @P1_7_1_3.block_append 1046 232 1256 1384 128 126 254 1118229280 170563184 1288792464 cost_1046_232_block8 cost_1046_232_block9 rfl rfl rfl

private theorem cost_1046_232_join1_0 : P1_7_1_3.blockEstimate 1046 232 232 512 = 12700811826 :=
  @P1_7_1_3.block_append 1046 232 232 488 256 256 512 2416303666 10284508160 12700811826 cost_1046_232_join0_0 cost_1046_232_join0_2 rfl rfl rfl

private theorem cost_1046_232_join1_2 : P1_7_1_3.blockEstimate 1046 232 744 512 = 19697508033 :=
  @P1_7_1_3.block_append 1046 232 744 1000 256 256 512 12391752704 7305755329 19697508033 cost_1046_232_join0_4 cost_1046_232_join0_6 rfl rfl rfl

private theorem cost_1046_232_join2_0 : P1_7_1_3.blockEstimate 1046 232 232 1024 = 32398319859 :=
  @P1_7_1_3.block_append 1046 232 232 744 512 512 1024 12700811826 19697508033 32398319859 cost_1046_232_join1_0 cost_1046_232_join1_2 rfl rfl rfl

private theorem cost_1046_232_join3_0 : P1_7_1_3.blockEstimate 1046 232 232 1278 = 33687112323 :=
  @P1_7_1_3.block_append 1046 232 232 1256 1024 254 1278 32398319859 1288792464 33687112323 cost_1046_232_join2_0 cost_1046_232_join0_8 rfl rfl rfl

private theorem cost_1046_232_total : P1_7_1_3.momentEstimate 1046 232 = 33687112323 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1046 + 232 = 1278 by decide]
  exact cost_1046_232_join3_0

theorem moment1046_232 : P1_7_1.groupedPoleMoment 1046 232 ≤ 33687112323 :=
  (P1_7_1_3.grouped_bound 1046 232).trans_eq cost_1046_232_total
private theorem cost_1047_228_block0 : P1_7_1_3.blockEstimate 1047 228 228 128 = 340498080 := by decide +kernel

private theorem cost_1047_228_block1 : P1_7_1_3.blockEstimate 1047 228 356 128 = 2077548873 := by decide +kernel

private theorem cost_1047_228_block2 : P1_7_1_3.blockEstimate 1047 228 484 128 = 4363486912 := by decide +kernel

private theorem cost_1047_228_block3 : P1_7_1_3.blockEstimate 1047 228 612 128 = 5837997760 := by decide +kernel

private theorem cost_1047_228_block4 : P1_7_1_3.blockEstimate 1047 228 740 128 = 6352012992 := by decide +kernel

private theorem cost_1047_228_block5 : P1_7_1_3.blockEstimate 1047 228 868 128 = 5905532608 := by decide +kernel

private theorem cost_1047_228_block6 : P1_7_1_3.blockEstimate 1047 228 996 128 = 4524759152 := by decide +kernel

private theorem cost_1047_228_block7 : P1_7_1_3.blockEstimate 1047 228 1124 128 = 2689091848 := by decide +kernel

private theorem cost_1047_228_block8 : P1_7_1_3.blockEstimate 1047 228 1252 128 = 1087912075 := by decide +kernel

private theorem cost_1047_228_block9 : P1_7_1_3.blockEstimate 1047 228 1380 123 = 159190673 := by decide +kernel

private theorem cost_1047_228_join0_0 : P1_7_1_3.blockEstimate 1047 228 228 256 = 2418046953 :=
  @P1_7_1_3.block_append 1047 228 228 356 128 128 256 340498080 2077548873 2418046953 cost_1047_228_block0 cost_1047_228_block1 rfl rfl rfl

private theorem cost_1047_228_join0_2 : P1_7_1_3.blockEstimate 1047 228 484 256 = 10201484672 :=
  @P1_7_1_3.block_append 1047 228 484 612 128 128 256 4363486912 5837997760 10201484672 cost_1047_228_block2 cost_1047_228_block3 rfl rfl rfl

private theorem cost_1047_228_join0_4 : P1_7_1_3.blockEstimate 1047 228 740 256 = 12257545600 :=
  @P1_7_1_3.block_append 1047 228 740 868 128 128 256 6352012992 5905532608 12257545600 cost_1047_228_block4 cost_1047_228_block5 rfl rfl rfl

private theorem cost_1047_228_join0_6 : P1_7_1_3.blockEstimate 1047 228 996 256 = 7213851000 :=
  @P1_7_1_3.block_append 1047 228 996 1124 128 128 256 4524759152 2689091848 7213851000 cost_1047_228_block6 cost_1047_228_block7 rfl rfl rfl

private theorem cost_1047_228_join0_8 : P1_7_1_3.blockEstimate 1047 228 1252 251 = 1247102748 :=
  @P1_7_1_3.block_append 1047 228 1252 1380 128 123 251 1087912075 159190673 1247102748 cost_1047_228_block8 cost_1047_228_block9 rfl rfl rfl

private theorem cost_1047_228_join1_0 : P1_7_1_3.blockEstimate 1047 228 228 512 = 12619531625 :=
  @P1_7_1_3.block_append 1047 228 228 484 256 256 512 2418046953 10201484672 12619531625 cost_1047_228_join0_0 cost_1047_228_join0_2 rfl rfl rfl

private theorem cost_1047_228_join1_2 : P1_7_1_3.blockEstimate 1047 228 740 512 = 19471396600 :=
  @P1_7_1_3.block_append 1047 228 740 996 256 256 512 12257545600 7213851000 19471396600 cost_1047_228_join0_4 cost_1047_228_join0_6 rfl rfl rfl

private theorem cost_1047_228_join2_0 : P1_7_1_3.blockEstimate 1047 228 228 1024 = 32090928225 :=
  @P1_7_1_3.block_append 1047 228 228 740 512 512 1024 12619531625 19471396600 32090928225 cost_1047_228_join1_0 cost_1047_228_join1_2 rfl rfl rfl

private theorem cost_1047_228_join3_0 : P1_7_1_3.blockEstimate 1047 228 228 1275 = 33338030973 :=
  @P1_7_1_3.block_append 1047 228 228 1252 1024 251 1275 32090928225 1247102748 33338030973 cost_1047_228_join2_0 cost_1047_228_join0_8 rfl rfl rfl

private theorem cost_1047_228_total : P1_7_1_3.momentEstimate 1047 228 = 33338030973 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1047 + 228 = 1275 by decide]
  exact cost_1047_228_join3_0

theorem moment1047_228 : P1_7_1.groupedPoleMoment 1047 228 ≤ 33338030973 :=
  (P1_7_1_3.grouped_bound 1047 228).trans_eq cost_1047_228_total
private theorem cost_1119_244_block0 : P1_7_1_3.blockEstimate 1119 244 244 128 = 366256800 := by decide +kernel

private theorem cost_1119_244_block1 : P1_7_1_3.blockEstimate 1119 244 372 128 = 2258152085 := by decide +kernel

private theorem cost_1119_244_block2 : P1_7_1_3.blockEstimate 1119 244 500 128 = 4934041280 := by decide +kernel

private theorem cost_1119_244_block3 : P1_7_1_3.blockEstimate 1119 244 628 128 = 6832701120 := by decide +kernel

private theorem cost_1119_244_block4 : P1_7_1_3.blockEstimate 1119 244 756 128 = 7703756480 := by decide +kernel

private theorem cost_1119_244_block5 : P1_7_1_3.blockEstimate 1119 244 884 128 = 7547207360 := by decide +kernel

private theorem cost_1119_244_block6 : P1_7_1_3.blockEstimate 1119 244 1012 128 = 6363593475 := by decide +kernel

private theorem cost_1119_244_block7 : P1_7_1_3.blockEstimate 1119 244 1140 128 = 4371223240 := by decide +kernel

private theorem cost_1119_244_block8 : P1_7_1_3.blockEstimate 1119 244 1268 128 = 2327348562 := by decide +kernel

private theorem cost_1119_244_block9 : P1_7_1_3.blockEstimate 1119 244 1396 128 = 761886432 := by decide +kernel

private theorem cost_1119_244_block10 : P1_7_1_3.blockEstimate 1119 244 1524 83 = 54326447 := by decide +kernel

private theorem cost_1119_244_join0_0 : P1_7_1_3.blockEstimate 1119 244 244 256 = 2624408885 :=
  @P1_7_1_3.block_append 1119 244 244 372 128 128 256 366256800 2258152085 2624408885 cost_1119_244_block0 cost_1119_244_block1 rfl rfl rfl

private theorem cost_1119_244_join0_2 : P1_7_1_3.blockEstimate 1119 244 500 256 = 11766742400 :=
  @P1_7_1_3.block_append 1119 244 500 628 128 128 256 4934041280 6832701120 11766742400 cost_1119_244_block2 cost_1119_244_block3 rfl rfl rfl

private theorem cost_1119_244_join0_4 : P1_7_1_3.blockEstimate 1119 244 756 256 = 15250963840 :=
  @P1_7_1_3.block_append 1119 244 756 884 128 128 256 7703756480 7547207360 15250963840 cost_1119_244_block4 cost_1119_244_block5 rfl rfl rfl

private theorem cost_1119_244_join0_6 : P1_7_1_3.blockEstimate 1119 244 1012 256 = 10734816715 :=
  @P1_7_1_3.block_append 1119 244 1012 1140 128 128 256 6363593475 4371223240 10734816715 cost_1119_244_block6 cost_1119_244_block7 rfl rfl rfl

private theorem cost_1119_244_join0_8 : P1_7_1_3.blockEstimate 1119 244 1268 256 = 3089234994 :=
  @P1_7_1_3.block_append 1119 244 1268 1396 128 128 256 2327348562 761886432 3089234994 cost_1119_244_block8 cost_1119_244_block9 rfl rfl rfl

private theorem cost_1119_244_join1_0 : P1_7_1_3.blockEstimate 1119 244 244 512 = 14391151285 :=
  @P1_7_1_3.block_append 1119 244 244 500 256 256 512 2624408885 11766742400 14391151285 cost_1119_244_join0_0 cost_1119_244_join0_2 rfl rfl rfl

private theorem cost_1119_244_join1_2 : P1_7_1_3.blockEstimate 1119 244 756 512 = 25985780555 :=
  @P1_7_1_3.block_append 1119 244 756 1012 256 256 512 15250963840 10734816715 25985780555 cost_1119_244_join0_4 cost_1119_244_join0_6 rfl rfl rfl

private theorem cost_1119_244_join1_4 : P1_7_1_3.blockEstimate 1119 244 1268 339 = 3143561441 :=
  @P1_7_1_3.block_append 1119 244 1268 1524 256 83 339 3089234994 54326447 3143561441 cost_1119_244_join0_8 cost_1119_244_block10 rfl rfl rfl

private theorem cost_1119_244_join2_0 : P1_7_1_3.blockEstimate 1119 244 244 1024 = 40376931840 :=
  @P1_7_1_3.block_append 1119 244 244 756 512 512 1024 14391151285 25985780555 40376931840 cost_1119_244_join1_0 cost_1119_244_join1_2 rfl rfl rfl

private theorem cost_1119_244_join3_0 : P1_7_1_3.blockEstimate 1119 244 244 1363 = 43520493281 :=
  @P1_7_1_3.block_append 1119 244 244 1268 1024 339 1363 40376931840 3143561441 43520493281 cost_1119_244_join2_0 cost_1119_244_join1_4 rfl rfl rfl

private theorem cost_1119_244_total : P1_7_1_3.momentEstimate 1119 244 = 43520493281 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1119 + 244 = 1363 by decide]
  exact cost_1119_244_join3_0

theorem moment1119_244 : P1_7_1.groupedPoleMoment 1119 244 ≤ 43520493281 :=
  (P1_7_1_3.grouped_bound 1119 244).trans_eq cost_1119_244_total
private theorem cost_1119_246_block0 : P1_7_1_3.blockEstimate 1119 246 246 128 = 366256800 := by decide +kernel

private theorem cost_1119_246_block1 : P1_7_1_3.blockEstimate 1119 246 374 128 = 2258257014 := by decide +kernel

private theorem cost_1119_246_block2 : P1_7_1_3.blockEstimate 1119 246 502 128 = 4949042176 := by decide +kernel

private theorem cost_1119_246_block3 : P1_7_1_3.blockEstimate 1119 246 630 128 = 6867248128 := by decide +kernel

private theorem cost_1119_246_block4 : P1_7_1_3.blockEstimate 1119 246 758 128 = 7749460992 := by decide +kernel

private theorem cost_1119_246_block5 : P1_7_1_3.blockEstimate 1119 246 886 128 = 7595680768 := by decide +kernel

private theorem cost_1119_246_block6 : P1_7_1_3.blockEstimate 1119 246 1014 128 = 6406610796 := by decide +kernel

private theorem cost_1119_246_block7 : P1_7_1_3.blockEstimate 1119 246 1142 128 = 4408328618 := by decide +kernel

private theorem cost_1119_246_block8 : P1_7_1_3.blockEstimate 1119 246 1270 128 = 2357550166 := by decide +kernel

private theorem cost_1119_246_block9 : P1_7_1_3.blockEstimate 1119 246 1398 128 = 780480016 := by decide +kernel

private theorem cost_1119_246_block10 : P1_7_1_3.blockEstimate 1119 246 1526 85 = 58226069 := by decide +kernel

private theorem cost_1119_246_join0_0 : P1_7_1_3.blockEstimate 1119 246 246 256 = 2624513814 :=
  @P1_7_1_3.block_append 1119 246 246 374 128 128 256 366256800 2258257014 2624513814 cost_1119_246_block0 cost_1119_246_block1 rfl rfl rfl

private theorem cost_1119_246_join0_2 : P1_7_1_3.blockEstimate 1119 246 502 256 = 11816290304 :=
  @P1_7_1_3.block_append 1119 246 502 630 128 128 256 4949042176 6867248128 11816290304 cost_1119_246_block2 cost_1119_246_block3 rfl rfl rfl

private theorem cost_1119_246_join0_4 : P1_7_1_3.blockEstimate 1119 246 758 256 = 15345141760 :=
  @P1_7_1_3.block_append 1119 246 758 886 128 128 256 7749460992 7595680768 15345141760 cost_1119_246_block4 cost_1119_246_block5 rfl rfl rfl

private theorem cost_1119_246_join0_6 : P1_7_1_3.blockEstimate 1119 246 1014 256 = 10814939414 :=
  @P1_7_1_3.block_append 1119 246 1014 1142 128 128 256 6406610796 4408328618 10814939414 cost_1119_246_block6 cost_1119_246_block7 rfl rfl rfl

private theorem cost_1119_246_join0_8 : P1_7_1_3.blockEstimate 1119 246 1270 256 = 3138030182 :=
  @P1_7_1_3.block_append 1119 246 1270 1398 128 128 256 2357550166 780480016 3138030182 cost_1119_246_block8 cost_1119_246_block9 rfl rfl rfl

private theorem cost_1119_246_join1_0 : P1_7_1_3.blockEstimate 1119 246 246 512 = 14440804118 :=
  @P1_7_1_3.block_append 1119 246 246 502 256 256 512 2624513814 11816290304 14440804118 cost_1119_246_join0_0 cost_1119_246_join0_2 rfl rfl rfl

private theorem cost_1119_246_join1_2 : P1_7_1_3.blockEstimate 1119 246 758 512 = 26160081174 :=
  @P1_7_1_3.block_append 1119 246 758 1014 256 256 512 15345141760 10814939414 26160081174 cost_1119_246_join0_4 cost_1119_246_join0_6 rfl rfl rfl

private theorem cost_1119_246_join1_4 : P1_7_1_3.blockEstimate 1119 246 1270 341 = 3196256251 :=
  @P1_7_1_3.block_append 1119 246 1270 1526 256 85 341 3138030182 58226069 3196256251 cost_1119_246_join0_8 cost_1119_246_block10 rfl rfl rfl

private theorem cost_1119_246_join2_0 : P1_7_1_3.blockEstimate 1119 246 246 1024 = 40600885292 :=
  @P1_7_1_3.block_append 1119 246 246 758 512 512 1024 14440804118 26160081174 40600885292 cost_1119_246_join1_0 cost_1119_246_join1_2 rfl rfl rfl

private theorem cost_1119_246_join3_0 : P1_7_1_3.blockEstimate 1119 246 246 1365 = 43797141543 :=
  @P1_7_1_3.block_append 1119 246 246 1270 1024 341 1365 40600885292 3196256251 43797141543 cost_1119_246_join2_0 cost_1119_246_join1_4 rfl rfl rfl

private theorem cost_1119_246_total : P1_7_1_3.momentEstimate 1119 246 = 43797141543 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1119 + 246 = 1365 by decide]
  exact cost_1119_246_join3_0

theorem moment1119_246 : P1_7_1.groupedPoleMoment 1119 246 ≤ 43797141543 :=
  (P1_7_1_3.grouped_bound 1119 246).trans_eq cost_1119_246_total
private theorem cost_1119_248_block0 : P1_7_1_3.blockEstimate 1119 248 248 128 = 366256800 := by decide +kernel

private theorem cost_1119_248_block1 : P1_7_1_3.blockEstimate 1119 248 376 128 = 2258327202 := by decide +kernel

private theorem cost_1119_248_block2 : P1_7_1_3.blockEstimate 1119 248 504 128 = 4963633728 := by decide +kernel

private theorem cost_1119_248_block3 : P1_7_1_3.blockEstimate 1119 248 632 128 = 6901451328 := by decide +kernel

private theorem cost_1119_248_block4 : P1_7_1_3.blockEstimate 1119 248 760 128 = 7794887232 := by decide +kernel

private theorem cost_1119_248_block5 : P1_7_1_3.blockEstimate 1119 248 888 128 = 7643941440 := by decide +kernel

private theorem cost_1119_248_block6 : P1_7_1_3.blockEstimate 1119 248 1016 128 = 6449510614 := by decide +kernel

private theorem cost_1119_248_block7 : P1_7_1_3.blockEstimate 1119 248 1144 128 = 4445518783 := by decide +kernel

private theorem cost_1119_248_block8 : P1_7_1_3.blockEstimate 1119 248 1272 128 = 2387903743 := by decide +kernel

private theorem cost_1119_248_block9 : P1_7_1_3.blockEstimate 1119 248 1400 128 = 799288192 := by decide +kernel

private theorem cost_1119_248_block10 : P1_7_1_3.blockEstimate 1119 248 1528 87 = 62305496 := by decide +kernel

private theorem cost_1119_248_join0_0 : P1_7_1_3.blockEstimate 1119 248 248 256 = 2624584002 :=
  @P1_7_1_3.block_append 1119 248 248 376 128 128 256 366256800 2258327202 2624584002 cost_1119_248_block0 cost_1119_248_block1 rfl rfl rfl

private theorem cost_1119_248_join0_2 : P1_7_1_3.blockEstimate 1119 248 504 256 = 11865085056 :=
  @P1_7_1_3.block_append 1119 248 504 632 128 128 256 4963633728 6901451328 11865085056 cost_1119_248_block2 cost_1119_248_block3 rfl rfl rfl

private theorem cost_1119_248_join0_4 : P1_7_1_3.blockEstimate 1119 248 760 256 = 15438828672 :=
  @P1_7_1_3.block_append 1119 248 760 888 128 128 256 7794887232 7643941440 15438828672 cost_1119_248_block4 cost_1119_248_block5 rfl rfl rfl

private theorem cost_1119_248_join0_6 : P1_7_1_3.blockEstimate 1119 248 1016 256 = 10895029397 :=
  @P1_7_1_3.block_append 1119 248 1016 1144 128 128 256 6449510614 4445518783 10895029397 cost_1119_248_block6 cost_1119_248_block7 rfl rfl rfl

private theorem cost_1119_248_join0_8 : P1_7_1_3.blockEstimate 1119 248 1272 256 = 3187191935 :=
  @P1_7_1_3.block_append 1119 248 1272 1400 128 128 256 2387903743 799288192 3187191935 cost_1119_248_block8 cost_1119_248_block9 rfl rfl rfl

private theorem cost_1119_248_join1_0 : P1_7_1_3.blockEstimate 1119 248 248 512 = 14489669058 :=
  @P1_7_1_3.block_append 1119 248 248 504 256 256 512 2624584002 11865085056 14489669058 cost_1119_248_join0_0 cost_1119_248_join0_2 rfl rfl rfl

private theorem cost_1119_248_join1_2 : P1_7_1_3.blockEstimate 1119 248 760 512 = 26333858069 :=
  @P1_7_1_3.block_append 1119 248 760 1016 256 256 512 15438828672 10895029397 26333858069 cost_1119_248_join0_4 cost_1119_248_join0_6 rfl rfl rfl

private theorem cost_1119_248_join1_4 : P1_7_1_3.blockEstimate 1119 248 1272 343 = 3249497431 :=
  @P1_7_1_3.block_append 1119 248 1272 1528 256 87 343 3187191935 62305496 3249497431 cost_1119_248_join0_8 cost_1119_248_block10 rfl rfl rfl

private theorem cost_1119_248_join2_0 : P1_7_1_3.blockEstimate 1119 248 248 1024 = 40823527127 :=
  @P1_7_1_3.block_append 1119 248 248 760 512 512 1024 14489669058 26333858069 40823527127 cost_1119_248_join1_0 cost_1119_248_join1_2 rfl rfl rfl

private theorem cost_1119_248_join3_0 : P1_7_1_3.blockEstimate 1119 248 248 1367 = 44073024558 :=
  @P1_7_1_3.block_append 1119 248 248 1272 1024 343 1367 40823527127 3249497431 44073024558 cost_1119_248_join2_0 cost_1119_248_join1_4 rfl rfl rfl

private theorem cost_1119_248_total : P1_7_1_3.momentEstimate 1119 248 = 44073024558 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1119 + 248 = 1367 by decide]
  exact cost_1119_248_join3_0

theorem moment1119_248 : P1_7_1.groupedPoleMoment 1119 248 ≤ 44073024558 :=
  (P1_7_1_3.grouped_bound 1119 248).trans_eq cost_1119_248_total
private theorem cost_1119_250_block0 : P1_7_1_3.blockEstimate 1119 250 250 128 = 366256800 := by decide +kernel

private theorem cost_1119_250_block1 : P1_7_1_3.blockEstimate 1119 250 378 128 = 2258369629 := by decide +kernel

private theorem cost_1119_250_block2 : P1_7_1_3.blockEstimate 1119 250 506 128 = 4977815936 := by decide +kernel

private theorem cost_1119_250_block3 : P1_7_1_3.blockEstimate 1119 250 634 128 = 6935310720 := by decide +kernel

private theorem cost_1119_250_block4 : P1_7_1_3.blockEstimate 1119 250 762 128 = 7840035200 := by decide +kernel

private theorem cost_1119_250_block5 : P1_7_1_3.blockEstimate 1119 250 890 128 = 7691989376 := by decide +kernel

private theorem cost_1119_250_block6 : P1_7_1_3.blockEstimate 1119 250 1018 128 = 6492295278 := by decide +kernel

private theorem cost_1119_250_block7 : P1_7_1_3.blockEstimate 1119 250 1146 128 = 4482792848 := by decide +kernel

private theorem cost_1119_250_block8 : P1_7_1_3.blockEstimate 1119 250 1274 128 = 2418408321 := by decide +kernel

private theorem cost_1119_250_block9 : P1_7_1_3.blockEstimate 1119 250 1402 128 = 818309968 := by decide +kernel

private theorem cost_1119_250_block10 : P1_7_1_3.blockEstimate 1119 250 1530 89 = 66568532 := by decide +kernel

private theorem cost_1119_250_join0_0 : P1_7_1_3.blockEstimate 1119 250 250 256 = 2624626429 :=
  @P1_7_1_3.block_append 1119 250 250 378 128 128 256 366256800 2258369629 2624626429 cost_1119_250_block0 cost_1119_250_block1 rfl rfl rfl

private theorem cost_1119_250_join0_2 : P1_7_1_3.blockEstimate 1119 250 506 256 = 11913126656 :=
  @P1_7_1_3.block_append 1119 250 506 634 128 128 256 4977815936 6935310720 11913126656 cost_1119_250_block2 cost_1119_250_block3 rfl rfl rfl

private theorem cost_1119_250_join0_4 : P1_7_1_3.blockEstimate 1119 250 762 256 = 15532024576 :=
  @P1_7_1_3.block_append 1119 250 762 890 128 128 256 7840035200 7691989376 15532024576 cost_1119_250_block4 cost_1119_250_block5 rfl rfl rfl

private theorem cost_1119_250_join0_6 : P1_7_1_3.blockEstimate 1119 250 1018 256 = 10975088126 :=
  @P1_7_1_3.block_append 1119 250 1018 1146 128 128 256 6492295278 4482792848 10975088126 cost_1119_250_block6 cost_1119_250_block7 rfl rfl rfl

private theorem cost_1119_250_join0_8 : P1_7_1_3.blockEstimate 1119 250 1274 256 = 3236718289 :=
  @P1_7_1_3.block_append 1119 250 1274 1402 128 128 256 2418408321 818309968 3236718289 cost_1119_250_block8 cost_1119_250_block9 rfl rfl rfl

private theorem cost_1119_250_join1_0 : P1_7_1_3.blockEstimate 1119 250 250 512 = 14537753085 :=
  @P1_7_1_3.block_append 1119 250 250 506 256 256 512 2624626429 11913126656 14537753085 cost_1119_250_join0_0 cost_1119_250_join0_2 rfl rfl rfl

private theorem cost_1119_250_join1_2 : P1_7_1_3.blockEstimate 1119 250 762 512 = 26507112702 :=
  @P1_7_1_3.block_append 1119 250 762 1018 256 256 512 15532024576 10975088126 26507112702 cost_1119_250_join0_4 cost_1119_250_join0_6 rfl rfl rfl

private theorem cost_1119_250_join1_4 : P1_7_1_3.blockEstimate 1119 250 1274 345 = 3303286821 :=
  @P1_7_1_3.block_append 1119 250 1274 1530 256 89 345 3236718289 66568532 3303286821 cost_1119_250_join0_8 cost_1119_250_block10 rfl rfl rfl

private theorem cost_1119_250_join2_0 : P1_7_1_3.blockEstimate 1119 250 250 1024 = 41044865787 :=
  @P1_7_1_3.block_append 1119 250 250 762 512 512 1024 14537753085 26507112702 41044865787 cost_1119_250_join1_0 cost_1119_250_join1_2 rfl rfl rfl

private theorem cost_1119_250_join3_0 : P1_7_1_3.blockEstimate 1119 250 250 1369 = 44348152608 :=
  @P1_7_1_3.block_append 1119 250 250 1274 1024 345 1369 41044865787 3303286821 44348152608 cost_1119_250_join2_0 cost_1119_250_join1_4 rfl rfl rfl

private theorem cost_1119_250_total : P1_7_1_3.momentEstimate 1119 250 = 44348152608 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1119 + 250 = 1369 by decide]
  exact cost_1119_250_join3_0

theorem moment1119_250 : P1_7_1.groupedPoleMoment 1119 250 ≤ 44348152608 :=
  (P1_7_1_3.grouped_bound 1119 250).trans_eq cost_1119_250_total
private theorem cost_1120_239_block0 : P1_7_1_3.blockEstimate 1120 239 239 128 = 366614560 := by decide +kernel

private theorem cost_1120_239_block1 : P1_7_1_3.blockEstimate 1120 239 367 128 = 2260162300 := by decide +kernel

private theorem cost_1120_239_block2 : P1_7_1_3.blockEstimate 1120 239 495 128 = 4900922880 := by decide +kernel

private theorem cost_1120_239_block3 : P1_7_1_3.blockEstimate 1120 239 623 128 = 6754936320 := by decide +kernel

private theorem cost_1120_239_block4 : P1_7_1_3.blockEstimate 1120 239 751 128 = 7602316800 := by decide +kernel

private theorem cost_1120_239_block5 : P1_7_1_3.blockEstimate 1120 239 879 128 = 7443064320 := by decide +kernel

private theorem cost_1120_239_block6 : P1_7_1_3.blockEstimate 1120 239 1007 128 = 6277381684 := by decide +kernel

private theorem cost_1120_239_block7 : P1_7_1_3.blockEstimate 1120 239 1135 128 = 4300576694 := by decide +kernel

private theorem cost_1120_239_block8 : P1_7_1_3.blockEstimate 1120 239 1263 128 = 2269447726 := by decide +kernel

private theorem cost_1120_239_block9 : P1_7_1_3.blockEstimate 1120 239 1391 128 = 726058656 := by decide +kernel

private theorem cost_1120_239_block10 : P1_7_1_3.blockEstimate 1120 239 1519 79 = 47094660 := by decide +kernel

private theorem cost_1120_239_join0_0 : P1_7_1_3.blockEstimate 1120 239 239 256 = 2626776860 :=
  @P1_7_1_3.block_append 1120 239 239 367 128 128 256 366614560 2260162300 2626776860 cost_1120_239_block0 cost_1120_239_block1 rfl rfl rfl

private theorem cost_1120_239_join0_2 : P1_7_1_3.blockEstimate 1120 239 495 256 = 11655859200 :=
  @P1_7_1_3.block_append 1120 239 495 623 128 128 256 4900922880 6754936320 11655859200 cost_1120_239_block2 cost_1120_239_block3 rfl rfl rfl

private theorem cost_1120_239_join0_4 : P1_7_1_3.blockEstimate 1120 239 751 256 = 15045381120 :=
  @P1_7_1_3.block_append 1120 239 751 879 128 128 256 7602316800 7443064320 15045381120 cost_1120_239_block4 cost_1120_239_block5 rfl rfl rfl

private theorem cost_1120_239_join0_6 : P1_7_1_3.blockEstimate 1120 239 1007 256 = 10577958378 :=
  @P1_7_1_3.block_append 1120 239 1007 1135 128 128 256 6277381684 4300576694 10577958378 cost_1120_239_block6 cost_1120_239_block7 rfl rfl rfl

private theorem cost_1120_239_join0_8 : P1_7_1_3.blockEstimate 1120 239 1263 256 = 2995506382 :=
  @P1_7_1_3.block_append 1120 239 1263 1391 128 128 256 2269447726 726058656 2995506382 cost_1120_239_block8 cost_1120_239_block9 rfl rfl rfl

private theorem cost_1120_239_join1_0 : P1_7_1_3.blockEstimate 1120 239 239 512 = 14282636060 :=
  @P1_7_1_3.block_append 1120 239 239 495 256 256 512 2626776860 11655859200 14282636060 cost_1120_239_join0_0 cost_1120_239_join0_2 rfl rfl rfl

private theorem cost_1120_239_join1_2 : P1_7_1_3.blockEstimate 1120 239 751 512 = 25623339498 :=
  @P1_7_1_3.block_append 1120 239 751 1007 256 256 512 15045381120 10577958378 25623339498 cost_1120_239_join0_4 cost_1120_239_join0_6 rfl rfl rfl

private theorem cost_1120_239_join1_4 : P1_7_1_3.blockEstimate 1120 239 1263 335 = 3042601042 :=
  @P1_7_1_3.block_append 1120 239 1263 1519 256 79 335 2995506382 47094660 3042601042 cost_1120_239_join0_8 cost_1120_239_block10 rfl rfl rfl

private theorem cost_1120_239_join2_0 : P1_7_1_3.blockEstimate 1120 239 239 1024 = 39905975558 :=
  @P1_7_1_3.block_append 1120 239 239 751 512 512 1024 14282636060 25623339498 39905975558 cost_1120_239_join1_0 cost_1120_239_join1_2 rfl rfl rfl

private theorem cost_1120_239_join3_0 : P1_7_1_3.blockEstimate 1120 239 239 1359 = 42948576600 :=
  @P1_7_1_3.block_append 1120 239 239 1263 1024 335 1359 39905975558 3042601042 42948576600 cost_1120_239_join2_0 cost_1120_239_join1_4 rfl rfl rfl

private theorem cost_1120_239_total : P1_7_1_3.momentEstimate 1120 239 = 42948576600 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1120 + 239 = 1359 by decide]
  exact cost_1120_239_join3_0

theorem moment1120_239 : P1_7_1.groupedPoleMoment 1120 239 ≤ 42948576600 :=
  (P1_7_1_3.grouped_bound 1120 239).trans_eq cost_1120_239_total
private theorem cost_1120_242_block0 : P1_7_1_3.blockEstimate 1120 242 242 128 = 366614560 := by decide +kernel

private theorem cost_1120_242_block1 : P1_7_1_3.blockEstimate 1120 242 370 128 = 2260476260 := by decide +kernel

private theorem cost_1120_242_block2 : P1_7_1_3.blockEstimate 1120 242 498 128 = 4924836288 := by decide +kernel

private theorem cost_1120_242_block3 : P1_7_1_3.blockEstimate 1120 242 626 128 = 6807996864 := by decide +kernel

private theorem cost_1120_242_block4 : P1_7_1_3.blockEstimate 1120 242 754 128 = 7671941568 := by decide +kernel

private theorem cost_1120_242_block5 : P1_7_1_3.blockEstimate 1120 242 882 128 = 7516670400 := by decide +kernel

private theorem cost_1120_242_block6 : P1_7_1_3.blockEstimate 1120 242 1010 128 = 6342527670 := by decide +kernel

private theorem cost_1120_242_block7 : P1_7_1_3.blockEstimate 1120 242 1138 128 = 4356077829 := by decide +kernel

private theorem cost_1120_242_block8 : P1_7_1_3.blockEstimate 1120 242 1266 128 = 2314394284 := by decide +kernel

private theorem cost_1120_242_block9 : P1_7_1_3.blockEstimate 1120 242 1394 128 = 753410288 := by decide +kernel

private theorem cost_1120_242_block10 : P1_7_1_3.blockEstimate 1120 242 1522 82 = 52491229 := by decide +kernel

private theorem cost_1120_242_join0_0 : P1_7_1_3.blockEstimate 1120 242 242 256 = 2627090820 :=
  @P1_7_1_3.block_append 1120 242 242 370 128 128 256 366614560 2260476260 2627090820 cost_1120_242_block0 cost_1120_242_block1 rfl rfl rfl

private theorem cost_1120_242_join0_2 : P1_7_1_3.blockEstimate 1120 242 498 256 = 11732833152 :=
  @P1_7_1_3.block_append 1120 242 498 626 128 128 256 4924836288 6807996864 11732833152 cost_1120_242_block2 cost_1120_242_block3 rfl rfl rfl

private theorem cost_1120_242_join0_4 : P1_7_1_3.blockEstimate 1120 242 754 256 = 15188611968 :=
  @P1_7_1_3.block_append 1120 242 754 882 128 128 256 7671941568 7516670400 15188611968 cost_1120_242_block4 cost_1120_242_block5 rfl rfl rfl

private theorem cost_1120_242_join0_6 : P1_7_1_3.blockEstimate 1120 242 1010 256 = 10698605499 :=
  @P1_7_1_3.block_append 1120 242 1010 1138 128 128 256 6342527670 4356077829 10698605499 cost_1120_242_block6 cost_1120_242_block7 rfl rfl rfl

private theorem cost_1120_242_join0_8 : P1_7_1_3.blockEstimate 1120 242 1266 256 = 3067804572 :=
  @P1_7_1_3.block_append 1120 242 1266 1394 128 128 256 2314394284 753410288 3067804572 cost_1120_242_block8 cost_1120_242_block9 rfl rfl rfl

private theorem cost_1120_242_join1_0 : P1_7_1_3.blockEstimate 1120 242 242 512 = 14359923972 :=
  @P1_7_1_3.block_append 1120 242 242 498 256 256 512 2627090820 11732833152 14359923972 cost_1120_242_join0_0 cost_1120_242_join0_2 rfl rfl rfl

private theorem cost_1120_242_join1_2 : P1_7_1_3.blockEstimate 1120 242 754 512 = 25887217467 :=
  @P1_7_1_3.block_append 1120 242 754 1010 256 256 512 15188611968 10698605499 25887217467 cost_1120_242_join0_4 cost_1120_242_join0_6 rfl rfl rfl

private theorem cost_1120_242_join1_4 : P1_7_1_3.blockEstimate 1120 242 1266 338 = 3120295801 :=
  @P1_7_1_3.block_append 1120 242 1266 1522 256 82 338 3067804572 52491229 3120295801 cost_1120_242_join0_8 cost_1120_242_block10 rfl rfl rfl

private theorem cost_1120_242_join2_0 : P1_7_1_3.blockEstimate 1120 242 242 1024 = 40247141439 :=
  @P1_7_1_3.block_append 1120 242 242 754 512 512 1024 14359923972 25887217467 40247141439 cost_1120_242_join1_0 cost_1120_242_join1_2 rfl rfl rfl

private theorem cost_1120_242_join3_0 : P1_7_1_3.blockEstimate 1120 242 242 1362 = 43367437240 :=
  @P1_7_1_3.block_append 1120 242 242 1266 1024 338 1362 40247141439 3120295801 43367437240 cost_1120_242_join2_0 cost_1120_242_join1_4 rfl rfl rfl

private theorem cost_1120_242_total : P1_7_1_3.momentEstimate 1120 242 = 43367437240 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1120 + 242 = 1362 by decide]
  exact cost_1120_242_join3_0

theorem moment1120_242 : P1_7_1.groupedPoleMoment 1120 242 ≤ 43367437240 :=
  (P1_7_1_3.grouped_bound 1120 242).trans_eq cost_1120_242_total
private theorem cost_1120_244_block0 : P1_7_1_3.blockEstimate 1120 244 244 128 = 366614560 := by decide +kernel

private theorem cost_1120_244_block1 : P1_7_1_3.blockEstimate 1120 244 372 128 = 2260623095 := by decide +kernel

private theorem cost_1120_244_block2 : P1_7_1_3.blockEstimate 1120 244 500 128 = 4940266240 := by decide +kernel

private theorem cost_1120_244_block3 : P1_7_1_3.blockEstimate 1120 244 628 128 = 6842940160 := by decide +kernel

private theorem cost_1120_244_block4 : P1_7_1_3.blockEstimate 1120 244 756 128 = 7718009600 := by decide +kernel

private theorem cost_1120_244_block5 : P1_7_1_3.blockEstimate 1120 244 884 128 = 7565474560 := by decide +kernel

private theorem cost_1120_244_block6 : P1_7_1_3.blockEstimate 1120 244 1012 128 = 6385802705 := by decide +kernel

private theorem cost_1120_244_block7 : P1_7_1_3.blockEstimate 1120 244 1140 128 = 4393186715 := by decide +kernel

private theorem cost_1120_244_block8 : P1_7_1_3.blockEstimate 1120 244 1268 128 = 2344550921 := by decide +kernel

private theorem cost_1120_244_block9 : P1_7_1_3.blockEstimate 1120 244 1396 128 = 771915232 := by decide +kernel

private theorem cost_1120_244_block10 : P1_7_1_3.blockEstimate 1120 244 1524 84 = 56305963 := by decide +kernel

private theorem cost_1120_244_join0_0 : P1_7_1_3.blockEstimate 1120 244 244 256 = 2627237655 :=
  @P1_7_1_3.block_append 1120 244 244 372 128 128 256 366614560 2260623095 2627237655 cost_1120_244_block0 cost_1120_244_block1 rfl rfl rfl

private theorem cost_1120_244_join0_2 : P1_7_1_3.blockEstimate 1120 244 500 256 = 11783206400 :=
  @P1_7_1_3.block_append 1120 244 500 628 128 128 256 4940266240 6842940160 11783206400 cost_1120_244_block2 cost_1120_244_block3 rfl rfl rfl

private theorem cost_1120_244_join0_4 : P1_7_1_3.blockEstimate 1120 244 756 256 = 15283484160 :=
  @P1_7_1_3.block_append 1120 244 756 884 128 128 256 7718009600 7565474560 15283484160 cost_1120_244_block4 cost_1120_244_block5 rfl rfl rfl

private theorem cost_1120_244_join0_6 : P1_7_1_3.blockEstimate 1120 244 1012 256 = 10778989420 :=
  @P1_7_1_3.block_append 1120 244 1012 1140 128 128 256 6385802705 4393186715 10778989420 cost_1120_244_block6 cost_1120_244_block7 rfl rfl rfl

private theorem cost_1120_244_join0_8 : P1_7_1_3.blockEstimate 1120 244 1268 256 = 3116466153 :=
  @P1_7_1_3.block_append 1120 244 1268 1396 128 128 256 2344550921 771915232 3116466153 cost_1120_244_block8 cost_1120_244_block9 rfl rfl rfl

private theorem cost_1120_244_join1_0 : P1_7_1_3.blockEstimate 1120 244 244 512 = 14410444055 :=
  @P1_7_1_3.block_append 1120 244 244 500 256 256 512 2627237655 11783206400 14410444055 cost_1120_244_join0_0 cost_1120_244_join0_2 rfl rfl rfl

private theorem cost_1120_244_join1_2 : P1_7_1_3.blockEstimate 1120 244 756 512 = 26062473580 :=
  @P1_7_1_3.block_append 1120 244 756 1012 256 256 512 15283484160 10778989420 26062473580 cost_1120_244_join0_4 cost_1120_244_join0_6 rfl rfl rfl

private theorem cost_1120_244_join1_4 : P1_7_1_3.blockEstimate 1120 244 1268 340 = 3172772116 :=
  @P1_7_1_3.block_append 1120 244 1268 1524 256 84 340 3116466153 56305963 3172772116 cost_1120_244_join0_8 cost_1120_244_block10 rfl rfl rfl

private theorem cost_1120_244_join2_0 : P1_7_1_3.blockEstimate 1120 244 244 1024 = 40472917635 :=
  @P1_7_1_3.block_append 1120 244 244 756 512 512 1024 14410444055 26062473580 40472917635 cost_1120_244_join1_0 cost_1120_244_join1_2 rfl rfl rfl

private theorem cost_1120_244_join3_0 : P1_7_1_3.blockEstimate 1120 244 244 1364 = 43645689751 :=
  @P1_7_1_3.block_append 1120 244 244 1268 1024 340 1364 40472917635 3172772116 43645689751 cost_1120_244_join2_0 cost_1120_244_join1_4 rfl rfl rfl

private theorem cost_1120_244_total : P1_7_1_3.momentEstimate 1120 244 = 43645689751 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1120 + 244 = 1364 by decide]
  exact cost_1120_244_join3_0

theorem moment1120_244 : P1_7_1.groupedPoleMoment 1120 244 ≤ 43645689751 :=
  (P1_7_1_3.grouped_bound 1120 244).trans_eq cost_1120_244_total
private theorem cost_1120_246_block0 : P1_7_1_3.blockEstimate 1120 246 246 128 = 366614560 := by decide +kernel

private theorem cost_1120_246_block1 : P1_7_1_3.blockEstimate 1120 246 374 128 = 2260728145 := by decide +kernel

private theorem cost_1120_246_block2 : P1_7_1_3.blockEstimate 1120 246 502 128 = 4955286336 := by decide +kernel

private theorem cost_1120_246_block3 : P1_7_1_3.blockEstimate 1120 246 630 128 = 6877539136 := by decide +kernel

private theorem cost_1120_246_block4 : P1_7_1_3.blockEstimate 1120 246 758 128 = 7763798848 := by decide +kernel

private theorem cost_1120_246_block5 : P1_7_1_3.blockEstimate 1120 246 886 128 = 7614065472 := by decide +kernel

private theorem cost_1120_246_block6 : P1_7_1_3.blockEstimate 1120 246 1014 128 = 6428956108 := by decide +kernel

private theorem cost_1120_246_block7 : P1_7_1_3.blockEstimate 1120 246 1142 128 = 4430380986 := by decide +kernel

private theorem cost_1120_246_block8 : P1_7_1_3.blockEstimate 1120 246 1270 128 = 2374860304 := by decide +kernel

private theorem cost_1120_246_block9 : P1_7_1_3.blockEstimate 1120 246 1398 128 = 790635504 := by decide +kernel

private theorem cost_1120_246_block10 : P1_7_1_3.blockEstimate 1120 246 1526 86 = 60298755 := by decide +kernel

private theorem cost_1120_246_join0_0 : P1_7_1_3.blockEstimate 1120 246 246 256 = 2627342705 :=
  @P1_7_1_3.block_append 1120 246 246 374 128 128 256 366614560 2260728145 2627342705 cost_1120_246_block0 cost_1120_246_block1 rfl rfl rfl

private theorem cost_1120_246_join0_2 : P1_7_1_3.blockEstimate 1120 246 502 256 = 11832825472 :=
  @P1_7_1_3.block_append 1120 246 502 630 128 128 256 4955286336 6877539136 11832825472 cost_1120_246_block2 cost_1120_246_block3 rfl rfl rfl

private theorem cost_1120_246_join0_4 : P1_7_1_3.blockEstimate 1120 246 758 256 = 15377864320 :=
  @P1_7_1_3.block_append 1120 246 758 886 128 128 256 7763798848 7614065472 15377864320 cost_1120_246_block4 cost_1120_246_block5 rfl rfl rfl

private theorem cost_1120_246_join0_6 : P1_7_1_3.blockEstimate 1120 246 1014 256 = 10859337094 :=
  @P1_7_1_3.block_append 1120 246 1014 1142 128 128 256 6428956108 4430380986 10859337094 cost_1120_246_block6 cost_1120_246_block7 rfl rfl rfl

private theorem cost_1120_246_join0_8 : P1_7_1_3.blockEstimate 1120 246 1270 256 = 3165495808 :=
  @P1_7_1_3.block_append 1120 246 1270 1398 128 128 256 2374860304 790635504 3165495808 cost_1120_246_block8 cost_1120_246_block9 rfl rfl rfl

private theorem cost_1120_246_join1_0 : P1_7_1_3.blockEstimate 1120 246 246 512 = 14460168177 :=
  @P1_7_1_3.block_append 1120 246 246 502 256 256 512 2627342705 11832825472 14460168177 cost_1120_246_join0_0 cost_1120_246_join0_2 rfl rfl rfl

private theorem cost_1120_246_join1_2 : P1_7_1_3.blockEstimate 1120 246 758 512 = 26237201414 :=
  @P1_7_1_3.block_append 1120 246 758 1014 256 256 512 15377864320 10859337094 26237201414 cost_1120_246_join0_4 cost_1120_246_join0_6 rfl rfl rfl

private theorem cost_1120_246_join1_4 : P1_7_1_3.blockEstimate 1120 246 1270 342 = 3225794563 :=
  @P1_7_1_3.block_append 1120 246 1270 1526 256 86 342 3165495808 60298755 3225794563 cost_1120_246_join0_8 cost_1120_246_block10 rfl rfl rfl

private theorem cost_1120_246_join2_0 : P1_7_1_3.blockEstimate 1120 246 246 1024 = 40697369591 :=
  @P1_7_1_3.block_append 1120 246 246 758 512 512 1024 14460168177 26237201414 40697369591 cost_1120_246_join1_0 cost_1120_246_join1_2 rfl rfl rfl

private theorem cost_1120_246_join3_0 : P1_7_1_3.blockEstimate 1120 246 246 1366 = 43923164154 :=
  @P1_7_1_3.block_append 1120 246 246 1270 1024 342 1366 40697369591 3225794563 43923164154 cost_1120_246_join2_0 cost_1120_246_join1_4 rfl rfl rfl

private theorem cost_1120_246_total : P1_7_1_3.momentEstimate 1120 246 = 43923164154 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1120 + 246 = 1366 by decide]
  exact cost_1120_246_join3_0

theorem moment1120_246 : P1_7_1.groupedPoleMoment 1120 246 ≤ 43923164154 :=
  (P1_7_1_3.grouped_bound 1120 246).trans_eq cost_1120_246_total
private theorem cost_1120_248_block0 : P1_7_1_3.blockEstimate 1120 248 248 128 = 366614560 := by decide +kernel

private theorem cost_1120_248_block1 : P1_7_1_3.blockEstimate 1120 248 376 128 = 2260798414 := by decide +kernel

private theorem cost_1120_248_block2 : P1_7_1_3.blockEstimate 1120 248 504 128 = 4969896576 := by decide +kernel

private theorem cost_1120_248_block3 : P1_7_1_3.blockEstimate 1120 248 632 128 = 6911793792 := by decide +kernel

private theorem cost_1120_248_block4 : P1_7_1_3.blockEstimate 1120 248 760 128 = 7809309312 := by decide +kernel

private theorem cost_1120_248_block5 : P1_7_1_3.blockEstimate 1120 248 888 128 = 7662443136 := by decide +kernel

private theorem cost_1120_248_block6 : P1_7_1_3.blockEstimate 1120 248 1016 128 = 6471990266 := by decide +kernel

private theorem cost_1120_248_block7 : P1_7_1_3.blockEstimate 1120 248 1144 128 = 4467659791 := by decide +kernel

private theorem cost_1120_248_block8 : P1_7_1_3.blockEstimate 1120 248 1272 128 = 2405321423 := by decide +kernel

private theorem cost_1120_248_block9 : P1_7_1_3.blockEstimate 1120 248 1400 128 = 809570112 := by decide +kernel

private theorem cost_1120_248_block10 : P1_7_1_3.blockEstimate 1120 248 1528 88 = 64473420 := by decide +kernel

private theorem cost_1120_248_join0_0 : P1_7_1_3.blockEstimate 1120 248 248 256 = 2627412974 :=
  @P1_7_1_3.block_append 1120 248 248 376 128 128 256 366614560 2260798414 2627412974 cost_1120_248_block0 cost_1120_248_block1 rfl rfl rfl

private theorem cost_1120_248_join0_2 : P1_7_1_3.blockEstimate 1120 248 504 256 = 11881690368 :=
  @P1_7_1_3.block_append 1120 248 504 632 128 128 256 4969896576 6911793792 11881690368 cost_1120_248_block2 cost_1120_248_block3 rfl rfl rfl

private theorem cost_1120_248_join0_4 : P1_7_1_3.blockEstimate 1120 248 760 256 = 15471752448 :=
  @P1_7_1_3.block_append 1120 248 760 888 128 128 256 7809309312 7662443136 15471752448 cost_1120_248_block4 cost_1120_248_block5 rfl rfl rfl

private theorem cost_1120_248_join0_6 : P1_7_1_3.blockEstimate 1120 248 1016 256 = 10939650057 :=
  @P1_7_1_3.block_append 1120 248 1016 1144 128 128 256 6471990266 4467659791 10939650057 cost_1120_248_block6 cost_1120_248_block7 rfl rfl rfl

private theorem cost_1120_248_join0_8 : P1_7_1_3.blockEstimate 1120 248 1272 256 = 3214891535 :=
  @P1_7_1_3.block_append 1120 248 1272 1400 128 128 256 2405321423 809570112 3214891535 cost_1120_248_block8 cost_1120_248_block9 rfl rfl rfl

private theorem cost_1120_248_join1_0 : P1_7_1_3.blockEstimate 1120 248 248 512 = 14509103342 :=
  @P1_7_1_3.block_append 1120 248 248 504 256 256 512 2627412974 11881690368 14509103342 cost_1120_248_join0_0 cost_1120_248_join0_2 rfl rfl rfl

private theorem cost_1120_248_join1_2 : P1_7_1_3.blockEstimate 1120 248 760 512 = 26411402505 :=
  @P1_7_1_3.block_append 1120 248 760 1016 256 256 512 15471752448 10939650057 26411402505 cost_1120_248_join0_4 cost_1120_248_join0_6 rfl rfl rfl

private theorem cost_1120_248_join1_4 : P1_7_1_3.blockEstimate 1120 248 1272 344 = 3279364955 :=
  @P1_7_1_3.block_append 1120 248 1272 1528 256 88 344 3214891535 64473420 3279364955 cost_1120_248_join0_8 cost_1120_248_block10 rfl rfl rfl

private theorem cost_1120_248_join2_0 : P1_7_1_3.blockEstimate 1120 248 248 1024 = 40920505847 :=
  @P1_7_1_3.block_append 1120 248 248 760 512 512 1024 14509103342 26411402505 40920505847 cost_1120_248_join1_0 cost_1120_248_join1_2 rfl rfl rfl

private theorem cost_1120_248_join3_0 : P1_7_1_3.blockEstimate 1120 248 248 1368 = 44199870802 :=
  @P1_7_1_3.block_append 1120 248 248 1272 1024 344 1368 40920505847 3279364955 44199870802 cost_1120_248_join2_0 cost_1120_248_join1_4 rfl rfl rfl

private theorem cost_1120_248_total : P1_7_1_3.momentEstimate 1120 248 = 44199870802 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1120 + 248 = 1368 by decide]
  exact cost_1120_248_join3_0

theorem moment1120_248 : P1_7_1.groupedPoleMoment 1120 248 ≤ 44199870802 :=
  (P1_7_1_3.grouped_bound 1120 248).trans_eq cost_1120_248_total

end Research6966.HelperRescueCatalogue

end Merged6967_Near6967RescueMoment10

section Merged6967_Near6967RescueMoment11
set_option Elab.async false


set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem cost_1130_247_block0 : P1_7_1_3.blockEstimate 1130 247 247 128 = 370192160 := by decide +kernel

private theorem cost_1130_247_block1 : P1_7_1_3.blockEstimate 1130 247 375 128 = 2285478950 := by decide +kernel

private theorem cost_1130_247_block2 : P1_7_1_3.blockEstimate 1130 247 503 128 = 5025178368 := by decide +kernel

private theorem cost_1130_247_block3 : P1_7_1_3.blockEstimate 1130 247 631 128 = 6997877504 := by decide +kernel

private theorem cost_1130_247_block4 : P1_7_1_3.blockEstimate 1130 247 759 128 = 7930389248 := by decide +kernel

private theorem cost_1130_247_block5 : P1_7_1_3.blockEstimate 1130 247 887 128 = 7822713600 := by decide +kernel

private theorem cost_1130_247_block6 : P1_7_1_3.blockEstimate 1130 247 1015 128 = 6674982552 := by decide +kernel

private theorem cost_1130_247_block7 : P1_7_1_3.blockEstimate 1130 247 1143 128 = 4672842267 := by decide +kernel

private theorem cost_1130_247_block8 : P1_7_1_3.blockEstimate 1130 247 1271 128 = 2567254172 := by decide +kernel

private theorem cost_1130_247_block9 : P1_7_1_3.blockEstimate 1130 247 1399 128 = 906289456 := by decide +kernel

private theorem cost_1130_247_block10 : P1_7_1_3.blockEstimate 1130 247 1527 97 = 86408750 := by decide +kernel

private theorem cost_1130_247_join0_0 : P1_7_1_3.blockEstimate 1130 247 247 256 = 2655671110 :=
  @P1_7_1_3.block_append 1130 247 247 375 128 128 256 370192160 2285478950 2655671110 cost_1130_247_block0 cost_1130_247_block1 rfl rfl rfl

private theorem cost_1130_247_join0_2 : P1_7_1_3.blockEstimate 1130 247 503 256 = 12023055872 :=
  @P1_7_1_3.block_append 1130 247 503 631 128 128 256 5025178368 6997877504 12023055872 cost_1130_247_block2 cost_1130_247_block3 rfl rfl rfl

private theorem cost_1130_247_join0_4 : P1_7_1_3.blockEstimate 1130 247 759 256 = 15753102848 :=
  @P1_7_1_3.block_append 1130 247 759 887 128 128 256 7930389248 7822713600 15753102848 cost_1130_247_block4 cost_1130_247_block5 rfl rfl rfl

private theorem cost_1130_247_join0_6 : P1_7_1_3.blockEstimate 1130 247 1015 256 = 11347824819 :=
  @P1_7_1_3.block_append 1130 247 1015 1143 128 128 256 6674982552 4672842267 11347824819 cost_1130_247_block6 cost_1130_247_block7 rfl rfl rfl

private theorem cost_1130_247_join0_8 : P1_7_1_3.blockEstimate 1130 247 1271 256 = 3473543628 :=
  @P1_7_1_3.block_append 1130 247 1271 1399 128 128 256 2567254172 906289456 3473543628 cost_1130_247_block8 cost_1130_247_block9 rfl rfl rfl

private theorem cost_1130_247_join1_0 : P1_7_1_3.blockEstimate 1130 247 247 512 = 14678726982 :=
  @P1_7_1_3.block_append 1130 247 247 503 256 256 512 2655671110 12023055872 14678726982 cost_1130_247_join0_0 cost_1130_247_join0_2 rfl rfl rfl

private theorem cost_1130_247_join1_2 : P1_7_1_3.blockEstimate 1130 247 759 512 = 27100927667 :=
  @P1_7_1_3.block_append 1130 247 759 1015 256 256 512 15753102848 11347824819 27100927667 cost_1130_247_join0_4 cost_1130_247_join0_6 rfl rfl rfl

private theorem cost_1130_247_join1_4 : P1_7_1_3.blockEstimate 1130 247 1271 353 = 3559952378 :=
  @P1_7_1_3.block_append 1130 247 1271 1527 256 97 353 3473543628 86408750 3559952378 cost_1130_247_join0_8 cost_1130_247_block10 rfl rfl rfl

private theorem cost_1130_247_join2_0 : P1_7_1_3.blockEstimate 1130 247 247 1024 = 41779654649 :=
  @P1_7_1_3.block_append 1130 247 247 759 512 512 1024 14678726982 27100927667 41779654649 cost_1130_247_join1_0 cost_1130_247_join1_2 rfl rfl rfl

private theorem cost_1130_247_join3_0 : P1_7_1_3.blockEstimate 1130 247 247 1377 = 45339607027 :=
  @P1_7_1_3.block_append 1130 247 247 1271 1024 353 1377 41779654649 3559952378 45339607027 cost_1130_247_join2_0 cost_1130_247_join1_4 rfl rfl rfl

private theorem cost_1130_247_total : P1_7_1_3.momentEstimate 1130 247 = 45339607027 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1130 + 247 = 1377 by decide]
  exact cost_1130_247_join3_0

theorem moment1130_247 : P1_7_1.groupedPoleMoment 1130 247 ≤ 45339607027 :=
  (P1_7_1_3.grouped_bound 1130 247).trans_eq cost_1130_247_total
private theorem cost_1130_249_block0 : P1_7_1_3.blockEstimate 1130 249 249 128 = 370192160 := by decide +kernel

private theorem cost_1130_249_block1 : P1_7_1_3.blockEstimate 1130 249 377 128 = 2285535090 := by decide +kernel

private theorem cost_1130_249_block2 : P1_7_1_3.blockEstimate 1130 249 505 128 = 5039768000 := by decide +kernel

private theorem cost_1130_249_block3 : P1_7_1_3.blockEstimate 1130 249 633 128 = 7032472000 := by decide +kernel

private theorem cost_1130_249_block4 : P1_7_1_3.blockEstimate 1130 249 761 128 = 7976600000 := by decide +kernel

private theorem cost_1130_249_block5 : P1_7_1_3.blockEstimate 1130 249 889 128 = 7872152000 := by decide +kernel

private theorem cost_1130_249_block6 : P1_7_1_3.blockEstimate 1130 249 1017 128 = 6719327724 := by decide +kernel

private theorem cost_1130_249_block7 : P1_7_1_3.blockEstimate 1130 249 1145 128 = 4711048245 := by decide +kernel

private theorem cost_1130_249_block8 : P1_7_1_3.blockEstimate 1130 249 1273 128 = 2598862287 := by decide +kernel

private theorem cost_1130_249_block9 : P1_7_1_3.blockEstimate 1130 249 1401 128 = 926595136 := by decide +kernel

private theorem cost_1130_249_block10 : P1_7_1_3.blockEstimate 1130 249 1529 99 = 91701200 := by decide +kernel

private theorem cost_1130_249_join0_0 : P1_7_1_3.blockEstimate 1130 249 249 256 = 2655727250 :=
  @P1_7_1_3.block_append 1130 249 249 377 128 128 256 370192160 2285535090 2655727250 cost_1130_249_block0 cost_1130_249_block1 rfl rfl rfl

private theorem cost_1130_249_join0_2 : P1_7_1_3.blockEstimate 1130 249 505 256 = 12072240000 :=
  @P1_7_1_3.block_append 1130 249 505 633 128 128 256 5039768000 7032472000 12072240000 cost_1130_249_block2 cost_1130_249_block3 rfl rfl rfl

private theorem cost_1130_249_join0_4 : P1_7_1_3.blockEstimate 1130 249 761 256 = 15848752000 :=
  @P1_7_1_3.block_append 1130 249 761 889 128 128 256 7976600000 7872152000 15848752000 cost_1130_249_block4 cost_1130_249_block5 rfl rfl rfl

private theorem cost_1130_249_join0_6 : P1_7_1_3.blockEstimate 1130 249 1017 256 = 11430375969 :=
  @P1_7_1_3.block_append 1130 249 1017 1145 128 128 256 6719327724 4711048245 11430375969 cost_1130_249_block6 cost_1130_249_block7 rfl rfl rfl

private theorem cost_1130_249_join0_8 : P1_7_1_3.blockEstimate 1130 249 1273 256 = 3525457423 :=
  @P1_7_1_3.block_append 1130 249 1273 1401 128 128 256 2598862287 926595136 3525457423 cost_1130_249_block8 cost_1130_249_block9 rfl rfl rfl

private theorem cost_1130_249_join1_0 : P1_7_1_3.blockEstimate 1130 249 249 512 = 14727967250 :=
  @P1_7_1_3.block_append 1130 249 249 505 256 256 512 2655727250 12072240000 14727967250 cost_1130_249_join0_0 cost_1130_249_join0_2 rfl rfl rfl

private theorem cost_1130_249_join1_2 : P1_7_1_3.blockEstimate 1130 249 761 512 = 27279127969 :=
  @P1_7_1_3.block_append 1130 249 761 1017 256 256 512 15848752000 11430375969 27279127969 cost_1130_249_join0_4 cost_1130_249_join0_6 rfl rfl rfl

private theorem cost_1130_249_join1_4 : P1_7_1_3.blockEstimate 1130 249 1273 355 = 3617158623 :=
  @P1_7_1_3.block_append 1130 249 1273 1529 256 99 355 3525457423 91701200 3617158623 cost_1130_249_join0_8 cost_1130_249_block10 rfl rfl rfl

private theorem cost_1130_249_join2_0 : P1_7_1_3.blockEstimate 1130 249 249 1024 = 42007095219 :=
  @P1_7_1_3.block_append 1130 249 249 761 512 512 1024 14727967250 27279127969 42007095219 cost_1130_249_join1_0 cost_1130_249_join1_2 rfl rfl rfl

private theorem cost_1130_249_join3_0 : P1_7_1_3.blockEstimate 1130 249 249 1379 = 45624253842 :=
  @P1_7_1_3.block_append 1130 249 249 1273 1024 355 1379 42007095219 3617158623 45624253842 cost_1130_249_join2_0 cost_1130_249_join1_4 rfl rfl rfl

private theorem cost_1130_249_total : P1_7_1_3.momentEstimate 1130 249 = 45624253842 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1130 + 249 = 1379 by decide]
  exact cost_1130_249_join3_0

theorem moment1130_249 : P1_7_1.groupedPoleMoment 1130 249 ≤ 45624253842 :=
  (P1_7_1_3.grouped_bound 1130 249).trans_eq cost_1130_249_total
private theorem cost_1130_251_block0 : P1_7_1_3.blockEstimate 1130 251 251 128 = 370192160 := by decide +kernel

private theorem cost_1130_251_block1 : P1_7_1_3.blockEstimate 1130 251 379 128 = 2285566645 := by decide +kernel

private theorem cost_1130_251_block2 : P1_7_1_3.blockEstimate 1130 251 507 128 = 5053942656 := by decide +kernel

private theorem cost_1130_251_block3 : P1_7_1_3.blockEstimate 1130 251 635 128 = 7066717056 := by decide +kernel

private theorem cost_1130_251_block4 : P1_7_1_3.blockEstimate 1130 251 763 128 = 8022526848 := by decide +kernel

private theorem cost_1130_251_block5 : P1_7_1_3.blockEstimate 1130 251 891 128 = 7921372032 := by decide +kernel

private theorem cost_1130_251_block6 : P1_7_1_3.blockEstimate 1130 251 1019 128 = 6763539744 := by decide +kernel

private theorem cost_1130_251_block7 : P1_7_1_3.blockEstimate 1130 251 1147 128 = 4749334424 := by decide +kernel

private theorem cost_1130_251_block8 : P1_7_1_3.blockEstimate 1130 251 1275 128 = 2630618191 := by decide +kernel

private theorem cost_1130_251_block9 : P1_7_1_3.blockEstimate 1130 251 1403 128 = 947111472 := by decide +kernel

private theorem cost_1130_251_block10 : P1_7_1_3.blockEstimate 1130 251 1531 101 = 97202105 := by decide +kernel

private theorem cost_1130_251_join0_0 : P1_7_1_3.blockEstimate 1130 251 251 256 = 2655758805 :=
  @P1_7_1_3.block_append 1130 251 251 379 128 128 256 370192160 2285566645 2655758805 cost_1130_251_block0 cost_1130_251_block1 rfl rfl rfl

private theorem cost_1130_251_join0_2 : P1_7_1_3.blockEstimate 1130 251 507 256 = 12120659712 :=
  @P1_7_1_3.block_append 1130 251 507 635 128 128 256 5053942656 7066717056 12120659712 cost_1130_251_block2 cost_1130_251_block3 rfl rfl rfl

private theorem cost_1130_251_join0_4 : P1_7_1_3.blockEstimate 1130 251 763 256 = 15943898880 :=
  @P1_7_1_3.block_append 1130 251 763 891 128 128 256 8022526848 7921372032 15943898880 cost_1130_251_block4 cost_1130_251_block5 rfl rfl rfl

private theorem cost_1130_251_join0_6 : P1_7_1_3.blockEstimate 1130 251 1019 256 = 11512874168 :=
  @P1_7_1_3.block_append 1130 251 1019 1147 128 128 256 6763539744 4749334424 11512874168 cost_1130_251_block6 cost_1130_251_block7 rfl rfl rfl

private theorem cost_1130_251_join0_8 : P1_7_1_3.blockEstimate 1130 251 1275 256 = 3577729663 :=
  @P1_7_1_3.block_append 1130 251 1275 1403 128 128 256 2630618191 947111472 3577729663 cost_1130_251_block8 cost_1130_251_block9 rfl rfl rfl

private theorem cost_1130_251_join1_0 : P1_7_1_3.blockEstimate 1130 251 251 512 = 14776418517 :=
  @P1_7_1_3.block_append 1130 251 251 507 256 256 512 2655758805 12120659712 14776418517 cost_1130_251_join0_0 cost_1130_251_join0_2 rfl rfl rfl

private theorem cost_1130_251_join1_2 : P1_7_1_3.blockEstimate 1130 251 763 512 = 27456773048 :=
  @P1_7_1_3.block_append 1130 251 763 1019 256 256 512 15943898880 11512874168 27456773048 cost_1130_251_join0_4 cost_1130_251_join0_6 rfl rfl rfl

private theorem cost_1130_251_join1_4 : P1_7_1_3.blockEstimate 1130 251 1275 357 = 3674931768 :=
  @P1_7_1_3.block_append 1130 251 1275 1531 256 101 357 3577729663 97202105 3674931768 cost_1130_251_join0_8 cost_1130_251_block10 rfl rfl rfl

private theorem cost_1130_251_join2_0 : P1_7_1_3.blockEstimate 1130 251 251 1024 = 42233191565 :=
  @P1_7_1_3.block_append 1130 251 251 763 512 512 1024 14776418517 27456773048 42233191565 cost_1130_251_join1_0 cost_1130_251_join1_2 rfl rfl rfl

private theorem cost_1130_251_join3_0 : P1_7_1_3.blockEstimate 1130 251 251 1381 = 45908123333 :=
  @P1_7_1_3.block_append 1130 251 251 1275 1024 357 1381 42233191565 3674931768 45908123333 cost_1130_251_join2_0 cost_1130_251_join1_4 rfl rfl rfl

private theorem cost_1130_251_total : P1_7_1_3.momentEstimate 1130 251 = 45908123333 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1130 + 251 = 1381 by decide]
  exact cost_1130_251_join3_0

theorem moment1130_251 : P1_7_1.groupedPoleMoment 1130 251 ≤ 45908123333 :=
  (P1_7_1_3.grouped_bound 1130 251).trans_eq cost_1130_251_total
private theorem cost_1192_260_block0 : P1_7_1_3.blockEstimate 1192 260 260 128 = 392373280 := by decide +kernel

private theorem cost_1192_260_block1 : P1_7_1_3.blockEstimate 1192 260 388 128 = 2438804512 := by decide +kernel

private theorem cost_1192_260_block2 : P1_7_1_3.blockEstimate 1192 260 516 128 = 5507184523 := by decide +kernel

private theorem cost_1192_260_block3 : P1_7_1_3.blockEstimate 1192 260 644 128 = 7876203264 := by decide +kernel

private theorem cost_1192_260_block4 : P1_7_1_3.blockEstimate 1192 260 772 128 = 9150518016 := by decide +kernel

private theorem cost_1192_260_block5 : P1_7_1_3.blockEstimate 1192 260 900 128 = 9330119424 := by decide +kernel

private theorem cost_1192_260_block6 : P1_7_1_3.blockEstimate 1192 260 1028 128 = 8415007488 := by decide +kernel

private theorem cost_1192_260_block7 : P1_7_1_3.blockEstimate 1192 260 1156 128 = 6456159804 := by decide +kernel

private theorem cost_1192_260_block8 : P1_7_1_3.blockEstimate 1192 260 1284 128 = 4058686143 := by decide +kernel

private theorem cost_1192_260_block9 : P1_7_1_3.blockEstimate 1192 260 1412 128 = 1916520593 := by decide +kernel

private theorem cost_1192_260_block10 : P1_7_1_3.blockEstimate 1192 260 1540 128 = 474772192 := by decide +kernel

private theorem cost_1192_260_block11 : P1_7_1_3.blockEstimate 1192 260 1668 44 = 9192249 := by decide +kernel

private theorem cost_1192_260_join0_0 : P1_7_1_3.blockEstimate 1192 260 260 256 = 2831177792 :=
  @P1_7_1_3.block_append 1192 260 260 388 128 128 256 392373280 2438804512 2831177792 cost_1192_260_block0 cost_1192_260_block1 rfl rfl rfl

private theorem cost_1192_260_join0_2 : P1_7_1_3.blockEstimate 1192 260 516 256 = 13383387787 :=
  @P1_7_1_3.block_append 1192 260 516 644 128 128 256 5507184523 7876203264 13383387787 cost_1192_260_block2 cost_1192_260_block3 rfl rfl rfl

private theorem cost_1192_260_join0_4 : P1_7_1_3.blockEstimate 1192 260 772 256 = 18480637440 :=
  @P1_7_1_3.block_append 1192 260 772 900 128 128 256 9150518016 9330119424 18480637440 cost_1192_260_block4 cost_1192_260_block5 rfl rfl rfl

private theorem cost_1192_260_join0_6 : P1_7_1_3.blockEstimate 1192 260 1028 256 = 14871167292 :=
  @P1_7_1_3.block_append 1192 260 1028 1156 128 128 256 8415007488 6456159804 14871167292 cost_1192_260_block6 cost_1192_260_block7 rfl rfl rfl

private theorem cost_1192_260_join0_8 : P1_7_1_3.blockEstimate 1192 260 1284 256 = 5975206736 :=
  @P1_7_1_3.block_append 1192 260 1284 1412 128 128 256 4058686143 1916520593 5975206736 cost_1192_260_block8 cost_1192_260_block9 rfl rfl rfl

private theorem cost_1192_260_join0_10 : P1_7_1_3.blockEstimate 1192 260 1540 172 = 483964441 :=
  @P1_7_1_3.block_append 1192 260 1540 1668 128 44 172 474772192 9192249 483964441 cost_1192_260_block10 cost_1192_260_block11 rfl rfl rfl

private theorem cost_1192_260_join1_0 : P1_7_1_3.blockEstimate 1192 260 260 512 = 16214565579 :=
  @P1_7_1_3.block_append 1192 260 260 516 256 256 512 2831177792 13383387787 16214565579 cost_1192_260_join0_0 cost_1192_260_join0_2 rfl rfl rfl

private theorem cost_1192_260_join1_2 : P1_7_1_3.blockEstimate 1192 260 772 512 = 33351804732 :=
  @P1_7_1_3.block_append 1192 260 772 1028 256 256 512 18480637440 14871167292 33351804732 cost_1192_260_join0_4 cost_1192_260_join0_6 rfl rfl rfl

private theorem cost_1192_260_join1_4 : P1_7_1_3.blockEstimate 1192 260 1284 428 = 6459171177 :=
  @P1_7_1_3.block_append 1192 260 1284 1540 256 172 428 5975206736 483964441 6459171177 cost_1192_260_join0_8 cost_1192_260_join0_10 rfl rfl rfl

private theorem cost_1192_260_join2_0 : P1_7_1_3.blockEstimate 1192 260 260 1024 = 49566370311 :=
  @P1_7_1_3.block_append 1192 260 260 772 512 512 1024 16214565579 33351804732 49566370311 cost_1192_260_join1_0 cost_1192_260_join1_2 rfl rfl rfl

private theorem cost_1192_260_join3_0 : P1_7_1_3.blockEstimate 1192 260 260 1452 = 56025541488 :=
  @P1_7_1_3.block_append 1192 260 260 1284 1024 428 1452 49566370311 6459171177 56025541488 cost_1192_260_join2_0 cost_1192_260_join1_4 rfl rfl rfl

private theorem cost_1192_260_total : P1_7_1_3.momentEstimate 1192 260 = 56025541488 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1192 + 260 = 1452 by decide]
  exact cost_1192_260_join3_0

theorem moment1192_260 : P1_7_1.groupedPoleMoment 1192 260 ≤ 56025541488 :=
  (P1_7_1_3.grouped_bound 1192 260).trans_eq cost_1192_260_total
private theorem cost_1193_258_block0 : P1_7_1_3.blockEstimate 1193 258 258 128 = 392731040 := by decide +kernel

private theorem cost_1193_258_block1 : P1_7_1_3.blockEstimate 1193 258 386 128 = 2441275808 := by decide +kernel

private theorem cost_1193_258_block2 : P1_7_1_3.blockEstimate 1193 258 514 128 = 5500249257 := by decide +kernel

private theorem cost_1193_258_block3 : P1_7_1_3.blockEstimate 1193 258 642 128 = 7851122944 := by decide +kernel

private theorem cost_1193_258_block4 : P1_7_1_3.blockEstimate 1193 258 770 128 = 9115672832 := by decide +kernel

private theorem cost_1193_258_block5 : P1_7_1_3.blockEstimate 1193 258 898 128 = 9293897984 := by decide +kernel

private theorem cost_1193_258_block6 : P1_7_1_3.blockEstimate 1193 258 1026 128 = 8385798400 := by decide +kernel

private theorem cost_1193_258_block7 : P1_7_1_3.blockEstimate 1193 258 1154 128 = 6437655341 := by decide +kernel

private theorem cost_1193_258_block8 : P1_7_1_3.blockEstimate 1193 258 1282 128 = 4042415938 := by decide +kernel

private theorem cost_1193_258_block9 : P1_7_1_3.blockEstimate 1193 258 1410 128 = 1903603681 := by decide +kernel

private theorem cost_1193_258_block10 : P1_7_1_3.blockEstimate 1193 258 1538 128 = 467662368 := by decide +kernel

private theorem cost_1193_258_block11 : P1_7_1_3.blockEstimate 1193 258 1666 43 = 8609975 := by decide +kernel

private theorem cost_1193_258_join0_0 : P1_7_1_3.blockEstimate 1193 258 258 256 = 2834006848 :=
  @P1_7_1_3.block_append 1193 258 258 386 128 128 256 392731040 2441275808 2834006848 cost_1193_258_block0 cost_1193_258_block1 rfl rfl rfl

private theorem cost_1193_258_join0_2 : P1_7_1_3.blockEstimate 1193 258 514 256 = 13351372201 :=
  @P1_7_1_3.block_append 1193 258 514 642 128 128 256 5500249257 7851122944 13351372201 cost_1193_258_block2 cost_1193_258_block3 rfl rfl rfl

private theorem cost_1193_258_join0_4 : P1_7_1_3.blockEstimate 1193 258 770 256 = 18409570816 :=
  @P1_7_1_3.block_append 1193 258 770 898 128 128 256 9115672832 9293897984 18409570816 cost_1193_258_block4 cost_1193_258_block5 rfl rfl rfl

private theorem cost_1193_258_join0_6 : P1_7_1_3.blockEstimate 1193 258 1026 256 = 14823453741 :=
  @P1_7_1_3.block_append 1193 258 1026 1154 128 128 256 8385798400 6437655341 14823453741 cost_1193_258_block6 cost_1193_258_block7 rfl rfl rfl

private theorem cost_1193_258_join0_8 : P1_7_1_3.blockEstimate 1193 258 1282 256 = 5946019619 :=
  @P1_7_1_3.block_append 1193 258 1282 1410 128 128 256 4042415938 1903603681 5946019619 cost_1193_258_block8 cost_1193_258_block9 rfl rfl rfl

private theorem cost_1193_258_join0_10 : P1_7_1_3.blockEstimate 1193 258 1538 171 = 476272343 :=
  @P1_7_1_3.block_append 1193 258 1538 1666 128 43 171 467662368 8609975 476272343 cost_1193_258_block10 cost_1193_258_block11 rfl rfl rfl

private theorem cost_1193_258_join1_0 : P1_7_1_3.blockEstimate 1193 258 258 512 = 16185379049 :=
  @P1_7_1_3.block_append 1193 258 258 514 256 256 512 2834006848 13351372201 16185379049 cost_1193_258_join0_0 cost_1193_258_join0_2 rfl rfl rfl

private theorem cost_1193_258_join1_2 : P1_7_1_3.blockEstimate 1193 258 770 512 = 33233024557 :=
  @P1_7_1_3.block_append 1193 258 770 1026 256 256 512 18409570816 14823453741 33233024557 cost_1193_258_join0_4 cost_1193_258_join0_6 rfl rfl rfl

private theorem cost_1193_258_join1_4 : P1_7_1_3.blockEstimate 1193 258 1282 427 = 6422291962 :=
  @P1_7_1_3.block_append 1193 258 1282 1538 256 171 427 5946019619 476272343 6422291962 cost_1193_258_join0_8 cost_1193_258_join0_10 rfl rfl rfl

private theorem cost_1193_258_join2_0 : P1_7_1_3.blockEstimate 1193 258 258 1024 = 49418403606 :=
  @P1_7_1_3.block_append 1193 258 258 770 512 512 1024 16185379049 33233024557 49418403606 cost_1193_258_join1_0 cost_1193_258_join1_2 rfl rfl rfl

private theorem cost_1193_258_join3_0 : P1_7_1_3.blockEstimate 1193 258 258 1451 = 55840695568 :=
  @P1_7_1_3.block_append 1193 258 258 1282 1024 427 1451 49418403606 6422291962 55840695568 cost_1193_258_join2_0 cost_1193_258_join1_4 rfl rfl rfl

private theorem cost_1193_258_total : P1_7_1_3.momentEstimate 1193 258 = 55840695568 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1193 + 258 = 1451 by decide]
  exact cost_1193_258_join3_0

theorem moment1193_258 : P1_7_1.groupedPoleMoment 1193 258 ≤ 55840695568 :=
  (P1_7_1_3.grouped_bound 1193 258).trans_eq cost_1193_258_total
private theorem cost_1193_260_block0 : P1_7_1_3.blockEstimate 1193 260 260 128 = 392731040 := by decide +kernel

private theorem cost_1193_260_block1 : P1_7_1_3.blockEstimate 1193 260 388 128 = 2441275808 := by decide +kernel

private theorem cost_1193_260_block2 : P1_7_1_3.blockEstimate 1193 260 516 128 = 5513548757 := by decide +kernel

private theorem cost_1193_260_block3 : P1_7_1_3.blockEstimate 1193 260 644 128 = 7886843712 := by decide +kernel

private theorem cost_1193_260_block4 : P1_7_1_3.blockEstimate 1193 260 772 128 = 9165434688 := by decide +kernel

private theorem cost_1193_260_block5 : P1_7_1_3.blockEstimate 1193 260 900 128 = 9349312320 := by decide +kernel

private theorem cost_1193_260_block6 : P1_7_1_3.blockEstimate 1193 260 1028 128 = 8438476608 := by decide +kernel

private theorem cost_1193_260_block7 : P1_7_1_3.blockEstimate 1193 260 1156 128 = 6482264661 := by decide +kernel

private theorem cost_1193_260_block8 : P1_7_1_3.blockEstimate 1193 260 1284 128 = 4081391822 := by decide +kernel

private theorem cost_1193_260_block9 : P1_7_1_3.blockEstimate 1193 260 1412 128 = 1932949055 := by decide +kernel

private theorem cost_1193_260_block10 : P1_7_1_3.blockEstimate 1193 260 1540 128 = 482800016 := by decide +kernel

private theorem cost_1193_260_block11 : P1_7_1_3.blockEstimate 1193 260 1668 45 = 9816702 := by decide +kernel

private theorem cost_1193_260_join0_0 : P1_7_1_3.blockEstimate 1193 260 260 256 = 2834006848 :=
  @P1_7_1_3.block_append 1193 260 260 388 128 128 256 392731040 2441275808 2834006848 cost_1193_260_block0 cost_1193_260_block1 rfl rfl rfl

private theorem cost_1193_260_join0_2 : P1_7_1_3.blockEstimate 1193 260 516 256 = 13400392469 :=
  @P1_7_1_3.block_append 1193 260 516 644 128 128 256 5513548757 7886843712 13400392469 cost_1193_260_block2 cost_1193_260_block3 rfl rfl rfl

private theorem cost_1193_260_join0_4 : P1_7_1_3.blockEstimate 1193 260 772 256 = 18514747008 :=
  @P1_7_1_3.block_append 1193 260 772 900 128 128 256 9165434688 9349312320 18514747008 cost_1193_260_block4 cost_1193_260_block5 rfl rfl rfl

private theorem cost_1193_260_join0_6 : P1_7_1_3.blockEstimate 1193 260 1028 256 = 14920741269 :=
  @P1_7_1_3.block_append 1193 260 1028 1156 128 128 256 8438476608 6482264661 14920741269 cost_1193_260_block6 cost_1193_260_block7 rfl rfl rfl

private theorem cost_1193_260_join0_8 : P1_7_1_3.blockEstimate 1193 260 1284 256 = 6014340877 :=
  @P1_7_1_3.block_append 1193 260 1284 1412 128 128 256 4081391822 1932949055 6014340877 cost_1193_260_block8 cost_1193_260_block9 rfl rfl rfl

private theorem cost_1193_260_join0_10 : P1_7_1_3.blockEstimate 1193 260 1540 173 = 492616718 :=
  @P1_7_1_3.block_append 1193 260 1540 1668 128 45 173 482800016 9816702 492616718 cost_1193_260_block10 cost_1193_260_block11 rfl rfl rfl

private theorem cost_1193_260_join1_0 : P1_7_1_3.blockEstimate 1193 260 260 512 = 16234399317 :=
  @P1_7_1_3.block_append 1193 260 260 516 256 256 512 2834006848 13400392469 16234399317 cost_1193_260_join0_0 cost_1193_260_join0_2 rfl rfl rfl

private theorem cost_1193_260_join1_2 : P1_7_1_3.blockEstimate 1193 260 772 512 = 33435488277 :=
  @P1_7_1_3.block_append 1193 260 772 1028 256 256 512 18514747008 14920741269 33435488277 cost_1193_260_join0_4 cost_1193_260_join0_6 rfl rfl rfl

private theorem cost_1193_260_join1_4 : P1_7_1_3.blockEstimate 1193 260 1284 429 = 6506957595 :=
  @P1_7_1_3.block_append 1193 260 1284 1540 256 173 429 6014340877 492616718 6506957595 cost_1193_260_join0_8 cost_1193_260_join0_10 rfl rfl rfl

private theorem cost_1193_260_join2_0 : P1_7_1_3.blockEstimate 1193 260 260 1024 = 49669887594 :=
  @P1_7_1_3.block_append 1193 260 260 772 512 512 1024 16234399317 33435488277 49669887594 cost_1193_260_join1_0 cost_1193_260_join1_2 rfl rfl rfl

private theorem cost_1193_260_join3_0 : P1_7_1_3.blockEstimate 1193 260 260 1453 = 56176845189 :=
  @P1_7_1_3.block_append 1193 260 260 1284 1024 429 1453 49669887594 6506957595 56176845189 cost_1193_260_join2_0 cost_1193_260_join1_4 rfl rfl rfl

private theorem cost_1193_260_total : P1_7_1_3.momentEstimate 1193 260 = 56176845189 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1193 + 260 = 1453 by decide]
  exact cost_1193_260_join3_0

theorem moment1193_260 : P1_7_1.groupedPoleMoment 1193 260 ≤ 56176845189 :=
  (P1_7_1_3.grouped_bound 1193 260).trans_eq cost_1193_260_total
private theorem cost_1193_267_block0 : P1_7_1_3.blockEstimate 1193 267 267 128 = 392731040 := by decide +kernel

private theorem cost_1193_267_block1 : P1_7_1_3.blockEstimate 1193 267 395 128 = 2441275808 := by decide +kernel

private theorem cost_1193_267_block2 : P1_7_1_3.blockEstimate 1193 267 523 128 = 5556741837 := by decide +kernel

private theorem cost_1193_267_block3 : P1_7_1_3.blockEstimate 1193 267 651 128 = 8008860544 := by decide +kernel

private theorem cost_1193_267_block4 : P1_7_1_3.blockEstimate 1193 267 779 128 = 9337111424 := by decide +kernel

private theorem cost_1193_267_block5 : P1_7_1_3.blockEstimate 1193 267 907 128 = 9541288832 := by decide +kernel

private theorem cost_1193_267_block6 : P1_7_1_3.blockEstimate 1193 267 1035 128 = 8621392768 := by decide +kernel

private theorem cost_1193_267_block7 : P1_7_1_3.blockEstimate 1193 267 1163 128 = 6638461740 := by decide +kernel

private theorem cost_1193_267_block8 : P1_7_1_3.blockEstimate 1193 267 1291 128 = 4218794151 := by decide +kernel

private theorem cost_1193_267_block9 : P1_7_1_3.blockEstimate 1193 267 1419 128 = 2037156408 := by decide +kernel

private theorem cost_1193_267_block10 : P1_7_1_3.blockEstimate 1193 267 1547 128 = 537765696 := by decide +kernel

private theorem cost_1193_267_block11 : P1_7_1_3.blockEstimate 1193 267 1675 52 = 14911884 := by decide +kernel

private theorem cost_1193_267_join0_0 : P1_7_1_3.blockEstimate 1193 267 267 256 = 2834006848 :=
  @P1_7_1_3.block_append 1193 267 267 395 128 128 256 392731040 2441275808 2834006848 cost_1193_267_block0 cost_1193_267_block1 rfl rfl rfl

private theorem cost_1193_267_join0_2 : P1_7_1_3.blockEstimate 1193 267 523 256 = 13565602381 :=
  @P1_7_1_3.block_append 1193 267 523 651 128 128 256 5556741837 8008860544 13565602381 cost_1193_267_block2 cost_1193_267_block3 rfl rfl rfl

private theorem cost_1193_267_join0_4 : P1_7_1_3.blockEstimate 1193 267 779 256 = 18878400256 :=
  @P1_7_1_3.block_append 1193 267 779 907 128 128 256 9337111424 9541288832 18878400256 cost_1193_267_block4 cost_1193_267_block5 rfl rfl rfl

private theorem cost_1193_267_join0_6 : P1_7_1_3.blockEstimate 1193 267 1035 256 = 15259854508 :=
  @P1_7_1_3.block_append 1193 267 1035 1163 128 128 256 8621392768 6638461740 15259854508 cost_1193_267_block6 cost_1193_267_block7 rfl rfl rfl

private theorem cost_1193_267_join0_8 : P1_7_1_3.blockEstimate 1193 267 1291 256 = 6255950559 :=
  @P1_7_1_3.block_append 1193 267 1291 1419 128 128 256 4218794151 2037156408 6255950559 cost_1193_267_block8 cost_1193_267_block9 rfl rfl rfl

private theorem cost_1193_267_join0_10 : P1_7_1_3.blockEstimate 1193 267 1547 180 = 552677580 :=
  @P1_7_1_3.block_append 1193 267 1547 1675 128 52 180 537765696 14911884 552677580 cost_1193_267_block10 cost_1193_267_block11 rfl rfl rfl

private theorem cost_1193_267_join1_0 : P1_7_1_3.blockEstimate 1193 267 267 512 = 16399609229 :=
  @P1_7_1_3.block_append 1193 267 267 523 256 256 512 2834006848 13565602381 16399609229 cost_1193_267_join0_0 cost_1193_267_join0_2 rfl rfl rfl

private theorem cost_1193_267_join1_2 : P1_7_1_3.blockEstimate 1193 267 779 512 = 34138254764 :=
  @P1_7_1_3.block_append 1193 267 779 1035 256 256 512 18878400256 15259854508 34138254764 cost_1193_267_join0_4 cost_1193_267_join0_6 rfl rfl rfl

private theorem cost_1193_267_join1_4 : P1_7_1_3.blockEstimate 1193 267 1291 436 = 6808628139 :=
  @P1_7_1_3.block_append 1193 267 1291 1547 256 180 436 6255950559 552677580 6808628139 cost_1193_267_join0_8 cost_1193_267_join0_10 rfl rfl rfl

private theorem cost_1193_267_join2_0 : P1_7_1_3.blockEstimate 1193 267 267 1024 = 50537863993 :=
  @P1_7_1_3.block_append 1193 267 267 779 512 512 1024 16399609229 34138254764 50537863993 cost_1193_267_join1_0 cost_1193_267_join1_2 rfl rfl rfl

private theorem cost_1193_267_join3_0 : P1_7_1_3.blockEstimate 1193 267 267 1460 = 57346492132 :=
  @P1_7_1_3.block_append 1193 267 267 1291 1024 436 1460 50537863993 6808628139 57346492132 cost_1193_267_join2_0 cost_1193_267_join1_4 rfl rfl rfl

private theorem cost_1193_267_total : P1_7_1_3.momentEstimate 1193 267 = 57346492132 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1193 + 267 = 1460 by decide]
  exact cost_1193_267_join3_0

theorem moment1193_267 : P1_7_1.groupedPoleMoment 1193 267 ≤ 57346492132 :=
  (P1_7_1_3.grouped_bound 1193 267).trans_eq cost_1193_267_total
private theorem cost_1218_262_block0 : P1_7_1_3.blockEstimate 1218 262 262 128 = 401675040 := by decide +kernel

private theorem cost_1218_262_block1 : P1_7_1_3.blockEstimate 1218 262 390 128 = 2503058208 := by decide +kernel

private theorem cost_1218_262_block2 : P1_7_1_3.blockEstimate 1218 262 518 128 = 5685900067 := by decide +kernel

private theorem cost_1218_262_block3 : P1_7_1_3.blockEstimate 1218 262 646 128 = 8189390784 := by decide +kernel

private theorem cost_1218_262_block4 : P1_7_1_3.blockEstimate 1218 262 774 128 = 9589813184 := by decide +kernel

private theorem cost_1218_262_block5 : P1_7_1_3.blockEstimate 1218 262 902 128 = 9887133632 := by decide +kernel

private theorem cost_1218_262_block6 : P1_7_1_3.blockEstimate 1218 262 1030 128 = 9081352128 := by decide +kernel

private theorem cost_1218_262_block7 : P1_7_1_3.blockEstimate 1218 262 1158 128 = 7193063422 := by decide +kernel

private theorem cost_1218_262_block8 : P1_7_1_3.blockEstimate 1218 262 1286 128 = 4711153020 := by decide +kernel

private theorem cost_1218_262_block9 : P1_7_1_3.blockEstimate 1218 262 1414 128 = 2400227593 := by decide +kernel

private theorem cost_1218_262_block10 : P1_7_1_3.blockEstimate 1218 262 1542 128 = 727718656 := by decide +kernel

private theorem cost_1218_262_block11 : P1_7_1_3.blockEstimate 1218 262 1670 72 = 39194544 := by decide +kernel

private theorem cost_1218_262_join0_0 : P1_7_1_3.blockEstimate 1218 262 262 256 = 2904733248 :=
  @P1_7_1_3.block_append 1218 262 262 390 128 128 256 401675040 2503058208 2904733248 cost_1218_262_block0 cost_1218_262_block1 rfl rfl rfl

private theorem cost_1218_262_join0_2 : P1_7_1_3.blockEstimate 1218 262 518 256 = 13875290851 :=
  @P1_7_1_3.block_append 1218 262 518 646 128 128 256 5685900067 8189390784 13875290851 cost_1218_262_block2 cost_1218_262_block3 rfl rfl rfl

private theorem cost_1218_262_join0_4 : P1_7_1_3.blockEstimate 1218 262 774 256 = 19476946816 :=
  @P1_7_1_3.block_append 1218 262 774 902 128 128 256 9589813184 9887133632 19476946816 cost_1218_262_block4 cost_1218_262_block5 rfl rfl rfl

private theorem cost_1218_262_join0_6 : P1_7_1_3.blockEstimate 1218 262 1030 256 = 16274415550 :=
  @P1_7_1_3.block_append 1218 262 1030 1158 128 128 256 9081352128 7193063422 16274415550 cost_1218_262_block6 cost_1218_262_block7 rfl rfl rfl

private theorem cost_1218_262_join0_8 : P1_7_1_3.blockEstimate 1218 262 1286 256 = 7111380613 :=
  @P1_7_1_3.block_append 1218 262 1286 1414 128 128 256 4711153020 2400227593 7111380613 cost_1218_262_block8 cost_1218_262_block9 rfl rfl rfl

private theorem cost_1218_262_join0_10 : P1_7_1_3.blockEstimate 1218 262 1542 200 = 766913200 :=
  @P1_7_1_3.block_append 1218 262 1542 1670 128 72 200 727718656 39194544 766913200 cost_1218_262_block10 cost_1218_262_block11 rfl rfl rfl

private theorem cost_1218_262_join1_0 : P1_7_1_3.blockEstimate 1218 262 262 512 = 16780024099 :=
  @P1_7_1_3.block_append 1218 262 262 518 256 256 512 2904733248 13875290851 16780024099 cost_1218_262_join0_0 cost_1218_262_join0_2 rfl rfl rfl

private theorem cost_1218_262_join1_2 : P1_7_1_3.blockEstimate 1218 262 774 512 = 35751362366 :=
  @P1_7_1_3.block_append 1218 262 774 1030 256 256 512 19476946816 16274415550 35751362366 cost_1218_262_join0_4 cost_1218_262_join0_6 rfl rfl rfl

private theorem cost_1218_262_join1_4 : P1_7_1_3.blockEstimate 1218 262 1286 456 = 7878293813 :=
  @P1_7_1_3.block_append 1218 262 1286 1542 256 200 456 7111380613 766913200 7878293813 cost_1218_262_join0_8 cost_1218_262_join0_10 rfl rfl rfl

private theorem cost_1218_262_join2_0 : P1_7_1_3.blockEstimate 1218 262 262 1024 = 52531386465 :=
  @P1_7_1_3.block_append 1218 262 262 774 512 512 1024 16780024099 35751362366 52531386465 cost_1218_262_join1_0 cost_1218_262_join1_2 rfl rfl rfl

private theorem cost_1218_262_join3_0 : P1_7_1_3.blockEstimate 1218 262 262 1480 = 60409680278 :=
  @P1_7_1_3.block_append 1218 262 262 1286 1024 456 1480 52531386465 7878293813 60409680278 cost_1218_262_join2_0 cost_1218_262_join1_4 rfl rfl rfl

private theorem cost_1218_262_total : P1_7_1_3.momentEstimate 1218 262 = 60409680278 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1218 + 262 = 1480 by decide]
  exact cost_1218_262_join3_0

theorem moment1218_262 : P1_7_1.groupedPoleMoment 1218 262 ≤ 60409680278 :=
  (P1_7_1_3.grouped_bound 1218 262).trans_eq cost_1218_262_total
private theorem cost_1253_269_block0 : P1_7_1_3.blockEstimate 1253 269 269 128 = 414196640 := by decide +kernel

private theorem cost_1253_269_block1 : P1_7_1_3.blockEstimate 1253 269 397 128 = 2589553568 := by decide +kernel

private theorem cost_1253_269_block2 : P1_7_1_3.blockEstimate 1253 269 525 128 = 5953866227 := by decide +kernel

private theorem cost_1253_269_block3 : P1_7_1_3.blockEstimate 1253 269 653 128 = 8693974080 := by decide +kernel

private theorem cost_1253_269_block4 : P1_7_1_3.blockEstimate 1253 269 781 128 = 10301981760 := by decide +kernel

private theorem cost_1253_269_block5 : P1_7_1_3.blockEstimate 1253 269 909 128 = 10777527360 := by decide +kernel

private theorem cost_1253_269_block6 : P1_7_1_3.blockEstimate 1253 269 1037 128 = 10120610880 := by decide +kernel

private theorem cost_1253_269_block7 : P1_7_1_3.blockEstimate 1253 269 1165 128 = 8335432226 := by decide +kernel

private theorem cost_1253_269_block8 : P1_7_1_3.blockEstimate 1253 269 1293 128 = 5762449364 := by decide +kernel

private theorem cost_1253_269_block9 : P1_7_1_3.blockEstimate 1253 269 1421 128 = 3220593829 := by decide +kernel

private theorem cost_1253_269_block10 : P1_7_1_3.blockEstimate 1253 269 1549 128 = 1217727120 := by decide +kernel

private theorem cost_1253_269_block11 : P1_7_1_3.blockEstimate 1253 269 1677 114 = 154088948 := by decide +kernel

private theorem cost_1253_269_join0_0 : P1_7_1_3.blockEstimate 1253 269 269 256 = 3003750208 :=
  @P1_7_1_3.block_append 1253 269 269 397 128 128 256 414196640 2589553568 3003750208 cost_1253_269_block0 cost_1253_269_block1 rfl rfl rfl

private theorem cost_1253_269_join0_2 : P1_7_1_3.blockEstimate 1253 269 525 256 = 14647840307 :=
  @P1_7_1_3.block_append 1253 269 525 653 128 128 256 5953866227 8693974080 14647840307 cost_1253_269_block2 cost_1253_269_block3 rfl rfl rfl

private theorem cost_1253_269_join0_4 : P1_7_1_3.blockEstimate 1253 269 781 256 = 21079509120 :=
  @P1_7_1_3.block_append 1253 269 781 909 128 128 256 10301981760 10777527360 21079509120 cost_1253_269_block4 cost_1253_269_block5 rfl rfl rfl

private theorem cost_1253_269_join0_6 : P1_7_1_3.blockEstimate 1253 269 1037 256 = 18456043106 :=
  @P1_7_1_3.block_append 1253 269 1037 1165 128 128 256 10120610880 8335432226 18456043106 cost_1253_269_block6 cost_1253_269_block7 rfl rfl rfl

private theorem cost_1253_269_join0_8 : P1_7_1_3.blockEstimate 1253 269 1293 256 = 8983043193 :=
  @P1_7_1_3.block_append 1253 269 1293 1421 128 128 256 5762449364 3220593829 8983043193 cost_1253_269_block8 cost_1253_269_block9 rfl rfl rfl

private theorem cost_1253_269_join0_10 : P1_7_1_3.blockEstimate 1253 269 1549 242 = 1371816068 :=
  @P1_7_1_3.block_append 1253 269 1549 1677 128 114 242 1217727120 154088948 1371816068 cost_1253_269_block10 cost_1253_269_block11 rfl rfl rfl

private theorem cost_1253_269_join1_0 : P1_7_1_3.blockEstimate 1253 269 269 512 = 17651590515 :=
  @P1_7_1_3.block_append 1253 269 269 525 256 256 512 3003750208 14647840307 17651590515 cost_1253_269_join0_0 cost_1253_269_join0_2 rfl rfl rfl

private theorem cost_1253_269_join1_2 : P1_7_1_3.blockEstimate 1253 269 781 512 = 39535552226 :=
  @P1_7_1_3.block_append 1253 269 781 1037 256 256 512 21079509120 18456043106 39535552226 cost_1253_269_join0_4 cost_1253_269_join0_6 rfl rfl rfl

private theorem cost_1253_269_join1_4 : P1_7_1_3.blockEstimate 1253 269 1293 498 = 10354859261 :=
  @P1_7_1_3.block_append 1253 269 1293 1549 256 242 498 8983043193 1371816068 10354859261 cost_1253_269_join0_8 cost_1253_269_join0_10 rfl rfl rfl

private theorem cost_1253_269_join2_0 : P1_7_1_3.blockEstimate 1253 269 269 1024 = 57187142741 :=
  @P1_7_1_3.block_append 1253 269 269 781 512 512 1024 17651590515 39535552226 57187142741 cost_1253_269_join1_0 cost_1253_269_join1_2 rfl rfl rfl

private theorem cost_1253_269_join3_0 : P1_7_1_3.blockEstimate 1253 269 269 1522 = 67542002002 :=
  @P1_7_1_3.block_append 1253 269 269 1293 1024 498 1522 57187142741 10354859261 67542002002 cost_1253_269_join2_0 cost_1253_269_join1_4 rfl rfl rfl

private theorem cost_1253_269_total : P1_7_1_3.momentEstimate 1253 269 = 67542002002 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1253 + 269 = 1522 by decide]
  exact cost_1253_269_join3_0

theorem moment1253_269 : P1_7_1.groupedPoleMoment 1253 269 ≤ 67542002002 :=
  (P1_7_1_3.grouped_bound 1253 269).trans_eq cost_1253_269_total
private theorem cost_1253_277_block0 : P1_7_1_3.blockEstimate 1253 277 277 128 = 414196640 := by decide +kernel

private theorem cost_1253_277_block1 : P1_7_1_3.blockEstimate 1253 277 405 128 = 2589553568 := by decide +kernel

private theorem cost_1253_277_block2 : P1_7_1_3.blockEstimate 1253 277 533 128 = 5998561857 := by decide +kernel

private theorem cost_1253_277_block3 : P1_7_1_3.blockEstimate 1253 277 661 128 = 8836921664 := by decide +kernel

private theorem cost_1253_277_block4 : P1_7_1_3.blockEstimate 1253 277 789 128 = 10510793024 := by decide +kernel

private theorem cost_1253_277_block5 : P1_7_1_3.blockEstimate 1253 277 917 128 = 11018647872 := by decide +kernel

private theorem cost_1253_277_block6 : P1_7_1_3.blockEstimate 1253 277 1045 128 = 10360486208 := by decide +kernel

private theorem cost_1253_277_block7 : P1_7_1_3.blockEstimate 1253 277 1173 128 = 8543455210 := by decide +kernel

private theorem cost_1253_277_block8 : P1_7_1_3.blockEstimate 1253 277 1301 128 = 5946121312 := by decide +kernel

private theorem cost_1253_277_block9 : P1_7_1_3.blockEstimate 1253 277 1429 128 = 3372474676 := by decide +kernel

private theorem cost_1253_277_block10 : P1_7_1_3.blockEstimate 1253 277 1557 128 = 1318757584 := by decide +kernel

private theorem cost_1253_277_block11 : P1_7_1_3.blockEstimate 1253 277 1685 122 = 187790963 := by decide +kernel

private theorem cost_1253_277_join0_0 : P1_7_1_3.blockEstimate 1253 277 277 256 = 3003750208 :=
  @P1_7_1_3.block_append 1253 277 277 405 128 128 256 414196640 2589553568 3003750208 cost_1253_277_block0 cost_1253_277_block1 rfl rfl rfl

private theorem cost_1253_277_join0_2 : P1_7_1_3.blockEstimate 1253 277 533 256 = 14835483521 :=
  @P1_7_1_3.block_append 1253 277 533 661 128 128 256 5998561857 8836921664 14835483521 cost_1253_277_block2 cost_1253_277_block3 rfl rfl rfl

private theorem cost_1253_277_join0_4 : P1_7_1_3.blockEstimate 1253 277 789 256 = 21529440896 :=
  @P1_7_1_3.block_append 1253 277 789 917 128 128 256 10510793024 11018647872 21529440896 cost_1253_277_block4 cost_1253_277_block5 rfl rfl rfl

private theorem cost_1253_277_join0_6 : P1_7_1_3.blockEstimate 1253 277 1045 256 = 18903941418 :=
  @P1_7_1_3.block_append 1253 277 1045 1173 128 128 256 10360486208 8543455210 18903941418 cost_1253_277_block6 cost_1253_277_block7 rfl rfl rfl

private theorem cost_1253_277_join0_8 : P1_7_1_3.blockEstimate 1253 277 1301 256 = 9318595988 :=
  @P1_7_1_3.block_append 1253 277 1301 1429 128 128 256 5946121312 3372474676 9318595988 cost_1253_277_block8 cost_1253_277_block9 rfl rfl rfl

private theorem cost_1253_277_join0_10 : P1_7_1_3.blockEstimate 1253 277 1557 250 = 1506548547 :=
  @P1_7_1_3.block_append 1253 277 1557 1685 128 122 250 1318757584 187790963 1506548547 cost_1253_277_block10 cost_1253_277_block11 rfl rfl rfl

private theorem cost_1253_277_join1_0 : P1_7_1_3.blockEstimate 1253 277 277 512 = 17839233729 :=
  @P1_7_1_3.block_append 1253 277 277 533 256 256 512 3003750208 14835483521 17839233729 cost_1253_277_join0_0 cost_1253_277_join0_2 rfl rfl rfl

private theorem cost_1253_277_join1_2 : P1_7_1_3.blockEstimate 1253 277 789 512 = 40433382314 :=
  @P1_7_1_3.block_append 1253 277 789 1045 256 256 512 21529440896 18903941418 40433382314 cost_1253_277_join0_4 cost_1253_277_join0_6 rfl rfl rfl

private theorem cost_1253_277_join1_4 : P1_7_1_3.blockEstimate 1253 277 1301 506 = 10825144535 :=
  @P1_7_1_3.block_append 1253 277 1301 1557 256 250 506 9318595988 1506548547 10825144535 cost_1253_277_join0_8 cost_1253_277_join0_10 rfl rfl rfl

private theorem cost_1253_277_join2_0 : P1_7_1_3.blockEstimate 1253 277 277 1024 = 58272616043 :=
  @P1_7_1_3.block_append 1253 277 277 789 512 512 1024 17839233729 40433382314 58272616043 cost_1253_277_join1_0 cost_1253_277_join1_2 rfl rfl rfl

private theorem cost_1253_277_join3_0 : P1_7_1_3.blockEstimate 1253 277 277 1530 = 69097760578 :=
  @P1_7_1_3.block_append 1253 277 277 1301 1024 506 1530 58272616043 10825144535 69097760578 cost_1253_277_join2_0 cost_1253_277_join1_4 rfl rfl rfl

private theorem cost_1253_277_total : P1_7_1_3.momentEstimate 1253 277 = 69097760578 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1253 + 277 = 1530 by decide]
  exact cost_1253_277_join3_0

theorem moment1253_277 : P1_7_1.groupedPoleMoment 1253 277 ≤ 69097760578 :=
  (P1_7_1_3.grouped_bound 1253 277).trans_eq cost_1253_277_total
private theorem cost_1254_272_block0 : P1_7_1_3.blockEstimate 1254 272 272 128 = 414554400 := by decide +kernel

private theorem cost_1254_272_block1 : P1_7_1_3.blockEstimate 1254 272 400 128 = 2592024864 := by decide +kernel

private theorem cost_1254_272_block2 : P1_7_1_3.blockEstimate 1254 272 528 128 = 5977847460 := by decide +kernel

private theorem cost_1254_272_block3 : P1_7_1_3.blockEstimate 1254 272 656 128 = 8759272704 := by decide +kernel

private theorem cost_1254_272_block4 : P1_7_1_3.blockEstimate 1254 272 784 128 = 10396329216 := by decide +kernel

private theorem cost_1254_272_block5 : P1_7_1_3.blockEstimate 1254 272 912 128 = 10888340736 := by decide +kernel

private theorem cost_1254_272_block6 : P1_7_1_3.blockEstimate 1254 272 1040 128 = 10235307264 := by decide +kernel

private theorem cost_1254_272_block7 : P1_7_1_3.blockEstimate 1254 272 1168 128 = 8442064826 := by decide +kernel

private theorem cost_1254_272_block8 : P1_7_1_3.blockEstimate 1254 272 1296 128 = 5858223469 := by decide +kernel

private theorem cost_1254_272_block9 : P1_7_1_3.blockEstimate 1254 272 1424 128 = 3298848796 := by decide +kernel

private theorem cost_1254_272_block10 : P1_7_1_3.blockEstimate 1254 272 1552 128 = 1268897456 := by decide +kernel

private theorem cost_1254_272_block11 : P1_7_1_3.blockEstimate 1254 272 1680 118 = 170536115 := by decide +kernel

private theorem cost_1254_272_join0_0 : P1_7_1_3.blockEstimate 1254 272 272 256 = 3006579264 :=
  @P1_7_1_3.block_append 1254 272 272 400 128 128 256 414554400 2592024864 3006579264 cost_1254_272_block0 cost_1254_272_block1 rfl rfl rfl

private theorem cost_1254_272_join0_2 : P1_7_1_3.blockEstimate 1254 272 528 256 = 14737120164 :=
  @P1_7_1_3.block_append 1254 272 528 656 128 128 256 5977847460 8759272704 14737120164 cost_1254_272_block2 cost_1254_272_block3 rfl rfl rfl

private theorem cost_1254_272_join0_4 : P1_7_1_3.blockEstimate 1254 272 784 256 = 21284669952 :=
  @P1_7_1_3.block_append 1254 272 784 912 128 128 256 10396329216 10888340736 21284669952 cost_1254_272_block4 cost_1254_272_block5 rfl rfl rfl

private theorem cost_1254_272_join0_6 : P1_7_1_3.blockEstimate 1254 272 1040 256 = 18677372090 :=
  @P1_7_1_3.block_append 1254 272 1040 1168 128 128 256 10235307264 8442064826 18677372090 cost_1254_272_block6 cost_1254_272_block7 rfl rfl rfl

private theorem cost_1254_272_join0_8 : P1_7_1_3.blockEstimate 1254 272 1296 256 = 9157072265 :=
  @P1_7_1_3.block_append 1254 272 1296 1424 128 128 256 5858223469 3298848796 9157072265 cost_1254_272_block8 cost_1254_272_block9 rfl rfl rfl

private theorem cost_1254_272_join0_10 : P1_7_1_3.blockEstimate 1254 272 1552 246 = 1439433571 :=
  @P1_7_1_3.block_append 1254 272 1552 1680 128 118 246 1268897456 170536115 1439433571 cost_1254_272_block10 cost_1254_272_block11 rfl rfl rfl

private theorem cost_1254_272_join1_0 : P1_7_1_3.blockEstimate 1254 272 272 512 = 17743699428 :=
  @P1_7_1_3.block_append 1254 272 272 528 256 256 512 3006579264 14737120164 17743699428 cost_1254_272_join0_0 cost_1254_272_join0_2 rfl rfl rfl

private theorem cost_1254_272_join1_2 : P1_7_1_3.blockEstimate 1254 272 784 512 = 39962042042 :=
  @P1_7_1_3.block_append 1254 272 784 1040 256 256 512 21284669952 18677372090 39962042042 cost_1254_272_join0_4 cost_1254_272_join0_6 rfl rfl rfl

private theorem cost_1254_272_join1_4 : P1_7_1_3.blockEstimate 1254 272 1296 502 = 10596505836 :=
  @P1_7_1_3.block_append 1254 272 1296 1552 256 246 502 9157072265 1439433571 10596505836 cost_1254_272_join0_8 cost_1254_272_join0_10 rfl rfl rfl

private theorem cost_1254_272_join2_0 : P1_7_1_3.blockEstimate 1254 272 272 1024 = 57705741470 :=
  @P1_7_1_3.block_append 1254 272 272 784 512 512 1024 17743699428 39962042042 57705741470 cost_1254_272_join1_0 cost_1254_272_join1_2 rfl rfl rfl

private theorem cost_1254_272_join3_0 : P1_7_1_3.blockEstimate 1254 272 272 1526 = 68302247306 :=
  @P1_7_1_3.block_append 1254 272 272 1296 1024 502 1526 57705741470 10596505836 68302247306 cost_1254_272_join2_0 cost_1254_272_join1_4 rfl rfl rfl

private theorem cost_1254_272_total : P1_7_1_3.momentEstimate 1254 272 = 68302247306 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1254 + 272 = 1526 by decide]
  exact cost_1254_272_join3_0

theorem moment1254_272 : P1_7_1.groupedPoleMoment 1254 272 ≤ 68302247306 :=
  (P1_7_1_3.grouped_bound 1254 272).trans_eq cost_1254_272_total
private theorem cost_1254_274_block0 : P1_7_1_3.blockEstimate 1254 274 274 128 = 414554400 := by decide +kernel

private theorem cost_1254_274_block1 : P1_7_1_3.blockEstimate 1254 274 402 128 = 2592024864 := by decide +kernel

private theorem cost_1254_274_block2 : P1_7_1_3.blockEstimate 1254 274 530 128 = 5989028786 := by decide +kernel

private theorem cost_1254_274_block3 : P1_7_1_3.blockEstimate 1254 274 658 128 = 8795054400 := by decide +kernel

private theorem cost_1254_274_block4 : P1_7_1_3.blockEstimate 1254 274 786 128 = 10448609600 := by decide +kernel

private theorem cost_1254_274_block5 : P1_7_1_3.blockEstimate 1254 274 914 128 = 10948731200 := by decide +kernel

private theorem cost_1254_274_block6 : P1_7_1_3.blockEstimate 1254 274 1042 128 = 10295419200 := by decide +kernel

private theorem cost_1254_274_block7 : P1_7_1_3.blockEstimate 1254 274 1170 128 = 8494212357 := by decide +kernel

private theorem cost_1254_274_block8 : P1_7_1_3.blockEstimate 1254 274 1298 128 = 5904243308 := by decide +kernel

private theorem cost_1254_274_block9 : P1_7_1_3.blockEstimate 1254 274 1426 128 = 3336939973 := by decide +kernel

private theorem cost_1254_274_block10 : P1_7_1_3.blockEstimate 1254 274 1554 128 = 1294295680 := by decide +kernel

private theorem cost_1254_274_block11 : P1_7_1_3.blockEstimate 1254 274 1682 120 = 179103320 := by decide +kernel

private theorem cost_1254_274_join0_0 : P1_7_1_3.blockEstimate 1254 274 274 256 = 3006579264 :=
  @P1_7_1_3.block_append 1254 274 274 402 128 128 256 414554400 2592024864 3006579264 cost_1254_274_block0 cost_1254_274_block1 rfl rfl rfl

private theorem cost_1254_274_join0_2 : P1_7_1_3.blockEstimate 1254 274 530 256 = 14784083186 :=
  @P1_7_1_3.block_append 1254 274 530 658 128 128 256 5989028786 8795054400 14784083186 cost_1254_274_block2 cost_1254_274_block3 rfl rfl rfl

private theorem cost_1254_274_join0_4 : P1_7_1_3.blockEstimate 1254 274 786 256 = 21397340800 :=
  @P1_7_1_3.block_append 1254 274 786 914 128 128 256 10448609600 10948731200 21397340800 cost_1254_274_block4 cost_1254_274_block5 rfl rfl rfl

private theorem cost_1254_274_join0_6 : P1_7_1_3.blockEstimate 1254 274 1042 256 = 18789631557 :=
  @P1_7_1_3.block_append 1254 274 1042 1170 128 128 256 10295419200 8494212357 18789631557 cost_1254_274_block6 cost_1254_274_block7 rfl rfl rfl

private theorem cost_1254_274_join0_8 : P1_7_1_3.blockEstimate 1254 274 1298 256 = 9241183281 :=
  @P1_7_1_3.block_append 1254 274 1298 1426 128 128 256 5904243308 3336939973 9241183281 cost_1254_274_block8 cost_1254_274_block9 rfl rfl rfl

private theorem cost_1254_274_join0_10 : P1_7_1_3.blockEstimate 1254 274 1554 248 = 1473399000 :=
  @P1_7_1_3.block_append 1254 274 1554 1682 128 120 248 1294295680 179103320 1473399000 cost_1254_274_block10 cost_1254_274_block11 rfl rfl rfl

private theorem cost_1254_274_join1_0 : P1_7_1_3.blockEstimate 1254 274 274 512 = 17790662450 :=
  @P1_7_1_3.block_append 1254 274 274 530 256 256 512 3006579264 14784083186 17790662450 cost_1254_274_join0_0 cost_1254_274_join0_2 rfl rfl rfl

private theorem cost_1254_274_join1_2 : P1_7_1_3.blockEstimate 1254 274 786 512 = 40186972357 :=
  @P1_7_1_3.block_append 1254 274 786 1042 256 256 512 21397340800 18789631557 40186972357 cost_1254_274_join0_4 cost_1254_274_join0_6 rfl rfl rfl

private theorem cost_1254_274_join1_4 : P1_7_1_3.blockEstimate 1254 274 1298 504 = 10714582281 :=
  @P1_7_1_3.block_append 1254 274 1298 1554 256 248 504 9241183281 1473399000 10714582281 cost_1254_274_join0_8 cost_1254_274_join0_10 rfl rfl rfl

private theorem cost_1254_274_join2_0 : P1_7_1_3.blockEstimate 1254 274 274 1024 = 57977634807 :=
  @P1_7_1_3.block_append 1254 274 274 786 512 512 1024 17790662450 40186972357 57977634807 cost_1254_274_join1_0 cost_1254_274_join1_2 rfl rfl rfl

private theorem cost_1254_274_join3_0 : P1_7_1_3.blockEstimate 1254 274 274 1528 = 68692217088 :=
  @P1_7_1_3.block_append 1254 274 274 1298 1024 504 1528 57977634807 10714582281 68692217088 cost_1254_274_join2_0 cost_1254_274_join1_4 rfl rfl rfl

private theorem cost_1254_274_total : P1_7_1_3.momentEstimate 1254 274 = 68692217088 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1254 + 274 = 1528 by decide]
  exact cost_1254_274_join3_0

theorem moment1254_274 : P1_7_1.groupedPoleMoment 1254 274 ≤ 68692217088 :=
  (P1_7_1_3.grouped_bound 1254 274).trans_eq cost_1254_274_total

end Research6966.HelperRescueCatalogue

end Merged6967_Near6967RescueMoment11

section Merged6967_Near6967RescueMoment12
set_option Elab.async false


set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem cost_1255_272_block0 : P1_7_1_3.blockEstimate 1255 272 272 128 = 414912160 := by decide +kernel

private theorem cost_1255_272_block1 : P1_7_1_3.blockEstimate 1255 272 400 128 = 2594496160 := by decide +kernel

private theorem cost_1255_272_block2 : P1_7_1_3.blockEstimate 1255 272 528 128 = 5984295308 := by decide +kernel

private theorem cost_1255_272_block3 : P1_7_1_3.blockEstimate 1255 272 656 128 = 8770192704 := by decide +kernel

private theorem cost_1255_272_block4 : P1_7_1_3.blockEstimate 1255 272 784 128 = 10411722048 := by decide +kernel

private theorem cost_1255_272_block5 : P1_7_1_3.blockEstimate 1255 272 912 128 = 10908206400 := by decide +kernel

private theorem cost_1255_272_block6 : P1_7_1_3.blockEstimate 1255 272 1040 128 = 10259645760 := by decide +kernel

private theorem cost_1255_272_block7 : P1_7_1_3.blockEstimate 1255 272 1168 128 = 8470541820 := by decide +kernel

private theorem cost_1255_272_block8 : P1_7_1_3.blockEstimate 1255 272 1296 128 = 5885374880 := by decide +kernel

private theorem cost_1255_272_block9 : P1_7_1_3.blockEstimate 1255 272 1424 128 = 3320539910 := by decide +kernel

private theorem cost_1255_272_block10 : P1_7_1_3.blockEstimate 1255 272 1552 128 = 1282700416 := by decide +kernel

private theorem cost_1255_272_block11 : P1_7_1_3.blockEstimate 1255 272 1680 119 = 174931240 := by decide +kernel

private theorem cost_1255_272_join0_0 : P1_7_1_3.blockEstimate 1255 272 272 256 = 3009408320 :=
  @P1_7_1_3.block_append 1255 272 272 400 128 128 256 414912160 2594496160 3009408320 cost_1255_272_block0 cost_1255_272_block1 rfl rfl rfl

private theorem cost_1255_272_join0_2 : P1_7_1_3.blockEstimate 1255 272 528 256 = 14754488012 :=
  @P1_7_1_3.block_append 1255 272 528 656 128 128 256 5984295308 8770192704 14754488012 cost_1255_272_block2 cost_1255_272_block3 rfl rfl rfl

private theorem cost_1255_272_join0_4 : P1_7_1_3.blockEstimate 1255 272 784 256 = 21319928448 :=
  @P1_7_1_3.block_append 1255 272 784 912 128 128 256 10411722048 10908206400 21319928448 cost_1255_272_block4 cost_1255_272_block5 rfl rfl rfl

private theorem cost_1255_272_join0_6 : P1_7_1_3.blockEstimate 1255 272 1040 256 = 18730187580 :=
  @P1_7_1_3.block_append 1255 272 1040 1168 128 128 256 10259645760 8470541820 18730187580 cost_1255_272_block6 cost_1255_272_block7 rfl rfl rfl

private theorem cost_1255_272_join0_8 : P1_7_1_3.blockEstimate 1255 272 1296 256 = 9205914790 :=
  @P1_7_1_3.block_append 1255 272 1296 1424 128 128 256 5885374880 3320539910 9205914790 cost_1255_272_block8 cost_1255_272_block9 rfl rfl rfl

private theorem cost_1255_272_join0_10 : P1_7_1_3.blockEstimate 1255 272 1552 247 = 1457631656 :=
  @P1_7_1_3.block_append 1255 272 1552 1680 128 119 247 1282700416 174931240 1457631656 cost_1255_272_block10 cost_1255_272_block11 rfl rfl rfl

private theorem cost_1255_272_join1_0 : P1_7_1_3.blockEstimate 1255 272 272 512 = 17763896332 :=
  @P1_7_1_3.block_append 1255 272 272 528 256 256 512 3009408320 14754488012 17763896332 cost_1255_272_join0_0 cost_1255_272_join0_2 rfl rfl rfl

private theorem cost_1255_272_join1_2 : P1_7_1_3.blockEstimate 1255 272 784 512 = 40050116028 :=
  @P1_7_1_3.block_append 1255 272 784 1040 256 256 512 21319928448 18730187580 40050116028 cost_1255_272_join0_4 cost_1255_272_join0_6 rfl rfl rfl

private theorem cost_1255_272_join1_4 : P1_7_1_3.blockEstimate 1255 272 1296 503 = 10663546446 :=
  @P1_7_1_3.block_append 1255 272 1296 1552 256 247 503 9205914790 1457631656 10663546446 cost_1255_272_join0_8 cost_1255_272_join0_10 rfl rfl rfl

private theorem cost_1255_272_join2_0 : P1_7_1_3.blockEstimate 1255 272 272 1024 = 57814012360 :=
  @P1_7_1_3.block_append 1255 272 272 784 512 512 1024 17763896332 40050116028 57814012360 cost_1255_272_join1_0 cost_1255_272_join1_2 rfl rfl rfl

private theorem cost_1255_272_join3_0 : P1_7_1_3.blockEstimate 1255 272 272 1527 = 68477558806 :=
  @P1_7_1_3.block_append 1255 272 272 1296 1024 503 1527 57814012360 10663546446 68477558806 cost_1255_272_join2_0 cost_1255_272_join1_4 rfl rfl rfl

private theorem cost_1255_272_total : P1_7_1_3.momentEstimate 1255 272 = 68477558806 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1255 + 272 = 1527 by decide]
  exact cost_1255_272_join3_0

theorem moment1255_272 : P1_7_1.groupedPoleMoment 1255 272 ≤ 68477558806 :=
  (P1_7_1_3.grouped_bound 1255 272).trans_eq cost_1255_272_total
private theorem cost_1255_274_block0 : P1_7_1_3.blockEstimate 1255 274 274 128 = 414912160 := by decide +kernel

private theorem cost_1255_274_block1 : P1_7_1_3.blockEstimate 1255 274 402 128 = 2594496160 := by decide +kernel

private theorem cost_1255_274_block2 : P1_7_1_3.blockEstimate 1255 274 530 128 = 5995488955 := by decide +kernel

private theorem cost_1255_274_block3 : P1_7_1_3.blockEstimate 1255 274 658 128 = 8806019200 := by decide +kernel

private theorem cost_1255_274_block4 : P1_7_1_3.blockEstimate 1255 274 786 128 = 10464080000 := by decide +kernel

private theorem cost_1255_274_block5 : P1_7_1_3.blockEstimate 1255 274 914 128 = 10968707200 := by decide +kernel

private theorem cost_1255_274_block6 : P1_7_1_3.blockEstimate 1255 274 1042 128 = 10319900800 := by decide +kernel

private theorem cost_1255_274_block7 : P1_7_1_3.blockEstimate 1255 274 1170 128 = 8522833455 := by decide +kernel

private theorem cost_1255_274_block8 : P1_7_1_3.blockEstimate 1255 274 1298 128 = 5931495958 := by decide +kernel

private theorem cost_1255_274_block9 : P1_7_1_3.blockEstimate 1255 274 1426 128 = 3358751428 := by decide +kernel

private theorem cost_1255_274_block10 : P1_7_1_3.blockEstimate 1255 274 1554 128 = 1308238672 := by decide +kernel

private theorem cost_1255_274_block11 : P1_7_1_3.blockEstimate 1255 274 1682 121 = 183644000 := by decide +kernel

private theorem cost_1255_274_join0_0 : P1_7_1_3.blockEstimate 1255 274 274 256 = 3009408320 :=
  @P1_7_1_3.block_append 1255 274 274 402 128 128 256 414912160 2594496160 3009408320 cost_1255_274_block0 cost_1255_274_block1 rfl rfl rfl

private theorem cost_1255_274_join0_2 : P1_7_1_3.blockEstimate 1255 274 530 256 = 14801508155 :=
  @P1_7_1_3.block_append 1255 274 530 658 128 128 256 5995488955 8806019200 14801508155 cost_1255_274_block2 cost_1255_274_block3 rfl rfl rfl

private theorem cost_1255_274_join0_4 : P1_7_1_3.blockEstimate 1255 274 786 256 = 21432787200 :=
  @P1_7_1_3.block_append 1255 274 786 914 128 128 256 10464080000 10968707200 21432787200 cost_1255_274_block4 cost_1255_274_block5 rfl rfl rfl

private theorem cost_1255_274_join0_6 : P1_7_1_3.blockEstimate 1255 274 1042 256 = 18842734255 :=
  @P1_7_1_3.block_append 1255 274 1042 1170 128 128 256 10319900800 8522833455 18842734255 cost_1255_274_block6 cost_1255_274_block7 rfl rfl rfl

private theorem cost_1255_274_join0_8 : P1_7_1_3.blockEstimate 1255 274 1298 256 = 9290247386 :=
  @P1_7_1_3.block_append 1255 274 1298 1426 128 128 256 5931495958 3358751428 9290247386 cost_1255_274_block8 cost_1255_274_block9 rfl rfl rfl

private theorem cost_1255_274_join0_10 : P1_7_1_3.blockEstimate 1255 274 1554 249 = 1491882672 :=
  @P1_7_1_3.block_append 1255 274 1554 1682 128 121 249 1308238672 183644000 1491882672 cost_1255_274_block10 cost_1255_274_block11 rfl rfl rfl

private theorem cost_1255_274_join1_0 : P1_7_1_3.blockEstimate 1255 274 274 512 = 17810916475 :=
  @P1_7_1_3.block_append 1255 274 274 530 256 256 512 3009408320 14801508155 17810916475 cost_1255_274_join0_0 cost_1255_274_join0_2 rfl rfl rfl

private theorem cost_1255_274_join1_2 : P1_7_1_3.blockEstimate 1255 274 786 512 = 40275521455 :=
  @P1_7_1_3.block_append 1255 274 786 1042 256 256 512 21432787200 18842734255 40275521455 cost_1255_274_join0_4 cost_1255_274_join0_6 rfl rfl rfl

private theorem cost_1255_274_join1_4 : P1_7_1_3.blockEstimate 1255 274 1298 505 = 10782130058 :=
  @P1_7_1_3.block_append 1255 274 1298 1554 256 249 505 9290247386 1491882672 10782130058 cost_1255_274_join0_8 cost_1255_274_join0_10 rfl rfl rfl

private theorem cost_1255_274_join2_0 : P1_7_1_3.blockEstimate 1255 274 274 1024 = 58086437930 :=
  @P1_7_1_3.block_append 1255 274 274 786 512 512 1024 17810916475 40275521455 58086437930 cost_1255_274_join1_0 cost_1255_274_join1_2 rfl rfl rfl

private theorem cost_1255_274_join3_0 : P1_7_1_3.blockEstimate 1255 274 274 1529 = 68868567988 :=
  @P1_7_1_3.block_append 1255 274 274 1298 1024 505 1529 58086437930 10782130058 68868567988 cost_1255_274_join2_0 cost_1255_274_join1_4 rfl rfl rfl

private theorem cost_1255_274_total : P1_7_1_3.momentEstimate 1255 274 = 68868567988 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1255 + 274 = 1529 by decide]
  exact cost_1255_274_join3_0

theorem moment1255_274 : P1_7_1.groupedPoleMoment 1255 274 ≤ 68868567988 :=
  (P1_7_1_3.grouped_bound 1255 274).trans_eq cost_1255_274_total
private theorem cost_1255_279_block0 : P1_7_1_3.blockEstimate 1255 279 279 128 = 414912160 := by decide +kernel

private theorem cost_1255_279_block1 : P1_7_1_3.blockEstimate 1255 279 407 128 = 2594496160 := by decide +kernel

private theorem cost_1255_279_block2 : P1_7_1_3.blockEstimate 1255 279 535 128 = 6021706710 := by decide +kernel

private theorem cost_1255_279_block3 : P1_7_1_3.blockEstimate 1255 279 663 128 = 8893776640 := by decide +kernel

private theorem cost_1255_279_block4 : P1_7_1_3.blockEstimate 1255 279 791 128 = 10593452800 := by decide +kernel

private theorem cost_1255_279_block5 : P1_7_1_3.blockEstimate 1255 279 919 128 = 11118723840 := by decide +kernel

private theorem cost_1255_279_block6 : P1_7_1_3.blockEstimate 1255 279 1047 128 = 10469589760 := by decide +kernel

private theorem cost_1255_279_block7 : P1_7_1_3.blockEstimate 1255 279 1175 128 = 8653178772 := by decide +kernel

private theorem cost_1255_279_block8 : P1_7_1_3.blockEstimate 1255 279 1303 128 = 6047244334 := by decide +kernel

private theorem cost_1255_279_block9 : P1_7_1_3.blockEstimate 1255 279 1431 128 = 3455018993 := by decide +kernel

private theorem cost_1255_279_block10 : P1_7_1_3.blockEstimate 1255 279 1559 128 = 1373097744 := by decide +kernel

private theorem cost_1255_279_block11 : P1_7_1_3.blockEstimate 1255 279 1687 126 = 206658320 := by decide +kernel

private theorem cost_1255_279_join0_0 : P1_7_1_3.blockEstimate 1255 279 279 256 = 3009408320 :=
  @P1_7_1_3.block_append 1255 279 279 407 128 128 256 414912160 2594496160 3009408320 cost_1255_279_block0 cost_1255_279_block1 rfl rfl rfl

private theorem cost_1255_279_join0_2 : P1_7_1_3.blockEstimate 1255 279 535 256 = 14915483350 :=
  @P1_7_1_3.block_append 1255 279 535 663 128 128 256 6021706710 8893776640 14915483350 cost_1255_279_block2 cost_1255_279_block3 rfl rfl rfl

private theorem cost_1255_279_join0_4 : P1_7_1_3.blockEstimate 1255 279 791 256 = 21712176640 :=
  @P1_7_1_3.block_append 1255 279 791 919 128 128 256 10593452800 11118723840 21712176640 cost_1255_279_block4 cost_1255_279_block5 rfl rfl rfl

private theorem cost_1255_279_join0_6 : P1_7_1_3.blockEstimate 1255 279 1047 256 = 19122768532 :=
  @P1_7_1_3.block_append 1255 279 1047 1175 128 128 256 10469589760 8653178772 19122768532 cost_1255_279_block6 cost_1255_279_block7 rfl rfl rfl

private theorem cost_1255_279_join0_8 : P1_7_1_3.blockEstimate 1255 279 1303 256 = 9502263327 :=
  @P1_7_1_3.block_append 1255 279 1303 1431 128 128 256 6047244334 3455018993 9502263327 cost_1255_279_block8 cost_1255_279_block9 rfl rfl rfl

private theorem cost_1255_279_join0_10 : P1_7_1_3.blockEstimate 1255 279 1559 254 = 1579756064 :=
  @P1_7_1_3.block_append 1255 279 1559 1687 128 126 254 1373097744 206658320 1579756064 cost_1255_279_block10 cost_1255_279_block11 rfl rfl rfl

private theorem cost_1255_279_join1_0 : P1_7_1_3.blockEstimate 1255 279 279 512 = 17924891670 :=
  @P1_7_1_3.block_append 1255 279 279 535 256 256 512 3009408320 14915483350 17924891670 cost_1255_279_join0_0 cost_1255_279_join0_2 rfl rfl rfl

private theorem cost_1255_279_join1_2 : P1_7_1_3.blockEstimate 1255 279 791 512 = 40834945172 :=
  @P1_7_1_3.block_append 1255 279 791 1047 256 256 512 21712176640 19122768532 40834945172 cost_1255_279_join0_4 cost_1255_279_join0_6 rfl rfl rfl

private theorem cost_1255_279_join1_4 : P1_7_1_3.blockEstimate 1255 279 1303 510 = 11082019391 :=
  @P1_7_1_3.block_append 1255 279 1303 1559 256 254 510 9502263327 1579756064 11082019391 cost_1255_279_join0_8 cost_1255_279_join0_10 rfl rfl rfl

private theorem cost_1255_279_join2_0 : P1_7_1_3.blockEstimate 1255 279 279 1024 = 58759836842 :=
  @P1_7_1_3.block_append 1255 279 279 791 512 512 1024 17924891670 40834945172 58759836842 cost_1255_279_join1_0 cost_1255_279_join1_2 rfl rfl rfl

private theorem cost_1255_279_join3_0 : P1_7_1_3.blockEstimate 1255 279 279 1534 = 69841856233 :=
  @P1_7_1_3.block_append 1255 279 279 1303 1024 510 1534 58759836842 11082019391 69841856233 cost_1255_279_join2_0 cost_1255_279_join1_4 rfl rfl rfl

private theorem cost_1255_279_total : P1_7_1_3.momentEstimate 1255 279 = 69841856233 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1255 + 279 = 1534 by decide]
  exact cost_1255_279_join3_0

theorem moment1255_279 : P1_7_1.groupedPoleMoment 1255 279 ≤ 69841856233 :=
  (P1_7_1_3.grouped_bound 1255 279).trans_eq cost_1255_279_total
private theorem cost_1256_272_block0 : P1_7_1_3.blockEstimate 1256 272 272 128 = 415269920 := by decide +kernel

private theorem cost_1256_272_block1 : P1_7_1_3.blockEstimate 1256 272 400 128 = 2596967456 := by decide +kernel

private theorem cost_1256_272_block2 : P1_7_1_3.blockEstimate 1256 272 528 128 = 5990743156 := by decide +kernel

private theorem cost_1256_272_block3 : P1_7_1_3.blockEstimate 1256 272 656 128 = 8781112704 := by decide +kernel

private theorem cost_1256_272_block4 : P1_7_1_3.blockEstimate 1256 272 784 128 = 10427114880 := by decide +kernel

private theorem cost_1256_272_block5 : P1_7_1_3.blockEstimate 1256 272 912 128 = 10928072064 := by decide +kernel

private theorem cost_1256_272_block6 : P1_7_1_3.blockEstimate 1256 272 1040 128 = 10283984256 := by decide +kernel

private theorem cost_1256_272_block7 : P1_7_1_3.blockEstimate 1256 272 1168 128 = 8499034795 := by decide +kernel

private theorem cost_1256_272_block8 : P1_7_1_3.blockEstimate 1256 272 1296 128 = 5912586470 := by decide +kernel

private theorem cost_1256_272_block9 : P1_7_1_3.blockEstimate 1256 272 1424 128 = 3342302865 := by decide +kernel

private theorem cost_1256_272_block10 : P1_7_1_3.blockEstimate 1256 272 1552 128 = 1296585280 := by decide +kernel

private theorem cost_1256_272_block11 : P1_7_1_3.blockEstimate 1256 272 1680 120 = 179402220 := by decide +kernel

private theorem cost_1256_272_join0_0 : P1_7_1_3.blockEstimate 1256 272 272 256 = 3012237376 :=
  @P1_7_1_3.block_append 1256 272 272 400 128 128 256 415269920 2596967456 3012237376 cost_1256_272_block0 cost_1256_272_block1 rfl rfl rfl

private theorem cost_1256_272_join0_2 : P1_7_1_3.blockEstimate 1256 272 528 256 = 14771855860 :=
  @P1_7_1_3.block_append 1256 272 528 656 128 128 256 5990743156 8781112704 14771855860 cost_1256_272_block2 cost_1256_272_block3 rfl rfl rfl

private theorem cost_1256_272_join0_4 : P1_7_1_3.blockEstimate 1256 272 784 256 = 21355186944 :=
  @P1_7_1_3.block_append 1256 272 784 912 128 128 256 10427114880 10928072064 21355186944 cost_1256_272_block4 cost_1256_272_block5 rfl rfl rfl

private theorem cost_1256_272_join0_6 : P1_7_1_3.blockEstimate 1256 272 1040 256 = 18783019051 :=
  @P1_7_1_3.block_append 1256 272 1040 1168 128 128 256 10283984256 8499034795 18783019051 cost_1256_272_block6 cost_1256_272_block7 rfl rfl rfl

private theorem cost_1256_272_join0_8 : P1_7_1_3.blockEstimate 1256 272 1296 256 = 9254889335 :=
  @P1_7_1_3.block_append 1256 272 1296 1424 128 128 256 5912586470 3342302865 9254889335 cost_1256_272_block8 cost_1256_272_block9 rfl rfl rfl

private theorem cost_1256_272_join0_10 : P1_7_1_3.blockEstimate 1256 272 1552 248 = 1475987500 :=
  @P1_7_1_3.block_append 1256 272 1552 1680 128 120 248 1296585280 179402220 1475987500 cost_1256_272_block10 cost_1256_272_block11 rfl rfl rfl

private theorem cost_1256_272_join1_0 : P1_7_1_3.blockEstimate 1256 272 272 512 = 17784093236 :=
  @P1_7_1_3.block_append 1256 272 272 528 256 256 512 3012237376 14771855860 17784093236 cost_1256_272_join0_0 cost_1256_272_join0_2 rfl rfl rfl

private theorem cost_1256_272_join1_2 : P1_7_1_3.blockEstimate 1256 272 784 512 = 40138205995 :=
  @P1_7_1_3.block_append 1256 272 784 1040 256 256 512 21355186944 18783019051 40138205995 cost_1256_272_join0_4 cost_1256_272_join0_6 rfl rfl rfl

private theorem cost_1256_272_join1_4 : P1_7_1_3.blockEstimate 1256 272 1296 504 = 10730876835 :=
  @P1_7_1_3.block_append 1256 272 1296 1552 256 248 504 9254889335 1475987500 10730876835 cost_1256_272_join0_8 cost_1256_272_join0_10 rfl rfl rfl

private theorem cost_1256_272_join2_0 : P1_7_1_3.blockEstimate 1256 272 272 1024 = 57922299231 :=
  @P1_7_1_3.block_append 1256 272 272 784 512 512 1024 17784093236 40138205995 57922299231 cost_1256_272_join1_0 cost_1256_272_join1_2 rfl rfl rfl

private theorem cost_1256_272_join3_0 : P1_7_1_3.blockEstimate 1256 272 272 1528 = 68653176066 :=
  @P1_7_1_3.block_append 1256 272 272 1296 1024 504 1528 57922299231 10730876835 68653176066 cost_1256_272_join2_0 cost_1256_272_join1_4 rfl rfl rfl

private theorem cost_1256_272_total : P1_7_1_3.momentEstimate 1256 272 = 68653176066 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1256 + 272 = 1528 by decide]
  exact cost_1256_272_join3_0

theorem moment1256_272 : P1_7_1.groupedPoleMoment 1256 272 ≤ 68653176066 :=
  (P1_7_1_3.grouped_bound 1256 272).trans_eq cost_1256_272_total
private theorem cost_1256_279_block0 : P1_7_1_3.blockEstimate 1256 279 279 128 = 415269920 := by decide +kernel

private theorem cost_1256_279_block1 : P1_7_1_3.blockEstimate 1256 279 407 128 = 2596967456 := by decide +kernel

private theorem cost_1256_279_block2 : P1_7_1_3.blockEstimate 1256 279 535 128 = 6028195774 := by decide +kernel

private theorem cost_1256_279_block3 : P1_7_1_3.blockEstimate 1256 279 663 128 = 8904851200 := by decide +kernel

private theorem cost_1256_279_block4 : P1_7_1_3.blockEstimate 1256 279 791 128 = 10609114880 := by decide +kernel

private theorem cost_1256_279_block5 : P1_7_1_3.blockEstimate 1256 279 919 128 = 11138973440 := by decide +kernel

private theorem cost_1256_279_block6 : P1_7_1_3.blockEstimate 1256 279 1047 128 = 10494426880 := by decide +kernel

private theorem cost_1256_279_block7 : P1_7_1_3.blockEstimate 1256 279 1175 128 = 8682170280 := by decide +kernel

private theorem cost_1256_279_block8 : P1_7_1_3.blockEstimate 1256 279 1303 128 = 6074809062 := by decide +kernel

private theorem cost_1256_279_block9 : P1_7_1_3.blockEstimate 1256 279 1431 128 = 3477201729 := by decide +kernel

private theorem cost_1256_279_block10 : P1_7_1_3.blockEstimate 1256 279 1559 128 = 1387471776 := by decide +kernel

private theorem cost_1256_279_block11 : P1_7_1_3.blockEstimate 1256 279 1687 127 = 211653536 := by decide +kernel

private theorem cost_1256_279_join0_0 : P1_7_1_3.blockEstimate 1256 279 279 256 = 3012237376 :=
  @P1_7_1_3.block_append 1256 279 279 407 128 128 256 415269920 2596967456 3012237376 cost_1256_279_block0 cost_1256_279_block1 rfl rfl rfl

private theorem cost_1256_279_join0_2 : P1_7_1_3.blockEstimate 1256 279 535 256 = 14933046974 :=
  @P1_7_1_3.block_append 1256 279 535 663 128 128 256 6028195774 8904851200 14933046974 cost_1256_279_block2 cost_1256_279_block3 rfl rfl rfl

private theorem cost_1256_279_join0_4 : P1_7_1_3.blockEstimate 1256 279 791 256 = 21748088320 :=
  @P1_7_1_3.block_append 1256 279 791 919 128 128 256 10609114880 11138973440 21748088320 cost_1256_279_block4 cost_1256_279_block5 rfl rfl rfl

private theorem cost_1256_279_join0_6 : P1_7_1_3.blockEstimate 1256 279 1047 256 = 19176597160 :=
  @P1_7_1_3.block_append 1256 279 1047 1175 128 128 256 10494426880 8682170280 19176597160 cost_1256_279_block6 cost_1256_279_block7 rfl rfl rfl

private theorem cost_1256_279_join0_8 : P1_7_1_3.blockEstimate 1256 279 1303 256 = 9552010791 :=
  @P1_7_1_3.block_append 1256 279 1303 1431 128 128 256 6074809062 3477201729 9552010791 cost_1256_279_block8 cost_1256_279_block9 rfl rfl rfl

private theorem cost_1256_279_join0_10 : P1_7_1_3.blockEstimate 1256 279 1559 255 = 1599125312 :=
  @P1_7_1_3.block_append 1256 279 1559 1687 128 127 255 1387471776 211653536 1599125312 cost_1256_279_block10 cost_1256_279_block11 rfl rfl rfl

private theorem cost_1256_279_join1_0 : P1_7_1_3.blockEstimate 1256 279 279 512 = 17945284350 :=
  @P1_7_1_3.block_append 1256 279 279 535 256 256 512 3012237376 14933046974 17945284350 cost_1256_279_join0_0 cost_1256_279_join0_2 rfl rfl rfl

private theorem cost_1256_279_join1_2 : P1_7_1_3.blockEstimate 1256 279 791 512 = 40924685480 :=
  @P1_7_1_3.block_append 1256 279 791 1047 256 256 512 21748088320 19176597160 40924685480 cost_1256_279_join0_4 cost_1256_279_join0_6 rfl rfl rfl

private theorem cost_1256_279_join1_4 : P1_7_1_3.blockEstimate 1256 279 1303 511 = 11151136103 :=
  @P1_7_1_3.block_append 1256 279 1303 1559 256 255 511 9552010791 1599125312 11151136103 cost_1256_279_join0_8 cost_1256_279_join0_10 rfl rfl rfl

private theorem cost_1256_279_join2_0 : P1_7_1_3.blockEstimate 1256 279 279 1024 = 58869969830 :=
  @P1_7_1_3.block_append 1256 279 279 791 512 512 1024 17945284350 40924685480 58869969830 cost_1256_279_join1_0 cost_1256_279_join1_2 rfl rfl rfl

private theorem cost_1256_279_join3_0 : P1_7_1_3.blockEstimate 1256 279 279 1535 = 70021105933 :=
  @P1_7_1_3.block_append 1256 279 279 1303 1024 511 1535 58869969830 11151136103 70021105933 cost_1256_279_join2_0 cost_1256_279_join1_4 rfl rfl rfl

private theorem cost_1256_279_total : P1_7_1_3.momentEstimate 1256 279 = 70021105933 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1256 + 279 = 1535 by decide]
  exact cost_1256_279_join3_0

theorem moment1256_279 : P1_7_1.groupedPoleMoment 1256 279 ≤ 70021105933 :=
  (P1_7_1_3.grouped_bound 1256 279).trans_eq cost_1256_279_total
private theorem cost_1274_274_block0 : P1_7_1_3.blockEstimate 1274 274 274 128 = 421709600 := by decide +kernel

private theorem cost_1274_274_block1 : P1_7_1_3.blockEstimate 1274 274 402 128 = 2641450784 := by decide +kernel

private theorem cost_1274_274_block2 : P1_7_1_3.blockEstimate 1274 274 530 128 = 6118232166 := by decide +kernel

private theorem cost_1274_274_block3 : P1_7_1_3.blockEstimate 1274 274 658 128 = 9014350400 := by decide +kernel

private theorem cost_1274_274_block4 : P1_7_1_3.blockEstimate 1274 274 786 128 = 10758017600 := by decide +kernel

private theorem cost_1274_274_block5 : P1_7_1_3.blockEstimate 1274 274 914 128 = 11348251200 := by decide +kernel

private theorem cost_1274_274_block6 : P1_7_1_3.blockEstimate 1274 274 1042 128 = 10785051200 := by decide +kernel

private theorem cost_1274_274_block7 : P1_7_1_3.blockEstimate 1274 274 1170 128 = 9069337246 := by decide +kernel

private theorem cost_1274_274_block8 : P1_7_1_3.blockEstimate 1274 274 1298 128 = 6460658917 := by decide +kernel

private theorem cost_1274_274_block9 : P1_7_1_3.blockEstimate 1274 274 1426 128 = 3786733730 := by decide +kernel

private theorem cost_1274_274_block10 : P1_7_1_3.blockEstimate 1274 274 1554 128 = 1588798880 := by decide +kernel

private theorem cost_1274_274_block11 : P1_7_1_3.blockEstimate 1274 274 1682 128 = 285167008 := by decide +kernel

private theorem cost_1274_274_block12 : P1_7_1_3.blockEstimate 1274 274 1810 12 = 257607 := by decide +kernel

private theorem cost_1274_274_join0_0 : P1_7_1_3.blockEstimate 1274 274 274 256 = 3063160384 :=
  @P1_7_1_3.block_append 1274 274 274 402 128 128 256 421709600 2641450784 3063160384 cost_1274_274_block0 cost_1274_274_block1 rfl rfl rfl

private theorem cost_1274_274_join0_2 : P1_7_1_3.blockEstimate 1274 274 530 256 = 15132582566 :=
  @P1_7_1_3.block_append 1274 274 530 658 128 128 256 6118232166 9014350400 15132582566 cost_1274_274_block2 cost_1274_274_block3 rfl rfl rfl

private theorem cost_1274_274_join0_4 : P1_7_1_3.blockEstimate 1274 274 786 256 = 22106268800 :=
  @P1_7_1_3.block_append 1274 274 786 914 128 128 256 10758017600 11348251200 22106268800 cost_1274_274_block4 cost_1274_274_block5 rfl rfl rfl

private theorem cost_1274_274_join0_6 : P1_7_1_3.blockEstimate 1274 274 1042 256 = 19854388446 :=
  @P1_7_1_3.block_append 1274 274 1042 1170 128 128 256 10785051200 9069337246 19854388446 cost_1274_274_block6 cost_1274_274_block7 rfl rfl rfl

private theorem cost_1274_274_join0_8 : P1_7_1_3.blockEstimate 1274 274 1298 256 = 10247392647 :=
  @P1_7_1_3.block_append 1274 274 1298 1426 128 128 256 6460658917 3786733730 10247392647 cost_1274_274_block8 cost_1274_274_block9 rfl rfl rfl

private theorem cost_1274_274_join0_10 : P1_7_1_3.blockEstimate 1274 274 1554 256 = 1873965888 :=
  @P1_7_1_3.block_append 1274 274 1554 1682 128 128 256 1588798880 285167008 1873965888 cost_1274_274_block10 cost_1274_274_block11 rfl rfl rfl

private theorem cost_1274_274_join1_0 : P1_7_1_3.blockEstimate 1274 274 274 512 = 18195742950 :=
  @P1_7_1_3.block_append 1274 274 274 530 256 256 512 3063160384 15132582566 18195742950 cost_1274_274_join0_0 cost_1274_274_join0_2 rfl rfl rfl

private theorem cost_1274_274_join1_2 : P1_7_1_3.blockEstimate 1274 274 786 512 = 41960657246 :=
  @P1_7_1_3.block_append 1274 274 786 1042 256 256 512 22106268800 19854388446 41960657246 cost_1274_274_join0_4 cost_1274_274_join0_6 rfl rfl rfl

private theorem cost_1274_274_join1_4 : P1_7_1_3.blockEstimate 1274 274 1298 512 = 12121358535 :=
  @P1_7_1_3.block_append 1274 274 1298 1554 256 256 512 10247392647 1873965888 12121358535 cost_1274_274_join0_8 cost_1274_274_join0_10 rfl rfl rfl

private theorem cost_1274_274_join2_0 : P1_7_1_3.blockEstimate 1274 274 274 1024 = 60156400196 :=
  @P1_7_1_3.block_append 1274 274 274 786 512 512 1024 18195742950 41960657246 60156400196 cost_1274_274_join1_0 cost_1274_274_join1_2 rfl rfl rfl

private theorem cost_1274_274_join2_2 : P1_7_1_3.blockEstimate 1274 274 1298 524 = 12121616142 :=
  @P1_7_1_3.block_append 1274 274 1298 1810 512 12 524 12121358535 257607 12121616142 cost_1274_274_join1_4 cost_1274_274_block12 rfl rfl rfl

private theorem cost_1274_274_join3_0 : P1_7_1_3.blockEstimate 1274 274 274 1548 = 72278016338 :=
  @P1_7_1_3.block_append 1274 274 274 1298 1024 524 1548 60156400196 12121616142 72278016338 cost_1274_274_join2_0 cost_1274_274_join2_2 rfl rfl rfl

private theorem cost_1274_274_total : P1_7_1_3.momentEstimate 1274 274 = 72278016338 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1274 + 274 = 1548 by decide]
  exact cost_1274_274_join3_0

theorem moment1274_274 : P1_7_1.groupedPoleMoment 1274 274 ≤ 72278016338 :=
  (P1_7_1_3.grouped_bound 1274 274).trans_eq cost_1274_274_total
private theorem cost_1343_293_block0 : P1_7_1_3.blockEstimate 1343 293 293 128 = 446395040 := by decide +kernel

private theorem cost_1343_293_block1 : P1_7_1_3.blockEstimate 1343 293 421 128 = 2811970208 := by decide +kernel

private theorem cost_1343_293_block2 : P1_7_1_3.blockEstimate 1343 293 549 128 = 6659564277 := by decide +kernel

private theorem cost_1343_293_block3 : P1_7_1_3.blockEstimate 1343 293 677 128 = 10125858624 := by decide +kernel

private theorem cost_1343_293_block4 : P1_7_1_3.blockEstimate 1343 293 805 128 = 12368123712 := by decide +kernel

private theorem cost_1343_293_block5 : P1_7_1_3.blockEstimate 1343 293 933 128 = 13377263424 := by decide +kernel

private theorem cost_1343_293_block6 : P1_7_1_3.blockEstimate 1343 293 1061 128 = 13153277760 := by decide +kernel

private theorem cost_1343_293_block7 : P1_7_1_3.blockEstimate 1343 293 1189 128 = 11696166720 := by decide +kernel

private theorem cost_1343_293_block8 : P1_7_1_3.blockEstimate 1343 293 1317 128 = 9083911992 := by decide +kernel

private theorem cost_1343_293_block9 : P1_7_1_3.blockEstimate 1343 293 1445 128 = 6027398011 := by decide +kernel

private theorem cost_1343_293_block10 : P1_7_1_3.blockEstimate 1343 293 1573 128 = 3226863457 := by decide +kernel

private theorem cost_1343_293_block11 : P1_7_1_3.blockEstimate 1343 293 1701 128 = 1132821120 := by decide +kernel

private theorem cost_1343_293_block12 : P1_7_1_3.blockEstimate 1343 293 1829 100 = 112982850 := by decide +kernel

private theorem cost_1343_293_join0_0 : P1_7_1_3.blockEstimate 1343 293 293 256 = 3258365248 :=
  @P1_7_1_3.block_append 1343 293 293 421 128 128 256 446395040 2811970208 3258365248 cost_1343_293_block0 cost_1343_293_block1 rfl rfl rfl

private theorem cost_1343_293_join0_2 : P1_7_1_3.blockEstimate 1343 293 549 256 = 16785422901 :=
  @P1_7_1_3.block_append 1343 293 549 677 128 128 256 6659564277 10125858624 16785422901 cost_1343_293_block2 cost_1343_293_block3 rfl rfl rfl

private theorem cost_1343_293_join0_4 : P1_7_1_3.blockEstimate 1343 293 805 256 = 25745387136 :=
  @P1_7_1_3.block_append 1343 293 805 933 128 128 256 12368123712 13377263424 25745387136 cost_1343_293_block4 cost_1343_293_block5 rfl rfl rfl

private theorem cost_1343_293_join0_6 : P1_7_1_3.blockEstimate 1343 293 1061 256 = 24849444480 :=
  @P1_7_1_3.block_append 1343 293 1061 1189 128 128 256 13153277760 11696166720 24849444480 cost_1343_293_block6 cost_1343_293_block7 rfl rfl rfl

private theorem cost_1343_293_join0_8 : P1_7_1_3.blockEstimate 1343 293 1317 256 = 15111310003 :=
  @P1_7_1_3.block_append 1343 293 1317 1445 128 128 256 9083911992 6027398011 15111310003 cost_1343_293_block8 cost_1343_293_block9 rfl rfl rfl

private theorem cost_1343_293_join0_10 : P1_7_1_3.blockEstimate 1343 293 1573 256 = 4359684577 :=
  @P1_7_1_3.block_append 1343 293 1573 1701 128 128 256 3226863457 1132821120 4359684577 cost_1343_293_block10 cost_1343_293_block11 rfl rfl rfl

private theorem cost_1343_293_join1_0 : P1_7_1_3.blockEstimate 1343 293 293 512 = 20043788149 :=
  @P1_7_1_3.block_append 1343 293 293 549 256 256 512 3258365248 16785422901 20043788149 cost_1343_293_join0_0 cost_1343_293_join0_2 rfl rfl rfl

private theorem cost_1343_293_join1_2 : P1_7_1_3.blockEstimate 1343 293 805 512 = 50594831616 :=
  @P1_7_1_3.block_append 1343 293 805 1061 256 256 512 25745387136 24849444480 50594831616 cost_1343_293_join0_4 cost_1343_293_join0_6 rfl rfl rfl

private theorem cost_1343_293_join1_4 : P1_7_1_3.blockEstimate 1343 293 1317 512 = 19470994580 :=
  @P1_7_1_3.block_append 1343 293 1317 1573 256 256 512 15111310003 4359684577 19470994580 cost_1343_293_join0_8 cost_1343_293_join0_10 rfl rfl rfl

private theorem cost_1343_293_join2_0 : P1_7_1_3.blockEstimate 1343 293 293 1024 = 70638619765 :=
  @P1_7_1_3.block_append 1343 293 293 805 512 512 1024 20043788149 50594831616 70638619765 cost_1343_293_join1_0 cost_1343_293_join1_2 rfl rfl rfl

private theorem cost_1343_293_join2_2 : P1_7_1_3.blockEstimate 1343 293 1317 612 = 19583977430 :=
  @P1_7_1_3.block_append 1343 293 1317 1829 512 100 612 19470994580 112982850 19583977430 cost_1343_293_join1_4 cost_1343_293_block12 rfl rfl rfl

private theorem cost_1343_293_join3_0 : P1_7_1_3.blockEstimate 1343 293 293 1636 = 90222597195 :=
  @P1_7_1_3.block_append 1343 293 293 1317 1024 612 1636 70638619765 19583977430 90222597195 cost_1343_293_join2_0 cost_1343_293_join2_2 rfl rfl rfl

private theorem cost_1343_293_total : P1_7_1_3.momentEstimate 1343 293 = 90222597195 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1343 + 293 = 1636 by decide]
  exact cost_1343_293_join3_0

theorem moment1343_293 : P1_7_1.groupedPoleMoment 1343 293 ≤ 90222597195 :=
  (P1_7_1_3.grouped_bound 1343 293).trans_eq cost_1343_293_total
private theorem cost_1343_297_block0 : P1_7_1_3.blockEstimate 1343 297 297 128 = 446395040 := by decide +kernel

private theorem cost_1343_297_block1 : P1_7_1_3.blockEstimate 1343 297 425 128 = 2811970208 := by decide +kernel

private theorem cost_1343_297_block2 : P1_7_1_3.blockEstimate 1343 297 553 128 = 6675236782 := by decide +kernel

private theorem cost_1343_297_block3 : P1_7_1_3.blockEstimate 1343 297 681 128 = 10195309504 := by decide +kernel

private theorem cost_1343_297_block4 : P1_7_1_3.blockEstimate 1343 297 809 128 = 12477846464 := by decide +kernel

private theorem cost_1343_297_block5 : P1_7_1_3.blockEstimate 1343 297 937 128 = 13510480832 := by decide +kernel

private theorem cost_1343_297_block6 : P1_7_1_3.blockEstimate 1343 297 1065 128 = 13293212608 := by decide +kernel

private theorem cost_1343_297_block7 : P1_7_1_3.blockEstimate 1343 297 1193 128 = 11826041792 := by decide +kernel

private theorem cost_1343_297_block8 : P1_7_1_3.blockEstimate 1343 297 1321 128 = 9196071938 := by decide +kernel

private theorem cost_1343_297_block9 : P1_7_1_3.blockEstimate 1343 297 1449 128 = 6127810457 := by decide +kernel

private theorem cost_1343_297_block10 : P1_7_1_3.blockEstimate 1343 297 1577 128 = 3307102165 := by decide +kernel

private theorem cost_1343_297_block11 : P1_7_1_3.blockEstimate 1343 297 1705 128 = 1183406432 := by decide +kernel

private theorem cost_1343_297_block12 : P1_7_1_3.blockEstimate 1343 297 1833 104 = 126691942 := by decide +kernel

private theorem cost_1343_297_join0_0 : P1_7_1_3.blockEstimate 1343 297 297 256 = 3258365248 :=
  @P1_7_1_3.block_append 1343 297 297 425 128 128 256 446395040 2811970208 3258365248 cost_1343_297_block0 cost_1343_297_block1 rfl rfl rfl

private theorem cost_1343_297_join0_2 : P1_7_1_3.blockEstimate 1343 297 553 256 = 16870546286 :=
  @P1_7_1_3.block_append 1343 297 553 681 128 128 256 6675236782 10195309504 16870546286 cost_1343_297_block2 cost_1343_297_block3 rfl rfl rfl

private theorem cost_1343_297_join0_4 : P1_7_1_3.blockEstimate 1343 297 809 256 = 25988327296 :=
  @P1_7_1_3.block_append 1343 297 809 937 128 128 256 12477846464 13510480832 25988327296 cost_1343_297_block4 cost_1343_297_block5 rfl rfl rfl

private theorem cost_1343_297_join0_6 : P1_7_1_3.blockEstimate 1343 297 1065 256 = 25119254400 :=
  @P1_7_1_3.block_append 1343 297 1065 1193 128 128 256 13293212608 11826041792 25119254400 cost_1343_297_block6 cost_1343_297_block7 rfl rfl rfl

private theorem cost_1343_297_join0_8 : P1_7_1_3.blockEstimate 1343 297 1321 256 = 15323882395 :=
  @P1_7_1_3.block_append 1343 297 1321 1449 128 128 256 9196071938 6127810457 15323882395 cost_1343_297_block8 cost_1343_297_block9 rfl rfl rfl

private theorem cost_1343_297_join0_10 : P1_7_1_3.blockEstimate 1343 297 1577 256 = 4490508597 :=
  @P1_7_1_3.block_append 1343 297 1577 1705 128 128 256 3307102165 1183406432 4490508597 cost_1343_297_block10 cost_1343_297_block11 rfl rfl rfl

private theorem cost_1343_297_join1_0 : P1_7_1_3.blockEstimate 1343 297 297 512 = 20128911534 :=
  @P1_7_1_3.block_append 1343 297 297 553 256 256 512 3258365248 16870546286 20128911534 cost_1343_297_join0_0 cost_1343_297_join0_2 rfl rfl rfl

private theorem cost_1343_297_join1_2 : P1_7_1_3.blockEstimate 1343 297 809 512 = 51107581696 :=
  @P1_7_1_3.block_append 1343 297 809 1065 256 256 512 25988327296 25119254400 51107581696 cost_1343_297_join0_4 cost_1343_297_join0_6 rfl rfl rfl

private theorem cost_1343_297_join1_4 : P1_7_1_3.blockEstimate 1343 297 1321 512 = 19814390992 :=
  @P1_7_1_3.block_append 1343 297 1321 1577 256 256 512 15323882395 4490508597 19814390992 cost_1343_297_join0_8 cost_1343_297_join0_10 rfl rfl rfl

private theorem cost_1343_297_join2_0 : P1_7_1_3.blockEstimate 1343 297 297 1024 = 71236493230 :=
  @P1_7_1_3.block_append 1343 297 297 809 512 512 1024 20128911534 51107581696 71236493230 cost_1343_297_join1_0 cost_1343_297_join1_2 rfl rfl rfl

private theorem cost_1343_297_join2_2 : P1_7_1_3.blockEstimate 1343 297 1321 616 = 19941082934 :=
  @P1_7_1_3.block_append 1343 297 1321 1833 512 104 616 19814390992 126691942 19941082934 cost_1343_297_join1_4 cost_1343_297_block12 rfl rfl rfl

private theorem cost_1343_297_join3_0 : P1_7_1_3.blockEstimate 1343 297 297 1640 = 91177576164 :=
  @P1_7_1_3.block_append 1343 297 297 1321 1024 616 1640 71236493230 19941082934 91177576164 cost_1343_297_join2_0 cost_1343_297_join2_2 rfl rfl rfl

private theorem cost_1343_297_total : P1_7_1_3.momentEstimate 1343 297 = 91177576164 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1343 + 297 = 1640 by decide]
  exact cost_1343_297_join3_0

theorem moment1343_297 : P1_7_1.groupedPoleMoment 1343 297 ≤ 91177576164 :=
  (P1_7_1_3.grouped_bound 1343 297).trans_eq cost_1343_297_total
private theorem cost_1343_299_block0 : P1_7_1_3.blockEstimate 1343 299 299 128 = 446395040 := by decide +kernel

private theorem cost_1343_299_block1 : P1_7_1_3.blockEstimate 1343 299 427 128 = 2811970208 := by decide +kernel

private theorem cost_1343_299_block2 : P1_7_1_3.blockEstimate 1343 299 555 128 = 6682545277 := by decide +kernel

private theorem cost_1343_299_block3 : P1_7_1_3.blockEstimate 1343 299 683 128 = 10229347200 := by decide +kernel

private theorem cost_1343_299_block4 : P1_7_1_3.blockEstimate 1343 299 811 128 = 12532118400 := by decide +kernel

private theorem cost_1343_299_block5 : P1_7_1_3.blockEstimate 1343 299 939 128 = 13576598400 := by decide +kernel

private theorem cost_1343_299_block6 : P1_7_1_3.blockEstimate 1343 299 1067 128 = 13362787200 := by decide +kernel

private theorem cost_1343_299_block7 : P1_7_1_3.blockEstimate 1343 299 1195 128 = 11890684800 := by decide +kernel

private theorem cost_1343_299_block8 : P1_7_1_3.blockEstimate 1343 299 1323 128 = 9252199655 := by decide +kernel

private theorem cost_1343_299_block9 : P1_7_1_3.blockEstimate 1343 299 1451 128 = 6178220301 := by decide +kernel

private theorem cost_1343_299_block10 : P1_7_1_3.blockEstimate 1343 299 1579 128 = 3347523302 := by decide +kernel

private theorem cost_1343_299_block11 : P1_7_1_3.blockEstimate 1343 299 1707 128 = 1209093776 := by decide +kernel

private theorem cost_1343_299_block12 : P1_7_1_3.blockEstimate 1343 299 1835 106 = 133938387 := by decide +kernel

private theorem cost_1343_299_join0_0 : P1_7_1_3.blockEstimate 1343 299 299 256 = 3258365248 :=
  @P1_7_1_3.block_append 1343 299 299 427 128 128 256 446395040 2811970208 3258365248 cost_1343_299_block0 cost_1343_299_block1 rfl rfl rfl

private theorem cost_1343_299_join0_2 : P1_7_1_3.blockEstimate 1343 299 555 256 = 16911892477 :=
  @P1_7_1_3.block_append 1343 299 555 683 128 128 256 6682545277 10229347200 16911892477 cost_1343_299_block2 cost_1343_299_block3 rfl rfl rfl

private theorem cost_1343_299_join0_4 : P1_7_1_3.blockEstimate 1343 299 811 256 = 26108716800 :=
  @P1_7_1_3.block_append 1343 299 811 939 128 128 256 12532118400 13576598400 26108716800 cost_1343_299_block4 cost_1343_299_block5 rfl rfl rfl

private theorem cost_1343_299_join0_6 : P1_7_1_3.blockEstimate 1343 299 1067 256 = 25253472000 :=
  @P1_7_1_3.block_append 1343 299 1067 1195 128 128 256 13362787200 11890684800 25253472000 cost_1343_299_block6 cost_1343_299_block7 rfl rfl rfl

private theorem cost_1343_299_join0_8 : P1_7_1_3.blockEstimate 1343 299 1323 256 = 15430419956 :=
  @P1_7_1_3.block_append 1343 299 1323 1451 128 128 256 9252199655 6178220301 15430419956 cost_1343_299_block8 cost_1343_299_block9 rfl rfl rfl

private theorem cost_1343_299_join0_10 : P1_7_1_3.blockEstimate 1343 299 1579 256 = 4556617078 :=
  @P1_7_1_3.block_append 1343 299 1579 1707 128 128 256 3347523302 1209093776 4556617078 cost_1343_299_block10 cost_1343_299_block11 rfl rfl rfl

private theorem cost_1343_299_join1_0 : P1_7_1_3.blockEstimate 1343 299 299 512 = 20170257725 :=
  @P1_7_1_3.block_append 1343 299 299 555 256 256 512 3258365248 16911892477 20170257725 cost_1343_299_join0_0 cost_1343_299_join0_2 rfl rfl rfl

private theorem cost_1343_299_join1_2 : P1_7_1_3.blockEstimate 1343 299 811 512 = 51362188800 :=
  @P1_7_1_3.block_append 1343 299 811 1067 256 256 512 26108716800 25253472000 51362188800 cost_1343_299_join0_4 cost_1343_299_join0_6 rfl rfl rfl

private theorem cost_1343_299_join1_4 : P1_7_1_3.blockEstimate 1343 299 1323 512 = 19987037034 :=
  @P1_7_1_3.block_append 1343 299 1323 1579 256 256 512 15430419956 4556617078 19987037034 cost_1343_299_join0_8 cost_1343_299_join0_10 rfl rfl rfl

private theorem cost_1343_299_join2_0 : P1_7_1_3.blockEstimate 1343 299 299 1024 = 71532446525 :=
  @P1_7_1_3.block_append 1343 299 299 811 512 512 1024 20170257725 51362188800 71532446525 cost_1343_299_join1_0 cost_1343_299_join1_2 rfl rfl rfl

private theorem cost_1343_299_join2_2 : P1_7_1_3.blockEstimate 1343 299 1323 618 = 20120975421 :=
  @P1_7_1_3.block_append 1343 299 1323 1835 512 106 618 19987037034 133938387 20120975421 cost_1343_299_join1_4 cost_1343_299_block12 rfl rfl rfl

private theorem cost_1343_299_join3_0 : P1_7_1_3.blockEstimate 1343 299 299 1642 = 91653421946 :=
  @P1_7_1_3.block_append 1343 299 299 1323 1024 618 1642 71532446525 20120975421 91653421946 cost_1343_299_join2_0 cost_1343_299_join2_2 rfl rfl rfl

private theorem cost_1343_299_total : P1_7_1_3.momentEstimate 1343 299 = 91653421946 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1343 + 299 = 1642 by decide]
  exact cost_1343_299_join3_0

theorem moment1343_299 : P1_7_1.groupedPoleMoment 1343 299 ≤ 91653421946 :=
  (P1_7_1_3.grouped_bound 1343 299).trans_eq cost_1343_299_total
private theorem cost_1344_287_block0 : P1_7_1_3.blockEstimate 1344 287 287 128 = 446752800 := by decide +kernel

private theorem cost_1344_287_block1 : P1_7_1_3.blockEstimate 1344 287 415 128 = 2814441504 := by decide +kernel

private theorem cost_1344_287_block2 : P1_7_1_3.blockEstimate 1344 287 543 128 = 6639820680 := by decide +kernel

private theorem cost_1344_287_block3 : P1_7_1_3.blockEstimate 1344 287 671 128 = 10029487104 := by decide +kernel

private theorem cost_1344_287_block4 : P1_7_1_3.blockEstimate 1344 287 799 128 = 12216554496 := by decide +kernel

private theorem cost_1344_287_block5 : P1_7_1_3.blockEstimate 1344 287 927 128 = 13195662336 := by decide +kernel

private theorem cost_1344_287_block6 : P1_7_1_3.blockEstimate 1344 287 1055 128 = 12966810624 := by decide +kernel

private theorem cost_1344_287_block7 : P1_7_1_3.blockEstimate 1344 287 1183 128 = 11529999360 := by decide +kernel

private theorem cost_1344_287_block8 : P1_7_1_3.blockEstimate 1344 287 1311 128 = 8948691888 := by decide +kernel

private theorem cost_1344_287_block9 : P1_7_1_3.blockEstimate 1344 287 1439 128 = 5906735691 := by decide +kernel

private theorem cost_1344_287_block10 : P1_7_1_3.blockEstimate 1344 287 1567 128 = 3130157763 := by decide +kernel

private theorem cost_1344_287_block11 : P1_7_1_3.blockEstimate 1344 287 1695 128 = 1071947424 := by decide +kernel

private theorem cost_1344_287_block12 : P1_7_1_3.blockEstimate 1344 287 1823 95 = 97343608 := by decide +kernel

private theorem cost_1344_287_join0_0 : P1_7_1_3.blockEstimate 1344 287 287 256 = 3261194304 :=
  @P1_7_1_3.block_append 1344 287 287 415 128 128 256 446752800 2814441504 3261194304 cost_1344_287_block0 cost_1344_287_block1 rfl rfl rfl

private theorem cost_1344_287_join0_2 : P1_7_1_3.blockEstimate 1344 287 543 256 = 16669307784 :=
  @P1_7_1_3.block_append 1344 287 543 671 128 128 256 6639820680 10029487104 16669307784 cost_1344_287_block2 cost_1344_287_block3 rfl rfl rfl

private theorem cost_1344_287_join0_4 : P1_7_1_3.blockEstimate 1344 287 799 256 = 25412216832 :=
  @P1_7_1_3.block_append 1344 287 799 927 128 128 256 12216554496 13195662336 25412216832 cost_1344_287_block4 cost_1344_287_block5 rfl rfl rfl

private theorem cost_1344_287_join0_6 : P1_7_1_3.blockEstimate 1344 287 1055 256 = 24496809984 :=
  @P1_7_1_3.block_append 1344 287 1055 1183 128 128 256 12966810624 11529999360 24496809984 cost_1344_287_block6 cost_1344_287_block7 rfl rfl rfl

private theorem cost_1344_287_join0_8 : P1_7_1_3.blockEstimate 1344 287 1311 256 = 14855427579 :=
  @P1_7_1_3.block_append 1344 287 1311 1439 128 128 256 8948691888 5906735691 14855427579 cost_1344_287_block8 cost_1344_287_block9 rfl rfl rfl

private theorem cost_1344_287_join0_10 : P1_7_1_3.blockEstimate 1344 287 1567 256 = 4202105187 :=
  @P1_7_1_3.block_append 1344 287 1567 1695 128 128 256 3130157763 1071947424 4202105187 cost_1344_287_block10 cost_1344_287_block11 rfl rfl rfl

private theorem cost_1344_287_join1_0 : P1_7_1_3.blockEstimate 1344 287 287 512 = 19930502088 :=
  @P1_7_1_3.block_append 1344 287 287 543 256 256 512 3261194304 16669307784 19930502088 cost_1344_287_join0_0 cost_1344_287_join0_2 rfl rfl rfl

private theorem cost_1344_287_join1_2 : P1_7_1_3.blockEstimate 1344 287 799 512 = 49909026816 :=
  @P1_7_1_3.block_append 1344 287 799 1055 256 256 512 25412216832 24496809984 49909026816 cost_1344_287_join0_4 cost_1344_287_join0_6 rfl rfl rfl

private theorem cost_1344_287_join1_4 : P1_7_1_3.blockEstimate 1344 287 1311 512 = 19057532766 :=
  @P1_7_1_3.block_append 1344 287 1311 1567 256 256 512 14855427579 4202105187 19057532766 cost_1344_287_join0_8 cost_1344_287_join0_10 rfl rfl rfl

private theorem cost_1344_287_join2_0 : P1_7_1_3.blockEstimate 1344 287 287 1024 = 69839528904 :=
  @P1_7_1_3.block_append 1344 287 287 799 512 512 1024 19930502088 49909026816 69839528904 cost_1344_287_join1_0 cost_1344_287_join1_2 rfl rfl rfl

private theorem cost_1344_287_join2_2 : P1_7_1_3.blockEstimate 1344 287 1311 607 = 19154876374 :=
  @P1_7_1_3.block_append 1344 287 1311 1823 512 95 607 19057532766 97343608 19154876374 cost_1344_287_join1_4 cost_1344_287_block12 rfl rfl rfl

private theorem cost_1344_287_join3_0 : P1_7_1_3.blockEstimate 1344 287 287 1631 = 88994405278 :=
  @P1_7_1_3.block_append 1344 287 287 1311 1024 607 1631 69839528904 19154876374 88994405278 cost_1344_287_join2_0 cost_1344_287_join2_2 rfl rfl rfl

private theorem cost_1344_287_total : P1_7_1_3.momentEstimate 1344 287 = 88994405278 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1344 + 287 = 1631 by decide]
  exact cost_1344_287_join3_0

theorem moment1344_287 : P1_7_1.groupedPoleMoment 1344 287 ≤ 88994405278 :=
  (P1_7_1_3.grouped_bound 1344 287).trans_eq cost_1344_287_total
private theorem cost_1344_291_block0 : P1_7_1_3.blockEstimate 1344 291 291 128 = 446752800 := by decide +kernel

private theorem cost_1344_291_block1 : P1_7_1_3.blockEstimate 1344 291 419 128 = 2814441504 := by decide +kernel

private theorem cost_1344_291_block2 : P1_7_1_3.blockEstimate 1344 291 547 128 = 6657731431 := by decide +kernel

private theorem cost_1344_291_block3 : P1_7_1_3.blockEstimate 1344 291 675 128 = 10101770368 := by decide +kernel

private theorem cost_1344_291_block4 : P1_7_1_3.blockEstimate 1344 291 803 128 = 12328781952 := by decide +kernel

private theorem cost_1344_291_block5 : P1_7_1_3.blockEstimate 1344 291 931 128 = 13331056768 := by decide +kernel

private theorem cost_1344_291_block6 : P1_7_1_3.blockEstimate 1344 291 1059 128 = 13108594816 := by decide +kernel

private theorem cost_1344_291_block7 : P1_7_1_3.blockEstimate 1344 291 1187 128 = 11661396096 := by decide +kernel

private theorem cost_1344_291_block8 : P1_7_1_3.blockEstimate 1344 291 1315 128 = 9060937275 := by decide +kernel

private theorem cost_1344_291_block9 : P1_7_1_3.blockEstimate 1344 291 1443 128 = 6006552674 := by decide +kernel

private theorem cost_1344_291_block10 : P1_7_1_3.blockEstimate 1344 291 1571 128 = 3209450112 := by decide +kernel

private theorem cost_1344_291_block11 : P1_7_1_3.blockEstimate 1344 291 1699 128 = 1121249536 := by decide +kernel

private theorem cost_1344_291_block12 : P1_7_1_3.blockEstimate 1344 291 1827 99 = 109800250 := by decide +kernel

private theorem cost_1344_291_join0_0 : P1_7_1_3.blockEstimate 1344 291 291 256 = 3261194304 :=
  @P1_7_1_3.block_append 1344 291 291 419 128 128 256 446752800 2814441504 3261194304 cost_1344_291_block0 cost_1344_291_block1 rfl rfl rfl

private theorem cost_1344_291_join0_2 : P1_7_1_3.blockEstimate 1344 291 547 256 = 16759501799 :=
  @P1_7_1_3.block_append 1344 291 547 675 128 128 256 6657731431 10101770368 16759501799 cost_1344_291_block2 cost_1344_291_block3 rfl rfl rfl

private theorem cost_1344_291_join0_4 : P1_7_1_3.blockEstimate 1344 291 803 256 = 25659838720 :=
  @P1_7_1_3.block_append 1344 291 803 931 128 128 256 12328781952 13331056768 25659838720 cost_1344_291_block4 cost_1344_291_block5 rfl rfl rfl

private theorem cost_1344_291_join0_6 : P1_7_1_3.blockEstimate 1344 291 1059 256 = 24769990912 :=
  @P1_7_1_3.block_append 1344 291 1059 1187 128 128 256 13108594816 11661396096 24769990912 cost_1344_291_block6 cost_1344_291_block7 rfl rfl rfl

private theorem cost_1344_291_join0_8 : P1_7_1_3.blockEstimate 1344 291 1315 256 = 15067489949 :=
  @P1_7_1_3.block_append 1344 291 1315 1443 128 128 256 9060937275 6006552674 15067489949 cost_1344_291_block8 cost_1344_291_block9 rfl rfl rfl

private theorem cost_1344_291_join0_10 : P1_7_1_3.blockEstimate 1344 291 1571 256 = 4330699648 :=
  @P1_7_1_3.block_append 1344 291 1571 1699 128 128 256 3209450112 1121249536 4330699648 cost_1344_291_block10 cost_1344_291_block11 rfl rfl rfl

private theorem cost_1344_291_join1_0 : P1_7_1_3.blockEstimate 1344 291 291 512 = 20020696103 :=
  @P1_7_1_3.block_append 1344 291 291 547 256 256 512 3261194304 16759501799 20020696103 cost_1344_291_join0_0 cost_1344_291_join0_2 rfl rfl rfl

private theorem cost_1344_291_join1_2 : P1_7_1_3.blockEstimate 1344 291 803 512 = 50429829632 :=
  @P1_7_1_3.block_append 1344 291 803 1059 256 256 512 25659838720 24769990912 50429829632 cost_1344_291_join0_4 cost_1344_291_join0_6 rfl rfl rfl

private theorem cost_1344_291_join1_4 : P1_7_1_3.blockEstimate 1344 291 1315 512 = 19398189597 :=
  @P1_7_1_3.block_append 1344 291 1315 1571 256 256 512 15067489949 4330699648 19398189597 cost_1344_291_join0_8 cost_1344_291_join0_10 rfl rfl rfl

private theorem cost_1344_291_join2_0 : P1_7_1_3.blockEstimate 1344 291 291 1024 = 70450525735 :=
  @P1_7_1_3.block_append 1344 291 291 803 512 512 1024 20020696103 50429829632 70450525735 cost_1344_291_join1_0 cost_1344_291_join1_2 rfl rfl rfl

private theorem cost_1344_291_join2_2 : P1_7_1_3.blockEstimate 1344 291 1315 611 = 19507989847 :=
  @P1_7_1_3.block_append 1344 291 1315 1827 512 99 611 19398189597 109800250 19507989847 cost_1344_291_join1_4 cost_1344_291_block12 rfl rfl rfl

private theorem cost_1344_291_join3_0 : P1_7_1_3.blockEstimate 1344 291 291 1635 = 89958515582 :=
  @P1_7_1_3.block_append 1344 291 291 1315 1024 611 1635 70450525735 19507989847 89958515582 cost_1344_291_join2_0 cost_1344_291_join2_2 rfl rfl rfl

private theorem cost_1344_291_total : P1_7_1_3.momentEstimate 1344 291 = 89958515582 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1344 + 291 = 1635 by decide]
  exact cost_1344_291_join3_0

theorem moment1344_291 : P1_7_1.groupedPoleMoment 1344 291 ≤ 89958515582 :=
  (P1_7_1_3.grouped_bound 1344 291).trans_eq cost_1344_291_total
private theorem cost_1344_293_block0 : P1_7_1_3.blockEstimate 1344 293 293 128 = 446752800 := by decide +kernel

private theorem cost_1344_293_block1 : P1_7_1_3.blockEstimate 1344 293 421 128 = 2814441504 := by decide +kernel

private theorem cost_1344_293_block2 : P1_7_1_3.blockEstimate 1344 293 549 128 = 6666120681 := by decide +kernel

private theorem cost_1344_293_block3 : P1_7_1_3.blockEstimate 1344 293 677 128 = 10137223488 := by decide +kernel

private theorem cost_1344_293_block4 : P1_7_1_3.blockEstimate 1344 293 805 128 = 12384305472 := by decide +kernel

private theorem cost_1344_293_block5 : P1_7_1_3.blockEstimate 1344 293 933 128 = 13398262080 := by decide +kernel

private theorem cost_1344_293_block6 : P1_7_1_3.blockEstimate 1344 293 1061 128 = 13179093312 := by decide +kernel

private theorem cost_1344_293_block7 : P1_7_1_3.blockEstimate 1344 293 1189 128 = 11726799168 := by decide +kernel

private theorem cost_1344_293_block8 : P1_7_1_3.blockEstimate 1344 293 1317 128 = 9117094376 := by decide +kernel

private theorem cost_1344_293_block9 : P1_7_1_3.blockEstimate 1344 293 1445 128 = 6056668611 := by decide +kernel

private theorem cost_1344_293_block10 : P1_7_1_3.blockEstimate 1344 293 1573 128 = 3249402081 := by decide +kernel

private theorem cost_1344_293_block11 : P1_7_1_3.blockEstimate 1344 293 1701 128 = 1146299248 := by decide +kernel

private theorem cost_1344_293_block12 : P1_7_1_3.blockEstimate 1344 293 1829 101 = 116403469 := by decide +kernel

private theorem cost_1344_293_join0_0 : P1_7_1_3.blockEstimate 1344 293 293 256 = 3261194304 :=
  @P1_7_1_3.block_append 1344 293 293 421 128 128 256 446752800 2814441504 3261194304 cost_1344_293_block0 cost_1344_293_block1 rfl rfl rfl

private theorem cost_1344_293_join0_2 : P1_7_1_3.blockEstimate 1344 293 549 256 = 16803344169 :=
  @P1_7_1_3.block_append 1344 293 549 677 128 128 256 6666120681 10137223488 16803344169 cost_1344_293_block2 cost_1344_293_block3 rfl rfl rfl

private theorem cost_1344_293_join0_4 : P1_7_1_3.blockEstimate 1344 293 805 256 = 25782567552 :=
  @P1_7_1_3.block_append 1344 293 805 933 128 128 256 12384305472 13398262080 25782567552 cost_1344_293_block4 cost_1344_293_block5 rfl rfl rfl

private theorem cost_1344_293_join0_6 : P1_7_1_3.blockEstimate 1344 293 1061 256 = 24905892480 :=
  @P1_7_1_3.block_append 1344 293 1061 1189 128 128 256 13179093312 11726799168 24905892480 cost_1344_293_block6 cost_1344_293_block7 rfl rfl rfl

private theorem cost_1344_293_join0_8 : P1_7_1_3.blockEstimate 1344 293 1317 256 = 15173762987 :=
  @P1_7_1_3.block_append 1344 293 1317 1445 128 128 256 9117094376 6056668611 15173762987 cost_1344_293_block8 cost_1344_293_block9 rfl rfl rfl

private theorem cost_1344_293_join0_10 : P1_7_1_3.blockEstimate 1344 293 1573 256 = 4395701329 :=
  @P1_7_1_3.block_append 1344 293 1573 1701 128 128 256 3249402081 1146299248 4395701329 cost_1344_293_block10 cost_1344_293_block11 rfl rfl rfl

private theorem cost_1344_293_join1_0 : P1_7_1_3.blockEstimate 1344 293 293 512 = 20064538473 :=
  @P1_7_1_3.block_append 1344 293 293 549 256 256 512 3261194304 16803344169 20064538473 cost_1344_293_join0_0 cost_1344_293_join0_2 rfl rfl rfl

private theorem cost_1344_293_join1_2 : P1_7_1_3.blockEstimate 1344 293 805 512 = 50688460032 :=
  @P1_7_1_3.block_append 1344 293 805 1061 256 256 512 25782567552 24905892480 50688460032 cost_1344_293_join0_4 cost_1344_293_join0_6 rfl rfl rfl

private theorem cost_1344_293_join1_4 : P1_7_1_3.blockEstimate 1344 293 1317 512 = 19569464316 :=
  @P1_7_1_3.block_append 1344 293 1317 1573 256 256 512 15173762987 4395701329 19569464316 cost_1344_293_join0_8 cost_1344_293_join0_10 rfl rfl rfl

private theorem cost_1344_293_join2_0 : P1_7_1_3.blockEstimate 1344 293 293 1024 = 70752998505 :=
  @P1_7_1_3.block_append 1344 293 293 805 512 512 1024 20064538473 50688460032 70752998505 cost_1344_293_join1_0 cost_1344_293_join1_2 rfl rfl rfl

private theorem cost_1344_293_join2_2 : P1_7_1_3.blockEstimate 1344 293 1317 613 = 19685867785 :=
  @P1_7_1_3.block_append 1344 293 1317 1829 512 101 613 19569464316 116403469 19685867785 cost_1344_293_join1_4 cost_1344_293_block12 rfl rfl rfl

private theorem cost_1344_293_join3_0 : P1_7_1_3.blockEstimate 1344 293 293 1637 = 90438866290 :=
  @P1_7_1_3.block_append 1344 293 293 1317 1024 613 1637 70752998505 19685867785 90438866290 cost_1344_293_join2_0 cost_1344_293_join2_2 rfl rfl rfl

private theorem cost_1344_293_total : P1_7_1_3.momentEstimate 1344 293 = 90438866290 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1344 + 293 = 1637 by decide]
  exact cost_1344_293_join3_0

theorem moment1344_293 : P1_7_1.groupedPoleMoment 1344 293 ≤ 90438866290 :=
  (P1_7_1_3.grouped_bound 1344 293).trans_eq cost_1344_293_total

end Research6966.HelperRescueCatalogue

end Merged6967_Near6967RescueMoment12

section Merged6967_Near6967RescueMoment13
set_option Elab.async false


set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem cost_1344_297_block0 : P1_7_1_3.blockEstimate 1344 297 297 128 = 446752800 := by decide +kernel

private theorem cost_1344_297_block1 : P1_7_1_3.blockEstimate 1344 297 425 128 = 2814441504 := by decide +kernel

private theorem cost_1344_297_block2 : P1_7_1_3.blockEstimate 1344 297 553 128 = 6681809030 := by decide +kernel

private theorem cost_1344_297_block3 : P1_7_1_3.blockEstimate 1344 297 681 128 = 10206752704 := by decide +kernel

private theorem cost_1344_297_block4 : P1_7_1_3.blockEstimate 1344 297 809 128 = 12494172096 := by decide +kernel

private theorem cost_1344_297_block5 : P1_7_1_3.blockEstimate 1344 297 937 128 = 13531688896 := by decide +kernel

private theorem cost_1344_297_block6 : P1_7_1_3.blockEstimate 1344 297 1065 128 = 13319303104 := by decide +kernel

private theorem cost_1344_297_block7 : P1_7_1_3.blockEstimate 1344 297 1193 128 = 11857014720 := by decide +kernel

private theorem cost_1344_297_block8 : P1_7_1_3.blockEstimate 1344 297 1321 128 = 9229489244 := by decide +kernel

private theorem cost_1344_297_block9 : P1_7_1_3.blockEstimate 1344 297 1449 128 = 6157310545 := by decide +kernel

private theorem cost_1344_297_block10 : P1_7_1_3.blockEstimate 1344 297 1577 128 = 3329912609 := by decide +kernel

private theorem cost_1344_297_block11 : P1_7_1_3.blockEstimate 1344 297 1705 128 = 1197191216 := by decide +kernel

private theorem cost_1344_297_block12 : P1_7_1_3.blockEstimate 1344 297 1833 105 = 130382829 := by decide +kernel

private theorem cost_1344_297_join0_0 : P1_7_1_3.blockEstimate 1344 297 297 256 = 3261194304 :=
  @P1_7_1_3.block_append 1344 297 297 425 128 128 256 446752800 2814441504 3261194304 cost_1344_297_block0 cost_1344_297_block1 rfl rfl rfl

private theorem cost_1344_297_join0_2 : P1_7_1_3.blockEstimate 1344 297 553 256 = 16888561734 :=
  @P1_7_1_3.block_append 1344 297 553 681 128 128 256 6681809030 10206752704 16888561734 cost_1344_297_block2 cost_1344_297_block3 rfl rfl rfl

private theorem cost_1344_297_join0_4 : P1_7_1_3.blockEstimate 1344 297 809 256 = 26025860992 :=
  @P1_7_1_3.block_append 1344 297 809 937 128 128 256 12494172096 13531688896 26025860992 cost_1344_297_block4 cost_1344_297_block5 rfl rfl rfl

private theorem cost_1344_297_join0_6 : P1_7_1_3.blockEstimate 1344 297 1065 256 = 25176317824 :=
  @P1_7_1_3.block_append 1344 297 1065 1193 128 128 256 13319303104 11857014720 25176317824 cost_1344_297_block6 cost_1344_297_block7 rfl rfl rfl

private theorem cost_1344_297_join0_8 : P1_7_1_3.blockEstimate 1344 297 1321 256 = 15386799789 :=
  @P1_7_1_3.block_append 1344 297 1321 1449 128 128 256 9229489244 6157310545 15386799789 cost_1344_297_block8 cost_1344_297_block9 rfl rfl rfl

private theorem cost_1344_297_join0_10 : P1_7_1_3.blockEstimate 1344 297 1577 256 = 4527103825 :=
  @P1_7_1_3.block_append 1344 297 1577 1705 128 128 256 3329912609 1197191216 4527103825 cost_1344_297_block10 cost_1344_297_block11 rfl rfl rfl

private theorem cost_1344_297_join1_0 : P1_7_1_3.blockEstimate 1344 297 297 512 = 20149756038 :=
  @P1_7_1_3.block_append 1344 297 297 553 256 256 512 3261194304 16888561734 20149756038 cost_1344_297_join0_0 cost_1344_297_join0_2 rfl rfl rfl

private theorem cost_1344_297_join1_2 : P1_7_1_3.blockEstimate 1344 297 809 512 = 51202178816 :=
  @P1_7_1_3.block_append 1344 297 809 1065 256 256 512 26025860992 25176317824 51202178816 cost_1344_297_join0_4 cost_1344_297_join0_6 rfl rfl rfl

private theorem cost_1344_297_join1_4 : P1_7_1_3.blockEstimate 1344 297 1321 512 = 19913903614 :=
  @P1_7_1_3.block_append 1344 297 1321 1577 256 256 512 15386799789 4527103825 19913903614 cost_1344_297_join0_8 cost_1344_297_join0_10 rfl rfl rfl

private theorem cost_1344_297_join2_0 : P1_7_1_3.blockEstimate 1344 297 297 1024 = 71351934854 :=
  @P1_7_1_3.block_append 1344 297 297 809 512 512 1024 20149756038 51202178816 71351934854 cost_1344_297_join1_0 cost_1344_297_join1_2 rfl rfl rfl

private theorem cost_1344_297_join2_2 : P1_7_1_3.blockEstimate 1344 297 1321 617 = 20044286443 :=
  @P1_7_1_3.block_append 1344 297 1321 1833 512 105 617 19913903614 130382829 20044286443 cost_1344_297_join1_4 cost_1344_297_block12 rfl rfl rfl

private theorem cost_1344_297_join3_0 : P1_7_1_3.blockEstimate 1344 297 297 1641 = 91396221297 :=
  @P1_7_1_3.block_append 1344 297 297 1321 1024 617 1641 71351934854 20044286443 91396221297 cost_1344_297_join2_0 cost_1344_297_join2_2 rfl rfl rfl

private theorem cost_1344_297_total : P1_7_1_3.momentEstimate 1344 297 = 91396221297 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1344 + 297 = 1641 by decide]
  exact cost_1344_297_join3_0

theorem moment1344_297 : P1_7_1.groupedPoleMoment 1344 297 ≤ 91396221297 :=
  (P1_7_1_3.grouped_bound 1344 297).trans_eq cost_1344_297_total
private theorem cost_1344_299_block0 : P1_7_1_3.blockEstimate 1344 299 299 128 = 446752800 := by decide +kernel

private theorem cost_1344_299_block1 : P1_7_1_3.blockEstimate 1344 299 427 128 = 2814441504 := by decide +kernel

private theorem cost_1344_299_block2 : P1_7_1_3.blockEstimate 1344 299 555 128 = 6689124921 := by decide +kernel

private theorem cost_1344_299_block3 : P1_7_1_3.blockEstimate 1344 299 683 128 = 10240828800 := by decide +kernel

private theorem cost_1344_299_block4 : P1_7_1_3.blockEstimate 1344 299 811 128 = 12548515200 := by decide +kernel

private theorem cost_1344_299_block5 : P1_7_1_3.blockEstimate 1344 299 939 128 = 13597910400 := by decide +kernel

private theorem cost_1344_299_block6 : P1_7_1_3.blockEstimate 1344 299 1067 128 = 13389014400 := by decide +kernel

private theorem cost_1344_299_block7 : P1_7_1_3.blockEstimate 1344 299 1195 128 = 11921827200 := by decide +kernel

private theorem cost_1344_299_block8 : P1_7_1_3.blockEstimate 1344 299 1323 128 = 9285731612 := by decide +kernel

private theorem cost_1344_299_block9 : P1_7_1_3.blockEstimate 1344 299 1451 128 = 6207834769 := by decide +kernel

private theorem cost_1344_299_block10 : P1_7_1_3.blockEstimate 1344 299 1579 128 = 3370469272 := by decide +kernel

private theorem cost_1344_299_block11 : P1_7_1_3.blockEstimate 1344 299 1707 128 = 1223031552 := by decide +kernel

private theorem cost_1344_299_block12 : P1_7_1_3.blockEstimate 1344 299 1835 107 = 137768166 := by decide +kernel

private theorem cost_1344_299_join0_0 : P1_7_1_3.blockEstimate 1344 299 299 256 = 3261194304 :=
  @P1_7_1_3.block_append 1344 299 299 427 128 128 256 446752800 2814441504 3261194304 cost_1344_299_block0 cost_1344_299_block1 rfl rfl rfl

private theorem cost_1344_299_join0_2 : P1_7_1_3.blockEstimate 1344 299 555 256 = 16929953721 :=
  @P1_7_1_3.block_append 1344 299 555 683 128 128 256 6689124921 10240828800 16929953721 cost_1344_299_block2 cost_1344_299_block3 rfl rfl rfl

private theorem cost_1344_299_join0_4 : P1_7_1_3.blockEstimate 1344 299 811 256 = 26146425600 :=
  @P1_7_1_3.block_append 1344 299 811 939 128 128 256 12548515200 13597910400 26146425600 cost_1344_299_block4 cost_1344_299_block5 rfl rfl rfl

private theorem cost_1344_299_join0_6 : P1_7_1_3.blockEstimate 1344 299 1067 256 = 25310841600 :=
  @P1_7_1_3.block_append 1344 299 1067 1195 128 128 256 13389014400 11921827200 25310841600 cost_1344_299_block6 cost_1344_299_block7 rfl rfl rfl

private theorem cost_1344_299_join0_8 : P1_7_1_3.blockEstimate 1344 299 1323 256 = 15493566381 :=
  @P1_7_1_3.block_append 1344 299 1323 1451 128 128 256 9285731612 6207834769 15493566381 cost_1344_299_block8 cost_1344_299_block9 rfl rfl rfl

private theorem cost_1344_299_join0_10 : P1_7_1_3.blockEstimate 1344 299 1579 256 = 4593500824 :=
  @P1_7_1_3.block_append 1344 299 1579 1707 128 128 256 3370469272 1223031552 4593500824 cost_1344_299_block10 cost_1344_299_block11 rfl rfl rfl

private theorem cost_1344_299_join1_0 : P1_7_1_3.blockEstimate 1344 299 299 512 = 20191148025 :=
  @P1_7_1_3.block_append 1344 299 299 555 256 256 512 3261194304 16929953721 20191148025 cost_1344_299_join0_0 cost_1344_299_join0_2 rfl rfl rfl

private theorem cost_1344_299_join1_2 : P1_7_1_3.blockEstimate 1344 299 811 512 = 51457267200 :=
  @P1_7_1_3.block_append 1344 299 811 1067 256 256 512 26146425600 25310841600 51457267200 cost_1344_299_join0_4 cost_1344_299_join0_6 rfl rfl rfl

private theorem cost_1344_299_join1_4 : P1_7_1_3.blockEstimate 1344 299 1323 512 = 20087067205 :=
  @P1_7_1_3.block_append 1344 299 1323 1579 256 256 512 15493566381 4593500824 20087067205 cost_1344_299_join0_8 cost_1344_299_join0_10 rfl rfl rfl

private theorem cost_1344_299_join2_0 : P1_7_1_3.blockEstimate 1344 299 299 1024 = 71648415225 :=
  @P1_7_1_3.block_append 1344 299 299 811 512 512 1024 20191148025 51457267200 71648415225 cost_1344_299_join1_0 cost_1344_299_join1_2 rfl rfl rfl

private theorem cost_1344_299_join2_2 : P1_7_1_3.blockEstimate 1344 299 1323 619 = 20224835371 :=
  @P1_7_1_3.block_append 1344 299 1323 1835 512 107 619 20087067205 137768166 20224835371 cost_1344_299_join1_4 cost_1344_299_block12 rfl rfl rfl

private theorem cost_1344_299_join3_0 : P1_7_1_3.blockEstimate 1344 299 299 1643 = 91873250596 :=
  @P1_7_1_3.block_append 1344 299 299 1323 1024 619 1643 71648415225 20224835371 91873250596 cost_1344_299_join2_0 cost_1344_299_join2_2 rfl rfl rfl

private theorem cost_1344_299_total : P1_7_1_3.momentEstimate 1344 299 = 91873250596 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1344 + 299 = 1643 by decide]
  exact cost_1344_299_join3_0

theorem moment1344_299 : P1_7_1.groupedPoleMoment 1344 299 ≤ 91873250596 :=
  (P1_7_1_3.grouped_bound 1344 299).trans_eq cost_1344_299_total
private theorem cost_1381_301_block0 : P1_7_1_3.blockEstimate 1381 301 301 128 = 459989920 := by decide +kernel

private theorem cost_1381_301_block1 : P1_7_1_3.blockEstimate 1381 301 429 128 = 2905879456 := by decide +kernel

private theorem cost_1381_301_block2 : P1_7_1_3.blockEstimate 1381 301 557 128 = 6939807691 := by decide +kernel

private theorem cost_1381_301_block3 : P1_7_1_3.blockEstimate 1381 301 685 128 = 10700666944 := by decide +kernel

private theorem cost_1381_301_block4 : P1_7_1_3.blockEstimate 1381 301 813 128 = 13211760704 := by decide +kernel

private theorem cost_1381_301_block5 : P1_7_1_3.blockEstimate 1381 301 941 128 = 14456174656 := by decide +kernel

private theorem cost_1381_301_block6 : P1_7_1_3.blockEstimate 1381 301 1069 128 = 14433908800 := by decide +kernel

private theorem cost_1381_301_block7 : P1_7_1_3.blockEstimate 1381 301 1197 128 = 13144963136 := by decide +kernel

private theorem cost_1381_301_block8 : P1_7_1_3.blockEstimate 1381 301 1325 128 = 10616598267 := by decide +kernel

private theorem cost_1381_301_block9 : P1_7_1_3.blockEstimate 1381 301 1453 128 = 7407441131 := by decide +kernel

private theorem cost_1381_301_block10 : P1_7_1_3.blockEstimate 1381 301 1581 128 = 4321733391 := by decide +kernel

private theorem cost_1381_301_block11 : P1_7_1_3.blockEstimate 1381 301 1709 128 = 1832604048 := by decide +kernel

private theorem cost_1381_301_block12 : P1_7_1_3.blockEstimate 1381 301 1837 128 = 350311824 := by decide +kernel

private theorem cost_1381_301_block13 : P1_7_1_3.blockEstimate 1381 301 1965 18 = 844520 := by decide +kernel

private theorem cost_1381_301_join0_0 : P1_7_1_3.blockEstimate 1381 301 301 256 = 3365869376 :=
  @P1_7_1_3.block_append 1381 301 301 429 128 128 256 459989920 2905879456 3365869376 cost_1381_301_block0 cost_1381_301_block1 rfl rfl rfl

private theorem cost_1381_301_join0_2 : P1_7_1_3.blockEstimate 1381 301 557 256 = 17640474635 :=
  @P1_7_1_3.block_append 1381 301 557 685 128 128 256 6939807691 10700666944 17640474635 cost_1381_301_block2 cost_1381_301_block3 rfl rfl rfl

private theorem cost_1381_301_join0_4 : P1_7_1_3.blockEstimate 1381 301 813 256 = 27667935360 :=
  @P1_7_1_3.block_append 1381 301 813 941 128 128 256 13211760704 14456174656 27667935360 cost_1381_301_block4 cost_1381_301_block5 rfl rfl rfl

private theorem cost_1381_301_join0_6 : P1_7_1_3.blockEstimate 1381 301 1069 256 = 27578871936 :=
  @P1_7_1_3.block_append 1381 301 1069 1197 128 128 256 14433908800 13144963136 27578871936 cost_1381_301_block6 cost_1381_301_block7 rfl rfl rfl

private theorem cost_1381_301_join0_8 : P1_7_1_3.blockEstimate 1381 301 1325 256 = 18024039398 :=
  @P1_7_1_3.block_append 1381 301 1325 1453 128 128 256 10616598267 7407441131 18024039398 cost_1381_301_block8 cost_1381_301_block9 rfl rfl rfl

private theorem cost_1381_301_join0_10 : P1_7_1_3.blockEstimate 1381 301 1581 256 = 6154337439 :=
  @P1_7_1_3.block_append 1381 301 1581 1709 128 128 256 4321733391 1832604048 6154337439 cost_1381_301_block10 cost_1381_301_block11 rfl rfl rfl

private theorem cost_1381_301_join0_12 : P1_7_1_3.blockEstimate 1381 301 1837 146 = 351156344 :=
  @P1_7_1_3.block_append 1381 301 1837 1965 128 18 146 350311824 844520 351156344 cost_1381_301_block12 cost_1381_301_block13 rfl rfl rfl

private theorem cost_1381_301_join1_0 : P1_7_1_3.blockEstimate 1381 301 301 512 = 21006344011 :=
  @P1_7_1_3.block_append 1381 301 301 557 256 256 512 3365869376 17640474635 21006344011 cost_1381_301_join0_0 cost_1381_301_join0_2 rfl rfl rfl

private theorem cost_1381_301_join1_2 : P1_7_1_3.blockEstimate 1381 301 813 512 = 55246807296 :=
  @P1_7_1_3.block_append 1381 301 813 1069 256 256 512 27667935360 27578871936 55246807296 cost_1381_301_join0_4 cost_1381_301_join0_6 rfl rfl rfl

private theorem cost_1381_301_join1_4 : P1_7_1_3.blockEstimate 1381 301 1325 512 = 24178376837 :=
  @P1_7_1_3.block_append 1381 301 1325 1581 256 256 512 18024039398 6154337439 24178376837 cost_1381_301_join0_8 cost_1381_301_join0_10 rfl rfl rfl

private theorem cost_1381_301_join2_0 : P1_7_1_3.blockEstimate 1381 301 301 1024 = 76253151307 :=
  @P1_7_1_3.block_append 1381 301 301 813 512 512 1024 21006344011 55246807296 76253151307 cost_1381_301_join1_0 cost_1381_301_join1_2 rfl rfl rfl

private theorem cost_1381_301_join2_2 : P1_7_1_3.blockEstimate 1381 301 1325 658 = 24529533181 :=
  @P1_7_1_3.block_append 1381 301 1325 1837 512 146 658 24178376837 351156344 24529533181 cost_1381_301_join1_4 cost_1381_301_join0_12 rfl rfl rfl

private theorem cost_1381_301_join3_0 : P1_7_1_3.blockEstimate 1381 301 301 1682 = 100782684488 :=
  @P1_7_1_3.block_append 1381 301 301 1325 1024 658 1682 76253151307 24529533181 100782684488 cost_1381_301_join2_0 cost_1381_301_join2_2 rfl rfl rfl

private theorem cost_1381_301_total : P1_7_1_3.momentEstimate 1381 301 = 100782684488 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1381 + 301 = 1682 by decide]
  exact cost_1381_301_join3_0

theorem moment1381_301 : P1_7_1.groupedPoleMoment 1381 301 ≤ 100782684488 :=
  (P1_7_1_3.grouped_bound 1381 301).trans_eq cost_1381_301_total
private theorem cost_1381_307_block0 : P1_7_1_3.blockEstimate 1381 307 307 128 = 459989920 := by decide +kernel

private theorem cost_1381_307_block1 : P1_7_1_3.blockEstimate 1381 307 435 128 = 2905879456 := by decide +kernel

private theorem cost_1381_307_block2 : P1_7_1_3.blockEstimate 1381 307 563 128 = 6959480351 := by decide +kernel

private theorem cost_1381_307_block3 : P1_7_1_3.blockEstimate 1381 307 691 128 = 10802856064 := by decide +kernel

private theorem cost_1381_307_block4 : P1_7_1_3.blockEstimate 1381 307 819 128 = 13378977920 := by decide +kernel

private theorem cost_1381_307_block5 : P1_7_1_3.blockEstimate 1381 307 947 128 = 14663254144 := by decide +kernel

private theorem cost_1381_307_block6 : P1_7_1_3.blockEstimate 1381 307 1075 128 = 14655684736 := by decide +kernel

private theorem cost_1381_307_block7 : P1_7_1_3.blockEstimate 1381 307 1203 128 = 13356269696 := by decide +kernel

private theorem cost_1381_307_block8 : P1_7_1_3.blockEstimate 1381 307 1331 128 = 10799395818 := by decide +kernel

private theorem cost_1381_307_block9 : P1_7_1_3.blockEstimate 1381 307 1459 128 = 7572793350 := by decide +kernel

private theorem cost_1381_307_block10 : P1_7_1_3.blockEstimate 1381 307 1587 128 = 4460053192 := by decide +kernel

private theorem cost_1381_307_block11 : P1_7_1_3.blockEstimate 1381 307 1715 128 = 1929411232 := by decide +kernel

private theorem cost_1381_307_block12 : P1_7_1_3.blockEstimate 1381 307 1843 128 = 393042592 := by decide +kernel

private theorem cost_1381_307_block13 : P1_7_1_3.blockEstimate 1381 307 1971 24 = 1888406 := by decide +kernel

private theorem cost_1381_307_join0_0 : P1_7_1_3.blockEstimate 1381 307 307 256 = 3365869376 :=
  @P1_7_1_3.block_append 1381 307 307 435 128 128 256 459989920 2905879456 3365869376 cost_1381_307_block0 cost_1381_307_block1 rfl rfl rfl

private theorem cost_1381_307_join0_2 : P1_7_1_3.blockEstimate 1381 307 563 256 = 17762336415 :=
  @P1_7_1_3.block_append 1381 307 563 691 128 128 256 6959480351 10802856064 17762336415 cost_1381_307_block2 cost_1381_307_block3 rfl rfl rfl

private theorem cost_1381_307_join0_4 : P1_7_1_3.blockEstimate 1381 307 819 256 = 28042232064 :=
  @P1_7_1_3.block_append 1381 307 819 947 128 128 256 13378977920 14663254144 28042232064 cost_1381_307_block4 cost_1381_307_block5 rfl rfl rfl

private theorem cost_1381_307_join0_6 : P1_7_1_3.blockEstimate 1381 307 1075 256 = 28011954432 :=
  @P1_7_1_3.block_append 1381 307 1075 1203 128 128 256 14655684736 13356269696 28011954432 cost_1381_307_block6 cost_1381_307_block7 rfl rfl rfl

private theorem cost_1381_307_join0_8 : P1_7_1_3.blockEstimate 1381 307 1331 256 = 18372189168 :=
  @P1_7_1_3.block_append 1381 307 1331 1459 128 128 256 10799395818 7572793350 18372189168 cost_1381_307_block8 cost_1381_307_block9 rfl rfl rfl

private theorem cost_1381_307_join0_10 : P1_7_1_3.blockEstimate 1381 307 1587 256 = 6389464424 :=
  @P1_7_1_3.block_append 1381 307 1587 1715 128 128 256 4460053192 1929411232 6389464424 cost_1381_307_block10 cost_1381_307_block11 rfl rfl rfl

private theorem cost_1381_307_join0_12 : P1_7_1_3.blockEstimate 1381 307 1843 152 = 394930998 :=
  @P1_7_1_3.block_append 1381 307 1843 1971 128 24 152 393042592 1888406 394930998 cost_1381_307_block12 cost_1381_307_block13 rfl rfl rfl

private theorem cost_1381_307_join1_0 : P1_7_1_3.blockEstimate 1381 307 307 512 = 21128205791 :=
  @P1_7_1_3.block_append 1381 307 307 563 256 256 512 3365869376 17762336415 21128205791 cost_1381_307_join0_0 cost_1381_307_join0_2 rfl rfl rfl

private theorem cost_1381_307_join1_2 : P1_7_1_3.blockEstimate 1381 307 819 512 = 56054186496 :=
  @P1_7_1_3.block_append 1381 307 819 1075 256 256 512 28042232064 28011954432 56054186496 cost_1381_307_join0_4 cost_1381_307_join0_6 rfl rfl rfl

private theorem cost_1381_307_join1_4 : P1_7_1_3.blockEstimate 1381 307 1331 512 = 24761653592 :=
  @P1_7_1_3.block_append 1381 307 1331 1587 256 256 512 18372189168 6389464424 24761653592 cost_1381_307_join0_8 cost_1381_307_join0_10 rfl rfl rfl

private theorem cost_1381_307_join2_0 : P1_7_1_3.blockEstimate 1381 307 307 1024 = 77182392287 :=
  @P1_7_1_3.block_append 1381 307 307 819 512 512 1024 21128205791 56054186496 77182392287 cost_1381_307_join1_0 cost_1381_307_join1_2 rfl rfl rfl

private theorem cost_1381_307_join2_2 : P1_7_1_3.blockEstimate 1381 307 1331 664 = 25156584590 :=
  @P1_7_1_3.block_append 1381 307 1331 1843 512 152 664 24761653592 394930998 25156584590 cost_1381_307_join1_4 cost_1381_307_join0_12 rfl rfl rfl

private theorem cost_1381_307_join3_0 : P1_7_1_3.blockEstimate 1381 307 307 1688 = 102338976877 :=
  @P1_7_1_3.block_append 1381 307 307 1331 1024 664 1688 77182392287 25156584590 102338976877 cost_1381_307_join2_0 cost_1381_307_join2_2 rfl rfl rfl

private theorem cost_1381_307_total : P1_7_1_3.momentEstimate 1381 307 = 102338976877 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1381 + 307 = 1688 by decide]
  exact cost_1381_307_join3_0

theorem moment1381_307 : P1_7_1.groupedPoleMoment 1381 307 ≤ 102338976877 :=
  (P1_7_1_3.grouped_bound 1381 307).trans_eq cost_1381_307_total
private theorem cost_1381_309_block0 : P1_7_1_3.blockEstimate 1381 309 309 128 = 459989920 := by decide +kernel

private theorem cost_1381_309_block1 : P1_7_1_3.blockEstimate 1381 309 437 128 = 2905879456 := by decide +kernel

private theorem cost_1381_309_block2 : P1_7_1_3.blockEstimate 1381 309 565 128 = 6965388249 := by decide +kernel

private theorem cost_1381_309_block3 : P1_7_1_3.blockEstimate 1381 309 693 128 = 10835963200 := by decide +kernel

private theorem cost_1381_309_block4 : P1_7_1_3.blockEstimate 1381 309 821 128 = 13433892160 := by decide +kernel

private theorem cost_1381_309_block5 : P1_7_1_3.blockEstimate 1381 309 949 128 = 14731586880 := by decide +kernel

private theorem cost_1381_309_block6 : P1_7_1_3.blockEstimate 1381 309 1077 128 = 14729047360 := by decide +kernel

private theorem cost_1381_309_block7 : P1_7_1_3.blockEstimate 1381 309 1205 128 = 13426273600 := by decide +kernel

private theorem cost_1381_309_block8 : P1_7_1_3.blockEstimate 1381 309 1333 128 = 10860269848 := by decide +kernel

private theorem cost_1381_309_block9 : P1_7_1_3.blockEstimate 1381 309 1461 128 = 7628152525 := by decide +kernel

private theorem cost_1381_309_block10 : P1_7_1_3.blockEstimate 1381 309 1589 128 = 4506534584 := by decide +kernel

private theorem cost_1381_309_block11 : P1_7_1_3.blockEstimate 1381 309 1717 128 = 1962180560 := by decide +kernel

private theorem cost_1381_309_block12 : P1_7_1_3.blockEstimate 1381 309 1845 128 = 407909328 := by decide +kernel

private theorem cost_1381_309_block13 : P1_7_1_3.blockEstimate 1381 309 1973 26 = 2367799 := by decide +kernel

private theorem cost_1381_309_join0_0 : P1_7_1_3.blockEstimate 1381 309 309 256 = 3365869376 :=
  @P1_7_1_3.block_append 1381 309 309 437 128 128 256 459989920 2905879456 3365869376 cost_1381_309_block0 cost_1381_309_block1 rfl rfl rfl

private theorem cost_1381_309_join0_2 : P1_7_1_3.blockEstimate 1381 309 565 256 = 17801351449 :=
  @P1_7_1_3.block_append 1381 309 565 693 128 128 256 6965388249 10835963200 17801351449 cost_1381_309_block2 cost_1381_309_block3 rfl rfl rfl

private theorem cost_1381_309_join0_4 : P1_7_1_3.blockEstimate 1381 309 821 256 = 28165479040 :=
  @P1_7_1_3.block_append 1381 309 821 949 128 128 256 13433892160 14731586880 28165479040 cost_1381_309_block4 cost_1381_309_block5 rfl rfl rfl

private theorem cost_1381_309_join0_6 : P1_7_1_3.blockEstimate 1381 309 1077 256 = 28155320960 :=
  @P1_7_1_3.block_append 1381 309 1077 1205 128 128 256 14729047360 13426273600 28155320960 cost_1381_309_block6 cost_1381_309_block7 rfl rfl rfl

private theorem cost_1381_309_join0_8 : P1_7_1_3.blockEstimate 1381 309 1333 256 = 18488422373 :=
  @P1_7_1_3.block_append 1381 309 1333 1461 128 128 256 10860269848 7628152525 18488422373 cost_1381_309_block8 cost_1381_309_block9 rfl rfl rfl

private theorem cost_1381_309_join0_10 : P1_7_1_3.blockEstimate 1381 309 1589 256 = 6468715144 :=
  @P1_7_1_3.block_append 1381 309 1589 1717 128 128 256 4506534584 1962180560 6468715144 cost_1381_309_block10 cost_1381_309_block11 rfl rfl rfl

private theorem cost_1381_309_join0_12 : P1_7_1_3.blockEstimate 1381 309 1845 154 = 410277127 :=
  @P1_7_1_3.block_append 1381 309 1845 1973 128 26 154 407909328 2367799 410277127 cost_1381_309_block12 cost_1381_309_block13 rfl rfl rfl

private theorem cost_1381_309_join1_0 : P1_7_1_3.blockEstimate 1381 309 309 512 = 21167220825 :=
  @P1_7_1_3.block_append 1381 309 309 565 256 256 512 3365869376 17801351449 21167220825 cost_1381_309_join0_0 cost_1381_309_join0_2 rfl rfl rfl

private theorem cost_1381_309_join1_2 : P1_7_1_3.blockEstimate 1381 309 821 512 = 56320800000 :=
  @P1_7_1_3.block_append 1381 309 821 1077 256 256 512 28165479040 28155320960 56320800000 cost_1381_309_join0_4 cost_1381_309_join0_6 rfl rfl rfl

private theorem cost_1381_309_join1_4 : P1_7_1_3.blockEstimate 1381 309 1333 512 = 24957137517 :=
  @P1_7_1_3.block_append 1381 309 1333 1589 256 256 512 18488422373 6468715144 24957137517 cost_1381_309_join0_8 cost_1381_309_join0_10 rfl rfl rfl

private theorem cost_1381_309_join2_0 : P1_7_1_3.blockEstimate 1381 309 309 1024 = 77488020825 :=
  @P1_7_1_3.block_append 1381 309 309 821 512 512 1024 21167220825 56320800000 77488020825 cost_1381_309_join1_0 cost_1381_309_join1_2 rfl rfl rfl

private theorem cost_1381_309_join2_2 : P1_7_1_3.blockEstimate 1381 309 1333 666 = 25367414644 :=
  @P1_7_1_3.block_append 1381 309 1333 1845 512 154 666 24957137517 410277127 25367414644 cost_1381_309_join1_4 cost_1381_309_join0_12 rfl rfl rfl

private theorem cost_1381_309_join3_0 : P1_7_1_3.blockEstimate 1381 309 309 1690 = 102855435469 :=
  @P1_7_1_3.block_append 1381 309 309 1333 1024 666 1690 77488020825 25367414644 102855435469 cost_1381_309_join2_0 cost_1381_309_join2_2 rfl rfl rfl

private theorem cost_1381_309_total : P1_7_1_3.momentEstimate 1381 309 = 102855435469 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1381 + 309 = 1690 by decide]
  exact cost_1381_309_join3_0

theorem moment1381_309 : P1_7_1.groupedPoleMoment 1381 309 ≤ 102855435469 :=
  (P1_7_1_3.grouped_bound 1381 309).trans_eq cost_1381_309_total
private theorem cost_1387_302_block0 : P1_7_1_3.blockEstimate 1387 302 302 128 = 462136480 := by decide +kernel

private theorem cost_1387_302_block1 : P1_7_1_3.blockEstimate 1387 302 430 128 = 2920707232 := by decide +kernel

private theorem cost_1387_302_block2 : P1_7_1_3.blockEstimate 1387 302 558 128 = 6982836384 := by decide +kernel

private theorem cost_1387_302_block3 : P1_7_1_3.blockEstimate 1387 302 686 128 = 10787226624 := by decide +kernel

private theorem cost_1387_302_block4 : P1_7_1_3.blockEstimate 1387 302 814 128 = 13338903552 := by decide +kernel

private theorem cost_1387_302_block5 : P1_7_1_3.blockEstimate 1387 302 942 128 = 14619706368 := by decide +kernel

private theorem cost_1387_302_block6 : P1_7_1_3.blockEstimate 1387 302 1070 128 = 14629635072 := by decide +kernel

private theorem cost_1387_302_block7 : P1_7_1_3.blockEstimate 1387 302 1198 128 = 13368689664 := by decide +kernel

private theorem cost_1387_302_block8 : P1_7_1_3.blockEstimate 1387 302 1326 128 = 10858832125 := by decide +kernel

private theorem cost_1387_302_block9 : P1_7_1_3.blockEstimate 1387 302 1454 128 = 7630480965 := by decide +kernel

private theorem cost_1387_302_block10 : P1_7_1_3.blockEstimate 1387 302 1582 128 = 4503008202 := by decide +kernel

private theorem cost_1387_302_block11 : P1_7_1_3.blockEstimate 1387 302 1710 128 = 1955193296 := by decide +kernel

private theorem cost_1387_302_block12 : P1_7_1_3.blockEstimate 1387 302 1838 128 = 402271696 := by decide +kernel

private theorem cost_1387_302_block13 : P1_7_1_3.blockEstimate 1387 302 1966 25 = 2128560 := by decide +kernel

private theorem cost_1387_302_join0_0 : P1_7_1_3.blockEstimate 1387 302 302 256 = 3382843712 :=
  @P1_7_1_3.block_append 1387 302 302 430 128 128 256 462136480 2920707232 3382843712 cost_1387_302_block0 cost_1387_302_block1 rfl rfl rfl

private theorem cost_1387_302_join0_2 : P1_7_1_3.blockEstimate 1387 302 558 256 = 17770063008 :=
  @P1_7_1_3.block_append 1387 302 558 686 128 128 256 6982836384 10787226624 17770063008 cost_1387_302_block2 cost_1387_302_block3 rfl rfl rfl

private theorem cost_1387_302_join0_4 : P1_7_1_3.blockEstimate 1387 302 814 256 = 27958609920 :=
  @P1_7_1_3.block_append 1387 302 814 942 128 128 256 13338903552 14619706368 27958609920 cost_1387_302_block4 cost_1387_302_block5 rfl rfl rfl

private theorem cost_1387_302_join0_6 : P1_7_1_3.blockEstimate 1387 302 1070 256 = 27998324736 :=
  @P1_7_1_3.block_append 1387 302 1070 1198 128 128 256 14629635072 13368689664 27998324736 cost_1387_302_block6 cost_1387_302_block7 rfl rfl rfl

private theorem cost_1387_302_join0_8 : P1_7_1_3.blockEstimate 1387 302 1326 256 = 18489313090 :=
  @P1_7_1_3.block_append 1387 302 1326 1454 128 128 256 10858832125 7630480965 18489313090 cost_1387_302_block8 cost_1387_302_block9 rfl rfl rfl

private theorem cost_1387_302_join0_10 : P1_7_1_3.blockEstimate 1387 302 1582 256 = 6458201498 :=
  @P1_7_1_3.block_append 1387 302 1582 1710 128 128 256 4503008202 1955193296 6458201498 cost_1387_302_block10 cost_1387_302_block11 rfl rfl rfl

private theorem cost_1387_302_join0_12 : P1_7_1_3.blockEstimate 1387 302 1838 153 = 404400256 :=
  @P1_7_1_3.block_append 1387 302 1838 1966 128 25 153 402271696 2128560 404400256 cost_1387_302_block12 cost_1387_302_block13 rfl rfl rfl

private theorem cost_1387_302_join1_0 : P1_7_1_3.blockEstimate 1387 302 302 512 = 21152906720 :=
  @P1_7_1_3.block_append 1387 302 302 558 256 256 512 3382843712 17770063008 21152906720 cost_1387_302_join0_0 cost_1387_302_join0_2 rfl rfl rfl

private theorem cost_1387_302_join1_2 : P1_7_1_3.blockEstimate 1387 302 814 512 = 55956934656 :=
  @P1_7_1_3.block_append 1387 302 814 1070 256 256 512 27958609920 27998324736 55956934656 cost_1387_302_join0_4 cost_1387_302_join0_6 rfl rfl rfl

private theorem cost_1387_302_join1_4 : P1_7_1_3.blockEstimate 1387 302 1326 512 = 24947514588 :=
  @P1_7_1_3.block_append 1387 302 1326 1582 256 256 512 18489313090 6458201498 24947514588 cost_1387_302_join0_8 cost_1387_302_join0_10 rfl rfl rfl

private theorem cost_1387_302_join2_0 : P1_7_1_3.blockEstimate 1387 302 302 1024 = 77109841376 :=
  @P1_7_1_3.block_append 1387 302 302 814 512 512 1024 21152906720 55956934656 77109841376 cost_1387_302_join1_0 cost_1387_302_join1_2 rfl rfl rfl

private theorem cost_1387_302_join2_2 : P1_7_1_3.blockEstimate 1387 302 1326 665 = 25351914844 :=
  @P1_7_1_3.block_append 1387 302 1326 1838 512 153 665 24947514588 404400256 25351914844 cost_1387_302_join1_4 cost_1387_302_join0_12 rfl rfl rfl

private theorem cost_1387_302_join3_0 : P1_7_1_3.blockEstimate 1387 302 302 1689 = 102461756220 :=
  @P1_7_1_3.block_append 1387 302 302 1326 1024 665 1689 77109841376 25351914844 102461756220 cost_1387_302_join2_0 cost_1387_302_join2_2 rfl rfl rfl

private theorem cost_1387_302_total : P1_7_1_3.momentEstimate 1387 302 = 102461756220 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1387 + 302 = 1689 by decide]
  exact cost_1387_302_join3_0

theorem moment1387_302 : P1_7_1.groupedPoleMoment 1387 302 ≤ 102461756220 :=
  (P1_7_1_3.grouped_bound 1387 302).trans_eq cost_1387_302_total
private theorem cost_1405_302_block0 : P1_7_1_3.blockEstimate 1405 302 302 128 = 468576160 := by decide +kernel

private theorem cost_1405_302_block1 : P1_7_1_3.blockEstimate 1405 302 430 128 = 2965190560 := by decide +kernel

private theorem cost_1405_302_block2 : P1_7_1_3.blockEstimate 1405 302 558 128 = 7101458238 := by decide +kernel

private theorem cost_1405_302_block3 : P1_7_1_3.blockEstimate 1405 302 686 128 = 10994914944 := by decide +kernel

private theorem cost_1405_302_block4 : P1_7_1_3.blockEstimate 1405 302 814 128 = 13635950208 := by decide +kernel

private theorem cost_1405_302_block5 : P1_7_1_3.blockEstimate 1405 302 942 128 = 15006111360 := by decide +kernel

private theorem cost_1405_302_block6 : P1_7_1_3.blockEstimate 1405 302 1070 128 = 15105398400 := by decide +kernel

private theorem cost_1405_302_block7 : P1_7_1_3.blockEstimate 1405 302 1198 128 = 13933811328 := by decide +kernel

private theorem cost_1405_302_block8 : P1_7_1_3.blockEstimate 1405 302 1326 128 = 11499990506 := by decide +kernel

private theorem cost_1405_302_block9 : P1_7_1_3.blockEstimate 1405 302 1454 128 = 8231828196 := by decide +kernel

private theorem cost_1405_302_block10 : P1_7_1_3.blockEstimate 1405 302 1582 128 = 4995016537 := by decide +kernel

private theorem cost_1405_302_block11 : P1_7_1_3.blockEstimate 1405 302 1710 128 = 2294661280 := by decide +kernel

private theorem cost_1405_302_block12 : P1_7_1_3.blockEstimate 1405 302 1838 128 = 556783776 := by decide +kernel

private theorem cost_1405_302_block13 : P1_7_1_3.blockEstimate 1405 302 1966 43 = 10165419 := by decide +kernel

private theorem cost_1405_302_join0_0 : P1_7_1_3.blockEstimate 1405 302 302 256 = 3433766720 :=
  @P1_7_1_3.block_append 1405 302 302 430 128 128 256 468576160 2965190560 3433766720 cost_1405_302_block0 cost_1405_302_block1 rfl rfl rfl

private theorem cost_1405_302_join0_2 : P1_7_1_3.blockEstimate 1405 302 558 256 = 18096373182 :=
  @P1_7_1_3.block_append 1405 302 558 686 128 128 256 7101458238 10994914944 18096373182 cost_1405_302_block2 cost_1405_302_block3 rfl rfl rfl

private theorem cost_1405_302_join0_4 : P1_7_1_3.blockEstimate 1405 302 814 256 = 28642061568 :=
  @P1_7_1_3.block_append 1405 302 814 942 128 128 256 13635950208 15006111360 28642061568 cost_1405_302_block4 cost_1405_302_block5 rfl rfl rfl

private theorem cost_1405_302_join0_6 : P1_7_1_3.blockEstimate 1405 302 1070 256 = 29039209728 :=
  @P1_7_1_3.block_append 1405 302 1070 1198 128 128 256 15105398400 13933811328 29039209728 cost_1405_302_block6 cost_1405_302_block7 rfl rfl rfl

private theorem cost_1405_302_join0_8 : P1_7_1_3.blockEstimate 1405 302 1326 256 = 19731818702 :=
  @P1_7_1_3.block_append 1405 302 1326 1454 128 128 256 11499990506 8231828196 19731818702 cost_1405_302_block8 cost_1405_302_block9 rfl rfl rfl

private theorem cost_1405_302_join0_10 : P1_7_1_3.blockEstimate 1405 302 1582 256 = 7289677817 :=
  @P1_7_1_3.block_append 1405 302 1582 1710 128 128 256 4995016537 2294661280 7289677817 cost_1405_302_block10 cost_1405_302_block11 rfl rfl rfl

private theorem cost_1405_302_join0_12 : P1_7_1_3.blockEstimate 1405 302 1838 171 = 566949195 :=
  @P1_7_1_3.block_append 1405 302 1838 1966 128 43 171 556783776 10165419 566949195 cost_1405_302_block12 cost_1405_302_block13 rfl rfl rfl

private theorem cost_1405_302_join1_0 : P1_7_1_3.blockEstimate 1405 302 302 512 = 21530139902 :=
  @P1_7_1_3.block_append 1405 302 302 558 256 256 512 3433766720 18096373182 21530139902 cost_1405_302_join0_0 cost_1405_302_join0_2 rfl rfl rfl

private theorem cost_1405_302_join1_2 : P1_7_1_3.blockEstimate 1405 302 814 512 = 57681271296 :=
  @P1_7_1_3.block_append 1405 302 814 1070 256 256 512 28642061568 29039209728 57681271296 cost_1405_302_join0_4 cost_1405_302_join0_6 rfl rfl rfl

private theorem cost_1405_302_join1_4 : P1_7_1_3.blockEstimate 1405 302 1326 512 = 27021496519 :=
  @P1_7_1_3.block_append 1405 302 1326 1582 256 256 512 19731818702 7289677817 27021496519 cost_1405_302_join0_8 cost_1405_302_join0_10 rfl rfl rfl

private theorem cost_1405_302_join2_0 : P1_7_1_3.blockEstimate 1405 302 302 1024 = 79211411198 :=
  @P1_7_1_3.block_append 1405 302 302 814 512 512 1024 21530139902 57681271296 79211411198 cost_1405_302_join1_0 cost_1405_302_join1_2 rfl rfl rfl

private theorem cost_1405_302_join2_2 : P1_7_1_3.blockEstimate 1405 302 1326 683 = 27588445714 :=
  @P1_7_1_3.block_append 1405 302 1326 1838 512 171 683 27021496519 566949195 27588445714 cost_1405_302_join1_4 cost_1405_302_join0_12 rfl rfl rfl

private theorem cost_1405_302_join3_0 : P1_7_1_3.blockEstimate 1405 302 302 1707 = 106799856912 :=
  @P1_7_1_3.block_append 1405 302 302 1326 1024 683 1707 79211411198 27588445714 106799856912 cost_1405_302_join2_0 cost_1405_302_join2_2 rfl rfl rfl

private theorem cost_1405_302_total : P1_7_1_3.momentEstimate 1405 302 = 106799856912 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1405 + 302 = 1707 by decide]
  exact cost_1405_302_join3_0

theorem moment1405_302 : P1_7_1.groupedPoleMoment 1405 302 ≤ 106799856912 :=
  (P1_7_1_3.grouped_bound 1405 302).trans_eq cost_1405_302_total
private theorem cost_1457_317_block0 : P1_7_1_3.blockEstimate 1457 317 317 128 = 487179680 := by decide +kernel

private theorem cost_1457_317_block1 : P1_7_1_3.blockEstimate 1457 317 445 128 = 3093697952 := by decide +kernel

private theorem cost_1457_317_block2 : P1_7_1_3.blockEstimate 1457 317 573 128 = 7490022439 := by decide +kernel

private theorem cost_1457_317_block3 : P1_7_1_3.blockEstimate 1457 317 701 128 = 11860728384 := by decide +kernel

private theorem cost_1457_317_block4 : P1_7_1_3.blockEstimate 1457 317 829 128 = 14942509632 := by decide +kernel

private theorem cost_1457_317_block5 : P1_7_1_3.blockEstimate 1457 317 957 128 = 16690502208 := by decide +kernel

private theorem cost_1457_317_block6 : P1_7_1_3.blockEstimate 1457 317 1085 128 = 17104706112 := by decide +kernel

private theorem cost_1457_317_block7 : P1_7_1_3.blockEstimate 1457 317 1213 128 = 16185121344 := by decide +kernel

private theorem cost_1457_317_block8 : P1_7_1_3.blockEstimate 1457 317 1341 128 = 13931882514 := by decide +kernel

private theorem cost_1457_317_block9 : P1_7_1_3.blockEstimate 1457 317 1469 128 = 10569985087 := by decide +kernel

private theorem cost_1457_317_block10 : P1_7_1_3.blockEstimate 1457 317 1597 128 = 6984617501 := by decide +kernel

private theorem cost_1457_317_block11 : P1_7_1_3.blockEstimate 1457 317 1725 128 = 3773359694 := by decide +kernel

private theorem cost_1457_317_block12 : P1_7_1_3.blockEstimate 1457 317 1853 128 = 1378590928 := by decide +kernel

private theorem cost_1457_317_block13 : P1_7_1_3.blockEstimate 1457 317 1981 110 = 162404942 := by decide +kernel

private theorem cost_1457_317_join0_0 : P1_7_1_3.blockEstimate 1457 317 317 256 = 3580877632 :=
  @P1_7_1_3.block_append 1457 317 317 445 128 128 256 487179680 3093697952 3580877632 cost_1457_317_block0 cost_1457_317_block1 rfl rfl rfl

private theorem cost_1457_317_join0_2 : P1_7_1_3.blockEstimate 1457 317 573 256 = 19350750823 :=
  @P1_7_1_3.block_append 1457 317 573 701 128 128 256 7490022439 11860728384 19350750823 cost_1457_317_block2 cost_1457_317_block3 rfl rfl rfl

private theorem cost_1457_317_join0_4 : P1_7_1_3.blockEstimate 1457 317 829 256 = 31633011840 :=
  @P1_7_1_3.block_append 1457 317 829 957 128 128 256 14942509632 16690502208 31633011840 cost_1457_317_block4 cost_1457_317_block5 rfl rfl rfl

private theorem cost_1457_317_join0_6 : P1_7_1_3.blockEstimate 1457 317 1085 256 = 33289827456 :=
  @P1_7_1_3.block_append 1457 317 1085 1213 128 128 256 17104706112 16185121344 33289827456 cost_1457_317_block6 cost_1457_317_block7 rfl rfl rfl

private theorem cost_1457_317_join0_8 : P1_7_1_3.blockEstimate 1457 317 1341 256 = 24501867601 :=
  @P1_7_1_3.block_append 1457 317 1341 1469 128 128 256 13931882514 10569985087 24501867601 cost_1457_317_block8 cost_1457_317_block9 rfl rfl rfl

private theorem cost_1457_317_join0_10 : P1_7_1_3.blockEstimate 1457 317 1597 256 = 10757977195 :=
  @P1_7_1_3.block_append 1457 317 1597 1725 128 128 256 6984617501 3773359694 10757977195 cost_1457_317_block10 cost_1457_317_block11 rfl rfl rfl

private theorem cost_1457_317_join0_12 : P1_7_1_3.blockEstimate 1457 317 1853 238 = 1540995870 :=
  @P1_7_1_3.block_append 1457 317 1853 1981 128 110 238 1378590928 162404942 1540995870 cost_1457_317_block12 cost_1457_317_block13 rfl rfl rfl

private theorem cost_1457_317_join1_0 : P1_7_1_3.blockEstimate 1457 317 317 512 = 22931628455 :=
  @P1_7_1_3.block_append 1457 317 317 573 256 256 512 3580877632 19350750823 22931628455 cost_1457_317_join0_0 cost_1457_317_join0_2 rfl rfl rfl

private theorem cost_1457_317_join1_2 : P1_7_1_3.blockEstimate 1457 317 829 512 = 64922839296 :=
  @P1_7_1_3.block_append 1457 317 829 1085 256 256 512 31633011840 33289827456 64922839296 cost_1457_317_join0_4 cost_1457_317_join0_6 rfl rfl rfl

private theorem cost_1457_317_join1_4 : P1_7_1_3.blockEstimate 1457 317 1341 512 = 35259844796 :=
  @P1_7_1_3.block_append 1457 317 1341 1597 256 256 512 24501867601 10757977195 35259844796 cost_1457_317_join0_8 cost_1457_317_join0_10 rfl rfl rfl

private theorem cost_1457_317_join2_0 : P1_7_1_3.blockEstimate 1457 317 317 1024 = 87854467751 :=
  @P1_7_1_3.block_append 1457 317 317 829 512 512 1024 22931628455 64922839296 87854467751 cost_1457_317_join1_0 cost_1457_317_join1_2 rfl rfl rfl

private theorem cost_1457_317_join2_2 : P1_7_1_3.blockEstimate 1457 317 1341 750 = 36800840666 :=
  @P1_7_1_3.block_append 1457 317 1341 1853 512 238 750 35259844796 1540995870 36800840666 cost_1457_317_join1_4 cost_1457_317_join0_12 rfl rfl rfl

private theorem cost_1457_317_join3_0 : P1_7_1_3.blockEstimate 1457 317 317 1774 = 124655308417 :=
  @P1_7_1_3.block_append 1457 317 317 1341 1024 750 1774 87854467751 36800840666 124655308417 cost_1457_317_join2_0 cost_1457_317_join2_2 rfl rfl rfl

private theorem cost_1457_317_total : P1_7_1_3.momentEstimate 1457 317 = 124655308417 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1457 + 317 = 1774 by decide]
  exact cost_1457_317_join3_0

theorem moment1457_317 : P1_7_1.groupedPoleMoment 1457 317 ≤ 124655308417 :=
  (P1_7_1_3.grouped_bound 1457 317).trans_eq cost_1457_317_total
private theorem cost_1458_322_block0 : P1_7_1_3.blockEstimate 1458 322 322 128 = 487537440 := by decide +kernel

private theorem cost_1458_322_block1 : P1_7_1_3.blockEstimate 1458 322 450 128 = 3096169248 := by decide +kernel

private theorem cost_1458_322_block2 : P1_7_1_3.blockEstimate 1458 322 578 128 = 7508058402 := by decide +kernel

private theorem cost_1458_322_block3 : P1_7_1_3.blockEstimate 1458 322 706 128 = 11954762304 := by decide +kernel

private theorem cost_1458_322_block4 : P1_7_1_3.blockEstimate 1458 322 834 128 = 15103521344 := by decide +kernel

private theorem cost_1458_322_block5 : P1_7_1_3.blockEstimate 1458 322 962 128 = 16897520192 := by decide +kernel

private theorem cost_1458_322_block6 : P1_7_1_3.blockEstimate 1458 322 1090 128 = 17336758848 := by decide +kernel

private theorem cost_1458_322_block7 : P1_7_1_3.blockEstimate 1458 322 1218 128 = 16421237312 := by decide +kernel

private theorem cost_1458_322_block8 : P1_7_1_3.blockEstimate 1458 322 1346 128 = 14151264932 := by decide +kernel

private theorem cost_1458_322_block9 : P1_7_1_3.blockEstimate 1458 322 1474 128 = 10769776058 := by decide +kernel

private theorem cost_1458_322_block10 : P1_7_1_3.blockEstimate 1458 322 1602 128 = 7161505908 := by decide +kernel

private theorem cost_1458_322_block11 : P1_7_1_3.blockEstimate 1458 322 1730 128 = 3913418815 := by decide +kernel

private theorem cost_1458_322_block12 : P1_7_1_3.blockEstimate 1458 322 1858 128 = 1467688608 := by decide +kernel

private theorem cost_1458_322_block13 : P1_7_1_3.blockEstimate 1458 322 1986 116 = 189816629 := by decide +kernel

private theorem cost_1458_322_join0_0 : P1_7_1_3.blockEstimate 1458 322 322 256 = 3583706688 :=
  @P1_7_1_3.block_append 1458 322 322 450 128 128 256 487537440 3096169248 3583706688 cost_1458_322_block0 cost_1458_322_block1 rfl rfl rfl

private theorem cost_1458_322_join0_2 : P1_7_1_3.blockEstimate 1458 322 578 256 = 19462820706 :=
  @P1_7_1_3.block_append 1458 322 578 706 128 128 256 7508058402 11954762304 19462820706 cost_1458_322_block2 cost_1458_322_block3 rfl rfl rfl

private theorem cost_1458_322_join0_4 : P1_7_1_3.blockEstimate 1458 322 834 256 = 32001041536 :=
  @P1_7_1_3.block_append 1458 322 834 962 128 128 256 15103521344 16897520192 32001041536 cost_1458_322_block4 cost_1458_322_block5 rfl rfl rfl

private theorem cost_1458_322_join0_6 : P1_7_1_3.blockEstimate 1458 322 1090 256 = 33757996160 :=
  @P1_7_1_3.block_append 1458 322 1090 1218 128 128 256 17336758848 16421237312 33757996160 cost_1458_322_block6 cost_1458_322_block7 rfl rfl rfl

private theorem cost_1458_322_join0_8 : P1_7_1_3.blockEstimate 1458 322 1346 256 = 24921040990 :=
  @P1_7_1_3.block_append 1458 322 1346 1474 128 128 256 14151264932 10769776058 24921040990 cost_1458_322_block8 cost_1458_322_block9 rfl rfl rfl

private theorem cost_1458_322_join0_10 : P1_7_1_3.blockEstimate 1458 322 1602 256 = 11074924723 :=
  @P1_7_1_3.block_append 1458 322 1602 1730 128 128 256 7161505908 3913418815 11074924723 cost_1458_322_block10 cost_1458_322_block11 rfl rfl rfl

private theorem cost_1458_322_join0_12 : P1_7_1_3.blockEstimate 1458 322 1858 244 = 1657505237 :=
  @P1_7_1_3.block_append 1458 322 1858 1986 128 116 244 1467688608 189816629 1657505237 cost_1458_322_block12 cost_1458_322_block13 rfl rfl rfl

private theorem cost_1458_322_join1_0 : P1_7_1_3.blockEstimate 1458 322 322 512 = 23046527394 :=
  @P1_7_1_3.block_append 1458 322 322 578 256 256 512 3583706688 19462820706 23046527394 cost_1458_322_join0_0 cost_1458_322_join0_2 rfl rfl rfl

private theorem cost_1458_322_join1_2 : P1_7_1_3.blockEstimate 1458 322 834 512 = 65759037696 :=
  @P1_7_1_3.block_append 1458 322 834 1090 256 256 512 32001041536 33757996160 65759037696 cost_1458_322_join0_4 cost_1458_322_join0_6 rfl rfl rfl

private theorem cost_1458_322_join1_4 : P1_7_1_3.blockEstimate 1458 322 1346 512 = 35995965713 :=
  @P1_7_1_3.block_append 1458 322 1346 1602 256 256 512 24921040990 11074924723 35995965713 cost_1458_322_join0_8 cost_1458_322_join0_10 rfl rfl rfl

private theorem cost_1458_322_join2_0 : P1_7_1_3.blockEstimate 1458 322 322 1024 = 88805565090 :=
  @P1_7_1_3.block_append 1458 322 322 834 512 512 1024 23046527394 65759037696 88805565090 cost_1458_322_join1_0 cost_1458_322_join1_2 rfl rfl rfl

private theorem cost_1458_322_join2_2 : P1_7_1_3.blockEstimate 1458 322 1346 756 = 37653470950 :=
  @P1_7_1_3.block_append 1458 322 1346 1858 512 244 756 35995965713 1657505237 37653470950 cost_1458_322_join1_4 cost_1458_322_join0_12 rfl rfl rfl

private theorem cost_1458_322_join3_0 : P1_7_1_3.blockEstimate 1458 322 322 1780 = 126459036040 :=
  @P1_7_1_3.block_append 1458 322 322 1346 1024 756 1780 88805565090 37653470950 126459036040 cost_1458_322_join2_0 cost_1458_322_join2_2 rfl rfl rfl

private theorem cost_1458_322_total : P1_7_1_3.momentEstimate 1458 322 = 126459036040 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1458 + 322 = 1780 by decide]
  exact cost_1458_322_join3_0

theorem moment1458_322 : P1_7_1.groupedPoleMoment 1458 322 ≤ 126459036040 :=
  (P1_7_1_3.grouped_bound 1458 322).trans_eq cost_1458_322_total
private theorem cost_1532_334_block0 : P1_7_1_3.blockEstimate 1532 334 334 128 = 514011680 := by decide +kernel

private theorem cost_1532_334_block1 : P1_7_1_3.blockEstimate 1532 334 462 128 = 3279045152 := by decide +kernel

private theorem cost_1532_334_block2 : P1_7_1_3.blockEstimate 1532 334 590 128 = 8021632383 := by decide +kernel

private theorem cost_1532_334_block3 : P1_7_1_3.blockEstimate 1532 334 718 128 = 13032153920 := by decide +kernel

private theorem cost_1532_334_block4 : P1_7_1_3.blockEstimate 1532 334 846 128 = 16736985920 := by decide +kernel

private theorem cost_1532_334_block5 : P1_7_1_3.blockEstimate 1532 334 974 128 = 19036726080 := by decide +kernel

private theorem cost_1532_334_block6 : P1_7_1_3.blockEstimate 1532 334 1102 128 = 19931374400 := by decide +kernel

private theorem cost_1532_334_block7 : P1_7_1_3.blockEstimate 1532 334 1230 128 = 19420930880 := by decide +kernel

private theorem cost_1532_334_block8 : P1_7_1_3.blockEstimate 1532 334 1358 128 = 17505395520 := by decide +kernel

private theorem cost_1532_334_block9 : P1_7_1_3.blockEstimate 1532 334 1486 128 = 14229432379 := by decide +kernel

private theorem cost_1532_334_block10 : P1_7_1_3.blockEstimate 1532 334 1614 128 = 10261882685 := by decide +kernel

private theorem cost_1532_334_block11 : P1_7_1_3.blockEstimate 1532 334 1742 128 = 6419561001 := by decide +kernel

private theorem cost_1532_334_block12 : P1_7_1_3.blockEstimate 1532 334 1870 128 = 3173348912 := by decide +kernel

private theorem cost_1532_334_block13 : P1_7_1_3.blockEstimate 1532 334 1998 128 = 956119600 := by decide +kernel

private theorem cost_1532_334_block14 : P1_7_1_3.blockEstimate 1532 334 2126 74 = 53706920 := by decide +kernel

private theorem cost_1532_334_join0_0 : P1_7_1_3.blockEstimate 1532 334 334 256 = 3793056832 :=
  @P1_7_1_3.block_append 1532 334 334 462 128 128 256 514011680 3279045152 3793056832 cost_1532_334_block0 cost_1532_334_block1 rfl rfl rfl

private theorem cost_1532_334_join0_2 : P1_7_1_3.blockEstimate 1532 334 590 256 = 21053786303 :=
  @P1_7_1_3.block_append 1532 334 590 718 128 128 256 8021632383 13032153920 21053786303 cost_1532_334_block2 cost_1532_334_block3 rfl rfl rfl

private theorem cost_1532_334_join0_4 : P1_7_1_3.blockEstimate 1532 334 846 256 = 35773712000 :=
  @P1_7_1_3.block_append 1532 334 846 974 128 128 256 16736985920 19036726080 35773712000 cost_1532_334_block4 cost_1532_334_block5 rfl rfl rfl

private theorem cost_1532_334_join0_6 : P1_7_1_3.blockEstimate 1532 334 1102 256 = 39352305280 :=
  @P1_7_1_3.block_append 1532 334 1102 1230 128 128 256 19931374400 19420930880 39352305280 cost_1532_334_block6 cost_1532_334_block7 rfl rfl rfl

private theorem cost_1532_334_join0_8 : P1_7_1_3.blockEstimate 1532 334 1358 256 = 31734827899 :=
  @P1_7_1_3.block_append 1532 334 1358 1486 128 128 256 17505395520 14229432379 31734827899 cost_1532_334_block8 cost_1532_334_block9 rfl rfl rfl

private theorem cost_1532_334_join0_10 : P1_7_1_3.blockEstimate 1532 334 1614 256 = 16681443686 :=
  @P1_7_1_3.block_append 1532 334 1614 1742 128 128 256 10261882685 6419561001 16681443686 cost_1532_334_block10 cost_1532_334_block11 rfl rfl rfl

private theorem cost_1532_334_join0_12 : P1_7_1_3.blockEstimate 1532 334 1870 256 = 4129468512 :=
  @P1_7_1_3.block_append 1532 334 1870 1998 128 128 256 3173348912 956119600 4129468512 cost_1532_334_block12 cost_1532_334_block13 rfl rfl rfl

private theorem cost_1532_334_join1_0 : P1_7_1_3.blockEstimate 1532 334 334 512 = 24846843135 :=
  @P1_7_1_3.block_append 1532 334 334 590 256 256 512 3793056832 21053786303 24846843135 cost_1532_334_join0_0 cost_1532_334_join0_2 rfl rfl rfl

private theorem cost_1532_334_join1_2 : P1_7_1_3.blockEstimate 1532 334 846 512 = 75126017280 :=
  @P1_7_1_3.block_append 1532 334 846 1102 256 256 512 35773712000 39352305280 75126017280 cost_1532_334_join0_4 cost_1532_334_join0_6 rfl rfl rfl

private theorem cost_1532_334_join1_4 : P1_7_1_3.blockEstimate 1532 334 1358 512 = 48416271585 :=
  @P1_7_1_3.block_append 1532 334 1358 1614 256 256 512 31734827899 16681443686 48416271585 cost_1532_334_join0_8 cost_1532_334_join0_10 rfl rfl rfl

private theorem cost_1532_334_join1_6 : P1_7_1_3.blockEstimate 1532 334 1870 330 = 4183175432 :=
  @P1_7_1_3.block_append 1532 334 1870 2126 256 74 330 4129468512 53706920 4183175432 cost_1532_334_join0_12 cost_1532_334_block14 rfl rfl rfl

private theorem cost_1532_334_join2_0 : P1_7_1_3.blockEstimate 1532 334 334 1024 = 99972860415 :=
  @P1_7_1_3.block_append 1532 334 334 846 512 512 1024 24846843135 75126017280 99972860415 cost_1532_334_join1_0 cost_1532_334_join1_2 rfl rfl rfl

private theorem cost_1532_334_join2_2 : P1_7_1_3.blockEstimate 1532 334 1358 842 = 52599447017 :=
  @P1_7_1_3.block_append 1532 334 1358 1870 512 330 842 48416271585 4183175432 52599447017 cost_1532_334_join1_4 cost_1532_334_join1_6 rfl rfl rfl

private theorem cost_1532_334_join3_0 : P1_7_1_3.blockEstimate 1532 334 334 1866 = 152572307432 :=
  @P1_7_1_3.block_append 1532 334 334 1358 1024 842 1866 99972860415 52599447017 152572307432 cost_1532_334_join2_0 cost_1532_334_join2_2 rfl rfl rfl

private theorem cost_1532_334_total : P1_7_1_3.momentEstimate 1532 334 = 152572307432 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1532 + 334 = 1866 by decide]
  exact cost_1532_334_join3_0

theorem moment1532_334 : P1_7_1.groupedPoleMoment 1532 334 ≤ 152572307432 :=
  (P1_7_1_3.grouped_bound 1532 334).trans_eq cost_1532_334_total
private theorem cost_1533_332_block0 : P1_7_1_3.blockEstimate 1533 332 332 128 = 514369440 := by decide +kernel

private theorem cost_1533_332_block1 : P1_7_1_3.blockEstimate 1533 332 460 128 = 3281516448 := by decide +kernel

private theorem cost_1533_332_block2 : P1_7_1_3.blockEstimate 1533 332 588 128 = 8025259467 := by decide +kernel

private theorem cost_1533_332_block3 : P1_7_1_3.blockEstimate 1533 332 716 128 = 13012617024 := by decide +kernel

private theorem cost_1533_332_block4 : P1_7_1_3.blockEstimate 1533 332 844 128 = 16695330624 := by decide +kernel

private theorem cost_1533_332_block5 : P1_7_1_3.blockEstimate 1533 332 972 128 = 18981340992 := by decide +kernel

private theorem cost_1533_332_block6 : P1_7_1_3.blockEstimate 1533 332 1100 128 = 19870648128 := by decide +kernel

private theorem cost_1533_332_block7 : P1_7_1_3.blockEstimate 1533 332 1228 128 = 19363252032 := by decide +kernel

private theorem cost_1533_332_block8 : P1_7_1_3.blockEstimate 1533 332 1356 128 = 17459152704 := by decide +kernel

private theorem cost_1533_332_block9 : P1_7_1_3.blockEstimate 1533 332 1484 128 = 14198387955 := by decide +kernel

private theorem cost_1533_332_block10 : P1_7_1_3.blockEstimate 1533 332 1612 128 = 10233957436 := by decide +kernel

private theorem cost_1533_332_block11 : P1_7_1_3.blockEstimate 1533 332 1740 128 = 6394578862 := by decide +kernel

private theorem cost_1533_332_block12 : P1_7_1_3.blockEstimate 1533 332 1868 128 = 3153822224 := by decide +kernel

private theorem cost_1533_332_block13 : P1_7_1_3.blockEstimate 1533 332 1996 128 = 944377360 := by decide +kernel

private theorem cost_1533_332_block14 : P1_7_1_3.blockEstimate 1533 332 2124 73 = 51651348 := by decide +kernel

private theorem cost_1533_332_join0_0 : P1_7_1_3.blockEstimate 1533 332 332 256 = 3795885888 :=
  @P1_7_1_3.block_append 1533 332 332 460 128 128 256 514369440 3281516448 3795885888 cost_1533_332_block0 cost_1533_332_block1 rfl rfl rfl

private theorem cost_1533_332_join0_2 : P1_7_1_3.blockEstimate 1533 332 588 256 = 21037876491 :=
  @P1_7_1_3.block_append 1533 332 588 716 128 128 256 8025259467 13012617024 21037876491 cost_1533_332_block2 cost_1533_332_block3 rfl rfl rfl

private theorem cost_1533_332_join0_4 : P1_7_1_3.blockEstimate 1533 332 844 256 = 35676671616 :=
  @P1_7_1_3.block_append 1533 332 844 972 128 128 256 16695330624 18981340992 35676671616 cost_1533_332_block4 cost_1533_332_block5 rfl rfl rfl

private theorem cost_1533_332_join0_6 : P1_7_1_3.blockEstimate 1533 332 1100 256 = 39233900160 :=
  @P1_7_1_3.block_append 1533 332 1100 1228 128 128 256 19870648128 19363252032 39233900160 cost_1533_332_block6 cost_1533_332_block7 rfl rfl rfl

private theorem cost_1533_332_join0_8 : P1_7_1_3.blockEstimate 1533 332 1356 256 = 31657540659 :=
  @P1_7_1_3.block_append 1533 332 1356 1484 128 128 256 17459152704 14198387955 31657540659 cost_1533_332_block8 cost_1533_332_block9 rfl rfl rfl

private theorem cost_1533_332_join0_10 : P1_7_1_3.blockEstimate 1533 332 1612 256 = 16628536298 :=
  @P1_7_1_3.block_append 1533 332 1612 1740 128 128 256 10233957436 6394578862 16628536298 cost_1533_332_block10 cost_1533_332_block11 rfl rfl rfl

private theorem cost_1533_332_join0_12 : P1_7_1_3.blockEstimate 1533 332 1868 256 = 4098199584 :=
  @P1_7_1_3.block_append 1533 332 1868 1996 128 128 256 3153822224 944377360 4098199584 cost_1533_332_block12 cost_1533_332_block13 rfl rfl rfl

private theorem cost_1533_332_join1_0 : P1_7_1_3.blockEstimate 1533 332 332 512 = 24833762379 :=
  @P1_7_1_3.block_append 1533 332 332 588 256 256 512 3795885888 21037876491 24833762379 cost_1533_332_join0_0 cost_1533_332_join0_2 rfl rfl rfl

private theorem cost_1533_332_join1_2 : P1_7_1_3.blockEstimate 1533 332 844 512 = 74910571776 :=
  @P1_7_1_3.block_append 1533 332 844 1100 256 256 512 35676671616 39233900160 74910571776 cost_1533_332_join0_4 cost_1533_332_join0_6 rfl rfl rfl

private theorem cost_1533_332_join1_4 : P1_7_1_3.blockEstimate 1533 332 1356 512 = 48286076957 :=
  @P1_7_1_3.block_append 1533 332 1356 1612 256 256 512 31657540659 16628536298 48286076957 cost_1533_332_join0_8 cost_1533_332_join0_10 rfl rfl rfl

private theorem cost_1533_332_join1_6 : P1_7_1_3.blockEstimate 1533 332 1868 329 = 4149850932 :=
  @P1_7_1_3.block_append 1533 332 1868 2124 256 73 329 4098199584 51651348 4149850932 cost_1533_332_join0_12 cost_1533_332_block14 rfl rfl rfl

private theorem cost_1533_332_join2_0 : P1_7_1_3.blockEstimate 1533 332 332 1024 = 99744334155 :=
  @P1_7_1_3.block_append 1533 332 332 844 512 512 1024 24833762379 74910571776 99744334155 cost_1533_332_join1_0 cost_1533_332_join1_2 rfl rfl rfl

private theorem cost_1533_332_join2_2 : P1_7_1_3.blockEstimate 1533 332 1356 841 = 52435927889 :=
  @P1_7_1_3.block_append 1533 332 1356 1868 512 329 841 48286076957 4149850932 52435927889 cost_1533_332_join1_4 cost_1533_332_join1_6 rfl rfl rfl

private theorem cost_1533_332_join3_0 : P1_7_1_3.blockEstimate 1533 332 332 1865 = 152180262044 :=
  @P1_7_1_3.block_append 1533 332 332 1356 1024 841 1865 99744334155 52435927889 152180262044 cost_1533_332_join2_0 cost_1533_332_join2_2 rfl rfl rfl

private theorem cost_1533_332_total : P1_7_1_3.momentEstimate 1533 332 = 152180262044 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1533 + 332 = 1865 by decide]
  exact cost_1533_332_join3_0

theorem moment1533_332 : P1_7_1.groupedPoleMoment 1533 332 ≤ 152180262044 :=
  (P1_7_1_3.grouped_bound 1533 332).trans_eq cost_1533_332_total
private theorem cost_1533_339_block0 : P1_7_1_3.blockEstimate 1533 339 339 128 = 514369440 := by decide +kernel

private theorem cost_1533_339_block1 : P1_7_1_3.blockEstimate 1533 339 467 128 = 3281516448 := by decide +kernel

private theorem cost_1533_339_block2 : P1_7_1_3.blockEstimate 1533 339 595 128 = 8034872007 := by decide +kernel

private theorem cost_1533_339_block3 : P1_7_1_3.blockEstimate 1533 339 723 128 = 13120812160 := by decide +kernel

private theorem cost_1533_339_block4 : P1_7_1_3.blockEstimate 1533 339 851 128 = 16900437120 := by decide +kernel

private theorem cost_1533_339_block5 : P1_7_1_3.blockEstimate 1533 339 979 128 = 19253998720 := by decide +kernel

private theorem cost_1533_339_block6 : P1_7_1_3.blockEstimate 1533 339 1107 128 = 20181496960 := by decide +kernel

private theorem cost_1533_339_block7 : P1_7_1_3.blockEstimate 1533 339 1235 128 = 19682931840 := by decide +kernel

private theorem cost_1533_339_block8 : P1_7_1_3.blockEstimate 1533 339 1363 128 = 17758303360 := by decide +kernel

private theorem cost_1533_339_block9 : P1_7_1_3.blockEstimate 1533 339 1491 128 = 14458844105 := by decide +kernel

private theorem cost_1533_339_block10 : P1_7_1_3.blockEstimate 1533 339 1619 128 = 10472470667 := by decide +kernel

private theorem cost_1533_339_block11 : P1_7_1_3.blockEstimate 1533 339 1747 128 = 6599501490 := by decide +kernel

private theorem cost_1533_339_block12 : P1_7_1_3.blockEstimate 1533 339 1875 128 = 3308227104 := by decide +kernel

private theorem cost_1533_339_block13 : P1_7_1_3.blockEstimate 1533 339 2003 128 = 1032944160 := by decide +kernel

private theorem cost_1533_339_block14 : P1_7_1_3.blockEstimate 1533 339 2131 80 = 67476980 := by decide +kernel

private theorem cost_1533_339_join0_0 : P1_7_1_3.blockEstimate 1533 339 339 256 = 3795885888 :=
  @P1_7_1_3.block_append 1533 339 339 467 128 128 256 514369440 3281516448 3795885888 cost_1533_339_block0 cost_1533_339_block1 rfl rfl rfl

private theorem cost_1533_339_join0_2 : P1_7_1_3.blockEstimate 1533 339 595 256 = 21155684167 :=
  @P1_7_1_3.block_append 1533 339 595 723 128 128 256 8034872007 13120812160 21155684167 cost_1533_339_block2 cost_1533_339_block3 rfl rfl rfl

private theorem cost_1533_339_join0_4 : P1_7_1_3.blockEstimate 1533 339 851 256 = 36154435840 :=
  @P1_7_1_3.block_append 1533 339 851 979 128 128 256 16900437120 19253998720 36154435840 cost_1533_339_block4 cost_1533_339_block5 rfl rfl rfl

private theorem cost_1533_339_join0_6 : P1_7_1_3.blockEstimate 1533 339 1107 256 = 39864428800 :=
  @P1_7_1_3.block_append 1533 339 1107 1235 128 128 256 20181496960 19682931840 39864428800 cost_1533_339_block6 cost_1533_339_block7 rfl rfl rfl

private theorem cost_1533_339_join0_8 : P1_7_1_3.blockEstimate 1533 339 1363 256 = 32217147465 :=
  @P1_7_1_3.block_append 1533 339 1363 1491 128 128 256 17758303360 14458844105 32217147465 cost_1533_339_block8 cost_1533_339_block9 rfl rfl rfl

private theorem cost_1533_339_join0_10 : P1_7_1_3.blockEstimate 1533 339 1619 256 = 17071972157 :=
  @P1_7_1_3.block_append 1533 339 1619 1747 128 128 256 10472470667 6599501490 17071972157 cost_1533_339_block10 cost_1533_339_block11 rfl rfl rfl

private theorem cost_1533_339_join0_12 : P1_7_1_3.blockEstimate 1533 339 1875 256 = 4341171264 :=
  @P1_7_1_3.block_append 1533 339 1875 2003 128 128 256 3308227104 1032944160 4341171264 cost_1533_339_block12 cost_1533_339_block13 rfl rfl rfl

private theorem cost_1533_339_join1_0 : P1_7_1_3.blockEstimate 1533 339 339 512 = 24951570055 :=
  @P1_7_1_3.block_append 1533 339 339 595 256 256 512 3795885888 21155684167 24951570055 cost_1533_339_join0_0 cost_1533_339_join0_2 rfl rfl rfl

private theorem cost_1533_339_join1_2 : P1_7_1_3.blockEstimate 1533 339 851 512 = 76018864640 :=
  @P1_7_1_3.block_append 1533 339 851 1107 256 256 512 36154435840 39864428800 76018864640 cost_1533_339_join0_4 cost_1533_339_join0_6 rfl rfl rfl

private theorem cost_1533_339_join1_4 : P1_7_1_3.blockEstimate 1533 339 1363 512 = 49289119622 :=
  @P1_7_1_3.block_append 1533 339 1363 1619 256 256 512 32217147465 17071972157 49289119622 cost_1533_339_join0_8 cost_1533_339_join0_10 rfl rfl rfl

private theorem cost_1533_339_join1_6 : P1_7_1_3.blockEstimate 1533 339 1875 336 = 4408648244 :=
  @P1_7_1_3.block_append 1533 339 1875 2131 256 80 336 4341171264 67476980 4408648244 cost_1533_339_join0_12 cost_1533_339_block14 rfl rfl rfl

private theorem cost_1533_339_join2_0 : P1_7_1_3.blockEstimate 1533 339 339 1024 = 100970434695 :=
  @P1_7_1_3.block_append 1533 339 339 851 512 512 1024 24951570055 76018864640 100970434695 cost_1533_339_join1_0 cost_1533_339_join1_2 rfl rfl rfl

private theorem cost_1533_339_join2_2 : P1_7_1_3.blockEstimate 1533 339 1363 848 = 53697767866 :=
  @P1_7_1_3.block_append 1533 339 1363 1875 512 336 848 49289119622 4408648244 53697767866 cost_1533_339_join1_4 cost_1533_339_join1_6 rfl rfl rfl

private theorem cost_1533_339_join3_0 : P1_7_1_3.blockEstimate 1533 339 339 1872 = 154668202561 :=
  @P1_7_1_3.block_append 1533 339 339 1363 1024 848 1872 100970434695 53697767866 154668202561 cost_1533_339_join2_0 cost_1533_339_join2_2 rfl rfl rfl

private theorem cost_1533_339_total : P1_7_1_3.momentEstimate 1533 339 = 154668202561 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1533 + 339 = 1872 by decide]
  exact cost_1533_339_join3_0

theorem moment1533_339 : P1_7_1.groupedPoleMoment 1533 339 ≤ 154668202561 :=
  (P1_7_1_3.grouped_bound 1533 339).trans_eq cost_1533_339_total

end Research6966.HelperRescueCatalogue

end Merged6967_Near6967RescueMoment13

section Merged6967_Near6967RescueMoment14
set_option Elab.async false


set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem cost_1533_341_block0 : P1_7_1_3.blockEstimate 1533 341 341 128 = 514369440 := by decide +kernel

private theorem cost_1533_341_block1 : P1_7_1_3.blockEstimate 1533 341 469 128 = 3281516448 := by decide +kernel

private theorem cost_1533_341_block2 : P1_7_1_3.blockEstimate 1533 341 597 128 = 8037125841 := by decide +kernel

private theorem cost_1533_341_block3 : P1_7_1_3.blockEstimate 1533 341 725 128 = 13150474560 := by decide +kernel

private theorem cost_1533_341_block4 : P1_7_1_3.blockEstimate 1533 341 853 128 = 16957935936 := by decide +kernel

private theorem cost_1533_341_block5 : P1_7_1_3.blockEstimate 1533 341 981 128 = 19330945344 := by decide +kernel

private theorem cost_1533_341_block6 : P1_7_1_3.blockEstimate 1533 341 1109 128 = 20269502784 := by decide +kernel

private theorem cost_1533_341_block7 : P1_7_1_3.blockEstimate 1533 341 1237 128 = 19773608256 := by decide +kernel

private theorem cost_1533_341_block8 : P1_7_1_3.blockEstimate 1533 341 1365 128 = 17843261760 := by decide +kernel

private theorem cost_1533_341_block9 : P1_7_1_3.blockEstimate 1533 341 1493 128 = 14533228087 := by decide +kernel

private theorem cost_1533_341_block10 : P1_7_1_3.blockEstimate 1533 341 1621 128 = 10540914529 := by decide +kernel

private theorem cost_1533_341_block11 : P1_7_1_3.blockEstimate 1533 341 1749 128 = 6658498292 := by decide +kernel

private theorem cost_1533_341_block12 : P1_7_1_3.blockEstimate 1533 341 1877 128 = 3352933008 := by decide +kernel

private theorem cost_1533_341_block13 : P1_7_1_3.blockEstimate 1533 341 2005 128 = 1058977424 := by decide +kernel

private theorem cost_1533_341_block14 : P1_7_1_3.blockEstimate 1533 341 2133 82 = 72522968 := by decide +kernel

private theorem cost_1533_341_join0_0 : P1_7_1_3.blockEstimate 1533 341 341 256 = 3795885888 :=
  @P1_7_1_3.block_append 1533 341 341 469 128 128 256 514369440 3281516448 3795885888 cost_1533_341_block0 cost_1533_341_block1 rfl rfl rfl

private theorem cost_1533_341_join0_2 : P1_7_1_3.blockEstimate 1533 341 597 256 = 21187600401 :=
  @P1_7_1_3.block_append 1533 341 597 725 128 128 256 8037125841 13150474560 21187600401 cost_1533_341_block2 cost_1533_341_block3 rfl rfl rfl

private theorem cost_1533_341_join0_4 : P1_7_1_3.blockEstimate 1533 341 853 256 = 36288881280 :=
  @P1_7_1_3.block_append 1533 341 853 981 128 128 256 16957935936 19330945344 36288881280 cost_1533_341_block4 cost_1533_341_block5 rfl rfl rfl

private theorem cost_1533_341_join0_6 : P1_7_1_3.blockEstimate 1533 341 1109 256 = 40043111040 :=
  @P1_7_1_3.block_append 1533 341 1109 1237 128 128 256 20269502784 19773608256 40043111040 cost_1533_341_block6 cost_1533_341_block7 rfl rfl rfl

private theorem cost_1533_341_join0_8 : P1_7_1_3.blockEstimate 1533 341 1365 256 = 32376489847 :=
  @P1_7_1_3.block_append 1533 341 1365 1493 128 128 256 17843261760 14533228087 32376489847 cost_1533_341_block8 cost_1533_341_block9 rfl rfl rfl

private theorem cost_1533_341_join0_10 : P1_7_1_3.blockEstimate 1533 341 1621 256 = 17199412821 :=
  @P1_7_1_3.block_append 1533 341 1621 1749 128 128 256 10540914529 6658498292 17199412821 cost_1533_341_block10 cost_1533_341_block11 rfl rfl rfl

private theorem cost_1533_341_join0_12 : P1_7_1_3.blockEstimate 1533 341 1877 256 = 4411910432 :=
  @P1_7_1_3.block_append 1533 341 1877 2005 128 128 256 3352933008 1058977424 4411910432 cost_1533_341_block12 cost_1533_341_block13 rfl rfl rfl

private theorem cost_1533_341_join1_0 : P1_7_1_3.blockEstimate 1533 341 341 512 = 24983486289 :=
  @P1_7_1_3.block_append 1533 341 341 597 256 256 512 3795885888 21187600401 24983486289 cost_1533_341_join0_0 cost_1533_341_join0_2 rfl rfl rfl

private theorem cost_1533_341_join1_2 : P1_7_1_3.blockEstimate 1533 341 853 512 = 76331992320 :=
  @P1_7_1_3.block_append 1533 341 853 1109 256 256 512 36288881280 40043111040 76331992320 cost_1533_341_join0_4 cost_1533_341_join0_6 rfl rfl rfl

private theorem cost_1533_341_join1_4 : P1_7_1_3.blockEstimate 1533 341 1365 512 = 49575902668 :=
  @P1_7_1_3.block_append 1533 341 1365 1621 256 256 512 32376489847 17199412821 49575902668 cost_1533_341_join0_8 cost_1533_341_join0_10 rfl rfl rfl

private theorem cost_1533_341_join1_6 : P1_7_1_3.blockEstimate 1533 341 1877 338 = 4484433400 :=
  @P1_7_1_3.block_append 1533 341 1877 2133 256 82 338 4411910432 72522968 4484433400 cost_1533_341_join0_12 cost_1533_341_block14 rfl rfl rfl

private theorem cost_1533_341_join2_0 : P1_7_1_3.blockEstimate 1533 341 341 1024 = 101315478609 :=
  @P1_7_1_3.block_append 1533 341 341 853 512 512 1024 24983486289 76331992320 101315478609 cost_1533_341_join1_0 cost_1533_341_join1_2 rfl rfl rfl

private theorem cost_1533_341_join2_2 : P1_7_1_3.blockEstimate 1533 341 1365 850 = 54060336068 :=
  @P1_7_1_3.block_append 1533 341 1365 1877 512 338 850 49575902668 4484433400 54060336068 cost_1533_341_join1_4 cost_1533_341_join1_6 rfl rfl rfl

private theorem cost_1533_341_join3_0 : P1_7_1_3.blockEstimate 1533 341 341 1874 = 155375814677 :=
  @P1_7_1_3.block_append 1533 341 341 1365 1024 850 1874 101315478609 54060336068 155375814677 cost_1533_341_join2_0 cost_1533_341_join2_2 rfl rfl rfl

private theorem cost_1533_341_total : P1_7_1_3.momentEstimate 1533 341 = 155375814677 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1533 + 341 = 1874 by decide]
  exact cost_1533_341_join3_0

theorem moment1533_341 : P1_7_1.groupedPoleMoment 1533 341 ≤ 155375814677 :=
  (P1_7_1_3.grouped_bound 1533 341).trans_eq cost_1533_341_total
private theorem cost_1534_332_block0 : P1_7_1_3.blockEstimate 1534 332 332 128 = 514727200 := by decide +kernel

private theorem cost_1534_332_block1 : P1_7_1_3.blockEstimate 1534 332 460 128 = 3283987744 := by decide +kernel

private theorem cost_1534_332_block2 : P1_7_1_3.blockEstimate 1534 332 588 128 = 8031918025 := by decide +kernel

private theorem cost_1534_332_block3 : P1_7_1_3.blockEstimate 1534 332 716 128 = 13024658304 := by decide +kernel

private theorem cost_1534_332_block4 : P1_7_1_3.blockEstimate 1534 332 844 128 = 16712827776 := by decide +kernel

private theorem cost_1534_332_block5 : P1_7_1_3.blockEstimate 1534 332 972 128 = 19004294016 := by decide +kernel

private theorem cost_1534_332_block6 : P1_7_1_3.blockEstimate 1534 332 1100 128 = 19899057024 := by decide +kernel

private theorem cost_1534_332_block7 : P1_7_1_3.blockEstimate 1534 332 1228 128 = 19397116800 := by decide +kernel

private theorem cost_1534_332_block8 : P1_7_1_3.blockEstimate 1534 332 1356 128 = 17498473344 := by decide +kernel

private theorem cost_1534_332_block9 : P1_7_1_3.blockEstimate 1534 332 1484 128 = 14241668737 := by decide +kernel

private theorem cost_1534_332_block10 : P1_7_1_3.blockEstimate 1534 332 1612 128 = 10273962190 := by decide +kernel

private theorem cost_1534_332_block11 : P1_7_1_3.blockEstimate 1534 332 1740 128 = 6427836725 := by decide +kernel

private theorem cost_1534_332_block12 : P1_7_1_3.blockEstimate 1534 332 1868 128 = 3178015856 := by decide +kernel

private theorem cost_1534_332_block13 : P1_7_1_3.blockEstimate 1534 332 1996 128 = 957452400 := by decide +kernel

private theorem cost_1534_332_block14 : P1_7_1_3.blockEstimate 1534 332 2124 74 = 53778626 := by decide +kernel

private theorem cost_1534_332_join0_0 : P1_7_1_3.blockEstimate 1534 332 332 256 = 3798714944 :=
  @P1_7_1_3.block_append 1534 332 332 460 128 128 256 514727200 3283987744 3798714944 cost_1534_332_block0 cost_1534_332_block1 rfl rfl rfl

private theorem cost_1534_332_join0_2 : P1_7_1_3.blockEstimate 1534 332 588 256 = 21056576329 :=
  @P1_7_1_3.block_append 1534 332 588 716 128 128 256 8031918025 13024658304 21056576329 cost_1534_332_block2 cost_1534_332_block3 rfl rfl rfl

private theorem cost_1534_332_join0_4 : P1_7_1_3.blockEstimate 1534 332 844 256 = 35717121792 :=
  @P1_7_1_3.block_append 1534 332 844 972 128 128 256 16712827776 19004294016 35717121792 cost_1534_332_block4 cost_1534_332_block5 rfl rfl rfl

private theorem cost_1534_332_join0_6 : P1_7_1_3.blockEstimate 1534 332 1100 256 = 39296173824 :=
  @P1_7_1_3.block_append 1534 332 1100 1228 128 128 256 19899057024 19397116800 39296173824 cost_1534_332_block6 cost_1534_332_block7 rfl rfl rfl

private theorem cost_1534_332_join0_8 : P1_7_1_3.blockEstimate 1534 332 1356 256 = 31740142081 :=
  @P1_7_1_3.block_append 1534 332 1356 1484 128 128 256 17498473344 14241668737 31740142081 cost_1534_332_block8 cost_1534_332_block9 rfl rfl rfl

private theorem cost_1534_332_join0_10 : P1_7_1_3.blockEstimate 1534 332 1612 256 = 16701798915 :=
  @P1_7_1_3.block_append 1534 332 1612 1740 128 128 256 10273962190 6427836725 16701798915 cost_1534_332_block10 cost_1534_332_block11 rfl rfl rfl

private theorem cost_1534_332_join0_12 : P1_7_1_3.blockEstimate 1534 332 1868 256 = 4135468256 :=
  @P1_7_1_3.block_append 1534 332 1868 1996 128 128 256 3178015856 957452400 4135468256 cost_1534_332_block12 cost_1534_332_block13 rfl rfl rfl

private theorem cost_1534_332_join1_0 : P1_7_1_3.blockEstimate 1534 332 332 512 = 24855291273 :=
  @P1_7_1_3.block_append 1534 332 332 588 256 256 512 3798714944 21056576329 24855291273 cost_1534_332_join0_0 cost_1534_332_join0_2 rfl rfl rfl

private theorem cost_1534_332_join1_2 : P1_7_1_3.blockEstimate 1534 332 844 512 = 75013295616 :=
  @P1_7_1_3.block_append 1534 332 844 1100 256 256 512 35717121792 39296173824 75013295616 cost_1534_332_join0_4 cost_1534_332_join0_6 rfl rfl rfl

private theorem cost_1534_332_join1_4 : P1_7_1_3.blockEstimate 1534 332 1356 512 = 48441940996 :=
  @P1_7_1_3.block_append 1534 332 1356 1612 256 256 512 31740142081 16701798915 48441940996 cost_1534_332_join0_8 cost_1534_332_join0_10 rfl rfl rfl

private theorem cost_1534_332_join1_6 : P1_7_1_3.blockEstimate 1534 332 1868 330 = 4189246882 :=
  @P1_7_1_3.block_append 1534 332 1868 2124 256 74 330 4135468256 53778626 4189246882 cost_1534_332_join0_12 cost_1534_332_block14 rfl rfl rfl

private theorem cost_1534_332_join2_0 : P1_7_1_3.blockEstimate 1534 332 332 1024 = 99868586889 :=
  @P1_7_1_3.block_append 1534 332 332 844 512 512 1024 24855291273 75013295616 99868586889 cost_1534_332_join1_0 cost_1534_332_join1_2 rfl rfl rfl

private theorem cost_1534_332_join2_2 : P1_7_1_3.blockEstimate 1534 332 1356 842 = 52631187878 :=
  @P1_7_1_3.block_append 1534 332 1356 1868 512 330 842 48441940996 4189246882 52631187878 cost_1534_332_join1_4 cost_1534_332_join1_6 rfl rfl rfl

private theorem cost_1534_332_join3_0 : P1_7_1_3.blockEstimate 1534 332 332 1866 = 152499774767 :=
  @P1_7_1_3.block_append 1534 332 332 1356 1024 842 1866 99868586889 52631187878 152499774767 cost_1534_332_join2_0 cost_1534_332_join2_2 rfl rfl rfl

private theorem cost_1534_332_total : P1_7_1_3.momentEstimate 1534 332 = 152499774767 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1534 + 332 = 1866 by decide]
  exact cost_1534_332_join3_0

theorem moment1534_332 : P1_7_1.groupedPoleMoment 1534 332 ≤ 152499774767 :=
  (P1_7_1_3.grouped_bound 1534 332).trans_eq cost_1534_332_total
private theorem cost_1534_341_block0 : P1_7_1_3.blockEstimate 1534 341 341 128 = 514727200 := by decide +kernel

private theorem cost_1534_341_block1 : P1_7_1_3.blockEstimate 1534 341 469 128 = 3283987744 := by decide +kernel

private theorem cost_1534_341_block2 : P1_7_1_3.blockEstimate 1534 341 597 128 = 8043794581 := by decide +kernel

private theorem cost_1534_341_block3 : P1_7_1_3.blockEstimate 1534 341 725 128 = 13162644288 := by decide +kernel

private theorem cost_1534_341_block4 : P1_7_1_3.blockEstimate 1534 341 853 128 = 16975708992 := by decide +kernel

private theorem cost_1534_341_block5 : P1_7_1_3.blockEstimate 1534 341 981 128 = 19354321728 := by decide +kernel

private theorem cost_1534_341_block6 : P1_7_1_3.blockEstimate 1534 341 1109 128 = 20298482496 := by decide +kernel

private theorem cost_1534_341_block7 : P1_7_1_3.blockEstimate 1534 341 1237 128 = 19808191296 := by decide +kernel

private theorem cost_1534_341_block8 : P1_7_1_3.blockEstimate 1534 341 1365 128 = 17883448128 := by decide +kernel

private theorem cost_1534_341_block9 : P1_7_1_3.blockEstimate 1534 341 1493 128 = 14577176995 := by decide +kernel

private theorem cost_1534_341_block10 : P1_7_1_3.blockEstimate 1534 341 1621 128 = 10581481849 := by decide +kernel

private theorem cost_1534_341_block11 : P1_7_1_3.blockEstimate 1534 341 1749 128 = 6692402467 := by decide +kernel

private theorem cost_1534_341_block12 : P1_7_1_3.blockEstimate 1534 341 1877 128 = 3377873856 := by decide +kernel

private theorem cost_1534_341_block13 : P1_7_1_3.blockEstimate 1534 341 2005 128 = 1072864192 := by decide +kernel

private theorem cost_1534_341_block14 : P1_7_1_3.blockEstimate 1534 341 2133 83 = 75187252 := by decide +kernel

private theorem cost_1534_341_join0_0 : P1_7_1_3.blockEstimate 1534 341 341 256 = 3798714944 :=
  @P1_7_1_3.block_append 1534 341 341 469 128 128 256 514727200 3283987744 3798714944 cost_1534_341_block0 cost_1534_341_block1 rfl rfl rfl

private theorem cost_1534_341_join0_2 : P1_7_1_3.blockEstimate 1534 341 597 256 = 21206438869 :=
  @P1_7_1_3.block_append 1534 341 597 725 128 128 256 8043794581 13162644288 21206438869 cost_1534_341_block2 cost_1534_341_block3 rfl rfl rfl

private theorem cost_1534_341_join0_4 : P1_7_1_3.blockEstimate 1534 341 853 256 = 36330030720 :=
  @P1_7_1_3.block_append 1534 341 853 981 128 128 256 16975708992 19354321728 36330030720 cost_1534_341_block4 cost_1534_341_block5 rfl rfl rfl

private theorem cost_1534_341_join0_6 : P1_7_1_3.blockEstimate 1534 341 1109 256 = 40106673792 :=
  @P1_7_1_3.block_append 1534 341 1109 1237 128 128 256 20298482496 19808191296 40106673792 cost_1534_341_block6 cost_1534_341_block7 rfl rfl rfl

private theorem cost_1534_341_join0_8 : P1_7_1_3.blockEstimate 1534 341 1365 256 = 32460625123 :=
  @P1_7_1_3.block_append 1534 341 1365 1493 128 128 256 17883448128 14577176995 32460625123 cost_1534_341_block8 cost_1534_341_block9 rfl rfl rfl

private theorem cost_1534_341_join0_10 : P1_7_1_3.blockEstimate 1534 341 1621 256 = 17273884316 :=
  @P1_7_1_3.block_append 1534 341 1621 1749 128 128 256 10581481849 6692402467 17273884316 cost_1534_341_block10 cost_1534_341_block11 rfl rfl rfl

private theorem cost_1534_341_join0_12 : P1_7_1_3.blockEstimate 1534 341 1877 256 = 4450738048 :=
  @P1_7_1_3.block_append 1534 341 1877 2005 128 128 256 3377873856 1072864192 4450738048 cost_1534_341_block12 cost_1534_341_block13 rfl rfl rfl

private theorem cost_1534_341_join1_0 : P1_7_1_3.blockEstimate 1534 341 341 512 = 25005153813 :=
  @P1_7_1_3.block_append 1534 341 341 597 256 256 512 3798714944 21206438869 25005153813 cost_1534_341_join0_0 cost_1534_341_join0_2 rfl rfl rfl

private theorem cost_1534_341_join1_2 : P1_7_1_3.blockEstimate 1534 341 853 512 = 76436704512 :=
  @P1_7_1_3.block_append 1534 341 853 1109 256 256 512 36330030720 40106673792 76436704512 cost_1534_341_join0_4 cost_1534_341_join0_6 rfl rfl rfl

private theorem cost_1534_341_join1_4 : P1_7_1_3.blockEstimate 1534 341 1365 512 = 49734509439 :=
  @P1_7_1_3.block_append 1534 341 1365 1621 256 256 512 32460625123 17273884316 49734509439 cost_1534_341_join0_8 cost_1534_341_join0_10 rfl rfl rfl

private theorem cost_1534_341_join1_6 : P1_7_1_3.blockEstimate 1534 341 1877 339 = 4525925300 :=
  @P1_7_1_3.block_append 1534 341 1877 2133 256 83 339 4450738048 75187252 4525925300 cost_1534_341_join0_12 cost_1534_341_block14 rfl rfl rfl

private theorem cost_1534_341_join2_0 : P1_7_1_3.blockEstimate 1534 341 341 1024 = 101441858325 :=
  @P1_7_1_3.block_append 1534 341 341 853 512 512 1024 25005153813 76436704512 101441858325 cost_1534_341_join1_0 cost_1534_341_join1_2 rfl rfl rfl

private theorem cost_1534_341_join2_2 : P1_7_1_3.blockEstimate 1534 341 1365 851 = 54260434739 :=
  @P1_7_1_3.block_append 1534 341 1365 1877 512 339 851 49734509439 4525925300 54260434739 cost_1534_341_join1_4 cost_1534_341_join1_6 rfl rfl rfl

private theorem cost_1534_341_join3_0 : P1_7_1_3.blockEstimate 1534 341 341 1875 = 155702293064 :=
  @P1_7_1_3.block_append 1534 341 341 1365 1024 851 1875 101441858325 54260434739 155702293064 cost_1534_341_join2_0 cost_1534_341_join2_2 rfl rfl rfl

private theorem cost_1534_341_total : P1_7_1_3.momentEstimate 1534 341 = 155702293064 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1534 + 341 = 1875 by decide]
  exact cost_1534_341_join3_0

theorem moment1534_341 : P1_7_1.groupedPoleMoment 1534 341 ≤ 155702293064 :=
  (P1_7_1_3.grouped_bound 1534 341).trans_eq cost_1534_341_total
private theorem cost_1535_341_block0 : P1_7_1_3.blockEstimate 1535 341 341 128 = 515084960 := by decide +kernel

private theorem cost_1535_341_block1 : P1_7_1_3.blockEstimate 1535 341 469 128 = 3286459040 := by decide +kernel

private theorem cost_1535_341_block2 : P1_7_1_3.blockEstimate 1535 341 597 128 = 8050463321 := by decide +kernel

private theorem cost_1535_341_block3 : P1_7_1_3.blockEstimate 1535 341 725 128 = 13174814016 := by decide +kernel

private theorem cost_1535_341_block4 : P1_7_1_3.blockEstimate 1535 341 853 128 = 16993482048 := by decide +kernel

private theorem cost_1535_341_block5 : P1_7_1_3.blockEstimate 1535 341 981 128 = 19377698112 := by decide +kernel

private theorem cost_1535_341_block6 : P1_7_1_3.blockEstimate 1535 341 1109 128 = 20327462208 := by decide +kernel

private theorem cost_1535_341_block7 : P1_7_1_3.blockEstimate 1535 341 1237 128 = 19842774336 := by decide +kernel

private theorem cost_1535_341_block8 : P1_7_1_3.blockEstimate 1535 341 1365 128 = 17923634496 := by decide +kernel

private theorem cost_1535_341_block9 : P1_7_1_3.blockEstimate 1535 341 1493 128 = 14621167945 := by decide +kernel

private theorem cost_1535_341_block10 : P1_7_1_3.blockEstimate 1535 341 1621 128 = 10622124541 := by decide +kernel

private theorem cost_1535_341_block11 : P1_7_1_3.blockEstimate 1535 341 1749 128 = 6726391197 := by decide +kernel

private theorem cost_1535_341_block12 : P1_7_1_3.blockEstimate 1535 341 1877 128 = 3402915200 := by decide +kernel

private theorem cost_1535_341_block13 : P1_7_1_3.blockEstimate 1535 341 2005 128 = 1086850432 := by decide +kernel

private theorem cost_1535_341_block14 : P1_7_1_3.blockEstimate 1535 341 2133 84 = 77916258 := by decide +kernel

private theorem cost_1535_341_join0_0 : P1_7_1_3.blockEstimate 1535 341 341 256 = 3801544000 :=
  @P1_7_1_3.block_append 1535 341 341 469 128 128 256 515084960 3286459040 3801544000 cost_1535_341_block0 cost_1535_341_block1 rfl rfl rfl

private theorem cost_1535_341_join0_2 : P1_7_1_3.blockEstimate 1535 341 597 256 = 21225277337 :=
  @P1_7_1_3.block_append 1535 341 597 725 128 128 256 8050463321 13174814016 21225277337 cost_1535_341_block2 cost_1535_341_block3 rfl rfl rfl

private theorem cost_1535_341_join0_4 : P1_7_1_3.blockEstimate 1535 341 853 256 = 36371180160 :=
  @P1_7_1_3.block_append 1535 341 853 981 128 128 256 16993482048 19377698112 36371180160 cost_1535_341_block4 cost_1535_341_block5 rfl rfl rfl

private theorem cost_1535_341_join0_6 : P1_7_1_3.blockEstimate 1535 341 1109 256 = 40170236544 :=
  @P1_7_1_3.block_append 1535 341 1109 1237 128 128 256 20327462208 19842774336 40170236544 cost_1535_341_block6 cost_1535_341_block7 rfl rfl rfl

private theorem cost_1535_341_join0_8 : P1_7_1_3.blockEstimate 1535 341 1365 256 = 32544802441 :=
  @P1_7_1_3.block_append 1535 341 1365 1493 128 128 256 17923634496 14621167945 32544802441 cost_1535_341_block8 cost_1535_341_block9 rfl rfl rfl

private theorem cost_1535_341_join0_10 : P1_7_1_3.blockEstimate 1535 341 1621 256 = 17348515738 :=
  @P1_7_1_3.block_append 1535 341 1621 1749 128 128 256 10622124541 6726391197 17348515738 cost_1535_341_block10 cost_1535_341_block11 rfl rfl rfl

private theorem cost_1535_341_join0_12 : P1_7_1_3.blockEstimate 1535 341 1877 256 = 4489765632 :=
  @P1_7_1_3.block_append 1535 341 1877 2005 128 128 256 3402915200 1086850432 4489765632 cost_1535_341_block12 cost_1535_341_block13 rfl rfl rfl

private theorem cost_1535_341_join1_0 : P1_7_1_3.blockEstimate 1535 341 341 512 = 25026821337 :=
  @P1_7_1_3.block_append 1535 341 341 597 256 256 512 3801544000 21225277337 25026821337 cost_1535_341_join0_0 cost_1535_341_join0_2 rfl rfl rfl

private theorem cost_1535_341_join1_2 : P1_7_1_3.blockEstimate 1535 341 853 512 = 76541416704 :=
  @P1_7_1_3.block_append 1535 341 853 1109 256 256 512 36371180160 40170236544 76541416704 cost_1535_341_join0_4 cost_1535_341_join0_6 rfl rfl rfl

private theorem cost_1535_341_join1_4 : P1_7_1_3.blockEstimate 1535 341 1365 512 = 49893318179 :=
  @P1_7_1_3.block_append 1535 341 1365 1621 256 256 512 32544802441 17348515738 49893318179 cost_1535_341_join0_8 cost_1535_341_join0_10 rfl rfl rfl

private theorem cost_1535_341_join1_6 : P1_7_1_3.blockEstimate 1535 341 1877 340 = 4567681890 :=
  @P1_7_1_3.block_append 1535 341 1877 2133 256 84 340 4489765632 77916258 4567681890 cost_1535_341_join0_12 cost_1535_341_block14 rfl rfl rfl

private theorem cost_1535_341_join2_0 : P1_7_1_3.blockEstimate 1535 341 341 1024 = 101568238041 :=
  @P1_7_1_3.block_append 1535 341 341 853 512 512 1024 25026821337 76541416704 101568238041 cost_1535_341_join1_0 cost_1535_341_join1_2 rfl rfl rfl

private theorem cost_1535_341_join2_2 : P1_7_1_3.blockEstimate 1535 341 1365 852 = 54461000069 :=
  @P1_7_1_3.block_append 1535 341 1365 1877 512 340 852 49893318179 4567681890 54461000069 cost_1535_341_join1_4 cost_1535_341_join1_6 rfl rfl rfl

private theorem cost_1535_341_join3_0 : P1_7_1_3.blockEstimate 1535 341 341 1876 = 156029238110 :=
  @P1_7_1_3.block_append 1535 341 341 1365 1024 852 1876 101568238041 54461000069 156029238110 cost_1535_341_join2_0 cost_1535_341_join2_2 rfl rfl rfl

private theorem cost_1535_341_total : P1_7_1_3.momentEstimate 1535 341 = 156029238110 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1535 + 341 = 1876 by decide]
  exact cost_1535_341_join3_0

theorem moment1535_341 : P1_7_1.groupedPoleMoment 1535 341 ≤ 156029238110 :=
  (P1_7_1_3.grouped_bound 1535 341).trans_eq cost_1535_341_total
private theorem cost_1613_347_block0 : P1_7_1_3.blockEstimate 1613 347 347 128 = 542990240 := by decide +kernel

private theorem cost_1613_347_block1 : P1_7_1_3.blockEstimate 1613 347 475 128 = 3479220128 := by decide +kernel

private theorem cost_1613_347_block2 : P1_7_1_3.blockEstimate 1613 347 603 128 = 8576600817 := by decide +kernel

private theorem cost_1613_347_block3 : P1_7_1_3.blockEstimate 1613 347 731 128 = 14216095104 := by decide +kernel

private theorem cost_1613_347_block4 : P1_7_1_3.blockEstimate 1613 347 859 128 = 18563589504 := by decide +kernel

private theorem cost_1613_347_block5 : P1_7_1_3.blockEstimate 1613 347 987 128 = 21451466112 := by decide +kernel

private theorem cost_1613_347_block6 : P1_7_1_3.blockEstimate 1613 347 1115 128 = 22879724928 := by decide +kernel

private theorem cost_1613_347_block7 : P1_7_1_3.blockEstimate 1613 347 1243 128 = 22848365952 := by decide +kernel

private theorem cost_1613_347_block8 : P1_7_1_3.blockEstimate 1613 347 1371 128 = 21357389184 := by decide +kernel

private theorem cost_1613_347_block9 : P1_7_1_3.blockEstimate 1613 347 1499 128 = 18407030076 := by decide +kernel

private theorem cost_1613_347_block10 : P1_7_1_3.blockEstimate 1613 347 1627 128 = 14255407159 := by decide +kernel

private theorem cost_1613_347_block11 : P1_7_1_3.blockEstimate 1613 347 1755 128 = 9858510565 := by decide +kernel

private theorem cost_1613_347_block12 : P1_7_1_3.blockEstimate 1613 347 1883 128 = 5830142676 := by decide +kernel

private theorem cost_1613_347_block13 : P1_7_1_3.blockEstimate 1613 347 2011 128 = 2613375904 := by decide +kernel

private theorem cost_1613_347_block14 : P1_7_1_3.blockEstimate 1613 347 2139 128 = 613364640 := by decide +kernel

private theorem cost_1613_347_block15 : P1_7_1_3.blockEstimate 1613 347 2267 40 = 9489690 := by decide +kernel

private theorem cost_1613_347_join0_0 : P1_7_1_3.blockEstimate 1613 347 347 256 = 4022210368 :=
  @P1_7_1_3.block_append 1613 347 347 475 128 128 256 542990240 3479220128 4022210368 cost_1613_347_block0 cost_1613_347_block1 rfl rfl rfl

private theorem cost_1613_347_join0_2 : P1_7_1_3.blockEstimate 1613 347 603 256 = 22792695921 :=
  @P1_7_1_3.block_append 1613 347 603 731 128 128 256 8576600817 14216095104 22792695921 cost_1613_347_block2 cost_1613_347_block3 rfl rfl rfl

private theorem cost_1613_347_join0_4 : P1_7_1_3.blockEstimate 1613 347 859 256 = 40015055616 :=
  @P1_7_1_3.block_append 1613 347 859 987 128 128 256 18563589504 21451466112 40015055616 cost_1613_347_block4 cost_1613_347_block5 rfl rfl rfl

private theorem cost_1613_347_join0_6 : P1_7_1_3.blockEstimate 1613 347 1115 256 = 45728090880 :=
  @P1_7_1_3.block_append 1613 347 1115 1243 128 128 256 22879724928 22848365952 45728090880 cost_1613_347_block6 cost_1613_347_block7 rfl rfl rfl

private theorem cost_1613_347_join0_8 : P1_7_1_3.blockEstimate 1613 347 1371 256 = 39764419260 :=
  @P1_7_1_3.block_append 1613 347 1371 1499 128 128 256 21357389184 18407030076 39764419260 cost_1613_347_block8 cost_1613_347_block9 rfl rfl rfl

private theorem cost_1613_347_join0_10 : P1_7_1_3.blockEstimate 1613 347 1627 256 = 24113917724 :=
  @P1_7_1_3.block_append 1613 347 1627 1755 128 128 256 14255407159 9858510565 24113917724 cost_1613_347_block10 cost_1613_347_block11 rfl rfl rfl

private theorem cost_1613_347_join0_12 : P1_7_1_3.blockEstimate 1613 347 1883 256 = 8443518580 :=
  @P1_7_1_3.block_append 1613 347 1883 2011 128 128 256 5830142676 2613375904 8443518580 cost_1613_347_block12 cost_1613_347_block13 rfl rfl rfl

private theorem cost_1613_347_join0_14 : P1_7_1_3.blockEstimate 1613 347 2139 168 = 622854330 :=
  @P1_7_1_3.block_append 1613 347 2139 2267 128 40 168 613364640 9489690 622854330 cost_1613_347_block14 cost_1613_347_block15 rfl rfl rfl

private theorem cost_1613_347_join1_0 : P1_7_1_3.blockEstimate 1613 347 347 512 = 26814906289 :=
  @P1_7_1_3.block_append 1613 347 347 603 256 256 512 4022210368 22792695921 26814906289 cost_1613_347_join0_0 cost_1613_347_join0_2 rfl rfl rfl

private theorem cost_1613_347_join1_2 : P1_7_1_3.blockEstimate 1613 347 859 512 = 85743146496 :=
  @P1_7_1_3.block_append 1613 347 859 1115 256 256 512 40015055616 45728090880 85743146496 cost_1613_347_join0_4 cost_1613_347_join0_6 rfl rfl rfl

private theorem cost_1613_347_join1_4 : P1_7_1_3.blockEstimate 1613 347 1371 512 = 63878336984 :=
  @P1_7_1_3.block_append 1613 347 1371 1627 256 256 512 39764419260 24113917724 63878336984 cost_1613_347_join0_8 cost_1613_347_join0_10 rfl rfl rfl

private theorem cost_1613_347_join1_6 : P1_7_1_3.blockEstimate 1613 347 1883 424 = 9066372910 :=
  @P1_7_1_3.block_append 1613 347 1883 2139 256 168 424 8443518580 622854330 9066372910 cost_1613_347_join0_12 cost_1613_347_join0_14 rfl rfl rfl

private theorem cost_1613_347_join2_0 : P1_7_1_3.blockEstimate 1613 347 347 1024 = 112558052785 :=
  @P1_7_1_3.block_append 1613 347 347 859 512 512 1024 26814906289 85743146496 112558052785 cost_1613_347_join1_0 cost_1613_347_join1_2 rfl rfl rfl

private theorem cost_1613_347_join2_2 : P1_7_1_3.blockEstimate 1613 347 1371 936 = 72944709894 :=
  @P1_7_1_3.block_append 1613 347 1371 1883 512 424 936 63878336984 9066372910 72944709894 cost_1613_347_join1_4 cost_1613_347_join1_6 rfl rfl rfl

private theorem cost_1613_347_join3_0 : P1_7_1_3.blockEstimate 1613 347 347 1960 = 185502762679 :=
  @P1_7_1_3.block_append 1613 347 347 1371 1024 936 1960 112558052785 72944709894 185502762679 cost_1613_347_join2_0 cost_1613_347_join2_2 rfl rfl rfl

private theorem cost_1613_347_total : P1_7_1_3.momentEstimate 1613 347 = 185502762679 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1613 + 347 = 1960 by decide]
  exact cost_1613_347_join3_0

theorem moment1613_347 : P1_7_1.groupedPoleMoment 1613 347 ≤ 185502762679 :=
  (P1_7_1_3.grouped_bound 1613 347).trans_eq cost_1613_347_total
private theorem cost_1641_357_block0 : P1_7_1_3.blockEstimate 1641 357 357 128 = 553007520 := by decide +kernel

private theorem cost_1641_357_block1 : P1_7_1_3.blockEstimate 1641 357 485 128 = 3548416416 := by decide +kernel

private theorem cost_1641_357_block2 : P1_7_1_3.blockEstimate 1641 357 613 128 = 8770004781 := by decide +kernel

private theorem cost_1641_357_block3 : P1_7_1_3.blockEstimate 1641 357 741 128 = 14703993664 := by decide +kernel

private theorem cost_1641_357_block4 : P1_7_1_3.blockEstimate 1641 357 869 128 = 19369976640 := by decide +kernel

private theorem cost_1641_357_block5 : P1_7_1_3.blockEstimate 1641 357 997 128 = 22534398784 := by decide +kernel

private theorem cost_1641_357_block6 : P1_7_1_3.blockEstimate 1641 357 1125 128 = 24197260096 := by decide +kernel

private theorem cost_1641_357_block7 : P1_7_1_3.blockEstimate 1641 357 1253 128 = 24358560576 := by decide +kernel

private theorem cost_1641_357_block8 : P1_7_1_3.blockEstimate 1641 357 1381 128 = 23018300224 := by decide +kernel

private theorem cost_1641_357_block9 : P1_7_1_3.blockEstimate 1641 357 1509 128 = 20176479040 := by decide +kernel

private theorem cost_1641_357_block10 : P1_7_1_3.blockEstimate 1641 357 1637 128 = 16004071811 := by decide +kernel

private theorem cost_1641_357_block11 : P1_7_1_3.blockEstimate 1641 357 1765 128 = 11423226482 := by decide +kernel

private theorem cost_1641_357_block12 : P1_7_1_3.blockEstimate 1641 357 1893 128 = 7113747236 := by decide +kernel

private theorem cost_1641_357_block13 : P1_7_1_3.blockEstimate 1641 357 2021 128 = 3523248848 := by decide +kernel

private theorem cost_1641_357_block14 : P1_7_1_3.blockEstimate 1641 357 2149 128 = 1083117264 := by decide +kernel

private theorem cost_1641_357_block15 : P1_7_1_3.blockEstimate 1641 357 2277 78 = 67189530 := by decide +kernel

private theorem cost_1641_357_join0_0 : P1_7_1_3.blockEstimate 1641 357 357 256 = 4101423936 :=
  @P1_7_1_3.block_append 1641 357 357 485 128 128 256 553007520 3548416416 4101423936 cost_1641_357_block0 cost_1641_357_block1 rfl rfl rfl

private theorem cost_1641_357_join0_2 : P1_7_1_3.blockEstimate 1641 357 613 256 = 23473998445 :=
  @P1_7_1_3.block_append 1641 357 613 741 128 128 256 8770004781 14703993664 23473998445 cost_1641_357_block2 cost_1641_357_block3 rfl rfl rfl

private theorem cost_1641_357_join0_4 : P1_7_1_3.blockEstimate 1641 357 869 256 = 41904375424 :=
  @P1_7_1_3.block_append 1641 357 869 997 128 128 256 19369976640 22534398784 41904375424 cost_1641_357_block4 cost_1641_357_block5 rfl rfl rfl

private theorem cost_1641_357_join0_6 : P1_7_1_3.blockEstimate 1641 357 1125 256 = 48555820672 :=
  @P1_7_1_3.block_append 1641 357 1125 1253 128 128 256 24197260096 24358560576 48555820672 cost_1641_357_block6 cost_1641_357_block7 rfl rfl rfl

private theorem cost_1641_357_join0_8 : P1_7_1_3.blockEstimate 1641 357 1381 256 = 43194779264 :=
  @P1_7_1_3.block_append 1641 357 1381 1509 128 128 256 23018300224 20176479040 43194779264 cost_1641_357_block8 cost_1641_357_block9 rfl rfl rfl

private theorem cost_1641_357_join0_10 : P1_7_1_3.blockEstimate 1641 357 1637 256 = 27427298293 :=
  @P1_7_1_3.block_append 1641 357 1637 1765 128 128 256 16004071811 11423226482 27427298293 cost_1641_357_block10 cost_1641_357_block11 rfl rfl rfl

private theorem cost_1641_357_join0_12 : P1_7_1_3.blockEstimate 1641 357 1893 256 = 10636996084 :=
  @P1_7_1_3.block_append 1641 357 1893 2021 128 128 256 7113747236 3523248848 10636996084 cost_1641_357_block12 cost_1641_357_block13 rfl rfl rfl

private theorem cost_1641_357_join0_14 : P1_7_1_3.blockEstimate 1641 357 2149 206 = 1150306794 :=
  @P1_7_1_3.block_append 1641 357 2149 2277 128 78 206 1083117264 67189530 1150306794 cost_1641_357_block14 cost_1641_357_block15 rfl rfl rfl

private theorem cost_1641_357_join1_0 : P1_7_1_3.blockEstimate 1641 357 357 512 = 27575422381 :=
  @P1_7_1_3.block_append 1641 357 357 613 256 256 512 4101423936 23473998445 27575422381 cost_1641_357_join0_0 cost_1641_357_join0_2 rfl rfl rfl

private theorem cost_1641_357_join1_2 : P1_7_1_3.blockEstimate 1641 357 869 512 = 90460196096 :=
  @P1_7_1_3.block_append 1641 357 869 1125 256 256 512 41904375424 48555820672 90460196096 cost_1641_357_join0_4 cost_1641_357_join0_6 rfl rfl rfl

private theorem cost_1641_357_join1_4 : P1_7_1_3.blockEstimate 1641 357 1381 512 = 70622077557 :=
  @P1_7_1_3.block_append 1641 357 1381 1637 256 256 512 43194779264 27427298293 70622077557 cost_1641_357_join0_8 cost_1641_357_join0_10 rfl rfl rfl

private theorem cost_1641_357_join1_6 : P1_7_1_3.blockEstimate 1641 357 1893 462 = 11787302878 :=
  @P1_7_1_3.block_append 1641 357 1893 2149 256 206 462 10636996084 1150306794 11787302878 cost_1641_357_join0_12 cost_1641_357_join0_14 rfl rfl rfl

private theorem cost_1641_357_join2_0 : P1_7_1_3.blockEstimate 1641 357 357 1024 = 118035618477 :=
  @P1_7_1_3.block_append 1641 357 357 869 512 512 1024 27575422381 90460196096 118035618477 cost_1641_357_join1_0 cost_1641_357_join1_2 rfl rfl rfl

private theorem cost_1641_357_join2_2 : P1_7_1_3.blockEstimate 1641 357 1381 974 = 82409380435 :=
  @P1_7_1_3.block_append 1641 357 1381 1893 512 462 974 70622077557 11787302878 82409380435 cost_1641_357_join1_4 cost_1641_357_join1_6 rfl rfl rfl

private theorem cost_1641_357_join3_0 : P1_7_1_3.blockEstimate 1641 357 357 1998 = 200444998912 :=
  @P1_7_1_3.block_append 1641 357 357 1381 1024 974 1998 118035618477 82409380435 200444998912 cost_1641_357_join2_0 cost_1641_357_join2_2 rfl rfl rfl

private theorem cost_1641_357_total : P1_7_1_3.momentEstimate 1641 357 = 200444998912 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1641 + 357 = 1998 by decide]
  exact cost_1641_357_join3_0

theorem moment1641_357 : P1_7_1.groupedPoleMoment 1641 357 ≤ 200444998912 :=
  (P1_7_1_3.grouped_bound 1641 357).trans_eq cost_1641_357_total
private theorem cost_1641_365_block0 : P1_7_1_3.blockEstimate 1641 365 365 128 = 553007520 := by decide +kernel

private theorem cost_1641_365_block1 : P1_7_1_3.blockEstimate 1641 365 493 128 = 3548416416 := by decide +kernel

private theorem cost_1641_365_block2 : P1_7_1_3.blockEstimate 1641 365 621 128 = 8772707499 := by decide +kernel

private theorem cost_1641_365_block3 : P1_7_1_3.blockEstimate 1641 365 749 128 = 14808922176 := by decide +kernel

private theorem cost_1641_365_block4 : P1_7_1_3.blockEstimate 1641 365 877 128 = 19603159104 := by decide +kernel

private theorem cost_1641_365_block5 : P1_7_1_3.blockEstimate 1641 365 1005 128 = 22862280768 := by decide +kernel

private theorem cost_1641_365_block6 : P1_7_1_3.blockEstimate 1641 365 1133 128 = 24586287168 := by decide +kernel

private theorem cost_1641_365_block7 : P1_7_1_3.blockEstimate 1641 365 1261 128 = 24775178304 := by decide +kernel

private theorem cost_1641_365_block8 : P1_7_1_3.blockEstimate 1641 365 1389 128 = 23428954176 := by decide +kernel

private theorem cost_1641_365_block9 : P1_7_1_3.blockEstimate 1641 365 1517 128 = 20547621190 := by decide +kernel

private theorem cost_1641_365_block10 : P1_7_1_3.blockEstimate 1641 365 1645 128 = 16335829098 := by decide +kernel

private theorem cost_1641_365_block11 : P1_7_1_3.blockEstimate 1641 365 1773 128 = 11727386335 := by decide +kernel

private theorem cost_1641_365_block12 : P1_7_1_3.blockEstimate 1641 365 1901 128 = 7372966962 := by decide +kernel

private theorem cost_1641_365_block13 : P1_7_1_3.blockEstimate 1641 365 2029 128 = 3717825680 := by decide +kernel

private theorem cost_1641_365_block14 : P1_7_1_3.blockEstimate 1641 365 2157 128 = 1196048528 := by decide +kernel

private theorem cost_1641_365_block15 : P1_7_1_3.blockEstimate 1641 365 2285 86 = 89377849 := by decide +kernel

private theorem cost_1641_365_join0_0 : P1_7_1_3.blockEstimate 1641 365 365 256 = 4101423936 :=
  @P1_7_1_3.block_append 1641 365 365 493 128 128 256 553007520 3548416416 4101423936 cost_1641_365_block0 cost_1641_365_block1 rfl rfl rfl

private theorem cost_1641_365_join0_2 : P1_7_1_3.blockEstimate 1641 365 621 256 = 23581629675 :=
  @P1_7_1_3.block_append 1641 365 621 749 128 128 256 8772707499 14808922176 23581629675 cost_1641_365_block2 cost_1641_365_block3 rfl rfl rfl

private theorem cost_1641_365_join0_4 : P1_7_1_3.blockEstimate 1641 365 877 256 = 42465439872 :=
  @P1_7_1_3.block_append 1641 365 877 1005 128 128 256 19603159104 22862280768 42465439872 cost_1641_365_block4 cost_1641_365_block5 rfl rfl rfl

private theorem cost_1641_365_join0_6 : P1_7_1_3.blockEstimate 1641 365 1133 256 = 49361465472 :=
  @P1_7_1_3.block_append 1641 365 1133 1261 128 128 256 24586287168 24775178304 49361465472 cost_1641_365_block6 cost_1641_365_block7 rfl rfl rfl

private theorem cost_1641_365_join0_8 : P1_7_1_3.blockEstimate 1641 365 1389 256 = 43976575366 :=
  @P1_7_1_3.block_append 1641 365 1389 1517 128 128 256 23428954176 20547621190 43976575366 cost_1641_365_block8 cost_1641_365_block9 rfl rfl rfl

private theorem cost_1641_365_join0_10 : P1_7_1_3.blockEstimate 1641 365 1645 256 = 28063215433 :=
  @P1_7_1_3.block_append 1641 365 1645 1773 128 128 256 16335829098 11727386335 28063215433 cost_1641_365_block10 cost_1641_365_block11 rfl rfl rfl

private theorem cost_1641_365_join0_12 : P1_7_1_3.blockEstimate 1641 365 1901 256 = 11090792642 :=
  @P1_7_1_3.block_append 1641 365 1901 2029 128 128 256 7372966962 3717825680 11090792642 cost_1641_365_block12 cost_1641_365_block13 rfl rfl rfl

private theorem cost_1641_365_join0_14 : P1_7_1_3.blockEstimate 1641 365 2157 214 = 1285426377 :=
  @P1_7_1_3.block_append 1641 365 2157 2285 128 86 214 1196048528 89377849 1285426377 cost_1641_365_block14 cost_1641_365_block15 rfl rfl rfl

private theorem cost_1641_365_join1_0 : P1_7_1_3.blockEstimate 1641 365 365 512 = 27683053611 :=
  @P1_7_1_3.block_append 1641 365 365 621 256 256 512 4101423936 23581629675 27683053611 cost_1641_365_join0_0 cost_1641_365_join0_2 rfl rfl rfl

private theorem cost_1641_365_join1_2 : P1_7_1_3.blockEstimate 1641 365 877 512 = 91826905344 :=
  @P1_7_1_3.block_append 1641 365 877 1133 256 256 512 42465439872 49361465472 91826905344 cost_1641_365_join0_4 cost_1641_365_join0_6 rfl rfl rfl

private theorem cost_1641_365_join1_4 : P1_7_1_3.blockEstimate 1641 365 1389 512 = 72039790799 :=
  @P1_7_1_3.block_append 1641 365 1389 1645 256 256 512 43976575366 28063215433 72039790799 cost_1641_365_join0_8 cost_1641_365_join0_10 rfl rfl rfl

private theorem cost_1641_365_join1_6 : P1_7_1_3.blockEstimate 1641 365 1901 470 = 12376219019 :=
  @P1_7_1_3.block_append 1641 365 1901 2157 256 214 470 11090792642 1285426377 12376219019 cost_1641_365_join0_12 cost_1641_365_join0_14 rfl rfl rfl

private theorem cost_1641_365_join2_0 : P1_7_1_3.blockEstimate 1641 365 365 1024 = 119509958955 :=
  @P1_7_1_3.block_append 1641 365 365 877 512 512 1024 27683053611 91826905344 119509958955 cost_1641_365_join1_0 cost_1641_365_join1_2 rfl rfl rfl

private theorem cost_1641_365_join2_2 : P1_7_1_3.blockEstimate 1641 365 1389 982 = 84416009818 :=
  @P1_7_1_3.block_append 1641 365 1389 1901 512 470 982 72039790799 12376219019 84416009818 cost_1641_365_join1_4 cost_1641_365_join1_6 rfl rfl rfl

private theorem cost_1641_365_join3_0 : P1_7_1_3.blockEstimate 1641 365 365 2006 = 203925968773 :=
  @P1_7_1_3.block_append 1641 365 365 1389 1024 982 2006 119509958955 84416009818 203925968773 cost_1641_365_join2_0 cost_1641_365_join2_2 rfl rfl rfl

private theorem cost_1641_365_total : P1_7_1_3.momentEstimate 1641 365 = 203925968773 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1641 + 365 = 2006 by decide]
  exact cost_1641_365_join3_0

theorem moment1641_365 : P1_7_1.groupedPoleMoment 1641 365 ≤ 203925968773 :=
  (P1_7_1_3.grouped_bound 1641 365).trans_eq cost_1641_365_total
private theorem cost_1641_367_block0 : P1_7_1_3.blockEstimate 1641 367 367 128 = 553007520 := by decide +kernel

private theorem cost_1641_367_block1 : P1_7_1_3.blockEstimate 1641 367 495 128 = 3548416416 := by decide +kernel

private theorem cost_1641_367_block2 : P1_7_1_3.blockEstimate 1641 367 623 128 = 8773116876 := by decide +kernel

private theorem cost_1641_367_block3 : P1_7_1_3.blockEstimate 1641 367 751 128 = 14833626624 := by decide +kernel

private theorem cost_1641_367_block4 : P1_7_1_3.blockEstimate 1641 367 879 128 = 19660090880 := by decide +kernel

private theorem cost_1641_367_block5 : P1_7_1_3.blockEstimate 1641 367 1007 128 = 22943051264 := by decide +kernel

private theorem cost_1641_367_block6 : P1_7_1_3.blockEstimate 1641 367 1135 128 = 24682507776 := by decide +kernel

private theorem cost_1641_367_block7 : P1_7_1_3.blockEstimate 1641 367 1263 128 = 24878460416 := by decide +kernel

private theorem cost_1641_367_block8 : P1_7_1_3.blockEstimate 1641 367 1391 128 = 23530909184 := by decide +kernel

private theorem cost_1641_367_block9 : P1_7_1_3.blockEstimate 1641 367 1519 128 = 20639874174 := by decide +kernel

private theorem cost_1641_367_block10 : P1_7_1_3.blockEstimate 1641 367 1647 128 = 16418987136 := by decide +kernel

private theorem cost_1641_367_block11 : P1_7_1_3.blockEstimate 1641 367 1775 128 = 11803821879 := by decide +kernel

private theorem cost_1641_367_block12 : P1_7_1_3.blockEstimate 1641 367 1903 128 = 7438333033 := by decide +kernel

private theorem cost_1641_367_block13 : P1_7_1_3.blockEstimate 1641 367 2031 128 = 3767188000 := by decide +kernel

private theorem cost_1641_367_block14 : P1_7_1_3.blockEstimate 1641 367 2159 128 = 1225153056 := by decide +kernel

private theorem cost_1641_367_block15 : P1_7_1_3.blockEstimate 1641 367 2287 88 = 95592750 := by decide +kernel

private theorem cost_1641_367_join0_0 : P1_7_1_3.blockEstimate 1641 367 367 256 = 4101423936 :=
  @P1_7_1_3.block_append 1641 367 367 495 128 128 256 553007520 3548416416 4101423936 cost_1641_367_block0 cost_1641_367_block1 rfl rfl rfl

private theorem cost_1641_367_join0_2 : P1_7_1_3.blockEstimate 1641 367 623 256 = 23606743500 :=
  @P1_7_1_3.block_append 1641 367 623 751 128 128 256 8773116876 14833626624 23606743500 cost_1641_367_block2 cost_1641_367_block3 rfl rfl rfl

private theorem cost_1641_367_join0_4 : P1_7_1_3.blockEstimate 1641 367 879 256 = 42603142144 :=
  @P1_7_1_3.block_append 1641 367 879 1007 128 128 256 19660090880 22943051264 42603142144 cost_1641_367_block4 cost_1641_367_block5 rfl rfl rfl

private theorem cost_1641_367_join0_6 : P1_7_1_3.blockEstimate 1641 367 1135 256 = 49560968192 :=
  @P1_7_1_3.block_append 1641 367 1135 1263 128 128 256 24682507776 24878460416 49560968192 cost_1641_367_block6 cost_1641_367_block7 rfl rfl rfl

private theorem cost_1641_367_join0_8 : P1_7_1_3.blockEstimate 1641 367 1391 256 = 44170783358 :=
  @P1_7_1_3.block_append 1641 367 1391 1519 128 128 256 23530909184 20639874174 44170783358 cost_1641_367_block8 cost_1641_367_block9 rfl rfl rfl

private theorem cost_1641_367_join0_10 : P1_7_1_3.blockEstimate 1641 367 1647 256 = 28222809015 :=
  @P1_7_1_3.block_append 1641 367 1647 1775 128 128 256 16418987136 11803821879 28222809015 cost_1641_367_block10 cost_1641_367_block11 rfl rfl rfl

private theorem cost_1641_367_join0_12 : P1_7_1_3.blockEstimate 1641 367 1903 256 = 11205521033 :=
  @P1_7_1_3.block_append 1641 367 1903 2031 128 128 256 7438333033 3767188000 11205521033 cost_1641_367_block12 cost_1641_367_block13 rfl rfl rfl

private theorem cost_1641_367_join0_14 : P1_7_1_3.blockEstimate 1641 367 2159 216 = 1320745806 :=
  @P1_7_1_3.block_append 1641 367 2159 2287 128 88 216 1225153056 95592750 1320745806 cost_1641_367_block14 cost_1641_367_block15 rfl rfl rfl

private theorem cost_1641_367_join1_0 : P1_7_1_3.blockEstimate 1641 367 367 512 = 27708167436 :=
  @P1_7_1_3.block_append 1641 367 367 623 256 256 512 4101423936 23606743500 27708167436 cost_1641_367_join0_0 cost_1641_367_join0_2 rfl rfl rfl

private theorem cost_1641_367_join1_2 : P1_7_1_3.blockEstimate 1641 367 879 512 = 92164110336 :=
  @P1_7_1_3.block_append 1641 367 879 1135 256 256 512 42603142144 49560968192 92164110336 cost_1641_367_join0_4 cost_1641_367_join0_6 rfl rfl rfl

private theorem cost_1641_367_join1_4 : P1_7_1_3.blockEstimate 1641 367 1391 512 = 72393592373 :=
  @P1_7_1_3.block_append 1641 367 1391 1647 256 256 512 44170783358 28222809015 72393592373 cost_1641_367_join0_8 cost_1641_367_join0_10 rfl rfl rfl

private theorem cost_1641_367_join1_6 : P1_7_1_3.blockEstimate 1641 367 1903 472 = 12526266839 :=
  @P1_7_1_3.block_append 1641 367 1903 2159 256 216 472 11205521033 1320745806 12526266839 cost_1641_367_join0_12 cost_1641_367_join0_14 rfl rfl rfl

private theorem cost_1641_367_join2_0 : P1_7_1_3.blockEstimate 1641 367 367 1024 = 119872277772 :=
  @P1_7_1_3.block_append 1641 367 367 879 512 512 1024 27708167436 92164110336 119872277772 cost_1641_367_join1_0 cost_1641_367_join1_2 rfl rfl rfl

private theorem cost_1641_367_join2_2 : P1_7_1_3.blockEstimate 1641 367 1391 984 = 84919859212 :=
  @P1_7_1_3.block_append 1641 367 1391 1903 512 472 984 72393592373 12526266839 84919859212 cost_1641_367_join1_4 cost_1641_367_join1_6 rfl rfl rfl

private theorem cost_1641_367_join3_0 : P1_7_1_3.blockEstimate 1641 367 367 2008 = 204792136984 :=
  @P1_7_1_3.block_append 1641 367 367 1391 1024 984 2008 119872277772 84919859212 204792136984 cost_1641_367_join2_0 cost_1641_367_join2_2 rfl rfl rfl

private theorem cost_1641_367_total : P1_7_1_3.momentEstimate 1641 367 = 204792136984 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1641 + 367 = 2008 by decide]
  exact cost_1641_367_join3_0

theorem moment1641_367 : P1_7_1.groupedPoleMoment 1641 367 ≤ 204792136984 :=
  (P1_7_1_3.grouped_bound 1641 367).trans_eq cost_1641_367_total
private theorem cost_1642_351_block0 : P1_7_1_3.blockEstimate 1642 351 351 128 = 553365280 := by decide +kernel

private theorem cost_1642_351_block1 : P1_7_1_3.blockEstimate 1642 351 479 128 = 3550887712 := by decide +kernel

private theorem cost_1642_351_block2 : P1_7_1_3.blockEstimate 1642 351 607 128 = 8773248216 := by decide +kernel

private theorem cost_1642_351_block3 : P1_7_1_3.blockEstimate 1642 351 735 128 = 14631181312 := by decide +kernel

private theorem cost_1642_351_block4 : P1_7_1_3.blockEstimate 1642 351 863 128 = 19207429120 := by decide +kernel

private theorem cost_1642_351_block5 : P1_7_1_3.blockEstimate 1642 351 991 128 = 22307281920 := by decide +kernel

private theorem cost_1642_351_block6 : P1_7_1_3.blockEstimate 1642 351 1119 128 = 23930739712 := by decide +kernel

private theorem cost_1642_351_block7 : P1_7_1_3.blockEstimate 1642 351 1247 128 = 24077802496 := by decide +kernel

private theorem cost_1642_351_block8 : P1_7_1_3.blockEstimate 1642 351 1375 128 = 22748470272 := by decide +kernel

private theorem cost_1642_351_block9 : P1_7_1_3.blockEstimate 1642 351 1503 128 = 19942743040 := by decide +kernel

private theorem cost_1642_351_block10 : P1_7_1_3.blockEstimate 1642 351 1631 128 = 15805079216 := by decide +kernel

private theorem cost_1642_351_block11 : P1_7_1_3.blockEstimate 1642 351 1759 128 = 11240740260 := by decide +kernel

private theorem cost_1642_351_block12 : P1_7_1_3.blockEstimate 1642 351 1887 128 = 6957860219 := by decide +kernel

private theorem cost_1642_351_block13 : P1_7_1_3.blockEstimate 1642 351 2015 128 = 3406308080 := by decide +kernel

private theorem cost_1642_351_block14 : P1_7_1_3.blockEstimate 1642 351 2143 128 = 1016045296 := by decide +kernel

private theorem cost_1642_351_block15 : P1_7_1_3.blockEstimate 1642 351 2271 73 = 55406071 := by decide +kernel

private theorem cost_1642_351_join0_0 : P1_7_1_3.blockEstimate 1642 351 351 256 = 4104252992 :=
  @P1_7_1_3.block_append 1642 351 351 479 128 128 256 553365280 3550887712 4104252992 cost_1642_351_block0 cost_1642_351_block1 rfl rfl rfl

private theorem cost_1642_351_join0_2 : P1_7_1_3.blockEstimate 1642 351 607 256 = 23404429528 :=
  @P1_7_1_3.block_append 1642 351 607 735 128 128 256 8773248216 14631181312 23404429528 cost_1642_351_block2 cost_1642_351_block3 rfl rfl rfl

private theorem cost_1642_351_join0_4 : P1_7_1_3.blockEstimate 1642 351 863 256 = 41514711040 :=
  @P1_7_1_3.block_append 1642 351 863 991 128 128 256 19207429120 22307281920 41514711040 cost_1642_351_block4 cost_1642_351_block5 rfl rfl rfl

private theorem cost_1642_351_join0_6 : P1_7_1_3.blockEstimate 1642 351 1119 256 = 48008542208 :=
  @P1_7_1_3.block_append 1642 351 1119 1247 128 128 256 23930739712 24077802496 48008542208 cost_1642_351_block6 cost_1642_351_block7 rfl rfl rfl

private theorem cost_1642_351_join0_8 : P1_7_1_3.blockEstimate 1642 351 1375 256 = 42691213312 :=
  @P1_7_1_3.block_append 1642 351 1375 1503 128 128 256 22748470272 19942743040 42691213312 cost_1642_351_block8 cost_1642_351_block9 rfl rfl rfl

private theorem cost_1642_351_join0_10 : P1_7_1_3.blockEstimate 1642 351 1631 256 = 27045819476 :=
  @P1_7_1_3.block_append 1642 351 1631 1759 128 128 256 15805079216 11240740260 27045819476 cost_1642_351_block10 cost_1642_351_block11 rfl rfl rfl

private theorem cost_1642_351_join0_12 : P1_7_1_3.blockEstimate 1642 351 1887 256 = 10364168299 :=
  @P1_7_1_3.block_append 1642 351 1887 2015 128 128 256 6957860219 3406308080 10364168299 cost_1642_351_block12 cost_1642_351_block13 rfl rfl rfl

private theorem cost_1642_351_join0_14 : P1_7_1_3.blockEstimate 1642 351 2143 201 = 1071451367 :=
  @P1_7_1_3.block_append 1642 351 2143 2271 128 73 201 1016045296 55406071 1071451367 cost_1642_351_block14 cost_1642_351_block15 rfl rfl rfl

private theorem cost_1642_351_join1_0 : P1_7_1_3.blockEstimate 1642 351 351 512 = 27508682520 :=
  @P1_7_1_3.block_append 1642 351 351 607 256 256 512 4104252992 23404429528 27508682520 cost_1642_351_join0_0 cost_1642_351_join0_2 rfl rfl rfl

private theorem cost_1642_351_join1_2 : P1_7_1_3.blockEstimate 1642 351 863 512 = 89523253248 :=
  @P1_7_1_3.block_append 1642 351 863 1119 256 256 512 41514711040 48008542208 89523253248 cost_1642_351_join0_4 cost_1642_351_join0_6 rfl rfl rfl

private theorem cost_1642_351_join1_4 : P1_7_1_3.blockEstimate 1642 351 1375 512 = 69737032788 :=
  @P1_7_1_3.block_append 1642 351 1375 1631 256 256 512 42691213312 27045819476 69737032788 cost_1642_351_join0_8 cost_1642_351_join0_10 rfl rfl rfl

private theorem cost_1642_351_join1_6 : P1_7_1_3.blockEstimate 1642 351 1887 457 = 11435619666 :=
  @P1_7_1_3.block_append 1642 351 1887 2143 256 201 457 10364168299 1071451367 11435619666 cost_1642_351_join0_12 cost_1642_351_join0_14 rfl rfl rfl

private theorem cost_1642_351_join2_0 : P1_7_1_3.blockEstimate 1642 351 351 1024 = 117031935768 :=
  @P1_7_1_3.block_append 1642 351 351 863 512 512 1024 27508682520 89523253248 117031935768 cost_1642_351_join1_0 cost_1642_351_join1_2 rfl rfl rfl

private theorem cost_1642_351_join2_2 : P1_7_1_3.blockEstimate 1642 351 1375 969 = 81172652454 :=
  @P1_7_1_3.block_append 1642 351 1375 1887 512 457 969 69737032788 11435619666 81172652454 cost_1642_351_join1_4 cost_1642_351_join1_6 rfl rfl rfl

private theorem cost_1642_351_join3_0 : P1_7_1_3.blockEstimate 1642 351 351 1993 = 198204588222 :=
  @P1_7_1_3.block_append 1642 351 351 1375 1024 969 1993 117031935768 81172652454 198204588222 cost_1642_351_join2_0 cost_1642_351_join2_2 rfl rfl rfl

private theorem cost_1642_351_total : P1_7_1_3.momentEstimate 1642 351 = 198204588222 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1642 + 351 = 1993 by decide]
  exact cost_1642_351_join3_0

theorem moment1642_351 : P1_7_1.groupedPoleMoment 1642 351 ≤ 198204588222 :=
  (P1_7_1_3.grouped_bound 1642 351).trans_eq cost_1642_351_total
private theorem cost_1642_355_block0 : P1_7_1_3.blockEstimate 1642 355 355 128 = 553365280 := by decide +kernel

private theorem cost_1642_355_block1 : P1_7_1_3.blockEstimate 1642 355 483 128 = 3550887712 := by decide +kernel

private theorem cost_1642_355_block2 : P1_7_1_3.blockEstimate 1642 355 611 128 = 8775689503 := by decide +kernel

private theorem cost_1642_355_block3 : P1_7_1_3.blockEstimate 1642 355 739 128 = 14688582784 := by decide +kernel

private theorem cost_1642_355_block4 : P1_7_1_3.blockEstimate 1642 355 867 128 = 19328498816 := by decide +kernel

private theorem cost_1642_355_block5 : P1_7_1_3.blockEstimate 1642 355 995 128 = 22475242624 := by decide +kernel

private theorem cost_1642_355_block6 : P1_7_1_3.blockEstimate 1642 355 1123 128 = 24128814208 := by decide +kernel

private theorem cost_1642_355_block7 : P1_7_1_3.blockEstimate 1642 355 1251 128 = 24289213568 := by decide +kernel

private theorem cost_1642_355_block8 : P1_7_1_3.blockEstimate 1642 355 1379 128 = 22956440704 := by decide +kernel

private theorem cost_1642_355_block9 : P1_7_1_3.blockEstimate 1642 355 1507 128 = 20130495616 := by decide +kernel

private theorem cost_1642_355_block10 : P1_7_1_3.blockEstimate 1642 355 1635 128 = 15970551127 := by decide +kernel

private theorem cost_1642_355_block11 : P1_7_1_3.blockEstimate 1642 355 1763 128 = 11391810612 := by decide +kernel

private theorem cost_1642_355_block12 : P1_7_1_3.blockEstimate 1642 355 1891 128 = 7085971090 := by decide +kernel

private theorem cost_1642_355_block13 : P1_7_1_3.blockEstimate 1642 355 2019 128 = 3501636976 := by decide +kernel

private theorem cost_1642_355_block14 : P1_7_1_3.blockEstimate 1642 355 2147 128 = 1070088560 := by decide +kernel

private theorem cost_1642_355_block15 : P1_7_1_3.blockEstimate 1642 355 2275 77 = 64744750 := by decide +kernel

private theorem cost_1642_355_join0_0 : P1_7_1_3.blockEstimate 1642 355 355 256 = 4104252992 :=
  @P1_7_1_3.block_append 1642 355 355 483 128 128 256 553365280 3550887712 4104252992 cost_1642_355_block0 cost_1642_355_block1 rfl rfl rfl

private theorem cost_1642_355_join0_2 : P1_7_1_3.blockEstimate 1642 355 611 256 = 23464272287 :=
  @P1_7_1_3.block_append 1642 355 611 739 128 128 256 8775689503 14688582784 23464272287 cost_1642_355_block2 cost_1642_355_block3 rfl rfl rfl

private theorem cost_1642_355_join0_4 : P1_7_1_3.blockEstimate 1642 355 867 256 = 41803741440 :=
  @P1_7_1_3.block_append 1642 355 867 995 128 128 256 19328498816 22475242624 41803741440 cost_1642_355_block4 cost_1642_355_block5 rfl rfl rfl

private theorem cost_1642_355_join0_6 : P1_7_1_3.blockEstimate 1642 355 1123 256 = 48418027776 :=
  @P1_7_1_3.block_append 1642 355 1123 1251 128 128 256 24128814208 24289213568 48418027776 cost_1642_355_block6 cost_1642_355_block7 rfl rfl rfl

private theorem cost_1642_355_join0_8 : P1_7_1_3.blockEstimate 1642 355 1379 256 = 43086936320 :=
  @P1_7_1_3.block_append 1642 355 1379 1507 128 128 256 22956440704 20130495616 43086936320 cost_1642_355_block8 cost_1642_355_block9 rfl rfl rfl

private theorem cost_1642_355_join0_10 : P1_7_1_3.blockEstimate 1642 355 1635 256 = 27362361739 :=
  @P1_7_1_3.block_append 1642 355 1635 1763 128 128 256 15970551127 11391810612 27362361739 cost_1642_355_block10 cost_1642_355_block11 rfl rfl rfl

private theorem cost_1642_355_join0_12 : P1_7_1_3.blockEstimate 1642 355 1891 256 = 10587608066 :=
  @P1_7_1_3.block_append 1642 355 1891 2019 128 128 256 7085971090 3501636976 10587608066 cost_1642_355_block12 cost_1642_355_block13 rfl rfl rfl

private theorem cost_1642_355_join0_14 : P1_7_1_3.blockEstimate 1642 355 2147 205 = 1134833310 :=
  @P1_7_1_3.block_append 1642 355 2147 2275 128 77 205 1070088560 64744750 1134833310 cost_1642_355_block14 cost_1642_355_block15 rfl rfl rfl

private theorem cost_1642_355_join1_0 : P1_7_1_3.blockEstimate 1642 355 355 512 = 27568525279 :=
  @P1_7_1_3.block_append 1642 355 355 611 256 256 512 4104252992 23464272287 27568525279 cost_1642_355_join0_0 cost_1642_355_join0_2 rfl rfl rfl

private theorem cost_1642_355_join1_2 : P1_7_1_3.blockEstimate 1642 355 867 512 = 90221769216 :=
  @P1_7_1_3.block_append 1642 355 867 1123 256 256 512 41803741440 48418027776 90221769216 cost_1642_355_join0_4 cost_1642_355_join0_6 rfl rfl rfl

private theorem cost_1642_355_join1_4 : P1_7_1_3.blockEstimate 1642 355 1379 512 = 70449298059 :=
  @P1_7_1_3.block_append 1642 355 1379 1635 256 256 512 43086936320 27362361739 70449298059 cost_1642_355_join0_8 cost_1642_355_join0_10 rfl rfl rfl

private theorem cost_1642_355_join1_6 : P1_7_1_3.blockEstimate 1642 355 1891 461 = 11722441376 :=
  @P1_7_1_3.block_append 1642 355 1891 2147 256 205 461 10587608066 1134833310 11722441376 cost_1642_355_join0_12 cost_1642_355_join0_14 rfl rfl rfl

private theorem cost_1642_355_join2_0 : P1_7_1_3.blockEstimate 1642 355 355 1024 = 117790294495 :=
  @P1_7_1_3.block_append 1642 355 355 867 512 512 1024 27568525279 90221769216 117790294495 cost_1642_355_join1_0 cost_1642_355_join1_2 rfl rfl rfl

private theorem cost_1642_355_join2_2 : P1_7_1_3.blockEstimate 1642 355 1379 973 = 82171739435 :=
  @P1_7_1_3.block_append 1642 355 1379 1891 512 461 973 70449298059 11722441376 82171739435 cost_1642_355_join1_4 cost_1642_355_join1_6 rfl rfl rfl

private theorem cost_1642_355_join3_0 : P1_7_1_3.blockEstimate 1642 355 355 1997 = 199962033930 :=
  @P1_7_1_3.block_append 1642 355 355 1379 1024 973 1997 117790294495 82171739435 199962033930 cost_1642_355_join2_0 cost_1642_355_join2_2 rfl rfl rfl

private theorem cost_1642_355_total : P1_7_1_3.momentEstimate 1642 355 = 199962033930 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1642 + 355 = 1997 by decide]
  exact cost_1642_355_join3_0

theorem moment1642_355 : P1_7_1.groupedPoleMoment 1642 355 ≤ 199962033930 :=
  (P1_7_1_3.grouped_bound 1642 355).trans_eq cost_1642_355_total
private theorem cost_1642_357_block0 : P1_7_1_3.blockEstimate 1642 357 357 128 = 553365280 := by decide +kernel

private theorem cost_1642_357_block1 : P1_7_1_3.blockEstimate 1642 357 485 128 = 3550887712 := by decide +kernel

private theorem cost_1642_357_block2 : P1_7_1_3.blockEstimate 1642 357 613 128 = 8776683489 := by decide +kernel

private theorem cost_1642_357_block3 : P1_7_1_3.blockEstimate 1642 357 741 128 = 14716366144 := by decide +kernel

private theorem cost_1642_357_block4 : P1_7_1_3.blockEstimate 1642 357 869 128 = 19388214592 := by decide +kernel

private theorem cost_1642_357_block5 : P1_7_1_3.blockEstimate 1642 357 997 128 = 22558502208 := by decide +kernel

private theorem cost_1642_357_block6 : P1_7_1_3.blockEstimate 1642 357 1125 128 = 24227228992 := by decide +kernel

private theorem cost_1642_357_block7 : P1_7_1_3.blockEstimate 1642 357 1253 128 = 24394394944 := by decide +kernel

private theorem cost_1642_357_block8 : P1_7_1_3.blockEstimate 1642 357 1381 128 = 23060000064 := by decide +kernel

private theorem cost_1642_357_block9 : P1_7_1_3.blockEstimate 1642 357 1509 128 = 20224044352 := by decide +kernel

private theorem cost_1642_357_block10 : P1_7_1_3.blockEstimate 1642 357 1637 128 = 16053403770 := by decide +kernel

private theorem cost_1642_357_block11 : P1_7_1_3.blockEstimate 1642 357 1765 128 = 11467589008 := by decide +kernel

private theorem cost_1642_357_block12 : P1_7_1_3.blockEstimate 1642 357 1893 128 = 7150368996 := by decide +kernel

private theorem cost_1642_357_block13 : P1_7_1_3.blockEstimate 1642 357 2021 128 = 3549738208 := by decide +kernel

private theorem cost_1642_357_block14 : P1_7_1_3.blockEstimate 1642 357 2149 128 = 1097639136 := by decide +kernel

private theorem cost_1642_357_block15 : P1_7_1_3.blockEstimate 1642 357 2277 79 = 69780780 := by decide +kernel

private theorem cost_1642_357_join0_0 : P1_7_1_3.blockEstimate 1642 357 357 256 = 4104252992 :=
  @P1_7_1_3.block_append 1642 357 357 485 128 128 256 553365280 3550887712 4104252992 cost_1642_357_block0 cost_1642_357_block1 rfl rfl rfl

private theorem cost_1642_357_join0_2 : P1_7_1_3.blockEstimate 1642 357 613 256 = 23493049633 :=
  @P1_7_1_3.block_append 1642 357 613 741 128 128 256 8776683489 14716366144 23493049633 cost_1642_357_block2 cost_1642_357_block3 rfl rfl rfl

private theorem cost_1642_357_join0_4 : P1_7_1_3.blockEstimate 1642 357 869 256 = 41946716800 :=
  @P1_7_1_3.block_append 1642 357 869 997 128 128 256 19388214592 22558502208 41946716800 cost_1642_357_block4 cost_1642_357_block5 rfl rfl rfl

private theorem cost_1642_357_join0_6 : P1_7_1_3.blockEstimate 1642 357 1125 256 = 48621623936 :=
  @P1_7_1_3.block_append 1642 357 1125 1253 128 128 256 24227228992 24394394944 48621623936 cost_1642_357_block6 cost_1642_357_block7 rfl rfl rfl

private theorem cost_1642_357_join0_8 : P1_7_1_3.blockEstimate 1642 357 1381 256 = 43284044416 :=
  @P1_7_1_3.block_append 1642 357 1381 1509 128 128 256 23060000064 20224044352 43284044416 cost_1642_357_block8 cost_1642_357_block9 rfl rfl rfl

private theorem cost_1642_357_join0_10 : P1_7_1_3.blockEstimate 1642 357 1637 256 = 27520992778 :=
  @P1_7_1_3.block_append 1642 357 1637 1765 128 128 256 16053403770 11467589008 27520992778 cost_1642_357_block10 cost_1642_357_block11 rfl rfl rfl

private theorem cost_1642_357_join0_12 : P1_7_1_3.blockEstimate 1642 357 1893 256 = 10700107204 :=
  @P1_7_1_3.block_append 1642 357 1893 2021 128 128 256 7150368996 3549738208 10700107204 cost_1642_357_block12 cost_1642_357_block13 rfl rfl rfl

private theorem cost_1642_357_join0_14 : P1_7_1_3.blockEstimate 1642 357 2149 207 = 1167419916 :=
  @P1_7_1_3.block_append 1642 357 2149 2277 128 79 207 1097639136 69780780 1167419916 cost_1642_357_block14 cost_1642_357_block15 rfl rfl rfl

private theorem cost_1642_357_join1_0 : P1_7_1_3.blockEstimate 1642 357 357 512 = 27597302625 :=
  @P1_7_1_3.block_append 1642 357 357 613 256 256 512 4104252992 23493049633 27597302625 cost_1642_357_join0_0 cost_1642_357_join0_2 rfl rfl rfl

private theorem cost_1642_357_join1_2 : P1_7_1_3.blockEstimate 1642 357 869 512 = 90568340736 :=
  @P1_7_1_3.block_append 1642 357 869 1125 256 256 512 41946716800 48621623936 90568340736 cost_1642_357_join0_4 cost_1642_357_join0_6 rfl rfl rfl

private theorem cost_1642_357_join1_4 : P1_7_1_3.blockEstimate 1642 357 1381 512 = 70805037194 :=
  @P1_7_1_3.block_append 1642 357 1381 1637 256 256 512 43284044416 27520992778 70805037194 cost_1642_357_join0_8 cost_1642_357_join0_10 rfl rfl rfl

private theorem cost_1642_357_join1_6 : P1_7_1_3.blockEstimate 1642 357 1893 463 = 11867527120 :=
  @P1_7_1_3.block_append 1642 357 1893 2149 256 207 463 10700107204 1167419916 11867527120 cost_1642_357_join0_12 cost_1642_357_join0_14 rfl rfl rfl

private theorem cost_1642_357_join2_0 : P1_7_1_3.blockEstimate 1642 357 357 1024 = 118165643361 :=
  @P1_7_1_3.block_append 1642 357 357 869 512 512 1024 27597302625 90568340736 118165643361 cost_1642_357_join1_0 cost_1642_357_join1_2 rfl rfl rfl

private theorem cost_1642_357_join2_2 : P1_7_1_3.blockEstimate 1642 357 1381 975 = 82672564314 :=
  @P1_7_1_3.block_append 1642 357 1381 1893 512 463 975 70805037194 11867527120 82672564314 cost_1642_357_join1_4 cost_1642_357_join1_6 rfl rfl rfl

private theorem cost_1642_357_join3_0 : P1_7_1_3.blockEstimate 1642 357 357 1999 = 200838207675 :=
  @P1_7_1_3.block_append 1642 357 357 1381 1024 975 1999 118165643361 82672564314 200838207675 cost_1642_357_join2_0 cost_1642_357_join2_2 rfl rfl rfl

private theorem cost_1642_357_total : P1_7_1_3.momentEstimate 1642 357 = 200838207675 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1642 + 357 = 1999 by decide]
  exact cost_1642_357_join3_0

theorem moment1642_357 : P1_7_1.groupedPoleMoment 1642 357 ≤ 200838207675 :=
  (P1_7_1_3.grouped_bound 1642 357).trans_eq cost_1642_357_total
private theorem cost_1642_363_block0 : P1_7_1_3.blockEstimate 1642 363 363 128 = 553365280 := by decide +kernel

private theorem cost_1642_363_block1 : P1_7_1_3.blockEstimate 1642 363 491 128 = 3550887712 := by decide +kernel

private theorem cost_1642_363_block2 : P1_7_1_3.blockEstimate 1642 363 619 128 = 8778882273 := by decide +kernel

private theorem cost_1642_363_block3 : P1_7_1_3.blockEstimate 1642 363 747 128 = 14796046720 := by decide +kernel

private theorem cost_1642_363_block4 : P1_7_1_3.blockEstimate 1642 363 875 128 = 19564085632 := by decide +kernel

private theorem cost_1642_363_block5 : P1_7_1_3.blockEstimate 1642 363 1003 128 = 22805397888 := by decide +kernel

private theorem cost_1642_363_block6 : P1_7_1_3.blockEstimate 1642 363 1131 128 = 24519983488 := by decide +kernel

private theorem cost_1642_363_block7 : P1_7_1_3.blockEstimate 1642 363 1259 128 = 24707842432 := by decide +kernel

private theorem cost_1642_363_block8 : P1_7_1_3.blockEstimate 1642 363 1387 128 = 23368974720 := by decide +kernel

private theorem cost_1642_363_block9 : P1_7_1_3.blockEstimate 1642 363 1515 128 = 20503380352 := by decide +kernel

private theorem cost_1642_363_block10 : P1_7_1_3.blockEstimate 1642 363 1643 128 = 16302463252 := by decide +kernel

private theorem cost_1642_363_block11 : P1_7_1_3.blockEstimate 1642 363 1771 128 = 11695885351 := by decide +kernel

private theorem cost_1642_363_block12 : P1_7_1_3.blockEstimate 1642 363 1899 128 = 7344921389 := by decide +kernel

private theorem cost_1642_363_block13 : P1_7_1_3.blockEstimate 1642 363 2027 128 = 3695777456 := by decide +kernel

private theorem cost_1642_363_block14 : P1_7_1_3.blockEstimate 1642 363 2155 128 = 1182395056 := by decide +kernel

private theorem cost_1642_363_block15 : P1_7_1_3.blockEstimate 1642 363 2283 85 = 86427275 := by decide +kernel

private theorem cost_1642_363_join0_0 : P1_7_1_3.blockEstimate 1642 363 363 256 = 4104252992 :=
  @P1_7_1_3.block_append 1642 363 363 491 128 128 256 553365280 3550887712 4104252992 cost_1642_363_block0 cost_1642_363_block1 rfl rfl rfl

private theorem cost_1642_363_join0_2 : P1_7_1_3.blockEstimate 1642 363 619 256 = 23574928993 :=
  @P1_7_1_3.block_append 1642 363 619 747 128 128 256 8778882273 14796046720 23574928993 cost_1642_363_block2 cost_1642_363_block3 rfl rfl rfl

private theorem cost_1642_363_join0_4 : P1_7_1_3.blockEstimate 1642 363 875 256 = 42369483520 :=
  @P1_7_1_3.block_append 1642 363 875 1003 128 128 256 19564085632 22805397888 42369483520 cost_1642_363_block4 cost_1642_363_block5 rfl rfl rfl

private theorem cost_1642_363_join0_6 : P1_7_1_3.blockEstimate 1642 363 1131 256 = 49227825920 :=
  @P1_7_1_3.block_append 1642 363 1131 1259 128 128 256 24519983488 24707842432 49227825920 cost_1642_363_block6 cost_1642_363_block7 rfl rfl rfl

private theorem cost_1642_363_join0_8 : P1_7_1_3.blockEstimate 1642 363 1387 256 = 43872355072 :=
  @P1_7_1_3.block_append 1642 363 1387 1515 128 128 256 23368974720 20503380352 43872355072 cost_1642_363_block8 cost_1642_363_block9 rfl rfl rfl

private theorem cost_1642_363_join0_10 : P1_7_1_3.blockEstimate 1642 363 1643 256 = 27998348603 :=
  @P1_7_1_3.block_append 1642 363 1643 1771 128 128 256 16302463252 11695885351 27998348603 cost_1642_363_block10 cost_1642_363_block11 rfl rfl rfl

private theorem cost_1642_363_join0_12 : P1_7_1_3.blockEstimate 1642 363 1899 256 = 11040698845 :=
  @P1_7_1_3.block_append 1642 363 1899 2027 128 128 256 7344921389 3695777456 11040698845 cost_1642_363_block12 cost_1642_363_block13 rfl rfl rfl

private theorem cost_1642_363_join0_14 : P1_7_1_3.blockEstimate 1642 363 2155 213 = 1268822331 :=
  @P1_7_1_3.block_append 1642 363 2155 2283 128 85 213 1182395056 86427275 1268822331 cost_1642_363_block14 cost_1642_363_block15 rfl rfl rfl

private theorem cost_1642_363_join1_0 : P1_7_1_3.blockEstimate 1642 363 363 512 = 27679181985 :=
  @P1_7_1_3.block_append 1642 363 363 619 256 256 512 4104252992 23574928993 27679181985 cost_1642_363_join0_0 cost_1642_363_join0_2 rfl rfl rfl

private theorem cost_1642_363_join1_2 : P1_7_1_3.blockEstimate 1642 363 875 512 = 91597309440 :=
  @P1_7_1_3.block_append 1642 363 875 1131 256 256 512 42369483520 49227825920 91597309440 cost_1642_363_join0_4 cost_1642_363_join0_6 rfl rfl rfl

private theorem cost_1642_363_join1_4 : P1_7_1_3.blockEstimate 1642 363 1387 512 = 71870703675 :=
  @P1_7_1_3.block_append 1642 363 1387 1643 256 256 512 43872355072 27998348603 71870703675 cost_1642_363_join0_8 cost_1642_363_join0_10 rfl rfl rfl

private theorem cost_1642_363_join1_6 : P1_7_1_3.blockEstimate 1642 363 1899 469 = 12309521176 :=
  @P1_7_1_3.block_append 1642 363 1899 2155 256 213 469 11040698845 1268822331 12309521176 cost_1642_363_join0_12 cost_1642_363_join0_14 rfl rfl rfl

private theorem cost_1642_363_join2_0 : P1_7_1_3.blockEstimate 1642 363 363 1024 = 119276491425 :=
  @P1_7_1_3.block_append 1642 363 363 875 512 512 1024 27679181985 91597309440 119276491425 cost_1642_363_join1_0 cost_1642_363_join1_2 rfl rfl rfl

private theorem cost_1642_363_join2_2 : P1_7_1_3.blockEstimate 1642 363 1387 981 = 84180224851 :=
  @P1_7_1_3.block_append 1642 363 1387 1899 512 469 981 71870703675 12309521176 84180224851 cost_1642_363_join1_4 cost_1642_363_join1_6 rfl rfl rfl

private theorem cost_1642_363_join3_0 : P1_7_1_3.blockEstimate 1642 363 363 2005 = 203456716276 :=
  @P1_7_1_3.block_append 1642 363 363 1387 1024 981 2005 119276491425 84180224851 203456716276 cost_1642_363_join2_0 cost_1642_363_join2_2 rfl rfl rfl

private theorem cost_1642_363_total : P1_7_1_3.momentEstimate 1642 363 = 203456716276 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1642 + 363 = 2005 by decide]
  exact cost_1642_363_join3_0

theorem moment1642_363 : P1_7_1.groupedPoleMoment 1642 363 ≤ 203456716276 :=
  (P1_7_1_3.grouped_bound 1642 363).trans_eq cost_1642_363_total

end Research6966.HelperRescueCatalogue

end Merged6967_Near6967RescueMoment14

section Merged6967_Near6967RescueMoment15
set_option Elab.async false


set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem cost_1694_364_block0 : P1_7_1_3.blockEstimate 1694 364 364 128 = 571968800 := by decide +kernel

private theorem cost_1694_364_block1 : P1_7_1_3.blockEstimate 1694 364 492 128 = 3679395104 := by decide +kernel

private theorem cost_1694_364_block2 : P1_7_1_3.blockEstimate 1694 364 620 128 = 9126542001 := by decide +kernel

private theorem cost_1694_364_block3 : P1_7_1_3.blockEstimate 1694 364 748 128 = 15456237440 := by decide +kernel

private theorem cost_1694_364_block4 : P1_7_1_3.blockEstimate 1694 364 876 128 = 20551333760 := by decide +kernel

private theorem cost_1694_364_block5 : P1_7_1_3.blockEstimate 1694 364 1004 128 = 24115509120 := by decide +kernel

private theorem cost_1694_364_block6 : P1_7_1_3.blockEstimate 1694 364 1132 128 = 26148763520 := by decide +kernel

private theorem cost_1694_364_block7 : P1_7_1_3.blockEstimate 1694 364 1260 128 = 26651096960 := by decide +kernel

private theorem cost_1694_364_block8 : P1_7_1_3.blockEstimate 1694 364 1388 128 = 25622509440 := by decide +kernel

private theorem cost_1694_364_block9 : P1_7_1_3.blockEstimate 1694 364 1516 128 = 23063000960 := by decide +kernel

private theorem cost_1694_364_block10 : P1_7_1_3.blockEstimate 1694 364 1644 128 = 19014987166 := by decide +kernel

private theorem cost_1694_364_block11 : P1_7_1_3.blockEstimate 1694 364 1772 128 = 14181292458 := by decide +kernel

private theorem cost_1694_364_block12 : P1_7_1_3.blockEstimate 1694 364 1900 128 = 9439717304 := by decide +kernel

private theorem cost_1694_364_block13 : P1_7_1_3.blockEstimate 1694 364 2028 128 = 5278029594 := by decide +kernel

private theorem cost_1694_364_block14 : P1_7_1_3.blockEstimate 1694 364 2156 128 = 2135519856 := by decide +kernel

private theorem cost_1694_364_block15 : P1_7_1_3.blockEstimate 1694 364 2284 128 = 368498288 := by decide +kernel

private theorem cost_1694_364_block16 : P1_7_1_3.blockEstimate 1694 364 2412 10 = 211242 := by decide +kernel

private theorem cost_1694_364_join0_0 : P1_7_1_3.blockEstimate 1694 364 364 256 = 4251363904 :=
  @P1_7_1_3.block_append 1694 364 364 492 128 128 256 571968800 3679395104 4251363904 cost_1694_364_block0 cost_1694_364_block1 rfl rfl rfl

private theorem cost_1694_364_join0_2 : P1_7_1_3.blockEstimate 1694 364 620 256 = 24582779441 :=
  @P1_7_1_3.block_append 1694 364 620 748 128 128 256 9126542001 15456237440 24582779441 cost_1694_364_block2 cost_1694_364_block3 rfl rfl rfl

private theorem cost_1694_364_join0_4 : P1_7_1_3.blockEstimate 1694 364 876 256 = 44666842880 :=
  @P1_7_1_3.block_append 1694 364 876 1004 128 128 256 20551333760 24115509120 44666842880 cost_1694_364_block4 cost_1694_364_block5 rfl rfl rfl

private theorem cost_1694_364_join0_6 : P1_7_1_3.blockEstimate 1694 364 1132 256 = 52799860480 :=
  @P1_7_1_3.block_append 1694 364 1132 1260 128 128 256 26148763520 26651096960 52799860480 cost_1694_364_block6 cost_1694_364_block7 rfl rfl rfl

private theorem cost_1694_364_join0_8 : P1_7_1_3.blockEstimate 1694 364 1388 256 = 48685510400 :=
  @P1_7_1_3.block_append 1694 364 1388 1516 128 128 256 25622509440 23063000960 48685510400 cost_1694_364_block8 cost_1694_364_block9 rfl rfl rfl

private theorem cost_1694_364_join0_10 : P1_7_1_3.blockEstimate 1694 364 1644 256 = 33196279624 :=
  @P1_7_1_3.block_append 1694 364 1644 1772 128 128 256 19014987166 14181292458 33196279624 cost_1694_364_block10 cost_1694_364_block11 rfl rfl rfl

private theorem cost_1694_364_join0_12 : P1_7_1_3.blockEstimate 1694 364 1900 256 = 14717746898 :=
  @P1_7_1_3.block_append 1694 364 1900 2028 128 128 256 9439717304 5278029594 14717746898 cost_1694_364_block12 cost_1694_364_block13 rfl rfl rfl

private theorem cost_1694_364_join0_14 : P1_7_1_3.blockEstimate 1694 364 2156 256 = 2504018144 :=
  @P1_7_1_3.block_append 1694 364 2156 2284 128 128 256 2135519856 368498288 2504018144 cost_1694_364_block14 cost_1694_364_block15 rfl rfl rfl

private theorem cost_1694_364_join1_0 : P1_7_1_3.blockEstimate 1694 364 364 512 = 28834143345 :=
  @P1_7_1_3.block_append 1694 364 364 620 256 256 512 4251363904 24582779441 28834143345 cost_1694_364_join0_0 cost_1694_364_join0_2 rfl rfl rfl

private theorem cost_1694_364_join1_2 : P1_7_1_3.blockEstimate 1694 364 876 512 = 97466703360 :=
  @P1_7_1_3.block_append 1694 364 876 1132 256 256 512 44666842880 52799860480 97466703360 cost_1694_364_join0_4 cost_1694_364_join0_6 rfl rfl rfl

private theorem cost_1694_364_join1_4 : P1_7_1_3.blockEstimate 1694 364 1388 512 = 81881790024 :=
  @P1_7_1_3.block_append 1694 364 1388 1644 256 256 512 48685510400 33196279624 81881790024 cost_1694_364_join0_8 cost_1694_364_join0_10 rfl rfl rfl

private theorem cost_1694_364_join1_6 : P1_7_1_3.blockEstimate 1694 364 1900 512 = 17221765042 :=
  @P1_7_1_3.block_append 1694 364 1900 2156 256 256 512 14717746898 2504018144 17221765042 cost_1694_364_join0_12 cost_1694_364_join0_14 rfl rfl rfl

private theorem cost_1694_364_join2_0 : P1_7_1_3.blockEstimate 1694 364 364 1024 = 126300846705 :=
  @P1_7_1_3.block_append 1694 364 364 876 512 512 1024 28834143345 97466703360 126300846705 cost_1694_364_join1_0 cost_1694_364_join1_2 rfl rfl rfl

private theorem cost_1694_364_join2_2 : P1_7_1_3.blockEstimate 1694 364 1388 1024 = 99103555066 :=
  @P1_7_1_3.block_append 1694 364 1388 1900 512 512 1024 81881790024 17221765042 99103555066 cost_1694_364_join1_4 cost_1694_364_join1_6 rfl rfl rfl

private theorem cost_1694_364_join3_0 : P1_7_1_3.blockEstimate 1694 364 364 2048 = 225404401771 :=
  @P1_7_1_3.block_append 1694 364 364 1388 1024 1024 2048 126300846705 99103555066 225404401771 cost_1694_364_join2_0 cost_1694_364_join2_2 rfl rfl rfl

private theorem cost_1694_364_join4_0 : P1_7_1_3.blockEstimate 1694 364 364 2058 = 225404613013 :=
  @P1_7_1_3.block_append 1694 364 364 2412 2048 10 2058 225404401771 211242 225404613013 cost_1694_364_join3_0 cost_1694_364_block16 rfl rfl rfl

private theorem cost_1694_364_total : P1_7_1_3.momentEstimate 1694 364 = 225404613013 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1694 + 364 = 2058 by decide]
  exact cost_1694_364_join4_0

theorem moment1694_364 : P1_7_1.groupedPoleMoment 1694 364 ≤ 225404613013 :=
  (P1_7_1_3.grouped_bound 1694 364).trans_eq cost_1694_364_total
private theorem cost_1695_369_block0 : P1_7_1_3.blockEstimate 1695 369 369 128 = 572326560 := by decide +kernel

private theorem cost_1695_369_block1 : P1_7_1_3.blockEstimate 1695 369 497 128 = 3681866400 := by decide +kernel

private theorem cost_1695_369_block2 : P1_7_1_3.blockEstimate 1695 369 625 128 = 9134237060 := by decide +kernel

private theorem cost_1695_369_block3 : P1_7_1_3.blockEstimate 1695 369 753 128 = 15532884160 := by decide +kernel

private theorem cost_1695_369_block4 : P1_7_1_3.blockEstimate 1695 369 881 128 = 20718993600 := by decide +kernel

private theorem cost_1695_369_block5 : P1_7_1_3.blockEstimate 1695 369 1009 128 = 24353210560 := by decide +kernel

private theorem cost_1695_369_block6 : P1_7_1_3.blockEstimate 1695 369 1137 128 = 26435535040 := by decide +kernel

private theorem cost_1695_369_block7 : P1_7_1_3.blockEstimate 1695 369 1265 128 = 26965967040 := by decide +kernel

private theorem cost_1695_369_block8 : P1_7_1_3.blockEstimate 1695 369 1393 128 = 25944506560 := by decide +kernel

private theorem cost_1695_369_block9 : P1_7_1_3.blockEstimate 1695 369 1521 128 = 23371153600 := by decide +kernel

private theorem cost_1695_369_block10 : P1_7_1_3.blockEstimate 1695 369 1649 128 = 19294929361 := by decide +kernel

private theorem cost_1695_369_block11 : P1_7_1_3.blockEstimate 1695 369 1777 128 = 14440259047 := by decide +kernel

private theorem cost_1695_369_block12 : P1_7_1_3.blockEstimate 1695 369 1905 128 = 9666514224 := by decide +kernel

private theorem cost_1695_369_block13 : P1_7_1_3.blockEstimate 1695 369 2033 128 = 5458494791 := by decide +kernel

private theorem cost_1695_369_block14 : P1_7_1_3.blockEstimate 1695 369 2161 128 = 2255560672 := by decide +kernel

private theorem cost_1695_369_block15 : P1_7_1_3.blockEstimate 1695 369 2289 128 = 417148896 := by decide +kernel

private theorem cost_1695_369_block16 : P1_7_1_3.blockEstimate 1695 369 2417 16 = 749532 := by decide +kernel

private theorem cost_1695_369_join0_0 : P1_7_1_3.blockEstimate 1695 369 369 256 = 4254192960 :=
  @P1_7_1_3.block_append 1695 369 369 497 128 128 256 572326560 3681866400 4254192960 cost_1695_369_block0 cost_1695_369_block1 rfl rfl rfl

private theorem cost_1695_369_join0_2 : P1_7_1_3.blockEstimate 1695 369 625 256 = 24667121220 :=
  @P1_7_1_3.block_append 1695 369 625 753 128 128 256 9134237060 15532884160 24667121220 cost_1695_369_block2 cost_1695_369_block3 rfl rfl rfl

private theorem cost_1695_369_join0_4 : P1_7_1_3.blockEstimate 1695 369 881 256 = 45072204160 :=
  @P1_7_1_3.block_append 1695 369 881 1009 128 128 256 20718993600 24353210560 45072204160 cost_1695_369_block4 cost_1695_369_block5 rfl rfl rfl

private theorem cost_1695_369_join0_6 : P1_7_1_3.blockEstimate 1695 369 1137 256 = 53401502080 :=
  @P1_7_1_3.block_append 1695 369 1137 1265 128 128 256 26435535040 26965967040 53401502080 cost_1695_369_block6 cost_1695_369_block7 rfl rfl rfl

private theorem cost_1695_369_join0_8 : P1_7_1_3.blockEstimate 1695 369 1393 256 = 49315660160 :=
  @P1_7_1_3.block_append 1695 369 1393 1521 128 128 256 25944506560 23371153600 49315660160 cost_1695_369_block8 cost_1695_369_block9 rfl rfl rfl

private theorem cost_1695_369_join0_10 : P1_7_1_3.blockEstimate 1695 369 1649 256 = 33735188408 :=
  @P1_7_1_3.block_append 1695 369 1649 1777 128 128 256 19294929361 14440259047 33735188408 cost_1695_369_block10 cost_1695_369_block11 rfl rfl rfl

private theorem cost_1695_369_join0_12 : P1_7_1_3.blockEstimate 1695 369 1905 256 = 15125009015 :=
  @P1_7_1_3.block_append 1695 369 1905 2033 128 128 256 9666514224 5458494791 15125009015 cost_1695_369_block12 cost_1695_369_block13 rfl rfl rfl

private theorem cost_1695_369_join0_14 : P1_7_1_3.blockEstimate 1695 369 2161 256 = 2672709568 :=
  @P1_7_1_3.block_append 1695 369 2161 2289 128 128 256 2255560672 417148896 2672709568 cost_1695_369_block14 cost_1695_369_block15 rfl rfl rfl

private theorem cost_1695_369_join1_0 : P1_7_1_3.blockEstimate 1695 369 369 512 = 28921314180 :=
  @P1_7_1_3.block_append 1695 369 369 625 256 256 512 4254192960 24667121220 28921314180 cost_1695_369_join0_0 cost_1695_369_join0_2 rfl rfl rfl

private theorem cost_1695_369_join1_2 : P1_7_1_3.blockEstimate 1695 369 881 512 = 98473706240 :=
  @P1_7_1_3.block_append 1695 369 881 1137 256 256 512 45072204160 53401502080 98473706240 cost_1695_369_join0_4 cost_1695_369_join0_6 rfl rfl rfl

private theorem cost_1695_369_join1_4 : P1_7_1_3.blockEstimate 1695 369 1393 512 = 83050848568 :=
  @P1_7_1_3.block_append 1695 369 1393 1649 256 256 512 49315660160 33735188408 83050848568 cost_1695_369_join0_8 cost_1695_369_join0_10 rfl rfl rfl

private theorem cost_1695_369_join1_6 : P1_7_1_3.blockEstimate 1695 369 1905 512 = 17797718583 :=
  @P1_7_1_3.block_append 1695 369 1905 2161 256 256 512 15125009015 2672709568 17797718583 cost_1695_369_join0_12 cost_1695_369_join0_14 rfl rfl rfl

private theorem cost_1695_369_join2_0 : P1_7_1_3.blockEstimate 1695 369 369 1024 = 127395020420 :=
  @P1_7_1_3.block_append 1695 369 369 881 512 512 1024 28921314180 98473706240 127395020420 cost_1695_369_join1_0 cost_1695_369_join1_2 rfl rfl rfl

private theorem cost_1695_369_join2_2 : P1_7_1_3.blockEstimate 1695 369 1393 1024 = 100848567151 :=
  @P1_7_1_3.block_append 1695 369 1393 1905 512 512 1024 83050848568 17797718583 100848567151 cost_1695_369_join1_4 cost_1695_369_join1_6 rfl rfl rfl

private theorem cost_1695_369_join3_0 : P1_7_1_3.blockEstimate 1695 369 369 2048 = 228243587571 :=
  @P1_7_1_3.block_append 1695 369 369 1393 1024 1024 2048 127395020420 100848567151 228243587571 cost_1695_369_join2_0 cost_1695_369_join2_2 rfl rfl rfl

private theorem cost_1695_369_join4_0 : P1_7_1_3.blockEstimate 1695 369 369 2064 = 228244337103 :=
  @P1_7_1_3.block_append 1695 369 369 2417 2048 16 2064 228243587571 749532 228244337103 cost_1695_369_join3_0 cost_1695_369_block16 rfl rfl rfl

private theorem cost_1695_369_total : P1_7_1_3.momentEstimate 1695 369 = 228244337103 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1695 + 369 = 2064 by decide]
  exact cost_1695_369_join4_0

theorem moment1695_369 : P1_7_1.groupedPoleMoment 1695 369 ≤ 228244337103 :=
  (P1_7_1_3.grouped_bound 1695 369).trans_eq cost_1695_369_total
private theorem cost_1695_376_block0 : P1_7_1_3.blockEstimate 1695 376 376 128 = 572326560 := by decide +kernel

private theorem cost_1695_376_block1 : P1_7_1_3.blockEstimate 1695 376 504 128 = 3681866400 := by decide +kernel

private theorem cost_1695_376_block2 : P1_7_1_3.blockEstimate 1695 376 632 128 = 9134863266 := by decide +kernel

private theorem cost_1695_376_block3 : P1_7_1_3.blockEstimate 1695 376 760 128 = 15616051776 := by decide +kernel

private theorem cost_1695_376_block4 : P1_7_1_3.blockEstimate 1695 376 888 128 = 20921895488 := by decide +kernel

private theorem cost_1695_376_block5 : P1_7_1_3.blockEstimate 1695 376 1016 128 = 24646486592 := by decide +kernel

private theorem cost_1695_376_block6 : P1_7_1_3.blockEstimate 1695 376 1144 128 = 26789825088 := by decide +kernel

private theorem cost_1695_376_block7 : P1_7_1_3.blockEstimate 1695 376 1272 128 = 27351910976 := by decide +kernel

private theorem cost_1695_376_block8 : P1_7_1_3.blockEstimate 1695 376 1400 128 = 26332744256 := by decide +kernel

private theorem cost_1695_376_block9 : P1_7_1_3.blockEstimate 1695 376 1528 128 = 23732324928 := by decide +kernel

private theorem cost_1695_376_block10 : P1_7_1_3.blockEstimate 1695 376 1656 128 = 19612865054 := by decide +kernel

private theorem cost_1695_376_block11 : P1_7_1_3.blockEstimate 1695 376 1784 128 = 14735329504 := by decide +kernel

private theorem cost_1695_376_block12 : P1_7_1_3.blockEstimate 1695 376 1912 128 = 9927164546 := by decide +kernel

private theorem cost_1695_376_block13 : P1_7_1_3.blockEstimate 1695 376 2040 128 = 5668150749 := by decide +kernel

private theorem cost_1695_376_block14 : P1_7_1_3.blockEstimate 1695 376 2168 128 = 2397805440 := by decide +kernel

private theorem cost_1695_376_block15 : P1_7_1_3.blockEstimate 1695 376 2296 128 = 478137216 := by decide +kernel

private theorem cost_1695_376_block16 : P1_7_1_3.blockEstimate 1695 376 2424 23 = 2058904 := by decide +kernel

private theorem cost_1695_376_join0_0 : P1_7_1_3.blockEstimate 1695 376 376 256 = 4254192960 :=
  @P1_7_1_3.block_append 1695 376 376 504 128 128 256 572326560 3681866400 4254192960 cost_1695_376_block0 cost_1695_376_block1 rfl rfl rfl

private theorem cost_1695_376_join0_2 : P1_7_1_3.blockEstimate 1695 376 632 256 = 24750915042 :=
  @P1_7_1_3.block_append 1695 376 632 760 128 128 256 9134863266 15616051776 24750915042 cost_1695_376_block2 cost_1695_376_block3 rfl rfl rfl

private theorem cost_1695_376_join0_4 : P1_7_1_3.blockEstimate 1695 376 888 256 = 45568382080 :=
  @P1_7_1_3.block_append 1695 376 888 1016 128 128 256 20921895488 24646486592 45568382080 cost_1695_376_block4 cost_1695_376_block5 rfl rfl rfl

private theorem cost_1695_376_join0_6 : P1_7_1_3.blockEstimate 1695 376 1144 256 = 54141736064 :=
  @P1_7_1_3.block_append 1695 376 1144 1272 128 128 256 26789825088 27351910976 54141736064 cost_1695_376_block6 cost_1695_376_block7 rfl rfl rfl

private theorem cost_1695_376_join0_8 : P1_7_1_3.blockEstimate 1695 376 1400 256 = 50065069184 :=
  @P1_7_1_3.block_append 1695 376 1400 1528 128 128 256 26332744256 23732324928 50065069184 cost_1695_376_block8 cost_1695_376_block9 rfl rfl rfl

private theorem cost_1695_376_join0_10 : P1_7_1_3.blockEstimate 1695 376 1656 256 = 34348194558 :=
  @P1_7_1_3.block_append 1695 376 1656 1784 128 128 256 19612865054 14735329504 34348194558 cost_1695_376_block10 cost_1695_376_block11 rfl rfl rfl

private theorem cost_1695_376_join0_12 : P1_7_1_3.blockEstimate 1695 376 1912 256 = 15595315295 :=
  @P1_7_1_3.block_append 1695 376 1912 2040 128 128 256 9927164546 5668150749 15595315295 cost_1695_376_block12 cost_1695_376_block13 rfl rfl rfl

private theorem cost_1695_376_join0_14 : P1_7_1_3.blockEstimate 1695 376 2168 256 = 2875942656 :=
  @P1_7_1_3.block_append 1695 376 2168 2296 128 128 256 2397805440 478137216 2875942656 cost_1695_376_block14 cost_1695_376_block15 rfl rfl rfl

private theorem cost_1695_376_join1_0 : P1_7_1_3.blockEstimate 1695 376 376 512 = 29005108002 :=
  @P1_7_1_3.block_append 1695 376 376 632 256 256 512 4254192960 24750915042 29005108002 cost_1695_376_join0_0 cost_1695_376_join0_2 rfl rfl rfl

private theorem cost_1695_376_join1_2 : P1_7_1_3.blockEstimate 1695 376 888 512 = 99710118144 :=
  @P1_7_1_3.block_append 1695 376 888 1144 256 256 512 45568382080 54141736064 99710118144 cost_1695_376_join0_4 cost_1695_376_join0_6 rfl rfl rfl

private theorem cost_1695_376_join1_4 : P1_7_1_3.blockEstimate 1695 376 1400 512 = 84413263742 :=
  @P1_7_1_3.block_append 1695 376 1400 1656 256 256 512 50065069184 34348194558 84413263742 cost_1695_376_join0_8 cost_1695_376_join0_10 rfl rfl rfl

private theorem cost_1695_376_join1_6 : P1_7_1_3.blockEstimate 1695 376 1912 512 = 18471257951 :=
  @P1_7_1_3.block_append 1695 376 1912 2168 256 256 512 15595315295 2875942656 18471257951 cost_1695_376_join0_12 cost_1695_376_join0_14 rfl rfl rfl

private theorem cost_1695_376_join2_0 : P1_7_1_3.blockEstimate 1695 376 376 1024 = 128715226146 :=
  @P1_7_1_3.block_append 1695 376 376 888 512 512 1024 29005108002 99710118144 128715226146 cost_1695_376_join1_0 cost_1695_376_join1_2 rfl rfl rfl

private theorem cost_1695_376_join2_2 : P1_7_1_3.blockEstimate 1695 376 1400 1024 = 102884521693 :=
  @P1_7_1_3.block_append 1695 376 1400 1912 512 512 1024 84413263742 18471257951 102884521693 cost_1695_376_join1_4 cost_1695_376_join1_6 rfl rfl rfl

private theorem cost_1695_376_join3_0 : P1_7_1_3.blockEstimate 1695 376 376 2048 = 231599747839 :=
  @P1_7_1_3.block_append 1695 376 376 1400 1024 1024 2048 128715226146 102884521693 231599747839 cost_1695_376_join2_0 cost_1695_376_join2_2 rfl rfl rfl

private theorem cost_1695_376_join4_0 : P1_7_1_3.blockEstimate 1695 376 376 2071 = 231601806743 :=
  @P1_7_1_3.block_append 1695 376 376 2424 2048 23 2071 231599747839 2058904 231601806743 cost_1695_376_join3_0 cost_1695_376_block16 rfl rfl rfl

private theorem cost_1695_376_total : P1_7_1_3.momentEstimate 1695 376 = 231601806743 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1695 + 376 = 2071 by decide]
  exact cost_1695_376_join4_0

theorem moment1695_376 : P1_7_1.groupedPoleMoment 1695 376 ≤ 231601806743 :=
  (P1_7_1_3.grouped_bound 1695 376).trans_eq cost_1695_376_total
private theorem cost_1695_378_block0 : P1_7_1_3.blockEstimate 1695 378 378 128 = 572326560 := by decide +kernel

private theorem cost_1695_378_block1 : P1_7_1_3.blockEstimate 1695 378 506 128 = 3681866400 := by decide +kernel

private theorem cost_1695_378_block2 : P1_7_1_3.blockEstimate 1695 378 634 128 = 9134927645 := by decide +kernel

private theorem cost_1695_378_block3 : P1_7_1_3.blockEstimate 1695 378 762 128 = 15638376832 := by decide +kernel

private theorem cost_1695_378_block4 : P1_7_1_3.blockEstimate 1695 378 890 128 = 20978577792 := by decide +kernel

private theorem cost_1695_378_block5 : P1_7_1_3.blockEstimate 1695 378 1018 128 = 24729137536 := by decide +kernel

private theorem cost_1695_378_block6 : P1_7_1_3.blockEstimate 1695 378 1146 128 = 26890056064 := by decide +kernel

private theorem cost_1695_378_block7 : P1_7_1_3.blockEstimate 1695 378 1274 128 = 27461333376 := by decide +kernel

private theorem cost_1695_378_block8 : P1_7_1_3.blockEstimate 1695 378 1402 128 = 26442969472 := by decide +kernel

private theorem cost_1695_378_block9 : P1_7_1_3.blockEstimate 1695 378 1530 128 = 23834964352 := by decide +kernel

private theorem cost_1695_378_block10 : P1_7_1_3.blockEstimate 1695 378 1658 128 = 19703679588 := by decide +kernel

private theorem cost_1695_378_block11 : P1_7_1_3.blockEstimate 1695 378 1786 128 = 14819945737 := by decide +kernel

private theorem cost_1695_378_block12 : P1_7_1_3.blockEstimate 1695 378 1914 128 = 10002097720 := by decide +kernel

private theorem cost_1695_378_block13 : P1_7_1_3.blockEstimate 1695 378 2042 128 = 5728659130 := by decide +kernel

private theorem cost_1695_378_block14 : P1_7_1_3.blockEstimate 1695 378 2170 128 = 2439191888 := by decide +kernel

private theorem cost_1695_378_block15 : P1_7_1_3.blockEstimate 1695 378 2298 128 = 496445776 := by decide +kernel

private theorem cost_1695_378_block16 : P1_7_1_3.blockEstimate 1695 378 2426 25 = 2605036 := by decide +kernel

private theorem cost_1695_378_join0_0 : P1_7_1_3.blockEstimate 1695 378 378 256 = 4254192960 :=
  @P1_7_1_3.block_append 1695 378 378 506 128 128 256 572326560 3681866400 4254192960 cost_1695_378_block0 cost_1695_378_block1 rfl rfl rfl

private theorem cost_1695_378_join0_2 : P1_7_1_3.blockEstimate 1695 378 634 256 = 24773304477 :=
  @P1_7_1_3.block_append 1695 378 634 762 128 128 256 9134927645 15638376832 24773304477 cost_1695_378_block2 cost_1695_378_block3 rfl rfl rfl

private theorem cost_1695_378_join0_4 : P1_7_1_3.blockEstimate 1695 378 890 256 = 45707715328 :=
  @P1_7_1_3.block_append 1695 378 890 1018 128 128 256 20978577792 24729137536 45707715328 cost_1695_378_block4 cost_1695_378_block5 rfl rfl rfl

private theorem cost_1695_378_join0_6 : P1_7_1_3.blockEstimate 1695 378 1146 256 = 54351389440 :=
  @P1_7_1_3.block_append 1695 378 1146 1274 128 128 256 26890056064 27461333376 54351389440 cost_1695_378_block6 cost_1695_378_block7 rfl rfl rfl

private theorem cost_1695_378_join0_8 : P1_7_1_3.blockEstimate 1695 378 1402 256 = 50277933824 :=
  @P1_7_1_3.block_append 1695 378 1402 1530 128 128 256 26442969472 23834964352 50277933824 cost_1695_378_block8 cost_1695_378_block9 rfl rfl rfl

private theorem cost_1695_378_join0_10 : P1_7_1_3.blockEstimate 1695 378 1658 256 = 34523625325 :=
  @P1_7_1_3.block_append 1695 378 1658 1786 128 128 256 19703679588 14819945737 34523625325 cost_1695_378_block10 cost_1695_378_block11 rfl rfl rfl

private theorem cost_1695_378_join0_12 : P1_7_1_3.blockEstimate 1695 378 1914 256 = 15730756850 :=
  @P1_7_1_3.block_append 1695 378 1914 2042 128 128 256 10002097720 5728659130 15730756850 cost_1695_378_block12 cost_1695_378_block13 rfl rfl rfl

private theorem cost_1695_378_join0_14 : P1_7_1_3.blockEstimate 1695 378 2170 256 = 2935637664 :=
  @P1_7_1_3.block_append 1695 378 2170 2298 128 128 256 2439191888 496445776 2935637664 cost_1695_378_block14 cost_1695_378_block15 rfl rfl rfl

private theorem cost_1695_378_join1_0 : P1_7_1_3.blockEstimate 1695 378 378 512 = 29027497437 :=
  @P1_7_1_3.block_append 1695 378 378 634 256 256 512 4254192960 24773304477 29027497437 cost_1695_378_join0_0 cost_1695_378_join0_2 rfl rfl rfl

private theorem cost_1695_378_join1_2 : P1_7_1_3.blockEstimate 1695 378 890 512 = 100059104768 :=
  @P1_7_1_3.block_append 1695 378 890 1146 256 256 512 45707715328 54351389440 100059104768 cost_1695_378_join0_4 cost_1695_378_join0_6 rfl rfl rfl

private theorem cost_1695_378_join1_4 : P1_7_1_3.blockEstimate 1695 378 1402 512 = 84801559149 :=
  @P1_7_1_3.block_append 1695 378 1402 1658 256 256 512 50277933824 34523625325 84801559149 cost_1695_378_join0_8 cost_1695_378_join0_10 rfl rfl rfl

private theorem cost_1695_378_join1_6 : P1_7_1_3.blockEstimate 1695 378 1914 512 = 18666394514 :=
  @P1_7_1_3.block_append 1695 378 1914 2170 256 256 512 15730756850 2935637664 18666394514 cost_1695_378_join0_12 cost_1695_378_join0_14 rfl rfl rfl

private theorem cost_1695_378_join2_0 : P1_7_1_3.blockEstimate 1695 378 378 1024 = 129086602205 :=
  @P1_7_1_3.block_append 1695 378 378 890 512 512 1024 29027497437 100059104768 129086602205 cost_1695_378_join1_0 cost_1695_378_join1_2 rfl rfl rfl

private theorem cost_1695_378_join2_2 : P1_7_1_3.blockEstimate 1695 378 1402 1024 = 103467953663 :=
  @P1_7_1_3.block_append 1695 378 1402 1914 512 512 1024 84801559149 18666394514 103467953663 cost_1695_378_join1_4 cost_1695_378_join1_6 rfl rfl rfl

private theorem cost_1695_378_join3_0 : P1_7_1_3.blockEstimate 1695 378 378 2048 = 232554555868 :=
  @P1_7_1_3.block_append 1695 378 378 1402 1024 1024 2048 129086602205 103467953663 232554555868 cost_1695_378_join2_0 cost_1695_378_join2_2 rfl rfl rfl

private theorem cost_1695_378_join4_0 : P1_7_1_3.blockEstimate 1695 378 378 2073 = 232557160904 :=
  @P1_7_1_3.block_append 1695 378 378 2426 2048 25 2073 232554555868 2605036 232557160904 cost_1695_378_join3_0 cost_1695_378_block16 rfl rfl rfl

private theorem cost_1695_378_total : P1_7_1_3.momentEstimate 1695 378 = 232557160904 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1695 + 378 = 2073 by decide]
  exact cost_1695_378_join4_0

theorem moment1695_378 : P1_7_1.groupedPoleMoment 1695 378 ≤ 232557160904 :=
  (P1_7_1_3.grouped_bound 1695 378).trans_eq cost_1695_378_total
private theorem cost_1697_365_block0 : P1_7_1_3.blockEstimate 1697 365 365 128 = 573042080 := by decide +kernel

private theorem cost_1697_365_block1 : P1_7_1_3.blockEstimate 1697 365 493 128 = 3686808992 := by decide +kernel

private theorem cost_1697_365_block2 : P1_7_1_3.blockEstimate 1697 365 621 128 = 9146834763 := by decide +kernel

private theorem cost_1697_365_block3 : P1_7_1_3.blockEstimate 1697 365 749 128 = 15506769984 := by decide +kernel

private theorem cost_1697_365_block4 : P1_7_1_3.blockEstimate 1697 365 877 128 = 20636813376 := by decide +kernel

private theorem cost_1697_365_block5 : P1_7_1_3.blockEstimate 1697 365 1005 128 = 24231741504 := by decide +kernel

private theorem cost_1697_365_block6 : P1_7_1_3.blockEstimate 1697 365 1133 128 = 26291554368 := by decide +kernel

private theorem cost_1697_365_block7 : P1_7_1_3.blockEstimate 1697 365 1261 128 = 26816251968 := by decide +kernel

private theorem cost_1697_365_block8 : P1_7_1_3.blockEstimate 1697 365 1389 128 = 25805834304 := by decide +kernel

private theorem cost_1697_365_block9 : P1_7_1_3.blockEstimate 1697 365 1517 128 = 23260301376 := by decide +kernel

private theorem cost_1697_365_block10 : P1_7_1_3.blockEstimate 1697 365 1645 128 = 19218863928 := by decide +kernel

private theorem cost_1697_365_block11 : P1_7_1_3.blockEstimate 1697 365 1773 128 = 14371305438 := by decide +kernel

private theorem cost_1697_365_block12 : P1_7_1_3.blockEstimate 1697 365 1901 128 = 9603498834 := by decide +kernel

private theorem cost_1697_365_block13 : P1_7_1_3.blockEstimate 1697 365 2029 128 = 5406176724 := by decide +kernel

private theorem cost_1697_365_block14 : P1_7_1_3.blockEstimate 1697 365 2157 128 = 2218511312 := by decide +kernel

private theorem cost_1697_365_block15 : P1_7_1_3.blockEstimate 1697 365 2285 128 = 401102800 := by decide +kernel

private theorem cost_1697_365_block16 : P1_7_1_3.blockEstimate 1697 365 2413 14 = 520850 := by decide +kernel

private theorem cost_1697_365_join0_0 : P1_7_1_3.blockEstimate 1697 365 365 256 = 4259851072 :=
  @P1_7_1_3.block_append 1697 365 365 493 128 128 256 573042080 3686808992 4259851072 cost_1697_365_block0 cost_1697_365_block1 rfl rfl rfl

private theorem cost_1697_365_join0_2 : P1_7_1_3.blockEstimate 1697 365 621 256 = 24653604747 :=
  @P1_7_1_3.block_append 1697 365 621 749 128 128 256 9146834763 15506769984 24653604747 cost_1697_365_block2 cost_1697_365_block3 rfl rfl rfl

private theorem cost_1697_365_join0_4 : P1_7_1_3.blockEstimate 1697 365 877 256 = 44868554880 :=
  @P1_7_1_3.block_append 1697 365 877 1005 128 128 256 20636813376 24231741504 44868554880 cost_1697_365_block4 cost_1697_365_block5 rfl rfl rfl

private theorem cost_1697_365_join0_6 : P1_7_1_3.blockEstimate 1697 365 1133 256 = 53107806336 :=
  @P1_7_1_3.block_append 1697 365 1133 1261 128 128 256 26291554368 26816251968 53107806336 cost_1697_365_block6 cost_1697_365_block7 rfl rfl rfl

private theorem cost_1697_365_join0_8 : P1_7_1_3.blockEstimate 1697 365 1389 256 = 49066135680 :=
  @P1_7_1_3.block_append 1697 365 1389 1517 128 128 256 25805834304 23260301376 49066135680 cost_1697_365_block8 cost_1697_365_block9 rfl rfl rfl

private theorem cost_1697_365_join0_10 : P1_7_1_3.blockEstimate 1697 365 1645 256 = 33590169366 :=
  @P1_7_1_3.block_append 1697 365 1645 1773 128 128 256 19218863928 14371305438 33590169366 cost_1697_365_block10 cost_1697_365_block11 rfl rfl rfl

private theorem cost_1697_365_join0_12 : P1_7_1_3.blockEstimate 1697 365 1901 256 = 15009675558 :=
  @P1_7_1_3.block_append 1697 365 1901 2029 128 128 256 9603498834 5406176724 15009675558 cost_1697_365_block12 cost_1697_365_block13 rfl rfl rfl

private theorem cost_1697_365_join0_14 : P1_7_1_3.blockEstimate 1697 365 2157 256 = 2619614112 :=
  @P1_7_1_3.block_append 1697 365 2157 2285 128 128 256 2218511312 401102800 2619614112 cost_1697_365_block14 cost_1697_365_block15 rfl rfl rfl

private theorem cost_1697_365_join1_0 : P1_7_1_3.blockEstimate 1697 365 365 512 = 28913455819 :=
  @P1_7_1_3.block_append 1697 365 365 621 256 256 512 4259851072 24653604747 28913455819 cost_1697_365_join0_0 cost_1697_365_join0_2 rfl rfl rfl

private theorem cost_1697_365_join1_2 : P1_7_1_3.blockEstimate 1697 365 877 512 = 97976361216 :=
  @P1_7_1_3.block_append 1697 365 877 1133 256 256 512 44868554880 53107806336 97976361216 cost_1697_365_join0_4 cost_1697_365_join0_6 rfl rfl rfl

private theorem cost_1697_365_join1_4 : P1_7_1_3.blockEstimate 1697 365 1389 512 = 82656305046 :=
  @P1_7_1_3.block_append 1697 365 1389 1645 256 256 512 49066135680 33590169366 82656305046 cost_1697_365_join0_8 cost_1697_365_join0_10 rfl rfl rfl

private theorem cost_1697_365_join1_6 : P1_7_1_3.blockEstimate 1697 365 1901 512 = 17629289670 :=
  @P1_7_1_3.block_append 1697 365 1901 2157 256 256 512 15009675558 2619614112 17629289670 cost_1697_365_join0_12 cost_1697_365_join0_14 rfl rfl rfl

private theorem cost_1697_365_join2_0 : P1_7_1_3.blockEstimate 1697 365 365 1024 = 126889817035 :=
  @P1_7_1_3.block_append 1697 365 365 877 512 512 1024 28913455819 97976361216 126889817035 cost_1697_365_join1_0 cost_1697_365_join1_2 rfl rfl rfl

private theorem cost_1697_365_join2_2 : P1_7_1_3.blockEstimate 1697 365 1389 1024 = 100285594716 :=
  @P1_7_1_3.block_append 1697 365 1389 1901 512 512 1024 82656305046 17629289670 100285594716 cost_1697_365_join1_4 cost_1697_365_join1_6 rfl rfl rfl

private theorem cost_1697_365_join3_0 : P1_7_1_3.blockEstimate 1697 365 365 2048 = 227175411751 :=
  @P1_7_1_3.block_append 1697 365 365 1389 1024 1024 2048 126889817035 100285594716 227175411751 cost_1697_365_join2_0 cost_1697_365_join2_2 rfl rfl rfl

private theorem cost_1697_365_join4_0 : P1_7_1_3.blockEstimate 1697 365 365 2062 = 227175932601 :=
  @P1_7_1_3.block_append 1697 365 365 2413 2048 14 2062 227175411751 520850 227175932601 cost_1697_365_join3_0 cost_1697_365_block16 rfl rfl rfl

private theorem cost_1697_365_total : P1_7_1_3.momentEstimate 1697 365 = 227175932601 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1697 + 365 = 2062 by decide]
  exact cost_1697_365_join4_0

theorem moment1697_365 : P1_7_1.groupedPoleMoment 1697 365 ≤ 227175932601 :=
  (P1_7_1_3.grouped_bound 1697 365).trans_eq cost_1697_365_total
private theorem cost_1698_365_block0 : P1_7_1_3.blockEstimate 1698 365 365 128 = 573399840 := by decide +kernel

private theorem cost_1698_365_block1 : P1_7_1_3.blockEstimate 1698 365 493 128 = 3689280288 := by decide +kernel

private theorem cost_1698_365_block2 : P1_7_1_3.blockEstimate 1698 365 621 128 = 9153515607 := by decide +kernel

private theorem cost_1698_365_block3 : P1_7_1_3.blockEstimate 1698 365 749 128 = 15519231552 := by decide +kernel

private theorem cost_1698_365_block4 : P1_7_1_3.blockEstimate 1698 365 877 128 = 20655271488 := by decide +kernel

private theorem cost_1698_365_block5 : P1_7_1_3.blockEstimate 1698 365 1005 128 = 24256196160 := by decide +kernel

private theorem cost_1698_365_block6 : P1_7_1_3.blockEstimate 1698 365 1133 128 = 26322005568 := by decide +kernel

private theorem cost_1698_365_block7 : P1_7_1_3.blockEstimate 1698 365 1261 128 = 26852699712 := by decide +kernel

private theorem cost_1698_365_block8 : P1_7_1_3.blockEstimate 1698 365 1389 128 = 25848278592 := by decide +kernel

private theorem cost_1698_365_block9 : P1_7_1_3.blockEstimate 1698 365 1517 128 = 23308742208 := by decide +kernel

private theorem cost_1698_365_block10 : P1_7_1_3.blockEstimate 1698 365 1645 128 = 19271779773 := by decide +kernel

private theorem cost_1698_365_block11 : P1_7_1_3.blockEstimate 1698 365 1773 128 = 14420871970 := by decide +kernel

private theorem cost_1698_365_block12 : P1_7_1_3.blockEstimate 1698 365 1901 128 = 9646035558 := by decide +kernel

private theorem cost_1698_365_block13 : P1_7_1_3.blockEstimate 1698 365 2029 128 = 5439329208 := by decide +kernel

private theorem cost_1698_365_block14 : P1_7_1_3.blockEstimate 1698 365 2157 128 = 2239877088 := by decide +kernel

private theorem cost_1698_365_block15 : P1_7_1_3.blockEstimate 1698 365 2285 128 = 409583584 := by decide +kernel

private theorem cost_1698_365_block16 : P1_7_1_3.blockEstimate 1698 365 2413 15 = 629276 := by decide +kernel

private theorem cost_1698_365_join0_0 : P1_7_1_3.blockEstimate 1698 365 365 256 = 4262680128 :=
  @P1_7_1_3.block_append 1698 365 365 493 128 128 256 573399840 3689280288 4262680128 cost_1698_365_block0 cost_1698_365_block1 rfl rfl rfl

private theorem cost_1698_365_join0_2 : P1_7_1_3.blockEstimate 1698 365 621 256 = 24672747159 :=
  @P1_7_1_3.block_append 1698 365 621 749 128 128 256 9153515607 15519231552 24672747159 cost_1698_365_block2 cost_1698_365_block3 rfl rfl rfl

private theorem cost_1698_365_join0_4 : P1_7_1_3.blockEstimate 1698 365 877 256 = 44911467648 :=
  @P1_7_1_3.block_append 1698 365 877 1005 128 128 256 20655271488 24256196160 44911467648 cost_1698_365_block4 cost_1698_365_block5 rfl rfl rfl

private theorem cost_1698_365_join0_6 : P1_7_1_3.blockEstimate 1698 365 1133 256 = 53174705280 :=
  @P1_7_1_3.block_append 1698 365 1133 1261 128 128 256 26322005568 26852699712 53174705280 cost_1698_365_block6 cost_1698_365_block7 rfl rfl rfl

private theorem cost_1698_365_join0_8 : P1_7_1_3.blockEstimate 1698 365 1389 256 = 49157020800 :=
  @P1_7_1_3.block_append 1698 365 1389 1517 128 128 256 25848278592 23308742208 49157020800 cost_1698_365_block8 cost_1698_365_block9 rfl rfl rfl

private theorem cost_1698_365_join0_10 : P1_7_1_3.blockEstimate 1698 365 1645 256 = 33692651743 :=
  @P1_7_1_3.block_append 1698 365 1645 1773 128 128 256 19271779773 14420871970 33692651743 cost_1698_365_block10 cost_1698_365_block11 rfl rfl rfl

private theorem cost_1698_365_join0_12 : P1_7_1_3.blockEstimate 1698 365 1901 256 = 15085364766 :=
  @P1_7_1_3.block_append 1698 365 1901 2029 128 128 256 9646035558 5439329208 15085364766 cost_1698_365_block12 cost_1698_365_block13 rfl rfl rfl

private theorem cost_1698_365_join0_14 : P1_7_1_3.blockEstimate 1698 365 2157 256 = 2649460672 :=
  @P1_7_1_3.block_append 1698 365 2157 2285 128 128 256 2239877088 409583584 2649460672 cost_1698_365_block14 cost_1698_365_block15 rfl rfl rfl

private theorem cost_1698_365_join1_0 : P1_7_1_3.blockEstimate 1698 365 365 512 = 28935427287 :=
  @P1_7_1_3.block_append 1698 365 365 621 256 256 512 4262680128 24672747159 28935427287 cost_1698_365_join0_0 cost_1698_365_join0_2 rfl rfl rfl

private theorem cost_1698_365_join1_2 : P1_7_1_3.blockEstimate 1698 365 877 512 = 98086172928 :=
  @P1_7_1_3.block_append 1698 365 877 1133 256 256 512 44911467648 53174705280 98086172928 cost_1698_365_join0_4 cost_1698_365_join0_6 rfl rfl rfl

private theorem cost_1698_365_join1_4 : P1_7_1_3.blockEstimate 1698 365 1389 512 = 82849672543 :=
  @P1_7_1_3.block_append 1698 365 1389 1645 256 256 512 49157020800 33692651743 82849672543 cost_1698_365_join0_8 cost_1698_365_join0_10 rfl rfl rfl

private theorem cost_1698_365_join1_6 : P1_7_1_3.blockEstimate 1698 365 1901 512 = 17734825438 :=
  @P1_7_1_3.block_append 1698 365 1901 2157 256 256 512 15085364766 2649460672 17734825438 cost_1698_365_join0_12 cost_1698_365_join0_14 rfl rfl rfl

private theorem cost_1698_365_join2_0 : P1_7_1_3.blockEstimate 1698 365 365 1024 = 127021600215 :=
  @P1_7_1_3.block_append 1698 365 365 877 512 512 1024 28935427287 98086172928 127021600215 cost_1698_365_join1_0 cost_1698_365_join1_2 rfl rfl rfl

private theorem cost_1698_365_join2_2 : P1_7_1_3.blockEstimate 1698 365 1389 1024 = 100584497981 :=
  @P1_7_1_3.block_append 1698 365 1389 1901 512 512 1024 82849672543 17734825438 100584497981 cost_1698_365_join1_4 cost_1698_365_join1_6 rfl rfl rfl

private theorem cost_1698_365_join3_0 : P1_7_1_3.blockEstimate 1698 365 365 2048 = 227606098196 :=
  @P1_7_1_3.block_append 1698 365 365 1389 1024 1024 2048 127021600215 100584497981 227606098196 cost_1698_365_join2_0 cost_1698_365_join2_2 rfl rfl rfl

private theorem cost_1698_365_join4_0 : P1_7_1_3.blockEstimate 1698 365 365 2063 = 227606727472 :=
  @P1_7_1_3.block_append 1698 365 365 2413 2048 15 2063 227606098196 629276 227606727472 cost_1698_365_join3_0 cost_1698_365_block16 rfl rfl rfl

private theorem cost_1698_365_total : P1_7_1_3.momentEstimate 1698 365 = 227606727472 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1698 + 365 = 2063 by decide]
  exact cost_1698_365_join4_0

theorem moment1698_365 : P1_7_1.groupedPoleMoment 1698 365 ≤ 227606727472 :=
  (P1_7_1_3.grouped_bound 1698 365).trans_eq cost_1698_365_total
private theorem cost_1788_397_block0 : P1_7_1_3.blockEstimate 1788 397 397 128 = 605598240 := by decide +kernel

private theorem cost_1788_397_block1 : P1_7_1_3.blockEstimate 1788 397 525 128 = 3911696928 := by decide +kernel

private theorem cost_1788_397_block2 : P1_7_1_3.blockEstimate 1788 397 653 128 = 9756398112 := by decide +kernel

private theorem cost_1788_397_block3 : P1_7_1_3.blockEstimate 1788 397 781 128 = 17003566759 := by decide +kernel

private theorem cost_1788_397_block4 : P1_7_1_3.blockEstimate 1788 397 909 128 = 23279357504 := by decide +kernel

private theorem cost_1788_397_block5 : P1_7_1_3.blockEstimate 1788 397 1037 128 = 27886325312 := by decide +kernel

private theorem cost_1788_397_block6 : P1_7_1_3.blockEstimate 1788 397 1165 128 = 30823960128 := by decide +kernel

private theorem cost_1788_397_block7 : P1_7_1_3.blockEstimate 1788 397 1293 128 = 32092261952 := by decide +kernel

private theorem cost_1788_397_block8 : P1_7_1_3.blockEstimate 1788 397 1421 128 = 31691230784 := by decide +kernel

private theorem cost_1788_397_block9 : P1_7_1_3.blockEstimate 1788 397 1549 128 = 29620866624 := by decide +kernel

private theorem cost_1788_397_block10 : P1_7_1_3.blockEstimate 1788 397 1677 128 = 25881619112 := by decide +kernel

private theorem cost_1788_397_block11 : P1_7_1_3.blockEstimate 1788 397 1805 128 = 20767674735 := by decide +kernel

private theorem cost_1788_397_block12 : P1_7_1_3.blockEstimate 1788 397 1933 128 = 15292054074 := by decide +kernel

private theorem cost_1788_397_block13 : P1_7_1_3.blockEstimate 1788 397 2061 128 = 10082538507 := by decide +kernel

private theorem cost_1788_397_block14 : P1_7_1_3.blockEstimate 1788 397 2189 128 = 5583584176 := by decide +kernel

private theorem cost_1788_397_block15 : P1_7_1_3.blockEstimate 1788 397 2317 128 = 2243499952 := by decide +kernel

private theorem cost_1788_397_block16 : P1_7_1_3.blockEstimate 1788 397 2445 128 = 381580208 := by decide +kernel

private theorem cost_1788_397_block17 : P1_7_1_3.blockEstimate 1788 397 2573 9 = 169517 := by decide +kernel

private theorem cost_1788_397_join0_0 : P1_7_1_3.blockEstimate 1788 397 397 256 = 4517295168 :=
  @P1_7_1_3.block_append 1788 397 397 525 128 128 256 605598240 3911696928 4517295168 cost_1788_397_block0 cost_1788_397_block1 rfl rfl rfl

private theorem cost_1788_397_join0_2 : P1_7_1_3.blockEstimate 1788 397 653 256 = 26759964871 :=
  @P1_7_1_3.block_append 1788 397 653 781 128 128 256 9756398112 17003566759 26759964871 cost_1788_397_block2 cost_1788_397_block3 rfl rfl rfl

private theorem cost_1788_397_join0_4 : P1_7_1_3.blockEstimate 1788 397 909 256 = 51165682816 :=
  @P1_7_1_3.block_append 1788 397 909 1037 128 128 256 23279357504 27886325312 51165682816 cost_1788_397_block4 cost_1788_397_block5 rfl rfl rfl

private theorem cost_1788_397_join0_6 : P1_7_1_3.blockEstimate 1788 397 1165 256 = 62916222080 :=
  @P1_7_1_3.block_append 1788 397 1165 1293 128 128 256 30823960128 32092261952 62916222080 cost_1788_397_block6 cost_1788_397_block7 rfl rfl rfl

private theorem cost_1788_397_join0_8 : P1_7_1_3.blockEstimate 1788 397 1421 256 = 61312097408 :=
  @P1_7_1_3.block_append 1788 397 1421 1549 128 128 256 31691230784 29620866624 61312097408 cost_1788_397_block8 cost_1788_397_block9 rfl rfl rfl

private theorem cost_1788_397_join0_10 : P1_7_1_3.blockEstimate 1788 397 1677 256 = 46649293847 :=
  @P1_7_1_3.block_append 1788 397 1677 1805 128 128 256 25881619112 20767674735 46649293847 cost_1788_397_block10 cost_1788_397_block11 rfl rfl rfl

private theorem cost_1788_397_join0_12 : P1_7_1_3.blockEstimate 1788 397 1933 256 = 25374592581 :=
  @P1_7_1_3.block_append 1788 397 1933 2061 128 128 256 15292054074 10082538507 25374592581 cost_1788_397_block12 cost_1788_397_block13 rfl rfl rfl

private theorem cost_1788_397_join0_14 : P1_7_1_3.blockEstimate 1788 397 2189 256 = 7827084128 :=
  @P1_7_1_3.block_append 1788 397 2189 2317 128 128 256 5583584176 2243499952 7827084128 cost_1788_397_block14 cost_1788_397_block15 rfl rfl rfl

private theorem cost_1788_397_join0_16 : P1_7_1_3.blockEstimate 1788 397 2445 137 = 381749725 :=
  @P1_7_1_3.block_append 1788 397 2445 2573 128 9 137 381580208 169517 381749725 cost_1788_397_block16 cost_1788_397_block17 rfl rfl rfl

private theorem cost_1788_397_join1_0 : P1_7_1_3.blockEstimate 1788 397 397 512 = 31277260039 :=
  @P1_7_1_3.block_append 1788 397 397 653 256 256 512 4517295168 26759964871 31277260039 cost_1788_397_join0_0 cost_1788_397_join0_2 rfl rfl rfl

private theorem cost_1788_397_join1_2 : P1_7_1_3.blockEstimate 1788 397 909 512 = 114081904896 :=
  @P1_7_1_3.block_append 1788 397 909 1165 256 256 512 51165682816 62916222080 114081904896 cost_1788_397_join0_4 cost_1788_397_join0_6 rfl rfl rfl

private theorem cost_1788_397_join1_4 : P1_7_1_3.blockEstimate 1788 397 1421 512 = 107961391255 :=
  @P1_7_1_3.block_append 1788 397 1421 1677 256 256 512 61312097408 46649293847 107961391255 cost_1788_397_join0_8 cost_1788_397_join0_10 rfl rfl rfl

private theorem cost_1788_397_join1_6 : P1_7_1_3.blockEstimate 1788 397 1933 512 = 33201676709 :=
  @P1_7_1_3.block_append 1788 397 1933 2189 256 256 512 25374592581 7827084128 33201676709 cost_1788_397_join0_12 cost_1788_397_join0_14 rfl rfl rfl

private theorem cost_1788_397_join2_0 : P1_7_1_3.blockEstimate 1788 397 397 1024 = 145359164935 :=
  @P1_7_1_3.block_append 1788 397 397 909 512 512 1024 31277260039 114081904896 145359164935 cost_1788_397_join1_0 cost_1788_397_join1_2 rfl rfl rfl

private theorem cost_1788_397_join2_2 : P1_7_1_3.blockEstimate 1788 397 1421 1024 = 141163067964 :=
  @P1_7_1_3.block_append 1788 397 1421 1933 512 512 1024 107961391255 33201676709 141163067964 cost_1788_397_join1_4 cost_1788_397_join1_6 rfl rfl rfl

private theorem cost_1788_397_join3_0 : P1_7_1_3.blockEstimate 1788 397 397 2048 = 286522232899 :=
  @P1_7_1_3.block_append 1788 397 397 1421 1024 1024 2048 145359164935 141163067964 286522232899 cost_1788_397_join2_0 cost_1788_397_join2_2 rfl rfl rfl

private theorem cost_1788_397_join4_0 : P1_7_1_3.blockEstimate 1788 397 397 2185 = 286903982624 :=
  @P1_7_1_3.block_append 1788 397 397 2445 2048 137 2185 286522232899 381749725 286903982624 cost_1788_397_join3_0 cost_1788_397_join0_16 rfl rfl rfl

private theorem cost_1788_397_total : P1_7_1_3.momentEstimate 1788 397 = 286903982624 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1788 + 397 = 2185 by decide]
  exact cost_1788_397_join4_0

theorem moment1788_397 : P1_7_1.groupedPoleMoment 1788 397 ≤ 286903982624 :=
  (P1_7_1_3.grouped_bound 1788 397).trans_eq cost_1788_397_total
private theorem cost_1789_399_block0 : P1_7_1_3.blockEstimate 1789 399 399 128 = 605956000 := by decide +kernel

private theorem cost_1789_399_block1 : P1_7_1_3.blockEstimate 1789 399 527 128 = 3914168224 := by decide +kernel

private theorem cost_1789_399_block2 : P1_7_1_3.blockEstimate 1789 399 655 128 = 9763080096 := by decide +kernel

private theorem cost_1789_399_block3 : P1_7_1_3.blockEstimate 1789 399 783 128 = 17033399380 := by decide +kernel

private theorem cost_1789_399_block4 : P1_7_1_3.blockEstimate 1789 399 911 128 = 23353561600 := by decide +kernel

private theorem cost_1789_399_block5 : P1_7_1_3.blockEstimate 1789 399 1039 128 = 27996787200 := by decide +kernel

private theorem cost_1789_399_block6 : P1_7_1_3.blockEstimate 1789 399 1167 128 = 30962291200 := by decide +kernel

private theorem cost_1789_399_block7 : P1_7_1_3.blockEstimate 1789 399 1295 128 = 32250073600 := by decide +kernel

private theorem cost_1789_399_block8 : P1_7_1_3.blockEstimate 1789 399 1423 128 = 31860134400 := by decide +kernel

private theorem cost_1789_399_block9 : P1_7_1_3.blockEstimate 1789 399 1551 128 = 29792473600 := by decide +kernel

private theorem cost_1789_399_block10 : P1_7_1_3.blockEstimate 1789 399 1679 128 = 26047621885 := by decide +kernel

private theorem cost_1789_399_block11 : P1_7_1_3.blockEstimate 1789 399 1807 128 = 20925086548 := by decide +kernel

private theorem cost_1789_399_block12 : P1_7_1_3.blockEstimate 1789 399 1935 128 = 15436664589 := by decide +kernel

private theorem cost_1789_399_block13 : P1_7_1_3.blockEstimate 1789 399 2063 128 = 10207199264 := by decide +kernel

private theorem cost_1789_399_block14 : P1_7_1_3.blockEstimate 1789 399 2191 128 = 5681162688 := by decide +kernel

private theorem cost_1789_399_block15 : P1_7_1_3.blockEstimate 1789 399 2319 128 = 2307244480 := by decide +kernel

private theorem cost_1789_399_block16 : P1_7_1_3.blockEstimate 1789 399 2447 128 = 406641088 := by decide +kernel

private theorem cost_1789_399_block17 : P1_7_1_3.blockEstimate 1789 399 2575 12 = 362152 := by decide +kernel

private theorem cost_1789_399_join0_0 : P1_7_1_3.blockEstimate 1789 399 399 256 = 4520124224 :=
  @P1_7_1_3.block_append 1789 399 399 527 128 128 256 605956000 3914168224 4520124224 cost_1789_399_block0 cost_1789_399_block1 rfl rfl rfl

private theorem cost_1789_399_join0_2 : P1_7_1_3.blockEstimate 1789 399 655 256 = 26796479476 :=
  @P1_7_1_3.block_append 1789 399 655 783 128 128 256 9763080096 17033399380 26796479476 cost_1789_399_block2 cost_1789_399_block3 rfl rfl rfl

private theorem cost_1789_399_join0_4 : P1_7_1_3.blockEstimate 1789 399 911 256 = 51350348800 :=
  @P1_7_1_3.block_append 1789 399 911 1039 128 128 256 23353561600 27996787200 51350348800 cost_1789_399_block4 cost_1789_399_block5 rfl rfl rfl

private theorem cost_1789_399_join0_6 : P1_7_1_3.blockEstimate 1789 399 1167 256 = 63212364800 :=
  @P1_7_1_3.block_append 1789 399 1167 1295 128 128 256 30962291200 32250073600 63212364800 cost_1789_399_block6 cost_1789_399_block7 rfl rfl rfl

private theorem cost_1789_399_join0_8 : P1_7_1_3.blockEstimate 1789 399 1423 256 = 61652608000 :=
  @P1_7_1_3.block_append 1789 399 1423 1551 128 128 256 31860134400 29792473600 61652608000 cost_1789_399_block8 cost_1789_399_block9 rfl rfl rfl

private theorem cost_1789_399_join0_10 : P1_7_1_3.blockEstimate 1789 399 1679 256 = 46972708433 :=
  @P1_7_1_3.block_append 1789 399 1679 1807 128 128 256 26047621885 20925086548 46972708433 cost_1789_399_block10 cost_1789_399_block11 rfl rfl rfl

private theorem cost_1789_399_join0_12 : P1_7_1_3.blockEstimate 1789 399 1935 256 = 25643863853 :=
  @P1_7_1_3.block_append 1789 399 1935 2063 128 128 256 15436664589 10207199264 25643863853 cost_1789_399_block12 cost_1789_399_block13 rfl rfl rfl

private theorem cost_1789_399_join0_14 : P1_7_1_3.blockEstimate 1789 399 2191 256 = 7988407168 :=
  @P1_7_1_3.block_append 1789 399 2191 2319 128 128 256 5681162688 2307244480 7988407168 cost_1789_399_block14 cost_1789_399_block15 rfl rfl rfl

private theorem cost_1789_399_join0_16 : P1_7_1_3.blockEstimate 1789 399 2447 140 = 407003240 :=
  @P1_7_1_3.block_append 1789 399 2447 2575 128 12 140 406641088 362152 407003240 cost_1789_399_block16 cost_1789_399_block17 rfl rfl rfl

private theorem cost_1789_399_join1_0 : P1_7_1_3.blockEstimate 1789 399 399 512 = 31316603700 :=
  @P1_7_1_3.block_append 1789 399 399 655 256 256 512 4520124224 26796479476 31316603700 cost_1789_399_join0_0 cost_1789_399_join0_2 rfl rfl rfl

private theorem cost_1789_399_join1_2 : P1_7_1_3.blockEstimate 1789 399 911 512 = 114562713600 :=
  @P1_7_1_3.block_append 1789 399 911 1167 256 256 512 51350348800 63212364800 114562713600 cost_1789_399_join0_4 cost_1789_399_join0_6 rfl rfl rfl

private theorem cost_1789_399_join1_4 : P1_7_1_3.blockEstimate 1789 399 1423 512 = 108625316433 :=
  @P1_7_1_3.block_append 1789 399 1423 1679 256 256 512 61652608000 46972708433 108625316433 cost_1789_399_join0_8 cost_1789_399_join0_10 rfl rfl rfl

private theorem cost_1789_399_join1_6 : P1_7_1_3.blockEstimate 1789 399 1935 512 = 33632271021 :=
  @P1_7_1_3.block_append 1789 399 1935 2191 256 256 512 25643863853 7988407168 33632271021 cost_1789_399_join0_12 cost_1789_399_join0_14 rfl rfl rfl

private theorem cost_1789_399_join2_0 : P1_7_1_3.blockEstimate 1789 399 399 1024 = 145879317300 :=
  @P1_7_1_3.block_append 1789 399 399 911 512 512 1024 31316603700 114562713600 145879317300 cost_1789_399_join1_0 cost_1789_399_join1_2 rfl rfl rfl

private theorem cost_1789_399_join2_2 : P1_7_1_3.blockEstimate 1789 399 1423 1024 = 142257587454 :=
  @P1_7_1_3.block_append 1789 399 1423 1935 512 512 1024 108625316433 33632271021 142257587454 cost_1789_399_join1_4 cost_1789_399_join1_6 rfl rfl rfl

private theorem cost_1789_399_join3_0 : P1_7_1_3.blockEstimate 1789 399 399 2048 = 288136904754 :=
  @P1_7_1_3.block_append 1789 399 399 1423 1024 1024 2048 145879317300 142257587454 288136904754 cost_1789_399_join2_0 cost_1789_399_join2_2 rfl rfl rfl

private theorem cost_1789_399_join4_0 : P1_7_1_3.blockEstimate 1789 399 399 2188 = 288543907994 :=
  @P1_7_1_3.block_append 1789 399 399 2447 2048 140 2188 288136904754 407003240 288543907994 cost_1789_399_join3_0 cost_1789_399_join0_16 rfl rfl rfl

private theorem cost_1789_399_total : P1_7_1_3.momentEstimate 1789 399 = 288543907994 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1789 + 399 = 2188 by decide]
  exact cost_1789_399_join4_0

theorem moment1789_399 : P1_7_1.groupedPoleMoment 1789 399 ≤ 288543907994 :=
  (P1_7_1_3.grouped_bound 1789 399).trans_eq cost_1789_399_total
private theorem cost_1790_388_block0 : P1_7_1_3.blockEstimate 1790 388 388 128 = 606313760 := by decide +kernel

private theorem cost_1790_388_block1 : P1_7_1_3.blockEstimate 1790 388 516 128 = 3916639520 := by decide +kernel

private theorem cost_1790_388_block2 : P1_7_1_3.blockEstimate 1790 388 644 128 = 9769762080 := by decide +kernel

private theorem cost_1790_388_block3 : P1_7_1_3.blockEstimate 1790 388 772 128 = 16944281447 := by decide +kernel

private theorem cost_1790_388_block4 : P1_7_1_3.blockEstimate 1790 388 900 128 = 23062708352 := by decide +kernel

private theorem cost_1790_388_block5 : P1_7_1_3.blockEstimate 1790 388 1028 128 = 27549565056 := by decide +kernel

private theorem cost_1790_388_block6 : P1_7_1_3.blockEstimate 1790 388 1156 128 = 30404837504 := by decide +kernel

private theorem cost_1790_388_block7 : P1_7_1_3.blockEstimate 1790 388 1284 128 = 31628525696 := by decide +kernel

private theorem cost_1790_388_block8 : P1_7_1_3.blockEstimate 1790 388 1412 128 = 31220629632 := by decide +kernel

private theorem cost_1790_388_block9 : P1_7_1_3.blockEstimate 1790 388 1540 128 = 29181149312 := by decide +kernel

private theorem cost_1790_388_block10 : P1_7_1_3.blockEstimate 1790 388 1668 128 = 25510107184 := by decide +kernel

private theorem cost_1790_388_block11 : P1_7_1_3.blockEstimate 1790 388 1796 128 = 20442859080 := by decide +kernel

private theorem cost_1790_388_block12 : P1_7_1_3.blockEstimate 1790 388 1924 128 = 14990480832 := by decide +kernel

private theorem cost_1790_388_block13 : P1_7_1_3.blockEstimate 1790 388 2052 128 = 9817937568 := by decide +kernel

private theorem cost_1790_388_block14 : P1_7_1_3.blockEstimate 1790 388 2180 128 = 5373718320 := by decide +kernel

private theorem cost_1790_388_block15 : P1_7_1_3.blockEstimate 1790 388 2308 128 = 2103714608 := by decide +kernel

private theorem cost_1790_388_block16 : P1_7_1_3.blockEstimate 1790 388 2436 128 = 327735088 := by decide +kernel

private theorem cost_1790_388_block17 : P1_7_1_3.blockEstimate 1790 388 2564 2 = 5369 := by decide +kernel

private theorem cost_1790_388_join0_0 : P1_7_1_3.blockEstimate 1790 388 388 256 = 4522953280 :=
  @P1_7_1_3.block_append 1790 388 388 516 128 128 256 606313760 3916639520 4522953280 cost_1790_388_block0 cost_1790_388_block1 rfl rfl rfl

private theorem cost_1790_388_join0_2 : P1_7_1_3.blockEstimate 1790 388 644 256 = 26714043527 :=
  @P1_7_1_3.block_append 1790 388 644 772 128 128 256 9769762080 16944281447 26714043527 cost_1790_388_block2 cost_1790_388_block3 rfl rfl rfl

private theorem cost_1790_388_join0_4 : P1_7_1_3.blockEstimate 1790 388 900 256 = 50612273408 :=
  @P1_7_1_3.block_append 1790 388 900 1028 128 128 256 23062708352 27549565056 50612273408 cost_1790_388_block4 cost_1790_388_block5 rfl rfl rfl

private theorem cost_1790_388_join0_6 : P1_7_1_3.blockEstimate 1790 388 1156 256 = 62033363200 :=
  @P1_7_1_3.block_append 1790 388 1156 1284 128 128 256 30404837504 31628525696 62033363200 cost_1790_388_block6 cost_1790_388_block7 rfl rfl rfl

private theorem cost_1790_388_join0_8 : P1_7_1_3.blockEstimate 1790 388 1412 256 = 60401778944 :=
  @P1_7_1_3.block_append 1790 388 1412 1540 128 128 256 31220629632 29181149312 60401778944 cost_1790_388_block8 cost_1790_388_block9 rfl rfl rfl

private theorem cost_1790_388_join0_10 : P1_7_1_3.blockEstimate 1790 388 1668 256 = 45952966264 :=
  @P1_7_1_3.block_append 1790 388 1668 1796 128 128 256 25510107184 20442859080 45952966264 cost_1790_388_block10 cost_1790_388_block11 rfl rfl rfl

private theorem cost_1790_388_join0_12 : P1_7_1_3.blockEstimate 1790 388 1924 256 = 24808418400 :=
  @P1_7_1_3.block_append 1790 388 1924 2052 128 128 256 14990480832 9817937568 24808418400 cost_1790_388_block12 cost_1790_388_block13 rfl rfl rfl

private theorem cost_1790_388_join0_14 : P1_7_1_3.blockEstimate 1790 388 2180 256 = 7477432928 :=
  @P1_7_1_3.block_append 1790 388 2180 2308 128 128 256 5373718320 2103714608 7477432928 cost_1790_388_block14 cost_1790_388_block15 rfl rfl rfl

private theorem cost_1790_388_join0_16 : P1_7_1_3.blockEstimate 1790 388 2436 130 = 327740457 :=
  @P1_7_1_3.block_append 1790 388 2436 2564 128 2 130 327735088 5369 327740457 cost_1790_388_block16 cost_1790_388_block17 rfl rfl rfl

private theorem cost_1790_388_join1_0 : P1_7_1_3.blockEstimate 1790 388 388 512 = 31236996807 :=
  @P1_7_1_3.block_append 1790 388 388 644 256 256 512 4522953280 26714043527 31236996807 cost_1790_388_join0_0 cost_1790_388_join0_2 rfl rfl rfl

private theorem cost_1790_388_join1_2 : P1_7_1_3.blockEstimate 1790 388 900 512 = 112645636608 :=
  @P1_7_1_3.block_append 1790 388 900 1156 256 256 512 50612273408 62033363200 112645636608 cost_1790_388_join0_4 cost_1790_388_join0_6 rfl rfl rfl

private theorem cost_1790_388_join1_4 : P1_7_1_3.blockEstimate 1790 388 1412 512 = 106354745208 :=
  @P1_7_1_3.block_append 1790 388 1412 1668 256 256 512 60401778944 45952966264 106354745208 cost_1790_388_join0_8 cost_1790_388_join0_10 rfl rfl rfl

private theorem cost_1790_388_join1_6 : P1_7_1_3.blockEstimate 1790 388 1924 512 = 32285851328 :=
  @P1_7_1_3.block_append 1790 388 1924 2180 256 256 512 24808418400 7477432928 32285851328 cost_1790_388_join0_12 cost_1790_388_join0_14 rfl rfl rfl

private theorem cost_1790_388_join2_0 : P1_7_1_3.blockEstimate 1790 388 388 1024 = 143882633415 :=
  @P1_7_1_3.block_append 1790 388 388 900 512 512 1024 31236996807 112645636608 143882633415 cost_1790_388_join1_0 cost_1790_388_join1_2 rfl rfl rfl

private theorem cost_1790_388_join2_2 : P1_7_1_3.blockEstimate 1790 388 1412 1024 = 138640596536 :=
  @P1_7_1_3.block_append 1790 388 1412 1924 512 512 1024 106354745208 32285851328 138640596536 cost_1790_388_join1_4 cost_1790_388_join1_6 rfl rfl rfl

private theorem cost_1790_388_join3_0 : P1_7_1_3.blockEstimate 1790 388 388 2048 = 282523229951 :=
  @P1_7_1_3.block_append 1790 388 388 1412 1024 1024 2048 143882633415 138640596536 282523229951 cost_1790_388_join2_0 cost_1790_388_join2_2 rfl rfl rfl

private theorem cost_1790_388_join4_0 : P1_7_1_3.blockEstimate 1790 388 388 2178 = 282850970408 :=
  @P1_7_1_3.block_append 1790 388 388 2436 2048 130 2178 282523229951 327740457 282850970408 cost_1790_388_join3_0 cost_1790_388_join0_16 rfl rfl rfl

private theorem cost_1790_388_total : P1_7_1_3.momentEstimate 1790 388 = 282850970408 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1790 + 388 = 2178 by decide]
  exact cost_1790_388_join4_0

theorem moment1790_388 : P1_7_1.groupedPoleMoment 1790 388 ≤ 282850970408 :=
  (P1_7_1_3.grouped_bound 1790 388).trans_eq cost_1790_388_total
private theorem cost_1881_410_block0 : P1_7_1_3.blockEstimate 1881 410 410 128 = 638869920 := by decide +kernel

private theorem cost_1881_410_block1 : P1_7_1_3.blockEstimate 1881 410 538 128 = 4141527456 := by decide +kernel

private theorem cost_1881_410_block2 : P1_7_1_3.blockEstimate 1881 410 666 128 = 10377822624 := by decide +kernel

private theorem cost_1881_410_block3 : P1_7_1_3.blockEstimate 1881 410 794 128 = 18295741911 := by decide +kernel

private theorem cost_1881_410_block4 : P1_7_1_3.blockEstimate 1881 410 922 128 = 25442701824 := by decide +kernel

private theorem cost_1881_410_block5 : P1_7_1_3.blockEstimate 1881 410 1050 128 = 30870163968 := by decide +kernel

private theorem cost_1881_410_block6 : P1_7_1_3.blockEstimate 1881 410 1178 128 = 34573767168 := by decide +kernel

private theorem cost_1881_410_block7 : P1_7_1_3.blockEstimate 1881 410 1306 128 = 36553511424 := by decide +kernel

private theorem cost_1881_410_block8 : P1_7_1_3.blockEstimate 1881 410 1434 128 = 36809396736 := by decide +kernel

private theorem cost_1881_410_block9 : P1_7_1_3.blockEstimate 1881 410 1562 128 = 35341423104 := by decide +kernel

private theorem cost_1881_410_block10 : P1_7_1_3.blockEstimate 1881 410 1690 128 = 32149590528 := by decide +kernel

private theorem cost_1881_410_block11 : P1_7_1_3.blockEstimate 1881 410 1818 128 = 27260427863 := by decide +kernel

private theorem cost_1881_410_block12 : P1_7_1_3.blockEstimate 1881 410 1946 128 = 21335366879 := by decide +kernel

private theorem cost_1881_410_block13 : P1_7_1_3.blockEstimate 1881 410 2074 128 = 15349473756 := by decide +kernel

private theorem cost_1881_410_block14 : P1_7_1_3.blockEstimate 1881 410 2202 128 = 9828645835 := by decide +kernel

private theorem cost_1881_410_block15 : P1_7_1_3.blockEstimate 1881 410 2330 128 = 5202518560 := by decide +kernel

private theorem cost_1881_410_block16 : P1_7_1_3.blockEstimate 1881 410 2458 128 = 1912310304 := by decide +kernel

private theorem cost_1881_410_block17 : P1_7_1_3.blockEstimate 1881 410 2586 115 = 240801877 := by decide +kernel

private theorem cost_1881_410_join0_0 : P1_7_1_3.blockEstimate 1881 410 410 256 = 4780397376 :=
  @P1_7_1_3.block_append 1881 410 410 538 128 128 256 638869920 4141527456 4780397376 cost_1881_410_block0 cost_1881_410_block1 rfl rfl rfl

private theorem cost_1881_410_join0_2 : P1_7_1_3.blockEstimate 1881 410 666 256 = 28673564535 :=
  @P1_7_1_3.block_append 1881 410 666 794 128 128 256 10377822624 18295741911 28673564535 cost_1881_410_block2 cost_1881_410_block3 rfl rfl rfl

private theorem cost_1881_410_join0_4 : P1_7_1_3.blockEstimate 1881 410 922 256 = 56312865792 :=
  @P1_7_1_3.block_append 1881 410 922 1050 128 128 256 25442701824 30870163968 56312865792 cost_1881_410_block4 cost_1881_410_block5 rfl rfl rfl

private theorem cost_1881_410_join0_6 : P1_7_1_3.blockEstimate 1881 410 1178 256 = 71127278592 :=
  @P1_7_1_3.block_append 1881 410 1178 1306 128 128 256 34573767168 36553511424 71127278592 cost_1881_410_block6 cost_1881_410_block7 rfl rfl rfl

private theorem cost_1881_410_join0_8 : P1_7_1_3.blockEstimate 1881 410 1434 256 = 72150819840 :=
  @P1_7_1_3.block_append 1881 410 1434 1562 128 128 256 36809396736 35341423104 72150819840 cost_1881_410_block8 cost_1881_410_block9 rfl rfl rfl

private theorem cost_1881_410_join0_10 : P1_7_1_3.blockEstimate 1881 410 1690 256 = 59410018391 :=
  @P1_7_1_3.block_append 1881 410 1690 1818 128 128 256 32149590528 27260427863 59410018391 cost_1881_410_block10 cost_1881_410_block11 rfl rfl rfl

private theorem cost_1881_410_join0_12 : P1_7_1_3.blockEstimate 1881 410 1946 256 = 36684840635 :=
  @P1_7_1_3.block_append 1881 410 1946 2074 128 128 256 21335366879 15349473756 36684840635 cost_1881_410_block12 cost_1881_410_block13 rfl rfl rfl

private theorem cost_1881_410_join0_14 : P1_7_1_3.blockEstimate 1881 410 2202 256 = 15031164395 :=
  @P1_7_1_3.block_append 1881 410 2202 2330 128 128 256 9828645835 5202518560 15031164395 cost_1881_410_block14 cost_1881_410_block15 rfl rfl rfl

private theorem cost_1881_410_join0_16 : P1_7_1_3.blockEstimate 1881 410 2458 243 = 2153112181 :=
  @P1_7_1_3.block_append 1881 410 2458 2586 128 115 243 1912310304 240801877 2153112181 cost_1881_410_block16 cost_1881_410_block17 rfl rfl rfl

private theorem cost_1881_410_join1_0 : P1_7_1_3.blockEstimate 1881 410 410 512 = 33453961911 :=
  @P1_7_1_3.block_append 1881 410 410 666 256 256 512 4780397376 28673564535 33453961911 cost_1881_410_join0_0 cost_1881_410_join0_2 rfl rfl rfl

private theorem cost_1881_410_join1_2 : P1_7_1_3.blockEstimate 1881 410 922 512 = 127440144384 :=
  @P1_7_1_3.block_append 1881 410 922 1178 256 256 512 56312865792 71127278592 127440144384 cost_1881_410_join0_4 cost_1881_410_join0_6 rfl rfl rfl

private theorem cost_1881_410_join1_4 : P1_7_1_3.blockEstimate 1881 410 1434 512 = 131560838231 :=
  @P1_7_1_3.block_append 1881 410 1434 1690 256 256 512 72150819840 59410018391 131560838231 cost_1881_410_join0_8 cost_1881_410_join0_10 rfl rfl rfl

private theorem cost_1881_410_join1_6 : P1_7_1_3.blockEstimate 1881 410 1946 512 = 51716005030 :=
  @P1_7_1_3.block_append 1881 410 1946 2202 256 256 512 36684840635 15031164395 51716005030 cost_1881_410_join0_12 cost_1881_410_join0_14 rfl rfl rfl

private theorem cost_1881_410_join2_0 : P1_7_1_3.blockEstimate 1881 410 410 1024 = 160894106295 :=
  @P1_7_1_3.block_append 1881 410 410 922 512 512 1024 33453961911 127440144384 160894106295 cost_1881_410_join1_0 cost_1881_410_join1_2 rfl rfl rfl

private theorem cost_1881_410_join2_2 : P1_7_1_3.blockEstimate 1881 410 1434 1024 = 183276843261 :=
  @P1_7_1_3.block_append 1881 410 1434 1946 512 512 1024 131560838231 51716005030 183276843261 cost_1881_410_join1_4 cost_1881_410_join1_6 rfl rfl rfl

private theorem cost_1881_410_join3_0 : P1_7_1_3.blockEstimate 1881 410 410 2048 = 344170949556 :=
  @P1_7_1_3.block_append 1881 410 410 1434 1024 1024 2048 160894106295 183276843261 344170949556 cost_1881_410_join2_0 cost_1881_410_join2_2 rfl rfl rfl

private theorem cost_1881_410_join4_0 : P1_7_1_3.blockEstimate 1881 410 410 2291 = 346324061737 :=
  @P1_7_1_3.block_append 1881 410 410 2458 2048 243 2291 344170949556 2153112181 346324061737 cost_1881_410_join3_0 cost_1881_410_join0_16 rfl rfl rfl

private theorem cost_1881_410_total : P1_7_1_3.momentEstimate 1881 410 = 346324061737 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1881 + 410 = 2291 by decide]
  exact cost_1881_410_join4_0

theorem moment1881_410 : P1_7_1.groupedPoleMoment 1881 410 ≤ 346324061737 :=
  (P1_7_1_3.grouped_bound 1881 410).trans_eq cost_1881_410_total
private theorem cost_1881_418_block0 : P1_7_1_3.blockEstimate 1881 418 418 128 = 638869920 := by decide +kernel

private theorem cost_1881_418_block1 : P1_7_1_3.blockEstimate 1881 418 546 128 = 4141527456 := by decide +kernel

private theorem cost_1881_418_block2 : P1_7_1_3.blockEstimate 1881 418 674 128 = 10377822624 := by decide +kernel

private theorem cost_1881_418_block3 : P1_7_1_3.blockEstimate 1881 418 802 128 = 18349636961 := by decide +kernel

private theorem cost_1881_418_block4 : P1_7_1_3.blockEstimate 1881 418 930 128 = 25657870592 := by decide +kernel

private theorem cost_1881_418_block5 : P1_7_1_3.blockEstimate 1881 418 1058 128 = 31218436352 := by decide +kernel

private theorem cost_1881_418_block6 : P1_7_1_3.blockEstimate 1881 418 1186 128 = 35021588736 := by decide +kernel

private theorem cost_1881_418_block7 : P1_7_1_3.blockEstimate 1881 418 1314 128 = 37067327744 := by decide +kernel

private theorem cost_1881_418_block8 : P1_7_1_3.blockEstimate 1881 418 1442 128 = 37355653376 := by decide +kernel

private theorem cost_1881_418_block9 : P1_7_1_3.blockEstimate 1881 418 1570 128 = 35886565632 := by decide +kernel

private theorem cost_1881_418_block10 : P1_7_1_3.blockEstimate 1881 418 1698 128 = 32660064512 := by decide +kernel

private theorem cost_1881_418_block11 : P1_7_1_3.blockEstimate 1881 418 1826 128 = 27713401036 := by decide +kernel

private theorem cost_1881_418_block12 : P1_7_1_3.blockEstimate 1881 418 1954 128 = 21759242744 := by decide +kernel

private theorem cost_1881_418_block13 : P1_7_1_3.blockEstimate 1881 418 2082 128 = 15735296197 := by decide +kernel

private theorem cost_1881_418_block14 : P1_7_1_3.blockEstimate 1881 418 2210 128 = 10158403853 := by decide +kernel

private theorem cost_1881_418_block15 : P1_7_1_3.blockEstimate 1881 418 2338 128 = 5456165664 := by decide +kernel

private theorem cost_1881_418_block16 : P1_7_1_3.blockEstimate 1881 418 2466 128 = 2073129760 := by decide +kernel

private theorem cost_1881_418_block17 : P1_7_1_3.blockEstimate 1881 418 2594 123 = 293295371 := by decide +kernel

private theorem cost_1881_418_join0_0 : P1_7_1_3.blockEstimate 1881 418 418 256 = 4780397376 :=
  @P1_7_1_3.block_append 1881 418 418 546 128 128 256 638869920 4141527456 4780397376 cost_1881_418_block0 cost_1881_418_block1 rfl rfl rfl

private theorem cost_1881_418_join0_2 : P1_7_1_3.blockEstimate 1881 418 674 256 = 28727459585 :=
  @P1_7_1_3.block_append 1881 418 674 802 128 128 256 10377822624 18349636961 28727459585 cost_1881_418_block2 cost_1881_418_block3 rfl rfl rfl

private theorem cost_1881_418_join0_4 : P1_7_1_3.blockEstimate 1881 418 930 256 = 56876306944 :=
  @P1_7_1_3.block_append 1881 418 930 1058 128 128 256 25657870592 31218436352 56876306944 cost_1881_418_block4 cost_1881_418_block5 rfl rfl rfl

private theorem cost_1881_418_join0_6 : P1_7_1_3.blockEstimate 1881 418 1186 256 = 72088916480 :=
  @P1_7_1_3.block_append 1881 418 1186 1314 128 128 256 35021588736 37067327744 72088916480 cost_1881_418_block6 cost_1881_418_block7 rfl rfl rfl

private theorem cost_1881_418_join0_8 : P1_7_1_3.blockEstimate 1881 418 1442 256 = 73242219008 :=
  @P1_7_1_3.block_append 1881 418 1442 1570 128 128 256 37355653376 35886565632 73242219008 cost_1881_418_block8 cost_1881_418_block9 rfl rfl rfl

private theorem cost_1881_418_join0_10 : P1_7_1_3.blockEstimate 1881 418 1698 256 = 60373465548 :=
  @P1_7_1_3.block_append 1881 418 1698 1826 128 128 256 32660064512 27713401036 60373465548 cost_1881_418_block10 cost_1881_418_block11 rfl rfl rfl

private theorem cost_1881_418_join0_12 : P1_7_1_3.blockEstimate 1881 418 1954 256 = 37494538941 :=
  @P1_7_1_3.block_append 1881 418 1954 2082 128 128 256 21759242744 15735296197 37494538941 cost_1881_418_block12 cost_1881_418_block13 rfl rfl rfl

private theorem cost_1881_418_join0_14 : P1_7_1_3.blockEstimate 1881 418 2210 256 = 15614569517 :=
  @P1_7_1_3.block_append 1881 418 2210 2338 128 128 256 10158403853 5456165664 15614569517 cost_1881_418_block14 cost_1881_418_block15 rfl rfl rfl

private theorem cost_1881_418_join0_16 : P1_7_1_3.blockEstimate 1881 418 2466 251 = 2366425131 :=
  @P1_7_1_3.block_append 1881 418 2466 2594 128 123 251 2073129760 293295371 2366425131 cost_1881_418_block16 cost_1881_418_block17 rfl rfl rfl

private theorem cost_1881_418_join1_0 : P1_7_1_3.blockEstimate 1881 418 418 512 = 33507856961 :=
  @P1_7_1_3.block_append 1881 418 418 674 256 256 512 4780397376 28727459585 33507856961 cost_1881_418_join0_0 cost_1881_418_join0_2 rfl rfl rfl

private theorem cost_1881_418_join1_2 : P1_7_1_3.blockEstimate 1881 418 930 512 = 128965223424 :=
  @P1_7_1_3.block_append 1881 418 930 1186 256 256 512 56876306944 72088916480 128965223424 cost_1881_418_join0_4 cost_1881_418_join0_6 rfl rfl rfl

private theorem cost_1881_418_join1_4 : P1_7_1_3.blockEstimate 1881 418 1442 512 = 133615684556 :=
  @P1_7_1_3.block_append 1881 418 1442 1698 256 256 512 73242219008 60373465548 133615684556 cost_1881_418_join0_8 cost_1881_418_join0_10 rfl rfl rfl

private theorem cost_1881_418_join1_6 : P1_7_1_3.blockEstimate 1881 418 1954 512 = 53109108458 :=
  @P1_7_1_3.block_append 1881 418 1954 2210 256 256 512 37494538941 15614569517 53109108458 cost_1881_418_join0_12 cost_1881_418_join0_14 rfl rfl rfl

private theorem cost_1881_418_join2_0 : P1_7_1_3.blockEstimate 1881 418 418 1024 = 162473080385 :=
  @P1_7_1_3.block_append 1881 418 418 930 512 512 1024 33507856961 128965223424 162473080385 cost_1881_418_join1_0 cost_1881_418_join1_2 rfl rfl rfl

private theorem cost_1881_418_join2_2 : P1_7_1_3.blockEstimate 1881 418 1442 1024 = 186724793014 :=
  @P1_7_1_3.block_append 1881 418 1442 1954 512 512 1024 133615684556 53109108458 186724793014 cost_1881_418_join1_4 cost_1881_418_join1_6 rfl rfl rfl

private theorem cost_1881_418_join3_0 : P1_7_1_3.blockEstimate 1881 418 418 2048 = 349197873399 :=
  @P1_7_1_3.block_append 1881 418 418 1442 1024 1024 2048 162473080385 186724793014 349197873399 cost_1881_418_join2_0 cost_1881_418_join2_2 rfl rfl rfl

private theorem cost_1881_418_join4_0 : P1_7_1_3.blockEstimate 1881 418 418 2299 = 351564298530 :=
  @P1_7_1_3.block_append 1881 418 418 2466 2048 251 2299 349197873399 2366425131 351564298530 cost_1881_418_join3_0 cost_1881_418_join0_16 rfl rfl rfl

private theorem cost_1881_418_total : P1_7_1_3.momentEstimate 1881 418 = 351564298530 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1881 + 418 = 2299 by decide]
  exact cost_1881_418_join4_0

theorem moment1881_418 : P1_7_1.groupedPoleMoment 1881 418 ≤ 351564298530 :=
  (P1_7_1_3.grouped_bound 1881 418).trans_eq cost_1881_418_total
private theorem cost_1882_420_block0 : P1_7_1_3.blockEstimate 1882 420 420 128 = 639227680 := by decide +kernel

private theorem cost_1882_420_block1 : P1_7_1_3.blockEstimate 1882 420 548 128 = 4143998752 := by decide +kernel

private theorem cost_1882_420_block2 : P1_7_1_3.blockEstimate 1882 420 676 128 = 10384504608 := by decide +kernel

private theorem cost_1882_420_block3 : P1_7_1_3.blockEstimate 1882 420 804 128 = 18374609959 := by decide +kernel

private theorem cost_1882_420_block4 : P1_7_1_3.blockEstimate 1882 420 932 128 = 25729741696 := by decide +kernel

private theorem cost_1882_420_block5 : P1_7_1_3.blockEstimate 1882 420 1060 128 = 31330644864 := by decide +kernel

private theorem cost_1882_420_block6 : P1_7_1_3.blockEstimate 1882 420 1188 128 = 35165746048 := by decide +kernel

private theorem cost_1882_420_block7 : P1_7_1_3.blockEstimate 1882 420 1316 128 = 37235045248 := by decide +kernel

private theorem cost_1882_420_block8 : P1_7_1_3.blockEstimate 1882 420 1444 128 = 37538542464 := by decide +kernel

private theorem cost_1882_420_block9 : P1_7_1_3.blockEstimate 1882 420 1572 128 = 36076237696 := by decide +kernel

private theorem cost_1882_420_block10 : P1_7_1_3.blockEstimate 1882 420 1700 128 = 32848130944 := by decide +kernel

private theorem cost_1882_420_block11 : P1_7_1_3.blockEstimate 1882 420 1828 128 = 27892949644 := by decide +kernel

private theorem cost_1882_420_block12 : P1_7_1_3.blockEstimate 1882 420 1956 128 = 21929025586 := by decide +kernel

private theorem cost_1882_420_block13 : P1_7_1_3.blockEstimate 1882 420 2084 128 = 15888926991 := by decide +kernel

private theorem cost_1882_420_block14 : P1_7_1_3.blockEstimate 1882 420 2212 128 = 10288863769 := by decide +kernel

private theorem cost_1882_420_block15 : P1_7_1_3.blockEstimate 1882 420 2340 128 = 5555958000 := by decide +kernel

private theorem cost_1882_420_block16 : P1_7_1_3.blockEstimate 1882 420 2468 128 = 2136272112 := by decide +kernel

private theorem cost_1882_420_block17 : P1_7_1_3.blockEstimate 1882 420 2596 126 = 314943728 := by decide +kernel

private theorem cost_1882_420_join0_0 : P1_7_1_3.blockEstimate 1882 420 420 256 = 4783226432 :=
  @P1_7_1_3.block_append 1882 420 420 548 128 128 256 639227680 4143998752 4783226432 cost_1882_420_block0 cost_1882_420_block1 rfl rfl rfl

private theorem cost_1882_420_join0_2 : P1_7_1_3.blockEstimate 1882 420 676 256 = 28759114567 :=
  @P1_7_1_3.block_append 1882 420 676 804 128 128 256 10384504608 18374609959 28759114567 cost_1882_420_block2 cost_1882_420_block3 rfl rfl rfl

private theorem cost_1882_420_join0_4 : P1_7_1_3.blockEstimate 1882 420 932 256 = 57060386560 :=
  @P1_7_1_3.block_append 1882 420 932 1060 128 128 256 25729741696 31330644864 57060386560 cost_1882_420_block4 cost_1882_420_block5 rfl rfl rfl

private theorem cost_1882_420_join0_6 : P1_7_1_3.blockEstimate 1882 420 1188 256 = 72400791296 :=
  @P1_7_1_3.block_append 1882 420 1188 1316 128 128 256 35165746048 37235045248 72400791296 cost_1882_420_block6 cost_1882_420_block7 rfl rfl rfl

private theorem cost_1882_420_join0_8 : P1_7_1_3.blockEstimate 1882 420 1444 256 = 73614780160 :=
  @P1_7_1_3.block_append 1882 420 1444 1572 128 128 256 37538542464 36076237696 73614780160 cost_1882_420_block8 cost_1882_420_block9 rfl rfl rfl

private theorem cost_1882_420_join0_10 : P1_7_1_3.blockEstimate 1882 420 1700 256 = 60741080588 :=
  @P1_7_1_3.block_append 1882 420 1700 1828 128 128 256 32848130944 27892949644 60741080588 cost_1882_420_block10 cost_1882_420_block11 rfl rfl rfl

private theorem cost_1882_420_join0_12 : P1_7_1_3.blockEstimate 1882 420 1956 256 = 37817952577 :=
  @P1_7_1_3.block_append 1882 420 1956 2084 128 128 256 21929025586 15888926991 37817952577 cost_1882_420_block12 cost_1882_420_block13 rfl rfl rfl

private theorem cost_1882_420_join0_14 : P1_7_1_3.blockEstimate 1882 420 2212 256 = 15844821769 :=
  @P1_7_1_3.block_append 1882 420 2212 2340 128 128 256 10288863769 5555958000 15844821769 cost_1882_420_block14 cost_1882_420_block15 rfl rfl rfl

private theorem cost_1882_420_join0_16 : P1_7_1_3.blockEstimate 1882 420 2468 254 = 2451215840 :=
  @P1_7_1_3.block_append 1882 420 2468 2596 128 126 254 2136272112 314943728 2451215840 cost_1882_420_block16 cost_1882_420_block17 rfl rfl rfl

private theorem cost_1882_420_join1_0 : P1_7_1_3.blockEstimate 1882 420 420 512 = 33542340999 :=
  @P1_7_1_3.block_append 1882 420 420 676 256 256 512 4783226432 28759114567 33542340999 cost_1882_420_join0_0 cost_1882_420_join0_2 rfl rfl rfl

private theorem cost_1882_420_join1_2 : P1_7_1_3.blockEstimate 1882 420 932 512 = 129461177856 :=
  @P1_7_1_3.block_append 1882 420 932 1188 256 256 512 57060386560 72400791296 129461177856 cost_1882_420_join0_4 cost_1882_420_join0_6 rfl rfl rfl

private theorem cost_1882_420_join1_4 : P1_7_1_3.blockEstimate 1882 420 1444 512 = 134355860748 :=
  @P1_7_1_3.block_append 1882 420 1444 1700 256 256 512 73614780160 60741080588 134355860748 cost_1882_420_join0_8 cost_1882_420_join0_10 rfl rfl rfl

private theorem cost_1882_420_join1_6 : P1_7_1_3.blockEstimate 1882 420 1956 512 = 53662774346 :=
  @P1_7_1_3.block_append 1882 420 1956 2212 256 256 512 37817952577 15844821769 53662774346 cost_1882_420_join0_12 cost_1882_420_join0_14 rfl rfl rfl

private theorem cost_1882_420_join2_0 : P1_7_1_3.blockEstimate 1882 420 420 1024 = 163003518855 :=
  @P1_7_1_3.block_append 1882 420 420 932 512 512 1024 33542340999 129461177856 163003518855 cost_1882_420_join1_0 cost_1882_420_join1_2 rfl rfl rfl

private theorem cost_1882_420_join2_2 : P1_7_1_3.blockEstimate 1882 420 1444 1024 = 188018635094 :=
  @P1_7_1_3.block_append 1882 420 1444 1956 512 512 1024 134355860748 53662774346 188018635094 cost_1882_420_join1_4 cost_1882_420_join1_6 rfl rfl rfl

private theorem cost_1882_420_join3_0 : P1_7_1_3.blockEstimate 1882 420 420 2048 = 351022153949 :=
  @P1_7_1_3.block_append 1882 420 420 1444 1024 1024 2048 163003518855 188018635094 351022153949 cost_1882_420_join2_0 cost_1882_420_join2_2 rfl rfl rfl

private theorem cost_1882_420_join4_0 : P1_7_1_3.blockEstimate 1882 420 420 2302 = 353473369789 :=
  @P1_7_1_3.block_append 1882 420 420 2468 2048 254 2302 351022153949 2451215840 353473369789 cost_1882_420_join3_0 cost_1882_420_join0_16 rfl rfl rfl

private theorem cost_1882_420_total : P1_7_1_3.momentEstimate 1882 420 = 353473369789 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1882 + 420 = 2302 by decide]
  exact cost_1882_420_join4_0

theorem moment1882_420 : P1_7_1.groupedPoleMoment 1882 420 ≤ 353473369789 :=
  (P1_7_1_3.grouped_bound 1882 420).trans_eq cost_1882_420_total

end Research6966.HelperRescueCatalogue

end Merged6967_Near6967RescueMoment15

section Merged6967_Near6967RescueMoment16
set_option Elab.async false


set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem cost_1883_408_block0 : P1_7_1_3.blockEstimate 1883 408 408 128 = 639585440 := by decide +kernel

private theorem cost_1883_408_block1 : P1_7_1_3.blockEstimate 1883 408 536 128 = 4146470048 := by decide +kernel

private theorem cost_1883_408_block2 : P1_7_1_3.blockEstimate 1883 408 664 128 = 10391186592 := by decide +kernel

private theorem cost_1883_408_block3 : P1_7_1_3.blockEstimate 1883 408 792 128 = 18306453354 := by decide +kernel

private theorem cost_1883_408_block4 : P1_7_1_3.blockEstimate 1883 408 920 128 = 25426240832 := by decide +kernel

private theorem cost_1883_408_block5 : P1_7_1_3.blockEstimate 1883 408 1048 128 = 30833993024 := by decide +kernel

private theorem cost_1883_408_block6 : P1_7_1_3.blockEstimate 1883 408 1176 128 = 34526274880 := by decide +kernel

private theorem cost_1883_408_block7 : P1_7_1_3.blockEstimate 1883 408 1304 128 = 36503086400 := by decide +kernel

private theorem cost_1883_408_block8 : P1_7_1_3.blockEstimate 1883 408 1432 128 = 36764427584 := by decide +kernel

private theorem cost_1883_408_block9 : P1_7_1_3.blockEstimate 1883 408 1560 128 = 35310298432 := by decide +kernel

private theorem cost_1883_408_block10 : P1_7_1_3.blockEstimate 1883 408 1688 128 = 32140698944 := by decide +kernel

private theorem cost_1883_408_block11 : P1_7_1_3.blockEstimate 1883 408 1816 128 = 27277617940 := by decide +kernel

private theorem cost_1883_408_block12 : P1_7_1_3.blockEstimate 1883 408 1944 128 = 21355014005 := by decide +kernel

private theorem cost_1883_408_block13 : P1_7_1_3.blockEstimate 1883 408 2072 128 = 15364998412 := by decide +kernel

private theorem cost_1883_408_block14 : P1_7_1_3.blockEstimate 1883 408 2200 128 = 9839463898 := by decide +kernel

private theorem cost_1883_408_block15 : P1_7_1_3.blockEstimate 1883 408 2328 128 = 5208696928 := by decide +kernel

private theorem cost_1883_408_block16 : P1_7_1_3.blockEstimate 1883 408 2456 128 = 1914482784 := by decide +kernel

private theorem cost_1883_408_block17 : P1_7_1_3.blockEstimate 1883 408 2584 115 = 241065371 := by decide +kernel

private theorem cost_1883_408_join0_0 : P1_7_1_3.blockEstimate 1883 408 408 256 = 4786055488 :=
  @P1_7_1_3.block_append 1883 408 408 536 128 128 256 639585440 4146470048 4786055488 cost_1883_408_block0 cost_1883_408_block1 rfl rfl rfl

private theorem cost_1883_408_join0_2 : P1_7_1_3.blockEstimate 1883 408 664 256 = 28697639946 :=
  @P1_7_1_3.block_append 1883 408 664 792 128 128 256 10391186592 18306453354 28697639946 cost_1883_408_block2 cost_1883_408_block3 rfl rfl rfl

private theorem cost_1883_408_join0_4 : P1_7_1_3.blockEstimate 1883 408 920 256 = 56260233856 :=
  @P1_7_1_3.block_append 1883 408 920 1048 128 128 256 25426240832 30833993024 56260233856 cost_1883_408_block4 cost_1883_408_block5 rfl rfl rfl

private theorem cost_1883_408_join0_6 : P1_7_1_3.blockEstimate 1883 408 1176 256 = 71029361280 :=
  @P1_7_1_3.block_append 1883 408 1176 1304 128 128 256 34526274880 36503086400 71029361280 cost_1883_408_block6 cost_1883_408_block7 rfl rfl rfl

private theorem cost_1883_408_join0_8 : P1_7_1_3.blockEstimate 1883 408 1432 256 = 72074726016 :=
  @P1_7_1_3.block_append 1883 408 1432 1560 128 128 256 36764427584 35310298432 72074726016 cost_1883_408_block8 cost_1883_408_block9 rfl rfl rfl

private theorem cost_1883_408_join0_10 : P1_7_1_3.blockEstimate 1883 408 1688 256 = 59418316884 :=
  @P1_7_1_3.block_append 1883 408 1688 1816 128 128 256 32140698944 27277617940 59418316884 cost_1883_408_block10 cost_1883_408_block11 rfl rfl rfl

private theorem cost_1883_408_join0_12 : P1_7_1_3.blockEstimate 1883 408 1944 256 = 36720012417 :=
  @P1_7_1_3.block_append 1883 408 1944 2072 128 128 256 21355014005 15364998412 36720012417 cost_1883_408_block12 cost_1883_408_block13 rfl rfl rfl

private theorem cost_1883_408_join0_14 : P1_7_1_3.blockEstimate 1883 408 2200 256 = 15048160826 :=
  @P1_7_1_3.block_append 1883 408 2200 2328 128 128 256 9839463898 5208696928 15048160826 cost_1883_408_block14 cost_1883_408_block15 rfl rfl rfl

private theorem cost_1883_408_join0_16 : P1_7_1_3.blockEstimate 1883 408 2456 243 = 2155548155 :=
  @P1_7_1_3.block_append 1883 408 2456 2584 128 115 243 1914482784 241065371 2155548155 cost_1883_408_block16 cost_1883_408_block17 rfl rfl rfl

private theorem cost_1883_408_join1_0 : P1_7_1_3.blockEstimate 1883 408 408 512 = 33483695434 :=
  @P1_7_1_3.block_append 1883 408 408 664 256 256 512 4786055488 28697639946 33483695434 cost_1883_408_join0_0 cost_1883_408_join0_2 rfl rfl rfl

private theorem cost_1883_408_join1_2 : P1_7_1_3.blockEstimate 1883 408 920 512 = 127289595136 :=
  @P1_7_1_3.block_append 1883 408 920 1176 256 256 512 56260233856 71029361280 127289595136 cost_1883_408_join0_4 cost_1883_408_join0_6 rfl rfl rfl

private theorem cost_1883_408_join1_4 : P1_7_1_3.blockEstimate 1883 408 1432 512 = 131493042900 :=
  @P1_7_1_3.block_append 1883 408 1432 1688 256 256 512 72074726016 59418316884 131493042900 cost_1883_408_join0_8 cost_1883_408_join0_10 rfl rfl rfl

private theorem cost_1883_408_join1_6 : P1_7_1_3.blockEstimate 1883 408 1944 512 = 51768173243 :=
  @P1_7_1_3.block_append 1883 408 1944 2200 256 256 512 36720012417 15048160826 51768173243 cost_1883_408_join0_12 cost_1883_408_join0_14 rfl rfl rfl

private theorem cost_1883_408_join2_0 : P1_7_1_3.blockEstimate 1883 408 408 1024 = 160773290570 :=
  @P1_7_1_3.block_append 1883 408 408 920 512 512 1024 33483695434 127289595136 160773290570 cost_1883_408_join1_0 cost_1883_408_join1_2 rfl rfl rfl

private theorem cost_1883_408_join2_2 : P1_7_1_3.blockEstimate 1883 408 1432 1024 = 183261216143 :=
  @P1_7_1_3.block_append 1883 408 1432 1944 512 512 1024 131493042900 51768173243 183261216143 cost_1883_408_join1_4 cost_1883_408_join1_6 rfl rfl rfl

private theorem cost_1883_408_join3_0 : P1_7_1_3.blockEstimate 1883 408 408 2048 = 344034506713 :=
  @P1_7_1_3.block_append 1883 408 408 1432 1024 1024 2048 160773290570 183261216143 344034506713 cost_1883_408_join2_0 cost_1883_408_join2_2 rfl rfl rfl

private theorem cost_1883_408_join4_0 : P1_7_1_3.blockEstimate 1883 408 408 2291 = 346190054868 :=
  @P1_7_1_3.block_append 1883 408 408 2456 2048 243 2291 344034506713 2155548155 346190054868 cost_1883_408_join3_0 cost_1883_408_join0_16 rfl rfl rfl

private theorem cost_1883_408_total : P1_7_1_3.momentEstimate 1883 408 = 346190054868 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1883 + 408 = 2291 by decide]
  exact cost_1883_408_join4_0

theorem moment1883_408 : P1_7_1.groupedPoleMoment 1883 408 ≤ 346190054868 :=
  (P1_7_1_3.grouped_bound 1883 408).trans_eq cost_1883_408_total
private theorem cost_1883_418_block0 : P1_7_1_3.blockEstimate 1883 418 418 128 = 639585440 := by decide +kernel

private theorem cost_1883_418_block1 : P1_7_1_3.blockEstimate 1883 418 546 128 = 4146470048 := by decide +kernel

private theorem cost_1883_418_block2 : P1_7_1_3.blockEstimate 1883 418 674 128 = 10391186592 := by decide +kernel

private theorem cost_1883_418_block3 : P1_7_1_3.blockEstimate 1883 418 802 128 = 18375339779 := by decide +kernel

private theorem cost_1883_418_block4 : P1_7_1_3.blockEstimate 1883 418 930 128 = 25697290112 := by decide +kernel

private theorem cost_1883_418_block5 : P1_7_1_3.blockEstimate 1883 418 1058 128 = 31271585664 := by decide +kernel

private theorem cost_1883_418_block6 : P1_7_1_3.blockEstimate 1883 418 1186 128 = 35088467840 := by decide +kernel

private theorem cost_1883_418_block7 : P1_7_1_3.blockEstimate 1883 418 1314 128 = 37147936640 := by decide +kernel

private theorem cost_1883_418_block8 : P1_7_1_3.blockEstimate 1883 418 1442 128 = 37449992064 := by decide +kernel

private theorem cost_1883_418_block9 : P1_7_1_3.blockEstimate 1883 418 1570 128 = 35994634112 := by decide +kernel

private theorem cost_1883_418_block10 : P1_7_1_3.blockEstimate 1883 418 1698 128 = 32781862784 := by decide +kernel

private theorem cost_1883_418_block11 : P1_7_1_3.blockEstimate 1883 418 1826 128 = 27845963402 := by decide +kernel

private theorem cost_1883_418_block12 : P1_7_1_3.blockEstimate 1883 418 1954 128 = 21885991104 := by decide +kernel

private theorem cost_1883_418_block13 : P1_7_1_3.blockEstimate 1883 418 2082 128 = 15848406485 := by decide +kernel

private theorem cost_1883_418_block14 : P1_7_1_3.blockEstimate 1883 418 2210 128 = 10252841430 := by decide +kernel

private theorem cost_1883_418_block15 : P1_7_1_3.blockEstimate 1883 418 2338 128 = 5526984400 := by decide +kernel

private theorem cost_1883_418_block16 : P1_7_1_3.blockEstimate 1883 418 2466 128 = 2116725456 := by decide +kernel

private theorem cost_1883_418_block17 : P1_7_1_3.blockEstimate 1883 418 2594 125 = 307838672 := by decide +kernel

private theorem cost_1883_418_join0_0 : P1_7_1_3.blockEstimate 1883 418 418 256 = 4786055488 :=
  @P1_7_1_3.block_append 1883 418 418 546 128 128 256 639585440 4146470048 4786055488 cost_1883_418_block0 cost_1883_418_block1 rfl rfl rfl

private theorem cost_1883_418_join0_2 : P1_7_1_3.blockEstimate 1883 418 674 256 = 28766526371 :=
  @P1_7_1_3.block_append 1883 418 674 802 128 128 256 10391186592 18375339779 28766526371 cost_1883_418_block2 cost_1883_418_block3 rfl rfl rfl

private theorem cost_1883_418_join0_4 : P1_7_1_3.blockEstimate 1883 418 930 256 = 56968875776 :=
  @P1_7_1_3.block_append 1883 418 930 1058 128 128 256 25697290112 31271585664 56968875776 cost_1883_418_block4 cost_1883_418_block5 rfl rfl rfl

private theorem cost_1883_418_join0_6 : P1_7_1_3.blockEstimate 1883 418 1186 256 = 72236404480 :=
  @P1_7_1_3.block_append 1883 418 1186 1314 128 128 256 35088467840 37147936640 72236404480 cost_1883_418_block6 cost_1883_418_block7 rfl rfl rfl

private theorem cost_1883_418_join0_8 : P1_7_1_3.blockEstimate 1883 418 1442 256 = 73444626176 :=
  @P1_7_1_3.block_append 1883 418 1442 1570 128 128 256 37449992064 35994634112 73444626176 cost_1883_418_block8 cost_1883_418_block9 rfl rfl rfl

private theorem cost_1883_418_join0_10 : P1_7_1_3.blockEstimate 1883 418 1698 256 = 60627826186 :=
  @P1_7_1_3.block_append 1883 418 1698 1826 128 128 256 32781862784 27845963402 60627826186 cost_1883_418_block10 cost_1883_418_block11 rfl rfl rfl

private theorem cost_1883_418_join0_12 : P1_7_1_3.blockEstimate 1883 418 1954 256 = 37734397589 :=
  @P1_7_1_3.block_append 1883 418 1954 2082 128 128 256 21885991104 15848406485 37734397589 cost_1883_418_block12 cost_1883_418_block13 rfl rfl rfl

private theorem cost_1883_418_join0_14 : P1_7_1_3.blockEstimate 1883 418 2210 256 = 15779825830 :=
  @P1_7_1_3.block_append 1883 418 2210 2338 128 128 256 10252841430 5526984400 15779825830 cost_1883_418_block14 cost_1883_418_block15 rfl rfl rfl

private theorem cost_1883_418_join0_16 : P1_7_1_3.blockEstimate 1883 418 2466 253 = 2424564128 :=
  @P1_7_1_3.block_append 1883 418 2466 2594 128 125 253 2116725456 307838672 2424564128 cost_1883_418_block16 cost_1883_418_block17 rfl rfl rfl

private theorem cost_1883_418_join1_0 : P1_7_1_3.blockEstimate 1883 418 418 512 = 33552581859 :=
  @P1_7_1_3.block_append 1883 418 418 674 256 256 512 4786055488 28766526371 33552581859 cost_1883_418_join0_0 cost_1883_418_join0_2 rfl rfl rfl

private theorem cost_1883_418_join1_2 : P1_7_1_3.blockEstimate 1883 418 930 512 = 129205280256 :=
  @P1_7_1_3.block_append 1883 418 930 1186 256 256 512 56968875776 72236404480 129205280256 cost_1883_418_join0_4 cost_1883_418_join0_6 rfl rfl rfl

private theorem cost_1883_418_join1_4 : P1_7_1_3.blockEstimate 1883 418 1442 512 = 134072452362 :=
  @P1_7_1_3.block_append 1883 418 1442 1698 256 256 512 73444626176 60627826186 134072452362 cost_1883_418_join0_8 cost_1883_418_join0_10 rfl rfl rfl

private theorem cost_1883_418_join1_6 : P1_7_1_3.blockEstimate 1883 418 1954 512 = 53514223419 :=
  @P1_7_1_3.block_append 1883 418 1954 2210 256 256 512 37734397589 15779825830 53514223419 cost_1883_418_join0_12 cost_1883_418_join0_14 rfl rfl rfl

private theorem cost_1883_418_join2_0 : P1_7_1_3.blockEstimate 1883 418 418 1024 = 162757862115 :=
  @P1_7_1_3.block_append 1883 418 418 930 512 512 1024 33552581859 129205280256 162757862115 cost_1883_418_join1_0 cost_1883_418_join1_2 rfl rfl rfl

private theorem cost_1883_418_join2_2 : P1_7_1_3.blockEstimate 1883 418 1442 1024 = 187586675781 :=
  @P1_7_1_3.block_append 1883 418 1442 1954 512 512 1024 134072452362 53514223419 187586675781 cost_1883_418_join1_4 cost_1883_418_join1_6 rfl rfl rfl

private theorem cost_1883_418_join3_0 : P1_7_1_3.blockEstimate 1883 418 418 2048 = 350344537896 :=
  @P1_7_1_3.block_append 1883 418 418 1442 1024 1024 2048 162757862115 187586675781 350344537896 cost_1883_418_join2_0 cost_1883_418_join2_2 rfl rfl rfl

private theorem cost_1883_418_join4_0 : P1_7_1_3.blockEstimate 1883 418 418 2301 = 352769102024 :=
  @P1_7_1_3.block_append 1883 418 418 2466 2048 253 2301 350344537896 2424564128 352769102024 cost_1883_418_join3_0 cost_1883_418_join0_16 rfl rfl rfl

private theorem cost_1883_418_total : P1_7_1_3.momentEstimate 1883 418 = 352769102024 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1883 + 418 = 2301 by decide]
  exact cost_1883_418_join4_0

theorem moment1883_418 : P1_7_1.groupedPoleMoment 1883 418 ≤ 352769102024 :=
  (P1_7_1_3.grouped_bound 1883 418).trans_eq cost_1883_418_total
private theorem cost_1948_419_block0 : P1_7_1_3.blockEstimate 1948 419 419 128 = 662839840 := by decide +kernel

private theorem cost_1948_419_block1 : P1_7_1_3.blockEstimate 1948 419 547 128 = 4307104288 := by decide +kernel

private theorem cost_1948_419_block2 : P1_7_1_3.blockEstimate 1948 419 675 128 = 10825515552 := by decide +kernel

private theorem cost_1948_419_block3 : P1_7_1_3.blockEstimate 1948 419 803 128 = 19217096535 := by decide +kernel

private theorem cost_1948_419_block4 : P1_7_1_3.blockEstimate 1948 419 931 128 = 27005919360 := by decide +kernel

private theorem cost_1948_419_block5 : P1_7_1_3.blockEstimate 1948 419 1059 128 = 33044242560 := by decide +kernel

private theorem cost_1948_419_block6 : P1_7_1_3.blockEstimate 1948 419 1187 128 = 37320958080 := by decide +kernel

private theorem cost_1948_419_block7 : P1_7_1_3.blockEstimate 1948 419 1315 128 = 39836065920 := by decide +kernel

private theorem cost_1948_419_block8 : P1_7_1_3.blockEstimate 1948 419 1443 128 = 40589566080 := by decide +kernel

private theorem cost_1948_419_block9 : P1_7_1_3.blockEstimate 1948 419 1571 128 = 39581458560 := by decide +kernel

private theorem cost_1948_419_block10 : P1_7_1_3.blockEstimate 1948 419 1699 128 = 36811743360 := by decide +kernel

private theorem cost_1948_419_block11 : P1_7_1_3.blockEstimate 1948 419 1827 128 = 32280458474 := by decide +kernel

private theorem cost_1948_419_block12 : P1_7_1_3.blockEstimate 1948 419 1955 128 = 26248365397 := by decide +kernel

private theorem cost_1948_419_block13 : P1_7_1_3.blockEstimate 1948 419 2083 128 = 19796589888 := by decide +kernel

private theorem cost_1948_419_block14 : P1_7_1_3.blockEstimate 1948 419 2211 128 = 13605767479 := by decide +kernel

private theorem cost_1948_419_block15 : P1_7_1_3.blockEstimate 1948 419 2339 128 = 8136627375 := by decide +kernel

private theorem cost_1948_419_block16 : P1_7_1_3.blockEstimate 1948 419 2467 128 = 3830727712 := by decide +kernel

private theorem cost_1948_419_block17 : P1_7_1_3.blockEstimate 1948 419 2595 128 = 1062204448 := by decide +kernel

private theorem cost_1948_419_block18 : P1_7_1_3.blockEstimate 1948 419 2723 63 = 42896400 := by decide +kernel

private theorem cost_1948_419_join0_0 : P1_7_1_3.blockEstimate 1948 419 419 256 = 4969944128 :=
  @P1_7_1_3.block_append 1948 419 419 547 128 128 256 662839840 4307104288 4969944128 cost_1948_419_block0 cost_1948_419_block1 rfl rfl rfl

private theorem cost_1948_419_join0_2 : P1_7_1_3.blockEstimate 1948 419 675 256 = 30042612087 :=
  @P1_7_1_3.block_append 1948 419 675 803 128 128 256 10825515552 19217096535 30042612087 cost_1948_419_block2 cost_1948_419_block3 rfl rfl rfl

private theorem cost_1948_419_join0_4 : P1_7_1_3.blockEstimate 1948 419 931 256 = 60050161920 :=
  @P1_7_1_3.block_append 1948 419 931 1059 128 128 256 27005919360 33044242560 60050161920 cost_1948_419_block4 cost_1948_419_block5 rfl rfl rfl

private theorem cost_1948_419_join0_6 : P1_7_1_3.blockEstimate 1948 419 1187 256 = 77157024000 :=
  @P1_7_1_3.block_append 1948 419 1187 1315 128 128 256 37320958080 39836065920 77157024000 cost_1948_419_block6 cost_1948_419_block7 rfl rfl rfl

private theorem cost_1948_419_join0_8 : P1_7_1_3.blockEstimate 1948 419 1443 256 = 80171024640 :=
  @P1_7_1_3.block_append 1948 419 1443 1571 128 128 256 40589566080 39581458560 80171024640 cost_1948_419_block8 cost_1948_419_block9 rfl rfl rfl

private theorem cost_1948_419_join0_10 : P1_7_1_3.blockEstimate 1948 419 1699 256 = 69092201834 :=
  @P1_7_1_3.block_append 1948 419 1699 1827 128 128 256 36811743360 32280458474 69092201834 cost_1948_419_block10 cost_1948_419_block11 rfl rfl rfl

private theorem cost_1948_419_join0_12 : P1_7_1_3.blockEstimate 1948 419 1955 256 = 46044955285 :=
  @P1_7_1_3.block_append 1948 419 1955 2083 128 128 256 26248365397 19796589888 46044955285 cost_1948_419_block12 cost_1948_419_block13 rfl rfl rfl

private theorem cost_1948_419_join0_14 : P1_7_1_3.blockEstimate 1948 419 2211 256 = 21742394854 :=
  @P1_7_1_3.block_append 1948 419 2211 2339 128 128 256 13605767479 8136627375 21742394854 cost_1948_419_block14 cost_1948_419_block15 rfl rfl rfl

private theorem cost_1948_419_join0_16 : P1_7_1_3.blockEstimate 1948 419 2467 256 = 4892932160 :=
  @P1_7_1_3.block_append 1948 419 2467 2595 128 128 256 3830727712 1062204448 4892932160 cost_1948_419_block16 cost_1948_419_block17 rfl rfl rfl

private theorem cost_1948_419_join1_0 : P1_7_1_3.blockEstimate 1948 419 419 512 = 35012556215 :=
  @P1_7_1_3.block_append 1948 419 419 675 256 256 512 4969944128 30042612087 35012556215 cost_1948_419_join0_0 cost_1948_419_join0_2 rfl rfl rfl

private theorem cost_1948_419_join1_2 : P1_7_1_3.blockEstimate 1948 419 931 512 = 137207185920 :=
  @P1_7_1_3.block_append 1948 419 931 1187 256 256 512 60050161920 77157024000 137207185920 cost_1948_419_join0_4 cost_1948_419_join0_6 rfl rfl rfl

private theorem cost_1948_419_join1_4 : P1_7_1_3.blockEstimate 1948 419 1443 512 = 149263226474 :=
  @P1_7_1_3.block_append 1948 419 1443 1699 256 256 512 80171024640 69092201834 149263226474 cost_1948_419_join0_8 cost_1948_419_join0_10 rfl rfl rfl

private theorem cost_1948_419_join1_6 : P1_7_1_3.blockEstimate 1948 419 1955 512 = 67787350139 :=
  @P1_7_1_3.block_append 1948 419 1955 2211 256 256 512 46044955285 21742394854 67787350139 cost_1948_419_join0_12 cost_1948_419_join0_14 rfl rfl rfl

private theorem cost_1948_419_join1_8 : P1_7_1_3.blockEstimate 1948 419 2467 319 = 4935828560 :=
  @P1_7_1_3.block_append 1948 419 2467 2723 256 63 319 4892932160 42896400 4935828560 cost_1948_419_join0_16 cost_1948_419_block18 rfl rfl rfl

private theorem cost_1948_419_join2_0 : P1_7_1_3.blockEstimate 1948 419 419 1024 = 172219742135 :=
  @P1_7_1_3.block_append 1948 419 419 931 512 512 1024 35012556215 137207185920 172219742135 cost_1948_419_join1_0 cost_1948_419_join1_2 rfl rfl rfl

private theorem cost_1948_419_join2_2 : P1_7_1_3.blockEstimate 1948 419 1443 1024 = 217050576613 :=
  @P1_7_1_3.block_append 1948 419 1443 1955 512 512 1024 149263226474 67787350139 217050576613 cost_1948_419_join1_4 cost_1948_419_join1_6 rfl rfl rfl

private theorem cost_1948_419_join3_0 : P1_7_1_3.blockEstimate 1948 419 419 2048 = 389270318748 :=
  @P1_7_1_3.block_append 1948 419 419 1443 1024 1024 2048 172219742135 217050576613 389270318748 cost_1948_419_join2_0 cost_1948_419_join2_2 rfl rfl rfl

private theorem cost_1948_419_join4_0 : P1_7_1_3.blockEstimate 1948 419 419 2367 = 394206147308 :=
  @P1_7_1_3.block_append 1948 419 419 2467 2048 319 2367 389270318748 4935828560 394206147308 cost_1948_419_join3_0 cost_1948_419_join1_8 rfl rfl rfl

private theorem cost_1948_419_total : P1_7_1_3.momentEstimate 1948 419 = 394206147308 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 1948 + 419 = 2367 by decide]
  exact cost_1948_419_join4_0

theorem moment1948_419 : P1_7_1.groupedPoleMoment 1948 419 ≤ 394206147308 :=
  (P1_7_1_3.grouped_bound 1948 419).trans_eq cost_1948_419_total
private theorem cost_2014_445_block0 : P1_7_1_3.blockEstimate 2014 445 445 128 = 686452000 := by decide +kernel

private theorem cost_2014_445_block1 : P1_7_1_3.blockEstimate 2014 445 573 128 = 4470209824 := by decide +kernel

private theorem cost_2014_445_block2 : P1_7_1_3.blockEstimate 2014 445 701 128 = 11266526496 := by decide +kernel

private theorem cost_2014_445_block3 : P1_7_1_3.blockEstimate 2014 445 829 128 = 20193956915 := by decide +kernel

private theorem cost_2014_445_block4 : P1_7_1_3.blockEstimate 2014 445 957 128 = 28992925760 := by decide +kernel

private theorem cost_2014_445_block5 : P1_7_1_3.blockEstimate 2014 445 1085 128 = 35982323776 := by decide +kernel

private theorem cost_2014_445_block6 : P1_7_1_3.blockEstimate 2014 445 1213 128 = 41101062208 := by decide +kernel

private theorem cost_2014_445_block7 : P1_7_1_3.blockEstimate 2014 445 1341 128 = 44349141056 := by decide +kernel

private theorem cost_2014_445_block8 : P1_7_1_3.blockEstimate 2014 445 1469 128 = 45726560320 := by decide +kernel

private theorem cost_2014_445_block9 : P1_7_1_3.blockEstimate 2014 445 1597 128 = 45233320000 := by decide +kernel

private theorem cost_2014_445_block10 : P1_7_1_3.blockEstimate 2014 445 1725 128 = 42869420096 := by decide +kernel

private theorem cost_2014_445_block11 : P1_7_1_3.blockEstimate 2014 445 1853 128 = 38634860608 := by decide +kernel

private theorem cost_2014_445_block12 : P1_7_1_3.blockEstimate 2014 445 1981 128 = 32618853929 := by decide +kernel

private theorem cost_2014_445_block13 : P1_7_1_3.blockEstimate 2014 445 2109 128 = 25735871839 := by decide +kernel

private theorem cost_2014_445_block14 : P1_7_1_3.blockEstimate 2014 445 2237 128 = 18857737693 := by decide +kernel

private theorem cost_2014_445_block15 : P1_7_1_3.blockEstimate 2014 445 2365 128 = 12487455827 := by decide +kernel

private theorem cost_2014_445_block16 : P1_7_1_3.blockEstimate 2014 445 2493 128 = 7045643712 := by decide +kernel

private theorem cost_2014_445_block17 : P1_7_1_3.blockEstimate 2014 445 2621 128 = 2991154624 := by decide +kernel

private theorem cost_2014_445_block18 : P1_7_1_3.blockEstimate 2014 445 2749 128 = 616418752 := by decide +kernel

private theorem cost_2014_445_block19 : P1_7_1_3.blockEstimate 2014 445 2877 27 = 3853836 := by decide +kernel

private theorem cost_2014_445_join0_0 : P1_7_1_3.blockEstimate 2014 445 445 256 = 5156661824 :=
  @P1_7_1_3.block_append 2014 445 445 573 128 128 256 686452000 4470209824 5156661824 cost_2014_445_block0 cost_2014_445_block1 rfl rfl rfl

private theorem cost_2014_445_join0_2 : P1_7_1_3.blockEstimate 2014 445 701 256 = 31460483411 :=
  @P1_7_1_3.block_append 2014 445 701 829 128 128 256 11266526496 20193956915 31460483411 cost_2014_445_block2 cost_2014_445_block3 rfl rfl rfl

private theorem cost_2014_445_join0_4 : P1_7_1_3.blockEstimate 2014 445 957 256 = 64975249536 :=
  @P1_7_1_3.block_append 2014 445 957 1085 128 128 256 28992925760 35982323776 64975249536 cost_2014_445_block4 cost_2014_445_block5 rfl rfl rfl

private theorem cost_2014_445_join0_6 : P1_7_1_3.blockEstimate 2014 445 1213 256 = 85450203264 :=
  @P1_7_1_3.block_append 2014 445 1213 1341 128 128 256 41101062208 44349141056 85450203264 cost_2014_445_block6 cost_2014_445_block7 rfl rfl rfl

private theorem cost_2014_445_join0_8 : P1_7_1_3.blockEstimate 2014 445 1469 256 = 90959880320 :=
  @P1_7_1_3.block_append 2014 445 1469 1597 128 128 256 45726560320 45233320000 90959880320 cost_2014_445_block8 cost_2014_445_block9 rfl rfl rfl

private theorem cost_2014_445_join0_10 : P1_7_1_3.blockEstimate 2014 445 1725 256 = 81504280704 :=
  @P1_7_1_3.block_append 2014 445 1725 1853 128 128 256 42869420096 38634860608 81504280704 cost_2014_445_block10 cost_2014_445_block11 rfl rfl rfl

private theorem cost_2014_445_join0_12 : P1_7_1_3.blockEstimate 2014 445 1981 256 = 58354725768 :=
  @P1_7_1_3.block_append 2014 445 1981 2109 128 128 256 32618853929 25735871839 58354725768 cost_2014_445_block12 cost_2014_445_block13 rfl rfl rfl

private theorem cost_2014_445_join0_14 : P1_7_1_3.blockEstimate 2014 445 2237 256 = 31345193520 :=
  @P1_7_1_3.block_append 2014 445 2237 2365 128 128 256 18857737693 12487455827 31345193520 cost_2014_445_block14 cost_2014_445_block15 rfl rfl rfl

private theorem cost_2014_445_join0_16 : P1_7_1_3.blockEstimate 2014 445 2493 256 = 10036798336 :=
  @P1_7_1_3.block_append 2014 445 2493 2621 128 128 256 7045643712 2991154624 10036798336 cost_2014_445_block16 cost_2014_445_block17 rfl rfl rfl

private theorem cost_2014_445_join0_18 : P1_7_1_3.blockEstimate 2014 445 2749 155 = 620272588 :=
  @P1_7_1_3.block_append 2014 445 2749 2877 128 27 155 616418752 3853836 620272588 cost_2014_445_block18 cost_2014_445_block19 rfl rfl rfl

private theorem cost_2014_445_join1_0 : P1_7_1_3.blockEstimate 2014 445 445 512 = 36617145235 :=
  @P1_7_1_3.block_append 2014 445 445 701 256 256 512 5156661824 31460483411 36617145235 cost_2014_445_join0_0 cost_2014_445_join0_2 rfl rfl rfl

private theorem cost_2014_445_join1_2 : P1_7_1_3.blockEstimate 2014 445 957 512 = 150425452800 :=
  @P1_7_1_3.block_append 2014 445 957 1213 256 256 512 64975249536 85450203264 150425452800 cost_2014_445_join0_4 cost_2014_445_join0_6 rfl rfl rfl

private theorem cost_2014_445_join1_4 : P1_7_1_3.blockEstimate 2014 445 1469 512 = 172464161024 :=
  @P1_7_1_3.block_append 2014 445 1469 1725 256 256 512 90959880320 81504280704 172464161024 cost_2014_445_join0_8 cost_2014_445_join0_10 rfl rfl rfl

private theorem cost_2014_445_join1_6 : P1_7_1_3.blockEstimate 2014 445 1981 512 = 89699919288 :=
  @P1_7_1_3.block_append 2014 445 1981 2237 256 256 512 58354725768 31345193520 89699919288 cost_2014_445_join0_12 cost_2014_445_join0_14 rfl rfl rfl

private theorem cost_2014_445_join1_8 : P1_7_1_3.blockEstimate 2014 445 2493 411 = 10657070924 :=
  @P1_7_1_3.block_append 2014 445 2493 2749 256 155 411 10036798336 620272588 10657070924 cost_2014_445_join0_16 cost_2014_445_join0_18 rfl rfl rfl

private theorem cost_2014_445_join2_0 : P1_7_1_3.blockEstimate 2014 445 445 1024 = 187042598035 :=
  @P1_7_1_3.block_append 2014 445 445 957 512 512 1024 36617145235 150425452800 187042598035 cost_2014_445_join1_0 cost_2014_445_join1_2 rfl rfl rfl

private theorem cost_2014_445_join2_2 : P1_7_1_3.blockEstimate 2014 445 1469 1024 = 262164080312 :=
  @P1_7_1_3.block_append 2014 445 1469 1981 512 512 1024 172464161024 89699919288 262164080312 cost_2014_445_join1_4 cost_2014_445_join1_6 rfl rfl rfl

private theorem cost_2014_445_join3_0 : P1_7_1_3.blockEstimate 2014 445 445 2048 = 449206678347 :=
  @P1_7_1_3.block_append 2014 445 445 1469 1024 1024 2048 187042598035 262164080312 449206678347 cost_2014_445_join2_0 cost_2014_445_join2_2 rfl rfl rfl

private theorem cost_2014_445_join4_0 : P1_7_1_3.blockEstimate 2014 445 445 2459 = 459863749271 :=
  @P1_7_1_3.block_append 2014 445 445 2493 2048 411 2459 449206678347 10657070924 459863749271 cost_2014_445_join3_0 cost_2014_445_join1_8 rfl rfl rfl

private theorem cost_2014_445_total : P1_7_1_3.momentEstimate 2014 445 = 459863749271 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2014 + 445 = 2459 by decide]
  exact cost_2014_445_join4_0

theorem moment2014_445 : P1_7_1.groupedPoleMoment 2014 445 ≤ 459863749271 :=
  (P1_7_1_3.grouped_bound 2014 445).trans_eq cost_2014_445_total
private theorem cost_2015_439_block0 : P1_7_1_3.blockEstimate 2015 439 439 128 = 686809760 := by decide +kernel

private theorem cost_2015_439_block1 : P1_7_1_3.blockEstimate 2015 439 567 128 = 4472681120 := by decide +kernel

private theorem cost_2015_439_block2 : P1_7_1_3.blockEstimate 2015 439 695 128 = 11273208480 := by decide +kernel

private theorem cost_2015_439_block3 : P1_7_1_3.blockEstimate 2015 439 823 128 = 20184439550 := by decide +kernel

private theorem cost_2015_439_block4 : P1_7_1_3.blockEstimate 2015 439 951 128 = 28866041600 := by decide +kernel

private theorem cost_2015_439_block5 : P1_7_1_3.blockEstimate 2015 439 1079 128 = 35746993920 := by decide +kernel

private theorem cost_2015_439_block6 : P1_7_1_3.blockEstimate 2015 439 1207 128 = 40782452480 := by decide +kernel

private theorem cost_2015_439_block7 : P1_7_1_3.blockEstimate 2015 439 1335 128 = 43972417280 := by decide +kernel

private theorem cost_2015_439_block8 : P1_7_1_3.blockEstimate 2015 439 1463 128 = 45316888320 := by decide +kernel

private theorem cost_2015_439_block9 : P1_7_1_3.blockEstimate 2015 439 1591 128 = 44815865600 := by decide +kernel

private theorem cost_2015_439_block10 : P1_7_1_3.blockEstimate 2015 439 1719 128 = 42469349120 := by decide +kernel

private theorem cost_2015_439_block11 : P1_7_1_3.blockEstimate 2015 439 1847 128 = 38277338880 := by decide +kernel

private theorem cost_2015_439_block12 : P1_7_1_3.blockEstimate 2015 439 1975 128 = 32311137664 := by decide +kernel

private theorem cost_2015_439_block13 : P1_7_1_3.blockEstimate 2015 439 2103 128 = 25445782969 := by decide +kernel

private theorem cost_2015_439_block14 : P1_7_1_3.blockEstimate 2015 439 2231 128 = 18591739841 := by decide +kernel

private theorem cost_2015_439_block15 : P1_7_1_3.blockEstimate 2015 439 2359 128 = 12256591464 := by decide +kernel

private theorem cost_2015_439_block16 : P1_7_1_3.blockEstimate 2015 439 2487 128 = 6862645840 := by decide +kernel

private theorem cost_2015_439_block17 : P1_7_1_3.blockEstimate 2015 439 2615 128 = 2866759248 := by decide +kernel

private theorem cost_2015_439_block18 : P1_7_1_3.blockEstimate 2015 439 2743 128 = 561504848 := by decide +kernel

private theorem cost_2015_439_block19 : P1_7_1_3.blockEstimate 2015 439 2871 22 = 2161749 := by decide +kernel

private theorem cost_2015_439_join0_0 : P1_7_1_3.blockEstimate 2015 439 439 256 = 5159490880 :=
  @P1_7_1_3.block_append 2015 439 439 567 128 128 256 686809760 4472681120 5159490880 cost_2015_439_block0 cost_2015_439_block1 rfl rfl rfl

private theorem cost_2015_439_join0_2 : P1_7_1_3.blockEstimate 2015 439 695 256 = 31457648030 :=
  @P1_7_1_3.block_append 2015 439 695 823 128 128 256 11273208480 20184439550 31457648030 cost_2015_439_block2 cost_2015_439_block3 rfl rfl rfl

private theorem cost_2015_439_join0_4 : P1_7_1_3.blockEstimate 2015 439 951 256 = 64613035520 :=
  @P1_7_1_3.block_append 2015 439 951 1079 128 128 256 28866041600 35746993920 64613035520 cost_2015_439_block4 cost_2015_439_block5 rfl rfl rfl

private theorem cost_2015_439_join0_6 : P1_7_1_3.blockEstimate 2015 439 1207 256 = 84754869760 :=
  @P1_7_1_3.block_append 2015 439 1207 1335 128 128 256 40782452480 43972417280 84754869760 cost_2015_439_block6 cost_2015_439_block7 rfl rfl rfl

private theorem cost_2015_439_join0_8 : P1_7_1_3.blockEstimate 2015 439 1463 256 = 90132753920 :=
  @P1_7_1_3.block_append 2015 439 1463 1591 128 128 256 45316888320 44815865600 90132753920 cost_2015_439_block8 cost_2015_439_block9 rfl rfl rfl

private theorem cost_2015_439_join0_10 : P1_7_1_3.blockEstimate 2015 439 1719 256 = 80746688000 :=
  @P1_7_1_3.block_append 2015 439 1719 1847 128 128 256 42469349120 38277338880 80746688000 cost_2015_439_block10 cost_2015_439_block11 rfl rfl rfl

private theorem cost_2015_439_join0_12 : P1_7_1_3.blockEstimate 2015 439 1975 256 = 57756920633 :=
  @P1_7_1_3.block_append 2015 439 1975 2103 128 128 256 32311137664 25445782969 57756920633 cost_2015_439_block12 cost_2015_439_block13 rfl rfl rfl

private theorem cost_2015_439_join0_14 : P1_7_1_3.blockEstimate 2015 439 2231 256 = 30848331305 :=
  @P1_7_1_3.block_append 2015 439 2231 2359 128 128 256 18591739841 12256591464 30848331305 cost_2015_439_block14 cost_2015_439_block15 rfl rfl rfl

private theorem cost_2015_439_join0_16 : P1_7_1_3.blockEstimate 2015 439 2487 256 = 9729405088 :=
  @P1_7_1_3.block_append 2015 439 2487 2615 128 128 256 6862645840 2866759248 9729405088 cost_2015_439_block16 cost_2015_439_block17 rfl rfl rfl

private theorem cost_2015_439_join0_18 : P1_7_1_3.blockEstimate 2015 439 2743 150 = 563666597 :=
  @P1_7_1_3.block_append 2015 439 2743 2871 128 22 150 561504848 2161749 563666597 cost_2015_439_block18 cost_2015_439_block19 rfl rfl rfl

private theorem cost_2015_439_join1_0 : P1_7_1_3.blockEstimate 2015 439 439 512 = 36617138910 :=
  @P1_7_1_3.block_append 2015 439 439 695 256 256 512 5159490880 31457648030 36617138910 cost_2015_439_join0_0 cost_2015_439_join0_2 rfl rfl rfl

private theorem cost_2015_439_join1_2 : P1_7_1_3.blockEstimate 2015 439 951 512 = 149367905280 :=
  @P1_7_1_3.block_append 2015 439 951 1207 256 256 512 64613035520 84754869760 149367905280 cost_2015_439_join0_4 cost_2015_439_join0_6 rfl rfl rfl

private theorem cost_2015_439_join1_4 : P1_7_1_3.blockEstimate 2015 439 1463 512 = 170879441920 :=
  @P1_7_1_3.block_append 2015 439 1463 1719 256 256 512 90132753920 80746688000 170879441920 cost_2015_439_join0_8 cost_2015_439_join0_10 rfl rfl rfl

private theorem cost_2015_439_join1_6 : P1_7_1_3.blockEstimate 2015 439 1975 512 = 88605251938 :=
  @P1_7_1_3.block_append 2015 439 1975 2231 256 256 512 57756920633 30848331305 88605251938 cost_2015_439_join0_12 cost_2015_439_join0_14 rfl rfl rfl

private theorem cost_2015_439_join1_8 : P1_7_1_3.blockEstimate 2015 439 2487 406 = 10293071685 :=
  @P1_7_1_3.block_append 2015 439 2487 2743 256 150 406 9729405088 563666597 10293071685 cost_2015_439_join0_16 cost_2015_439_join0_18 rfl rfl rfl

private theorem cost_2015_439_join2_0 : P1_7_1_3.blockEstimate 2015 439 439 1024 = 185985044190 :=
  @P1_7_1_3.block_append 2015 439 439 951 512 512 1024 36617138910 149367905280 185985044190 cost_2015_439_join1_0 cost_2015_439_join1_2 rfl rfl rfl

private theorem cost_2015_439_join2_2 : P1_7_1_3.blockEstimate 2015 439 1463 1024 = 259484693858 :=
  @P1_7_1_3.block_append 2015 439 1463 1975 512 512 1024 170879441920 88605251938 259484693858 cost_2015_439_join1_4 cost_2015_439_join1_6 rfl rfl rfl

private theorem cost_2015_439_join3_0 : P1_7_1_3.blockEstimate 2015 439 439 2048 = 445469738048 :=
  @P1_7_1_3.block_append 2015 439 439 1463 1024 1024 2048 185985044190 259484693858 445469738048 cost_2015_439_join2_0 cost_2015_439_join2_2 rfl rfl rfl

private theorem cost_2015_439_join4_0 : P1_7_1_3.blockEstimate 2015 439 439 2454 = 455762809733 :=
  @P1_7_1_3.block_append 2015 439 439 2487 2048 406 2454 445469738048 10293071685 455762809733 cost_2015_439_join3_0 cost_2015_439_join1_8 rfl rfl rfl

private theorem cost_2015_439_total : P1_7_1_3.momentEstimate 2015 439 = 455762809733 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2015 + 439 = 2454 by decide]
  exact cost_2015_439_join4_0

theorem moment2015_439 : P1_7_1.groupedPoleMoment 2015 439 ≤ 455762809733 :=
  (P1_7_1_3.grouped_bound 2015 439).trans_eq cost_2015_439_total
private theorem cost_2015_447_block0 : P1_7_1_3.blockEstimate 2015 447 447 128 = 686809760 := by decide +kernel

private theorem cost_2015_447_block1 : P1_7_1_3.blockEstimate 2015 447 575 128 = 4472681120 := by decide +kernel

private theorem cost_2015_447_block2 : P1_7_1_3.blockEstimate 2015 447 703 128 = 11273208480 := by decide +kernel

private theorem cost_2015_447_block3 : P1_7_1_3.blockEstimate 2015 447 831 128 = 20213541712 := by decide +kernel

private theorem cost_2015_447_block4 : P1_7_1_3.blockEstimate 2015 447 959 128 = 29060691968 := by decide +kernel

private theorem cost_2015_447_block5 : P1_7_1_3.blockEstimate 2015 447 1087 128 = 36096112640 := by decide +kernel

private theorem cost_2015_447_block6 : P1_7_1_3.blockEstimate 2015 447 1215 128 = 41252485120 := by decide +kernel

private theorem cost_2015_447_block7 : P1_7_1_3.blockEstimate 2015 447 1343 128 = 44529809408 := by decide +kernel

private theorem cost_2015_447_block8 : P1_7_1_3.blockEstimate 2015 447 1471 128 = 45928085504 := by decide +kernel

private theorem cost_2015_447_block9 : P1_7_1_3.blockEstimate 2015 447 1599 128 = 45447313408 := by decide +kernel

private theorem cost_2015_447_block10 : P1_7_1_3.blockEstimate 2015 447 1727 128 = 43087493120 := by decide +kernel

private theorem cost_2015_447_block11 : P1_7_1_3.blockEstimate 2015 447 1855 128 = 38848624640 := by decide +kernel

private theorem cost_2015_447_block12 : P1_7_1_3.blockEstimate 2015 447 1983 128 = 32822610593 := by decide +kernel

private theorem cost_2015_447_block13 : P1_7_1_3.blockEstimate 2015 447 2111 128 = 25928500411 := by decide +kernel

private theorem cost_2015_447_block14 : P1_7_1_3.blockEstimate 2015 447 2239 128 = 19032376233 := by decide +kernel

private theorem cost_2015_447_block15 : P1_7_1_3.blockEstimate 2015 447 2367 128 = 12637099367 := by decide +kernel

private theorem cost_2015_447_block16 : P1_7_1_3.blockEstimate 2015 447 2495 128 = 7162778384 := by decide +kernel

private theorem cost_2015_447_block17 : P1_7_1_3.blockEstimate 2015 447 2623 128 = 3069583120 := by decide +kernel

private theorem cost_2015_447_block18 : P1_7_1_3.blockEstimate 2015 447 2751 128 = 651291408 := by decide +kernel

private theorem cost_2015_447_block19 : P1_7_1_3.blockEstimate 2015 447 2879 30 = 5204132 := by decide +kernel

private theorem cost_2015_447_join0_0 : P1_7_1_3.blockEstimate 2015 447 447 256 = 5159490880 :=
  @P1_7_1_3.block_append 2015 447 447 575 128 128 256 686809760 4472681120 5159490880 cost_2015_447_block0 cost_2015_447_block1 rfl rfl rfl

private theorem cost_2015_447_join0_2 : P1_7_1_3.blockEstimate 2015 447 703 256 = 31486750192 :=
  @P1_7_1_3.block_append 2015 447 703 831 128 128 256 11273208480 20213541712 31486750192 cost_2015_447_block2 cost_2015_447_block3 rfl rfl rfl

private theorem cost_2015_447_join0_4 : P1_7_1_3.blockEstimate 2015 447 959 256 = 65156804608 :=
  @P1_7_1_3.block_append 2015 447 959 1087 128 128 256 29060691968 36096112640 65156804608 cost_2015_447_block4 cost_2015_447_block5 rfl rfl rfl

private theorem cost_2015_447_join0_6 : P1_7_1_3.blockEstimate 2015 447 1215 256 = 85782294528 :=
  @P1_7_1_3.block_append 2015 447 1215 1343 128 128 256 41252485120 44529809408 85782294528 cost_2015_447_block6 cost_2015_447_block7 rfl rfl rfl

private theorem cost_2015_447_join0_8 : P1_7_1_3.blockEstimate 2015 447 1471 256 = 91375398912 :=
  @P1_7_1_3.block_append 2015 447 1471 1599 128 128 256 45928085504 45447313408 91375398912 cost_2015_447_block8 cost_2015_447_block9 rfl rfl rfl

private theorem cost_2015_447_join0_10 : P1_7_1_3.blockEstimate 2015 447 1727 256 = 81936117760 :=
  @P1_7_1_3.block_append 2015 447 1727 1855 128 128 256 43087493120 38848624640 81936117760 cost_2015_447_block10 cost_2015_447_block11 rfl rfl rfl

private theorem cost_2015_447_join0_12 : P1_7_1_3.blockEstimate 2015 447 1983 256 = 58751111004 :=
  @P1_7_1_3.block_append 2015 447 1983 2111 128 128 256 32822610593 25928500411 58751111004 cost_2015_447_block12 cost_2015_447_block13 rfl rfl rfl

private theorem cost_2015_447_join0_14 : P1_7_1_3.blockEstimate 2015 447 2239 256 = 31669475600 :=
  @P1_7_1_3.block_append 2015 447 2239 2367 128 128 256 19032376233 12637099367 31669475600 cost_2015_447_block14 cost_2015_447_block15 rfl rfl rfl

private theorem cost_2015_447_join0_16 : P1_7_1_3.blockEstimate 2015 447 2495 256 = 10232361504 :=
  @P1_7_1_3.block_append 2015 447 2495 2623 128 128 256 7162778384 3069583120 10232361504 cost_2015_447_block16 cost_2015_447_block17 rfl rfl rfl

private theorem cost_2015_447_join0_18 : P1_7_1_3.blockEstimate 2015 447 2751 158 = 656495540 :=
  @P1_7_1_3.block_append 2015 447 2751 2879 128 30 158 651291408 5204132 656495540 cost_2015_447_block18 cost_2015_447_block19 rfl rfl rfl

private theorem cost_2015_447_join1_0 : P1_7_1_3.blockEstimate 2015 447 447 512 = 36646241072 :=
  @P1_7_1_3.block_append 2015 447 447 703 256 256 512 5159490880 31486750192 36646241072 cost_2015_447_join0_0 cost_2015_447_join0_2 rfl rfl rfl

private theorem cost_2015_447_join1_2 : P1_7_1_3.blockEstimate 2015 447 959 512 = 150939099136 :=
  @P1_7_1_3.block_append 2015 447 959 1215 256 256 512 65156804608 85782294528 150939099136 cost_2015_447_join0_4 cost_2015_447_join0_6 rfl rfl rfl

private theorem cost_2015_447_join1_4 : P1_7_1_3.blockEstimate 2015 447 1471 512 = 173311516672 :=
  @P1_7_1_3.block_append 2015 447 1471 1727 256 256 512 91375398912 81936117760 173311516672 cost_2015_447_join0_8 cost_2015_447_join0_10 rfl rfl rfl

private theorem cost_2015_447_join1_6 : P1_7_1_3.blockEstimate 2015 447 1983 512 = 90420586604 :=
  @P1_7_1_3.block_append 2015 447 1983 2239 256 256 512 58751111004 31669475600 90420586604 cost_2015_447_join0_12 cost_2015_447_join0_14 rfl rfl rfl

private theorem cost_2015_447_join1_8 : P1_7_1_3.blockEstimate 2015 447 2495 414 = 10888857044 :=
  @P1_7_1_3.block_append 2015 447 2495 2751 256 158 414 10232361504 656495540 10888857044 cost_2015_447_join0_16 cost_2015_447_join0_18 rfl rfl rfl

private theorem cost_2015_447_join2_0 : P1_7_1_3.blockEstimate 2015 447 447 1024 = 187585340208 :=
  @P1_7_1_3.block_append 2015 447 447 959 512 512 1024 36646241072 150939099136 187585340208 cost_2015_447_join1_0 cost_2015_447_join1_2 rfl rfl rfl

private theorem cost_2015_447_join2_2 : P1_7_1_3.blockEstimate 2015 447 1471 1024 = 263732103276 :=
  @P1_7_1_3.block_append 2015 447 1471 1983 512 512 1024 173311516672 90420586604 263732103276 cost_2015_447_join1_4 cost_2015_447_join1_6 rfl rfl rfl

private theorem cost_2015_447_join3_0 : P1_7_1_3.blockEstimate 2015 447 447 2048 = 451317443484 :=
  @P1_7_1_3.block_append 2015 447 447 1471 1024 1024 2048 187585340208 263732103276 451317443484 cost_2015_447_join2_0 cost_2015_447_join2_2 rfl rfl rfl

private theorem cost_2015_447_join4_0 : P1_7_1_3.blockEstimate 2015 447 447 2462 = 462206300528 :=
  @P1_7_1_3.block_append 2015 447 447 2495 2048 414 2462 451317443484 10888857044 462206300528 cost_2015_447_join3_0 cost_2015_447_join1_8 rfl rfl rfl

private theorem cost_2015_447_total : P1_7_1_3.momentEstimate 2015 447 = 462206300528 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2015 + 447 = 2462 by decide]
  exact cost_2015_447_join4_0

theorem moment2015_447 : P1_7_1.groupedPoleMoment 2015 447 ≤ 462206300528 :=
  (P1_7_1_3.grouped_bound 2015 447).trans_eq cost_2015_447_total
private theorem cost_2015_449_block0 : P1_7_1_3.blockEstimate 2015 449 449 128 = 686809760 := by decide +kernel

private theorem cost_2015_449_block1 : P1_7_1_3.blockEstimate 2015 449 577 128 = 4472681120 := by decide +kernel

private theorem cost_2015_449_block2 : P1_7_1_3.blockEstimate 2015 449 705 128 = 11273208480 := by decide +kernel

private theorem cost_2015_449_block3 : P1_7_1_3.blockEstimate 2015 449 833 128 = 20219787440 := by decide +kernel

private theorem cost_2015_449_block4 : P1_7_1_3.blockEstimate 2015 449 961 128 = 29107512000 := by decide +kernel

private theorem cost_2015_449_block5 : P1_7_1_3.blockEstimate 2015 449 1089 128 = 36181713600 := by decide +kernel

private theorem cost_2015_449_block6 : P1_7_1_3.blockEstimate 2015 449 1217 128 = 41368478400 := by decide +kernel

private theorem cost_2015_449_block7 : P1_7_1_3.blockEstimate 2015 449 1345 128 = 44667806400 := by decide +kernel

private theorem cost_2015_449_block8 : P1_7_1_3.blockEstimate 2015 449 1473 128 = 46079697600 := by decide +kernel

private theorem cost_2015_449_block9 : P1_7_1_3.blockEstimate 2015 449 1601 128 = 45604152000 := by decide +kernel

private theorem cost_2015_449_block10 : P1_7_1_3.blockEstimate 2015 449 1729 128 = 43241169600 := by decide +kernel

private theorem cost_2015_449_block11 : P1_7_1_3.blockEstimate 2015 449 1857 128 = 38990750400 := by decide +kernel

private theorem cost_2015_449_block12 : P1_7_1_3.blockEstimate 2015 449 1985 128 = 32950487293 := by decide +kernel

private theorem cost_2015_449_block13 : P1_7_1_3.blockEstimate 2015 449 2113 128 = 26049560366 := by decide +kernel

private theorem cost_2015_449_block14 : P1_7_1_3.blockEstimate 2015 449 2241 128 = 19143085772 := by decide +kernel

private theorem cost_2015_449_block15 : P1_7_1_3.blockEstimate 2015 449 2369 128 = 12732941089 := by decide +kernel

private theorem cost_2015_449_block16 : P1_7_1_3.blockEstimate 2015 449 2497 128 = 7238682592 := by decide +kernel

private theorem cost_2015_449_block17 : P1_7_1_3.blockEstimate 2015 449 2625 128 = 3121313760 := by decide +kernel

private theorem cost_2015_449_block18 : P1_7_1_3.blockEstimate 2015 449 2753 128 = 674916320 := by decide +kernel

private theorem cost_2015_449_block19 : P1_7_1_3.blockEstimate 2015 449 2881 32 = 6258040 := by decide +kernel

private theorem cost_2015_449_join0_0 : P1_7_1_3.blockEstimate 2015 449 449 256 = 5159490880 :=
  @P1_7_1_3.block_append 2015 449 449 577 128 128 256 686809760 4472681120 5159490880 cost_2015_449_block0 cost_2015_449_block1 rfl rfl rfl

private theorem cost_2015_449_join0_2 : P1_7_1_3.blockEstimate 2015 449 705 256 = 31492995920 :=
  @P1_7_1_3.block_append 2015 449 705 833 128 128 256 11273208480 20219787440 31492995920 cost_2015_449_block2 cost_2015_449_block3 rfl rfl rfl

private theorem cost_2015_449_join0_4 : P1_7_1_3.blockEstimate 2015 449 961 256 = 65289225600 :=
  @P1_7_1_3.block_append 2015 449 961 1089 128 128 256 29107512000 36181713600 65289225600 cost_2015_449_block4 cost_2015_449_block5 rfl rfl rfl

private theorem cost_2015_449_join0_6 : P1_7_1_3.blockEstimate 2015 449 1217 256 = 86036284800 :=
  @P1_7_1_3.block_append 2015 449 1217 1345 128 128 256 41368478400 44667806400 86036284800 cost_2015_449_block6 cost_2015_449_block7 rfl rfl rfl

private theorem cost_2015_449_join0_8 : P1_7_1_3.blockEstimate 2015 449 1473 256 = 91683849600 :=
  @P1_7_1_3.block_append 2015 449 1473 1601 128 128 256 46079697600 45604152000 91683849600 cost_2015_449_block8 cost_2015_449_block9 rfl rfl rfl

private theorem cost_2015_449_join0_10 : P1_7_1_3.blockEstimate 2015 449 1729 256 = 82231920000 :=
  @P1_7_1_3.block_append 2015 449 1729 1857 128 128 256 43241169600 38990750400 82231920000 cost_2015_449_block10 cost_2015_449_block11 rfl rfl rfl

private theorem cost_2015_449_join0_12 : P1_7_1_3.blockEstimate 2015 449 1985 256 = 59000047659 :=
  @P1_7_1_3.block_append 2015 449 1985 2113 128 128 256 32950487293 26049560366 59000047659 cost_2015_449_block12 cost_2015_449_block13 rfl rfl rfl

private theorem cost_2015_449_join0_14 : P1_7_1_3.blockEstimate 2015 449 2241 256 = 31876026861 :=
  @P1_7_1_3.block_append 2015 449 2241 2369 128 128 256 19143085772 12732941089 31876026861 cost_2015_449_block14 cost_2015_449_block15 rfl rfl rfl

private theorem cost_2015_449_join0_16 : P1_7_1_3.blockEstimate 2015 449 2497 256 = 10359996352 :=
  @P1_7_1_3.block_append 2015 449 2497 2625 128 128 256 7238682592 3121313760 10359996352 cost_2015_449_block16 cost_2015_449_block17 rfl rfl rfl

private theorem cost_2015_449_join0_18 : P1_7_1_3.blockEstimate 2015 449 2753 160 = 681174360 :=
  @P1_7_1_3.block_append 2015 449 2753 2881 128 32 160 674916320 6258040 681174360 cost_2015_449_block18 cost_2015_449_block19 rfl rfl rfl

private theorem cost_2015_449_join1_0 : P1_7_1_3.blockEstimate 2015 449 449 512 = 36652486800 :=
  @P1_7_1_3.block_append 2015 449 449 705 256 256 512 5159490880 31492995920 36652486800 cost_2015_449_join0_0 cost_2015_449_join0_2 rfl rfl rfl

private theorem cost_2015_449_join1_2 : P1_7_1_3.blockEstimate 2015 449 961 512 = 151325510400 :=
  @P1_7_1_3.block_append 2015 449 961 1217 256 256 512 65289225600 86036284800 151325510400 cost_2015_449_join0_4 cost_2015_449_join0_6 rfl rfl rfl

private theorem cost_2015_449_join1_4 : P1_7_1_3.blockEstimate 2015 449 1473 512 = 173915769600 :=
  @P1_7_1_3.block_append 2015 449 1473 1729 256 256 512 91683849600 82231920000 173915769600 cost_2015_449_join0_8 cost_2015_449_join0_10 rfl rfl rfl

private theorem cost_2015_449_join1_6 : P1_7_1_3.blockEstimate 2015 449 1985 512 = 90876074520 :=
  @P1_7_1_3.block_append 2015 449 1985 2241 256 256 512 59000047659 31876026861 90876074520 cost_2015_449_join0_12 cost_2015_449_join0_14 rfl rfl rfl

private theorem cost_2015_449_join1_8 : P1_7_1_3.blockEstimate 2015 449 2497 416 = 11041170712 :=
  @P1_7_1_3.block_append 2015 449 2497 2753 256 160 416 10359996352 681174360 11041170712 cost_2015_449_join0_16 cost_2015_449_join0_18 rfl rfl rfl

private theorem cost_2015_449_join2_0 : P1_7_1_3.blockEstimate 2015 449 449 1024 = 187977997200 :=
  @P1_7_1_3.block_append 2015 449 449 961 512 512 1024 36652486800 151325510400 187977997200 cost_2015_449_join1_0 cost_2015_449_join1_2 rfl rfl rfl

private theorem cost_2015_449_join2_2 : P1_7_1_3.blockEstimate 2015 449 1473 1024 = 264791844120 :=
  @P1_7_1_3.block_append 2015 449 1473 1985 512 512 1024 173915769600 90876074520 264791844120 cost_2015_449_join1_4 cost_2015_449_join1_6 rfl rfl rfl

private theorem cost_2015_449_join3_0 : P1_7_1_3.blockEstimate 2015 449 449 2048 = 452769841320 :=
  @P1_7_1_3.block_append 2015 449 449 1473 1024 1024 2048 187977997200 264791844120 452769841320 cost_2015_449_join2_0 cost_2015_449_join2_2 rfl rfl rfl

private theorem cost_2015_449_join4_0 : P1_7_1_3.blockEstimate 2015 449 449 2464 = 463811012032 :=
  @P1_7_1_3.block_append 2015 449 449 2497 2048 416 2464 452769841320 11041170712 463811012032 cost_2015_449_join3_0 cost_2015_449_join1_8 rfl rfl rfl

private theorem cost_2015_449_total : P1_7_1_3.momentEstimate 2015 449 = 463811012032 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2015 + 449 = 2464 by decide]
  exact cost_2015_449_join4_0

theorem moment2015_449 : P1_7_1.groupedPoleMoment 2015 449 ≤ 463811012032 :=
  (P1_7_1_3.grouped_bound 2015 449).trans_eq cost_2015_449_total
private theorem cost_2016_430_block0 : P1_7_1_3.blockEstimate 2016 430 430 128 = 687167520 := by decide +kernel

private theorem cost_2016_430_block1 : P1_7_1_3.blockEstimate 2016 430 558 128 = 4475152416 := by decide +kernel

private theorem cost_2016_430_block2 : P1_7_1_3.blockEstimate 2016 430 686 128 = 11279890464 := by decide +kernel

private theorem cost_2016_430_block3 : P1_7_1_3.blockEstimate 2016 430 814 128 = 20155956771 := by decide +kernel

private theorem cost_2016_430_block4 : P1_7_1_3.blockEstimate 2016 430 942 128 = 28652907584 := by decide +kernel

private theorem cost_2016_430_block5 : P1_7_1_3.blockEstimate 2016 430 1070 128 = 35368397888 := by decide +kernel

private theorem cost_2016_430_block6 : P1_7_1_3.blockEstimate 2016 430 1198 128 = 40276143168 := by decide +kernel

private theorem cost_2016_430_block7 : P1_7_1_3.blockEstimate 2016 430 1326 128 = 43376143424 := by decide +kernel

private theorem cost_2016_430_block8 : P1_7_1_3.blockEstimate 2016 430 1454 128 = 44668398656 := by decide +kernel

private theorem cost_2016_430_block9 : P1_7_1_3.blockEstimate 2016 430 1582 128 = 44152908864 := by decide +kernel

private theorem cost_2016_430_block10 : P1_7_1_3.blockEstimate 2016 430 1710 128 = 41829674048 := by decide +kernel

private theorem cost_2016_430_block11 : P1_7_1_3.blockEstimate 2016 430 1838 128 = 37698694208 := by decide +kernel

private theorem cost_2016_430_block12 : P1_7_1_3.blockEstimate 2016 430 1966 128 = 31810049397 := by decide +kernel

private theorem cost_2016_430_block13 : P1_7_1_3.blockEstimate 2016 430 2094 128 = 24976306488 := by decide +kernel

private theorem cost_2016_430_block14 : P1_7_1_3.blockEstimate 2016 430 2222 128 = 18163220208 := by decide +kernel

private theorem cost_2016_430_block15 : P1_7_1_3.blockEstimate 2016 430 2350 128 = 11886758811 := by decide +kernel

private theorem cost_2016_430_block16 : P1_7_1_3.blockEstimate 2016 430 2478 128 = 6571779888 := by decide +kernel

private theorem cost_2016_430_block17 : P1_7_1_3.blockEstimate 2016 430 2606 128 = 2671960880 := by decide +kernel

private theorem cost_2016_430_block18 : P1_7_1_3.blockEstimate 2016 430 2734 128 = 479551280 := by decide +kernel

private theorem cost_2016_430_block19 : P1_7_1_3.blockEstimate 2016 430 2862 14 = 619102 := by decide +kernel

private theorem cost_2016_430_join0_0 : P1_7_1_3.blockEstimate 2016 430 430 256 = 5162319936 :=
  @P1_7_1_3.block_append 2016 430 430 558 128 128 256 687167520 4475152416 5162319936 cost_2016_430_block0 cost_2016_430_block1 rfl rfl rfl

private theorem cost_2016_430_join0_2 : P1_7_1_3.blockEstimate 2016 430 686 256 = 31435847235 :=
  @P1_7_1_3.block_append 2016 430 686 814 128 128 256 11279890464 20155956771 31435847235 cost_2016_430_block2 cost_2016_430_block3 rfl rfl rfl

private theorem cost_2016_430_join0_4 : P1_7_1_3.blockEstimate 2016 430 942 256 = 64021305472 :=
  @P1_7_1_3.block_append 2016 430 942 1070 128 128 256 28652907584 35368397888 64021305472 cost_2016_430_block4 cost_2016_430_block5 rfl rfl rfl

private theorem cost_2016_430_join0_6 : P1_7_1_3.blockEstimate 2016 430 1198 256 = 83652286592 :=
  @P1_7_1_3.block_append 2016 430 1198 1326 128 128 256 40276143168 43376143424 83652286592 cost_2016_430_block6 cost_2016_430_block7 rfl rfl rfl

private theorem cost_2016_430_join0_8 : P1_7_1_3.blockEstimate 2016 430 1454 256 = 88821307520 :=
  @P1_7_1_3.block_append 2016 430 1454 1582 128 128 256 44668398656 44152908864 88821307520 cost_2016_430_block8 cost_2016_430_block9 rfl rfl rfl

private theorem cost_2016_430_join0_10 : P1_7_1_3.blockEstimate 2016 430 1710 256 = 79528368256 :=
  @P1_7_1_3.block_append 2016 430 1710 1838 128 128 256 41829674048 37698694208 79528368256 cost_2016_430_block10 cost_2016_430_block11 rfl rfl rfl

private theorem cost_2016_430_join0_12 : P1_7_1_3.blockEstimate 2016 430 1966 256 = 56786355885 :=
  @P1_7_1_3.block_append 2016 430 1966 2094 128 128 256 31810049397 24976306488 56786355885 cost_2016_430_block12 cost_2016_430_block13 rfl rfl rfl

private theorem cost_2016_430_join0_14 : P1_7_1_3.blockEstimate 2016 430 2222 256 = 30049979019 :=
  @P1_7_1_3.block_append 2016 430 2222 2350 128 128 256 18163220208 11886758811 30049979019 cost_2016_430_block14 cost_2016_430_block15 rfl rfl rfl

private theorem cost_2016_430_join0_16 : P1_7_1_3.blockEstimate 2016 430 2478 256 = 9243740768 :=
  @P1_7_1_3.block_append 2016 430 2478 2606 128 128 256 6571779888 2671960880 9243740768 cost_2016_430_block16 cost_2016_430_block17 rfl rfl rfl

private theorem cost_2016_430_join0_18 : P1_7_1_3.blockEstimate 2016 430 2734 142 = 480170382 :=
  @P1_7_1_3.block_append 2016 430 2734 2862 128 14 142 479551280 619102 480170382 cost_2016_430_block18 cost_2016_430_block19 rfl rfl rfl

private theorem cost_2016_430_join1_0 : P1_7_1_3.blockEstimate 2016 430 430 512 = 36598167171 :=
  @P1_7_1_3.block_append 2016 430 430 686 256 256 512 5162319936 31435847235 36598167171 cost_2016_430_join0_0 cost_2016_430_join0_2 rfl rfl rfl

private theorem cost_2016_430_join1_2 : P1_7_1_3.blockEstimate 2016 430 942 512 = 147673592064 :=
  @P1_7_1_3.block_append 2016 430 942 1198 256 256 512 64021305472 83652286592 147673592064 cost_2016_430_join0_4 cost_2016_430_join0_6 rfl rfl rfl

private theorem cost_2016_430_join1_4 : P1_7_1_3.blockEstimate 2016 430 1454 512 = 168349675776 :=
  @P1_7_1_3.block_append 2016 430 1454 1710 256 256 512 88821307520 79528368256 168349675776 cost_2016_430_join0_8 cost_2016_430_join0_10 rfl rfl rfl

private theorem cost_2016_430_join1_6 : P1_7_1_3.blockEstimate 2016 430 1966 512 = 86836334904 :=
  @P1_7_1_3.block_append 2016 430 1966 2222 256 256 512 56786355885 30049979019 86836334904 cost_2016_430_join0_12 cost_2016_430_join0_14 rfl rfl rfl

private theorem cost_2016_430_join1_8 : P1_7_1_3.blockEstimate 2016 430 2478 398 = 9723911150 :=
  @P1_7_1_3.block_append 2016 430 2478 2734 256 142 398 9243740768 480170382 9723911150 cost_2016_430_join0_16 cost_2016_430_join0_18 rfl rfl rfl

private theorem cost_2016_430_join2_0 : P1_7_1_3.blockEstimate 2016 430 430 1024 = 184271759235 :=
  @P1_7_1_3.block_append 2016 430 430 942 512 512 1024 36598167171 147673592064 184271759235 cost_2016_430_join1_0 cost_2016_430_join1_2 rfl rfl rfl

private theorem cost_2016_430_join2_2 : P1_7_1_3.blockEstimate 2016 430 1454 1024 = 255186010680 :=
  @P1_7_1_3.block_append 2016 430 1454 1966 512 512 1024 168349675776 86836334904 255186010680 cost_2016_430_join1_4 cost_2016_430_join1_6 rfl rfl rfl

private theorem cost_2016_430_join3_0 : P1_7_1_3.blockEstimate 2016 430 430 2048 = 439457769915 :=
  @P1_7_1_3.block_append 2016 430 430 1454 1024 1024 2048 184271759235 255186010680 439457769915 cost_2016_430_join2_0 cost_2016_430_join2_2 rfl rfl rfl

private theorem cost_2016_430_join4_0 : P1_7_1_3.blockEstimate 2016 430 430 2446 = 449181681065 :=
  @P1_7_1_3.block_append 2016 430 430 2478 2048 398 2446 439457769915 9723911150 449181681065 cost_2016_430_join3_0 cost_2016_430_join1_8 rfl rfl rfl

private theorem cost_2016_430_total : P1_7_1_3.momentEstimate 2016 430 = 449181681065 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2016 + 430 = 2446 by decide]
  exact cost_2016_430_join4_0

theorem moment2016_430 : P1_7_1.groupedPoleMoment 2016 430 ≤ 449181681065 :=
  (P1_7_1_3.grouped_bound 2016 430).trans_eq cost_2016_430_total
private theorem cost_2016_437_block0 : P1_7_1_3.blockEstimate 2016 437 437 128 = 687167520 := by decide +kernel

private theorem cost_2016_437_block1 : P1_7_1_3.blockEstimate 2016 437 565 128 = 4475152416 := by decide +kernel

private theorem cost_2016_437_block2 : P1_7_1_3.blockEstimate 2016 437 693 128 = 11279890464 := by decide +kernel

private theorem cost_2016_437_block3 : P1_7_1_3.blockEstimate 2016 437 821 128 = 20188990821 := by decide +kernel

private theorem cost_2016_437_block4 : P1_7_1_3.blockEstimate 2016 437 949 128 = 28835607360 := by decide +kernel

private theorem cost_2016_437_block5 : P1_7_1_3.blockEstimate 2016 437 1077 128 = 35685282624 := by decide +kernel

private theorem cost_2016_437_block6 : P1_7_1_3.blockEstimate 2016 437 1205 128 = 40697852736 := by decide +kernel

private theorem cost_2016_437_block7 : P1_7_1_3.blockEstimate 2016 437 1333 128 = 43873317696 := by decide +kernel

private theorem cost_2016_437_block8 : P1_7_1_3.blockEstimate 2016 437 1461 128 = 45211677504 := by decide +kernel

private theorem cost_2016_437_block9 : P1_7_1_3.blockEstimate 2016 437 1589 128 = 44712932160 := by decide +kernel

private theorem cost_2016_437_block10 : P1_7_1_3.blockEstimate 2016 437 1717 128 = 42377081664 := by decide +kernel

private theorem cost_2016_437_block11 : P1_7_1_3.blockEstimate 2016 437 1845 128 = 38204126016 := by decide +kernel

private theorem cost_2016_437_block12 : P1_7_1_3.blockEstimate 2016 437 1973 128 = 32258447536 := by decide +kernel

private theorem cost_2016_437_block13 : P1_7_1_3.blockEstimate 2016 437 2101 128 = 25396664607 := by decide +kernel

private theorem cost_2016_437_block14 : P1_7_1_3.blockEstimate 2016 437 2229 128 = 18545685849 := by decide +kernel

private theorem cost_2016_437_block15 : P1_7_1_3.blockEstimate 2016 437 2357 128 = 12215594090 := by decide +kernel

private theorem cost_2016_437_block16 : P1_7_1_3.blockEstimate 2016 437 2485 128 = 6829320688 := by decide +kernel

private theorem cost_2016_437_block17 : P1_7_1_3.blockEstimate 2016 437 2613 128 = 2843385328 := by decide +kernel

private theorem cost_2016_437_block18 : P1_7_1_3.blockEstimate 2016 437 2741 128 = 551096816 := by decide +kernel

private theorem cost_2016_437_block19 : P1_7_1_3.blockEstimate 2016 437 2869 21 = 1898431 := by decide +kernel

private theorem cost_2016_437_join0_0 : P1_7_1_3.blockEstimate 2016 437 437 256 = 5162319936 :=
  @P1_7_1_3.block_append 2016 437 437 565 128 128 256 687167520 4475152416 5162319936 cost_2016_437_block0 cost_2016_437_block1 rfl rfl rfl

private theorem cost_2016_437_join0_2 : P1_7_1_3.blockEstimate 2016 437 693 256 = 31468881285 :=
  @P1_7_1_3.block_append 2016 437 693 821 128 128 256 11279890464 20188990821 31468881285 cost_2016_437_block2 cost_2016_437_block3 rfl rfl rfl

private theorem cost_2016_437_join0_4 : P1_7_1_3.blockEstimate 2016 437 949 256 = 64520889984 :=
  @P1_7_1_3.block_append 2016 437 949 1077 128 128 256 28835607360 35685282624 64520889984 cost_2016_437_block4 cost_2016_437_block5 rfl rfl rfl

private theorem cost_2016_437_join0_6 : P1_7_1_3.blockEstimate 2016 437 1205 256 = 84571170432 :=
  @P1_7_1_3.block_append 2016 437 1205 1333 128 128 256 40697852736 43873317696 84571170432 cost_2016_437_block6 cost_2016_437_block7 rfl rfl rfl

private theorem cost_2016_437_join0_8 : P1_7_1_3.blockEstimate 2016 437 1461 256 = 89924609664 :=
  @P1_7_1_3.block_append 2016 437 1461 1589 128 128 256 45211677504 44712932160 89924609664 cost_2016_437_block8 cost_2016_437_block9 rfl rfl rfl

private theorem cost_2016_437_join0_10 : P1_7_1_3.blockEstimate 2016 437 1717 256 = 80581207680 :=
  @P1_7_1_3.block_append 2016 437 1717 1845 128 128 256 42377081664 38204126016 80581207680 cost_2016_437_block10 cost_2016_437_block11 rfl rfl rfl

private theorem cost_2016_437_join0_12 : P1_7_1_3.blockEstimate 2016 437 1973 256 = 57655112143 :=
  @P1_7_1_3.block_append 2016 437 1973 2101 128 128 256 32258447536 25396664607 57655112143 cost_2016_437_block12 cost_2016_437_block13 rfl rfl rfl

private theorem cost_2016_437_join0_14 : P1_7_1_3.blockEstimate 2016 437 2229 256 = 30761279939 :=
  @P1_7_1_3.block_append 2016 437 2229 2357 128 128 256 18545685849 12215594090 30761279939 cost_2016_437_block14 cost_2016_437_block15 rfl rfl rfl

private theorem cost_2016_437_join0_16 : P1_7_1_3.blockEstimate 2016 437 2485 256 = 9672706016 :=
  @P1_7_1_3.block_append 2016 437 2485 2613 128 128 256 6829320688 2843385328 9672706016 cost_2016_437_block16 cost_2016_437_block17 rfl rfl rfl

private theorem cost_2016_437_join0_18 : P1_7_1_3.blockEstimate 2016 437 2741 149 = 552995247 :=
  @P1_7_1_3.block_append 2016 437 2741 2869 128 21 149 551096816 1898431 552995247 cost_2016_437_block18 cost_2016_437_block19 rfl rfl rfl

private theorem cost_2016_437_join1_0 : P1_7_1_3.blockEstimate 2016 437 437 512 = 36631201221 :=
  @P1_7_1_3.block_append 2016 437 437 693 256 256 512 5162319936 31468881285 36631201221 cost_2016_437_join0_0 cost_2016_437_join0_2 rfl rfl rfl

private theorem cost_2016_437_join1_2 : P1_7_1_3.blockEstimate 2016 437 949 512 = 149092060416 :=
  @P1_7_1_3.block_append 2016 437 949 1205 256 256 512 64520889984 84571170432 149092060416 cost_2016_437_join0_4 cost_2016_437_join0_6 rfl rfl rfl

private theorem cost_2016_437_join1_4 : P1_7_1_3.blockEstimate 2016 437 1461 512 = 170505817344 :=
  @P1_7_1_3.block_append 2016 437 1461 1717 256 256 512 89924609664 80581207680 170505817344 cost_2016_437_join0_8 cost_2016_437_join0_10 rfl rfl rfl

private theorem cost_2016_437_join1_6 : P1_7_1_3.blockEstimate 2016 437 1973 512 = 88416392082 :=
  @P1_7_1_3.block_append 2016 437 1973 2229 256 256 512 57655112143 30761279939 88416392082 cost_2016_437_join0_12 cost_2016_437_join0_14 rfl rfl rfl

private theorem cost_2016_437_join1_8 : P1_7_1_3.blockEstimate 2016 437 2485 405 = 10225701263 :=
  @P1_7_1_3.block_append 2016 437 2485 2741 256 149 405 9672706016 552995247 10225701263 cost_2016_437_join0_16 cost_2016_437_join0_18 rfl rfl rfl

private theorem cost_2016_437_join2_0 : P1_7_1_3.blockEstimate 2016 437 437 1024 = 185723261637 :=
  @P1_7_1_3.block_append 2016 437 437 949 512 512 1024 36631201221 149092060416 185723261637 cost_2016_437_join1_0 cost_2016_437_join1_2 rfl rfl rfl

private theorem cost_2016_437_join2_2 : P1_7_1_3.blockEstimate 2016 437 1461 1024 = 258922209426 :=
  @P1_7_1_3.block_append 2016 437 1461 1973 512 512 1024 170505817344 88416392082 258922209426 cost_2016_437_join1_4 cost_2016_437_join1_6 rfl rfl rfl

private theorem cost_2016_437_join3_0 : P1_7_1_3.blockEstimate 2016 437 437 2048 = 444645471063 :=
  @P1_7_1_3.block_append 2016 437 437 1461 1024 1024 2048 185723261637 258922209426 444645471063 cost_2016_437_join2_0 cost_2016_437_join2_2 rfl rfl rfl

private theorem cost_2016_437_join4_0 : P1_7_1_3.blockEstimate 2016 437 437 2453 = 454871172326 :=
  @P1_7_1_3.block_append 2016 437 437 2485 2048 405 2453 444645471063 10225701263 454871172326 cost_2016_437_join3_0 cost_2016_437_join1_8 rfl rfl rfl

private theorem cost_2016_437_total : P1_7_1_3.momentEstimate 2016 437 = 454871172326 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2016 + 437 = 2453 by decide]
  exact cost_2016_437_join4_0

theorem moment2016_437 : P1_7_1.groupedPoleMoment 2016 437 ≤ 454871172326 :=
  (P1_7_1_3.grouped_bound 2016 437).trans_eq cost_2016_437_total
private theorem cost_2016_439_block0 : P1_7_1_3.blockEstimate 2016 439 439 128 = 687167520 := by decide +kernel

private theorem cost_2016_439_block1 : P1_7_1_3.blockEstimate 2016 439 567 128 = 4475152416 := by decide +kernel

private theorem cost_2016_439_block2 : P1_7_1_3.blockEstimate 2016 439 695 128 = 11279890464 := by decide +kernel

private theorem cost_2016_439_block3 : P1_7_1_3.blockEstimate 2016 439 823 128 = 20197364550 := by decide +kernel

private theorem cost_2016_439_block4 : P1_7_1_3.blockEstimate 2016 439 951 128 = 28886147840 := by decide +kernel

private theorem cost_2016_439_block5 : P1_7_1_3.blockEstimate 2016 439 1079 128 = 35774309120 := by decide +kernel

private theorem cost_2016_439_block6 : P1_7_1_3.blockEstimate 2016 439 1207 128 = 40816976640 := by decide +kernel

private theorem cost_2016_439_block7 : P1_7_1_3.blockEstimate 2016 439 1335 128 = 44014150400 := by decide +kernel

private theorem cost_2016_439_block8 : P1_7_1_3.blockEstimate 2016 439 1463 128 = 45365830400 := by decide +kernel

private theorem cost_2016_439_block9 : P1_7_1_3.blockEstimate 2016 439 1591 128 = 44872016640 := by decide +kernel

private theorem cost_2016_439_block10 : P1_7_1_3.blockEstimate 2016 439 1719 128 = 42532709120 := by decide +kernel

private theorem cost_2016_439_block11 : P1_7_1_3.blockEstimate 2016 439 1847 128 = 38347907840 := by decide +kernel

private theorem cost_2016_439_block12 : P1_7_1_3.blockEstimate 2016 439 1975 128 = 32386519894 := by decide +kernel

private theorem cost_2016_439_block13 : P1_7_1_3.blockEstimate 2016 439 2103 128 = 25517118881 := by decide +kernel

private theorem cost_2016_439_block14 : P1_7_1_3.blockEstimate 2016 439 2231 128 = 18655466857 := by decide +kernel

private theorem cost_2016_439_block15 : P1_7_1_3.blockEstimate 2016 439 2359 128 = 12310200085 := by decide +kernel

private theorem cost_2016_439_block16 : P1_7_1_3.blockEstimate 2016 439 2487 128 = 6903697696 := by decide +kernel

private theorem cost_2016_439_block17 : P1_7_1_3.blockEstimate 2016 439 2615 128 = 2893295904 := by decide +kernel

private theorem cost_2016_439_block18 : P1_7_1_3.blockEstimate 2016 439 2743 128 = 572608800 := by decide +kernel

private theorem cost_2016_439_block19 : P1_7_1_3.blockEstimate 2016 439 2871 23 = 2451166 := by decide +kernel

private theorem cost_2016_439_join0_0 : P1_7_1_3.blockEstimate 2016 439 439 256 = 5162319936 :=
  @P1_7_1_3.block_append 2016 439 439 567 128 128 256 687167520 4475152416 5162319936 cost_2016_439_block0 cost_2016_439_block1 rfl rfl rfl

private theorem cost_2016_439_join0_2 : P1_7_1_3.blockEstimate 2016 439 695 256 = 31477255014 :=
  @P1_7_1_3.block_append 2016 439 695 823 128 128 256 11279890464 20197364550 31477255014 cost_2016_439_block2 cost_2016_439_block3 rfl rfl rfl

private theorem cost_2016_439_join0_4 : P1_7_1_3.blockEstimate 2016 439 951 256 = 64660456960 :=
  @P1_7_1_3.block_append 2016 439 951 1079 128 128 256 28886147840 35774309120 64660456960 cost_2016_439_block4 cost_2016_439_block5 rfl rfl rfl

private theorem cost_2016_439_join0_6 : P1_7_1_3.blockEstimate 2016 439 1207 256 = 84831127040 :=
  @P1_7_1_3.block_append 2016 439 1207 1335 128 128 256 40816976640 44014150400 84831127040 cost_2016_439_block6 cost_2016_439_block7 rfl rfl rfl

private theorem cost_2016_439_join0_8 : P1_7_1_3.blockEstimate 2016 439 1463 256 = 90237847040 :=
  @P1_7_1_3.block_append 2016 439 1463 1591 128 128 256 45365830400 44872016640 90237847040 cost_2016_439_block8 cost_2016_439_block9 rfl rfl rfl

private theorem cost_2016_439_join0_10 : P1_7_1_3.blockEstimate 2016 439 1719 256 = 80880616960 :=
  @P1_7_1_3.block_append 2016 439 1719 1847 128 128 256 42532709120 38347907840 80880616960 cost_2016_439_block10 cost_2016_439_block11 rfl rfl rfl

private theorem cost_2016_439_join0_12 : P1_7_1_3.blockEstimate 2016 439 1975 256 = 57903638775 :=
  @P1_7_1_3.block_append 2016 439 1975 2103 128 128 256 32386519894 25517118881 57903638775 cost_2016_439_block12 cost_2016_439_block13 rfl rfl rfl

private theorem cost_2016_439_join0_14 : P1_7_1_3.blockEstimate 2016 439 2231 256 = 30965666942 :=
  @P1_7_1_3.block_append 2016 439 2231 2359 128 128 256 18655466857 12310200085 30965666942 cost_2016_439_block14 cost_2016_439_block15 rfl rfl rfl

private theorem cost_2016_439_join0_16 : P1_7_1_3.blockEstimate 2016 439 2487 256 = 9796993600 :=
  @P1_7_1_3.block_append 2016 439 2487 2615 128 128 256 6903697696 2893295904 9796993600 cost_2016_439_block16 cost_2016_439_block17 rfl rfl rfl

private theorem cost_2016_439_join0_18 : P1_7_1_3.blockEstimate 2016 439 2743 151 = 575059966 :=
  @P1_7_1_3.block_append 2016 439 2743 2871 128 23 151 572608800 2451166 575059966 cost_2016_439_block18 cost_2016_439_block19 rfl rfl rfl

private theorem cost_2016_439_join1_0 : P1_7_1_3.blockEstimate 2016 439 439 512 = 36639574950 :=
  @P1_7_1_3.block_append 2016 439 439 695 256 256 512 5162319936 31477255014 36639574950 cost_2016_439_join0_0 cost_2016_439_join0_2 rfl rfl rfl

private theorem cost_2016_439_join1_2 : P1_7_1_3.blockEstimate 2016 439 951 512 = 149491584000 :=
  @P1_7_1_3.block_append 2016 439 951 1207 256 256 512 64660456960 84831127040 149491584000 cost_2016_439_join0_4 cost_2016_439_join0_6 rfl rfl rfl

private theorem cost_2016_439_join1_4 : P1_7_1_3.blockEstimate 2016 439 1463 512 = 171118464000 :=
  @P1_7_1_3.block_append 2016 439 1463 1719 256 256 512 90237847040 80880616960 171118464000 cost_2016_439_join0_8 cost_2016_439_join0_10 rfl rfl rfl

private theorem cost_2016_439_join1_6 : P1_7_1_3.blockEstimate 2016 439 1975 512 = 88869305717 :=
  @P1_7_1_3.block_append 2016 439 1975 2231 256 256 512 57903638775 30965666942 88869305717 cost_2016_439_join0_12 cost_2016_439_join0_14 rfl rfl rfl

private theorem cost_2016_439_join1_8 : P1_7_1_3.blockEstimate 2016 439 2487 407 = 10372053566 :=
  @P1_7_1_3.block_append 2016 439 2487 2743 256 151 407 9796993600 575059966 10372053566 cost_2016_439_join0_16 cost_2016_439_join0_18 rfl rfl rfl

private theorem cost_2016_439_join2_0 : P1_7_1_3.blockEstimate 2016 439 439 1024 = 186131158950 :=
  @P1_7_1_3.block_append 2016 439 439 951 512 512 1024 36639574950 149491584000 186131158950 cost_2016_439_join1_0 cost_2016_439_join1_2 rfl rfl rfl

private theorem cost_2016_439_join2_2 : P1_7_1_3.blockEstimate 2016 439 1463 1024 = 259987769717 :=
  @P1_7_1_3.block_append 2016 439 1463 1975 512 512 1024 171118464000 88869305717 259987769717 cost_2016_439_join1_4 cost_2016_439_join1_6 rfl rfl rfl

private theorem cost_2016_439_join3_0 : P1_7_1_3.blockEstimate 2016 439 439 2048 = 446118928667 :=
  @P1_7_1_3.block_append 2016 439 439 1463 1024 1024 2048 186131158950 259987769717 446118928667 cost_2016_439_join2_0 cost_2016_439_join2_2 rfl rfl rfl

private theorem cost_2016_439_join4_0 : P1_7_1_3.blockEstimate 2016 439 439 2455 = 456490982233 :=
  @P1_7_1_3.block_append 2016 439 439 2487 2048 407 2455 446118928667 10372053566 456490982233 cost_2016_439_join3_0 cost_2016_439_join1_8 rfl rfl rfl

private theorem cost_2016_439_total : P1_7_1_3.momentEstimate 2016 439 = 456490982233 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2016 + 439 = 2455 by decide]
  exact cost_2016_439_join4_0

theorem moment2016_439 : P1_7_1.groupedPoleMoment 2016 439 ≤ 456490982233 :=
  (P1_7_1_3.grouped_bound 2016 439).trans_eq cost_2016_439_total
private theorem cost_2016_445_block0 : P1_7_1_3.blockEstimate 2016 445 445 128 = 687167520 := by decide +kernel

private theorem cost_2016_445_block1 : P1_7_1_3.blockEstimate 2016 445 573 128 = 4475152416 := by decide +kernel

private theorem cost_2016_445_block2 : P1_7_1_3.blockEstimate 2016 445 701 128 = 11279890464 := by decide +kernel

private theorem cost_2016_445_block3 : P1_7_1_3.blockEstimate 2016 445 829 128 = 20219836331 := by decide +kernel

private theorem cost_2016_445_block4 : P1_7_1_3.blockEstimate 2016 445 957 128 = 29033344064 := by decide +kernel

private theorem cost_2016_445_block5 : P1_7_1_3.blockEstimate 2016 445 1085 128 = 36037356608 := by decide +kernel

private theorem cost_2016_445_block6 : P1_7_1_3.blockEstimate 2016 445 1213 128 = 41170709568 := by decide +kernel

private theorem cost_2016_445_block7 : P1_7_1_3.blockEstimate 2016 445 1341 128 = 44433402944 := by decide +kernel

private theorem cost_2016_445_block8 : P1_7_1_3.blockEstimate 2016 445 1469 128 = 45825436736 := by decide +kernel

private theorem cost_2016_445_block9 : P1_7_1_3.blockEstimate 2016 445 1597 128 = 45346810944 := by decide +kernel

private theorem cost_2016_445_block10 : P1_7_1_3.blockEstimate 2016 445 1725 128 = 42997525568 := by decide +kernel

private theorem cost_2016_445_block11 : P1_7_1_3.blockEstimate 2016 445 1853 128 = 38777580608 := by decide +kernel

private theorem cost_2016_445_block12 : P1_7_1_3.blockEstimate 2016 445 1981 128 = 32770686485 := by decide +kernel

private theorem cost_2016_445_block13 : P1_7_1_3.blockEstimate 2016 445 2109 128 = 25879406156 := by decide +kernel

private theorem cost_2016_445_block14 : P1_7_1_3.blockEstimate 2016 445 2237 128 = 18986142832 := by decide +kernel

private theorem cost_2016_445_block15 : P1_7_1_3.blockEstimate 2016 445 2365 128 = 12595745304 := by decide +kernel

private theorem cost_2016_445_block16 : P1_7_1_3.blockEstimate 2016 445 2493 128 = 7128931376 := by decide +kernel

private theorem cost_2016_445_block17 : P1_7_1_3.blockEstimate 2016 445 2621 128 = 3045498928 := by decide +kernel

private theorem cost_2016_445_block18 : P1_7_1_3.blockEstimate 2016 445 2749 128 = 639984688 := by decide +kernel

private theorem cost_2016_445_block19 : P1_7_1_3.blockEstimate 2016 445 2877 29 = 4727212 := by decide +kernel

private theorem cost_2016_445_join0_0 : P1_7_1_3.blockEstimate 2016 445 445 256 = 5162319936 :=
  @P1_7_1_3.block_append 2016 445 445 573 128 128 256 687167520 4475152416 5162319936 cost_2016_445_block0 cost_2016_445_block1 rfl rfl rfl

private theorem cost_2016_445_join0_2 : P1_7_1_3.blockEstimate 2016 445 701 256 = 31499726795 :=
  @P1_7_1_3.block_append 2016 445 701 829 128 128 256 11279890464 20219836331 31499726795 cost_2016_445_block2 cost_2016_445_block3 rfl rfl rfl

private theorem cost_2016_445_join0_4 : P1_7_1_3.blockEstimate 2016 445 957 256 = 65070700672 :=
  @P1_7_1_3.block_append 2016 445 957 1085 128 128 256 29033344064 36037356608 65070700672 cost_2016_445_block4 cost_2016_445_block5 rfl rfl rfl

private theorem cost_2016_445_join0_6 : P1_7_1_3.blockEstimate 2016 445 1213 256 = 85604112512 :=
  @P1_7_1_3.block_append 2016 445 1213 1341 128 128 256 41170709568 44433402944 85604112512 cost_2016_445_block6 cost_2016_445_block7 rfl rfl rfl

private theorem cost_2016_445_join0_8 : P1_7_1_3.blockEstimate 2016 445 1469 256 = 91172247680 :=
  @P1_7_1_3.block_append 2016 445 1469 1597 128 128 256 45825436736 45346810944 91172247680 cost_2016_445_block8 cost_2016_445_block9 rfl rfl rfl

private theorem cost_2016_445_join0_10 : P1_7_1_3.blockEstimate 2016 445 1725 256 = 81775106176 :=
  @P1_7_1_3.block_append 2016 445 1725 1853 128 128 256 42997525568 38777580608 81775106176 cost_2016_445_block10 cost_2016_445_block11 rfl rfl rfl

private theorem cost_2016_445_join0_12 : P1_7_1_3.blockEstimate 2016 445 1981 256 = 58650092641 :=
  @P1_7_1_3.block_append 2016 445 1981 2109 128 128 256 32770686485 25879406156 58650092641 cost_2016_445_block12 cost_2016_445_block13 rfl rfl rfl

private theorem cost_2016_445_join0_14 : P1_7_1_3.blockEstimate 2016 445 2237 256 = 31581888136 :=
  @P1_7_1_3.block_append 2016 445 2237 2365 128 128 256 18986142832 12595745304 31581888136 cost_2016_445_block14 cost_2016_445_block15 rfl rfl rfl

private theorem cost_2016_445_join0_16 : P1_7_1_3.blockEstimate 2016 445 2493 256 = 10174430304 :=
  @P1_7_1_3.block_append 2016 445 2493 2621 128 128 256 7128931376 3045498928 10174430304 cost_2016_445_block16 cost_2016_445_block17 rfl rfl rfl

private theorem cost_2016_445_join0_18 : P1_7_1_3.blockEstimate 2016 445 2749 157 = 644711900 :=
  @P1_7_1_3.block_append 2016 445 2749 2877 128 29 157 639984688 4727212 644711900 cost_2016_445_block18 cost_2016_445_block19 rfl rfl rfl

private theorem cost_2016_445_join1_0 : P1_7_1_3.blockEstimate 2016 445 445 512 = 36662046731 :=
  @P1_7_1_3.block_append 2016 445 445 701 256 256 512 5162319936 31499726795 36662046731 cost_2016_445_join0_0 cost_2016_445_join0_2 rfl rfl rfl

private theorem cost_2016_445_join1_2 : P1_7_1_3.blockEstimate 2016 445 957 512 = 150674813184 :=
  @P1_7_1_3.block_append 2016 445 957 1213 256 256 512 65070700672 85604112512 150674813184 cost_2016_445_join0_4 cost_2016_445_join0_6 rfl rfl rfl

private theorem cost_2016_445_join1_4 : P1_7_1_3.blockEstimate 2016 445 1469 512 = 172947353856 :=
  @P1_7_1_3.block_append 2016 445 1469 1725 256 256 512 91172247680 81775106176 172947353856 cost_2016_445_join0_8 cost_2016_445_join0_10 rfl rfl rfl

private theorem cost_2016_445_join1_6 : P1_7_1_3.blockEstimate 2016 445 1981 512 = 90231980777 :=
  @P1_7_1_3.block_append 2016 445 1981 2237 256 256 512 58650092641 31581888136 90231980777 cost_2016_445_join0_12 cost_2016_445_join0_14 rfl rfl rfl

private theorem cost_2016_445_join1_8 : P1_7_1_3.blockEstimate 2016 445 2493 413 = 10819142204 :=
  @P1_7_1_3.block_append 2016 445 2493 2749 256 157 413 10174430304 644711900 10819142204 cost_2016_445_join0_16 cost_2016_445_join0_18 rfl rfl rfl

private theorem cost_2016_445_join2_0 : P1_7_1_3.blockEstimate 2016 445 445 1024 = 187336859915 :=
  @P1_7_1_3.block_append 2016 445 445 957 512 512 1024 36662046731 150674813184 187336859915 cost_2016_445_join1_0 cost_2016_445_join1_2 rfl rfl rfl

private theorem cost_2016_445_join2_2 : P1_7_1_3.blockEstimate 2016 445 1469 1024 = 263179334633 :=
  @P1_7_1_3.block_append 2016 445 1469 1981 512 512 1024 172947353856 90231980777 263179334633 cost_2016_445_join1_4 cost_2016_445_join1_6 rfl rfl rfl

private theorem cost_2016_445_join3_0 : P1_7_1_3.blockEstimate 2016 445 445 2048 = 450516194548 :=
  @P1_7_1_3.block_append 2016 445 445 1469 1024 1024 2048 187336859915 263179334633 450516194548 cost_2016_445_join2_0 cost_2016_445_join2_2 rfl rfl rfl

private theorem cost_2016_445_join4_0 : P1_7_1_3.blockEstimate 2016 445 445 2461 = 461335336752 :=
  @P1_7_1_3.block_append 2016 445 445 2493 2048 413 2461 450516194548 10819142204 461335336752 cost_2016_445_join3_0 cost_2016_445_join1_8 rfl rfl rfl

private theorem cost_2016_445_total : P1_7_1_3.momentEstimate 2016 445 = 461335336752 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2016 + 445 = 2461 by decide]
  exact cost_2016_445_join4_0

theorem moment2016_445 : P1_7_1.groupedPoleMoment 2016 445 ≤ 461335336752 :=
  (P1_7_1_3.grouped_bound 2016 445).trans_eq cost_2016_445_total
private theorem cost_2068_445_block0 : P1_7_1_3.blockEstimate 2068 445 445 128 = 705771040 := by decide +kernel

private theorem cost_2068_445_block1 : P1_7_1_3.blockEstimate 2068 445 573 128 = 4603659808 := by decide +kernel

private theorem cost_2068_445_block2 : P1_7_1_3.blockEstimate 2068 445 701 128 = 11627353632 := by decide +kernel

private theorem cost_2068_445_block3 : P1_7_1_3.blockEstimate 2068 445 829 128 = 20892701147 := by decide +kernel

private theorem cost_2068_445_block4 : P1_7_1_3.blockEstimate 2068 445 957 128 = 30084219968 := by decide +kernel

private theorem cost_2068_445_block5 : P1_7_1_3.blockEstimate 2068 445 1085 128 = 37468210240 := by decide +kernel

private theorem cost_2068_445_block6 : P1_7_1_3.blockEstimate 2068 445 1213 128 = 42981540928 := by decide +kernel

private theorem cost_2068_445_block7 : P1_7_1_3.blockEstimate 2068 445 1341 128 = 46624212032 := by decide +kernel

private theorem cost_2068_445_block8 : P1_7_1_3.blockEstimate 2068 445 1469 128 = 48396223552 := by decide +kernel

private theorem cost_2068_445_block9 : P1_7_1_3.blockEstimate 2068 445 1597 128 = 48297575488 := by decide +kernel

private theorem cost_2068_445_block10 : P1_7_1_3.blockEstimate 2068 445 1725 128 = 46328267840 := by decide +kernel

private theorem cost_2068_445_block11 : P1_7_1_3.blockEstimate 2068 445 1853 128 = 42488300608 := by decide +kernel

private theorem cost_2068_445_block12 : P1_7_1_3.blockEstimate 2068 445 1981 128 = 36784954772 := by decide +kernel

private theorem cost_2068_445_block13 : P1_7_1_3.blockEstimate 2068 445 2109 128 = 29742337469 := by decide +kernel

private theorem cost_2068_445_block14 : P1_7_1_3.blockEstimate 2068 445 2237 128 = 22476547784 := by decide +kernel

private theorem cost_2068_445_block15 : P1_7_1_3.blockEstimate 2068 445 2365 128 = 15573226951 := by decide +kernel

private theorem cost_2068_445_block16 : P1_7_1_3.blockEstimate 2068 445 2493 128 = 9480006737 := by decide +kernel

private theorem cost_2068_445_block17 : P1_7_1_3.blockEstimate 2068 445 2621 128 = 4643908208 := by decide +kernel

private theorem cost_2068_445_block18 : P1_7_1_3.blockEstimate 2068 445 2749 128 = 1436718704 := by decide +kernel

private theorem cost_2068_445_block19 : P1_7_1_3.blockEstimate 2068 445 2877 81 = 94997938 := by decide +kernel

private theorem cost_2068_445_join0_0 : P1_7_1_3.blockEstimate 2068 445 445 256 = 5309430848 :=
  @P1_7_1_3.block_append 2068 445 445 573 128 128 256 705771040 4603659808 5309430848 cost_2068_445_block0 cost_2068_445_block1 rfl rfl rfl

private theorem cost_2068_445_join0_2 : P1_7_1_3.blockEstimate 2068 445 701 256 = 32520054779 :=
  @P1_7_1_3.block_append 2068 445 701 829 128 128 256 11627353632 20892701147 32520054779 cost_2068_445_block2 cost_2068_445_block3 rfl rfl rfl

private theorem cost_2068_445_join0_4 : P1_7_1_3.blockEstimate 2068 445 957 256 = 67552430208 :=
  @P1_7_1_3.block_append 2068 445 957 1085 128 128 256 30084219968 37468210240 67552430208 cost_2068_445_block4 cost_2068_445_block5 rfl rfl rfl

private theorem cost_2068_445_join0_6 : P1_7_1_3.blockEstimate 2068 445 1213 256 = 89605752960 :=
  @P1_7_1_3.block_append 2068 445 1213 1341 128 128 256 42981540928 46624212032 89605752960 cost_2068_445_block6 cost_2068_445_block7 rfl rfl rfl

private theorem cost_2068_445_join0_8 : P1_7_1_3.blockEstimate 2068 445 1469 256 = 96693799040 :=
  @P1_7_1_3.block_append 2068 445 1469 1597 128 128 256 48396223552 48297575488 96693799040 cost_2068_445_block8 cost_2068_445_block9 rfl rfl rfl

private theorem cost_2068_445_join0_10 : P1_7_1_3.blockEstimate 2068 445 1725 256 = 88816568448 :=
  @P1_7_1_3.block_append 2068 445 1725 1853 128 128 256 46328267840 42488300608 88816568448 cost_2068_445_block10 cost_2068_445_block11 rfl rfl rfl

private theorem cost_2068_445_join0_12 : P1_7_1_3.blockEstimate 2068 445 1981 256 = 66527292241 :=
  @P1_7_1_3.block_append 2068 445 1981 2109 128 128 256 36784954772 29742337469 66527292241 cost_2068_445_block12 cost_2068_445_block13 rfl rfl rfl

private theorem cost_2068_445_join0_14 : P1_7_1_3.blockEstimate 2068 445 2237 256 = 38049774735 :=
  @P1_7_1_3.block_append 2068 445 2237 2365 128 128 256 22476547784 15573226951 38049774735 cost_2068_445_block14 cost_2068_445_block15 rfl rfl rfl

private theorem cost_2068_445_join0_16 : P1_7_1_3.blockEstimate 2068 445 2493 256 = 14123914945 :=
  @P1_7_1_3.block_append 2068 445 2493 2621 128 128 256 9480006737 4643908208 14123914945 cost_2068_445_block16 cost_2068_445_block17 rfl rfl rfl

private theorem cost_2068_445_join0_18 : P1_7_1_3.blockEstimate 2068 445 2749 209 = 1531716642 :=
  @P1_7_1_3.block_append 2068 445 2749 2877 128 81 209 1436718704 94997938 1531716642 cost_2068_445_block18 cost_2068_445_block19 rfl rfl rfl

private theorem cost_2068_445_join1_0 : P1_7_1_3.blockEstimate 2068 445 445 512 = 37829485627 :=
  @P1_7_1_3.block_append 2068 445 445 701 256 256 512 5309430848 32520054779 37829485627 cost_2068_445_join0_0 cost_2068_445_join0_2 rfl rfl rfl

private theorem cost_2068_445_join1_2 : P1_7_1_3.blockEstimate 2068 445 957 512 = 157158183168 :=
  @P1_7_1_3.block_append 2068 445 957 1213 256 256 512 67552430208 89605752960 157158183168 cost_2068_445_join0_4 cost_2068_445_join0_6 rfl rfl rfl

private theorem cost_2068_445_join1_4 : P1_7_1_3.blockEstimate 2068 445 1469 512 = 185510367488 :=
  @P1_7_1_3.block_append 2068 445 1469 1725 256 256 512 96693799040 88816568448 185510367488 cost_2068_445_join0_8 cost_2068_445_join0_10 rfl rfl rfl

private theorem cost_2068_445_join1_6 : P1_7_1_3.blockEstimate 2068 445 1981 512 = 104577066976 :=
  @P1_7_1_3.block_append 2068 445 1981 2237 256 256 512 66527292241 38049774735 104577066976 cost_2068_445_join0_12 cost_2068_445_join0_14 rfl rfl rfl

private theorem cost_2068_445_join1_8 : P1_7_1_3.blockEstimate 2068 445 2493 465 = 15655631587 :=
  @P1_7_1_3.block_append 2068 445 2493 2749 256 209 465 14123914945 1531716642 15655631587 cost_2068_445_join0_16 cost_2068_445_join0_18 rfl rfl rfl

private theorem cost_2068_445_join2_0 : P1_7_1_3.blockEstimate 2068 445 445 1024 = 194987668795 :=
  @P1_7_1_3.block_append 2068 445 445 957 512 512 1024 37829485627 157158183168 194987668795 cost_2068_445_join1_0 cost_2068_445_join1_2 rfl rfl rfl

private theorem cost_2068_445_join2_2 : P1_7_1_3.blockEstimate 2068 445 1469 1024 = 290087434464 :=
  @P1_7_1_3.block_append 2068 445 1469 1981 512 512 1024 185510367488 104577066976 290087434464 cost_2068_445_join1_4 cost_2068_445_join1_6 rfl rfl rfl

private theorem cost_2068_445_join3_0 : P1_7_1_3.blockEstimate 2068 445 445 2048 = 485075103259 :=
  @P1_7_1_3.block_append 2068 445 445 1469 1024 1024 2048 194987668795 290087434464 485075103259 cost_2068_445_join2_0 cost_2068_445_join2_2 rfl rfl rfl

private theorem cost_2068_445_join4_0 : P1_7_1_3.blockEstimate 2068 445 445 2513 = 500730734846 :=
  @P1_7_1_3.block_append 2068 445 445 2493 2048 465 2513 485075103259 15655631587 500730734846 cost_2068_445_join3_0 cost_2068_445_join1_8 rfl rfl rfl

private theorem cost_2068_445_total : P1_7_1_3.momentEstimate 2068 445 = 500730734846 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2068 + 445 = 2513 by decide]
  exact cost_2068_445_join4_0

theorem moment2068_445 : P1_7_1.groupedPoleMoment 2068 445 ≤ 500730734846 :=
  (P1_7_1_3.grouped_bound 2068 445).trans_eq cost_2068_445_total

end Research6966.HelperRescueCatalogue

end Merged6967_Near6967RescueMoment16

section Merged6967_Near6967RescueMoment17
set_option Elab.async false


set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem cost_2071_450_block0 : P1_7_1_3.blockEstimate 2071 450 450 128 = 706844320 := by decide +kernel

private theorem cost_2071_450_block1 : P1_7_1_3.blockEstimate 2071 450 578 128 = 4611073696 := by decide +kernel

private theorem cost_2071_450_block2 : P1_7_1_3.blockEstimate 2071 450 706 128 = 11647399584 := by decide +kernel

private theorem cost_2071_450_block3 : P1_7_1_3.blockEstimate 2071 450 834 128 = 20947970791 := by decide +kernel

private theorem cost_2071_450_block4 : P1_7_1_3.blockEstimate 2071 450 962 128 = 30266963584 := by decide +kernel

private theorem cost_2071_450_block5 : P1_7_1_3.blockEstimate 2071 450 1090 128 = 37774374528 := by decide +kernel

private theorem cost_2071_450_block6 : P1_7_1_3.blockEstimate 2071 450 1218 128 = 43390154368 := by decide +kernel

private theorem cost_2071_450_block7 : P1_7_1_3.blockEstimate 2071 450 1346 128 = 47114303104 := by decide +kernel

private theorem cost_2071_450_block8 : P1_7_1_3.blockEstimate 2071 450 1474 128 = 48946820736 := by decide +kernel

private theorem cost_2071_450_block9 : P1_7_1_3.blockEstimate 2071 450 1602 128 = 48887707264 := by decide +kernel

private theorem cost_2071_450_block10 : P1_7_1_3.blockEstimate 2071 450 1730 128 = 46936962688 := by decide +kernel

private theorem cost_2071_450_block11 : P1_7_1_3.blockEstimate 2071 450 1858 128 = 43094587008 := by decide +kernel

private theorem cost_2071_450_block12 : P1_7_1_3.blockEstimate 2071 450 1986 128 = 37368933635 := by decide +kernel

private theorem cost_2071_450_block13 : P1_7_1_3.blockEstimate 2071 450 2114 128 = 30297614560 := by decide +kernel

private theorem cost_2071_450_block14 : P1_7_1_3.blockEstimate 2071 450 2242 128 = 22987982347 := by decide +kernel

private theorem cost_2071_450_block15 : P1_7_1_3.blockEstimate 2071 450 2370 128 = 16021454860 := by decide +kernel

private theorem cost_2071_450_block16 : P1_7_1_3.blockEstimate 2071 450 2498 128 = 9846544435 := by decide +kernel

private theorem cost_2071_450_block17 : P1_7_1_3.blockEstimate 2071 450 2626 128 = 4908889168 := by decide +kernel

private theorem cost_2071_450_block18 : P1_7_1_3.blockEstimate 2071 450 2754 128 = 1587069008 := by decide +kernel

private theorem cost_2071_450_block19 : P1_7_1_3.blockEstimate 2071 450 2882 89 = 125359292 := by decide +kernel

private theorem cost_2071_450_join0_0 : P1_7_1_3.blockEstimate 2071 450 450 256 = 5317918016 :=
  @P1_7_1_3.block_append 2071 450 450 578 128 128 256 706844320 4611073696 5317918016 cost_2071_450_block0 cost_2071_450_block1 rfl rfl rfl

private theorem cost_2071_450_join0_2 : P1_7_1_3.blockEstimate 2071 450 706 256 = 32595370375 :=
  @P1_7_1_3.block_append 2071 450 706 834 128 128 256 11647399584 20947970791 32595370375 cost_2071_450_block2 cost_2071_450_block3 rfl rfl rfl

private theorem cost_2071_450_join0_4 : P1_7_1_3.blockEstimate 2071 450 962 256 = 68041338112 :=
  @P1_7_1_3.block_append 2071 450 962 1090 128 128 256 30266963584 37774374528 68041338112 cost_2071_450_block4 cost_2071_450_block5 rfl rfl rfl

private theorem cost_2071_450_join0_6 : P1_7_1_3.blockEstimate 2071 450 1218 256 = 90504457472 :=
  @P1_7_1_3.block_append 2071 450 1218 1346 128 128 256 43390154368 47114303104 90504457472 cost_2071_450_block6 cost_2071_450_block7 rfl rfl rfl

private theorem cost_2071_450_join0_8 : P1_7_1_3.blockEstimate 2071 450 1474 256 = 97834528000 :=
  @P1_7_1_3.block_append 2071 450 1474 1602 128 128 256 48946820736 48887707264 97834528000 cost_2071_450_block8 cost_2071_450_block9 rfl rfl rfl

private theorem cost_2071_450_join0_10 : P1_7_1_3.blockEstimate 2071 450 1730 256 = 90031549696 :=
  @P1_7_1_3.block_append 2071 450 1730 1858 128 128 256 46936962688 43094587008 90031549696 cost_2071_450_block10 cost_2071_450_block11 rfl rfl rfl

private theorem cost_2071_450_join0_12 : P1_7_1_3.blockEstimate 2071 450 1986 256 = 67666548195 :=
  @P1_7_1_3.block_append 2071 450 1986 2114 128 128 256 37368933635 30297614560 67666548195 cost_2071_450_block12 cost_2071_450_block13 rfl rfl rfl

private theorem cost_2071_450_join0_14 : P1_7_1_3.blockEstimate 2071 450 2242 256 = 39009437207 :=
  @P1_7_1_3.block_append 2071 450 2242 2370 128 128 256 22987982347 16021454860 39009437207 cost_2071_450_block14 cost_2071_450_block15 rfl rfl rfl

private theorem cost_2071_450_join0_16 : P1_7_1_3.blockEstimate 2071 450 2498 256 = 14755433603 :=
  @P1_7_1_3.block_append 2071 450 2498 2626 128 128 256 9846544435 4908889168 14755433603 cost_2071_450_block16 cost_2071_450_block17 rfl rfl rfl

private theorem cost_2071_450_join0_18 : P1_7_1_3.blockEstimate 2071 450 2754 217 = 1712428300 :=
  @P1_7_1_3.block_append 2071 450 2754 2882 128 89 217 1587069008 125359292 1712428300 cost_2071_450_block18 cost_2071_450_block19 rfl rfl rfl

private theorem cost_2071_450_join1_0 : P1_7_1_3.blockEstimate 2071 450 450 512 = 37913288391 :=
  @P1_7_1_3.block_append 2071 450 450 706 256 256 512 5317918016 32595370375 37913288391 cost_2071_450_join0_0 cost_2071_450_join0_2 rfl rfl rfl

private theorem cost_2071_450_join1_2 : P1_7_1_3.blockEstimate 2071 450 962 512 = 158545795584 :=
  @P1_7_1_3.block_append 2071 450 962 1218 256 256 512 68041338112 90504457472 158545795584 cost_2071_450_join0_4 cost_2071_450_join0_6 rfl rfl rfl

private theorem cost_2071_450_join1_4 : P1_7_1_3.blockEstimate 2071 450 1474 512 = 187866077696 :=
  @P1_7_1_3.block_append 2071 450 1474 1730 256 256 512 97834528000 90031549696 187866077696 cost_2071_450_join0_8 cost_2071_450_join0_10 rfl rfl rfl

private theorem cost_2071_450_join1_6 : P1_7_1_3.blockEstimate 2071 450 1986 512 = 106675985402 :=
  @P1_7_1_3.block_append 2071 450 1986 2242 256 256 512 67666548195 39009437207 106675985402 cost_2071_450_join0_12 cost_2071_450_join0_14 rfl rfl rfl

private theorem cost_2071_450_join1_8 : P1_7_1_3.blockEstimate 2071 450 2498 473 = 16467861903 :=
  @P1_7_1_3.block_append 2071 450 2498 2754 256 217 473 14755433603 1712428300 16467861903 cost_2071_450_join0_16 cost_2071_450_join0_18 rfl rfl rfl

private theorem cost_2071_450_join2_0 : P1_7_1_3.blockEstimate 2071 450 450 1024 = 196459083975 :=
  @P1_7_1_3.block_append 2071 450 450 962 512 512 1024 37913288391 158545795584 196459083975 cost_2071_450_join1_0 cost_2071_450_join1_2 rfl rfl rfl

private theorem cost_2071_450_join2_2 : P1_7_1_3.blockEstimate 2071 450 1474 1024 = 294542063098 :=
  @P1_7_1_3.block_append 2071 450 1474 1986 512 512 1024 187866077696 106675985402 294542063098 cost_2071_450_join1_4 cost_2071_450_join1_6 rfl rfl rfl

private theorem cost_2071_450_join3_0 : P1_7_1_3.blockEstimate 2071 450 450 2048 = 491001147073 :=
  @P1_7_1_3.block_append 2071 450 450 1474 1024 1024 2048 196459083975 294542063098 491001147073 cost_2071_450_join2_0 cost_2071_450_join2_2 rfl rfl rfl

private theorem cost_2071_450_join4_0 : P1_7_1_3.blockEstimate 2071 450 450 2521 = 507469008976 :=
  @P1_7_1_3.block_append 2071 450 450 2498 2048 473 2521 491001147073 16467861903 507469008976 cost_2071_450_join3_0 cost_2071_450_join1_8 rfl rfl rfl

private theorem cost_2071_450_total : P1_7_1_3.momentEstimate 2071 450 = 507469008976 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2071 + 450 = 2521 by decide]
  exact cost_2071_450_join4_0

theorem moment2071_450 : P1_7_1.groupedPoleMoment 2071 450 ≤ 507469008976 :=
  (P1_7_1_3.grouped_bound 2071 450).trans_eq cost_2071_450_total
private theorem cost_2071_459_block0 : P1_7_1_3.blockEstimate 2071 459 459 128 = 706844320 := by decide +kernel

private theorem cost_2071_459_block1 : P1_7_1_3.blockEstimate 2071 459 587 128 = 4611073696 := by decide +kernel

private theorem cost_2071_459_block2 : P1_7_1_3.blockEstimate 2071 459 715 128 = 11647399584 := by decide +kernel

private theorem cost_2071_459_block3 : P1_7_1_3.blockEstimate 2071 459 843 128 = 20971505125 := by decide +kernel

private theorem cost_2071_459_block4 : P1_7_1_3.blockEstimate 2071 459 971 128 = 30474712960 := by decide +kernel

private theorem cost_2071_459_block5 : P1_7_1_3.blockEstimate 2071 459 1099 128 = 38165854080 := by decide +kernel

private theorem cost_2071_459_block6 : P1_7_1_3.blockEstimate 2071 459 1227 128 = 43927615360 := by decide +kernel

private theorem cost_2071_459_block7 : P1_7_1_3.blockEstimate 2071 459 1355 128 = 47759996800 := by decide +kernel

private theorem cost_2071_459_block8 : P1_7_1_3.blockEstimate 2071 459 1483 128 = 49662998400 := by decide +kernel

private theorem cost_2071_459_block9 : P1_7_1_3.blockEstimate 2071 459 1611 128 = 49636620160 := by decide +kernel

private theorem cost_2071_459_block10 : P1_7_1_3.blockEstimate 2071 459 1739 128 = 47680862080 := by decide +kernel

private theorem cost_2071_459_block11 : P1_7_1_3.blockEstimate 2071 459 1867 128 = 43795724160 := by decide +kernel

private theorem cost_2071_459_block12 : P1_7_1_3.blockEstimate 2071 459 1995 128 = 37995799920 := by decide +kernel

private theorem cost_2071_459_block13 : P1_7_1_3.blockEstimate 2071 459 2123 128 = 30884379500 := by decide +kernel

private theorem cost_2071_459_block14 : P1_7_1_3.blockEstimate 2071 459 2251 128 = 23533334693 := by decide +kernel

private theorem cost_2071_459_block15 : P1_7_1_3.blockEstimate 2071 459 2379 128 = 16505884915 := by decide +kernel

private theorem cost_2071_459_block16 : P1_7_1_3.blockEstimate 2071 459 2507 128 = 10248114297 := by decide +kernel

private theorem cost_2071_459_block17 : P1_7_1_3.blockEstimate 2071 459 2635 128 = 5206257488 := by decide +kernel

private theorem cost_2071_459_block18 : P1_7_1_3.blockEstimate 2071 459 2763 128 = 1762472784 := by decide +kernel

private theorem cost_2071_459_block19 : P1_7_1_3.blockEstimate 2071 459 2891 98 = 166261600 := by decide +kernel

private theorem cost_2071_459_join0_0 : P1_7_1_3.blockEstimate 2071 459 459 256 = 5317918016 :=
  @P1_7_1_3.block_append 2071 459 459 587 128 128 256 706844320 4611073696 5317918016 cost_2071_459_block0 cost_2071_459_block1 rfl rfl rfl

private theorem cost_2071_459_join0_2 : P1_7_1_3.blockEstimate 2071 459 715 256 = 32618904709 :=
  @P1_7_1_3.block_append 2071 459 715 843 128 128 256 11647399584 20971505125 32618904709 cost_2071_459_block2 cost_2071_459_block3 rfl rfl rfl

private theorem cost_2071_459_join0_4 : P1_7_1_3.blockEstimate 2071 459 971 256 = 68640567040 :=
  @P1_7_1_3.block_append 2071 459 971 1099 128 128 256 30474712960 38165854080 68640567040 cost_2071_459_block4 cost_2071_459_block5 rfl rfl rfl

private theorem cost_2071_459_join0_6 : P1_7_1_3.blockEstimate 2071 459 1227 256 = 91687612160 :=
  @P1_7_1_3.block_append 2071 459 1227 1355 128 128 256 43927615360 47759996800 91687612160 cost_2071_459_block6 cost_2071_459_block7 rfl rfl rfl

private theorem cost_2071_459_join0_8 : P1_7_1_3.blockEstimate 2071 459 1483 256 = 99299618560 :=
  @P1_7_1_3.block_append 2071 459 1483 1611 128 128 256 49662998400 49636620160 99299618560 cost_2071_459_block8 cost_2071_459_block9 rfl rfl rfl

private theorem cost_2071_459_join0_10 : P1_7_1_3.blockEstimate 2071 459 1739 256 = 91476586240 :=
  @P1_7_1_3.block_append 2071 459 1739 1867 128 128 256 47680862080 43795724160 91476586240 cost_2071_459_block10 cost_2071_459_block11 rfl rfl rfl

private theorem cost_2071_459_join0_12 : P1_7_1_3.blockEstimate 2071 459 1995 256 = 68880179420 :=
  @P1_7_1_3.block_append 2071 459 1995 2123 128 128 256 37995799920 30884379500 68880179420 cost_2071_459_block12 cost_2071_459_block13 rfl rfl rfl

private theorem cost_2071_459_join0_14 : P1_7_1_3.blockEstimate 2071 459 2251 256 = 40039219608 :=
  @P1_7_1_3.block_append 2071 459 2251 2379 128 128 256 23533334693 16505884915 40039219608 cost_2071_459_block14 cost_2071_459_block15 rfl rfl rfl

private theorem cost_2071_459_join0_16 : P1_7_1_3.blockEstimate 2071 459 2507 256 = 15454371785 :=
  @P1_7_1_3.block_append 2071 459 2507 2635 128 128 256 10248114297 5206257488 15454371785 cost_2071_459_block16 cost_2071_459_block17 rfl rfl rfl

private theorem cost_2071_459_join0_18 : P1_7_1_3.blockEstimate 2071 459 2763 226 = 1928734384 :=
  @P1_7_1_3.block_append 2071 459 2763 2891 128 98 226 1762472784 166261600 1928734384 cost_2071_459_block18 cost_2071_459_block19 rfl rfl rfl

private theorem cost_2071_459_join1_0 : P1_7_1_3.blockEstimate 2071 459 459 512 = 37936822725 :=
  @P1_7_1_3.block_append 2071 459 459 715 256 256 512 5317918016 32618904709 37936822725 cost_2071_459_join0_0 cost_2071_459_join0_2 rfl rfl rfl

private theorem cost_2071_459_join1_2 : P1_7_1_3.blockEstimate 2071 459 971 512 = 160328179200 :=
  @P1_7_1_3.block_append 2071 459 971 1227 256 256 512 68640567040 91687612160 160328179200 cost_2071_459_join0_4 cost_2071_459_join0_6 rfl rfl rfl

private theorem cost_2071_459_join1_4 : P1_7_1_3.blockEstimate 2071 459 1483 512 = 190776204800 :=
  @P1_7_1_3.block_append 2071 459 1483 1739 256 256 512 99299618560 91476586240 190776204800 cost_2071_459_join0_8 cost_2071_459_join0_10 rfl rfl rfl

private theorem cost_2071_459_join1_6 : P1_7_1_3.blockEstimate 2071 459 1995 512 = 108919399028 :=
  @P1_7_1_3.block_append 2071 459 1995 2251 256 256 512 68880179420 40039219608 108919399028 cost_2071_459_join0_12 cost_2071_459_join0_14 rfl rfl rfl

private theorem cost_2071_459_join1_8 : P1_7_1_3.blockEstimate 2071 459 2507 482 = 17383106169 :=
  @P1_7_1_3.block_append 2071 459 2507 2763 256 226 482 15454371785 1928734384 17383106169 cost_2071_459_join0_16 cost_2071_459_join0_18 rfl rfl rfl

private theorem cost_2071_459_join2_0 : P1_7_1_3.blockEstimate 2071 459 459 1024 = 198265001925 :=
  @P1_7_1_3.block_append 2071 459 459 971 512 512 1024 37936822725 160328179200 198265001925 cost_2071_459_join1_0 cost_2071_459_join1_2 rfl rfl rfl

private theorem cost_2071_459_join2_2 : P1_7_1_3.blockEstimate 2071 459 1483 1024 = 299695603828 :=
  @P1_7_1_3.block_append 2071 459 1483 1995 512 512 1024 190776204800 108919399028 299695603828 cost_2071_459_join1_4 cost_2071_459_join1_6 rfl rfl rfl

private theorem cost_2071_459_join3_0 : P1_7_1_3.blockEstimate 2071 459 459 2048 = 497960605753 :=
  @P1_7_1_3.block_append 2071 459 459 1483 1024 1024 2048 198265001925 299695603828 497960605753 cost_2071_459_join2_0 cost_2071_459_join2_2 rfl rfl rfl

private theorem cost_2071_459_join4_0 : P1_7_1_3.blockEstimate 2071 459 459 2530 = 515343711922 :=
  @P1_7_1_3.block_append 2071 459 459 2507 2048 482 2530 497960605753 17383106169 515343711922 cost_2071_459_join3_0 cost_2071_459_join1_8 rfl rfl rfl

private theorem cost_2071_459_total : P1_7_1_3.momentEstimate 2071 459 = 515343711922 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2071 + 459 = 2530 by decide]
  exact cost_2071_459_join4_0

theorem moment2071_459 : P1_7_1.groupedPoleMoment 2071 459 ≤ 515343711922 :=
  (P1_7_1_3.grouped_bound 2071 459).trans_eq cost_2071_459_total
private theorem cost_2071_461_block0 : P1_7_1_3.blockEstimate 2071 461 461 128 = 706844320 := by decide +kernel

private theorem cost_2071_461_block1 : P1_7_1_3.blockEstimate 2071 461 589 128 = 4611073696 := by decide +kernel

private theorem cost_2071_461_block2 : P1_7_1_3.blockEstimate 2071 461 717 128 = 11647399584 := by decide +kernel

private theorem cost_2071_461_block3 : P1_7_1_3.blockEstimate 2071 461 845 128 = 20975768891 := by decide +kernel

private theorem cost_2071_461_block4 : P1_7_1_3.blockEstimate 2071 461 973 128 = 30518773824 := by decide +kernel

private theorem cost_2071_461_block5 : P1_7_1_3.blockEstimate 2071 461 1101 128 = 38250924096 := by decide +kernel

private theorem cost_2071_461_block6 : P1_7_1_3.blockEstimate 2071 461 1229 128 = 44045305920 := by decide +kernel

private theorem cost_2071_461_block7 : P1_7_1_3.blockEstimate 2071 461 1357 128 = 47901919296 := by decide +kernel

private theorem cost_2071_461_block8 : P1_7_1_3.blockEstimate 2071 461 1485 128 = 49820764224 := by decide +kernel

private theorem cost_2071_461_block9 : P1_7_1_3.blockEstimate 2071 461 1613 128 = 49801840704 := by decide +kernel

private theorem cost_2071_461_block10 : P1_7_1_3.blockEstimate 2071 461 1741 128 = 47845148736 := by decide +kernel

private theorem cost_2071_461_block11 : P1_7_1_3.blockEstimate 2071 461 1869 128 = 43950688320 := by decide +kernel

private theorem cost_2071_461_block12 : P1_7_1_3.blockEstimate 2071 461 1997 128 = 38134761931 := by decide +kernel

private theorem cost_2071_461_block13 : P1_7_1_3.blockEstimate 2071 461 2125 128 = 31015129396 := by decide +kernel

private theorem cost_2071_461_block14 : P1_7_1_3.blockEstimate 2071 461 2253 128 = 23655073242 := by decide +kernel

private theorem cost_2071_461_block15 : P1_7_1_3.blockEstimate 2071 461 2381 128 = 16614267607 := by decide +kernel

private theorem cost_2071_461_block16 : P1_7_1_3.blockEstimate 2071 461 2509 128 = 10338260170 := by decide +kernel

private theorem cost_2071_461_block17 : P1_7_1_3.blockEstimate 2071 461 2637 128 = 5273416576 := by decide +kernel

private theorem cost_2071_461_block18 : P1_7_1_3.blockEstimate 2071 461 2765 128 = 1802697600 := by decide +kernel

private theorem cost_2071_461_block19 : P1_7_1_3.blockEstimate 2071 461 2893 100 = 176409850 := by decide +kernel

private theorem cost_2071_461_join0_0 : P1_7_1_3.blockEstimate 2071 461 461 256 = 5317918016 :=
  @P1_7_1_3.block_append 2071 461 461 589 128 128 256 706844320 4611073696 5317918016 cost_2071_461_block0 cost_2071_461_block1 rfl rfl rfl

private theorem cost_2071_461_join0_2 : P1_7_1_3.blockEstimate 2071 461 717 256 = 32623168475 :=
  @P1_7_1_3.block_append 2071 461 717 845 128 128 256 11647399584 20975768891 32623168475 cost_2071_461_block2 cost_2071_461_block3 rfl rfl rfl

private theorem cost_2071_461_join0_4 : P1_7_1_3.blockEstimate 2071 461 973 256 = 68769697920 :=
  @P1_7_1_3.block_append 2071 461 973 1101 128 128 256 30518773824 38250924096 68769697920 cost_2071_461_block4 cost_2071_461_block5 rfl rfl rfl

private theorem cost_2071_461_join0_6 : P1_7_1_3.blockEstimate 2071 461 1229 256 = 91947225216 :=
  @P1_7_1_3.block_append 2071 461 1229 1357 128 128 256 44045305920 47901919296 91947225216 cost_2071_461_block6 cost_2071_461_block7 rfl rfl rfl

private theorem cost_2071_461_join0_8 : P1_7_1_3.blockEstimate 2071 461 1485 256 = 99622604928 :=
  @P1_7_1_3.block_append 2071 461 1485 1613 128 128 256 49820764224 49801840704 99622604928 cost_2071_461_block8 cost_2071_461_block9 rfl rfl rfl

private theorem cost_2071_461_join0_10 : P1_7_1_3.blockEstimate 2071 461 1741 256 = 91795837056 :=
  @P1_7_1_3.block_append 2071 461 1741 1869 128 128 256 47845148736 43950688320 91795837056 cost_2071_461_block10 cost_2071_461_block11 rfl rfl rfl

private theorem cost_2071_461_join0_12 : P1_7_1_3.blockEstimate 2071 461 1997 256 = 69149891327 :=
  @P1_7_1_3.block_append 2071 461 1997 2125 128 128 256 38134761931 31015129396 69149891327 cost_2071_461_block12 cost_2071_461_block13 rfl rfl rfl

private theorem cost_2071_461_join0_14 : P1_7_1_3.blockEstimate 2071 461 2253 256 = 40269340849 :=
  @P1_7_1_3.block_append 2071 461 2253 2381 128 128 256 23655073242 16614267607 40269340849 cost_2071_461_block14 cost_2071_461_block15 rfl rfl rfl

private theorem cost_2071_461_join0_16 : P1_7_1_3.blockEstimate 2071 461 2509 256 = 15611676746 :=
  @P1_7_1_3.block_append 2071 461 2509 2637 128 128 256 10338260170 5273416576 15611676746 cost_2071_461_block16 cost_2071_461_block17 rfl rfl rfl

private theorem cost_2071_461_join0_18 : P1_7_1_3.blockEstimate 2071 461 2765 228 = 1979107450 :=
  @P1_7_1_3.block_append 2071 461 2765 2893 128 100 228 1802697600 176409850 1979107450 cost_2071_461_block18 cost_2071_461_block19 rfl rfl rfl

private theorem cost_2071_461_join1_0 : P1_7_1_3.blockEstimate 2071 461 461 512 = 37941086491 :=
  @P1_7_1_3.block_append 2071 461 461 717 256 256 512 5317918016 32623168475 37941086491 cost_2071_461_join0_0 cost_2071_461_join0_2 rfl rfl rfl

private theorem cost_2071_461_join1_2 : P1_7_1_3.blockEstimate 2071 461 973 512 = 160716923136 :=
  @P1_7_1_3.block_append 2071 461 973 1229 256 256 512 68769697920 91947225216 160716923136 cost_2071_461_join0_4 cost_2071_461_join0_6 rfl rfl rfl

private theorem cost_2071_461_join1_4 : P1_7_1_3.blockEstimate 2071 461 1485 512 = 191418441984 :=
  @P1_7_1_3.block_append 2071 461 1485 1741 256 256 512 99622604928 91795837056 191418441984 cost_2071_461_join0_8 cost_2071_461_join0_10 rfl rfl rfl

private theorem cost_2071_461_join1_6 : P1_7_1_3.blockEstimate 2071 461 1997 512 = 109419232176 :=
  @P1_7_1_3.block_append 2071 461 1997 2253 256 256 512 69149891327 40269340849 109419232176 cost_2071_461_join0_12 cost_2071_461_join0_14 rfl rfl rfl

private theorem cost_2071_461_join1_8 : P1_7_1_3.blockEstimate 2071 461 2509 484 = 17590784196 :=
  @P1_7_1_3.block_append 2071 461 2509 2765 256 228 484 15611676746 1979107450 17590784196 cost_2071_461_join0_16 cost_2071_461_join0_18 rfl rfl rfl

private theorem cost_2071_461_join2_0 : P1_7_1_3.blockEstimate 2071 461 461 1024 = 198658009627 :=
  @P1_7_1_3.block_append 2071 461 461 973 512 512 1024 37941086491 160716923136 198658009627 cost_2071_461_join1_0 cost_2071_461_join1_2 rfl rfl rfl

private theorem cost_2071_461_join2_2 : P1_7_1_3.blockEstimate 2071 461 1485 1024 = 300837674160 :=
  @P1_7_1_3.block_append 2071 461 1485 1997 512 512 1024 191418441984 109419232176 300837674160 cost_2071_461_join1_4 cost_2071_461_join1_6 rfl rfl rfl

private theorem cost_2071_461_join3_0 : P1_7_1_3.blockEstimate 2071 461 461 2048 = 499495683787 :=
  @P1_7_1_3.block_append 2071 461 461 1485 1024 1024 2048 198658009627 300837674160 499495683787 cost_2071_461_join2_0 cost_2071_461_join2_2 rfl rfl rfl

private theorem cost_2071_461_join4_0 : P1_7_1_3.blockEstimate 2071 461 461 2532 = 517086467983 :=
  @P1_7_1_3.block_append 2071 461 461 2509 2048 484 2532 499495683787 17590784196 517086467983 cost_2071_461_join3_0 cost_2071_461_join1_8 rfl rfl rfl

private theorem cost_2071_461_total : P1_7_1_3.momentEstimate 2071 461 = 517086467983 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2071 + 461 = 2532 by decide]
  exact cost_2071_461_join4_0

theorem moment2071_461 : P1_7_1.groupedPoleMoment 2071 461 ≤ 517086467983 :=
  (P1_7_1_3.grouped_bound 2071 461).trans_eq cost_2071_461_total
private theorem cost_2073_450_block0 : P1_7_1_3.blockEstimate 2073 450 450 128 = 707559840 := by decide +kernel

private theorem cost_2073_450_block1 : P1_7_1_3.blockEstimate 2073 450 578 128 = 4616016288 := by decide +kernel

private theorem cost_2073_450_block2 : P1_7_1_3.blockEstimate 2073 450 706 128 = 11660763552 := by decide +kernel

private theorem cost_2073_450_block3 : P1_7_1_3.blockEstimate 2073 450 834 128 = 20973871017 := by decide +kernel

private theorem cost_2073_450_block4 : P1_7_1_3.blockEstimate 2073 450 962 128 = 30307546368 := by decide +kernel

private theorem cost_2073_450_block5 : P1_7_1_3.blockEstimate 2073 450 1090 128 = 37829735680 := by decide +kernel

private theorem cost_2073_450_block6 : P1_7_1_3.blockEstimate 2073 450 1218 128 = 43460293888 := by decide +kernel

private theorem cost_2073_450_block7 : P1_7_1_3.blockEstimate 2073 450 1346 128 = 47199220992 := by decide +kernel

private theorem cost_2073_450_block8 : P1_7_1_3.blockEstimate 2073 450 1474 128 = 49046516992 := by decide +kernel

private theorem cost_2073_450_block9 : P1_7_1_3.blockEstimate 2073 450 1602 128 = 49002181888 := by decide +kernel

private theorem cost_2073_450_block10 : P1_7_1_3.blockEstimate 2073 450 1730 128 = 47066215680 := by decide +kernel

private theorem cost_2073_450_block11 : P1_7_1_3.blockEstimate 2073 450 1858 128 = 43238618368 := by decide +kernel

private theorem cost_2073_450_block12 : P1_7_1_3.blockEstimate 2073 450 1986 128 = 37526641182 := by decide +kernel

private theorem cost_2073_450_block13 : P1_7_1_3.blockEstimate 2073 450 2114 128 = 30452502965 := by decide +kernel

private theorem cost_2073_450_block14 : P1_7_1_3.blockEstimate 2073 450 2242 128 = 23129544588 := by decide +kernel

private theorem cost_2073_450_block15 : P1_7_1_3.blockEstimate 2073 450 2370 128 = 16143986442 := by decide +kernel

private theorem cost_2073_450_block16 : P1_7_1_3.blockEstimate 2073 450 2498 128 = 9945843269 := by decide +kernel

private theorem cost_2073_450_block17 : P1_7_1_3.blockEstimate 2073 450 2626 128 = 4979550496 := by decide +kernel

private theorem cost_2073_450_block18 : P1_7_1_3.blockEstimate 2073 450 2754 128 = 1626906912 := by decide +kernel

private theorem cost_2073_450_block19 : P1_7_1_3.blockEstimate 2073 450 2882 91 = 133926723 := by decide +kernel

private theorem cost_2073_450_join0_0 : P1_7_1_3.blockEstimate 2073 450 450 256 = 5323576128 :=
  @P1_7_1_3.block_append 2073 450 450 578 128 128 256 707559840 4616016288 5323576128 cost_2073_450_block0 cost_2073_450_block1 rfl rfl rfl

private theorem cost_2073_450_join0_2 : P1_7_1_3.blockEstimate 2073 450 706 256 = 32634634569 :=
  @P1_7_1_3.block_append 2073 450 706 834 128 128 256 11660763552 20973871017 32634634569 cost_2073_450_block2 cost_2073_450_block3 rfl rfl rfl

private theorem cost_2073_450_join0_4 : P1_7_1_3.blockEstimate 2073 450 962 256 = 68137282048 :=
  @P1_7_1_3.block_append 2073 450 962 1090 128 128 256 30307546368 37829735680 68137282048 cost_2073_450_block4 cost_2073_450_block5 rfl rfl rfl

private theorem cost_2073_450_join0_6 : P1_7_1_3.blockEstimate 2073 450 1218 256 = 90659514880 :=
  @P1_7_1_3.block_append 2073 450 1218 1346 128 128 256 43460293888 47199220992 90659514880 cost_2073_450_block6 cost_2073_450_block7 rfl rfl rfl

private theorem cost_2073_450_join0_8 : P1_7_1_3.blockEstimate 2073 450 1474 256 = 98048698880 :=
  @P1_7_1_3.block_append 2073 450 1474 1602 128 128 256 49046516992 49002181888 98048698880 cost_2073_450_block8 cost_2073_450_block9 rfl rfl rfl

private theorem cost_2073_450_join0_10 : P1_7_1_3.blockEstimate 2073 450 1730 256 = 90304834048 :=
  @P1_7_1_3.block_append 2073 450 1730 1858 128 128 256 47066215680 43238618368 90304834048 cost_2073_450_block10 cost_2073_450_block11 rfl rfl rfl

private theorem cost_2073_450_join0_12 : P1_7_1_3.blockEstimate 2073 450 1986 256 = 67979144147 :=
  @P1_7_1_3.block_append 2073 450 1986 2114 128 128 256 37526641182 30452502965 67979144147 cost_2073_450_block12 cost_2073_450_block13 rfl rfl rfl

private theorem cost_2073_450_join0_14 : P1_7_1_3.blockEstimate 2073 450 2242 256 = 39273531030 :=
  @P1_7_1_3.block_append 2073 450 2242 2370 128 128 256 23129544588 16143986442 39273531030 cost_2073_450_block14 cost_2073_450_block15 rfl rfl rfl

private theorem cost_2073_450_join0_16 : P1_7_1_3.blockEstimate 2073 450 2498 256 = 14925393765 :=
  @P1_7_1_3.block_append 2073 450 2498 2626 128 128 256 9945843269 4979550496 14925393765 cost_2073_450_block16 cost_2073_450_block17 rfl rfl rfl

private theorem cost_2073_450_join0_18 : P1_7_1_3.blockEstimate 2073 450 2754 219 = 1760833635 :=
  @P1_7_1_3.block_append 2073 450 2754 2882 128 91 219 1626906912 133926723 1760833635 cost_2073_450_block18 cost_2073_450_block19 rfl rfl rfl

private theorem cost_2073_450_join1_0 : P1_7_1_3.blockEstimate 2073 450 450 512 = 37958210697 :=
  @P1_7_1_3.block_append 2073 450 450 706 256 256 512 5323576128 32634634569 37958210697 cost_2073_450_join0_0 cost_2073_450_join0_2 rfl rfl rfl

private theorem cost_2073_450_join1_2 : P1_7_1_3.blockEstimate 2073 450 962 512 = 158796796928 :=
  @P1_7_1_3.block_append 2073 450 962 1218 256 256 512 68137282048 90659514880 158796796928 cost_2073_450_join0_4 cost_2073_450_join0_6 rfl rfl rfl

private theorem cost_2073_450_join1_4 : P1_7_1_3.blockEstimate 2073 450 1474 512 = 188353532928 :=
  @P1_7_1_3.block_append 2073 450 1474 1730 256 256 512 98048698880 90304834048 188353532928 cost_2073_450_join0_8 cost_2073_450_join0_10 rfl rfl rfl

private theorem cost_2073_450_join1_6 : P1_7_1_3.blockEstimate 2073 450 1986 512 = 107252675177 :=
  @P1_7_1_3.block_append 2073 450 1986 2242 256 256 512 67979144147 39273531030 107252675177 cost_2073_450_join0_12 cost_2073_450_join0_14 rfl rfl rfl

private theorem cost_2073_450_join1_8 : P1_7_1_3.blockEstimate 2073 450 2498 475 = 16686227400 :=
  @P1_7_1_3.block_append 2073 450 2498 2754 256 219 475 14925393765 1760833635 16686227400 cost_2073_450_join0_16 cost_2073_450_join0_18 rfl rfl rfl

private theorem cost_2073_450_join2_0 : P1_7_1_3.blockEstimate 2073 450 450 1024 = 196755007625 :=
  @P1_7_1_3.block_append 2073 450 450 962 512 512 1024 37958210697 158796796928 196755007625 cost_2073_450_join1_0 cost_2073_450_join1_2 rfl rfl rfl

private theorem cost_2073_450_join2_2 : P1_7_1_3.blockEstimate 2073 450 1474 1024 = 295606208105 :=
  @P1_7_1_3.block_append 2073 450 1474 1986 512 512 1024 188353532928 107252675177 295606208105 cost_2073_450_join1_4 cost_2073_450_join1_6 rfl rfl rfl

private theorem cost_2073_450_join3_0 : P1_7_1_3.blockEstimate 2073 450 450 2048 = 492361215730 :=
  @P1_7_1_3.block_append 2073 450 450 1474 1024 1024 2048 196755007625 295606208105 492361215730 cost_2073_450_join2_0 cost_2073_450_join2_2 rfl rfl rfl

private theorem cost_2073_450_join4_0 : P1_7_1_3.blockEstimate 2073 450 450 2523 = 509047443130 :=
  @P1_7_1_3.block_append 2073 450 450 2498 2048 475 2523 492361215730 16686227400 509047443130 cost_2073_450_join3_0 cost_2073_450_join1_8 rfl rfl rfl

private theorem cost_2073_450_total : P1_7_1_3.momentEstimate 2073 450 = 509047443130 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2073 + 450 = 2523 by decide]
  exact cost_2073_450_join4_0

theorem moment2073_450 : P1_7_1.groupedPoleMoment 2073 450 ≤ 509047443130 :=
  (P1_7_1_3.grouped_bound 2073 450).trans_eq cost_2073_450_total
private theorem cost_2152_463_block0 : P1_7_1_3.blockEstimate 2152 463 463 128 = 735822880 := by decide +kernel

private theorem cost_2152_463_block1 : P1_7_1_3.blockEstimate 2152 463 591 128 = 4811248672 := by decide +kernel

private theorem cost_2152_463_block2 : P1_7_1_3.blockEstimate 2152 463 719 128 = 12188640288 := by decide +kernel

private theorem cost_2152_463_block3 : P1_7_1_3.blockEstimate 2152 463 847 128 = 22030297460 := by decide +kernel

private theorem cost_2152_463_block4 : P1_7_1_3.blockEstimate 2152 463 975 128 = 32221778432 := by decide +kernel

private theorem cost_2152_463_block5 : P1_7_1_3.blockEstimate 2152 463 1103 128 = 40610779648 := by decide +kernel

private theorem cost_2152_463_block6 : P1_7_1_3.blockEstimate 2152 463 1231 128 = 47053623808 := by decide +kernel

private theorem cost_2152_463_block7 : P1_7_1_3.blockEstimate 2152 463 1359 128 = 51550310912 := by decide +kernel

private theorem cost_2152_463_block8 : P1_7_1_3.blockEstimate 2152 463 1487 128 = 54100840960 := by decide +kernel

private theorem cost_2152_463_block9 : P1_7_1_3.blockEstimate 2152 463 1615 128 = 54705213952 := by decide +kernel

private theorem cost_2152_463_block10 : P1_7_1_3.blockEstimate 2152 463 1743 128 = 53363429888 := by decide +kernel

private theorem cost_2152_463_block11 : P1_7_1_3.blockEstimate 2152 463 1871 128 = 50075488768 := by decide +kernel

private theorem cost_2152_463_block12 : P1_7_1_3.blockEstimate 2152 463 1999 128 = 44841390592 := by decide +kernel

private theorem cost_2152_463_block13 : P1_7_1_3.blockEstimate 2152 463 2127 128 = 37784937475 := by decide +kernel

private theorem cost_2152_463_block14 : P1_7_1_3.blockEstimate 2152 463 2255 128 = 29938194429 := by decide +kernel

private theorem cost_2152_463_block15 : P1_7_1_3.blockEstimate 2152 463 2383 128 = 22164731517 := by decide +kernel

private theorem cost_2152_463_block16 : P1_7_1_3.blockEstimate 2152 463 2511 128 = 14967715069 := by decide +kernel

private theorem cost_2152_463_block17 : P1_7_1_3.blockEstimate 2152 463 2639 128 = 8763670048 := by decide +kernel

private theorem cost_2152_463_block18 : P1_7_1_3.blockEstimate 2152 463 2767 128 = 4022001184 := by decide +kernel

private theorem cost_2152_463_block19 : P1_7_1_3.blockEstimate 2152 463 2895 128 = 1049738784 := by decide +kernel

private theorem cost_2152_463_block20 : P1_7_1_3.blockEstimate 2152 463 3023 55 = 31949974 := by decide +kernel

private theorem cost_2152_463_join0_0 : P1_7_1_3.blockEstimate 2152 463 463 256 = 5547071552 :=
  @P1_7_1_3.block_append 2152 463 463 591 128 128 256 735822880 4811248672 5547071552 cost_2152_463_block0 cost_2152_463_block1 rfl rfl rfl

private theorem cost_2152_463_join0_2 : P1_7_1_3.blockEstimate 2152 463 719 256 = 34218937748 :=
  @P1_7_1_3.block_append 2152 463 719 847 128 128 256 12188640288 22030297460 34218937748 cost_2152_463_block2 cost_2152_463_block3 rfl rfl rfl

private theorem cost_2152_463_join0_4 : P1_7_1_3.blockEstimate 2152 463 975 256 = 72832558080 :=
  @P1_7_1_3.block_append 2152 463 975 1103 128 128 256 32221778432 40610779648 72832558080 cost_2152_463_block4 cost_2152_463_block5 rfl rfl rfl

private theorem cost_2152_463_join0_6 : P1_7_1_3.blockEstimate 2152 463 1231 256 = 98603934720 :=
  @P1_7_1_3.block_append 2152 463 1231 1359 128 128 256 47053623808 51550310912 98603934720 cost_2152_463_block6 cost_2152_463_block7 rfl rfl rfl

private theorem cost_2152_463_join0_8 : P1_7_1_3.blockEstimate 2152 463 1487 256 = 108806054912 :=
  @P1_7_1_3.block_append 2152 463 1487 1615 128 128 256 54100840960 54705213952 108806054912 cost_2152_463_block8 cost_2152_463_block9 rfl rfl rfl

private theorem cost_2152_463_join0_10 : P1_7_1_3.blockEstimate 2152 463 1743 256 = 103438918656 :=
  @P1_7_1_3.block_append 2152 463 1743 1871 128 128 256 53363429888 50075488768 103438918656 cost_2152_463_block10 cost_2152_463_block11 rfl rfl rfl

private theorem cost_2152_463_join0_12 : P1_7_1_3.blockEstimate 2152 463 1999 256 = 82626328067 :=
  @P1_7_1_3.block_append 2152 463 1999 2127 128 128 256 44841390592 37784937475 82626328067 cost_2152_463_block12 cost_2152_463_block13 rfl rfl rfl

private theorem cost_2152_463_join0_14 : P1_7_1_3.blockEstimate 2152 463 2255 256 = 52102925946 :=
  @P1_7_1_3.block_append 2152 463 2255 2383 128 128 256 29938194429 22164731517 52102925946 cost_2152_463_block14 cost_2152_463_block15 rfl rfl rfl

private theorem cost_2152_463_join0_16 : P1_7_1_3.blockEstimate 2152 463 2511 256 = 23731385117 :=
  @P1_7_1_3.block_append 2152 463 2511 2639 128 128 256 14967715069 8763670048 23731385117 cost_2152_463_block16 cost_2152_463_block17 rfl rfl rfl

private theorem cost_2152_463_join0_18 : P1_7_1_3.blockEstimate 2152 463 2767 256 = 5071739968 :=
  @P1_7_1_3.block_append 2152 463 2767 2895 128 128 256 4022001184 1049738784 5071739968 cost_2152_463_block18 cost_2152_463_block19 rfl rfl rfl

private theorem cost_2152_463_join1_0 : P1_7_1_3.blockEstimate 2152 463 463 512 = 39766009300 :=
  @P1_7_1_3.block_append 2152 463 463 719 256 256 512 5547071552 34218937748 39766009300 cost_2152_463_join0_0 cost_2152_463_join0_2 rfl rfl rfl

private theorem cost_2152_463_join1_2 : P1_7_1_3.blockEstimate 2152 463 975 512 = 171436492800 :=
  @P1_7_1_3.block_append 2152 463 975 1231 256 256 512 72832558080 98603934720 171436492800 cost_2152_463_join0_4 cost_2152_463_join0_6 rfl rfl rfl

private theorem cost_2152_463_join1_4 : P1_7_1_3.blockEstimate 2152 463 1487 512 = 212244973568 :=
  @P1_7_1_3.block_append 2152 463 1487 1743 256 256 512 108806054912 103438918656 212244973568 cost_2152_463_join0_8 cost_2152_463_join0_10 rfl rfl rfl

private theorem cost_2152_463_join1_6 : P1_7_1_3.blockEstimate 2152 463 1999 512 = 134729254013 :=
  @P1_7_1_3.block_append 2152 463 1999 2255 256 256 512 82626328067 52102925946 134729254013 cost_2152_463_join0_12 cost_2152_463_join0_14 rfl rfl rfl

private theorem cost_2152_463_join1_8 : P1_7_1_3.blockEstimate 2152 463 2511 512 = 28803125085 :=
  @P1_7_1_3.block_append 2152 463 2511 2767 256 256 512 23731385117 5071739968 28803125085 cost_2152_463_join0_16 cost_2152_463_join0_18 rfl rfl rfl

private theorem cost_2152_463_join2_0 : P1_7_1_3.blockEstimate 2152 463 463 1024 = 211202502100 :=
  @P1_7_1_3.block_append 2152 463 463 975 512 512 1024 39766009300 171436492800 211202502100 cost_2152_463_join1_0 cost_2152_463_join1_2 rfl rfl rfl

private theorem cost_2152_463_join2_2 : P1_7_1_3.blockEstimate 2152 463 1487 1024 = 346974227581 :=
  @P1_7_1_3.block_append 2152 463 1487 1999 512 512 1024 212244973568 134729254013 346974227581 cost_2152_463_join1_4 cost_2152_463_join1_6 rfl rfl rfl

private theorem cost_2152_463_join2_4 : P1_7_1_3.blockEstimate 2152 463 2511 567 = 28835075059 :=
  @P1_7_1_3.block_append 2152 463 2511 3023 512 55 567 28803125085 31949974 28835075059 cost_2152_463_join1_8 cost_2152_463_block20 rfl rfl rfl

private theorem cost_2152_463_join3_0 : P1_7_1_3.blockEstimate 2152 463 463 2048 = 558176729681 :=
  @P1_7_1_3.block_append 2152 463 463 1487 1024 1024 2048 211202502100 346974227581 558176729681 cost_2152_463_join2_0 cost_2152_463_join2_2 rfl rfl rfl

private theorem cost_2152_463_join4_0 : P1_7_1_3.blockEstimate 2152 463 463 2615 = 587011804740 :=
  @P1_7_1_3.block_append 2152 463 463 2511 2048 567 2615 558176729681 28835075059 587011804740 cost_2152_463_join3_0 cost_2152_463_join2_4 rfl rfl rfl

private theorem cost_2152_463_total : P1_7_1_3.momentEstimate 2152 463 = 587011804740 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2152 + 463 = 2615 by decide]
  exact cost_2152_463_join4_0

theorem moment2152_463 : P1_7_1.groupedPoleMoment 2152 463 ≤ 587011804740 :=
  (P1_7_1_3.grouped_bound 2152 463).trans_eq cost_2152_463_total
private theorem cost_2186_475_block0 : P1_7_1_3.blockEstimate 2186 475 475 128 = 747986720 := by decide +kernel

private theorem cost_2186_475_block1 : P1_7_1_3.blockEstimate 2186 475 603 128 = 4895272736 := by decide +kernel

private theorem cost_2186_475_block2 : P1_7_1_3.blockEstimate 2186 475 731 128 = 12415827744 := by decide +kernel

private theorem cost_2186_475_block3 : P1_7_1_3.blockEstimate 2186 475 859 128 = 22490141261 := by decide +kernel

private theorem cost_2186_475_block4 : P1_7_1_3.blockEstimate 2186 475 987 128 = 33181038464 := by decide +kernel

private theorem cost_2186_475_block5 : P1_7_1_3.blockEstimate 2186 475 1115 128 = 42098947968 := by decide +kernel

private theorem cost_2186_475_block6 : P1_7_1_3.blockEstimate 2186 475 1243 128 = 49020368768 := by decide +kernel

private theorem cost_2186_475_block7 : P1_7_1_3.blockEstimate 2186 475 1371 128 = 53945300864 := by decide +kernel

private theorem cost_2186_475_block8 : P1_7_1_3.blockEstimate 2186 475 1499 128 = 56873744256 := by decide +kernel

private theorem cost_2186_475_block9 : P1_7_1_3.blockEstimate 2186 475 1627 128 = 57805698944 := by decide +kernel

private theorem cost_2186_475_block10 : P1_7_1_3.blockEstimate 2186 475 1755 128 = 56741164928 := by decide +kernel

private theorem cost_2186_475_block11 : P1_7_1_3.blockEstimate 2186 475 1883 128 = 53680142208 := by decide +kernel

private theorem cost_2186_475_block12 : P1_7_1_3.blockEstimate 2186 475 2011 128 = 48622630784 := by decide +kernel

private theorem cost_2186_475_block13 : P1_7_1_3.blockEstimate 2186 475 2139 128 = 41628436893 := by decide +kernel

private theorem cost_2186_475_block14 : P1_7_1_3.blockEstimate 2186 475 2267 128 = 33580283273 := by decide +kernel

private theorem cost_2186_475_block15 : P1_7_1_3.blockEstimate 2186 475 2395 128 = 25466067426 := by decide +kernel

private theorem cost_2186_475_block16 : P1_7_1_3.blockEstimate 2186 475 2523 128 = 17811060777 := by decide +kernel

private theorem cost_2186_475_block17 : P1_7_1_3.blockEstimate 2186 475 2651 128 = 11046928562 := by decide +kernel

private theorem cost_2186_475_block18 : P1_7_1_3.blockEstimate 2186 475 2779 128 = 5631331888 := by decide +kernel

private theorem cost_2186_475_block19 : P1_7_1_3.blockEstimate 2186 475 2907 128 = 1930019376 := by decide +kernel

private theorem cost_2186_475_block20 : P1_7_1_3.blockEstimate 2186 475 3035 101 = 191952761 := by decide +kernel

private theorem cost_2186_475_join0_0 : P1_7_1_3.blockEstimate 2186 475 475 256 = 5643259456 :=
  @P1_7_1_3.block_append 2186 475 475 603 128 128 256 747986720 4895272736 5643259456 cost_2186_475_block0 cost_2186_475_block1 rfl rfl rfl

private theorem cost_2186_475_join0_2 : P1_7_1_3.blockEstimate 2186 475 731 256 = 34905969005 :=
  @P1_7_1_3.block_append 2186 475 731 859 128 128 256 12415827744 22490141261 34905969005 cost_2186_475_block2 cost_2186_475_block3 rfl rfl rfl

private theorem cost_2186_475_join0_4 : P1_7_1_3.blockEstimate 2186 475 987 256 = 75279986432 :=
  @P1_7_1_3.block_append 2186 475 987 1115 128 128 256 33181038464 42098947968 75279986432 cost_2186_475_block4 cost_2186_475_block5 rfl rfl rfl

private theorem cost_2186_475_join0_6 : P1_7_1_3.blockEstimate 2186 475 1243 256 = 102965669632 :=
  @P1_7_1_3.block_append 2186 475 1243 1371 128 128 256 49020368768 53945300864 102965669632 cost_2186_475_block6 cost_2186_475_block7 rfl rfl rfl

private theorem cost_2186_475_join0_8 : P1_7_1_3.blockEstimate 2186 475 1499 256 = 114679443200 :=
  @P1_7_1_3.block_append 2186 475 1499 1627 128 128 256 56873744256 57805698944 114679443200 cost_2186_475_block8 cost_2186_475_block9 rfl rfl rfl

private theorem cost_2186_475_join0_10 : P1_7_1_3.blockEstimate 2186 475 1755 256 = 110421307136 :=
  @P1_7_1_3.block_append 2186 475 1755 1883 128 128 256 56741164928 53680142208 110421307136 cost_2186_475_block10 cost_2186_475_block11 rfl rfl rfl

private theorem cost_2186_475_join0_12 : P1_7_1_3.blockEstimate 2186 475 2011 256 = 90251067677 :=
  @P1_7_1_3.block_append 2186 475 2011 2139 128 128 256 48622630784 41628436893 90251067677 cost_2186_475_block12 cost_2186_475_block13 rfl rfl rfl

private theorem cost_2186_475_join0_14 : P1_7_1_3.blockEstimate 2186 475 2267 256 = 59046350699 :=
  @P1_7_1_3.block_append 2186 475 2267 2395 128 128 256 33580283273 25466067426 59046350699 cost_2186_475_block14 cost_2186_475_block15 rfl rfl rfl

private theorem cost_2186_475_join0_16 : P1_7_1_3.blockEstimate 2186 475 2523 256 = 28857989339 :=
  @P1_7_1_3.block_append 2186 475 2523 2651 128 128 256 17811060777 11046928562 28857989339 cost_2186_475_block16 cost_2186_475_block17 rfl rfl rfl

private theorem cost_2186_475_join0_18 : P1_7_1_3.blockEstimate 2186 475 2779 256 = 7561351264 :=
  @P1_7_1_3.block_append 2186 475 2779 2907 128 128 256 5631331888 1930019376 7561351264 cost_2186_475_block18 cost_2186_475_block19 rfl rfl rfl

private theorem cost_2186_475_join1_0 : P1_7_1_3.blockEstimate 2186 475 475 512 = 40549228461 :=
  @P1_7_1_3.block_append 2186 475 475 731 256 256 512 5643259456 34905969005 40549228461 cost_2186_475_join0_0 cost_2186_475_join0_2 rfl rfl rfl

private theorem cost_2186_475_join1_2 : P1_7_1_3.blockEstimate 2186 475 987 512 = 178245656064 :=
  @P1_7_1_3.block_append 2186 475 987 1243 256 256 512 75279986432 102965669632 178245656064 cost_2186_475_join0_4 cost_2186_475_join0_6 rfl rfl rfl

private theorem cost_2186_475_join1_4 : P1_7_1_3.blockEstimate 2186 475 1499 512 = 225100750336 :=
  @P1_7_1_3.block_append 2186 475 1499 1755 256 256 512 114679443200 110421307136 225100750336 cost_2186_475_join0_8 cost_2186_475_join0_10 rfl rfl rfl

private theorem cost_2186_475_join1_6 : P1_7_1_3.blockEstimate 2186 475 2011 512 = 149297418376 :=
  @P1_7_1_3.block_append 2186 475 2011 2267 256 256 512 90251067677 59046350699 149297418376 cost_2186_475_join0_12 cost_2186_475_join0_14 rfl rfl rfl

private theorem cost_2186_475_join1_8 : P1_7_1_3.blockEstimate 2186 475 2523 512 = 36419340603 :=
  @P1_7_1_3.block_append 2186 475 2523 2779 256 256 512 28857989339 7561351264 36419340603 cost_2186_475_join0_16 cost_2186_475_join0_18 rfl rfl rfl

private theorem cost_2186_475_join2_0 : P1_7_1_3.blockEstimate 2186 475 475 1024 = 218794884525 :=
  @P1_7_1_3.block_append 2186 475 475 987 512 512 1024 40549228461 178245656064 218794884525 cost_2186_475_join1_0 cost_2186_475_join1_2 rfl rfl rfl

private theorem cost_2186_475_join2_2 : P1_7_1_3.blockEstimate 2186 475 1499 1024 = 374398168712 :=
  @P1_7_1_3.block_append 2186 475 1499 2011 512 512 1024 225100750336 149297418376 374398168712 cost_2186_475_join1_4 cost_2186_475_join1_6 rfl rfl rfl

private theorem cost_2186_475_join2_4 : P1_7_1_3.blockEstimate 2186 475 2523 613 = 36611293364 :=
  @P1_7_1_3.block_append 2186 475 2523 3035 512 101 613 36419340603 191952761 36611293364 cost_2186_475_join1_8 cost_2186_475_block20 rfl rfl rfl

private theorem cost_2186_475_join3_0 : P1_7_1_3.blockEstimate 2186 475 475 2048 = 593193053237 :=
  @P1_7_1_3.block_append 2186 475 475 1499 1024 1024 2048 218794884525 374398168712 593193053237 cost_2186_475_join2_0 cost_2186_475_join2_2 rfl rfl rfl

private theorem cost_2186_475_join4_0 : P1_7_1_3.blockEstimate 2186 475 475 2661 = 629804346601 :=
  @P1_7_1_3.block_append 2186 475 475 2523 2048 613 2661 593193053237 36611293364 629804346601 cost_2186_475_join3_0 cost_2186_475_join2_4 rfl rfl rfl

private theorem cost_2186_475_total : P1_7_1_3.momentEstimate 2186 475 = 629804346601 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2186 + 475 = 2661 by decide]
  exact cost_2186_475_join4_0

theorem moment2186_475 : P1_7_1.groupedPoleMoment 2186 475 ≤ 629804346601 :=
  (P1_7_1_3.grouped_bound 2186 475).trans_eq cost_2186_475_total
private theorem cost_2186_486_block0 : P1_7_1_3.blockEstimate 2186 486 486 128 = 747986720 := by decide +kernel

private theorem cost_2186_486_block1 : P1_7_1_3.blockEstimate 2186 486 614 128 = 4895272736 := by decide +kernel

private theorem cost_2186_486_block2 : P1_7_1_3.blockEstimate 2186 486 742 128 = 12415827744 := by decide +kernel

private theorem cost_2186_486_block3 : P1_7_1_3.blockEstimate 2186 486 870 128 = 22499428451 := by decide +kernel

private theorem cost_2186_486_block4 : P1_7_1_3.blockEstimate 2186 486 998 128 = 33395670464 := by decide +kernel

private theorem cost_2186_486_block5 : P1_7_1_3.blockEstimate 2186 486 1126 128 = 42563550656 := by decide +kernel

private theorem cost_2186_486_block6 : P1_7_1_3.blockEstimate 2186 486 1254 128 = 49688804800 := by decide +kernel

private theorem cost_2186_486_block7 : P1_7_1_3.blockEstimate 2186 486 1382 128 = 54771432896 := by decide +kernel

private theorem cost_2186_486_block8 : P1_7_1_3.blockEstimate 2186 486 1510 128 = 57811434944 := by decide +kernel

private theorem cost_2186_486_block9 : P1_7_1_3.blockEstimate 2186 486 1638 128 = 58808810944 := by decide +kernel

private theorem cost_2186_486_block10 : P1_7_1_3.blockEstimate 2186 486 1766 128 = 57763560896 := by decide +kernel

private theorem cost_2186_486_block11 : P1_7_1_3.blockEstimate 2186 486 1894 128 = 54675684800 := by decide +kernel

private theorem cost_2186_486_block12 : P1_7_1_3.blockEstimate 2186 486 2022 128 = 49545182656 := by decide +kernel

private theorem cost_2186_486_block13 : P1_7_1_3.blockEstimate 2186 486 2150 128 = 42458845805 := by decide +kernel

private theorem cost_2186_486_block14 : P1_7_1_3.blockEstimate 2186 486 2278 128 = 34368521057 := by decide +kernel

private theorem cost_2186_486_block15 : P1_7_1_3.blockEstimate 2186 486 2406 128 = 26195945015 := by decide +kernel

private theorem cost_2186_486_block16 : P1_7_1_3.blockEstimate 2186 486 2534 128 = 18458308882 := by decide +kernel

private theorem cost_2186_486_block17 : P1_7_1_3.blockEstimate 2186 486 2662 128 = 11584186359 := by decide +kernel

private theorem cost_2186_486_block18 : P1_7_1_3.blockEstimate 2186 486 2790 128 = 6032997760 := by decide +kernel

private theorem cost_2186_486_block19 : P1_7_1_3.blockEstimate 2186 486 2918 128 = 2174451072 := by decide +kernel

private theorem cost_2186_486_block20 : P1_7_1_3.blockEstimate 2186 486 3046 112 = 260001168 := by decide +kernel

private theorem cost_2186_486_join0_0 : P1_7_1_3.blockEstimate 2186 486 486 256 = 5643259456 :=
  @P1_7_1_3.block_append 2186 486 486 614 128 128 256 747986720 4895272736 5643259456 cost_2186_486_block0 cost_2186_486_block1 rfl rfl rfl

private theorem cost_2186_486_join0_2 : P1_7_1_3.blockEstimate 2186 486 742 256 = 34915256195 :=
  @P1_7_1_3.block_append 2186 486 742 870 128 128 256 12415827744 22499428451 34915256195 cost_2186_486_block2 cost_2186_486_block3 rfl rfl rfl

private theorem cost_2186_486_join0_4 : P1_7_1_3.blockEstimate 2186 486 998 256 = 75959221120 :=
  @P1_7_1_3.block_append 2186 486 998 1126 128 128 256 33395670464 42563550656 75959221120 cost_2186_486_block4 cost_2186_486_block5 rfl rfl rfl

private theorem cost_2186_486_join0_6 : P1_7_1_3.blockEstimate 2186 486 1254 256 = 104460237696 :=
  @P1_7_1_3.block_append 2186 486 1254 1382 128 128 256 49688804800 54771432896 104460237696 cost_2186_486_block6 cost_2186_486_block7 rfl rfl rfl

private theorem cost_2186_486_join0_8 : P1_7_1_3.blockEstimate 2186 486 1510 256 = 116620245888 :=
  @P1_7_1_3.block_append 2186 486 1510 1638 128 128 256 57811434944 58808810944 116620245888 cost_2186_486_block8 cost_2186_486_block9 rfl rfl rfl

private theorem cost_2186_486_join0_10 : P1_7_1_3.blockEstimate 2186 486 1766 256 = 112439245696 :=
  @P1_7_1_3.block_append 2186 486 1766 1894 128 128 256 57763560896 54675684800 112439245696 cost_2186_486_block10 cost_2186_486_block11 rfl rfl rfl

private theorem cost_2186_486_join0_12 : P1_7_1_3.blockEstimate 2186 486 2022 256 = 92004028461 :=
  @P1_7_1_3.block_append 2186 486 2022 2150 128 128 256 49545182656 42458845805 92004028461 cost_2186_486_block12 cost_2186_486_block13 rfl rfl rfl

private theorem cost_2186_486_join0_14 : P1_7_1_3.blockEstimate 2186 486 2278 256 = 60564466072 :=
  @P1_7_1_3.block_append 2186 486 2278 2406 128 128 256 34368521057 26195945015 60564466072 cost_2186_486_block14 cost_2186_486_block15 rfl rfl rfl

private theorem cost_2186_486_join0_16 : P1_7_1_3.blockEstimate 2186 486 2534 256 = 30042495241 :=
  @P1_7_1_3.block_append 2186 486 2534 2662 128 128 256 18458308882 11584186359 30042495241 cost_2186_486_block16 cost_2186_486_block17 rfl rfl rfl

private theorem cost_2186_486_join0_18 : P1_7_1_3.blockEstimate 2186 486 2790 256 = 8207448832 :=
  @P1_7_1_3.block_append 2186 486 2790 2918 128 128 256 6032997760 2174451072 8207448832 cost_2186_486_block18 cost_2186_486_block19 rfl rfl rfl

private theorem cost_2186_486_join1_0 : P1_7_1_3.blockEstimate 2186 486 486 512 = 40558515651 :=
  @P1_7_1_3.block_append 2186 486 486 742 256 256 512 5643259456 34915256195 40558515651 cost_2186_486_join0_0 cost_2186_486_join0_2 rfl rfl rfl

private theorem cost_2186_486_join1_2 : P1_7_1_3.blockEstimate 2186 486 998 512 = 180419458816 :=
  @P1_7_1_3.block_append 2186 486 998 1254 256 256 512 75959221120 104460237696 180419458816 cost_2186_486_join0_4 cost_2186_486_join0_6 rfl rfl rfl

private theorem cost_2186_486_join1_4 : P1_7_1_3.blockEstimate 2186 486 1510 512 = 229059491584 :=
  @P1_7_1_3.block_append 2186 486 1510 1766 256 256 512 116620245888 112439245696 229059491584 cost_2186_486_join0_8 cost_2186_486_join0_10 rfl rfl rfl

private theorem cost_2186_486_join1_6 : P1_7_1_3.blockEstimate 2186 486 2022 512 = 152568494533 :=
  @P1_7_1_3.block_append 2186 486 2022 2278 256 256 512 92004028461 60564466072 152568494533 cost_2186_486_join0_12 cost_2186_486_join0_14 rfl rfl rfl

private theorem cost_2186_486_join1_8 : P1_7_1_3.blockEstimate 2186 486 2534 512 = 38249944073 :=
  @P1_7_1_3.block_append 2186 486 2534 2790 256 256 512 30042495241 8207448832 38249944073 cost_2186_486_join0_16 cost_2186_486_join0_18 rfl rfl rfl

private theorem cost_2186_486_join2_0 : P1_7_1_3.blockEstimate 2186 486 486 1024 = 220977974467 :=
  @P1_7_1_3.block_append 2186 486 486 998 512 512 1024 40558515651 180419458816 220977974467 cost_2186_486_join1_0 cost_2186_486_join1_2 rfl rfl rfl

private theorem cost_2186_486_join2_2 : P1_7_1_3.blockEstimate 2186 486 1510 1024 = 381627986117 :=
  @P1_7_1_3.block_append 2186 486 1510 2022 512 512 1024 229059491584 152568494533 381627986117 cost_2186_486_join1_4 cost_2186_486_join1_6 rfl rfl rfl

private theorem cost_2186_486_join2_4 : P1_7_1_3.blockEstimate 2186 486 2534 624 = 38509945241 :=
  @P1_7_1_3.block_append 2186 486 2534 3046 512 112 624 38249944073 260001168 38509945241 cost_2186_486_join1_8 cost_2186_486_block20 rfl rfl rfl

private theorem cost_2186_486_join3_0 : P1_7_1_3.blockEstimate 2186 486 486 2048 = 602605960584 :=
  @P1_7_1_3.block_append 2186 486 486 1510 1024 1024 2048 220977974467 381627986117 602605960584 cost_2186_486_join2_0 cost_2186_486_join2_2 rfl rfl rfl

private theorem cost_2186_486_join4_0 : P1_7_1_3.blockEstimate 2186 486 486 2672 = 641115905825 :=
  @P1_7_1_3.block_append 2186 486 486 2534 2048 624 2672 602605960584 38509945241 641115905825 cost_2186_486_join3_0 cost_2186_486_join2_4 rfl rfl rfl

private theorem cost_2186_486_total : P1_7_1_3.momentEstimate 2186 486 = 641115905825 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2186 + 486 = 2672 by decide]
  exact cost_2186_486_join4_0

theorem moment2186_486 : P1_7_1.groupedPoleMoment 2186 486 ≤ 641115905825 :=
  (P1_7_1_3.grouped_bound 2186 486).trans_eq cost_2186_486_total
private theorem cost_2187_475_block0 : P1_7_1_3.blockEstimate 2187 475 475 128 = 748344480 := by decide +kernel

private theorem cost_2187_475_block1 : P1_7_1_3.blockEstimate 2187 475 603 128 = 4897744032 := by decide +kernel

private theorem cost_2187_475_block2 : P1_7_1_3.blockEstimate 2187 475 731 128 = 12422509728 := by decide +kernel

private theorem cost_2187_475_block3 : P1_7_1_3.blockEstimate 2187 475 859 128 = 22503122649 := by decide +kernel

private theorem cost_2187_475_block4 : P1_7_1_3.blockEstimate 2187 475 987 128 = 33201693056 := by decide +kernel

private theorem cost_2187_475_block5 : P1_7_1_3.blockEstimate 2187 475 1115 128 = 42127401344 := by decide +kernel

private theorem cost_2187_475_block6 : P1_7_1_3.blockEstimate 2187 475 1243 128 = 49056620928 := by decide +kernel

private theorem cost_2187_475_block7 : P1_7_1_3.blockEstimate 2187 475 1371 128 = 53989351808 := by decide +kernel

private theorem cost_2187_475_block8 : P1_7_1_3.blockEstimate 2187 475 1499 128 = 56925593984 := by decide +kernel

private theorem cost_2187_475_block9 : P1_7_1_3.blockEstimate 2187 475 1627 128 = 57865347456 := by decide +kernel

private theorem cost_2187_475_block10 : P1_7_1_3.blockEstimate 2187 475 1755 128 = 56808612224 := by decide +kernel

private theorem cost_2187_475_block11 : P1_7_1_3.blockEstimate 2187 475 1883 128 = 53755388288 := by decide +kernel

private theorem cost_2187_475_block12 : P1_7_1_3.blockEstimate 2187 475 2011 128 = 48705675648 := by decide +kernel

private theorem cost_2187_475_block13 : P1_7_1_3.blockEstimate 2187 475 2139 128 = 41717101405 := by decide +kernel

private theorem cost_2187_475_block14 : P1_7_1_3.blockEstimate 2187 475 2267 128 = 33665070333 := by decide +kernel

private theorem cost_2187_475_block15 : P1_7_1_3.blockEstimate 2187 475 2395 128 = 25543134654 := by decide +kernel

private theorem cost_2187_475_block16 : P1_7_1_3.blockEstimate 2187 475 2523 128 = 17877640117 := by decide +kernel

private theorem cost_2187_475_block17 : P1_7_1_3.blockEstimate 2187 475 2651 128 = 11101034440 := by decide +kernel

private theorem cost_2187_475_block18 : P1_7_1_3.blockEstimate 2187 475 2779 128 = 5670164048 := by decide +kernel

private theorem cost_2187_475_block19 : P1_7_1_3.blockEstimate 2187 475 2907 128 = 1952584272 := by decide +kernel

private theorem cost_2187_475_block20 : P1_7_1_3.blockEstimate 2187 475 3035 102 = 197675335 := by decide +kernel

private theorem cost_2187_475_join0_0 : P1_7_1_3.blockEstimate 2187 475 475 256 = 5646088512 :=
  @P1_7_1_3.block_append 2187 475 475 603 128 128 256 748344480 4897744032 5646088512 cost_2187_475_block0 cost_2187_475_block1 rfl rfl rfl

private theorem cost_2187_475_join0_2 : P1_7_1_3.blockEstimate 2187 475 731 256 = 34925632377 :=
  @P1_7_1_3.block_append 2187 475 731 859 128 128 256 12422509728 22503122649 34925632377 cost_2187_475_block2 cost_2187_475_block3 rfl rfl rfl

private theorem cost_2187_475_join0_4 : P1_7_1_3.blockEstimate 2187 475 987 256 = 75329094400 :=
  @P1_7_1_3.block_append 2187 475 987 1115 128 128 256 33201693056 42127401344 75329094400 cost_2187_475_block4 cost_2187_475_block5 rfl rfl rfl

private theorem cost_2187_475_join0_6 : P1_7_1_3.blockEstimate 2187 475 1243 256 = 103045972736 :=
  @P1_7_1_3.block_append 2187 475 1243 1371 128 128 256 49056620928 53989351808 103045972736 cost_2187_475_block6 cost_2187_475_block7 rfl rfl rfl

private theorem cost_2187_475_join0_8 : P1_7_1_3.blockEstimate 2187 475 1499 256 = 114790941440 :=
  @P1_7_1_3.block_append 2187 475 1499 1627 128 128 256 56925593984 57865347456 114790941440 cost_2187_475_block8 cost_2187_475_block9 rfl rfl rfl

private theorem cost_2187_475_join0_10 : P1_7_1_3.blockEstimate 2187 475 1755 256 = 110564000512 :=
  @P1_7_1_3.block_append 2187 475 1755 1883 128 128 256 56808612224 53755388288 110564000512 cost_2187_475_block10 cost_2187_475_block11 rfl rfl rfl

private theorem cost_2187_475_join0_12 : P1_7_1_3.blockEstimate 2187 475 2011 256 = 90422777053 :=
  @P1_7_1_3.block_append 2187 475 2011 2139 128 128 256 48705675648 41717101405 90422777053 cost_2187_475_block12 cost_2187_475_block13 rfl rfl rfl

private theorem cost_2187_475_join0_14 : P1_7_1_3.blockEstimate 2187 475 2267 256 = 59208204987 :=
  @P1_7_1_3.block_append 2187 475 2267 2395 128 128 256 33665070333 25543134654 59208204987 cost_2187_475_block14 cost_2187_475_block15 rfl rfl rfl

private theorem cost_2187_475_join0_16 : P1_7_1_3.blockEstimate 2187 475 2523 256 = 28978674557 :=
  @P1_7_1_3.block_append 2187 475 2523 2651 128 128 256 17877640117 11101034440 28978674557 cost_2187_475_block16 cost_2187_475_block17 rfl rfl rfl

private theorem cost_2187_475_join0_18 : P1_7_1_3.blockEstimate 2187 475 2779 256 = 7622748320 :=
  @P1_7_1_3.block_append 2187 475 2779 2907 128 128 256 5670164048 1952584272 7622748320 cost_2187_475_block18 cost_2187_475_block19 rfl rfl rfl

private theorem cost_2187_475_join1_0 : P1_7_1_3.blockEstimate 2187 475 475 512 = 40571720889 :=
  @P1_7_1_3.block_append 2187 475 475 731 256 256 512 5646088512 34925632377 40571720889 cost_2187_475_join0_0 cost_2187_475_join0_2 rfl rfl rfl

private theorem cost_2187_475_join1_2 : P1_7_1_3.blockEstimate 2187 475 987 512 = 178375067136 :=
  @P1_7_1_3.block_append 2187 475 987 1243 256 256 512 75329094400 103045972736 178375067136 cost_2187_475_join0_4 cost_2187_475_join0_6 rfl rfl rfl

private theorem cost_2187_475_join1_4 : P1_7_1_3.blockEstimate 2187 475 1499 512 = 225354941952 :=
  @P1_7_1_3.block_append 2187 475 1499 1755 256 256 512 114790941440 110564000512 225354941952 cost_2187_475_join0_8 cost_2187_475_join0_10 rfl rfl rfl

private theorem cost_2187_475_join1_6 : P1_7_1_3.blockEstimate 2187 475 2011 512 = 149630982040 :=
  @P1_7_1_3.block_append 2187 475 2011 2267 256 256 512 90422777053 59208204987 149630982040 cost_2187_475_join0_12 cost_2187_475_join0_14 rfl rfl rfl

private theorem cost_2187_475_join1_8 : P1_7_1_3.blockEstimate 2187 475 2523 512 = 36601422877 :=
  @P1_7_1_3.block_append 2187 475 2523 2779 256 256 512 28978674557 7622748320 36601422877 cost_2187_475_join0_16 cost_2187_475_join0_18 rfl rfl rfl

private theorem cost_2187_475_join2_0 : P1_7_1_3.blockEstimate 2187 475 475 1024 = 218946788025 :=
  @P1_7_1_3.block_append 2187 475 475 987 512 512 1024 40571720889 178375067136 218946788025 cost_2187_475_join1_0 cost_2187_475_join1_2 rfl rfl rfl

private theorem cost_2187_475_join2_2 : P1_7_1_3.blockEstimate 2187 475 1499 1024 = 374985923992 :=
  @P1_7_1_3.block_append 2187 475 1499 2011 512 512 1024 225354941952 149630982040 374985923992 cost_2187_475_join1_4 cost_2187_475_join1_6 rfl rfl rfl

private theorem cost_2187_475_join2_4 : P1_7_1_3.blockEstimate 2187 475 2523 614 = 36799098212 :=
  @P1_7_1_3.block_append 2187 475 2523 3035 512 102 614 36601422877 197675335 36799098212 cost_2187_475_join1_8 cost_2187_475_block20 rfl rfl rfl

private theorem cost_2187_475_join3_0 : P1_7_1_3.blockEstimate 2187 475 475 2048 = 593932712017 :=
  @P1_7_1_3.block_append 2187 475 475 1499 1024 1024 2048 218946788025 374985923992 593932712017 cost_2187_475_join2_0 cost_2187_475_join2_2 rfl rfl rfl

private theorem cost_2187_475_join4_0 : P1_7_1_3.blockEstimate 2187 475 475 2662 = 630731810229 :=
  @P1_7_1_3.block_append 2187 475 475 2523 2048 614 2662 593932712017 36799098212 630731810229 cost_2187_475_join3_0 cost_2187_475_join2_4 rfl rfl rfl

private theorem cost_2187_475_total : P1_7_1_3.momentEstimate 2187 475 = 630731810229 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2187 + 475 = 2662 by decide]
  exact cost_2187_475_join4_0

theorem moment2187_475 : P1_7_1.groupedPoleMoment 2187 475 ≤ 630731810229 :=
  (P1_7_1_3.grouped_bound 2187 475).trans_eq cost_2187_475_total
private theorem cost_2187_486_block0 : P1_7_1_3.blockEstimate 2187 486 486 128 = 748344480 := by decide +kernel

private theorem cost_2187_486_block1 : P1_7_1_3.blockEstimate 2187 486 614 128 = 4897744032 := by decide +kernel

private theorem cost_2187_486_block2 : P1_7_1_3.blockEstimate 2187 486 742 128 = 12422509728 := by decide +kernel

private theorem cost_2187_486_block3 : P1_7_1_3.blockEstimate 2187 486 870 128 = 22512415350 := by decide +kernel

private theorem cost_2187_486_block4 : P1_7_1_3.blockEstimate 2187 486 998 128 = 33416459520 := by decide +kernel

private theorem cost_2187_486_block5 : P1_7_1_3.blockEstimate 2187 486 1126 128 = 42592318720 := by decide +kernel

private theorem cost_2187_486_block6 : P1_7_1_3.blockEstimate 2187 486 1254 128 = 49725551872 := by decide +kernel

private theorem cost_2187_486_block7 : P1_7_1_3.blockEstimate 2187 486 1382 128 = 54816158976 := by decide +kernel

private theorem cost_2187_486_block8 : P1_7_1_3.blockEstimate 2187 486 1510 128 = 57864140032 := by decide +kernel

private theorem cost_2187_486_block9 : P1_7_1_3.blockEstimate 2187 486 1638 128 = 58869495040 := by decide +kernel

private theorem cost_2187_486_block10 : P1_7_1_3.blockEstimate 2187 486 1766 128 = 57832224000 := by decide +kernel

private theorem cost_2187_486_block11 : P1_7_1_3.blockEstimate 2187 486 1894 128 = 54752326912 := by decide +kernel

private theorem cost_2187_486_block12 : P1_7_1_3.blockEstimate 2187 486 2022 128 = 49629803776 := by decide +kernel

private theorem cost_2187_486_block13 : P1_7_1_3.blockEstimate 2187 486 2150 128 = 42548654636 := by decide +kernel

private theorem cost_2187_486_block14 : P1_7_1_3.blockEstimate 2187 486 2278 128 = 34454246755 := by decide +kernel

private theorem cost_2187_486_block15 : P1_7_1_3.blockEstimate 2187 486 2406 128 = 26274041884 := by decide +kernel

private theorem cost_2187_486_block16 : P1_7_1_3.blockEstimate 2187 486 2534 128 = 18526024131 := by decide +kernel

private theorem cost_2187_486_block17 : P1_7_1_3.blockEstimate 2187 486 2662 128 = 11639565134 := by decide +kernel

private theorem cost_2187_486_block18 : P1_7_1_3.blockEstimate 2187 486 2790 128 = 6073185040 := by decide +kernel

private theorem cost_2187_486_block19 : P1_7_1_3.blockEstimate 2187 486 2918 128 = 2198449936 := by decide +kernel

private theorem cost_2187_486_block20 : P1_7_1_3.blockEstimate 2187 486 3046 113 = 267001521 := by decide +kernel

private theorem cost_2187_486_join0_0 : P1_7_1_3.blockEstimate 2187 486 486 256 = 5646088512 :=
  @P1_7_1_3.block_append 2187 486 486 614 128 128 256 748344480 4897744032 5646088512 cost_2187_486_block0 cost_2187_486_block1 rfl rfl rfl

private theorem cost_2187_486_join0_2 : P1_7_1_3.blockEstimate 2187 486 742 256 = 34934925078 :=
  @P1_7_1_3.block_append 2187 486 742 870 128 128 256 12422509728 22512415350 34934925078 cost_2187_486_block2 cost_2187_486_block3 rfl rfl rfl

private theorem cost_2187_486_join0_4 : P1_7_1_3.blockEstimate 2187 486 998 256 = 76008778240 :=
  @P1_7_1_3.block_append 2187 486 998 1126 128 128 256 33416459520 42592318720 76008778240 cost_2187_486_block4 cost_2187_486_block5 rfl rfl rfl

private theorem cost_2187_486_join0_6 : P1_7_1_3.blockEstimate 2187 486 1254 256 = 104541710848 :=
  @P1_7_1_3.block_append 2187 486 1254 1382 128 128 256 49725551872 54816158976 104541710848 cost_2187_486_block6 cost_2187_486_block7 rfl rfl rfl

private theorem cost_2187_486_join0_8 : P1_7_1_3.blockEstimate 2187 486 1510 256 = 116733635072 :=
  @P1_7_1_3.block_append 2187 486 1510 1638 128 128 256 57864140032 58869495040 116733635072 cost_2187_486_block8 cost_2187_486_block9 rfl rfl rfl

private theorem cost_2187_486_join0_10 : P1_7_1_3.blockEstimate 2187 486 1766 256 = 112584550912 :=
  @P1_7_1_3.block_append 2187 486 1766 1894 128 128 256 57832224000 54752326912 112584550912 cost_2187_486_block10 cost_2187_486_block11 rfl rfl rfl

private theorem cost_2187_486_join0_12 : P1_7_1_3.blockEstimate 2187 486 2022 256 = 92178458412 :=
  @P1_7_1_3.block_append 2187 486 2022 2150 128 128 256 49629803776 42548654636 92178458412 cost_2187_486_block12 cost_2187_486_block13 rfl rfl rfl

private theorem cost_2187_486_join0_14 : P1_7_1_3.blockEstimate 2187 486 2278 256 = 60728288639 :=
  @P1_7_1_3.block_append 2187 486 2278 2406 128 128 256 34454246755 26274041884 60728288639 cost_2187_486_block14 cost_2187_486_block15 rfl rfl rfl

private theorem cost_2187_486_join0_16 : P1_7_1_3.blockEstimate 2187 486 2534 256 = 30165589265 :=
  @P1_7_1_3.block_append 2187 486 2534 2662 128 128 256 18526024131 11639565134 30165589265 cost_2187_486_block16 cost_2187_486_block17 rfl rfl rfl

private theorem cost_2187_486_join0_18 : P1_7_1_3.blockEstimate 2187 486 2790 256 = 8271634976 :=
  @P1_7_1_3.block_append 2187 486 2790 2918 128 128 256 6073185040 2198449936 8271634976 cost_2187_486_block18 cost_2187_486_block19 rfl rfl rfl

private theorem cost_2187_486_join1_0 : P1_7_1_3.blockEstimate 2187 486 486 512 = 40581013590 :=
  @P1_7_1_3.block_append 2187 486 486 742 256 256 512 5646088512 34934925078 40581013590 cost_2187_486_join0_0 cost_2187_486_join0_2 rfl rfl rfl

private theorem cost_2187_486_join1_2 : P1_7_1_3.blockEstimate 2187 486 998 512 = 180550489088 :=
  @P1_7_1_3.block_append 2187 486 998 1254 256 256 512 76008778240 104541710848 180550489088 cost_2187_486_join0_4 cost_2187_486_join0_6 rfl rfl rfl

private theorem cost_2187_486_join1_4 : P1_7_1_3.blockEstimate 2187 486 1510 512 = 229318185984 :=
  @P1_7_1_3.block_append 2187 486 1510 1766 256 256 512 116733635072 112584550912 229318185984 cost_2187_486_join0_8 cost_2187_486_join0_10 rfl rfl rfl

private theorem cost_2187_486_join1_6 : P1_7_1_3.blockEstimate 2187 486 2022 512 = 152906747051 :=
  @P1_7_1_3.block_append 2187 486 2022 2278 256 256 512 92178458412 60728288639 152906747051 cost_2187_486_join0_12 cost_2187_486_join0_14 rfl rfl rfl

private theorem cost_2187_486_join1_8 : P1_7_1_3.blockEstimate 2187 486 2534 512 = 38437224241 :=
  @P1_7_1_3.block_append 2187 486 2534 2790 256 256 512 30165589265 8271634976 38437224241 cost_2187_486_join0_16 cost_2187_486_join0_18 rfl rfl rfl

private theorem cost_2187_486_join2_0 : P1_7_1_3.blockEstimate 2187 486 486 1024 = 221131502678 :=
  @P1_7_1_3.block_append 2187 486 486 998 512 512 1024 40581013590 180550489088 221131502678 cost_2187_486_join1_0 cost_2187_486_join1_2 rfl rfl rfl

private theorem cost_2187_486_join2_2 : P1_7_1_3.blockEstimate 2187 486 1510 1024 = 382224933035 :=
  @P1_7_1_3.block_append 2187 486 1510 2022 512 512 1024 229318185984 152906747051 382224933035 cost_2187_486_join1_4 cost_2187_486_join1_6 rfl rfl rfl

private theorem cost_2187_486_join2_4 : P1_7_1_3.blockEstimate 2187 486 2534 625 = 38704225762 :=
  @P1_7_1_3.block_append 2187 486 2534 3046 512 113 625 38437224241 267001521 38704225762 cost_2187_486_join1_8 cost_2187_486_block20 rfl rfl rfl

private theorem cost_2187_486_join3_0 : P1_7_1_3.blockEstimate 2187 486 486 2048 = 603356435713 :=
  @P1_7_1_3.block_append 2187 486 486 1510 1024 1024 2048 221131502678 382224933035 603356435713 cost_2187_486_join2_0 cost_2187_486_join2_2 rfl rfl rfl

private theorem cost_2187_486_join4_0 : P1_7_1_3.blockEstimate 2187 486 486 2673 = 642060661475 :=
  @P1_7_1_3.block_append 2187 486 486 2534 2048 625 2673 603356435713 38704225762 642060661475 cost_2187_486_join3_0 cost_2187_486_join2_4 rfl rfl rfl

private theorem cost_2187_486_total : P1_7_1_3.momentEstimate 2187 486 = 642060661475 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2187 + 486 = 2673 by decide]
  exact cost_2187_486_join4_0

theorem moment2187_486 : P1_7_1.groupedPoleMoment 2187 486 ≤ 642060661475 :=
  (P1_7_1_3.grouped_bound 2187 486).trans_eq cost_2187_486_total
private theorem cost_2300_500_block0 : P1_7_1_3.blockEstimate 2300 500 500 128 = 788771360 := by decide +kernel

private theorem cost_2300_500_block1 : P1_7_1_3.blockEstimate 2300 500 628 128 = 5177000480 := by decide +kernel

private theorem cost_2300_500_block2 : P1_7_1_3.blockEstimate 2300 500 756 128 = 13177573920 := by decide +kernel

private theorem cost_2300_500_block3 : P1_7_1_3.blockEstimate 2300 500 884 128 = 23984672943 := by decide +kernel

private theorem cost_2300_500_block4 : P1_7_1_3.blockEstimate 2300 500 1012 128 = 36019671552 := by decide +kernel

private theorem cost_2300_500_block5 : P1_7_1_3.blockEstimate 2300 500 1140 128 = 46444319232 := by decide +kernel

private theorem cost_2300_500_block6 : P1_7_1_3.blockEstimate 2300 500 1268 128 = 54767620608 := by decide +kernel

private theorem cost_2300_500_block7 : P1_7_1_3.blockEstimate 2300 500 1396 128 = 60989575680 := by decide +kernel

private theorem cost_2300_500_block8 : P1_7_1_3.blockEstimate 2300 500 1524 128 = 65110184448 := by decide +kernel

private theorem cost_2300_500_block9 : P1_7_1_3.blockEstimate 2300 500 1652 128 = 67129446912 := by decide +kernel

private theorem cost_2300_500_block10 : P1_7_1_3.blockEstimate 2300 500 1780 128 = 67047363072 := by decide +kernel

private theorem cost_2300_500_block11 : P1_7_1_3.blockEstimate 2300 500 1908 128 = 64863932928 := by decide +kernel

private theorem cost_2300_500_block12 : P1_7_1_3.blockEstimate 2300 500 2036 128 = 60579156480 := by decide +kernel

private theorem cost_2300_500_block13 : P1_7_1_3.blockEstimate 2300 500 2164 128 = 54193033728 := by decide +kernel

private theorem cost_2300_500_block14 : P1_7_1_3.blockEstimate 2300 500 2292 128 = 45914461269 := by decide +kernel

private theorem cost_2300_500_block15 : P1_7_1_3.blockEstimate 2300 500 2420 128 = 36915249258 := by decide +kernel

private theorem cost_2300_500_block16 : P1_7_1_3.blockEstimate 2300 500 2548 128 = 27987989642 := by decide +kernel

private theorem cost_2300_500_block17 : P1_7_1_3.blockEstimate 2300 500 2676 128 = 19636767776 := by decide +kernel

private theorem cost_2300_500_block18 : P1_7_1_3.blockEstimate 2300 500 2804 128 = 12275054912 := by decide +kernel

private theorem cost_2300_500_block19 : P1_7_1_3.blockEstimate 2300 500 2932 128 = 6378445120 := by decide +kernel

private theorem cost_2300_500_block20 : P1_7_1_3.blockEstimate 2300 500 3060 128 = 2294364480 := by decide +kernel

private theorem cost_2300_500_block21 : P1_7_1_3.blockEstimate 2300 500 3188 112 = 273889560 := by decide +kernel

private theorem cost_2300_500_join0_0 : P1_7_1_3.blockEstimate 2300 500 500 256 = 5965771840 :=
  @P1_7_1_3.block_append 2300 500 500 628 128 128 256 788771360 5177000480 5965771840 cost_2300_500_block0 cost_2300_500_block1 rfl rfl rfl

private theorem cost_2300_500_join0_2 : P1_7_1_3.blockEstimate 2300 500 756 256 = 37162246863 :=
  @P1_7_1_3.block_append 2300 500 756 884 128 128 256 13177573920 23984672943 37162246863 cost_2300_500_block2 cost_2300_500_block3 rfl rfl rfl

private theorem cost_2300_500_join0_4 : P1_7_1_3.blockEstimate 2300 500 1012 256 = 82463990784 :=
  @P1_7_1_3.block_append 2300 500 1012 1140 128 128 256 36019671552 46444319232 82463990784 cost_2300_500_block4 cost_2300_500_block5 rfl rfl rfl

private theorem cost_2300_500_join0_6 : P1_7_1_3.blockEstimate 2300 500 1268 256 = 115757196288 :=
  @P1_7_1_3.block_append 2300 500 1268 1396 128 128 256 54767620608 60989575680 115757196288 cost_2300_500_block6 cost_2300_500_block7 rfl rfl rfl

private theorem cost_2300_500_join0_8 : P1_7_1_3.blockEstimate 2300 500 1524 256 = 132239631360 :=
  @P1_7_1_3.block_append 2300 500 1524 1652 128 128 256 65110184448 67129446912 132239631360 cost_2300_500_block8 cost_2300_500_block9 rfl rfl rfl

private theorem cost_2300_500_join0_10 : P1_7_1_3.blockEstimate 2300 500 1780 256 = 131911296000 :=
  @P1_7_1_3.block_append 2300 500 1780 1908 128 128 256 67047363072 64863932928 131911296000 cost_2300_500_block10 cost_2300_500_block11 rfl rfl rfl

private theorem cost_2300_500_join0_12 : P1_7_1_3.blockEstimate 2300 500 2036 256 = 114772190208 :=
  @P1_7_1_3.block_append 2300 500 2036 2164 128 128 256 60579156480 54193033728 114772190208 cost_2300_500_block12 cost_2300_500_block13 rfl rfl rfl

private theorem cost_2300_500_join0_14 : P1_7_1_3.blockEstimate 2300 500 2292 256 = 82829710527 :=
  @P1_7_1_3.block_append 2300 500 2292 2420 128 128 256 45914461269 36915249258 82829710527 cost_2300_500_block14 cost_2300_500_block15 rfl rfl rfl

private theorem cost_2300_500_join0_16 : P1_7_1_3.blockEstimate 2300 500 2548 256 = 47624757418 :=
  @P1_7_1_3.block_append 2300 500 2548 2676 128 128 256 27987989642 19636767776 47624757418 cost_2300_500_block16 cost_2300_500_block17 rfl rfl rfl

private theorem cost_2300_500_join0_18 : P1_7_1_3.blockEstimate 2300 500 2804 256 = 18653500032 :=
  @P1_7_1_3.block_append 2300 500 2804 2932 128 128 256 12275054912 6378445120 18653500032 cost_2300_500_block18 cost_2300_500_block19 rfl rfl rfl

private theorem cost_2300_500_join0_20 : P1_7_1_3.blockEstimate 2300 500 3060 240 = 2568254040 :=
  @P1_7_1_3.block_append 2300 500 3060 3188 128 112 240 2294364480 273889560 2568254040 cost_2300_500_block20 cost_2300_500_block21 rfl rfl rfl

private theorem cost_2300_500_join1_0 : P1_7_1_3.blockEstimate 2300 500 500 512 = 43128018703 :=
  @P1_7_1_3.block_append 2300 500 500 756 256 256 512 5965771840 37162246863 43128018703 cost_2300_500_join0_0 cost_2300_500_join0_2 rfl rfl rfl

private theorem cost_2300_500_join1_2 : P1_7_1_3.blockEstimate 2300 500 1012 512 = 198221187072 :=
  @P1_7_1_3.block_append 2300 500 1012 1268 256 256 512 82463990784 115757196288 198221187072 cost_2300_500_join0_4 cost_2300_500_join0_6 rfl rfl rfl

private theorem cost_2300_500_join1_4 : P1_7_1_3.blockEstimate 2300 500 1524 512 = 264150927360 :=
  @P1_7_1_3.block_append 2300 500 1524 1780 256 256 512 132239631360 131911296000 264150927360 cost_2300_500_join0_8 cost_2300_500_join0_10 rfl rfl rfl

private theorem cost_2300_500_join1_6 : P1_7_1_3.blockEstimate 2300 500 2036 512 = 197601900735 :=
  @P1_7_1_3.block_append 2300 500 2036 2292 256 256 512 114772190208 82829710527 197601900735 cost_2300_500_join0_12 cost_2300_500_join0_14 rfl rfl rfl

private theorem cost_2300_500_join1_8 : P1_7_1_3.blockEstimate 2300 500 2548 512 = 66278257450 :=
  @P1_7_1_3.block_append 2300 500 2548 2804 256 256 512 47624757418 18653500032 66278257450 cost_2300_500_join0_16 cost_2300_500_join0_18 rfl rfl rfl

private theorem cost_2300_500_join2_0 : P1_7_1_3.blockEstimate 2300 500 500 1024 = 241349205775 :=
  @P1_7_1_3.block_append 2300 500 500 1012 512 512 1024 43128018703 198221187072 241349205775 cost_2300_500_join1_0 cost_2300_500_join1_2 rfl rfl rfl

private theorem cost_2300_500_join2_2 : P1_7_1_3.blockEstimate 2300 500 1524 1024 = 461752828095 :=
  @P1_7_1_3.block_append 2300 500 1524 2036 512 512 1024 264150927360 197601900735 461752828095 cost_2300_500_join1_4 cost_2300_500_join1_6 rfl rfl rfl

private theorem cost_2300_500_join2_4 : P1_7_1_3.blockEstimate 2300 500 2548 752 = 68846511490 :=
  @P1_7_1_3.block_append 2300 500 2548 3060 512 240 752 66278257450 2568254040 68846511490 cost_2300_500_join1_8 cost_2300_500_join0_20 rfl rfl rfl

private theorem cost_2300_500_join3_0 : P1_7_1_3.blockEstimate 2300 500 500 2048 = 703102033870 :=
  @P1_7_1_3.block_append 2300 500 500 1524 1024 1024 2048 241349205775 461752828095 703102033870 cost_2300_500_join2_0 cost_2300_500_join2_2 rfl rfl rfl

private theorem cost_2300_500_join4_0 : P1_7_1_3.blockEstimate 2300 500 500 2800 = 771948545360 :=
  @P1_7_1_3.block_append 2300 500 500 2548 2048 752 2800 703102033870 68846511490 771948545360 cost_2300_500_join3_0 cost_2300_500_join2_4 rfl rfl rfl

private theorem cost_2300_500_total : P1_7_1_3.momentEstimate 2300 500 = 771948545360 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2300 + 500 = 2800 by decide]
  exact cost_2300_500_join4_0

theorem moment2300_500 : P1_7_1.groupedPoleMoment 2300 500 ≤ 771948545360 :=
  (P1_7_1_3.grouped_bound 2300 500).trans_eq cost_2300_500_total
private theorem cost_2300_510_block0 : P1_7_1_3.blockEstimate 2300 510 510 128 = 788771360 := by decide +kernel

private theorem cost_2300_510_block1 : P1_7_1_3.blockEstimate 2300 510 638 128 = 5177000480 := by decide +kernel

private theorem cost_2300_510_block2 : P1_7_1_3.blockEstimate 2300 510 766 128 = 13177573920 := by decide +kernel

private theorem cost_2300_510_block3 : P1_7_1_3.blockEstimate 2300 510 894 128 = 23985183523 := by decide +kernel

private theorem cost_2300_510_block4 : P1_7_1_3.blockEstimate 2300 510 1022 128 = 36174646592 := by decide +kernel

private theorem cost_2300_510_block5 : P1_7_1_3.blockEstimate 2300 510 1150 128 = 46849232192 := by decide +kernel

private theorem cost_2300_510_block6 : P1_7_1_3.blockEstimate 2300 510 1278 128 = 55380528448 := by decide +kernel

private theorem cost_2300_510_block7 : P1_7_1_3.blockEstimate 2300 510 1406 128 = 61768535360 := by decide +kernel

private theorem cost_2300_510_block8 : P1_7_1_3.blockEstimate 2300 510 1534 128 = 66013252928 := by decide +kernel

private theorem cost_2300_510_block9 : P1_7_1_3.blockEstimate 2300 510 1662 128 = 68114681152 := by decide +kernel

private theorem cost_2300_510_block10 : P1_7_1_3.blockEstimate 2300 510 1790 128 = 68072820032 := by decide +kernel

private theorem cost_2300_510_block11 : P1_7_1_3.blockEstimate 2300 510 1918 128 = 65887669568 := by decide +kernel

private theorem cost_2300_510_block12 : P1_7_1_3.blockEstimate 2300 510 2046 128 = 61559229760 := by decide +kernel

private theorem cost_2300_510_block13 : P1_7_1_3.blockEstimate 2300 510 2174 128 = 55087501890 := by decide +kernel

private theorem cost_2300_510_block14 : P1_7_1_3.blockEstimate 2300 510 2302 128 = 46736144916 := by decide +kernel

private theorem cost_2300_510_block15 : P1_7_1_3.blockEstimate 2300 510 2430 128 = 37696731111 := by decide +kernel

private theorem cost_2300_510_block16 : P1_7_1_3.blockEstimate 2300 510 2558 128 = 28708923127 := by decide +kernel

private theorem cost_2300_510_block17 : P1_7_1_3.blockEstimate 2300 510 2686 128 = 20274774168 := by decide +kernel

private theorem cost_2300_510_block18 : P1_7_1_3.blockEstimate 2300 510 2814 128 = 12804719280 := by decide +kernel

private theorem cost_2300_510_block19 : P1_7_1_3.blockEstimate 2300 510 2942 128 = 6777104048 := by decide +kernel

private theorem cost_2300_510_block20 : P1_7_1_3.blockEstimate 2300 510 3070 128 = 2542357168 := by decide +kernel

private theorem cost_2300_510_block21 : P1_7_1_3.blockEstimate 2300 510 3198 122 = 352120754 := by decide +kernel

private theorem cost_2300_510_join0_0 : P1_7_1_3.blockEstimate 2300 510 510 256 = 5965771840 :=
  @P1_7_1_3.block_append 2300 510 510 638 128 128 256 788771360 5177000480 5965771840 cost_2300_510_block0 cost_2300_510_block1 rfl rfl rfl

private theorem cost_2300_510_join0_2 : P1_7_1_3.blockEstimate 2300 510 766 256 = 37162757443 :=
  @P1_7_1_3.block_append 2300 510 766 894 128 128 256 13177573920 23985183523 37162757443 cost_2300_510_block2 cost_2300_510_block3 rfl rfl rfl

private theorem cost_2300_510_join0_4 : P1_7_1_3.blockEstimate 2300 510 1022 256 = 83023878784 :=
  @P1_7_1_3.block_append 2300 510 1022 1150 128 128 256 36174646592 46849232192 83023878784 cost_2300_510_block4 cost_2300_510_block5 rfl rfl rfl

private theorem cost_2300_510_join0_6 : P1_7_1_3.blockEstimate 2300 510 1278 256 = 117149063808 :=
  @P1_7_1_3.block_append 2300 510 1278 1406 128 128 256 55380528448 61768535360 117149063808 cost_2300_510_block6 cost_2300_510_block7 rfl rfl rfl

private theorem cost_2300_510_join0_8 : P1_7_1_3.blockEstimate 2300 510 1534 256 = 134127934080 :=
  @P1_7_1_3.block_append 2300 510 1534 1662 128 128 256 66013252928 68114681152 134127934080 cost_2300_510_block8 cost_2300_510_block9 rfl rfl rfl

private theorem cost_2300_510_join0_10 : P1_7_1_3.blockEstimate 2300 510 1790 256 = 133960489600 :=
  @P1_7_1_3.block_append 2300 510 1790 1918 128 128 256 68072820032 65887669568 133960489600 cost_2300_510_block10 cost_2300_510_block11 rfl rfl rfl

private theorem cost_2300_510_join0_12 : P1_7_1_3.blockEstimate 2300 510 2046 256 = 116646731650 :=
  @P1_7_1_3.block_append 2300 510 2046 2174 128 128 256 61559229760 55087501890 116646731650 cost_2300_510_block12 cost_2300_510_block13 rfl rfl rfl

private theorem cost_2300_510_join0_14 : P1_7_1_3.blockEstimate 2300 510 2302 256 = 84432876027 :=
  @P1_7_1_3.block_append 2300 510 2302 2430 128 128 256 46736144916 37696731111 84432876027 cost_2300_510_block14 cost_2300_510_block15 rfl rfl rfl

private theorem cost_2300_510_join0_16 : P1_7_1_3.blockEstimate 2300 510 2558 256 = 48983697295 :=
  @P1_7_1_3.block_append 2300 510 2558 2686 128 128 256 28708923127 20274774168 48983697295 cost_2300_510_block16 cost_2300_510_block17 rfl rfl rfl

private theorem cost_2300_510_join0_18 : P1_7_1_3.blockEstimate 2300 510 2814 256 = 19581823328 :=
  @P1_7_1_3.block_append 2300 510 2814 2942 128 128 256 12804719280 6777104048 19581823328 cost_2300_510_block18 cost_2300_510_block19 rfl rfl rfl

private theorem cost_2300_510_join0_20 : P1_7_1_3.blockEstimate 2300 510 3070 250 = 2894477922 :=
  @P1_7_1_3.block_append 2300 510 3070 3198 128 122 250 2542357168 352120754 2894477922 cost_2300_510_block20 cost_2300_510_block21 rfl rfl rfl

private theorem cost_2300_510_join1_0 : P1_7_1_3.blockEstimate 2300 510 510 512 = 43128529283 :=
  @P1_7_1_3.block_append 2300 510 510 766 256 256 512 5965771840 37162757443 43128529283 cost_2300_510_join0_0 cost_2300_510_join0_2 rfl rfl rfl

private theorem cost_2300_510_join1_2 : P1_7_1_3.blockEstimate 2300 510 1022 512 = 200172942592 :=
  @P1_7_1_3.block_append 2300 510 1022 1278 256 256 512 83023878784 117149063808 200172942592 cost_2300_510_join0_4 cost_2300_510_join0_6 rfl rfl rfl

private theorem cost_2300_510_join1_4 : P1_7_1_3.blockEstimate 2300 510 1534 512 = 268088423680 :=
  @P1_7_1_3.block_append 2300 510 1534 1790 256 256 512 134127934080 133960489600 268088423680 cost_2300_510_join0_8 cost_2300_510_join0_10 rfl rfl rfl

private theorem cost_2300_510_join1_6 : P1_7_1_3.blockEstimate 2300 510 2046 512 = 201079607677 :=
  @P1_7_1_3.block_append 2300 510 2046 2302 256 256 512 116646731650 84432876027 201079607677 cost_2300_510_join0_12 cost_2300_510_join0_14 rfl rfl rfl

private theorem cost_2300_510_join1_8 : P1_7_1_3.blockEstimate 2300 510 2558 512 = 68565520623 :=
  @P1_7_1_3.block_append 2300 510 2558 2814 256 256 512 48983697295 19581823328 68565520623 cost_2300_510_join0_16 cost_2300_510_join0_18 rfl rfl rfl

private theorem cost_2300_510_join2_0 : P1_7_1_3.blockEstimate 2300 510 510 1024 = 243301471875 :=
  @P1_7_1_3.block_append 2300 510 510 1022 512 512 1024 43128529283 200172942592 243301471875 cost_2300_510_join1_0 cost_2300_510_join1_2 rfl rfl rfl

private theorem cost_2300_510_join2_2 : P1_7_1_3.blockEstimate 2300 510 1534 1024 = 469168031357 :=
  @P1_7_1_3.block_append 2300 510 1534 2046 512 512 1024 268088423680 201079607677 469168031357 cost_2300_510_join1_4 cost_2300_510_join1_6 rfl rfl rfl

private theorem cost_2300_510_join2_4 : P1_7_1_3.blockEstimate 2300 510 2558 762 = 71459998545 :=
  @P1_7_1_3.block_append 2300 510 2558 3070 512 250 762 68565520623 2894477922 71459998545 cost_2300_510_join1_8 cost_2300_510_join0_20 rfl rfl rfl

private theorem cost_2300_510_join3_0 : P1_7_1_3.blockEstimate 2300 510 510 2048 = 712469503232 :=
  @P1_7_1_3.block_append 2300 510 510 1534 1024 1024 2048 243301471875 469168031357 712469503232 cost_2300_510_join2_0 cost_2300_510_join2_2 rfl rfl rfl

private theorem cost_2300_510_join4_0 : P1_7_1_3.blockEstimate 2300 510 510 2810 = 783929501777 :=
  @P1_7_1_3.block_append 2300 510 510 2558 2048 762 2810 712469503232 71459998545 783929501777 cost_2300_510_join3_0 cost_2300_510_join2_4 rfl rfl rfl

private theorem cost_2300_510_total : P1_7_1_3.momentEstimate 2300 510 = 783929501777 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2300 + 510 = 2810 by decide]
  exact cost_2300_510_join4_0

theorem moment2300_510 : P1_7_1.groupedPoleMoment 2300 510 ≤ 783929501777 :=
  (P1_7_1_3.grouped_bound 2300 510).trans_eq cost_2300_510_total
private theorem cost_2300_512_block0 : P1_7_1_3.blockEstimate 2300 512 512 128 = 788771360 := by decide +kernel

private theorem cost_2300_512_block1 : P1_7_1_3.blockEstimate 2300 512 640 128 = 5177000480 := by decide +kernel

private theorem cost_2300_512_block2 : P1_7_1_3.blockEstimate 2300 512 768 128 = 13177573920 := by decide +kernel

private theorem cost_2300_512_block3 : P1_7_1_3.blockEstimate 2300 512 896 128 = 23985185312 := by decide +kernel

private theorem cost_2300_512_block4 : P1_7_1_3.blockEstimate 2300 512 1024 128 = 36202992768 := by decide +kernel

private theorem cost_2300_512_block5 : P1_7_1_3.blockEstimate 2300 512 1152 128 = 46927762560 := by decide +kernel

private theorem cost_2300_512_block6 : P1_7_1_3.blockEstimate 2300 512 1280 128 = 55500854400 := by decide +kernel

private theorem cost_2300_512_block7 : P1_7_1_3.blockEstimate 2300 512 1408 128 = 61922268288 := by decide +kernel

private theorem cost_2300_512_block8 : P1_7_1_3.blockEstimate 2300 512 1536 128 = 66192004224 := by decide +kernel

private theorem cost_2300_512_block9 : P1_7_1_3.blockEstimate 2300 512 1664 128 = 68310062208 := by decide +kernel

private theorem cost_2300_512_block10 : P1_7_1_3.blockEstimate 2300 512 1792 128 = 68276442240 := by decide +kernel

private theorem cost_2300_512_block11 : P1_7_1_3.blockEstimate 2300 512 1920 128 = 66091144320 := by decide +kernel

private theorem cost_2300_512_block12 : P1_7_1_3.blockEstimate 2300 512 2048 128 = 61754168448 := by decide +kernel

private theorem cost_2300_512_block13 : P1_7_1_3.blockEstimate 2300 512 2176 128 = 55265523585 := by decide +kernel

private theorem cost_2300_512_block14 : P1_7_1_3.blockEstimate 2300 512 2304 128 = 46900795916 := by decide +kernel

private theorem cost_2300_512_block15 : P1_7_1_3.blockEstimate 2300 512 2432 128 = 37853568982 := by decide +kernel

private theorem cost_2300_512_block16 : P1_7_1_3.blockEstimate 2300 512 2560 128 = 28853854740 := by decide +kernel

private theorem cost_2300_512_block17 : P1_7_1_3.blockEstimate 2300 512 2688 128 = 20403318034 := by decide +kernel

private theorem cost_2300_512_block18 : P1_7_1_3.blockEstimate 2300 512 2816 128 = 12911784800 := by decide +kernel

private theorem cost_2300_512_block19 : P1_7_1_3.blockEstimate 2300 512 2944 128 = 6858152800 := by decide +kernel

private theorem cost_2300_512_block20 : P1_7_1_3.blockEstimate 2300 512 3072 128 = 2593456992 := by decide +kernel

private theorem cost_2300_512_block21 : P1_7_1_3.blockEstimate 2300 512 3200 124 = 369353313 := by decide +kernel

private theorem cost_2300_512_join0_0 : P1_7_1_3.blockEstimate 2300 512 512 256 = 5965771840 :=
  @P1_7_1_3.block_append 2300 512 512 640 128 128 256 788771360 5177000480 5965771840 cost_2300_512_block0 cost_2300_512_block1 rfl rfl rfl

private theorem cost_2300_512_join0_2 : P1_7_1_3.blockEstimate 2300 512 768 256 = 37162759232 :=
  @P1_7_1_3.block_append 2300 512 768 896 128 128 256 13177573920 23985185312 37162759232 cost_2300_512_block2 cost_2300_512_block3 rfl rfl rfl

private theorem cost_2300_512_join0_4 : P1_7_1_3.blockEstimate 2300 512 1024 256 = 83130755328 :=
  @P1_7_1_3.block_append 2300 512 1024 1152 128 128 256 36202992768 46927762560 83130755328 cost_2300_512_block4 cost_2300_512_block5 rfl rfl rfl

private theorem cost_2300_512_join0_6 : P1_7_1_3.blockEstimate 2300 512 1280 256 = 117423122688 :=
  @P1_7_1_3.block_append 2300 512 1280 1408 128 128 256 55500854400 61922268288 117423122688 cost_2300_512_block6 cost_2300_512_block7 rfl rfl rfl

private theorem cost_2300_512_join0_8 : P1_7_1_3.blockEstimate 2300 512 1536 256 = 134502066432 :=
  @P1_7_1_3.block_append 2300 512 1536 1664 128 128 256 66192004224 68310062208 134502066432 cost_2300_512_block8 cost_2300_512_block9 rfl rfl rfl

private theorem cost_2300_512_join0_10 : P1_7_1_3.blockEstimate 2300 512 1792 256 = 134367586560 :=
  @P1_7_1_3.block_append 2300 512 1792 1920 128 128 256 68276442240 66091144320 134367586560 cost_2300_512_block10 cost_2300_512_block11 rfl rfl rfl

private theorem cost_2300_512_join0_12 : P1_7_1_3.blockEstimate 2300 512 2048 256 = 117019692033 :=
  @P1_7_1_3.block_append 2300 512 2048 2176 128 128 256 61754168448 55265523585 117019692033 cost_2300_512_block12 cost_2300_512_block13 rfl rfl rfl

private theorem cost_2300_512_join0_14 : P1_7_1_3.blockEstimate 2300 512 2304 256 = 84754364898 :=
  @P1_7_1_3.block_append 2300 512 2304 2432 128 128 256 46900795916 37853568982 84754364898 cost_2300_512_block14 cost_2300_512_block15 rfl rfl rfl

private theorem cost_2300_512_join0_16 : P1_7_1_3.blockEstimate 2300 512 2560 256 = 49257172774 :=
  @P1_7_1_3.block_append 2300 512 2560 2688 128 128 256 28853854740 20403318034 49257172774 cost_2300_512_block16 cost_2300_512_block17 rfl rfl rfl

private theorem cost_2300_512_join0_18 : P1_7_1_3.blockEstimate 2300 512 2816 256 = 19769937600 :=
  @P1_7_1_3.block_append 2300 512 2816 2944 128 128 256 12911784800 6858152800 19769937600 cost_2300_512_block18 cost_2300_512_block19 rfl rfl rfl

private theorem cost_2300_512_join0_20 : P1_7_1_3.blockEstimate 2300 512 3072 252 = 2962810305 :=
  @P1_7_1_3.block_append 2300 512 3072 3200 128 124 252 2593456992 369353313 2962810305 cost_2300_512_block20 cost_2300_512_block21 rfl rfl rfl

private theorem cost_2300_512_join1_0 : P1_7_1_3.blockEstimate 2300 512 512 512 = 43128531072 :=
  @P1_7_1_3.block_append 2300 512 512 768 256 256 512 5965771840 37162759232 43128531072 cost_2300_512_join0_0 cost_2300_512_join0_2 rfl rfl rfl

private theorem cost_2300_512_join1_2 : P1_7_1_3.blockEstimate 2300 512 1024 512 = 200553878016 :=
  @P1_7_1_3.block_append 2300 512 1024 1280 256 256 512 83130755328 117423122688 200553878016 cost_2300_512_join0_4 cost_2300_512_join0_6 rfl rfl rfl

private theorem cost_2300_512_join1_4 : P1_7_1_3.blockEstimate 2300 512 1536 512 = 268869652992 :=
  @P1_7_1_3.block_append 2300 512 1536 1792 256 256 512 134502066432 134367586560 268869652992 cost_2300_512_join0_8 cost_2300_512_join0_10 rfl rfl rfl

private theorem cost_2300_512_join1_6 : P1_7_1_3.blockEstimate 2300 512 2048 512 = 201774056931 :=
  @P1_7_1_3.block_append 2300 512 2048 2304 256 256 512 117019692033 84754364898 201774056931 cost_2300_512_join0_12 cost_2300_512_join0_14 rfl rfl rfl

private theorem cost_2300_512_join1_8 : P1_7_1_3.blockEstimate 2300 512 2560 512 = 69027110374 :=
  @P1_7_1_3.block_append 2300 512 2560 2816 256 256 512 49257172774 19769937600 69027110374 cost_2300_512_join0_16 cost_2300_512_join0_18 rfl rfl rfl

private theorem cost_2300_512_join2_0 : P1_7_1_3.blockEstimate 2300 512 512 1024 = 243682409088 :=
  @P1_7_1_3.block_append 2300 512 512 1024 512 512 1024 43128531072 200553878016 243682409088 cost_2300_512_join1_0 cost_2300_512_join1_2 rfl rfl rfl

private theorem cost_2300_512_join2_2 : P1_7_1_3.blockEstimate 2300 512 1536 1024 = 470643709923 :=
  @P1_7_1_3.block_append 2300 512 1536 2048 512 512 1024 268869652992 201774056931 470643709923 cost_2300_512_join1_4 cost_2300_512_join1_6 rfl rfl rfl

private theorem cost_2300_512_join2_4 : P1_7_1_3.blockEstimate 2300 512 2560 764 = 71989920679 :=
  @P1_7_1_3.block_append 2300 512 2560 3072 512 252 764 69027110374 2962810305 71989920679 cost_2300_512_join1_8 cost_2300_512_join0_20 rfl rfl rfl

private theorem cost_2300_512_join3_0 : P1_7_1_3.blockEstimate 2300 512 512 2048 = 714326119011 :=
  @P1_7_1_3.block_append 2300 512 512 1536 1024 1024 2048 243682409088 470643709923 714326119011 cost_2300_512_join2_0 cost_2300_512_join2_2 rfl rfl rfl

private theorem cost_2300_512_join4_0 : P1_7_1_3.blockEstimate 2300 512 512 2812 = 786316039690 :=
  @P1_7_1_3.block_append 2300 512 512 2560 2048 764 2812 714326119011 71989920679 786316039690 cost_2300_512_join3_0 cost_2300_512_join2_4 rfl rfl rfl

private theorem cost_2300_512_total : P1_7_1_3.momentEstimate 2300 512 = 786316039690 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2300 + 512 = 2812 by decide]
  exact cost_2300_512_join4_0

theorem moment2300_512 : P1_7_1.groupedPoleMoment 2300 512 ≤ 786316039690 :=
  (P1_7_1_3.grouped_bound 2300 512).trans_eq cost_2300_512_total

end Research6966.HelperRescueCatalogue

end Merged6967_Near6967RescueMoment17

section Merged6967_Near6967RescueMoment18
set_option Elab.async false


set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem cost_2301_498_block0 : P1_7_1_3.blockEstimate 2301 498 498 128 = 789129120 := by decide +kernel

private theorem cost_2301_498_block1 : P1_7_1_3.blockEstimate 2301 498 626 128 = 5179471776 := by decide +kernel

private theorem cost_2301_498_block2 : P1_7_1_3.blockEstimate 2301 498 754 128 = 13184255904 := by decide +kernel

private theorem cost_2301_498_block3 : P1_7_1_3.blockEstimate 2301 498 882 128 = 23997359321 := by decide +kernel

private theorem cost_2301_498_block4 : P1_7_1_3.blockEstimate 2301 498 1010 128 = 36006945792 := by decide +kernel

private theorem cost_2301_498_block5 : P1_7_1_3.blockEstimate 2301 498 1138 128 = 46389978112 := by decide +kernel

private theorem cost_2301_498_block6 : P1_7_1_3.blockEstimate 2301 498 1266 128 = 54680052736 := by decide +kernel

private theorem cost_2301_498_block7 : P1_7_1_3.blockEstimate 2301 498 1394 128 = 60877169664 := by decide +kernel

private theorem cost_2301_498_block8 : P1_7_1_3.blockEstimate 2301 498 1522 128 = 64981328896 := by decide +kernel

private theorem cost_2301_498_block9 : P1_7_1_3.blockEstimate 2301 498 1650 128 = 66992530432 := by decide +kernel

private theorem cost_2301_498_block10 : P1_7_1_3.blockEstimate 2301 498 1778 128 = 66910774272 := by decide +kernel

private theorem cost_2301_498_block11 : P1_7_1_3.blockEstimate 2301 498 1906 128 = 64736060416 := by decide +kernel

private theorem cost_2301_498_block12 : P1_7_1_3.blockEstimate 2301 498 2034 128 = 60468388864 := by decide +kernel

private theorem cost_2301_498_block13 : P1_7_1_3.blockEstimate 2301 498 2162 128 = 54107759616 := by decide +kernel

private theorem cost_2301_498_block14 : P1_7_1_3.blockEstimate 2301 498 2290 128 = 45848083600 := by decide +kernel

private theorem cost_2301_498_block15 : P1_7_1_3.blockEstimate 2301 498 2418 128 = 36851516191 := by decide +kernel

private theorem cost_2301_498_block16 : P1_7_1_3.blockEstimate 2301 498 2546 128 = 27927788348 := by decide +kernel

private theorem cost_2301_498_block17 : P1_7_1_3.blockEstimate 2301 498 2674 128 = 19581906150 := by decide +kernel

private theorem cost_2301_498_block18 : P1_7_1_3.blockEstimate 2301 498 2802 128 = 12228639936 := by decide +kernel

private theorem cost_2301_498_block19 : P1_7_1_3.blockEstimate 2301 498 2930 128 = 6342196416 := by decide +kernel

private theorem cost_2301_498_block20 : P1_7_1_3.blockEstimate 2301 498 3058 128 = 2271296704 := by decide +kernel

private theorem cost_2301_498_block21 : P1_7_1_3.blockEstimate 2301 498 3186 111 = 266887656 := by decide +kernel

private theorem cost_2301_498_join0_0 : P1_7_1_3.blockEstimate 2301 498 498 256 = 5968600896 :=
  @P1_7_1_3.block_append 2301 498 498 626 128 128 256 789129120 5179471776 5968600896 cost_2301_498_block0 cost_2301_498_block1 rfl rfl rfl

private theorem cost_2301_498_join0_2 : P1_7_1_3.blockEstimate 2301 498 754 256 = 37181615225 :=
  @P1_7_1_3.block_append 2301 498 754 882 128 128 256 13184255904 23997359321 37181615225 cost_2301_498_block2 cost_2301_498_block3 rfl rfl rfl

private theorem cost_2301_498_join0_4 : P1_7_1_3.blockEstimate 2301 498 1010 256 = 82396923904 :=
  @P1_7_1_3.block_append 2301 498 1010 1138 128 128 256 36006945792 46389978112 82396923904 cost_2301_498_block4 cost_2301_498_block5 rfl rfl rfl

private theorem cost_2301_498_join0_6 : P1_7_1_3.blockEstimate 2301 498 1266 256 = 115557222400 :=
  @P1_7_1_3.block_append 2301 498 1266 1394 128 128 256 54680052736 60877169664 115557222400 cost_2301_498_block6 cost_2301_498_block7 rfl rfl rfl

private theorem cost_2301_498_join0_8 : P1_7_1_3.blockEstimate 2301 498 1522 256 = 131973859328 :=
  @P1_7_1_3.block_append 2301 498 1522 1650 128 128 256 64981328896 66992530432 131973859328 cost_2301_498_block8 cost_2301_498_block9 rfl rfl rfl

private theorem cost_2301_498_join0_10 : P1_7_1_3.blockEstimate 2301 498 1778 256 = 131646834688 :=
  @P1_7_1_3.block_append 2301 498 1778 1906 128 128 256 66910774272 64736060416 131646834688 cost_2301_498_block10 cost_2301_498_block11 rfl rfl rfl

private theorem cost_2301_498_join0_12 : P1_7_1_3.blockEstimate 2301 498 2034 256 = 114576148480 :=
  @P1_7_1_3.block_append 2301 498 2034 2162 128 128 256 60468388864 54107759616 114576148480 cost_2301_498_block12 cost_2301_498_block13 rfl rfl rfl

private theorem cost_2301_498_join0_14 : P1_7_1_3.blockEstimate 2301 498 2290 256 = 82699599791 :=
  @P1_7_1_3.block_append 2301 498 2290 2418 128 128 256 45848083600 36851516191 82699599791 cost_2301_498_block14 cost_2301_498_block15 rfl rfl rfl

private theorem cost_2301_498_join0_16 : P1_7_1_3.blockEstimate 2301 498 2546 256 = 47509694498 :=
  @P1_7_1_3.block_append 2301 498 2546 2674 128 128 256 27927788348 19581906150 47509694498 cost_2301_498_block16 cost_2301_498_block17 rfl rfl rfl

private theorem cost_2301_498_join0_18 : P1_7_1_3.blockEstimate 2301 498 2802 256 = 18570836352 :=
  @P1_7_1_3.block_append 2301 498 2802 2930 128 128 256 12228639936 6342196416 18570836352 cost_2301_498_block18 cost_2301_498_block19 rfl rfl rfl

private theorem cost_2301_498_join0_20 : P1_7_1_3.blockEstimate 2301 498 3058 239 = 2538184360 :=
  @P1_7_1_3.block_append 2301 498 3058 3186 128 111 239 2271296704 266887656 2538184360 cost_2301_498_block20 cost_2301_498_block21 rfl rfl rfl

private theorem cost_2301_498_join1_0 : P1_7_1_3.blockEstimate 2301 498 498 512 = 43150216121 :=
  @P1_7_1_3.block_append 2301 498 498 754 256 256 512 5968600896 37181615225 43150216121 cost_2301_498_join0_0 cost_2301_498_join0_2 rfl rfl rfl

private theorem cost_2301_498_join1_2 : P1_7_1_3.blockEstimate 2301 498 1010 512 = 197954146304 :=
  @P1_7_1_3.block_append 2301 498 1010 1266 256 256 512 82396923904 115557222400 197954146304 cost_2301_498_join0_4 cost_2301_498_join0_6 rfl rfl rfl

private theorem cost_2301_498_join1_4 : P1_7_1_3.blockEstimate 2301 498 1522 512 = 263620694016 :=
  @P1_7_1_3.block_append 2301 498 1522 1778 256 256 512 131973859328 131646834688 263620694016 cost_2301_498_join0_8 cost_2301_498_join0_10 rfl rfl rfl

private theorem cost_2301_498_join1_6 : P1_7_1_3.blockEstimate 2301 498 2034 512 = 197275748271 :=
  @P1_7_1_3.block_append 2301 498 2034 2290 256 256 512 114576148480 82699599791 197275748271 cost_2301_498_join0_12 cost_2301_498_join0_14 rfl rfl rfl

private theorem cost_2301_498_join1_8 : P1_7_1_3.blockEstimate 2301 498 2546 512 = 66080530850 :=
  @P1_7_1_3.block_append 2301 498 2546 2802 256 256 512 47509694498 18570836352 66080530850 cost_2301_498_join0_16 cost_2301_498_join0_18 rfl rfl rfl

private theorem cost_2301_498_join2_0 : P1_7_1_3.blockEstimate 2301 498 498 1024 = 241104362425 :=
  @P1_7_1_3.block_append 2301 498 498 1010 512 512 1024 43150216121 197954146304 241104362425 cost_2301_498_join1_0 cost_2301_498_join1_2 rfl rfl rfl

private theorem cost_2301_498_join2_2 : P1_7_1_3.blockEstimate 2301 498 1522 1024 = 460896442287 :=
  @P1_7_1_3.block_append 2301 498 1522 2034 512 512 1024 263620694016 197275748271 460896442287 cost_2301_498_join1_4 cost_2301_498_join1_6 rfl rfl rfl

private theorem cost_2301_498_join2_4 : P1_7_1_3.blockEstimate 2301 498 2546 751 = 68618715210 :=
  @P1_7_1_3.block_append 2301 498 2546 3058 512 239 751 66080530850 2538184360 68618715210 cost_2301_498_join1_8 cost_2301_498_join0_20 rfl rfl rfl

private theorem cost_2301_498_join3_0 : P1_7_1_3.blockEstimate 2301 498 498 2048 = 702000804712 :=
  @P1_7_1_3.block_append 2301 498 498 1522 1024 1024 2048 241104362425 460896442287 702000804712 cost_2301_498_join2_0 cost_2301_498_join2_2 rfl rfl rfl

private theorem cost_2301_498_join4_0 : P1_7_1_3.blockEstimate 2301 498 498 2799 = 770619519922 :=
  @P1_7_1_3.block_append 2301 498 498 2546 2048 751 2799 702000804712 68618715210 770619519922 cost_2301_498_join3_0 cost_2301_498_join2_4 rfl rfl rfl

private theorem cost_2301_498_total : P1_7_1_3.momentEstimate 2301 498 = 770619519922 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2301 + 498 = 2799 by decide]
  exact cost_2301_498_join4_0

theorem moment2301_498 : P1_7_1.groupedPoleMoment 2301 498 ≤ 770619519922 :=
  (P1_7_1_3.grouped_bound 2301 498).trans_eq cost_2301_498_total
private theorem cost_2301_512_block0 : P1_7_1_3.blockEstimate 2301 512 512 128 = 789129120 := by decide +kernel

private theorem cost_2301_512_block1 : P1_7_1_3.blockEstimate 2301 512 640 128 = 5179471776 := by decide +kernel

private theorem cost_2301_512_block2 : P1_7_1_3.blockEstimate 2301 512 768 128 = 13184255904 := by decide +kernel

private theorem cost_2301_512_block3 : P1_7_1_3.blockEstimate 2301 512 896 128 = 23998175136 := by decide +kernel

private theorem cost_2301_512_block4 : P1_7_1_3.blockEstimate 2301 512 1024 128 = 36224038080 := by decide +kernel

private theorem cost_2301_512_block5 : P1_7_1_3.blockEstimate 2301 512 1152 128 = 46957212864 := by decide +kernel

private theorem cost_2301_512_block6 : P1_7_1_3.blockEstimate 2301 512 1280 128 = 55538709696 := by decide +kernel

private theorem cost_2301_512_block7 : P1_7_1_3.blockEstimate 2301 512 1408 128 = 61968528576 := by decide +kernel

private theorem cost_2301_512_block8 : P1_7_1_3.blockEstimate 2301 512 1536 128 = 66246669504 := by decide +kernel

private theorem cost_2301_512_block9 : P1_7_1_3.blockEstimate 2301 512 1664 128 = 68373132480 := by decide +kernel

private theorem cost_2301_512_block10 : P1_7_1_3.blockEstimate 2301 512 1792 128 = 68347917504 := by decide +kernel

private theorem cost_2301_512_block11 : P1_7_1_3.blockEstimate 2301 512 1920 128 = 66171024576 := by decide +kernel

private theorem cost_2301_512_block12 : P1_7_1_3.blockEstimate 2301 512 2048 128 = 61842453696 := by decide +kernel

private theorem cost_2301_512_block13 : P1_7_1_3.blockEstimate 2301 512 2176 128 = 55362208704 := by decide +kernel

private theorem cost_2301_512_block14 : P1_7_1_3.blockEstimate 2301 512 2304 128 = 46999685736 := by decide +kernel

private theorem cost_2301_512_block15 : P1_7_1_3.blockEstimate 2301 512 2432 128 = 37946867370 := by decide +kernel

private theorem cost_2301_512_block16 : P1_7_1_3.blockEstimate 2301 512 2560 128 = 28938492827 := by decide +kernel

private theorem cost_2301_512_block17 : P1_7_1_3.blockEstimate 2301 512 2688 128 = 20476651424 := by decide +kernel

private theorem cost_2301_512_block18 : P1_7_1_3.blockEstimate 2301 512 2816 128 = 12971881616 := by decide +kernel

private theorem cost_2301_512_block19 : P1_7_1_3.blockEstimate 2301 512 2944 128 = 6902130832 := by decide +kernel

private theorem cost_2301_512_block20 : P1_7_1_3.blockEstimate 2301 512 3072 128 = 2620398736 := by decide +kernel

private theorem cost_2301_512_block21 : P1_7_1_3.blockEstimate 2301 512 3200 125 = 378343568 := by decide +kernel

private theorem cost_2301_512_join0_0 : P1_7_1_3.blockEstimate 2301 512 512 256 = 5968600896 :=
  @P1_7_1_3.block_append 2301 512 512 640 128 128 256 789129120 5179471776 5968600896 cost_2301_512_block0 cost_2301_512_block1 rfl rfl rfl

private theorem cost_2301_512_join0_2 : P1_7_1_3.blockEstimate 2301 512 768 256 = 37182431040 :=
  @P1_7_1_3.block_append 2301 512 768 896 128 128 256 13184255904 23998175136 37182431040 cost_2301_512_block2 cost_2301_512_block3 rfl rfl rfl

private theorem cost_2301_512_join0_4 : P1_7_1_3.blockEstimate 2301 512 1024 256 = 83181250944 :=
  @P1_7_1_3.block_append 2301 512 1024 1152 128 128 256 36224038080 46957212864 83181250944 cost_2301_512_block4 cost_2301_512_block5 rfl rfl rfl

private theorem cost_2301_512_join0_6 : P1_7_1_3.blockEstimate 2301 512 1280 256 = 117507238272 :=
  @P1_7_1_3.block_append 2301 512 1280 1408 128 128 256 55538709696 61968528576 117507238272 cost_2301_512_block6 cost_2301_512_block7 rfl rfl rfl

private theorem cost_2301_512_join0_8 : P1_7_1_3.blockEstimate 2301 512 1536 256 = 134619801984 :=
  @P1_7_1_3.block_append 2301 512 1536 1664 128 128 256 66246669504 68373132480 134619801984 cost_2301_512_block8 cost_2301_512_block9 rfl rfl rfl

private theorem cost_2301_512_join0_10 : P1_7_1_3.blockEstimate 2301 512 1792 256 = 134518942080 :=
  @P1_7_1_3.block_append 2301 512 1792 1920 128 128 256 68347917504 66171024576 134518942080 cost_2301_512_block10 cost_2301_512_block11 rfl rfl rfl

private theorem cost_2301_512_join0_12 : P1_7_1_3.blockEstimate 2301 512 2048 256 = 117204662400 :=
  @P1_7_1_3.block_append 2301 512 2048 2176 128 128 256 61842453696 55362208704 117204662400 cost_2301_512_block12 cost_2301_512_block13 rfl rfl rfl

private theorem cost_2301_512_join0_14 : P1_7_1_3.blockEstimate 2301 512 2304 256 = 84946553106 :=
  @P1_7_1_3.block_append 2301 512 2304 2432 128 128 256 46999685736 37946867370 84946553106 cost_2301_512_block14 cost_2301_512_block15 rfl rfl rfl

private theorem cost_2301_512_join0_16 : P1_7_1_3.blockEstimate 2301 512 2560 256 = 49415144251 :=
  @P1_7_1_3.block_append 2301 512 2560 2688 128 128 256 28938492827 20476651424 49415144251 cost_2301_512_block16 cost_2301_512_block17 rfl rfl rfl

private theorem cost_2301_512_join0_18 : P1_7_1_3.blockEstimate 2301 512 2816 256 = 19874012448 :=
  @P1_7_1_3.block_append 2301 512 2816 2944 128 128 256 12971881616 6902130832 19874012448 cost_2301_512_block18 cost_2301_512_block19 rfl rfl rfl

private theorem cost_2301_512_join0_20 : P1_7_1_3.blockEstimate 2301 512 3072 253 = 2998742304 :=
  @P1_7_1_3.block_append 2301 512 3072 3200 128 125 253 2620398736 378343568 2998742304 cost_2301_512_block20 cost_2301_512_block21 rfl rfl rfl

private theorem cost_2301_512_join1_0 : P1_7_1_3.blockEstimate 2301 512 512 512 = 43151031936 :=
  @P1_7_1_3.block_append 2301 512 512 768 256 256 512 5968600896 37182431040 43151031936 cost_2301_512_join0_0 cost_2301_512_join0_2 rfl rfl rfl

private theorem cost_2301_512_join1_2 : P1_7_1_3.blockEstimate 2301 512 1024 512 = 200688489216 :=
  @P1_7_1_3.block_append 2301 512 1024 1280 256 256 512 83181250944 117507238272 200688489216 cost_2301_512_join0_4 cost_2301_512_join0_6 rfl rfl rfl

private theorem cost_2301_512_join1_4 : P1_7_1_3.blockEstimate 2301 512 1536 512 = 269138744064 :=
  @P1_7_1_3.block_append 2301 512 1536 1792 256 256 512 134619801984 134518942080 269138744064 cost_2301_512_join0_8 cost_2301_512_join0_10 rfl rfl rfl

private theorem cost_2301_512_join1_6 : P1_7_1_3.blockEstimate 2301 512 2048 512 = 202151215506 :=
  @P1_7_1_3.block_append 2301 512 2048 2304 256 256 512 117204662400 84946553106 202151215506 cost_2301_512_join0_12 cost_2301_512_join0_14 rfl rfl rfl

private theorem cost_2301_512_join1_8 : P1_7_1_3.blockEstimate 2301 512 2560 512 = 69289156699 :=
  @P1_7_1_3.block_append 2301 512 2560 2816 256 256 512 49415144251 19874012448 69289156699 cost_2301_512_join0_16 cost_2301_512_join0_18 rfl rfl rfl

private theorem cost_2301_512_join2_0 : P1_7_1_3.blockEstimate 2301 512 512 1024 = 243839521152 :=
  @P1_7_1_3.block_append 2301 512 512 1024 512 512 1024 43151031936 200688489216 243839521152 cost_2301_512_join1_0 cost_2301_512_join1_2 rfl rfl rfl

private theorem cost_2301_512_join2_2 : P1_7_1_3.blockEstimate 2301 512 1536 1024 = 471289959570 :=
  @P1_7_1_3.block_append 2301 512 1536 2048 512 512 1024 269138744064 202151215506 471289959570 cost_2301_512_join1_4 cost_2301_512_join1_6 rfl rfl rfl

private theorem cost_2301_512_join2_4 : P1_7_1_3.blockEstimate 2301 512 2560 765 = 72287899003 :=
  @P1_7_1_3.block_append 2301 512 2560 3072 512 253 765 69289156699 2998742304 72287899003 cost_2301_512_join1_8 cost_2301_512_join0_20 rfl rfl rfl

private theorem cost_2301_512_join3_0 : P1_7_1_3.blockEstimate 2301 512 512 2048 = 715129480722 :=
  @P1_7_1_3.block_append 2301 512 512 1536 1024 1024 2048 243839521152 471289959570 715129480722 cost_2301_512_join2_0 cost_2301_512_join2_2 rfl rfl rfl

private theorem cost_2301_512_join4_0 : P1_7_1_3.blockEstimate 2301 512 512 2813 = 787417379725 :=
  @P1_7_1_3.block_append 2301 512 512 2560 2048 765 2813 715129480722 72287899003 787417379725 cost_2301_512_join3_0 cost_2301_512_join2_4 rfl rfl rfl

private theorem cost_2301_512_total : P1_7_1_3.momentEstimate 2301 512 = 787417379725 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2301 + 512 = 2813 by decide]
  exact cost_2301_512_join4_0

theorem moment2301_512 : P1_7_1.groupedPoleMoment 2301 512 ≤ 787417379725 :=
  (P1_7_1_3.grouped_bound 2301 512).trans_eq cost_2301_512_total
private theorem cost_2301_514_block0 : P1_7_1_3.blockEstimate 2301 514 514 128 = 789129120 := by decide +kernel

private theorem cost_2301_514_block1 : P1_7_1_3.blockEstimate 2301 514 642 128 = 5179471776 := by decide +kernel

private theorem cost_2301_514_block2 : P1_7_1_3.blockEstimate 2301 514 770 128 = 13184255904 := by decide +kernel

private theorem cost_2301_514_block3 : P1_7_1_3.blockEstimate 2301 514 898 128 = 23998175136 := by decide +kernel

private theorem cost_2301_514_block4 : P1_7_1_3.blockEstimate 2301 514 1026 128 = 36251519229 := by decide +kernel

private theorem cost_2301_514_block5 : P1_7_1_3.blockEstimate 2301 514 1154 128 = 47034974720 := by decide +kernel

private theorem cost_2301_514_block6 : P1_7_1_3.blockEstimate 2301 514 1282 128 = 55658365440 := by decide +kernel

private theorem cost_2301_514_block7 : P1_7_1_3.blockEstimate 2301 514 1410 128 = 62121689600 := by decide +kernel

private theorem cost_2301_514_block8 : P1_7_1_3.blockEstimate 2301 514 1538 128 = 66424947200 := by decide +kernel

private theorem cost_2301_514_block9 : P1_7_1_3.blockEstimate 2301 514 1666 128 = 68568138240 := by decide +kernel

private theorem cost_2301_514_block10 : P1_7_1_3.blockEstimate 2301 514 1794 128 = 68551262720 := by decide +kernel

private theorem cost_2301_514_block11 : P1_7_1_3.blockEstimate 2301 514 1922 128 = 66374320640 := by decide +kernel

private theorem cost_2301_514_block12 : P1_7_1_3.blockEstimate 2301 514 2050 128 = 62037312000 := by decide +kernel

private theorem cost_2301_514_block13 : P1_7_1_3.blockEstimate 2301 514 2178 128 = 55540253417 := by decide +kernel

private theorem cost_2301_514_block14 : P1_7_1_3.blockEstimate 2301 514 2306 128 = 47164611007 := by decide +kernel

private theorem cost_2301_514_block15 : P1_7_1_3.blockEstimate 2301 514 2434 128 = 38104065761 := by decide +kernel

private theorem cost_2301_514_block16 : P1_7_1_3.blockEstimate 2301 514 2562 128 = 29083869816 := by decide +kernel

private theorem cost_2301_514_block17 : P1_7_1_3.blockEstimate 2301 514 2690 128 = 20605726710 := by decide +kernel

private theorem cost_2301_514_block18 : P1_7_1_3.blockEstimate 2301 514 2818 128 = 13079567040 := by decide +kernel

private theorem cost_2301_514_block19 : P1_7_1_3.blockEstimate 2301 514 2946 128 = 6983875264 := by decide +kernel

private theorem cost_2301_514_block20 : P1_7_1_3.blockEstimate 2301 514 3074 128 = 2672270016 := by decide +kernel

private theorem cost_2301_514_block21 : P1_7_1_3.blockEstimate 2301 514 3202 127 = 396409536 := by decide +kernel

private theorem cost_2301_514_join0_0 : P1_7_1_3.blockEstimate 2301 514 514 256 = 5968600896 :=
  @P1_7_1_3.block_append 2301 514 514 642 128 128 256 789129120 5179471776 5968600896 cost_2301_514_block0 cost_2301_514_block1 rfl rfl rfl

private theorem cost_2301_514_join0_2 : P1_7_1_3.blockEstimate 2301 514 770 256 = 37182431040 :=
  @P1_7_1_3.block_append 2301 514 770 898 128 128 256 13184255904 23998175136 37182431040 cost_2301_514_block2 cost_2301_514_block3 rfl rfl rfl

private theorem cost_2301_514_join0_4 : P1_7_1_3.blockEstimate 2301 514 1026 256 = 83286493949 :=
  @P1_7_1_3.block_append 2301 514 1026 1154 128 128 256 36251519229 47034974720 83286493949 cost_2301_514_block4 cost_2301_514_block5 rfl rfl rfl

private theorem cost_2301_514_join0_6 : P1_7_1_3.blockEstimate 2301 514 1282 256 = 117780055040 :=
  @P1_7_1_3.block_append 2301 514 1282 1410 128 128 256 55658365440 62121689600 117780055040 cost_2301_514_block6 cost_2301_514_block7 rfl rfl rfl

private theorem cost_2301_514_join0_8 : P1_7_1_3.blockEstimate 2301 514 1538 256 = 134993085440 :=
  @P1_7_1_3.block_append 2301 514 1538 1666 128 128 256 66424947200 68568138240 134993085440 cost_2301_514_block8 cost_2301_514_block9 rfl rfl rfl

private theorem cost_2301_514_join0_10 : P1_7_1_3.blockEstimate 2301 514 1794 256 = 134925583360 :=
  @P1_7_1_3.block_append 2301 514 1794 1922 128 128 256 68551262720 66374320640 134925583360 cost_2301_514_block10 cost_2301_514_block11 rfl rfl rfl

private theorem cost_2301_514_join0_12 : P1_7_1_3.blockEstimate 2301 514 2050 256 = 117577565417 :=
  @P1_7_1_3.block_append 2301 514 2050 2178 128 128 256 62037312000 55540253417 117577565417 cost_2301_514_block12 cost_2301_514_block13 rfl rfl rfl

private theorem cost_2301_514_join0_14 : P1_7_1_3.blockEstimate 2301 514 2306 256 = 85268676768 :=
  @P1_7_1_3.block_append 2301 514 2306 2434 128 128 256 47164611007 38104065761 85268676768 cost_2301_514_block14 cost_2301_514_block15 rfl rfl rfl

private theorem cost_2301_514_join0_16 : P1_7_1_3.blockEstimate 2301 514 2562 256 = 49689596526 :=
  @P1_7_1_3.block_append 2301 514 2562 2690 128 128 256 29083869816 20605726710 49689596526 cost_2301_514_block16 cost_2301_514_block17 rfl rfl rfl

private theorem cost_2301_514_join0_18 : P1_7_1_3.blockEstimate 2301 514 2818 256 = 20063442304 :=
  @P1_7_1_3.block_append 2301 514 2818 2946 128 128 256 13079567040 6983875264 20063442304 cost_2301_514_block18 cost_2301_514_block19 rfl rfl rfl

private theorem cost_2301_514_join0_20 : P1_7_1_3.blockEstimate 2301 514 3074 255 = 3068679552 :=
  @P1_7_1_3.block_append 2301 514 3074 3202 128 127 255 2672270016 396409536 3068679552 cost_2301_514_block20 cost_2301_514_block21 rfl rfl rfl

private theorem cost_2301_514_join1_0 : P1_7_1_3.blockEstimate 2301 514 514 512 = 43151031936 :=
  @P1_7_1_3.block_append 2301 514 514 770 256 256 512 5968600896 37182431040 43151031936 cost_2301_514_join0_0 cost_2301_514_join0_2 rfl rfl rfl

private theorem cost_2301_514_join1_2 : P1_7_1_3.blockEstimate 2301 514 1026 512 = 201066548989 :=
  @P1_7_1_3.block_append 2301 514 1026 1282 256 256 512 83286493949 117780055040 201066548989 cost_2301_514_join0_4 cost_2301_514_join0_6 rfl rfl rfl

private theorem cost_2301_514_join1_4 : P1_7_1_3.blockEstimate 2301 514 1538 512 = 269918668800 :=
  @P1_7_1_3.block_append 2301 514 1538 1794 256 256 512 134993085440 134925583360 269918668800 cost_2301_514_join0_8 cost_2301_514_join0_10 rfl rfl rfl

private theorem cost_2301_514_join1_6 : P1_7_1_3.blockEstimate 2301 514 2050 512 = 202846242185 :=
  @P1_7_1_3.block_append 2301 514 2050 2306 256 256 512 117577565417 85268676768 202846242185 cost_2301_514_join0_12 cost_2301_514_join0_14 rfl rfl rfl

private theorem cost_2301_514_join1_8 : P1_7_1_3.blockEstimate 2301 514 2562 512 = 69753038830 :=
  @P1_7_1_3.block_append 2301 514 2562 2818 256 256 512 49689596526 20063442304 69753038830 cost_2301_514_join0_16 cost_2301_514_join0_18 rfl rfl rfl

private theorem cost_2301_514_join2_0 : P1_7_1_3.blockEstimate 2301 514 514 1024 = 244217580925 :=
  @P1_7_1_3.block_append 2301 514 514 1026 512 512 1024 43151031936 201066548989 244217580925 cost_2301_514_join1_0 cost_2301_514_join1_2 rfl rfl rfl

private theorem cost_2301_514_join2_2 : P1_7_1_3.blockEstimate 2301 514 1538 1024 = 472764910985 :=
  @P1_7_1_3.block_append 2301 514 1538 2050 512 512 1024 269918668800 202846242185 472764910985 cost_2301_514_join1_4 cost_2301_514_join1_6 rfl rfl rfl

private theorem cost_2301_514_join2_4 : P1_7_1_3.blockEstimate 2301 514 2562 767 = 72821718382 :=
  @P1_7_1_3.block_append 2301 514 2562 3074 512 255 767 69753038830 3068679552 72821718382 cost_2301_514_join1_8 cost_2301_514_join0_20 rfl rfl rfl

private theorem cost_2301_514_join3_0 : P1_7_1_3.blockEstimate 2301 514 514 2048 = 716982491910 :=
  @P1_7_1_3.block_append 2301 514 514 1538 1024 1024 2048 244217580925 472764910985 716982491910 cost_2301_514_join2_0 cost_2301_514_join2_2 rfl rfl rfl

private theorem cost_2301_514_join4_0 : P1_7_1_3.blockEstimate 2301 514 514 2815 = 789804210292 :=
  @P1_7_1_3.block_append 2301 514 514 2562 2048 767 2815 716982491910 72821718382 789804210292 cost_2301_514_join3_0 cost_2301_514_join2_4 rfl rfl rfl

private theorem cost_2301_514_total : P1_7_1_3.momentEstimate 2301 514 = 789804210292 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2301 + 514 = 2815 by decide]
  exact cost_2301_514_join4_0

theorem moment2301_514 : P1_7_1.groupedPoleMoment 2301 514 ≤ 789804210292 :=
  (P1_7_1_3.grouped_bound 2301 514).trans_eq cost_2301_514_total
private theorem cost_2302_498_block0 : P1_7_1_3.blockEstimate 2302 498 498 128 = 789486880 := by decide +kernel

private theorem cost_2302_498_block1 : P1_7_1_3.blockEstimate 2302 498 626 128 = 5181943072 := by decide +kernel

private theorem cost_2302_498_block2 : P1_7_1_3.blockEstimate 2302 498 754 128 = 13190937888 := by decide +kernel

private theorem cost_2302_498_block3 : P1_7_1_3.blockEstimate 2302 498 882 128 = 24010348690 := by decide +kernel

private theorem cost_2302_498_block4 : P1_7_1_3.blockEstimate 2302 498 1010 128 = 36027863872 := by decide +kernel

private theorem cost_2302_498_block5 : P1_7_1_3.blockEstimate 2302 498 1138 128 = 46419071808 := by decide +kernel

private theorem cost_2302_498_block6 : P1_7_1_3.blockEstimate 2302 498 1266 128 = 54717322048 := by decide +kernel

private theorem cost_2302_498_block7 : P1_7_1_3.blockEstimate 2302 498 1394 128 = 60922614592 := by decide +kernel

private theorem cost_2302_498_block8 : P1_7_1_3.blockEstimate 2302 498 1522 128 = 65034949440 := by decide +kernel

private theorem cost_2302_498_block9 : P1_7_1_3.blockEstimate 2302 498 1650 128 = 67054326592 := by decide +kernel

private theorem cost_2302_498_block10 : P1_7_1_3.blockEstimate 2302 498 1778 128 = 66980746048 := by decide +kernel

private theorem cost_2302_498_block11 : P1_7_1_3.blockEstimate 2302 498 1906 128 = 64814207808 := by decide +kernel

private theorem cost_2302_498_block12 : P1_7_1_3.blockEstimate 2302 498 2034 128 = 60554711872 := by decide +kernel

private theorem cost_2302_498_block13 : P1_7_1_3.blockEstimate 2302 498 2162 128 = 54202258240 := by decide +kernel

private theorem cost_2302_498_block14 : P1_7_1_3.blockEstimate 2302 498 2290 128 = 45945836791 := by decide +kernel

private theorem cost_2302_498_block15 : P1_7_1_3.blockEstimate 2302 498 2418 128 = 36943640699 := by decide +kernel

private theorem cost_2302_498_block16 : P1_7_1_3.blockEstimate 2302 498 2546 128 = 28011146004 := by decide +kernel

private theorem cost_2302_498_block17 : P1_7_1_3.blockEstimate 2302 498 2674 128 = 19653823952 := by decide +kernel

private theorem cost_2302_498_block18 : P1_7_1_3.blockEstimate 2302 498 2802 128 = 12287169280 := by decide +kernel

private theorem cost_2302_498_block19 : P1_7_1_3.blockEstimate 2302 498 2930 128 = 6384505600 := by decide +kernel

private theorem cost_2302_498_block20 : P1_7_1_3.blockEstimate 2302 498 3058 128 = 2296468224 := by decide +kernel

private theorem cost_2302_498_block21 : P1_7_1_3.blockEstimate 2302 498 3186 112 = 274133216 := by decide +kernel

private theorem cost_2302_498_join0_0 : P1_7_1_3.blockEstimate 2302 498 498 256 = 5971429952 :=
  @P1_7_1_3.block_append 2302 498 498 626 128 128 256 789486880 5181943072 5971429952 cost_2302_498_block0 cost_2302_498_block1 rfl rfl rfl

private theorem cost_2302_498_join0_2 : P1_7_1_3.blockEstimate 2302 498 754 256 = 37201286578 :=
  @P1_7_1_3.block_append 2302 498 754 882 128 128 256 13190937888 24010348690 37201286578 cost_2302_498_block2 cost_2302_498_block3 rfl rfl rfl

private theorem cost_2302_498_join0_4 : P1_7_1_3.blockEstimate 2302 498 1010 256 = 82446935680 :=
  @P1_7_1_3.block_append 2302 498 1010 1138 128 128 256 36027863872 46419071808 82446935680 cost_2302_498_block4 cost_2302_498_block5 rfl rfl rfl

private theorem cost_2302_498_join0_6 : P1_7_1_3.blockEstimate 2302 498 1266 256 = 115639936640 :=
  @P1_7_1_3.block_append 2302 498 1266 1394 128 128 256 54717322048 60922614592 115639936640 cost_2302_498_block6 cost_2302_498_block7 rfl rfl rfl

private theorem cost_2302_498_join0_8 : P1_7_1_3.blockEstimate 2302 498 1522 256 = 132089276032 :=
  @P1_7_1_3.block_append 2302 498 1522 1650 128 128 256 65034949440 67054326592 132089276032 cost_2302_498_block8 cost_2302_498_block9 rfl rfl rfl

private theorem cost_2302_498_join0_10 : P1_7_1_3.blockEstimate 2302 498 1778 256 = 131794953856 :=
  @P1_7_1_3.block_append 2302 498 1778 1906 128 128 256 66980746048 64814207808 131794953856 cost_2302_498_block10 cost_2302_498_block11 rfl rfl rfl

private theorem cost_2302_498_join0_12 : P1_7_1_3.blockEstimate 2302 498 2034 256 = 114756970112 :=
  @P1_7_1_3.block_append 2302 498 2034 2162 128 128 256 60554711872 54202258240 114756970112 cost_2302_498_block12 cost_2302_498_block13 rfl rfl rfl

private theorem cost_2302_498_join0_14 : P1_7_1_3.blockEstimate 2302 498 2290 256 = 82889477490 :=
  @P1_7_1_3.block_append 2302 498 2290 2418 128 128 256 45945836791 36943640699 82889477490 cost_2302_498_block14 cost_2302_498_block15 rfl rfl rfl

private theorem cost_2302_498_join0_16 : P1_7_1_3.blockEstimate 2302 498 2546 256 = 47664969956 :=
  @P1_7_1_3.block_append 2302 498 2546 2674 128 128 256 28011146004 19653823952 47664969956 cost_2302_498_block16 cost_2302_498_block17 rfl rfl rfl

private theorem cost_2302_498_join0_18 : P1_7_1_3.blockEstimate 2302 498 2802 256 = 18671674880 :=
  @P1_7_1_3.block_append 2302 498 2802 2930 128 128 256 12287169280 6384505600 18671674880 cost_2302_498_block18 cost_2302_498_block19 rfl rfl rfl

private theorem cost_2302_498_join0_20 : P1_7_1_3.blockEstimate 2302 498 3058 240 = 2570601440 :=
  @P1_7_1_3.block_append 2302 498 3058 3186 128 112 240 2296468224 274133216 2570601440 cost_2302_498_block20 cost_2302_498_block21 rfl rfl rfl

private theorem cost_2302_498_join1_0 : P1_7_1_3.blockEstimate 2302 498 498 512 = 43172716530 :=
  @P1_7_1_3.block_append 2302 498 498 754 256 256 512 5971429952 37201286578 43172716530 cost_2302_498_join0_0 cost_2302_498_join0_2 rfl rfl rfl

private theorem cost_2302_498_join1_2 : P1_7_1_3.blockEstimate 2302 498 1010 512 = 198086872320 :=
  @P1_7_1_3.block_append 2302 498 1010 1266 256 256 512 82446935680 115639936640 198086872320 cost_2302_498_join0_4 cost_2302_498_join0_6 rfl rfl rfl

private theorem cost_2302_498_join1_4 : P1_7_1_3.blockEstimate 2302 498 1522 512 = 263884229888 :=
  @P1_7_1_3.block_append 2302 498 1522 1778 256 256 512 132089276032 131794953856 263884229888 cost_2302_498_join0_8 cost_2302_498_join0_10 rfl rfl rfl

private theorem cost_2302_498_join1_6 : P1_7_1_3.blockEstimate 2302 498 2034 512 = 197646447602 :=
  @P1_7_1_3.block_append 2302 498 2034 2290 256 256 512 114756970112 82889477490 197646447602 cost_2302_498_join0_12 cost_2302_498_join0_14 rfl rfl rfl

private theorem cost_2302_498_join1_8 : P1_7_1_3.blockEstimate 2302 498 2546 512 = 66336644836 :=
  @P1_7_1_3.block_append 2302 498 2546 2802 256 256 512 47664969956 18671674880 66336644836 cost_2302_498_join0_16 cost_2302_498_join0_18 rfl rfl rfl

private theorem cost_2302_498_join2_0 : P1_7_1_3.blockEstimate 2302 498 498 1024 = 241259588850 :=
  @P1_7_1_3.block_append 2302 498 498 1010 512 512 1024 43172716530 198086872320 241259588850 cost_2302_498_join1_0 cost_2302_498_join1_2 rfl rfl rfl

private theorem cost_2302_498_join2_2 : P1_7_1_3.blockEstimate 2302 498 1522 1024 = 461530677490 :=
  @P1_7_1_3.block_append 2302 498 1522 2034 512 512 1024 263884229888 197646447602 461530677490 cost_2302_498_join1_4 cost_2302_498_join1_6 rfl rfl rfl

private theorem cost_2302_498_join2_4 : P1_7_1_3.blockEstimate 2302 498 2546 752 = 68907246276 :=
  @P1_7_1_3.block_append 2302 498 2546 3058 512 240 752 66336644836 2570601440 68907246276 cost_2302_498_join1_8 cost_2302_498_join0_20 rfl rfl rfl

private theorem cost_2302_498_join3_0 : P1_7_1_3.blockEstimate 2302 498 498 2048 = 702790266340 :=
  @P1_7_1_3.block_append 2302 498 498 1522 1024 1024 2048 241259588850 461530677490 702790266340 cost_2302_498_join2_0 cost_2302_498_join2_2 rfl rfl rfl

private theorem cost_2302_498_join4_0 : P1_7_1_3.blockEstimate 2302 498 498 2800 = 771697512616 :=
  @P1_7_1_3.block_append 2302 498 498 2546 2048 752 2800 702790266340 68907246276 771697512616 cost_2302_498_join3_0 cost_2302_498_join2_4 rfl rfl rfl

private theorem cost_2302_498_total : P1_7_1_3.momentEstimate 2302 498 = 771697512616 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2302 + 498 = 2800 by decide]
  exact cost_2302_498_join4_0

theorem moment2302_498 : P1_7_1.groupedPoleMoment 2302 498 ≤ 771697512616 :=
  (P1_7_1_3.grouped_bound 2302 498).trans_eq cost_2302_498_total
private theorem cost_2302_512_block0 : P1_7_1_3.blockEstimate 2302 512 512 128 = 789486880 := by decide +kernel

private theorem cost_2302_512_block1 : P1_7_1_3.blockEstimate 2302 512 640 128 = 5181943072 := by decide +kernel

private theorem cost_2302_512_block2 : P1_7_1_3.blockEstimate 2302 512 768 128 = 13190937888 := by decide +kernel

private theorem cost_2302_512_block3 : P1_7_1_3.blockEstimate 2302 512 896 128 = 24011164960 := by decide +kernel

private theorem cost_2302_512_block4 : P1_7_1_3.blockEstimate 2302 512 1024 128 = 36245083392 := by decide +kernel

private theorem cost_2302_512_block5 : P1_7_1_3.blockEstimate 2302 512 1152 128 = 46986663168 := by decide +kernel

private theorem cost_2302_512_block6 : P1_7_1_3.blockEstimate 2302 512 1280 128 = 55576564992 := by decide +kernel

private theorem cost_2302_512_block7 : P1_7_1_3.blockEstimate 2302 512 1408 128 = 62014788864 := by decide +kernel

private theorem cost_2302_512_block8 : P1_7_1_3.blockEstimate 2302 512 1536 128 = 66301334784 := by decide +kernel

private theorem cost_2302_512_block9 : P1_7_1_3.blockEstimate 2302 512 1664 128 = 68436202752 := by decide +kernel

private theorem cost_2302_512_block10 : P1_7_1_3.blockEstimate 2302 512 1792 128 = 68419392768 := by decide +kernel

private theorem cost_2302_512_block11 : P1_7_1_3.blockEstimate 2302 512 1920 128 = 66250904832 := by decide +kernel

private theorem cost_2302_512_block12 : P1_7_1_3.blockEstimate 2302 512 2048 128 = 61930738944 := by decide +kernel

private theorem cost_2302_512_block13 : P1_7_1_3.blockEstimate 2302 512 2176 128 = 55458896384 := by decide +kernel

private theorem cost_2302_512_block14 : P1_7_1_3.blockEstimate 2302 512 2304 128 = 47098667540 := by decide +kernel

private theorem cost_2302_512_block15 : P1_7_1_3.blockEstimate 2302 512 2432 128 = 38040275118 := by decide +kernel

private theorem cost_2302_512_block16 : P1_7_1_3.blockEstimate 2302 512 2560 128 = 29023254391 := by decide +kernel

private theorem cost_2302_512_block17 : P1_7_1_3.blockEstimate 2302 512 2688 128 = 20550111637 := by decide +kernel

private theorem cost_2302_512_block18 : P1_7_1_3.blockEstimate 2302 512 2816 128 = 13032129392 := by decide +kernel

private theorem cost_2302_512_block19 : P1_7_1_3.blockEstimate 2302 512 2944 128 = 6946258800 := by decide +kernel

private theorem cost_2302_512_block20 : P1_7_1_3.blockEstimate 2302 512 3072 128 = 2647489392 := by decide +kernel

private theorem cost_2302_512_block21 : P1_7_1_3.blockEstimate 2302 512 3200 126 = 387479408 := by decide +kernel

private theorem cost_2302_512_join0_0 : P1_7_1_3.blockEstimate 2302 512 512 256 = 5971429952 :=
  @P1_7_1_3.block_append 2302 512 512 640 128 128 256 789486880 5181943072 5971429952 cost_2302_512_block0 cost_2302_512_block1 rfl rfl rfl

private theorem cost_2302_512_join0_2 : P1_7_1_3.blockEstimate 2302 512 768 256 = 37202102848 :=
  @P1_7_1_3.block_append 2302 512 768 896 128 128 256 13190937888 24011164960 37202102848 cost_2302_512_block2 cost_2302_512_block3 rfl rfl rfl

private theorem cost_2302_512_join0_4 : P1_7_1_3.blockEstimate 2302 512 1024 256 = 83231746560 :=
  @P1_7_1_3.block_append 2302 512 1024 1152 128 128 256 36245083392 46986663168 83231746560 cost_2302_512_block4 cost_2302_512_block5 rfl rfl rfl

private theorem cost_2302_512_join0_6 : P1_7_1_3.blockEstimate 2302 512 1280 256 = 117591353856 :=
  @P1_7_1_3.block_append 2302 512 1280 1408 128 128 256 55576564992 62014788864 117591353856 cost_2302_512_block6 cost_2302_512_block7 rfl rfl rfl

private theorem cost_2302_512_join0_8 : P1_7_1_3.blockEstimate 2302 512 1536 256 = 134737537536 :=
  @P1_7_1_3.block_append 2302 512 1536 1664 128 128 256 66301334784 68436202752 134737537536 cost_2302_512_block8 cost_2302_512_block9 rfl rfl rfl

private theorem cost_2302_512_join0_10 : P1_7_1_3.blockEstimate 2302 512 1792 256 = 134670297600 :=
  @P1_7_1_3.block_append 2302 512 1792 1920 128 128 256 68419392768 66250904832 134670297600 cost_2302_512_block10 cost_2302_512_block11 rfl rfl rfl

private theorem cost_2302_512_join0_12 : P1_7_1_3.blockEstimate 2302 512 2048 256 = 117389635328 :=
  @P1_7_1_3.block_append 2302 512 2048 2176 128 128 256 61930738944 55458896384 117389635328 cost_2302_512_block12 cost_2302_512_block13 rfl rfl rfl

private theorem cost_2302_512_join0_14 : P1_7_1_3.blockEstimate 2302 512 2304 256 = 85138942658 :=
  @P1_7_1_3.block_append 2302 512 2304 2432 128 128 256 47098667540 38040275118 85138942658 cost_2302_512_block14 cost_2302_512_block15 rfl rfl rfl

private theorem cost_2302_512_join0_16 : P1_7_1_3.blockEstimate 2302 512 2560 256 = 49573366028 :=
  @P1_7_1_3.block_append 2302 512 2560 2688 128 128 256 29023254391 20550111637 49573366028 cost_2302_512_block16 cost_2302_512_block17 rfl rfl rfl

private theorem cost_2302_512_join0_18 : P1_7_1_3.blockEstimate 2302 512 2816 256 = 19978388192 :=
  @P1_7_1_3.block_append 2302 512 2816 2944 128 128 256 13032129392 6946258800 19978388192 cost_2302_512_block18 cost_2302_512_block19 rfl rfl rfl

private theorem cost_2302_512_join0_20 : P1_7_1_3.blockEstimate 2302 512 3072 254 = 3034968800 :=
  @P1_7_1_3.block_append 2302 512 3072 3200 128 126 254 2647489392 387479408 3034968800 cost_2302_512_block20 cost_2302_512_block21 rfl rfl rfl

private theorem cost_2302_512_join1_0 : P1_7_1_3.blockEstimate 2302 512 512 512 = 43173532800 :=
  @P1_7_1_3.block_append 2302 512 512 768 256 256 512 5971429952 37202102848 43173532800 cost_2302_512_join0_0 cost_2302_512_join0_2 rfl rfl rfl

private theorem cost_2302_512_join1_2 : P1_7_1_3.blockEstimate 2302 512 1024 512 = 200823100416 :=
  @P1_7_1_3.block_append 2302 512 1024 1280 256 256 512 83231746560 117591353856 200823100416 cost_2302_512_join0_4 cost_2302_512_join0_6 rfl rfl rfl

private theorem cost_2302_512_join1_4 : P1_7_1_3.blockEstimate 2302 512 1536 512 = 269407835136 :=
  @P1_7_1_3.block_append 2302 512 1536 1792 256 256 512 134737537536 134670297600 269407835136 cost_2302_512_join0_8 cost_2302_512_join0_10 rfl rfl rfl

private theorem cost_2302_512_join1_6 : P1_7_1_3.blockEstimate 2302 512 2048 512 = 202528577986 :=
  @P1_7_1_3.block_append 2302 512 2048 2304 256 256 512 117389635328 85138942658 202528577986 cost_2302_512_join0_12 cost_2302_512_join0_14 rfl rfl rfl

private theorem cost_2302_512_join1_8 : P1_7_1_3.blockEstimate 2302 512 2560 512 = 69551754220 :=
  @P1_7_1_3.block_append 2302 512 2560 2816 256 256 512 49573366028 19978388192 69551754220 cost_2302_512_join0_16 cost_2302_512_join0_18 rfl rfl rfl

private theorem cost_2302_512_join2_0 : P1_7_1_3.blockEstimate 2302 512 512 1024 = 243996633216 :=
  @P1_7_1_3.block_append 2302 512 512 1024 512 512 1024 43173532800 200823100416 243996633216 cost_2302_512_join1_0 cost_2302_512_join1_2 rfl rfl rfl

private theorem cost_2302_512_join2_2 : P1_7_1_3.blockEstimate 2302 512 1536 1024 = 471936413122 :=
  @P1_7_1_3.block_append 2302 512 1536 2048 512 512 1024 269407835136 202528577986 471936413122 cost_2302_512_join1_4 cost_2302_512_join1_6 rfl rfl rfl

private theorem cost_2302_512_join2_4 : P1_7_1_3.blockEstimate 2302 512 2560 766 = 72586723020 :=
  @P1_7_1_3.block_append 2302 512 2560 3072 512 254 766 69551754220 3034968800 72586723020 cost_2302_512_join1_8 cost_2302_512_join0_20 rfl rfl rfl

private theorem cost_2302_512_join3_0 : P1_7_1_3.blockEstimate 2302 512 512 2048 = 715933046338 :=
  @P1_7_1_3.block_append 2302 512 512 1536 1024 1024 2048 243996633216 471936413122 715933046338 cost_2302_512_join2_0 cost_2302_512_join2_2 rfl rfl rfl

private theorem cost_2302_512_join4_0 : P1_7_1_3.blockEstimate 2302 512 512 2814 = 788519769358 :=
  @P1_7_1_3.block_append 2302 512 512 2560 2048 766 2814 715933046338 72586723020 788519769358 cost_2302_512_join3_0 cost_2302_512_join2_4 rfl rfl rfl

private theorem cost_2302_512_total : P1_7_1_3.momentEstimate 2302 512 = 788519769358 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2302 + 512 = 2814 by decide]
  exact cost_2302_512_join4_0

theorem moment2302_512 : P1_7_1.groupedPoleMoment 2302 512 ≤ 788519769358 :=
  (P1_7_1_3.grouped_bound 2302 512).trans_eq cost_2302_512_total
private theorem cost_2321_499_block0 : P1_7_1_3.blockEstimate 2321 499 499 128 = 796284320 := by decide +kernel

private theorem cost_2321_499_block1 : P1_7_1_3.blockEstimate 2321 499 627 128 = 5228897696 := by decide +kernel

private theorem cost_2321_499_block2 : P1_7_1_3.blockEstimate 2321 499 755 128 = 13317895584 := by decide +kernel

private theorem cost_2321_499_block3 : P1_7_1_3.blockEstimate 2321 499 883 128 = 24257311775 := by decide +kernel

private theorem cost_2321_499_block4 : P1_7_1_3.blockEstimate 2321 499 1011 128 = 36442448000 := by decide +kernel

private theorem cost_2321_499_block5 : P1_7_1_3.blockEstimate 2321 499 1139 128 = 47014224000 := by decide +kernel

private theorem cost_2321_499_block6 : P1_7_1_3.blockEstimate 2321 499 1267 128 = 55488848000 := by decide +kernel

private theorem cost_2321_499_block7 : P1_7_1_3.blockEstimate 2321 499 1395 128 = 61866320000 := by decide +kernel

private theorem cost_2321_499_block8 : P1_7_1_3.blockEstimate 2321 499 1523 128 = 66146640000 := by decide +kernel

private theorem cost_2321_499_block9 : P1_7_1_3.blockEstimate 2321 499 1651 128 = 68329808000 := by decide +kernel

private theorem cost_2321_499_block10 : P1_7_1_3.blockEstimate 2321 499 1779 128 = 68415824000 := by decide +kernel

private theorem cost_2321_499_block11 : P1_7_1_3.blockEstimate 2321 499 1907 128 = 66404688000 := by decide +kernel

private theorem cost_2321_499_block12 : P1_7_1_3.blockEstimate 2321 499 2035 128 = 62296400000 := by decide +kernel

private theorem cost_2321_499_block13 : P1_7_1_3.blockEstimate 2321 499 2163 128 = 56090960000 := by decide +kernel

private theorem cost_2321_499_block14 : P1_7_1_3.blockEstimate 2321 499 2291 128 = 47902376099 := by decide +kernel

private theorem cost_2321_499_block15 : P1_7_1_3.blockEstimate 2321 499 2419 128 = 38794463740 := by decide +kernel

private theorem cost_2321_499_block16 : P1_7_1_3.blockEstimate 2321 499 2547 128 = 29692185938 := by decide +kernel

private theorem cost_2321_499_block17 : P1_7_1_3.blockEstimate 2321 499 2675 128 = 21111072513 := by decide +kernel

private theorem cost_2321_499_block18 : P1_7_1_3.blockEstimate 2321 499 2803 128 = 13481769356 := by decide +kernel

private theorem cost_2321_499_block19 : P1_7_1_3.blockEstimate 2321 499 2931 128 = 7258821440 := by decide +kernel

private theorem cost_2321_499_block20 : P1_7_1_3.blockEstimate 2321 499 3059 128 = 2829957952 := by decide +kernel

private theorem cost_2321_499_block21 : P1_7_1_3.blockEstimate 2321 499 3187 128 = 447980352 := by decide +kernel

private theorem cost_2321_499_block22 : P1_7_1_3.blockEstimate 2321 499 3315 4 = 30156 := by decide +kernel

private theorem cost_2321_499_join0_0 : P1_7_1_3.blockEstimate 2321 499 499 256 = 6025182016 :=
  @P1_7_1_3.block_append 2321 499 499 627 128 128 256 796284320 5228897696 6025182016 cost_2321_499_block0 cost_2321_499_block1 rfl rfl rfl

private theorem cost_2321_499_join0_2 : P1_7_1_3.blockEstimate 2321 499 755 256 = 37575207359 :=
  @P1_7_1_3.block_append 2321 499 755 883 128 128 256 13317895584 24257311775 37575207359 cost_2321_499_block2 cost_2321_499_block3 rfl rfl rfl

private theorem cost_2321_499_join0_4 : P1_7_1_3.blockEstimate 2321 499 1011 256 = 83456672000 :=
  @P1_7_1_3.block_append 2321 499 1011 1139 128 128 256 36442448000 47014224000 83456672000 cost_2321_499_block4 cost_2321_499_block5 rfl rfl rfl

private theorem cost_2321_499_join0_6 : P1_7_1_3.blockEstimate 2321 499 1267 256 = 117355168000 :=
  @P1_7_1_3.block_append 2321 499 1267 1395 128 128 256 55488848000 61866320000 117355168000 cost_2321_499_block6 cost_2321_499_block7 rfl rfl rfl

private theorem cost_2321_499_join0_8 : P1_7_1_3.blockEstimate 2321 499 1523 256 = 134476448000 :=
  @P1_7_1_3.block_append 2321 499 1523 1651 128 128 256 66146640000 68329808000 134476448000 cost_2321_499_block8 cost_2321_499_block9 rfl rfl rfl

private theorem cost_2321_499_join0_10 : P1_7_1_3.blockEstimate 2321 499 1779 256 = 134820512000 :=
  @P1_7_1_3.block_append 2321 499 1779 1907 128 128 256 68415824000 66404688000 134820512000 cost_2321_499_block10 cost_2321_499_block11 rfl rfl rfl

private theorem cost_2321_499_join0_12 : P1_7_1_3.blockEstimate 2321 499 2035 256 = 118387360000 :=
  @P1_7_1_3.block_append 2321 499 2035 2163 128 128 256 62296400000 56090960000 118387360000 cost_2321_499_block12 cost_2321_499_block13 rfl rfl rfl

private theorem cost_2321_499_join0_14 : P1_7_1_3.blockEstimate 2321 499 2291 256 = 86696839839 :=
  @P1_7_1_3.block_append 2321 499 2291 2419 128 128 256 47902376099 38794463740 86696839839 cost_2321_499_block14 cost_2321_499_block15 rfl rfl rfl

private theorem cost_2321_499_join0_16 : P1_7_1_3.blockEstimate 2321 499 2547 256 = 50803258451 :=
  @P1_7_1_3.block_append 2321 499 2547 2675 128 128 256 29692185938 21111072513 50803258451 cost_2321_499_block16 cost_2321_499_block17 rfl rfl rfl

private theorem cost_2321_499_join0_18 : P1_7_1_3.blockEstimate 2321 499 2803 256 = 20740590796 :=
  @P1_7_1_3.block_append 2321 499 2803 2931 128 128 256 13481769356 7258821440 20740590796 cost_2321_499_block18 cost_2321_499_block19 rfl rfl rfl

private theorem cost_2321_499_join0_20 : P1_7_1_3.blockEstimate 2321 499 3059 256 = 3277938304 :=
  @P1_7_1_3.block_append 2321 499 3059 3187 128 128 256 2829957952 447980352 3277938304 cost_2321_499_block20 cost_2321_499_block21 rfl rfl rfl

private theorem cost_2321_499_join1_0 : P1_7_1_3.blockEstimate 2321 499 499 512 = 43600389375 :=
  @P1_7_1_3.block_append 2321 499 499 755 256 256 512 6025182016 37575207359 43600389375 cost_2321_499_join0_0 cost_2321_499_join0_2 rfl rfl rfl

private theorem cost_2321_499_join1_2 : P1_7_1_3.blockEstimate 2321 499 1011 512 = 200811840000 :=
  @P1_7_1_3.block_append 2321 499 1011 1267 256 256 512 83456672000 117355168000 200811840000 cost_2321_499_join0_4 cost_2321_499_join0_6 rfl rfl rfl

private theorem cost_2321_499_join1_4 : P1_7_1_3.blockEstimate 2321 499 1523 512 = 269296960000 :=
  @P1_7_1_3.block_append 2321 499 1523 1779 256 256 512 134476448000 134820512000 269296960000 cost_2321_499_join0_8 cost_2321_499_join0_10 rfl rfl rfl

private theorem cost_2321_499_join1_6 : P1_7_1_3.blockEstimate 2321 499 2035 512 = 205084199839 :=
  @P1_7_1_3.block_append 2321 499 2035 2291 256 256 512 118387360000 86696839839 205084199839 cost_2321_499_join0_12 cost_2321_499_join0_14 rfl rfl rfl

private theorem cost_2321_499_join1_8 : P1_7_1_3.blockEstimate 2321 499 2547 512 = 71543849247 :=
  @P1_7_1_3.block_append 2321 499 2547 2803 256 256 512 50803258451 20740590796 71543849247 cost_2321_499_join0_16 cost_2321_499_join0_18 rfl rfl rfl

private theorem cost_2321_499_join1_10 : P1_7_1_3.blockEstimate 2321 499 3059 260 = 3277968460 :=
  @P1_7_1_3.block_append 2321 499 3059 3315 256 4 260 3277938304 30156 3277968460 cost_2321_499_join0_20 cost_2321_499_block22 rfl rfl rfl

private theorem cost_2321_499_join2_0 : P1_7_1_3.blockEstimate 2321 499 499 1024 = 244412229375 :=
  @P1_7_1_3.block_append 2321 499 499 1011 512 512 1024 43600389375 200811840000 244412229375 cost_2321_499_join1_0 cost_2321_499_join1_2 rfl rfl rfl

private theorem cost_2321_499_join2_2 : P1_7_1_3.blockEstimate 2321 499 1523 1024 = 474381159839 :=
  @P1_7_1_3.block_append 2321 499 1523 2035 512 512 1024 269296960000 205084199839 474381159839 cost_2321_499_join1_4 cost_2321_499_join1_6 rfl rfl rfl

private theorem cost_2321_499_join2_4 : P1_7_1_3.blockEstimate 2321 499 2547 772 = 74821817707 :=
  @P1_7_1_3.block_append 2321 499 2547 3059 512 260 772 71543849247 3277968460 74821817707 cost_2321_499_join1_8 cost_2321_499_join1_10 rfl rfl rfl

private theorem cost_2321_499_join3_0 : P1_7_1_3.blockEstimate 2321 499 499 2048 = 718793389214 :=
  @P1_7_1_3.block_append 2321 499 499 1523 1024 1024 2048 244412229375 474381159839 718793389214 cost_2321_499_join2_0 cost_2321_499_join2_2 rfl rfl rfl

private theorem cost_2321_499_join4_0 : P1_7_1_3.blockEstimate 2321 499 499 2820 = 793615206921 :=
  @P1_7_1_3.block_append 2321 499 499 2547 2048 772 2820 718793389214 74821817707 793615206921 cost_2321_499_join3_0 cost_2321_499_join2_4 rfl rfl rfl

private theorem cost_2321_499_total : P1_7_1_3.momentEstimate 2321 499 = 793615206921 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2321 + 499 = 2820 by decide]
  exact cost_2321_499_join4_0

theorem moment2321_499 : P1_7_1.groupedPoleMoment 2321 499 ≤ 793615206921 :=
  (P1_7_1_3.grouped_bound 2321 499).trans_eq cost_2321_499_total
private theorem cost_2378_511_block0 : P1_7_1_3.blockEstimate 2378 511 511 128 = 816676640 := by decide +kernel

private theorem cost_2378_511_block1 : P1_7_1_3.blockEstimate 2378 511 639 128 = 5369761568 := by decide +kernel

private theorem cost_2378_511_block2 : P1_7_1_3.blockEstimate 2378 511 767 128 = 13698768672 := by decide +kernel

private theorem cost_2378_511_block3 : P1_7_1_3.blockEstimate 2378 511 895 128 = 24998391584 := by decide +kernel

private theorem cost_2378_511_block4 : P1_7_1_3.blockEstimate 2378 511 1023 128 = 37829820416 := by decide +kernel

private theorem cost_2378_511_block5 : P1_7_1_3.blockEstimate 2378 511 1151 128 = 49183801344 := by decide +kernel

private theorem cost_2378_511_block6 : P1_7_1_3.blockEstimate 2378 511 1279 128 = 58390298624 := by decide +kernel

private theorem cost_2378_511_block7 : P1_7_1_3.blockEstimate 2378 511 1407 128 = 65449312256 := by decide +kernel

private theorem cost_2378_511_block8 : P1_7_1_3.blockEstimate 2378 511 1535 128 = 70360842240 := by decide +kernel

private theorem cost_2378_511_block9 : P1_7_1_3.blockEstimate 2378 511 1663 128 = 73124888576 := by decide +kernel

private theorem cost_2378_511_block10 : P1_7_1_3.blockEstimate 2378 511 1791 128 = 73741451264 := by decide +kernel

private theorem cost_2378_511_block11 : P1_7_1_3.blockEstimate 2378 511 1919 128 = 72210530304 := by decide +kernel

private theorem cost_2378_511_block12 : P1_7_1_3.blockEstimate 2378 511 2047 128 = 68532125696 := by decide +kernel

private theorem cost_2378_511_block13 : P1_7_1_3.blockEstimate 2378 511 2175 128 = 62706237440 := by decide +kernel

private theorem cost_2378_511_block14 : P1_7_1_3.blockEstimate 2378 511 2303 128 = 54750912674 := by decide +kernel

private theorem cost_2378_511_block15 : P1_7_1_3.blockEstimate 2378 511 2431 128 = 45368627458 := by decide +kernel

private theorem cost_2378_511_block16 : P1_7_1_3.blockEstimate 2378 511 2559 128 = 35743366394 := by decide +kernel

private theorem cost_2378_511_block17 : P1_7_1_3.blockEstimate 2378 511 2687 128 = 26451514578 := by decide +kernel

private theorem cost_2378_511_block18 : P1_7_1_3.blockEstimate 2378 511 2815 128 = 17965493425 := by decide +kernel

private theorem cost_2378_511_block19 : P1_7_1_3.blockEstimate 2378 511 2943 128 = 10693360368 := by decide +kernel

private theorem cost_2378_511_block20 : P1_7_1_3.blockEstimate 2378 511 3071 128 = 5111166704 := by decide +kernel

private theorem cost_2378_511_block21 : P1_7_1_3.blockEstimate 2378 511 3199 128 = 1499968240 := by decide +kernel

private theorem cost_2378_511_block22 : P1_7_1_3.blockEstimate 2378 511 3327 73 = 80759063 := by decide +kernel

private theorem cost_2378_511_join0_0 : P1_7_1_3.blockEstimate 2378 511 511 256 = 6186438208 :=
  @P1_7_1_3.block_append 2378 511 511 639 128 128 256 816676640 5369761568 6186438208 cost_2378_511_block0 cost_2378_511_block1 rfl rfl rfl

private theorem cost_2378_511_join0_2 : P1_7_1_3.blockEstimate 2378 511 767 256 = 38697160256 :=
  @P1_7_1_3.block_append 2378 511 767 895 128 128 256 13698768672 24998391584 38697160256 cost_2378_511_block2 cost_2378_511_block3 rfl rfl rfl

private theorem cost_2378_511_join0_4 : P1_7_1_3.blockEstimate 2378 511 1023 256 = 87013621760 :=
  @P1_7_1_3.block_append 2378 511 1023 1151 128 128 256 37829820416 49183801344 87013621760 cost_2378_511_block4 cost_2378_511_block5 rfl rfl rfl

private theorem cost_2378_511_join0_6 : P1_7_1_3.blockEstimate 2378 511 1279 256 = 123839610880 :=
  @P1_7_1_3.block_append 2378 511 1279 1407 128 128 256 58390298624 65449312256 123839610880 cost_2378_511_block6 cost_2378_511_block7 rfl rfl rfl

private theorem cost_2378_511_join0_8 : P1_7_1_3.blockEstimate 2378 511 1535 256 = 143485730816 :=
  @P1_7_1_3.block_append 2378 511 1535 1663 128 128 256 70360842240 73124888576 143485730816 cost_2378_511_block8 cost_2378_511_block9 rfl rfl rfl

private theorem cost_2378_511_join0_10 : P1_7_1_3.blockEstimate 2378 511 1791 256 = 145951981568 :=
  @P1_7_1_3.block_append 2378 511 1791 1919 128 128 256 73741451264 72210530304 145951981568 cost_2378_511_block10 cost_2378_511_block11 rfl rfl rfl

private theorem cost_2378_511_join0_12 : P1_7_1_3.blockEstimate 2378 511 2047 256 = 131238363136 :=
  @P1_7_1_3.block_append 2378 511 2047 2175 128 128 256 68532125696 62706237440 131238363136 cost_2378_511_block12 cost_2378_511_block13 rfl rfl rfl

private theorem cost_2378_511_join0_14 : P1_7_1_3.blockEstimate 2378 511 2303 256 = 100119540132 :=
  @P1_7_1_3.block_append 2378 511 2303 2431 128 128 256 54750912674 45368627458 100119540132 cost_2378_511_block14 cost_2378_511_block15 rfl rfl rfl

private theorem cost_2378_511_join0_16 : P1_7_1_3.blockEstimate 2378 511 2559 256 = 62194880972 :=
  @P1_7_1_3.block_append 2378 511 2559 2687 128 128 256 35743366394 26451514578 62194880972 cost_2378_511_block16 cost_2378_511_block17 rfl rfl rfl

private theorem cost_2378_511_join0_18 : P1_7_1_3.blockEstimate 2378 511 2815 256 = 28658853793 :=
  @P1_7_1_3.block_append 2378 511 2815 2943 128 128 256 17965493425 10693360368 28658853793 cost_2378_511_block18 cost_2378_511_block19 rfl rfl rfl

private theorem cost_2378_511_join0_20 : P1_7_1_3.blockEstimate 2378 511 3071 256 = 6611134944 :=
  @P1_7_1_3.block_append 2378 511 3071 3199 128 128 256 5111166704 1499968240 6611134944 cost_2378_511_block20 cost_2378_511_block21 rfl rfl rfl

private theorem cost_2378_511_join1_0 : P1_7_1_3.blockEstimate 2378 511 511 512 = 44883598464 :=
  @P1_7_1_3.block_append 2378 511 511 767 256 256 512 6186438208 38697160256 44883598464 cost_2378_511_join0_0 cost_2378_511_join0_2 rfl rfl rfl

private theorem cost_2378_511_join1_2 : P1_7_1_3.blockEstimate 2378 511 1023 512 = 210853232640 :=
  @P1_7_1_3.block_append 2378 511 1023 1279 256 256 512 87013621760 123839610880 210853232640 cost_2378_511_join0_4 cost_2378_511_join0_6 rfl rfl rfl

private theorem cost_2378_511_join1_4 : P1_7_1_3.blockEstimate 2378 511 1535 512 = 289437712384 :=
  @P1_7_1_3.block_append 2378 511 1535 1791 256 256 512 143485730816 145951981568 289437712384 cost_2378_511_join0_8 cost_2378_511_join0_10 rfl rfl rfl

private theorem cost_2378_511_join1_6 : P1_7_1_3.blockEstimate 2378 511 2047 512 = 231357903268 :=
  @P1_7_1_3.block_append 2378 511 2047 2303 256 256 512 131238363136 100119540132 231357903268 cost_2378_511_join0_12 cost_2378_511_join0_14 rfl rfl rfl

private theorem cost_2378_511_join1_8 : P1_7_1_3.blockEstimate 2378 511 2559 512 = 90853734765 :=
  @P1_7_1_3.block_append 2378 511 2559 2815 256 256 512 62194880972 28658853793 90853734765 cost_2378_511_join0_16 cost_2378_511_join0_18 rfl rfl rfl

private theorem cost_2378_511_join1_10 : P1_7_1_3.blockEstimate 2378 511 3071 329 = 6691894007 :=
  @P1_7_1_3.block_append 2378 511 3071 3327 256 73 329 6611134944 80759063 6691894007 cost_2378_511_join0_20 cost_2378_511_block22 rfl rfl rfl

private theorem cost_2378_511_join2_0 : P1_7_1_3.blockEstimate 2378 511 511 1024 = 255736831104 :=
  @P1_7_1_3.block_append 2378 511 511 1023 512 512 1024 44883598464 210853232640 255736831104 cost_2378_511_join1_0 cost_2378_511_join1_2 rfl rfl rfl

private theorem cost_2378_511_join2_2 : P1_7_1_3.blockEstimate 2378 511 1535 1024 = 520795615652 :=
  @P1_7_1_3.block_append 2378 511 1535 2047 512 512 1024 289437712384 231357903268 520795615652 cost_2378_511_join1_4 cost_2378_511_join1_6 rfl rfl rfl

private theorem cost_2378_511_join2_4 : P1_7_1_3.blockEstimate 2378 511 2559 841 = 97545628772 :=
  @P1_7_1_3.block_append 2378 511 2559 3071 512 329 841 90853734765 6691894007 97545628772 cost_2378_511_join1_8 cost_2378_511_join1_10 rfl rfl rfl

private theorem cost_2378_511_join3_0 : P1_7_1_3.blockEstimate 2378 511 511 2048 = 776532446756 :=
  @P1_7_1_3.block_append 2378 511 511 1535 1024 1024 2048 255736831104 520795615652 776532446756 cost_2378_511_join2_0 cost_2378_511_join2_2 rfl rfl rfl

private theorem cost_2378_511_join4_0 : P1_7_1_3.blockEstimate 2378 511 511 2889 = 874078075528 :=
  @P1_7_1_3.block_append 2378 511 511 2559 2048 841 2889 776532446756 97545628772 874078075528 cost_2378_511_join3_0 cost_2378_511_join2_4 rfl rfl rfl

private theorem cost_2378_511_total : P1_7_1_3.momentEstimate 2378 511 = 874078075528 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2378 + 511 = 2889 by decide]
  exact cost_2378_511_join4_0

theorem moment2378_511 : P1_7_1.groupedPoleMoment 2378 511 ≤ 874078075528 :=
  (P1_7_1_3.grouped_bound 2378 511).trans_eq cost_2378_511_total
private theorem cost_2445_531_block0 : P1_7_1_3.blockEstimate 2445 531 531 128 = 840646560 := by decide +kernel

private theorem cost_2445_531_block1 : P1_7_1_3.blockEstimate 2445 531 659 128 = 5535338400 := by decide +kernel

private theorem cost_2445_531_block2 : P1_7_1_3.blockEstimate 2445 531 787 128 = 14146461600 := by decide +kernel

private theorem cost_2445_531_block3 : P1_7_1_3.blockEstimate 2445 531 915 128 = 25868709792 := by decide +kernel

private theorem cost_2445_531_block4 : P1_7_1_3.blockEstimate 2445 531 1043 128 = 39501232503 := by decide +kernel

private theorem cost_2445_531_block5 : P1_7_1_3.blockEstimate 2445 531 1171 128 = 51967683712 := by decide +kernel

private theorem cost_2445_531_block6 : P1_7_1_3.blockEstimate 2445 531 1299 128 = 62204963968 := by decide +kernel

private theorem cost_2445_531_block7 : P1_7_1_3.blockEstimate 2445 531 1427 128 = 70210874496 := by decide +kernel

private theorem cost_2445_531_block8 : P1_7_1_3.blockEstimate 2445 531 1555 128 = 75985415296 := by decide +kernel

private theorem cost_2445_531_block9 : P1_7_1_3.blockEstimate 2445 531 1683 128 = 79528586368 := by decide +kernel

private theorem cost_2445_531_block10 : P1_7_1_3.blockEstimate 2445 531 1811 128 = 80840387712 := by decide +kernel

private theorem cost_2445_531_block11 : P1_7_1_3.blockEstimate 2445 531 1939 128 = 79920819328 := by decide +kernel

private theorem cost_2445_531_block12 : P1_7_1_3.blockEstimate 2445 531 2067 128 = 76769881216 := by decide +kernel

private theorem cost_2445_531_block13 : P1_7_1_3.blockEstimate 2445 531 2195 128 = 71387573376 := by decide +kernel

private theorem cost_2445_531_block14 : P1_7_1_3.blockEstimate 2445 531 2323 128 = 63773926374 := by decide +kernel

private theorem cost_2445_531_block15 : P1_7_1_3.blockEstimate 2445 531 2451 128 = 54239264015 := by decide +kernel

private theorem cost_2445_531_block16 : P1_7_1_3.blockEstimate 2445 531 2579 128 = 44056277168 := by decide +kernel

private theorem cost_2445_531_block17 : P1_7_1_3.blockEstimate 2445 531 2707 128 = 33963916411 := by decide +kernel

private theorem cost_2445_531_block18 : P1_7_1_3.blockEstimate 2445 531 2835 128 = 24466822547 := by decide +kernel

private theorem cost_2445_531_block19 : P1_7_1_3.blockEstimate 2445 531 2963 128 = 15983564735 := by decide +kernel

private theorem cost_2445_531_block20 : P1_7_1_3.blockEstimate 2445 531 3091 128 = 8976942112 := by decide +kernel

private theorem cost_2445_531_block21 : P1_7_1_3.blockEstimate 2445 531 3219 128 = 3839792160 := by decide +kernel

private theorem cost_2445_531_block22 : P1_7_1_3.blockEstimate 2445 531 3347 128 = 824501280 := by decide +kernel

private theorem cost_2445_531_block23 : P1_7_1_3.blockEstimate 2445 531 3475 32 = 7603080 := by decide +kernel

private theorem cost_2445_531_join0_0 : P1_7_1_3.blockEstimate 2445 531 531 256 = 6375984960 :=
  @P1_7_1_3.block_append 2445 531 531 659 128 128 256 840646560 5535338400 6375984960 cost_2445_531_block0 cost_2445_531_block1 rfl rfl rfl

private theorem cost_2445_531_join0_2 : P1_7_1_3.blockEstimate 2445 531 787 256 = 40015171392 :=
  @P1_7_1_3.block_append 2445 531 787 915 128 128 256 14146461600 25868709792 40015171392 cost_2445_531_block2 cost_2445_531_block3 rfl rfl rfl

private theorem cost_2445_531_join0_4 : P1_7_1_3.blockEstimate 2445 531 1043 256 = 91468916215 :=
  @P1_7_1_3.block_append 2445 531 1043 1171 128 128 256 39501232503 51967683712 91468916215 cost_2445_531_block4 cost_2445_531_block5 rfl rfl rfl

private theorem cost_2445_531_join0_6 : P1_7_1_3.blockEstimate 2445 531 1299 256 = 132415838464 :=
  @P1_7_1_3.block_append 2445 531 1299 1427 128 128 256 62204963968 70210874496 132415838464 cost_2445_531_block6 cost_2445_531_block7 rfl rfl rfl

private theorem cost_2445_531_join0_8 : P1_7_1_3.blockEstimate 2445 531 1555 256 = 155514001664 :=
  @P1_7_1_3.block_append 2445 531 1555 1683 128 128 256 75985415296 79528586368 155514001664 cost_2445_531_block8 cost_2445_531_block9 rfl rfl rfl

private theorem cost_2445_531_join0_10 : P1_7_1_3.blockEstimate 2445 531 1811 256 = 160761207040 :=
  @P1_7_1_3.block_append 2445 531 1811 1939 128 128 256 80840387712 79920819328 160761207040 cost_2445_531_block10 cost_2445_531_block11 rfl rfl rfl

private theorem cost_2445_531_join0_12 : P1_7_1_3.blockEstimate 2445 531 2067 256 = 148157454592 :=
  @P1_7_1_3.block_append 2445 531 2067 2195 128 128 256 76769881216 71387573376 148157454592 cost_2445_531_block12 cost_2445_531_block13 rfl rfl rfl

private theorem cost_2445_531_join0_14 : P1_7_1_3.blockEstimate 2445 531 2323 256 = 118013190389 :=
  @P1_7_1_3.block_append 2445 531 2323 2451 128 128 256 63773926374 54239264015 118013190389 cost_2445_531_block14 cost_2445_531_block15 rfl rfl rfl

private theorem cost_2445_531_join0_16 : P1_7_1_3.blockEstimate 2445 531 2579 256 = 78020193579 :=
  @P1_7_1_3.block_append 2445 531 2579 2707 128 128 256 44056277168 33963916411 78020193579 cost_2445_531_block16 cost_2445_531_block17 rfl rfl rfl

private theorem cost_2445_531_join0_18 : P1_7_1_3.blockEstimate 2445 531 2835 256 = 40450387282 :=
  @P1_7_1_3.block_append 2445 531 2835 2963 128 128 256 24466822547 15983564735 40450387282 cost_2445_531_block18 cost_2445_531_block19 rfl rfl rfl

private theorem cost_2445_531_join0_20 : P1_7_1_3.blockEstimate 2445 531 3091 256 = 12816734272 :=
  @P1_7_1_3.block_append 2445 531 3091 3219 128 128 256 8976942112 3839792160 12816734272 cost_2445_531_block20 cost_2445_531_block21 rfl rfl rfl

private theorem cost_2445_531_join0_22 : P1_7_1_3.blockEstimate 2445 531 3347 160 = 832104360 :=
  @P1_7_1_3.block_append 2445 531 3347 3475 128 32 160 824501280 7603080 832104360 cost_2445_531_block22 cost_2445_531_block23 rfl rfl rfl

private theorem cost_2445_531_join1_0 : P1_7_1_3.blockEstimate 2445 531 531 512 = 46391156352 :=
  @P1_7_1_3.block_append 2445 531 531 787 256 256 512 6375984960 40015171392 46391156352 cost_2445_531_join0_0 cost_2445_531_join0_2 rfl rfl rfl

private theorem cost_2445_531_join1_2 : P1_7_1_3.blockEstimate 2445 531 1043 512 = 223884754679 :=
  @P1_7_1_3.block_append 2445 531 1043 1299 256 256 512 91468916215 132415838464 223884754679 cost_2445_531_join0_4 cost_2445_531_join0_6 rfl rfl rfl

private theorem cost_2445_531_join1_4 : P1_7_1_3.blockEstimate 2445 531 1555 512 = 316275208704 :=
  @P1_7_1_3.block_append 2445 531 1555 1811 256 256 512 155514001664 160761207040 316275208704 cost_2445_531_join0_8 cost_2445_531_join0_10 rfl rfl rfl

private theorem cost_2445_531_join1_6 : P1_7_1_3.blockEstimate 2445 531 2067 512 = 266170644981 :=
  @P1_7_1_3.block_append 2445 531 2067 2323 256 256 512 148157454592 118013190389 266170644981 cost_2445_531_join0_12 cost_2445_531_join0_14 rfl rfl rfl

private theorem cost_2445_531_join1_8 : P1_7_1_3.blockEstimate 2445 531 2579 512 = 118470580861 :=
  @P1_7_1_3.block_append 2445 531 2579 2835 256 256 512 78020193579 40450387282 118470580861 cost_2445_531_join0_16 cost_2445_531_join0_18 rfl rfl rfl

private theorem cost_2445_531_join1_10 : P1_7_1_3.blockEstimate 2445 531 3091 416 = 13648838632 :=
  @P1_7_1_3.block_append 2445 531 3091 3347 256 160 416 12816734272 832104360 13648838632 cost_2445_531_join0_20 cost_2445_531_join0_22 rfl rfl rfl

private theorem cost_2445_531_join2_0 : P1_7_1_3.blockEstimate 2445 531 531 1024 = 270275911031 :=
  @P1_7_1_3.block_append 2445 531 531 1043 512 512 1024 46391156352 223884754679 270275911031 cost_2445_531_join1_0 cost_2445_531_join1_2 rfl rfl rfl

private theorem cost_2445_531_join2_2 : P1_7_1_3.blockEstimate 2445 531 1555 1024 = 582445853685 :=
  @P1_7_1_3.block_append 2445 531 1555 2067 512 512 1024 316275208704 266170644981 582445853685 cost_2445_531_join1_4 cost_2445_531_join1_6 rfl rfl rfl

private theorem cost_2445_531_join2_4 : P1_7_1_3.blockEstimate 2445 531 2579 928 = 132119419493 :=
  @P1_7_1_3.block_append 2445 531 2579 3091 512 416 928 118470580861 13648838632 132119419493 cost_2445_531_join1_8 cost_2445_531_join1_10 rfl rfl rfl

private theorem cost_2445_531_join3_0 : P1_7_1_3.blockEstimate 2445 531 531 2048 = 852721764716 :=
  @P1_7_1_3.block_append 2445 531 531 1555 1024 1024 2048 270275911031 582445853685 852721764716 cost_2445_531_join2_0 cost_2445_531_join2_2 rfl rfl rfl

private theorem cost_2445_531_join4_0 : P1_7_1_3.blockEstimate 2445 531 531 2976 = 984841184209 :=
  @P1_7_1_3.block_append 2445 531 531 2579 2048 928 2976 852721764716 132119419493 984841184209 cost_2445_531_join3_0 cost_2445_531_join2_4 rfl rfl rfl

private theorem cost_2445_531_total : P1_7_1_3.momentEstimate 2445 531 = 984841184209 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2445 + 531 = 2976 by decide]
  exact cost_2445_531_join4_0

theorem moment2445_531 : P1_7_1.groupedPoleMoment 2445 531 ≤ 984841184209 :=
  (P1_7_1_3.grouped_bound 2445 531).trans_eq cost_2445_531_total
private theorem cost_2462_535_block0 : P1_7_1_3.blockEstimate 2462 535 535 128 = 846728480 := by decide +kernel

private theorem cost_2462_535_block1 : P1_7_1_3.blockEstimate 2462 535 663 128 = 5577350432 := by decide +kernel

private theorem cost_2462_535_block2 : P1_7_1_3.blockEstimate 2462 535 791 128 = 14260055328 := by decide +kernel

private theorem cost_2462_535_block3 : P1_7_1_3.blockEstimate 2462 535 919 128 = 26089536800 := by decide +kernel

private theorem cost_2462_535_block4 : P1_7_1_3.blockEstimate 2462 535 1047 128 = 39903827630 := by decide +kernel

private theorem cost_2462_535_block5 : P1_7_1_3.blockEstimate 2462 535 1175 128 = 52629145344 := by decide +kernel

private theorem cost_2462_535_block6 : P1_7_1_3.blockEstimate 2462 535 1303 128 = 63110252288 := by decide +kernel

private theorem cost_2462_535_block7 : P1_7_1_3.blockEstimate 2462 535 1431 128 = 71343212288 := by decide +kernel

private theorem cost_2462_535_block8 : P1_7_1_3.blockEstimate 2462 535 1559 128 = 77328025344 := by decide +kernel

private theorem cost_2462_535_block9 : P1_7_1_3.blockEstimate 2462 535 1687 128 = 81064691456 := by decide +kernel

private theorem cost_2462_535_block10 : P1_7_1_3.blockEstimate 2462 535 1815 128 = 82553210624 := by decide +kernel

private theorem cost_2462_535_block11 : P1_7_1_3.blockEstimate 2462 535 1943 128 = 81793582848 := by decide +kernel

private theorem cost_2462_535_block12 : P1_7_1_3.blockEstimate 2462 535 2071 128 = 78785808128 := by decide +kernel

private theorem cost_2462_535_block13 : P1_7_1_3.blockEstimate 2462 535 2199 128 = 73529886464 := by decide +kernel

private theorem cost_2462_535_block14 : P1_7_1_3.blockEstimate 2462 535 2327 128 = 66025817856 := by decide +kernel

private theorem cost_2462_535_block15 : P1_7_1_3.blockEstimate 2462 535 2455 128 = 56501676535 := by decide +kernel

private theorem cost_2462_535_block16 : P1_7_1_3.blockEstimate 2462 535 2583 128 = 46198111711 := by decide +kernel

private theorem cost_2462_535_block17 : P1_7_1_3.blockEstimate 2462 535 2711 128 = 35924265412 := by decide +kernel

private theorem cost_2462_535_block18 : P1_7_1_3.blockEstimate 2462 535 2839 128 = 26190432993 := by decide +kernel

private theorem cost_2462_535_block19 : P1_7_1_3.blockEstimate 2462 535 2967 128 = 17428907369 := by decide +kernel

private theorem cost_2462_535_block20 : P1_7_1_3.blockEstimate 2462 535 3095 128 = 10082074928 := by decide +kernel

private theorem cost_2462_535_block21 : P1_7_1_3.blockEstimate 2462 535 3223 128 = 4577596720 := by decide +kernel

private theorem cost_2462_535_block22 : P1_7_1_3.blockEstimate 2462 535 3351 128 = 1171515696 := by decide +kernel

private theorem cost_2462_535_block23 : P1_7_1_3.blockEstimate 2462 535 3479 53 = 32866631 := by decide +kernel

private theorem cost_2462_535_join0_0 : P1_7_1_3.blockEstimate 2462 535 535 256 = 6424078912 :=
  @P1_7_1_3.block_append 2462 535 535 663 128 128 256 846728480 5577350432 6424078912 cost_2462_535_block0 cost_2462_535_block1 rfl rfl rfl

private theorem cost_2462_535_join0_2 : P1_7_1_3.blockEstimate 2462 535 791 256 = 40349592128 :=
  @P1_7_1_3.block_append 2462 535 791 919 128 128 256 14260055328 26089536800 40349592128 cost_2462_535_block2 cost_2462_535_block3 rfl rfl rfl

private theorem cost_2462_535_join0_4 : P1_7_1_3.blockEstimate 2462 535 1047 256 = 92532972974 :=
  @P1_7_1_3.block_append 2462 535 1047 1175 128 128 256 39903827630 52629145344 92532972974 cost_2462_535_block4 cost_2462_535_block5 rfl rfl rfl

private theorem cost_2462_535_join0_6 : P1_7_1_3.blockEstimate 2462 535 1303 256 = 134453464576 :=
  @P1_7_1_3.block_append 2462 535 1303 1431 128 128 256 63110252288 71343212288 134453464576 cost_2462_535_block6 cost_2462_535_block7 rfl rfl rfl

private theorem cost_2462_535_join0_8 : P1_7_1_3.blockEstimate 2462 535 1559 256 = 158392716800 :=
  @P1_7_1_3.block_append 2462 535 1559 1687 128 128 256 77328025344 81064691456 158392716800 cost_2462_535_block8 cost_2462_535_block9 rfl rfl rfl

private theorem cost_2462_535_join0_10 : P1_7_1_3.blockEstimate 2462 535 1815 256 = 164346793472 :=
  @P1_7_1_3.block_append 2462 535 1815 1943 128 128 256 82553210624 81793582848 164346793472 cost_2462_535_block10 cost_2462_535_block11 rfl rfl rfl

private theorem cost_2462_535_join0_12 : P1_7_1_3.blockEstimate 2462 535 2071 256 = 152315694592 :=
  @P1_7_1_3.block_append 2462 535 2071 2199 128 128 256 78785808128 73529886464 152315694592 cost_2462_535_block12 cost_2462_535_block13 rfl rfl rfl

private theorem cost_2462_535_join0_14 : P1_7_1_3.blockEstimate 2462 535 2327 256 = 122527494391 :=
  @P1_7_1_3.block_append 2462 535 2327 2455 128 128 256 66025817856 56501676535 122527494391 cost_2462_535_block14 cost_2462_535_block15 rfl rfl rfl

private theorem cost_2462_535_join0_16 : P1_7_1_3.blockEstimate 2462 535 2583 256 = 82122377123 :=
  @P1_7_1_3.block_append 2462 535 2583 2711 128 128 256 46198111711 35924265412 82122377123 cost_2462_535_block16 cost_2462_535_block17 rfl rfl rfl

private theorem cost_2462_535_join0_18 : P1_7_1_3.blockEstimate 2462 535 2839 256 = 43619340362 :=
  @P1_7_1_3.block_append 2462 535 2839 2967 128 128 256 26190432993 17428907369 43619340362 cost_2462_535_block18 cost_2462_535_block19 rfl rfl rfl

private theorem cost_2462_535_join0_20 : P1_7_1_3.blockEstimate 2462 535 3095 256 = 14659671648 :=
  @P1_7_1_3.block_append 2462 535 3095 3223 128 128 256 10082074928 4577596720 14659671648 cost_2462_535_block20 cost_2462_535_block21 rfl rfl rfl

private theorem cost_2462_535_join0_22 : P1_7_1_3.blockEstimate 2462 535 3351 181 = 1204382327 :=
  @P1_7_1_3.block_append 2462 535 3351 3479 128 53 181 1171515696 32866631 1204382327 cost_2462_535_block22 cost_2462_535_block23 rfl rfl rfl

private theorem cost_2462_535_join1_0 : P1_7_1_3.blockEstimate 2462 535 535 512 = 46773671040 :=
  @P1_7_1_3.block_append 2462 535 535 791 256 256 512 6424078912 40349592128 46773671040 cost_2462_535_join0_0 cost_2462_535_join0_2 rfl rfl rfl

private theorem cost_2462_535_join1_2 : P1_7_1_3.blockEstimate 2462 535 1047 512 = 226986437550 :=
  @P1_7_1_3.block_append 2462 535 1047 1303 256 256 512 92532972974 134453464576 226986437550 cost_2462_535_join0_4 cost_2462_535_join0_6 rfl rfl rfl

private theorem cost_2462_535_join1_4 : P1_7_1_3.blockEstimate 2462 535 1559 512 = 322739510272 :=
  @P1_7_1_3.block_append 2462 535 1559 1815 256 256 512 158392716800 164346793472 322739510272 cost_2462_535_join0_8 cost_2462_535_join0_10 rfl rfl rfl

private theorem cost_2462_535_join1_6 : P1_7_1_3.blockEstimate 2462 535 2071 512 = 274843188983 :=
  @P1_7_1_3.block_append 2462 535 2071 2327 256 256 512 152315694592 122527494391 274843188983 cost_2462_535_join0_12 cost_2462_535_join0_14 rfl rfl rfl

private theorem cost_2462_535_join1_8 : P1_7_1_3.blockEstimate 2462 535 2583 512 = 125741717485 :=
  @P1_7_1_3.block_append 2462 535 2583 2839 256 256 512 82122377123 43619340362 125741717485 cost_2462_535_join0_16 cost_2462_535_join0_18 rfl rfl rfl

private theorem cost_2462_535_join1_10 : P1_7_1_3.blockEstimate 2462 535 3095 437 = 15864053975 :=
  @P1_7_1_3.block_append 2462 535 3095 3351 256 181 437 14659671648 1204382327 15864053975 cost_2462_535_join0_20 cost_2462_535_join0_22 rfl rfl rfl

private theorem cost_2462_535_join2_0 : P1_7_1_3.blockEstimate 2462 535 535 1024 = 273760108590 :=
  @P1_7_1_3.block_append 2462 535 535 1047 512 512 1024 46773671040 226986437550 273760108590 cost_2462_535_join1_0 cost_2462_535_join1_2 rfl rfl rfl

private theorem cost_2462_535_join2_2 : P1_7_1_3.blockEstimate 2462 535 1559 1024 = 597582699255 :=
  @P1_7_1_3.block_append 2462 535 1559 2071 512 512 1024 322739510272 274843188983 597582699255 cost_2462_535_join1_4 cost_2462_535_join1_6 rfl rfl rfl

private theorem cost_2462_535_join2_4 : P1_7_1_3.blockEstimate 2462 535 2583 949 = 141605771460 :=
  @P1_7_1_3.block_append 2462 535 2583 3095 512 437 949 125741717485 15864053975 141605771460 cost_2462_535_join1_8 cost_2462_535_join1_10 rfl rfl rfl

private theorem cost_2462_535_join3_0 : P1_7_1_3.blockEstimate 2462 535 535 2048 = 871342807845 :=
  @P1_7_1_3.block_append 2462 535 535 1559 1024 1024 2048 273760108590 597582699255 871342807845 cost_2462_535_join2_0 cost_2462_535_join2_2 rfl rfl rfl

private theorem cost_2462_535_join4_0 : P1_7_1_3.blockEstimate 2462 535 535 2997 = 1012948579305 :=
  @P1_7_1_3.block_append 2462 535 535 2583 2048 949 2997 871342807845 141605771460 1012948579305 cost_2462_535_join3_0 cost_2462_535_join2_4 rfl rfl rfl

private theorem cost_2462_535_total : P1_7_1_3.momentEstimate 2462 535 = 1012948579305 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2462 + 535 = 2997 by decide]
  exact cost_2462_535_join4_0

theorem moment2462_535 : P1_7_1.groupedPoleMoment 2462 535 ≤ 1012948579305 :=
  (P1_7_1_3.grouped_bound 2462 535).trans_eq cost_2462_535_total
private theorem cost_2462_548_block0 : P1_7_1_3.blockEstimate 2462 548 548 128 = 846728480 := by decide +kernel

private theorem cost_2462_548_block1 : P1_7_1_3.blockEstimate 2462 548 676 128 = 5577350432 := by decide +kernel

private theorem cost_2462_548_block2 : P1_7_1_3.blockEstimate 2462 548 804 128 = 14260055328 := by decide +kernel

private theorem cost_2462_548_block3 : P1_7_1_3.blockEstimate 2462 548 932 128 = 26089536800 := by decide +kernel

private theorem cost_2462_548_block4 : P1_7_1_3.blockEstimate 2462 548 1060 128 = 40021005327 := by decide +kernel

private theorem cost_2462_548_block5 : P1_7_1_3.blockEstimate 2462 548 1188 128 = 53102371968 := by decide +kernel

private theorem cost_2462_548_block6 : P1_7_1_3.blockEstimate 2462 548 1316 128 = 63896151168 := by decide +kernel

private theorem cost_2462_548_block7 : P1_7_1_3.blockEstimate 2462 548 1444 128 = 72387257472 := by decide +kernel

private theorem cost_2462_548_block8 : P1_7_1_3.blockEstimate 2462 548 1572 128 = 78575690880 := by decide +kernel

private theorem cost_2462_548_block9 : P1_7_1_3.blockEstimate 2462 548 1700 128 = 82461451392 := by decide +kernel

private theorem cost_2462_548_block10 : P1_7_1_3.blockEstimate 2462 548 1828 128 = 84044539008 := by decide +kernel

private theorem cost_2462_548_block11 : P1_7_1_3.blockEstimate 2462 548 1956 128 = 83324953728 := by decide +kernel

private theorem cost_2462_548_block12 : P1_7_1_3.blockEstimate 2462 548 2084 128 = 80302695552 := by decide +kernel

private theorem cost_2462_548_block13 : P1_7_1_3.blockEstimate 2462 548 2212 128 = 74977764480 := by decide +kernel

private theorem cost_2462_548_block14 : P1_7_1_3.blockEstimate 2462 548 2340 128 = 67350190704 := by decide +kernel

private theorem cost_2462_548_block15 : P1_7_1_3.blockEstimate 2462 548 2468 128 = 57726868781 := by decide +kernel

private theorem cost_2462_548_block16 : P1_7_1_3.blockEstimate 2462 548 2596 128 = 47369039473 := by decide +kernel

private theorem cost_2462_548_block17 : P1_7_1_3.blockEstimate 2462 548 2724 128 = 37014698579 := by decide +kernel

private theorem cost_2462_548_block18 : P1_7_1_3.blockEstimate 2462 548 2852 128 = 27171562695 := by decide +kernel

private theorem cost_2462_548_block19 : P1_7_1_3.blockEstimate 2462 548 2980 128 = 18268755061 := by decide +kernel

private theorem cost_2462_548_block20 : P1_7_1_3.blockEstimate 2462 548 3108 128 = 10748643632 := by decide +kernel

private theorem cost_2462_548_block21 : P1_7_1_3.blockEstimate 2462 548 3236 128 = 5045124400 := by decide +kernel

private theorem cost_2462_548_block22 : P1_7_1_3.blockEstimate 2462 548 3364 128 = 1414443312 := by decide +kernel

private theorem cost_2462_548_block23 : P1_7_1_3.blockEstimate 2462 548 3492 66 = 62298353 := by decide +kernel

private theorem cost_2462_548_join0_0 : P1_7_1_3.blockEstimate 2462 548 548 256 = 6424078912 :=
  @P1_7_1_3.block_append 2462 548 548 676 128 128 256 846728480 5577350432 6424078912 cost_2462_548_block0 cost_2462_548_block1 rfl rfl rfl

private theorem cost_2462_548_join0_2 : P1_7_1_3.blockEstimate 2462 548 804 256 = 40349592128 :=
  @P1_7_1_3.block_append 2462 548 804 932 128 128 256 14260055328 26089536800 40349592128 cost_2462_548_block2 cost_2462_548_block3 rfl rfl rfl

private theorem cost_2462_548_join0_4 : P1_7_1_3.blockEstimate 2462 548 1060 256 = 93123377295 :=
  @P1_7_1_3.block_append 2462 548 1060 1188 128 128 256 40021005327 53102371968 93123377295 cost_2462_548_block4 cost_2462_548_block5 rfl rfl rfl

private theorem cost_2462_548_join0_6 : P1_7_1_3.blockEstimate 2462 548 1316 256 = 136283408640 :=
  @P1_7_1_3.block_append 2462 548 1316 1444 128 128 256 63896151168 72387257472 136283408640 cost_2462_548_block6 cost_2462_548_block7 rfl rfl rfl

private theorem cost_2462_548_join0_8 : P1_7_1_3.blockEstimate 2462 548 1572 256 = 161037142272 :=
  @P1_7_1_3.block_append 2462 548 1572 1700 128 128 256 78575690880 82461451392 161037142272 cost_2462_548_block8 cost_2462_548_block9 rfl rfl rfl

private theorem cost_2462_548_join0_10 : P1_7_1_3.blockEstimate 2462 548 1828 256 = 167369492736 :=
  @P1_7_1_3.block_append 2462 548 1828 1956 128 128 256 84044539008 83324953728 167369492736 cost_2462_548_block10 cost_2462_548_block11 rfl rfl rfl

private theorem cost_2462_548_join0_12 : P1_7_1_3.blockEstimate 2462 548 2084 256 = 155280460032 :=
  @P1_7_1_3.block_append 2462 548 2084 2212 128 128 256 80302695552 74977764480 155280460032 cost_2462_548_block12 cost_2462_548_block13 rfl rfl rfl

private theorem cost_2462_548_join0_14 : P1_7_1_3.blockEstimate 2462 548 2340 256 = 125077059485 :=
  @P1_7_1_3.block_append 2462 548 2340 2468 128 128 256 67350190704 57726868781 125077059485 cost_2462_548_block14 cost_2462_548_block15 rfl rfl rfl

private theorem cost_2462_548_join0_16 : P1_7_1_3.blockEstimate 2462 548 2596 256 = 84383738052 :=
  @P1_7_1_3.block_append 2462 548 2596 2724 128 128 256 47369039473 37014698579 84383738052 cost_2462_548_block16 cost_2462_548_block17 rfl rfl rfl

private theorem cost_2462_548_join0_18 : P1_7_1_3.blockEstimate 2462 548 2852 256 = 45440317756 :=
  @P1_7_1_3.block_append 2462 548 2852 2980 128 128 256 27171562695 18268755061 45440317756 cost_2462_548_block18 cost_2462_548_block19 rfl rfl rfl

private theorem cost_2462_548_join0_20 : P1_7_1_3.blockEstimate 2462 548 3108 256 = 15793768032 :=
  @P1_7_1_3.block_append 2462 548 3108 3236 128 128 256 10748643632 5045124400 15793768032 cost_2462_548_block20 cost_2462_548_block21 rfl rfl rfl

private theorem cost_2462_548_join0_22 : P1_7_1_3.blockEstimate 2462 548 3364 194 = 1476741665 :=
  @P1_7_1_3.block_append 2462 548 3364 3492 128 66 194 1414443312 62298353 1476741665 cost_2462_548_block22 cost_2462_548_block23 rfl rfl rfl

private theorem cost_2462_548_join1_0 : P1_7_1_3.blockEstimate 2462 548 548 512 = 46773671040 :=
  @P1_7_1_3.block_append 2462 548 548 804 256 256 512 6424078912 40349592128 46773671040 cost_2462_548_join0_0 cost_2462_548_join0_2 rfl rfl rfl

private theorem cost_2462_548_join1_2 : P1_7_1_3.blockEstimate 2462 548 1060 512 = 229406785935 :=
  @P1_7_1_3.block_append 2462 548 1060 1316 256 256 512 93123377295 136283408640 229406785935 cost_2462_548_join0_4 cost_2462_548_join0_6 rfl rfl rfl

private theorem cost_2462_548_join1_4 : P1_7_1_3.blockEstimate 2462 548 1572 512 = 328406635008 :=
  @P1_7_1_3.block_append 2462 548 1572 1828 256 256 512 161037142272 167369492736 328406635008 cost_2462_548_join0_8 cost_2462_548_join0_10 rfl rfl rfl

private theorem cost_2462_548_join1_6 : P1_7_1_3.blockEstimate 2462 548 2084 512 = 280357519517 :=
  @P1_7_1_3.block_append 2462 548 2084 2340 256 256 512 155280460032 125077059485 280357519517 cost_2462_548_join0_12 cost_2462_548_join0_14 rfl rfl rfl

private theorem cost_2462_548_join1_8 : P1_7_1_3.blockEstimate 2462 548 2596 512 = 129824055808 :=
  @P1_7_1_3.block_append 2462 548 2596 2852 256 256 512 84383738052 45440317756 129824055808 cost_2462_548_join0_16 cost_2462_548_join0_18 rfl rfl rfl

private theorem cost_2462_548_join1_10 : P1_7_1_3.blockEstimate 2462 548 3108 450 = 17270509697 :=
  @P1_7_1_3.block_append 2462 548 3108 3364 256 194 450 15793768032 1476741665 17270509697 cost_2462_548_join0_20 cost_2462_548_join0_22 rfl rfl rfl

private theorem cost_2462_548_join2_0 : P1_7_1_3.blockEstimate 2462 548 548 1024 = 276180456975 :=
  @P1_7_1_3.block_append 2462 548 548 1060 512 512 1024 46773671040 229406785935 276180456975 cost_2462_548_join1_0 cost_2462_548_join1_2 rfl rfl rfl

private theorem cost_2462_548_join2_2 : P1_7_1_3.blockEstimate 2462 548 1572 1024 = 608764154525 :=
  @P1_7_1_3.block_append 2462 548 1572 2084 512 512 1024 328406635008 280357519517 608764154525 cost_2462_548_join1_4 cost_2462_548_join1_6 rfl rfl rfl

private theorem cost_2462_548_join2_4 : P1_7_1_3.blockEstimate 2462 548 2596 962 = 147094565505 :=
  @P1_7_1_3.block_append 2462 548 2596 3108 512 450 962 129824055808 17270509697 147094565505 cost_2462_548_join1_8 cost_2462_548_join1_10 rfl rfl rfl

private theorem cost_2462_548_join3_0 : P1_7_1_3.blockEstimate 2462 548 548 2048 = 884944611500 :=
  @P1_7_1_3.block_append 2462 548 548 1572 1024 1024 2048 276180456975 608764154525 884944611500 cost_2462_548_join2_0 cost_2462_548_join2_2 rfl rfl rfl

private theorem cost_2462_548_join4_0 : P1_7_1_3.blockEstimate 2462 548 548 3010 = 1032039177005 :=
  @P1_7_1_3.block_append 2462 548 548 2596 2048 962 3010 884944611500 147094565505 1032039177005 cost_2462_548_join3_0 cost_2462_548_join2_4 rfl rfl rfl

private theorem cost_2462_548_total : P1_7_1_3.momentEstimate 2462 548 = 1032039177005 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2462 + 548 = 3010 by decide]
  exact cost_2462_548_join4_0

theorem moment2462_548 : P1_7_1.groupedPoleMoment 2462 548 ≤ 1032039177005 :=
  (P1_7_1_3.grouped_bound 2462 548).trans_eq cost_2462_548_total
private theorem cost_2462_550_block0 : P1_7_1_3.blockEstimate 2462 550 550 128 = 846728480 := by decide +kernel

private theorem cost_2462_550_block1 : P1_7_1_3.blockEstimate 2462 550 678 128 = 5577350432 := by decide +kernel

private theorem cost_2462_550_block2 : P1_7_1_3.blockEstimate 2462 550 806 128 = 14260055328 := by decide +kernel

private theorem cost_2462_550_block3 : P1_7_1_3.blockEstimate 2462 550 934 128 = 26089536800 := by decide +kernel

private theorem cost_2462_550_block4 : P1_7_1_3.blockEstimate 2462 550 1062 128 = 40036348655 := by decide +kernel

private theorem cost_2462_550_block5 : P1_7_1_3.blockEstimate 2462 550 1190 128 = 53171799744 := by decide +kernel

private theorem cost_2462_550_block6 : P1_7_1_3.blockEstimate 2462 550 1318 128 = 64013928128 := by decide +kernel

private theorem cost_2462_550_block7 : P1_7_1_3.blockEstimate 2462 550 1446 128 = 72544995008 := by decide +kernel

private theorem cost_2462_550_block8 : P1_7_1_3.blockEstimate 2462 550 1574 128 = 78765000384 := by decide +kernel

private theorem cost_2462_550_block9 : P1_7_1_3.blockEstimate 2462 550 1702 128 = 82673944256 := by decide +kernel

private theorem cost_2462_550_block10 : P1_7_1_3.blockEstimate 2462 550 1830 128 = 84271826624 := by decide +kernel

private theorem cost_2462_550_block11 : P1_7_1_3.blockEstimate 2462 550 1958 128 = 83558647488 := by decide +kernel

private theorem cost_2462_550_block12 : P1_7_1_3.blockEstimate 2462 550 2086 128 = 80534406848 := by decide +kernel

private theorem cost_2462_550_block13 : P1_7_1_3.blockEstimate 2462 550 2214 128 = 75199104704 := by decide +kernel

private theorem cost_2462_550_block14 : P1_7_1_3.blockEstimate 2462 550 2342 128 = 67552809586 := by decide +kernel

private theorem cost_2462_550_block15 : P1_7_1_3.blockEstimate 2462 550 2470 128 = 57915779636 := by decide +kernel

private theorem cost_2462_550_block16 : P1_7_1_3.blockEstimate 2462 550 2598 128 = 47549880715 := by decide +kernel

private theorem cost_2462_550_block17 : P1_7_1_3.blockEstimate 2462 550 2726 128 = 37183411443 := by decide +kernel

private theorem cost_2462_550_block18 : P1_7_1_3.blockEstimate 2462 550 2854 128 = 27323707503 := by decide +kernel

private theorem cost_2462_550_block19 : P1_7_1_3.blockEstimate 2462 550 2982 128 = 18399405619 := by decide +kernel

private theorem cost_2462_550_block20 : P1_7_1_3.blockEstimate 2462 550 3110 128 = 10852866592 := by decide +kernel

private theorem cost_2462_550_block21 : P1_7_1_3.blockEstimate 2462 550 3238 128 = 5118956064 := by decide +kernel

private theorem cost_2462_550_block22 : P1_7_1_3.blockEstimate 2462 550 3366 128 = 1453951520 := by decide +kernel

private theorem cost_2462_550_block23 : P1_7_1_3.blockEstimate 2462 550 3494 68 = 67976965 := by decide +kernel

private theorem cost_2462_550_join0_0 : P1_7_1_3.blockEstimate 2462 550 550 256 = 6424078912 :=
  @P1_7_1_3.block_append 2462 550 550 678 128 128 256 846728480 5577350432 6424078912 cost_2462_550_block0 cost_2462_550_block1 rfl rfl rfl

private theorem cost_2462_550_join0_2 : P1_7_1_3.blockEstimate 2462 550 806 256 = 40349592128 :=
  @P1_7_1_3.block_append 2462 550 806 934 128 128 256 14260055328 26089536800 40349592128 cost_2462_550_block2 cost_2462_550_block3 rfl rfl rfl

private theorem cost_2462_550_join0_4 : P1_7_1_3.blockEstimate 2462 550 1062 256 = 93208148399 :=
  @P1_7_1_3.block_append 2462 550 1062 1190 128 128 256 40036348655 53171799744 93208148399 cost_2462_550_block4 cost_2462_550_block5 rfl rfl rfl

private theorem cost_2462_550_join0_6 : P1_7_1_3.blockEstimate 2462 550 1318 256 = 136558923136 :=
  @P1_7_1_3.block_append 2462 550 1318 1446 128 128 256 64013928128 72544995008 136558923136 cost_2462_550_block6 cost_2462_550_block7 rfl rfl rfl

private theorem cost_2462_550_join0_8 : P1_7_1_3.blockEstimate 2462 550 1574 256 = 161438944640 :=
  @P1_7_1_3.block_append 2462 550 1574 1702 128 128 256 78765000384 82673944256 161438944640 cost_2462_550_block8 cost_2462_550_block9 rfl rfl rfl

private theorem cost_2462_550_join0_10 : P1_7_1_3.blockEstimate 2462 550 1830 256 = 167830474112 :=
  @P1_7_1_3.block_append 2462 550 1830 1958 128 128 256 84271826624 83558647488 167830474112 cost_2462_550_block10 cost_2462_550_block11 rfl rfl rfl

private theorem cost_2462_550_join0_12 : P1_7_1_3.blockEstimate 2462 550 2086 256 = 155733511552 :=
  @P1_7_1_3.block_append 2462 550 2086 2214 128 128 256 80534406848 75199104704 155733511552 cost_2462_550_block12 cost_2462_550_block13 rfl rfl rfl

private theorem cost_2462_550_join0_14 : P1_7_1_3.blockEstimate 2462 550 2342 256 = 125468589222 :=
  @P1_7_1_3.block_append 2462 550 2342 2470 128 128 256 67552809586 57915779636 125468589222 cost_2462_550_block14 cost_2462_550_block15 rfl rfl rfl

private theorem cost_2462_550_join0_16 : P1_7_1_3.blockEstimate 2462 550 2598 256 = 84733292158 :=
  @P1_7_1_3.block_append 2462 550 2598 2726 128 128 256 47549880715 37183411443 84733292158 cost_2462_550_block16 cost_2462_550_block17 rfl rfl rfl

private theorem cost_2462_550_join0_18 : P1_7_1_3.blockEstimate 2462 550 2854 256 = 45723113122 :=
  @P1_7_1_3.block_append 2462 550 2854 2982 128 128 256 27323707503 18399405619 45723113122 cost_2462_550_block18 cost_2462_550_block19 rfl rfl rfl

private theorem cost_2462_550_join0_20 : P1_7_1_3.blockEstimate 2462 550 3110 256 = 15971822656 :=
  @P1_7_1_3.block_append 2462 550 3110 3238 128 128 256 10852866592 5118956064 15971822656 cost_2462_550_block20 cost_2462_550_block21 rfl rfl rfl

private theorem cost_2462_550_join0_22 : P1_7_1_3.blockEstimate 2462 550 3366 196 = 1521928485 :=
  @P1_7_1_3.block_append 2462 550 3366 3494 128 68 196 1453951520 67976965 1521928485 cost_2462_550_block22 cost_2462_550_block23 rfl rfl rfl

private theorem cost_2462_550_join1_0 : P1_7_1_3.blockEstimate 2462 550 550 512 = 46773671040 :=
  @P1_7_1_3.block_append 2462 550 550 806 256 256 512 6424078912 40349592128 46773671040 cost_2462_550_join0_0 cost_2462_550_join0_2 rfl rfl rfl

private theorem cost_2462_550_join1_2 : P1_7_1_3.blockEstimate 2462 550 1062 512 = 229767071535 :=
  @P1_7_1_3.block_append 2462 550 1062 1318 256 256 512 93208148399 136558923136 229767071535 cost_2462_550_join0_4 cost_2462_550_join0_6 rfl rfl rfl

private theorem cost_2462_550_join1_4 : P1_7_1_3.blockEstimate 2462 550 1574 512 = 329269418752 :=
  @P1_7_1_3.block_append 2462 550 1574 1830 256 256 512 161438944640 167830474112 329269418752 cost_2462_550_join0_8 cost_2462_550_join0_10 rfl rfl rfl

private theorem cost_2462_550_join1_6 : P1_7_1_3.blockEstimate 2462 550 2086 512 = 281202100774 :=
  @P1_7_1_3.block_append 2462 550 2086 2342 256 256 512 155733511552 125468589222 281202100774 cost_2462_550_join0_12 cost_2462_550_join0_14 rfl rfl rfl

private theorem cost_2462_550_join1_8 : P1_7_1_3.blockEstimate 2462 550 2598 512 = 130456405280 :=
  @P1_7_1_3.block_append 2462 550 2598 2854 256 256 512 84733292158 45723113122 130456405280 cost_2462_550_join0_16 cost_2462_550_join0_18 rfl rfl rfl

private theorem cost_2462_550_join1_10 : P1_7_1_3.blockEstimate 2462 550 3110 452 = 17493751141 :=
  @P1_7_1_3.block_append 2462 550 3110 3366 256 196 452 15971822656 1521928485 17493751141 cost_2462_550_join0_20 cost_2462_550_join0_22 rfl rfl rfl

private theorem cost_2462_550_join2_0 : P1_7_1_3.blockEstimate 2462 550 550 1024 = 276540742575 :=
  @P1_7_1_3.block_append 2462 550 550 1062 512 512 1024 46773671040 229767071535 276540742575 cost_2462_550_join1_0 cost_2462_550_join1_2 rfl rfl rfl

private theorem cost_2462_550_join2_2 : P1_7_1_3.blockEstimate 2462 550 1574 1024 = 610471519526 :=
  @P1_7_1_3.block_append 2462 550 1574 2086 512 512 1024 329269418752 281202100774 610471519526 cost_2462_550_join1_4 cost_2462_550_join1_6 rfl rfl rfl

private theorem cost_2462_550_join2_4 : P1_7_1_3.blockEstimate 2462 550 2598 964 = 147950156421 :=
  @P1_7_1_3.block_append 2462 550 2598 3110 512 452 964 130456405280 17493751141 147950156421 cost_2462_550_join1_8 cost_2462_550_join1_10 rfl rfl rfl

private theorem cost_2462_550_join3_0 : P1_7_1_3.blockEstimate 2462 550 550 2048 = 887012262101 :=
  @P1_7_1_3.block_append 2462 550 550 1574 1024 1024 2048 276540742575 610471519526 887012262101 cost_2462_550_join2_0 cost_2462_550_join2_2 rfl rfl rfl

private theorem cost_2462_550_join4_0 : P1_7_1_3.blockEstimate 2462 550 550 3012 = 1034962418522 :=
  @P1_7_1_3.block_append 2462 550 550 2598 2048 964 3012 887012262101 147950156421 1034962418522 cost_2462_550_join3_0 cost_2462_550_join2_4 rfl rfl rfl

private theorem cost_2462_550_total : P1_7_1_3.momentEstimate 2462 550 = 1034962418522 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2462 + 550 = 3012 by decide]
  exact cost_2462_550_join4_0

theorem moment2462_550 : P1_7_1.groupedPoleMoment 2462 550 ≤ 1034962418522 :=
  (P1_7_1_3.grouped_bound 2462 550).trans_eq cost_2462_550_total
private theorem cost_2463_535_block0 : P1_7_1_3.blockEstimate 2463 535 535 128 = 847086240 := by decide +kernel

private theorem cost_2463_535_block1 : P1_7_1_3.blockEstimate 2463 535 663 128 = 5579821728 := by decide +kernel

private theorem cost_2463_535_block2 : P1_7_1_3.blockEstimate 2463 535 791 128 = 14266737312 := by decide +kernel

private theorem cost_2463_535_block3 : P1_7_1_3.blockEstimate 2463 535 919 128 = 26102526624 := by decide +kernel

private theorem cost_2463_535_block4 : P1_7_1_3.blockEstimate 2463 535 1047 128 = 39925029526 := by decide +kernel

private theorem cost_2463_535_block5 : P1_7_1_3.blockEstimate 2463 535 1175 128 = 52659127040 := by decide +kernel

private theorem cost_2463_535_block6 : P1_7_1_3.blockEstimate 2463 535 1303 128 = 63149015808 := by decide +kernel

private theorem cost_2463_535_block7 : P1_7_1_3.blockEstimate 2463 535 1431 128 = 71390757632 := by decide +kernel

private theorem cost_2463_535_block8 : P1_7_1_3.blockEstimate 2463 535 1559 128 = 77384352512 := by decide +kernel

private theorem cost_2463_535_block9 : P1_7_1_3.blockEstimate 2463 535 1687 128 = 81129800448 := by decide +kernel

private theorem cost_2463_535_block10 : P1_7_1_3.blockEstimate 2463 535 1815 128 = 82627101440 := by decide +kernel

private theorem cost_2463_535_block11 : P1_7_1_3.blockEstimate 2463 535 1943 128 = 81876255488 := by decide +kernel

private theorem cost_2463_535_block12 : P1_7_1_3.blockEstimate 2463 535 2071 128 = 78877262592 := by decide +kernel

private theorem cost_2463_535_block13 : P1_7_1_3.blockEstimate 2463 535 2199 128 = 73630122752 := by decide +kernel

private theorem cost_2463_535_block14 : P1_7_1_3.blockEstimate 2463 535 2327 128 = 66134835968 := by decide +kernel

private theorem cost_2463_535_block15 : P1_7_1_3.blockEstimate 2463 535 2455 128 = 56613877615 := by decide +kernel

private theorem cost_2463_535_block16 : P1_7_1_3.blockEstimate 2463 535 2583 128 = 46304437711 := by decide +kernel

private theorem cost_2463_535_block17 : P1_7_1_3.blockEstimate 2463 535 2711 128 = 36021572692 := by decide +kernel

private theorem cost_2463_535_block18 : P1_7_1_3.blockEstimate 2463 535 2839 128 = 26275969889 := by decide +kernel

private theorem cost_2463_535_block19 : P1_7_1_3.blockEstimate 2463 535 2967 128 = 17500782559 := by decide +kernel

private theorem cost_2463_535_block20 : P1_7_1_3.blockEstimate 2463 535 3095 128 = 10137232208 := by decide +kernel

private theorem cost_2463_535_block21 : P1_7_1_3.blockEstimate 2463 535 3223 128 = 4614799184 := by decide +kernel

private theorem cost_2463_535_block22 : P1_7_1_3.blockEstimate 2463 535 3351 128 = 1189845840 := by decide +kernel

private theorem cost_2463_535_block23 : P1_7_1_3.blockEstimate 2463 535 3479 54 = 34717193 := by decide +kernel

private theorem cost_2463_535_join0_0 : P1_7_1_3.blockEstimate 2463 535 535 256 = 6426907968 :=
  @P1_7_1_3.block_append 2463 535 535 663 128 128 256 847086240 5579821728 6426907968 cost_2463_535_block0 cost_2463_535_block1 rfl rfl rfl

private theorem cost_2463_535_join0_2 : P1_7_1_3.blockEstimate 2463 535 791 256 = 40369263936 :=
  @P1_7_1_3.block_append 2463 535 791 919 128 128 256 14266737312 26102526624 40369263936 cost_2463_535_block2 cost_2463_535_block3 rfl rfl rfl

private theorem cost_2463_535_join0_4 : P1_7_1_3.blockEstimate 2463 535 1047 256 = 92584156566 :=
  @P1_7_1_3.block_append 2463 535 1047 1175 128 128 256 39925029526 52659127040 92584156566 cost_2463_535_block4 cost_2463_535_block5 rfl rfl rfl

private theorem cost_2463_535_join0_6 : P1_7_1_3.blockEstimate 2463 535 1303 256 = 134539773440 :=
  @P1_7_1_3.block_append 2463 535 1303 1431 128 128 256 63149015808 71390757632 134539773440 cost_2463_535_block6 cost_2463_535_block7 rfl rfl rfl

private theorem cost_2463_535_join0_8 : P1_7_1_3.blockEstimate 2463 535 1559 256 = 158514152960 :=
  @P1_7_1_3.block_append 2463 535 1559 1687 128 128 256 77384352512 81129800448 158514152960 cost_2463_535_block8 cost_2463_535_block9 rfl rfl rfl

private theorem cost_2463_535_join0_10 : P1_7_1_3.blockEstimate 2463 535 1815 256 = 164503356928 :=
  @P1_7_1_3.block_append 2463 535 1815 1943 128 128 256 82627101440 81876255488 164503356928 cost_2463_535_block10 cost_2463_535_block11 rfl rfl rfl

private theorem cost_2463_535_join0_12 : P1_7_1_3.blockEstimate 2463 535 2071 256 = 152507385344 :=
  @P1_7_1_3.block_append 2463 535 2071 2199 128 128 256 78877262592 73630122752 152507385344 cost_2463_535_block12 cost_2463_535_block13 rfl rfl rfl

private theorem cost_2463_535_join0_14 : P1_7_1_3.blockEstimate 2463 535 2327 256 = 122748713583 :=
  @P1_7_1_3.block_append 2463 535 2327 2455 128 128 256 66134835968 56613877615 122748713583 cost_2463_535_block14 cost_2463_535_block15 rfl rfl rfl

private theorem cost_2463_535_join0_16 : P1_7_1_3.blockEstimate 2463 535 2583 256 = 82326010403 :=
  @P1_7_1_3.block_append 2463 535 2583 2711 128 128 256 46304437711 36021572692 82326010403 cost_2463_535_block16 cost_2463_535_block17 rfl rfl rfl

private theorem cost_2463_535_join0_18 : P1_7_1_3.blockEstimate 2463 535 2839 256 = 43776752448 :=
  @P1_7_1_3.block_append 2463 535 2839 2967 128 128 256 26275969889 17500782559 43776752448 cost_2463_535_block18 cost_2463_535_block19 rfl rfl rfl

private theorem cost_2463_535_join0_20 : P1_7_1_3.blockEstimate 2463 535 3095 256 = 14752031392 :=
  @P1_7_1_3.block_append 2463 535 3095 3223 128 128 256 10137232208 4614799184 14752031392 cost_2463_535_block20 cost_2463_535_block21 rfl rfl rfl

private theorem cost_2463_535_join0_22 : P1_7_1_3.blockEstimate 2463 535 3351 182 = 1224563033 :=
  @P1_7_1_3.block_append 2463 535 3351 3479 128 54 182 1189845840 34717193 1224563033 cost_2463_535_block22 cost_2463_535_block23 rfl rfl rfl

private theorem cost_2463_535_join1_0 : P1_7_1_3.blockEstimate 2463 535 535 512 = 46796171904 :=
  @P1_7_1_3.block_append 2463 535 535 791 256 256 512 6426907968 40369263936 46796171904 cost_2463_535_join0_0 cost_2463_535_join0_2 rfl rfl rfl

private theorem cost_2463_535_join1_2 : P1_7_1_3.blockEstimate 2463 535 1047 512 = 227123930006 :=
  @P1_7_1_3.block_append 2463 535 1047 1303 256 256 512 92584156566 134539773440 227123930006 cost_2463_535_join0_4 cost_2463_535_join0_6 rfl rfl rfl

private theorem cost_2463_535_join1_4 : P1_7_1_3.blockEstimate 2463 535 1559 512 = 323017509888 :=
  @P1_7_1_3.block_append 2463 535 1559 1815 256 256 512 158514152960 164503356928 323017509888 cost_2463_535_join0_8 cost_2463_535_join0_10 rfl rfl rfl

private theorem cost_2463_535_join1_6 : P1_7_1_3.blockEstimate 2463 535 2071 512 = 275256098927 :=
  @P1_7_1_3.block_append 2463 535 2071 2327 256 256 512 152507385344 122748713583 275256098927 cost_2463_535_join0_12 cost_2463_535_join0_14 rfl rfl rfl

private theorem cost_2463_535_join1_8 : P1_7_1_3.blockEstimate 2463 535 2583 512 = 126102762851 :=
  @P1_7_1_3.block_append 2463 535 2583 2839 256 256 512 82326010403 43776752448 126102762851 cost_2463_535_join0_16 cost_2463_535_join0_18 rfl rfl rfl

private theorem cost_2463_535_join1_10 : P1_7_1_3.blockEstimate 2463 535 3095 438 = 15976594425 :=
  @P1_7_1_3.block_append 2463 535 3095 3351 256 182 438 14752031392 1224563033 15976594425 cost_2463_535_join0_20 cost_2463_535_join0_22 rfl rfl rfl

private theorem cost_2463_535_join2_0 : P1_7_1_3.blockEstimate 2463 535 535 1024 = 273920101910 :=
  @P1_7_1_3.block_append 2463 535 535 1047 512 512 1024 46796171904 227123930006 273920101910 cost_2463_535_join1_0 cost_2463_535_join1_2 rfl rfl rfl

private theorem cost_2463_535_join2_2 : P1_7_1_3.blockEstimate 2463 535 1559 1024 = 598273608815 :=
  @P1_7_1_3.block_append 2463 535 1559 2071 512 512 1024 323017509888 275256098927 598273608815 cost_2463_535_join1_4 cost_2463_535_join1_6 rfl rfl rfl

private theorem cost_2463_535_join2_4 : P1_7_1_3.blockEstimate 2463 535 2583 950 = 142079357276 :=
  @P1_7_1_3.block_append 2463 535 2583 3095 512 438 950 126102762851 15976594425 142079357276 cost_2463_535_join1_8 cost_2463_535_join1_10 rfl rfl rfl

private theorem cost_2463_535_join3_0 : P1_7_1_3.blockEstimate 2463 535 535 2048 = 872193710725 :=
  @P1_7_1_3.block_append 2463 535 535 1559 1024 1024 2048 273920101910 598273608815 872193710725 cost_2463_535_join2_0 cost_2463_535_join2_2 rfl rfl rfl

private theorem cost_2463_535_join4_0 : P1_7_1_3.blockEstimate 2463 535 535 2998 = 1014273068001 :=
  @P1_7_1_3.block_append 2463 535 535 2583 2048 950 2998 872193710725 142079357276 1014273068001 cost_2463_535_join3_0 cost_2463_535_join2_4 rfl rfl rfl

private theorem cost_2463_535_total : P1_7_1_3.momentEstimate 2463 535 = 1014273068001 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2463 + 535 = 2998 by decide]
  exact cost_2463_535_join4_0

theorem moment2463_535 : P1_7_1.groupedPoleMoment 2463 535 ≤ 1014273068001 :=
  (P1_7_1_3.grouped_bound 2463 535).trans_eq cost_2463_535_total

end Research6966.HelperRescueCatalogue

end Merged6967_Near6967RescueMoment18

section Merged6967_Near6967RescueMoment19
set_option Elab.async false


set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem cost_2463_546_block0 : P1_7_1_3.blockEstimate 2463 546 546 128 = 847086240 := by decide +kernel

private theorem cost_2463_546_block1 : P1_7_1_3.blockEstimate 2463 546 674 128 = 5579821728 := by decide +kernel

private theorem cost_2463_546_block2 : P1_7_1_3.blockEstimate 2463 546 802 128 = 14266737312 := by decide +kernel

private theorem cost_2463_546_block3 : P1_7_1_3.blockEstimate 2463 546 930 128 = 26102526624 := by decide +kernel

private theorem cost_2463_546_block4 : P1_7_1_3.blockEstimate 2463 546 1058 128 = 40026230791 := by decide +kernel

private theorem cost_2463_546_block5 : P1_7_1_3.blockEstimate 2463 546 1186 128 = 53062255744 := by decide +kernel

private theorem cost_2463_546_block6 : P1_7_1_3.blockEstimate 2463 546 1314 128 = 63816713344 := by decide +kernel

private theorem cost_2463_546_block7 : P1_7_1_3.blockEstimate 2463 546 1442 128 = 72276886656 := by decide +kernel

private theorem cost_2463_546_block8 : P1_7_1_3.blockEstimate 2463 546 1570 128 = 78442775680 := by decide +kernel

private theorem cost_2463_546_block9 : P1_7_1_3.blockEstimate 2463 546 1698 128 = 82314380416 := by decide +kernel

private theorem cost_2463_546_block10 : P1_7_1_3.blockEstimate 2463 546 1826 128 = 83891700864 := by decide +kernel

private theorem cost_2463_546_block11 : P1_7_1_3.blockEstimate 2463 546 1954 128 = 83174737024 := by decide +kernel

private theorem cost_2463_546_block12 : P1_7_1_3.blockEstimate 2463 546 2082 128 = 80163488896 := by decide +kernel

private theorem cost_2463_546_block13 : P1_7_1_3.blockEstimate 2463 546 2210 128 = 74857956480 := by decide +kernel

private theorem cost_2463_546_block14 : P1_7_1_3.blockEstimate 2463 546 2338 128 = 67258143898 := by decide +kernel

private theorem cost_2463_546_block15 : P1_7_1_3.blockEstimate 2463 546 2466 128 = 57651286201 := by decide +kernel

private theorem cost_2463_546_block16 : P1_7_1_3.blockEstimate 2463 546 2594 128 = 47295780234 := by decide +kernel

private theorem cost_2463_546_block17 : P1_7_1_3.blockEstimate 2463 546 2722 128 = 36944709822 := by decide +kernel

private theorem cost_2463_546_block18 : P1_7_1_3.blockEstimate 2463 546 2850 128 = 27106544050 := by decide +kernel

private theorem cost_2463_546_block19 : P1_7_1_3.blockEstimate 2463 546 2978 128 = 18211772078 := by decide +kernel

private theorem cost_2463_546_block20 : P1_7_1_3.blockEstimate 2463 546 3106 128 = 10701522704 := by decide +kernel

private theorem cost_2463_546_block21 : P1_7_1_3.blockEstimate 2463 546 3234 128 = 5010580240 := by decide +kernel

private theorem cost_2463_546_block22 : P1_7_1_3.blockEstimate 2463 546 3362 128 = 1395490576 := by decide +kernel

private theorem cost_2463_546_block23 : P1_7_1_3.blockEstimate 2463 546 3490 65 = 59605927 := by decide +kernel

private theorem cost_2463_546_join0_0 : P1_7_1_3.blockEstimate 2463 546 546 256 = 6426907968 :=
  @P1_7_1_3.block_append 2463 546 546 674 128 128 256 847086240 5579821728 6426907968 cost_2463_546_block0 cost_2463_546_block1 rfl rfl rfl

private theorem cost_2463_546_join0_2 : P1_7_1_3.blockEstimate 2463 546 802 256 = 40369263936 :=
  @P1_7_1_3.block_append 2463 546 802 930 128 128 256 14266737312 26102526624 40369263936 cost_2463_546_block2 cost_2463_546_block3 rfl rfl rfl

private theorem cost_2463_546_join0_4 : P1_7_1_3.blockEstimate 2463 546 1058 256 = 93088486535 :=
  @P1_7_1_3.block_append 2463 546 1058 1186 128 128 256 40026230791 53062255744 93088486535 cost_2463_546_block4 cost_2463_546_block5 rfl rfl rfl

private theorem cost_2463_546_join0_6 : P1_7_1_3.blockEstimate 2463 546 1314 256 = 136093600000 :=
  @P1_7_1_3.block_append 2463 546 1314 1442 128 128 256 63816713344 72276886656 136093600000 cost_2463_546_block6 cost_2463_546_block7 rfl rfl rfl

private theorem cost_2463_546_join0_8 : P1_7_1_3.blockEstimate 2463 546 1570 256 = 160757156096 :=
  @P1_7_1_3.block_append 2463 546 1570 1698 128 128 256 78442775680 82314380416 160757156096 cost_2463_546_block8 cost_2463_546_block9 rfl rfl rfl

private theorem cost_2463_546_join0_10 : P1_7_1_3.blockEstimate 2463 546 1826 256 = 167066437888 :=
  @P1_7_1_3.block_append 2463 546 1826 1954 128 128 256 83891700864 83174737024 167066437888 cost_2463_546_block10 cost_2463_546_block11 rfl rfl rfl

private theorem cost_2463_546_join0_12 : P1_7_1_3.blockEstimate 2463 546 2082 256 = 155021445376 :=
  @P1_7_1_3.block_append 2463 546 2082 2210 128 128 256 80163488896 74857956480 155021445376 cost_2463_546_block12 cost_2463_546_block13 rfl rfl rfl

private theorem cost_2463_546_join0_14 : P1_7_1_3.blockEstimate 2463 546 2338 256 = 124909430099 :=
  @P1_7_1_3.block_append 2463 546 2338 2466 128 128 256 67258143898 57651286201 124909430099 cost_2463_546_block14 cost_2463_546_block15 rfl rfl rfl

private theorem cost_2463_546_join0_16 : P1_7_1_3.blockEstimate 2463 546 2594 256 = 84240490056 :=
  @P1_7_1_3.block_append 2463 546 2594 2722 128 128 256 47295780234 36944709822 84240490056 cost_2463_546_block16 cost_2463_546_block17 rfl rfl rfl

private theorem cost_2463_546_join0_18 : P1_7_1_3.blockEstimate 2463 546 2850 256 = 45318316128 :=
  @P1_7_1_3.block_append 2463 546 2850 2978 128 128 256 27106544050 18211772078 45318316128 cost_2463_546_block18 cost_2463_546_block19 rfl rfl rfl

private theorem cost_2463_546_join0_20 : P1_7_1_3.blockEstimate 2463 546 3106 256 = 15712102944 :=
  @P1_7_1_3.block_append 2463 546 3106 3234 128 128 256 10701522704 5010580240 15712102944 cost_2463_546_block20 cost_2463_546_block21 rfl rfl rfl

private theorem cost_2463_546_join0_22 : P1_7_1_3.blockEstimate 2463 546 3362 193 = 1455096503 :=
  @P1_7_1_3.block_append 2463 546 3362 3490 128 65 193 1395490576 59605927 1455096503 cost_2463_546_block22 cost_2463_546_block23 rfl rfl rfl

private theorem cost_2463_546_join1_0 : P1_7_1_3.blockEstimate 2463 546 546 512 = 46796171904 :=
  @P1_7_1_3.block_append 2463 546 546 802 256 256 512 6426907968 40369263936 46796171904 cost_2463_546_join0_0 cost_2463_546_join0_2 rfl rfl rfl

private theorem cost_2463_546_join1_2 : P1_7_1_3.blockEstimate 2463 546 1058 512 = 229182086535 :=
  @P1_7_1_3.block_append 2463 546 1058 1314 256 256 512 93088486535 136093600000 229182086535 cost_2463_546_join0_4 cost_2463_546_join0_6 rfl rfl rfl

private theorem cost_2463_546_join1_4 : P1_7_1_3.blockEstimate 2463 546 1570 512 = 327823593984 :=
  @P1_7_1_3.block_append 2463 546 1570 1826 256 256 512 160757156096 167066437888 327823593984 cost_2463_546_join0_8 cost_2463_546_join0_10 rfl rfl rfl

private theorem cost_2463_546_join1_6 : P1_7_1_3.blockEstimate 2463 546 2082 512 = 279930875475 :=
  @P1_7_1_3.block_append 2463 546 2082 2338 256 256 512 155021445376 124909430099 279930875475 cost_2463_546_join0_12 cost_2463_546_join0_14 rfl rfl rfl

private theorem cost_2463_546_join1_8 : P1_7_1_3.blockEstimate 2463 546 2594 512 = 129558806184 :=
  @P1_7_1_3.block_append 2463 546 2594 2850 256 256 512 84240490056 45318316128 129558806184 cost_2463_546_join0_16 cost_2463_546_join0_18 rfl rfl rfl

private theorem cost_2463_546_join1_10 : P1_7_1_3.blockEstimate 2463 546 3106 449 = 17167199447 :=
  @P1_7_1_3.block_append 2463 546 3106 3362 256 193 449 15712102944 1455096503 17167199447 cost_2463_546_join0_20 cost_2463_546_join0_22 rfl rfl rfl

private theorem cost_2463_546_join2_0 : P1_7_1_3.blockEstimate 2463 546 546 1024 = 275978258439 :=
  @P1_7_1_3.block_append 2463 546 546 1058 512 512 1024 46796171904 229182086535 275978258439 cost_2463_546_join1_0 cost_2463_546_join1_2 rfl rfl rfl

private theorem cost_2463_546_join2_2 : P1_7_1_3.blockEstimate 2463 546 1570 1024 = 607754469459 :=
  @P1_7_1_3.block_append 2463 546 1570 2082 512 512 1024 327823593984 279930875475 607754469459 cost_2463_546_join1_4 cost_2463_546_join1_6 rfl rfl rfl

private theorem cost_2463_546_join2_4 : P1_7_1_3.blockEstimate 2463 546 2594 961 = 146726005631 :=
  @P1_7_1_3.block_append 2463 546 2594 3106 512 449 961 129558806184 17167199447 146726005631 cost_2463_546_join1_8 cost_2463_546_join1_10 rfl rfl rfl

private theorem cost_2463_546_join3_0 : P1_7_1_3.blockEstimate 2463 546 546 2048 = 883732727898 :=
  @P1_7_1_3.block_append 2463 546 546 1570 1024 1024 2048 275978258439 607754469459 883732727898 cost_2463_546_join2_0 cost_2463_546_join2_2 rfl rfl rfl

private theorem cost_2463_546_join4_0 : P1_7_1_3.blockEstimate 2463 546 546 3009 = 1030458733529 :=
  @P1_7_1_3.block_append 2463 546 546 2594 2048 961 3009 883732727898 146726005631 1030458733529 cost_2463_546_join3_0 cost_2463_546_join2_4 rfl rfl rfl

private theorem cost_2463_546_total : P1_7_1_3.momentEstimate 2463 546 = 1030458733529 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2463 + 546 = 3009 by decide]
  exact cost_2463_546_join4_0

theorem moment2463_546 : P1_7_1.groupedPoleMoment 2463 546 ≤ 1030458733529 :=
  (P1_7_1_3.grouped_bound 2463 546).trans_eq cost_2463_546_total
private theorem cost_2464_524_block0 : P1_7_1_3.blockEstimate 2464 524 524 128 = 847444000 := by decide +kernel

private theorem cost_2464_524_block1 : P1_7_1_3.blockEstimate 2464 524 652 128 = 5582293024 := by decide +kernel

private theorem cost_2464_524_block2 : P1_7_1_3.blockEstimate 2464 524 780 128 = 14273419296 := by decide +kernel

private theorem cost_2464_524_block3 : P1_7_1_3.blockEstimate 2464 524 908 128 = 26115516448 := by decide +kernel

private theorem cost_2464_524_block4 : P1_7_1_3.blockEstimate 2464 524 1036 128 = 39821127157 := by decide +kernel

private theorem cost_2464_524_block5 : P1_7_1_3.blockEstimate 2464 524 1164 128 = 52258483200 := by decide +kernel

private theorem cost_2464_524_block6 : P1_7_1_3.blockEstimate 2464 524 1292 128 = 62494387200 := by decide +kernel

private theorem cost_2464_524_block7 : P1_7_1_3.blockEstimate 2464 524 1420 128 = 70528281600 := by decide +kernel

private theorem cost_2464_524_block8 : P1_7_1_3.blockEstimate 2464 524 1548 128 = 76360166400 := by decide +kernel

private theorem cost_2464_524_block9 : P1_7_1_3.blockEstimate 2464 524 1676 128 = 79990041600 := by decide +kernel

private theorem cost_2464_524_block10 : P1_7_1_3.blockEstimate 2464 524 1804 128 = 81417907200 := by decide +kernel

private theorem cost_2464_524_block11 : P1_7_1_3.blockEstimate 2464 524 1932 128 = 80643763200 := by decide +kernel

private theorem cost_2464_524_block12 : P1_7_1_3.blockEstimate 2464 524 2060 128 = 77667609600 := by decide +kernel

private theorem cost_2464_524_block13 : P1_7_1_3.blockEstimate 2464 524 2188 128 = 72489446400 := by decide +kernel

private theorem cost_2464_524_block14 : P1_7_1_3.blockEstimate 2464 524 2316 128 = 65109273600 := by decide +kernel

private theorem cost_2464_524_block15 : P1_7_1_3.blockEstimate 2464 524 2444 128 = 55690543236 := by decide +kernel

private theorem cost_2464_524_block16 : P1_7_1_3.blockEstimate 2464 524 2572 128 = 45424212243 := by decide +kernel

private theorem cost_2464_524_block17 : P1_7_1_3.blockEstimate 2464 524 2700 128 = 35202523280 := by decide +kernel

private theorem cost_2464_524_block18 : P1_7_1_3.blockEstimate 2464 524 2828 128 = 25539618754 := by decide +kernel

private theorem cost_2464_524_block19 : P1_7_1_3.blockEstimate 2464 524 2956 128 = 16872171343 := by decide +kernel

private theorem cost_2464_524_block20 : P1_7_1_3.blockEstimate 2464 524 3084 128 = 9640384480 := by decide +kernel

private theorem cost_2464_524_block21 : P1_7_1_3.blockEstimate 2464 524 3212 128 = 4270284768 := by decide +kernel

private theorem cost_2464_524_block22 : P1_7_1_3.blockEstimate 2464 524 3340 128 = 1018374112 := by decide +kernel

private theorem cost_2464_524_block23 : P1_7_1_3.blockEstimate 2464 524 3468 44 = 19168545 := by decide +kernel

private theorem cost_2464_524_join0_0 : P1_7_1_3.blockEstimate 2464 524 524 256 = 6429737024 :=
  @P1_7_1_3.block_append 2464 524 524 652 128 128 256 847444000 5582293024 6429737024 cost_2464_524_block0 cost_2464_524_block1 rfl rfl rfl

private theorem cost_2464_524_join0_2 : P1_7_1_3.blockEstimate 2464 524 780 256 = 40388935744 :=
  @P1_7_1_3.block_append 2464 524 780 908 128 128 256 14273419296 26115516448 40388935744 cost_2464_524_block2 cost_2464_524_block3 rfl rfl rfl

private theorem cost_2464_524_join0_4 : P1_7_1_3.blockEstimate 2464 524 1036 256 = 92079610357 :=
  @P1_7_1_3.block_append 2464 524 1036 1164 128 128 256 39821127157 52258483200 92079610357 cost_2464_524_block4 cost_2464_524_block5 rfl rfl rfl

private theorem cost_2464_524_join0_6 : P1_7_1_3.blockEstimate 2464 524 1292 256 = 133022668800 :=
  @P1_7_1_3.block_append 2464 524 1292 1420 128 128 256 62494387200 70528281600 133022668800 cost_2464_524_block6 cost_2464_524_block7 rfl rfl rfl

private theorem cost_2464_524_join0_8 : P1_7_1_3.blockEstimate 2464 524 1548 256 = 156350208000 :=
  @P1_7_1_3.block_append 2464 524 1548 1676 128 128 256 76360166400 79990041600 156350208000 cost_2464_524_block8 cost_2464_524_block9 rfl rfl rfl

private theorem cost_2464_524_join0_10 : P1_7_1_3.blockEstimate 2464 524 1804 256 = 162061670400 :=
  @P1_7_1_3.block_append 2464 524 1804 1932 128 128 256 81417907200 80643763200 162061670400 cost_2464_524_block10 cost_2464_524_block11 rfl rfl rfl

private theorem cost_2464_524_join0_12 : P1_7_1_3.blockEstimate 2464 524 2060 256 = 150157056000 :=
  @P1_7_1_3.block_append 2464 524 2060 2188 128 128 256 77667609600 72489446400 150157056000 cost_2464_524_block12 cost_2464_524_block13 rfl rfl rfl

private theorem cost_2464_524_join0_14 : P1_7_1_3.blockEstimate 2464 524 2316 256 = 120799816836 :=
  @P1_7_1_3.block_append 2464 524 2316 2444 128 128 256 65109273600 55690543236 120799816836 cost_2464_524_block14 cost_2464_524_block15 rfl rfl rfl

private theorem cost_2464_524_join0_16 : P1_7_1_3.blockEstimate 2464 524 2572 256 = 80626735523 :=
  @P1_7_1_3.block_append 2464 524 2572 2700 128 128 256 45424212243 35202523280 80626735523 cost_2464_524_block16 cost_2464_524_block17 rfl rfl rfl

private theorem cost_2464_524_join0_18 : P1_7_1_3.blockEstimate 2464 524 2828 256 = 42411790097 :=
  @P1_7_1_3.block_append 2464 524 2828 2956 128 128 256 25539618754 16872171343 42411790097 cost_2464_524_block18 cost_2464_524_block19 rfl rfl rfl

private theorem cost_2464_524_join0_20 : P1_7_1_3.blockEstimate 2464 524 3084 256 = 13910669248 :=
  @P1_7_1_3.block_append 2464 524 3084 3212 128 128 256 9640384480 4270284768 13910669248 cost_2464_524_block20 cost_2464_524_block21 rfl rfl rfl

private theorem cost_2464_524_join0_22 : P1_7_1_3.blockEstimate 2464 524 3340 172 = 1037542657 :=
  @P1_7_1_3.block_append 2464 524 3340 3468 128 44 172 1018374112 19168545 1037542657 cost_2464_524_block22 cost_2464_524_block23 rfl rfl rfl

private theorem cost_2464_524_join1_0 : P1_7_1_3.blockEstimate 2464 524 524 512 = 46818672768 :=
  @P1_7_1_3.block_append 2464 524 524 780 256 256 512 6429737024 40388935744 46818672768 cost_2464_524_join0_0 cost_2464_524_join0_2 rfl rfl rfl

private theorem cost_2464_524_join1_2 : P1_7_1_3.blockEstimate 2464 524 1036 512 = 225102279157 :=
  @P1_7_1_3.block_append 2464 524 1036 1292 256 256 512 92079610357 133022668800 225102279157 cost_2464_524_join0_4 cost_2464_524_join0_6 rfl rfl rfl

private theorem cost_2464_524_join1_4 : P1_7_1_3.blockEstimate 2464 524 1548 512 = 318411878400 :=
  @P1_7_1_3.block_append 2464 524 1548 1804 256 256 512 156350208000 162061670400 318411878400 cost_2464_524_join0_8 cost_2464_524_join0_10 rfl rfl rfl

private theorem cost_2464_524_join1_6 : P1_7_1_3.blockEstimate 2464 524 2060 512 = 270956872836 :=
  @P1_7_1_3.block_append 2464 524 2060 2316 256 256 512 150157056000 120799816836 270956872836 cost_2464_524_join0_12 cost_2464_524_join0_14 rfl rfl rfl

private theorem cost_2464_524_join1_8 : P1_7_1_3.blockEstimate 2464 524 2572 512 = 123038525620 :=
  @P1_7_1_3.block_append 2464 524 2572 2828 256 256 512 80626735523 42411790097 123038525620 cost_2464_524_join0_16 cost_2464_524_join0_18 rfl rfl rfl

private theorem cost_2464_524_join1_10 : P1_7_1_3.blockEstimate 2464 524 3084 428 = 14948211905 :=
  @P1_7_1_3.block_append 2464 524 3084 3340 256 172 428 13910669248 1037542657 14948211905 cost_2464_524_join0_20 cost_2464_524_join0_22 rfl rfl rfl

private theorem cost_2464_524_join2_0 : P1_7_1_3.blockEstimate 2464 524 524 1024 = 271920951925 :=
  @P1_7_1_3.block_append 2464 524 524 1036 512 512 1024 46818672768 225102279157 271920951925 cost_2464_524_join1_0 cost_2464_524_join1_2 rfl rfl rfl

private theorem cost_2464_524_join2_2 : P1_7_1_3.blockEstimate 2464 524 1548 1024 = 589368751236 :=
  @P1_7_1_3.block_append 2464 524 1548 2060 512 512 1024 318411878400 270956872836 589368751236 cost_2464_524_join1_4 cost_2464_524_join1_6 rfl rfl rfl

private theorem cost_2464_524_join2_4 : P1_7_1_3.blockEstimate 2464 524 2572 940 = 137986737525 :=
  @P1_7_1_3.block_append 2464 524 2572 3084 512 428 940 123038525620 14948211905 137986737525 cost_2464_524_join1_8 cost_2464_524_join1_10 rfl rfl rfl

private theorem cost_2464_524_join3_0 : P1_7_1_3.blockEstimate 2464 524 524 2048 = 861289703161 :=
  @P1_7_1_3.block_append 2464 524 524 1548 1024 1024 2048 271920951925 589368751236 861289703161 cost_2464_524_join2_0 cost_2464_524_join2_2 rfl rfl rfl

private theorem cost_2464_524_join4_0 : P1_7_1_3.blockEstimate 2464 524 524 2988 = 999276440686 :=
  @P1_7_1_3.block_append 2464 524 524 2572 2048 940 2988 861289703161 137986737525 999276440686 cost_2464_524_join3_0 cost_2464_524_join2_4 rfl rfl rfl

private theorem cost_2464_524_total : P1_7_1_3.momentEstimate 2464 524 = 999276440686 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2464 + 524 = 2988 by decide]
  exact cost_2464_524_join4_0

theorem moment2464_524 : P1_7_1.groupedPoleMoment 2464 524 ≤ 999276440686 :=
  (P1_7_1_3.grouped_bound 2464 524).trans_eq cost_2464_524_total
private theorem cost_2464_535_block0 : P1_7_1_3.blockEstimate 2464 535 535 128 = 847444000 := by decide +kernel

private theorem cost_2464_535_block1 : P1_7_1_3.blockEstimate 2464 535 663 128 = 5582293024 := by decide +kernel

private theorem cost_2464_535_block2 : P1_7_1_3.blockEstimate 2464 535 791 128 = 14273419296 := by decide +kernel

private theorem cost_2464_535_block3 : P1_7_1_3.blockEstimate 2464 535 919 128 = 26115516448 := by decide +kernel

private theorem cost_2464_535_block4 : P1_7_1_3.blockEstimate 2464 535 1047 128 = 39946231422 := by decide +kernel

private theorem cost_2464_535_block5 : P1_7_1_3.blockEstimate 2464 535 1175 128 = 52689108736 := by decide +kernel

private theorem cost_2464_535_block6 : P1_7_1_3.blockEstimate 2464 535 1303 128 = 63187779328 := by decide +kernel

private theorem cost_2464_535_block7 : P1_7_1_3.blockEstimate 2464 535 1431 128 = 71438302976 := by decide +kernel

private theorem cost_2464_535_block8 : P1_7_1_3.blockEstimate 2464 535 1559 128 = 77440679680 := by decide +kernel

private theorem cost_2464_535_block9 : P1_7_1_3.blockEstimate 2464 535 1687 128 = 81194909440 := by decide +kernel

private theorem cost_2464_535_block10 : P1_7_1_3.blockEstimate 2464 535 1815 128 = 82700992256 := by decide +kernel

private theorem cost_2464_535_block11 : P1_7_1_3.blockEstimate 2464 535 1943 128 = 81958928128 := by decide +kernel

private theorem cost_2464_535_block12 : P1_7_1_3.blockEstimate 2464 535 2071 128 = 78968717056 := by decide +kernel

private theorem cost_2464_535_block13 : P1_7_1_3.blockEstimate 2464 535 2199 128 = 73730359040 := by decide +kernel

private theorem cost_2464_535_block14 : P1_7_1_3.blockEstimate 2464 535 2327 128 = 66243854080 := by decide +kernel

private theorem cost_2464_535_block15 : P1_7_1_3.blockEstimate 2464 535 2455 128 = 56726170885 := by decide +kernel

private theorem cost_2464_535_block16 : P1_7_1_3.blockEstimate 2464 535 2583 128 = 46410879159 := by decide +kernel

private theorem cost_2464_535_block17 : P1_7_1_3.blockEstimate 2464 535 2711 128 = 36119010108 := by decide +kernel

private theorem cost_2464_535_block18 : P1_7_1_3.blockEstimate 2464 535 2839 128 = 26361648945 := by decide +kernel

private theorem cost_2464_535_block19 : P1_7_1_3.blockEstimate 2464 535 2967 128 = 17572807064 := by decide +kernel

private theorem cost_2464_535_block20 : P1_7_1_3.blockEstimate 2464 535 3095 128 = 10192550176 := by decide +kernel

private theorem cost_2464_535_block21 : P1_7_1_3.blockEstimate 2464 535 3223 128 = 4652161312 := by decide +kernel

private theorem cost_2464_535_block22 : P1_7_1_3.blockEstimate 2464 535 3351 128 = 1208334624 := by decide +kernel

private theorem cost_2464_535_block23 : P1_7_1_3.blockEstimate 2464 535 3479 55 = 36636838 := by decide +kernel

private theorem cost_2464_535_join0_0 : P1_7_1_3.blockEstimate 2464 535 535 256 = 6429737024 :=
  @P1_7_1_3.block_append 2464 535 535 663 128 128 256 847444000 5582293024 6429737024 cost_2464_535_block0 cost_2464_535_block1 rfl rfl rfl

private theorem cost_2464_535_join0_2 : P1_7_1_3.blockEstimate 2464 535 791 256 = 40388935744 :=
  @P1_7_1_3.block_append 2464 535 791 919 128 128 256 14273419296 26115516448 40388935744 cost_2464_535_block2 cost_2464_535_block3 rfl rfl rfl

private theorem cost_2464_535_join0_4 : P1_7_1_3.blockEstimate 2464 535 1047 256 = 92635340158 :=
  @P1_7_1_3.block_append 2464 535 1047 1175 128 128 256 39946231422 52689108736 92635340158 cost_2464_535_block4 cost_2464_535_block5 rfl rfl rfl

private theorem cost_2464_535_join0_6 : P1_7_1_3.blockEstimate 2464 535 1303 256 = 134626082304 :=
  @P1_7_1_3.block_append 2464 535 1303 1431 128 128 256 63187779328 71438302976 134626082304 cost_2464_535_block6 cost_2464_535_block7 rfl rfl rfl

private theorem cost_2464_535_join0_8 : P1_7_1_3.blockEstimate 2464 535 1559 256 = 158635589120 :=
  @P1_7_1_3.block_append 2464 535 1559 1687 128 128 256 77440679680 81194909440 158635589120 cost_2464_535_block8 cost_2464_535_block9 rfl rfl rfl

private theorem cost_2464_535_join0_10 : P1_7_1_3.blockEstimate 2464 535 1815 256 = 164659920384 :=
  @P1_7_1_3.block_append 2464 535 1815 1943 128 128 256 82700992256 81958928128 164659920384 cost_2464_535_block10 cost_2464_535_block11 rfl rfl rfl

private theorem cost_2464_535_join0_12 : P1_7_1_3.blockEstimate 2464 535 2071 256 = 152699076096 :=
  @P1_7_1_3.block_append 2464 535 2071 2199 128 128 256 78968717056 73730359040 152699076096 cost_2464_535_block12 cost_2464_535_block13 rfl rfl rfl

private theorem cost_2464_535_join0_14 : P1_7_1_3.blockEstimate 2464 535 2327 256 = 122970024965 :=
  @P1_7_1_3.block_append 2464 535 2327 2455 128 128 256 66243854080 56726170885 122970024965 cost_2464_535_block14 cost_2464_535_block15 rfl rfl rfl

private theorem cost_2464_535_join0_16 : P1_7_1_3.blockEstimate 2464 535 2583 256 = 82529889267 :=
  @P1_7_1_3.block_append 2464 535 2583 2711 128 128 256 46410879159 36119010108 82529889267 cost_2464_535_block16 cost_2464_535_block17 rfl rfl rfl

private theorem cost_2464_535_join0_18 : P1_7_1_3.blockEstimate 2464 535 2839 256 = 43934456009 :=
  @P1_7_1_3.block_append 2464 535 2839 2967 128 128 256 26361648945 17572807064 43934456009 cost_2464_535_block18 cost_2464_535_block19 rfl rfl rfl

private theorem cost_2464_535_join0_20 : P1_7_1_3.blockEstimate 2464 535 3095 256 = 14844711488 :=
  @P1_7_1_3.block_append 2464 535 3095 3223 128 128 256 10192550176 4652161312 14844711488 cost_2464_535_block20 cost_2464_535_block21 rfl rfl rfl

private theorem cost_2464_535_join0_22 : P1_7_1_3.blockEstimate 2464 535 3351 183 = 1244971462 :=
  @P1_7_1_3.block_append 2464 535 3351 3479 128 55 183 1208334624 36636838 1244971462 cost_2464_535_block22 cost_2464_535_block23 rfl rfl rfl

private theorem cost_2464_535_join1_0 : P1_7_1_3.blockEstimate 2464 535 535 512 = 46818672768 :=
  @P1_7_1_3.block_append 2464 535 535 791 256 256 512 6429737024 40388935744 46818672768 cost_2464_535_join0_0 cost_2464_535_join0_2 rfl rfl rfl

private theorem cost_2464_535_join1_2 : P1_7_1_3.blockEstimate 2464 535 1047 512 = 227261422462 :=
  @P1_7_1_3.block_append 2464 535 1047 1303 256 256 512 92635340158 134626082304 227261422462 cost_2464_535_join0_4 cost_2464_535_join0_6 rfl rfl rfl

private theorem cost_2464_535_join1_4 : P1_7_1_3.blockEstimate 2464 535 1559 512 = 323295509504 :=
  @P1_7_1_3.block_append 2464 535 1559 1815 256 256 512 158635589120 164659920384 323295509504 cost_2464_535_join0_8 cost_2464_535_join0_10 rfl rfl rfl

private theorem cost_2464_535_join1_6 : P1_7_1_3.blockEstimate 2464 535 2071 512 = 275669101061 :=
  @P1_7_1_3.block_append 2464 535 2071 2327 256 256 512 152699076096 122970024965 275669101061 cost_2464_535_join0_12 cost_2464_535_join0_14 rfl rfl rfl

private theorem cost_2464_535_join1_8 : P1_7_1_3.blockEstimate 2464 535 2583 512 = 126464345276 :=
  @P1_7_1_3.block_append 2464 535 2583 2839 256 256 512 82529889267 43934456009 126464345276 cost_2464_535_join0_16 cost_2464_535_join0_18 rfl rfl rfl

private theorem cost_2464_535_join1_10 : P1_7_1_3.blockEstimate 2464 535 3095 439 = 16089682950 :=
  @P1_7_1_3.block_append 2464 535 3095 3351 256 183 439 14844711488 1244971462 16089682950 cost_2464_535_join0_20 cost_2464_535_join0_22 rfl rfl rfl

private theorem cost_2464_535_join2_0 : P1_7_1_3.blockEstimate 2464 535 535 1024 = 274080095230 :=
  @P1_7_1_3.block_append 2464 535 535 1047 512 512 1024 46818672768 227261422462 274080095230 cost_2464_535_join1_0 cost_2464_535_join1_2 rfl rfl rfl

private theorem cost_2464_535_join2_2 : P1_7_1_3.blockEstimate 2464 535 1559 1024 = 598964610565 :=
  @P1_7_1_3.block_append 2464 535 1559 2071 512 512 1024 323295509504 275669101061 598964610565 cost_2464_535_join1_4 cost_2464_535_join1_6 rfl rfl rfl

private theorem cost_2464_535_join2_4 : P1_7_1_3.blockEstimate 2464 535 2583 951 = 142554028226 :=
  @P1_7_1_3.block_append 2464 535 2583 3095 512 439 951 126464345276 16089682950 142554028226 cost_2464_535_join1_8 cost_2464_535_join1_10 rfl rfl rfl

private theorem cost_2464_535_join3_0 : P1_7_1_3.blockEstimate 2464 535 535 2048 = 873044705795 :=
  @P1_7_1_3.block_append 2464 535 535 1559 1024 1024 2048 274080095230 598964610565 873044705795 cost_2464_535_join2_0 cost_2464_535_join2_2 rfl rfl rfl

private theorem cost_2464_535_join4_0 : P1_7_1_3.blockEstimate 2464 535 535 2999 = 1015598734021 :=
  @P1_7_1_3.block_append 2464 535 535 2583 2048 951 2999 873044705795 142554028226 1015598734021 cost_2464_535_join3_0 cost_2464_535_join2_4 rfl rfl rfl

private theorem cost_2464_535_total : P1_7_1_3.momentEstimate 2464 535 = 1015598734021 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2464 + 535 = 2999 by decide]
  exact cost_2464_535_join4_0

theorem moment2464_535 : P1_7_1.groupedPoleMoment 2464 535 ≤ 1015598734021 :=
  (P1_7_1_3.grouped_bound 2464 535).trans_eq cost_2464_535_total
private theorem cost_2509_546_block0 : P1_7_1_3.blockEstimate 2509 546 546 128 = 863543200 := by decide +kernel

private theorem cost_2509_546_block1 : P1_7_1_3.blockEstimate 2509 546 674 128 = 5693501344 := by decide +kernel

private theorem cost_2509_546_block2 : P1_7_1_3.blockEstimate 2509 546 802 128 = 14574108576 := by decide +kernel

private theorem cost_2509_546_block3 : P1_7_1_3.blockEstimate 2509 546 930 128 = 26700058528 := by decide +kernel

private theorem cost_2509_546_block4 : P1_7_1_3.blockEstimate 2509 546 1058 128 = 41004025237 := by decide +kernel

private theorem cost_2509_546_block5 : P1_7_1_3.blockEstimate 2509 546 1186 128 = 54452003328 := by decide +kernel

private theorem cost_2509_546_block6 : P1_7_1_3.blockEstimate 2509 546 1314 128 = 65618715136 := by decide +kernel

private theorem cost_2509_546_block7 : P1_7_1_3.blockEstimate 2509 546 1442 128 = 74491142656 := by decide +kernel

private theorem cost_2509_546_block8 : P1_7_1_3.blockEstimate 2509 546 1570 128 = 81069285888 := by decide +kernel

private theorem cost_2509_546_block9 : P1_7_1_3.blockEstimate 2509 546 1698 128 = 85353144832 := by decide +kernel

private theorem cost_2509_546_block10 : P1_7_1_3.blockEstimate 2509 546 1826 128 = 87342719488 := by decide +kernel

private theorem cost_2509_546_block11 : P1_7_1_3.blockEstimate 2509 546 1954 128 = 87038009856 := by decide +kernel

private theorem cost_2509_546_block12 : P1_7_1_3.blockEstimate 2509 546 2082 128 = 84439015936 := by decide +kernel

private theorem cost_2509_546_block13 : P1_7_1_3.blockEstimate 2509 546 2210 128 = 79545737728 := by decide +kernel

private theorem cost_2509_546_block14 : P1_7_1_3.blockEstimate 2509 546 2338 128 = 72358175232 := by decide +kernel

private theorem cost_2509_546_block15 : P1_7_1_3.blockEstimate 2509 546 2466 128 = 62955043190 := by decide +kernel

private theorem cost_2509_546_block16 : P1_7_1_3.blockEstimate 2509 546 2594 128 = 52359901840 := by decide +kernel

private theorem cost_2509_546_block17 : P1_7_1_3.blockEstimate 2509 546 2722 128 = 41614448575 := by decide +kernel

private theorem cost_2509_546_block18 : P1_7_1_3.blockEstimate 2509 546 2850 128 = 31252826283 := by decide +kernel

private theorem cost_2509_546_block19 : P1_7_1_3.blockEstimate 2509 546 2978 128 = 21743019590 := by decide +kernel

private theorem cost_2509_546_block20 : P1_7_1_3.blockEstimate 2509 546 3106 128 = 13482770112 := by decide +kernel

private theorem cost_2509_546_block21 : P1_7_1_3.blockEstimate 2509 546 3234 128 = 6968426176 := by decide +kernel

private theorem cost_2509_546_block22 : P1_7_1_3.blockEstimate 2509 546 3362 128 = 2487729856 := by decide +kernel

private theorem cost_2509_546_block23 : P1_7_1_3.blockEstimate 2509 546 3490 111 = 291563944 := by decide +kernel

private theorem cost_2509_546_join0_0 : P1_7_1_3.blockEstimate 2509 546 546 256 = 6557044544 :=
  @P1_7_1_3.block_append 2509 546 546 674 128 128 256 863543200 5693501344 6557044544 cost_2509_546_block0 cost_2509_546_block1 rfl rfl rfl

private theorem cost_2509_546_join0_2 : P1_7_1_3.blockEstimate 2509 546 802 256 = 41274167104 :=
  @P1_7_1_3.block_append 2509 546 802 930 128 128 256 14574108576 26700058528 41274167104 cost_2509_546_block2 cost_2509_546_block3 rfl rfl rfl

private theorem cost_2509_546_join0_4 : P1_7_1_3.blockEstimate 2509 546 1058 256 = 95456028565 :=
  @P1_7_1_3.block_append 2509 546 1058 1186 128 128 256 41004025237 54452003328 95456028565 cost_2509_546_block4 cost_2509_546_block5 rfl rfl rfl

private theorem cost_2509_546_join0_6 : P1_7_1_3.blockEstimate 2509 546 1314 256 = 140109857792 :=
  @P1_7_1_3.block_append 2509 546 1314 1442 128 128 256 65618715136 74491142656 140109857792 cost_2509_546_block6 cost_2509_546_block7 rfl rfl rfl

private theorem cost_2509_546_join0_8 : P1_7_1_3.blockEstimate 2509 546 1570 256 = 166422430720 :=
  @P1_7_1_3.block_append 2509 546 1570 1698 128 128 256 81069285888 85353144832 166422430720 cost_2509_546_block8 cost_2509_546_block9 rfl rfl rfl

private theorem cost_2509_546_join0_10 : P1_7_1_3.blockEstimate 2509 546 1826 256 = 174380729344 :=
  @P1_7_1_3.block_append 2509 546 1826 1954 128 128 256 87342719488 87038009856 174380729344 cost_2509_546_block10 cost_2509_546_block11 rfl rfl rfl

private theorem cost_2509_546_join0_12 : P1_7_1_3.blockEstimate 2509 546 2082 256 = 163984753664 :=
  @P1_7_1_3.block_append 2509 546 2082 2210 128 128 256 84439015936 79545737728 163984753664 cost_2509_546_block12 cost_2509_546_block13 rfl rfl rfl

private theorem cost_2509_546_join0_14 : P1_7_1_3.blockEstimate 2509 546 2338 256 = 135313218422 :=
  @P1_7_1_3.block_append 2509 546 2338 2466 128 128 256 72358175232 62955043190 135313218422 cost_2509_546_block14 cost_2509_546_block15 rfl rfl rfl

private theorem cost_2509_546_join0_16 : P1_7_1_3.blockEstimate 2509 546 2594 256 = 93974350415 :=
  @P1_7_1_3.block_append 2509 546 2594 2722 128 128 256 52359901840 41614448575 93974350415 cost_2509_546_block16 cost_2509_546_block17 rfl rfl rfl

private theorem cost_2509_546_join0_18 : P1_7_1_3.blockEstimate 2509 546 2850 256 = 52995845873 :=
  @P1_7_1_3.block_append 2509 546 2850 2978 128 128 256 31252826283 21743019590 52995845873 cost_2509_546_block18 cost_2509_546_block19 rfl rfl rfl

private theorem cost_2509_546_join0_20 : P1_7_1_3.blockEstimate 2509 546 3106 256 = 20451196288 :=
  @P1_7_1_3.block_append 2509 546 3106 3234 128 128 256 13482770112 6968426176 20451196288 cost_2509_546_block20 cost_2509_546_block21 rfl rfl rfl

private theorem cost_2509_546_join0_22 : P1_7_1_3.blockEstimate 2509 546 3362 239 = 2779293800 :=
  @P1_7_1_3.block_append 2509 546 3362 3490 128 111 239 2487729856 291563944 2779293800 cost_2509_546_block22 cost_2509_546_block23 rfl rfl rfl

private theorem cost_2509_546_join1_0 : P1_7_1_3.blockEstimate 2509 546 546 512 = 47831211648 :=
  @P1_7_1_3.block_append 2509 546 546 802 256 256 512 6557044544 41274167104 47831211648 cost_2509_546_join0_0 cost_2509_546_join0_2 rfl rfl rfl

private theorem cost_2509_546_join1_2 : P1_7_1_3.blockEstimate 2509 546 1058 512 = 235565886357 :=
  @P1_7_1_3.block_append 2509 546 1058 1314 256 256 512 95456028565 140109857792 235565886357 cost_2509_546_join0_4 cost_2509_546_join0_6 rfl rfl rfl

private theorem cost_2509_546_join1_4 : P1_7_1_3.blockEstimate 2509 546 1570 512 = 340803160064 :=
  @P1_7_1_3.block_append 2509 546 1570 1826 256 256 512 166422430720 174380729344 340803160064 cost_2509_546_join0_8 cost_2509_546_join0_10 rfl rfl rfl

private theorem cost_2509_546_join1_6 : P1_7_1_3.blockEstimate 2509 546 2082 512 = 299297972086 :=
  @P1_7_1_3.block_append 2509 546 2082 2338 256 256 512 163984753664 135313218422 299297972086 cost_2509_546_join0_12 cost_2509_546_join0_14 rfl rfl rfl

private theorem cost_2509_546_join1_8 : P1_7_1_3.blockEstimate 2509 546 2594 512 = 146970196288 :=
  @P1_7_1_3.block_append 2509 546 2594 2850 256 256 512 93974350415 52995845873 146970196288 cost_2509_546_join0_16 cost_2509_546_join0_18 rfl rfl rfl

private theorem cost_2509_546_join1_10 : P1_7_1_3.blockEstimate 2509 546 3106 495 = 23230490088 :=
  @P1_7_1_3.block_append 2509 546 3106 3362 256 239 495 20451196288 2779293800 23230490088 cost_2509_546_join0_20 cost_2509_546_join0_22 rfl rfl rfl

private theorem cost_2509_546_join2_0 : P1_7_1_3.blockEstimate 2509 546 546 1024 = 283397098005 :=
  @P1_7_1_3.block_append 2509 546 546 1058 512 512 1024 47831211648 235565886357 283397098005 cost_2509_546_join1_0 cost_2509_546_join1_2 rfl rfl rfl

private theorem cost_2509_546_join2_2 : P1_7_1_3.blockEstimate 2509 546 1570 1024 = 640101132150 :=
  @P1_7_1_3.block_append 2509 546 1570 2082 512 512 1024 340803160064 299297972086 640101132150 cost_2509_546_join1_4 cost_2509_546_join1_6 rfl rfl rfl

private theorem cost_2509_546_join2_4 : P1_7_1_3.blockEstimate 2509 546 2594 1007 = 170200686376 :=
  @P1_7_1_3.block_append 2509 546 2594 3106 512 495 1007 146970196288 23230490088 170200686376 cost_2509_546_join1_8 cost_2509_546_join1_10 rfl rfl rfl

private theorem cost_2509_546_join3_0 : P1_7_1_3.blockEstimate 2509 546 546 2048 = 923498230155 :=
  @P1_7_1_3.block_append 2509 546 546 1570 1024 1024 2048 283397098005 640101132150 923498230155 cost_2509_546_join2_0 cost_2509_546_join2_2 rfl rfl rfl

private theorem cost_2509_546_join4_0 : P1_7_1_3.blockEstimate 2509 546 546 3055 = 1093698916531 :=
  @P1_7_1_3.block_append 2509 546 546 2594 2048 1007 3055 923498230155 170200686376 1093698916531 cost_2509_546_join3_0 cost_2509_546_join2_4 rfl rfl rfl

private theorem cost_2509_546_total : P1_7_1_3.momentEstimate 2509 546 = 1093698916531 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2509 + 546 = 3055 by decide]
  exact cost_2509_546_join4_0

theorem moment2509_546 : P1_7_1.groupedPoleMoment 2509 546 ≤ 1093698916531 :=
  (P1_7_1_3.grouped_bound 2509 546).trans_eq cost_2509_546_total
private theorem cost_2509_556_block0 : P1_7_1_3.blockEstimate 2509 556 556 128 = 863543200 := by decide +kernel

private theorem cost_2509_556_block1 : P1_7_1_3.blockEstimate 2509 556 684 128 = 5693501344 := by decide +kernel

private theorem cost_2509_556_block2 : P1_7_1_3.blockEstimate 2509 556 812 128 = 14574108576 := by decide +kernel

private theorem cost_2509_556_block3 : P1_7_1_3.blockEstimate 2509 556 940 128 = 26700058528 := by decide +kernel

private theorem cost_2509_556_block4 : P1_7_1_3.blockEstimate 2509 556 1068 128 = 41079320147 := by decide +kernel

private theorem cost_2509_556_block5 : P1_7_1_3.blockEstimate 2509 556 1196 128 = 54803844928 := by decide +kernel

private theorem cost_2509_556_block6 : P1_7_1_3.blockEstimate 2509 556 1324 128 = 66220330816 := by decide +kernel

private theorem cost_2509_556_block7 : P1_7_1_3.blockEstimate 2509 556 1452 128 = 75300589376 := by decide +kernel

private theorem cost_2509_556_block8 : P1_7_1_3.blockEstimate 2509 556 1580 128 = 82044620608 := by decide +kernel

private theorem cost_2509_556_block9 : P1_7_1_3.blockEstimate 2509 556 1708 128 = 86452424512 := by decide +kernel

private theorem cost_2509_556_block10 : P1_7_1_3.blockEstimate 2509 556 1836 128 = 88524001088 := by decide +kernel

private theorem cost_2509_556_block11 : P1_7_1_3.blockEstimate 2509 556 1964 128 = 88259350336 := by decide +kernel

private theorem cost_2509_556_block12 : P1_7_1_3.blockEstimate 2509 556 2092 128 = 85658472256 := by decide +kernel

private theorem cost_2509_556_block13 : P1_7_1_3.blockEstimate 2509 556 2220 128 = 80721366848 := by decide +kernel

private theorem cost_2509_556_block14 : P1_7_1_3.blockEstimate 2509 556 2348 128 = 73448034112 := by decide +kernel

private theorem cost_2509_556_block15 : P1_7_1_3.blockEstimate 2509 556 2476 128 = 63947518937 := by decide +kernel

private theorem cost_2509_556_block16 : P1_7_1_3.blockEstimate 2509 556 2604 128 = 53310498035 := by decide +kernel

private theorem cost_2509_556_block17 : P1_7_1_3.blockEstimate 2509 556 2732 128 = 42508618103 := by decide +kernel

private theorem cost_2509_556_block18 : P1_7_1_3.blockEstimate 2509 556 2860 128 = 32068956552 := by decide +kernel

private theorem cost_2509_556_block19 : P1_7_1_3.blockEstimate 2509 556 2988 128 = 22457723694 := by decide +kernel

private theorem cost_2509_556_block20 : P1_7_1_3.blockEstimate 2509 556 3116 128 = 14070007184 := by decide +kernel

private theorem cost_2509_556_block21 : P1_7_1_3.blockEstimate 2509 556 3244 128 = 7407382928 := by decide +kernel

private theorem cost_2509_556_block22 : P1_7_1_3.blockEstimate 2509 556 3372 128 = 2758745488 := by decide +kernel

private theorem cost_2509_556_block23 : P1_7_1_3.blockEstimate 2509 556 3500 121 = 375720434 := by decide +kernel

private theorem cost_2509_556_join0_0 : P1_7_1_3.blockEstimate 2509 556 556 256 = 6557044544 :=
  @P1_7_1_3.block_append 2509 556 556 684 128 128 256 863543200 5693501344 6557044544 cost_2509_556_block0 cost_2509_556_block1 rfl rfl rfl

private theorem cost_2509_556_join0_2 : P1_7_1_3.blockEstimate 2509 556 812 256 = 41274167104 :=
  @P1_7_1_3.block_append 2509 556 812 940 128 128 256 14574108576 26700058528 41274167104 cost_2509_556_block2 cost_2509_556_block3 rfl rfl rfl

private theorem cost_2509_556_join0_4 : P1_7_1_3.blockEstimate 2509 556 1068 256 = 95883165075 :=
  @P1_7_1_3.block_append 2509 556 1068 1196 128 128 256 41079320147 54803844928 95883165075 cost_2509_556_block4 cost_2509_556_block5 rfl rfl rfl

private theorem cost_2509_556_join0_6 : P1_7_1_3.blockEstimate 2509 556 1324 256 = 141520920192 :=
  @P1_7_1_3.block_append 2509 556 1324 1452 128 128 256 66220330816 75300589376 141520920192 cost_2509_556_block6 cost_2509_556_block7 rfl rfl rfl

private theorem cost_2509_556_join0_8 : P1_7_1_3.blockEstimate 2509 556 1580 256 = 168497045120 :=
  @P1_7_1_3.block_append 2509 556 1580 1708 128 128 256 82044620608 86452424512 168497045120 cost_2509_556_block8 cost_2509_556_block9 rfl rfl rfl

private theorem cost_2509_556_join0_10 : P1_7_1_3.blockEstimate 2509 556 1836 256 = 176783351424 :=
  @P1_7_1_3.block_append 2509 556 1836 1964 128 128 256 88524001088 88259350336 176783351424 cost_2509_556_block10 cost_2509_556_block11 rfl rfl rfl

private theorem cost_2509_556_join0_12 : P1_7_1_3.blockEstimate 2509 556 2092 256 = 166379839104 :=
  @P1_7_1_3.block_append 2509 556 2092 2220 128 128 256 85658472256 80721366848 166379839104 cost_2509_556_block12 cost_2509_556_block13 rfl rfl rfl

private theorem cost_2509_556_join0_14 : P1_7_1_3.blockEstimate 2509 556 2348 256 = 137395553049 :=
  @P1_7_1_3.block_append 2509 556 2348 2476 128 128 256 73448034112 63947518937 137395553049 cost_2509_556_block14 cost_2509_556_block15 rfl rfl rfl

private theorem cost_2509_556_join0_16 : P1_7_1_3.blockEstimate 2509 556 2604 256 = 95819116138 :=
  @P1_7_1_3.block_append 2509 556 2604 2732 128 128 256 53310498035 42508618103 95819116138 cost_2509_556_block16 cost_2509_556_block17 rfl rfl rfl

private theorem cost_2509_556_join0_18 : P1_7_1_3.blockEstimate 2509 556 2860 256 = 54526680246 :=
  @P1_7_1_3.block_append 2509 556 2860 2988 128 128 256 32068956552 22457723694 54526680246 cost_2509_556_block18 cost_2509_556_block19 rfl rfl rfl

private theorem cost_2509_556_join0_20 : P1_7_1_3.blockEstimate 2509 556 3116 256 = 21477390112 :=
  @P1_7_1_3.block_append 2509 556 3116 3244 128 128 256 14070007184 7407382928 21477390112 cost_2509_556_block20 cost_2509_556_block21 rfl rfl rfl

private theorem cost_2509_556_join0_22 : P1_7_1_3.blockEstimate 2509 556 3372 249 = 3134465922 :=
  @P1_7_1_3.block_append 2509 556 3372 3500 128 121 249 2758745488 375720434 3134465922 cost_2509_556_block22 cost_2509_556_block23 rfl rfl rfl

private theorem cost_2509_556_join1_0 : P1_7_1_3.blockEstimate 2509 556 556 512 = 47831211648 :=
  @P1_7_1_3.block_append 2509 556 556 812 256 256 512 6557044544 41274167104 47831211648 cost_2509_556_join0_0 cost_2509_556_join0_2 rfl rfl rfl

private theorem cost_2509_556_join1_2 : P1_7_1_3.blockEstimate 2509 556 1068 512 = 237404085267 :=
  @P1_7_1_3.block_append 2509 556 1068 1324 256 256 512 95883165075 141520920192 237404085267 cost_2509_556_join0_4 cost_2509_556_join0_6 rfl rfl rfl

private theorem cost_2509_556_join1_4 : P1_7_1_3.blockEstimate 2509 556 1580 512 = 345280396544 :=
  @P1_7_1_3.block_append 2509 556 1580 1836 256 256 512 168497045120 176783351424 345280396544 cost_2509_556_join0_8 cost_2509_556_join0_10 rfl rfl rfl

private theorem cost_2509_556_join1_6 : P1_7_1_3.blockEstimate 2509 556 2092 512 = 303775392153 :=
  @P1_7_1_3.block_append 2509 556 2092 2348 256 256 512 166379839104 137395553049 303775392153 cost_2509_556_join0_12 cost_2509_556_join0_14 rfl rfl rfl

private theorem cost_2509_556_join1_8 : P1_7_1_3.blockEstimate 2509 556 2604 512 = 150345796384 :=
  @P1_7_1_3.block_append 2509 556 2604 2860 256 256 512 95819116138 54526680246 150345796384 cost_2509_556_join0_16 cost_2509_556_join0_18 rfl rfl rfl

private theorem cost_2509_556_join1_10 : P1_7_1_3.blockEstimate 2509 556 3116 505 = 24611856034 :=
  @P1_7_1_3.block_append 2509 556 3116 3372 256 249 505 21477390112 3134465922 24611856034 cost_2509_556_join0_20 cost_2509_556_join0_22 rfl rfl rfl

private theorem cost_2509_556_join2_0 : P1_7_1_3.blockEstimate 2509 556 556 1024 = 285235296915 :=
  @P1_7_1_3.block_append 2509 556 556 1068 512 512 1024 47831211648 237404085267 285235296915 cost_2509_556_join1_0 cost_2509_556_join1_2 rfl rfl rfl

private theorem cost_2509_556_join2_2 : P1_7_1_3.blockEstimate 2509 556 1580 1024 = 649055788697 :=
  @P1_7_1_3.block_append 2509 556 1580 2092 512 512 1024 345280396544 303775392153 649055788697 cost_2509_556_join1_4 cost_2509_556_join1_6 rfl rfl rfl

private theorem cost_2509_556_join2_4 : P1_7_1_3.blockEstimate 2509 556 2604 1017 = 174957652418 :=
  @P1_7_1_3.block_append 2509 556 2604 3116 512 505 1017 150345796384 24611856034 174957652418 cost_2509_556_join1_8 cost_2509_556_join1_10 rfl rfl rfl

private theorem cost_2509_556_join3_0 : P1_7_1_3.blockEstimate 2509 556 556 2048 = 934291085612 :=
  @P1_7_1_3.block_append 2509 556 556 1580 1024 1024 2048 285235296915 649055788697 934291085612 cost_2509_556_join2_0 cost_2509_556_join2_2 rfl rfl rfl

private theorem cost_2509_556_join4_0 : P1_7_1_3.blockEstimate 2509 556 556 3065 = 1109248738030 :=
  @P1_7_1_3.block_append 2509 556 556 2604 2048 1017 3065 934291085612 174957652418 1109248738030 cost_2509_556_join3_0 cost_2509_556_join2_4 rfl rfl rfl

private theorem cost_2509_556_total : P1_7_1_3.momentEstimate 2509 556 = 1109248738030 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2509 + 556 = 3065 by decide]
  exact cost_2509_556_join4_0

theorem moment2509_556 : P1_7_1.groupedPoleMoment 2509 556 ≤ 1109248738030 :=
  (P1_7_1_3.grouped_bound 2509 556).trans_eq cost_2509_556_total
private theorem cost_2510_546_block0 : P1_7_1_3.blockEstimate 2510 546 546 128 = 863900960 := by decide +kernel

private theorem cost_2510_546_block1 : P1_7_1_3.blockEstimate 2510 546 674 128 = 5695972640 := by decide +kernel

private theorem cost_2510_546_block2 : P1_7_1_3.blockEstimate 2510 546 802 128 = 14580790560 := by decide +kernel

private theorem cost_2510_546_block3 : P1_7_1_3.blockEstimate 2510 546 930 128 = 26713048352 := by decide +kernel

private theorem cost_2510_546_block4 : P1_7_1_3.blockEstimate 2510 546 1058 128 = 41025281638 := by decide +kernel

private theorem cost_2510_546_block5 : P1_7_1_3.blockEstimate 2510 546 1186 128 = 54482215232 := by decide +kernel

private theorem cost_2510_546_block6 : P1_7_1_3.blockEstimate 2510 546 1314 128 = 65657889088 := by decide +kernel

private theorem cost_2510_546_block7 : P1_7_1_3.blockEstimate 2510 546 1442 128 = 74539278656 := by decide +kernel

private theorem cost_2510_546_block8 : P1_7_1_3.blockEstimate 2510 546 1570 128 = 81126383936 := by decide +kernel

private theorem cost_2510_546_block9 : P1_7_1_3.blockEstimate 2510 546 1698 128 = 85419204928 := by decide +kernel

private theorem cost_2510_546_block10 : P1_7_1_3.blockEstimate 2510 546 1826 128 = 87417741632 := by decide +kernel

private theorem cost_2510_546_block11 : P1_7_1_3.blockEstimate 2510 546 1954 128 = 87121994048 := by decide +kernel

private theorem cost_2510_546_block12 : P1_7_1_3.blockEstimate 2510 546 2082 128 = 84531962176 := by decide +kernel

private theorem cost_2510_546_block13 : P1_7_1_3.blockEstimate 2510 546 2210 128 = 79647646016 := by decide +kernel

private theorem cost_2510_546_block14 : P1_7_1_3.blockEstimate 2510 546 2338 128 = 72469045568 := by decide +kernel

private theorem cost_2510_546_block15 : P1_7_1_3.blockEstimate 2510 546 2466 128 = 63072140416 := by decide +kernel

private theorem cost_2510_546_block16 : P1_7_1_3.blockEstimate 2510 546 2594 128 = 52472658970 := by decide +kernel

private theorem cost_2510_546_block17 : P1_7_1_3.blockEstimate 2510 546 2722 128 = 41718992798 := by decide +kernel

private theorem cost_2510_546_block18 : P1_7_1_3.blockEstimate 2510 546 2850 128 = 31346284148 := by decide +kernel

private theorem cost_2510_546_block19 : P1_7_1_3.blockEstimate 2510 546 2978 128 = 21823243943 := by decide +kernel

private theorem cost_2510_546_block20 : P1_7_1_3.blockEstimate 2510 546 3106 128 = 13547063552 := by decide +kernel

private theorem cost_2510_546_block21 : P1_7_1_3.blockEstimate 2510 546 3234 128 = 7014795520 := by decide +kernel

private theorem cost_2510_546_block22 : P1_7_1_3.blockEstimate 2510 546 3362 128 = 2515257600 := by decide +kernel

private theorem cost_2510_546_block23 : P1_7_1_3.blockEstimate 2510 546 3490 112 = 299473440 := by decide +kernel

private theorem cost_2510_546_join0_0 : P1_7_1_3.blockEstimate 2510 546 546 256 = 6559873600 :=
  @P1_7_1_3.block_append 2510 546 546 674 128 128 256 863900960 5695972640 6559873600 cost_2510_546_block0 cost_2510_546_block1 rfl rfl rfl

private theorem cost_2510_546_join0_2 : P1_7_1_3.blockEstimate 2510 546 802 256 = 41293838912 :=
  @P1_7_1_3.block_append 2510 546 802 930 128 128 256 14580790560 26713048352 41293838912 cost_2510_546_block2 cost_2510_546_block3 rfl rfl rfl

private theorem cost_2510_546_join0_4 : P1_7_1_3.blockEstimate 2510 546 1058 256 = 95507496870 :=
  @P1_7_1_3.block_append 2510 546 1058 1186 128 128 256 41025281638 54482215232 95507496870 cost_2510_546_block4 cost_2510_546_block5 rfl rfl rfl

private theorem cost_2510_546_join0_6 : P1_7_1_3.blockEstimate 2510 546 1314 256 = 140197167744 :=
  @P1_7_1_3.block_append 2510 546 1314 1442 128 128 256 65657889088 74539278656 140197167744 cost_2510_546_block6 cost_2510_546_block7 rfl rfl rfl

private theorem cost_2510_546_join0_8 : P1_7_1_3.blockEstimate 2510 546 1570 256 = 166545588864 :=
  @P1_7_1_3.block_append 2510 546 1570 1698 128 128 256 81126383936 85419204928 166545588864 cost_2510_546_block8 cost_2510_546_block9 rfl rfl rfl

private theorem cost_2510_546_join0_10 : P1_7_1_3.blockEstimate 2510 546 1826 256 = 174539735680 :=
  @P1_7_1_3.block_append 2510 546 1826 1954 128 128 256 87417741632 87121994048 174539735680 cost_2510_546_block10 cost_2510_546_block11 rfl rfl rfl

private theorem cost_2510_546_join0_12 : P1_7_1_3.blockEstimate 2510 546 2082 256 = 164179608192 :=
  @P1_7_1_3.block_append 2510 546 2082 2210 128 128 256 84531962176 79647646016 164179608192 cost_2510_546_block12 cost_2510_546_block13 rfl rfl rfl

private theorem cost_2510_546_join0_14 : P1_7_1_3.blockEstimate 2510 546 2338 256 = 135541185984 :=
  @P1_7_1_3.block_append 2510 546 2338 2466 128 128 256 72469045568 63072140416 135541185984 cost_2510_546_block14 cost_2510_546_block15 rfl rfl rfl

private theorem cost_2510_546_join0_16 : P1_7_1_3.blockEstimate 2510 546 2594 256 = 94191651768 :=
  @P1_7_1_3.block_append 2510 546 2594 2722 128 128 256 52472658970 41718992798 94191651768 cost_2510_546_block16 cost_2510_546_block17 rfl rfl rfl

private theorem cost_2510_546_join0_18 : P1_7_1_3.blockEstimate 2510 546 2850 256 = 53169528091 :=
  @P1_7_1_3.block_append 2510 546 2850 2978 128 128 256 31346284148 21823243943 53169528091 cost_2510_546_block18 cost_2510_546_block19 rfl rfl rfl

private theorem cost_2510_546_join0_20 : P1_7_1_3.blockEstimate 2510 546 3106 256 = 20561859072 :=
  @P1_7_1_3.block_append 2510 546 3106 3234 128 128 256 13547063552 7014795520 20561859072 cost_2510_546_block20 cost_2510_546_block21 rfl rfl rfl

private theorem cost_2510_546_join0_22 : P1_7_1_3.blockEstimate 2510 546 3362 240 = 2814731040 :=
  @P1_7_1_3.block_append 2510 546 3362 3490 128 112 240 2515257600 299473440 2814731040 cost_2510_546_block22 cost_2510_546_block23 rfl rfl rfl

private theorem cost_2510_546_join1_0 : P1_7_1_3.blockEstimate 2510 546 546 512 = 47853712512 :=
  @P1_7_1_3.block_append 2510 546 546 802 256 256 512 6559873600 41293838912 47853712512 cost_2510_546_join0_0 cost_2510_546_join0_2 rfl rfl rfl

private theorem cost_2510_546_join1_2 : P1_7_1_3.blockEstimate 2510 546 1058 512 = 235704664614 :=
  @P1_7_1_3.block_append 2510 546 1058 1314 256 256 512 95507496870 140197167744 235704664614 cost_2510_546_join0_4 cost_2510_546_join0_6 rfl rfl rfl

private theorem cost_2510_546_join1_4 : P1_7_1_3.blockEstimate 2510 546 1570 512 = 341085324544 :=
  @P1_7_1_3.block_append 2510 546 1570 1826 256 256 512 166545588864 174539735680 341085324544 cost_2510_546_join0_8 cost_2510_546_join0_10 rfl rfl rfl

private theorem cost_2510_546_join1_6 : P1_7_1_3.blockEstimate 2510 546 2082 512 = 299720794176 :=
  @P1_7_1_3.block_append 2510 546 2082 2338 256 256 512 164179608192 135541185984 299720794176 cost_2510_546_join0_12 cost_2510_546_join0_14 rfl rfl rfl

private theorem cost_2510_546_join1_8 : P1_7_1_3.blockEstimate 2510 546 2594 512 = 147361179859 :=
  @P1_7_1_3.block_append 2510 546 2594 2850 256 256 512 94191651768 53169528091 147361179859 cost_2510_546_join0_16 cost_2510_546_join0_18 rfl rfl rfl

private theorem cost_2510_546_join1_10 : P1_7_1_3.blockEstimate 2510 546 3106 496 = 23376590112 :=
  @P1_7_1_3.block_append 2510 546 3106 3362 256 240 496 20561859072 2814731040 23376590112 cost_2510_546_join0_20 cost_2510_546_join0_22 rfl rfl rfl

private theorem cost_2510_546_join2_0 : P1_7_1_3.blockEstimate 2510 546 546 1024 = 283558377126 :=
  @P1_7_1_3.block_append 2510 546 546 1058 512 512 1024 47853712512 235704664614 283558377126 cost_2510_546_join1_0 cost_2510_546_join1_2 rfl rfl rfl

private theorem cost_2510_546_join2_2 : P1_7_1_3.blockEstimate 2510 546 1570 1024 = 640806118720 :=
  @P1_7_1_3.block_append 2510 546 1570 2082 512 512 1024 341085324544 299720794176 640806118720 cost_2510_546_join1_4 cost_2510_546_join1_6 rfl rfl rfl

private theorem cost_2510_546_join2_4 : P1_7_1_3.blockEstimate 2510 546 2594 1008 = 170737769971 :=
  @P1_7_1_3.block_append 2510 546 2594 3106 512 496 1008 147361179859 23376590112 170737769971 cost_2510_546_join1_8 cost_2510_546_join1_10 rfl rfl rfl

private theorem cost_2510_546_join3_0 : P1_7_1_3.blockEstimate 2510 546 546 2048 = 924364495846 :=
  @P1_7_1_3.block_append 2510 546 546 1570 1024 1024 2048 283558377126 640806118720 924364495846 cost_2510_546_join2_0 cost_2510_546_join2_2 rfl rfl rfl

private theorem cost_2510_546_join4_0 : P1_7_1_3.blockEstimate 2510 546 546 3056 = 1095102265817 :=
  @P1_7_1_3.block_append 2510 546 546 2594 2048 1008 3056 924364495846 170737769971 1095102265817 cost_2510_546_join3_0 cost_2510_546_join2_4 rfl rfl rfl

private theorem cost_2510_546_total : P1_7_1_3.momentEstimate 2510 546 = 1095102265817 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2510 + 546 = 3056 by decide]
  exact cost_2510_546_join4_0

theorem moment2510_546 : P1_7_1.groupedPoleMoment 2510 546 ≤ 1095102265817 :=
  (P1_7_1_3.grouped_bound 2510 546).trans_eq cost_2510_546_total
private theorem cost_2510_558_block0 : P1_7_1_3.blockEstimate 2510 558 558 128 = 863900960 := by decide +kernel

private theorem cost_2510_558_block1 : P1_7_1_3.blockEstimate 2510 558 686 128 = 5695972640 := by decide +kernel

private theorem cost_2510_558_block2 : P1_7_1_3.blockEstimate 2510 558 814 128 = 14580790560 := by decide +kernel

private theorem cost_2510_558_block3 : P1_7_1_3.blockEstimate 2510 558 942 128 = 26713048352 := by decide +kernel

private theorem cost_2510_558_block4 : P1_7_1_3.blockEstimate 2510 558 1070 128 = 41113692677 := by decide +kernel

private theorem cost_2510_558_block5 : P1_7_1_3.blockEstimate 2510 558 1198 128 = 54901885376 := by decide +kernel

private theorem cost_2510_558_block6 : P1_7_1_3.blockEstimate 2510 558 1326 128 = 66377681344 := by decide +kernel

private theorem cost_2510_558_block7 : P1_7_1_3.blockEstimate 2510 558 1454 128 = 75508861376 := by decide +kernel

private theorem cost_2510_558_block8 : P1_7_1_3.blockEstimate 2510 558 1582 128 = 82295425472 := by decide +kernel

private theorem cost_2510_558_block9 : P1_7_1_3.blockEstimate 2510 558 1710 128 = 86737373632 := by decide +kernel

private theorem cost_2510_558_block10 : P1_7_1_3.blockEstimate 2510 558 1838 128 = 88834705856 := by decide +kernel

private theorem cost_2510_558_block11 : P1_7_1_3.blockEstimate 2510 558 1966 128 = 88587422144 := by decide +kernel

private theorem cost_2510_558_block12 : P1_7_1_3.blockEstimate 2510 558 2094 128 = 85995522496 := by decide +kernel

private theorem cost_2510_558_block13 : P1_7_1_3.blockEstimate 2510 558 2222 128 = 81059006912 := by decide +kernel

private theorem cost_2510_558_block14 : P1_7_1_3.blockEstimate 2510 558 2350 128 = 73777875392 := by decide +kernel

private theorem cost_2510_558_block15 : P1_7_1_3.blockEstimate 2510 558 2478 128 = 64264493047 := by decide +kernel

private theorem cost_2510_558_block16 : P1_7_1_3.blockEstimate 2510 558 2606 128 = 53615041146 := by decide +kernel

private theorem cost_2510_558_block17 : P1_7_1_3.blockEstimate 2510 558 2734 128 = 42793966353 := by decide +kernel

private theorem cost_2510_558_block18 : P1_7_1_3.blockEstimate 2510 558 2862 128 = 32327922297 := by decide +kernel

private theorem cost_2510_558_block19 : P1_7_1_3.blockEstimate 2510 558 2990 128 = 22683505643 := by decide +kernel

private theorem cost_2510_558_block20 : P1_7_1_3.blockEstimate 2510 558 3118 128 = 14254676000 := by decide +kernel

private theorem cost_2510_558_block21 : P1_7_1_3.blockEstimate 2510 558 3246 128 = 7544741920 := by decide +kernel

private theorem cost_2510_558_block22 : P1_7_1_3.blockEstimate 2510 558 3374 128 = 2843944992 := by decide +kernel

private theorem cost_2510_558_block23 : P1_7_1_3.blockEstimate 2510 558 3502 124 = 403940943 := by decide +kernel

private theorem cost_2510_558_join0_0 : P1_7_1_3.blockEstimate 2510 558 558 256 = 6559873600 :=
  @P1_7_1_3.block_append 2510 558 558 686 128 128 256 863900960 5695972640 6559873600 cost_2510_558_block0 cost_2510_558_block1 rfl rfl rfl

private theorem cost_2510_558_join0_2 : P1_7_1_3.blockEstimate 2510 558 814 256 = 41293838912 :=
  @P1_7_1_3.block_append 2510 558 814 942 128 128 256 14580790560 26713048352 41293838912 cost_2510_558_block2 cost_2510_558_block3 rfl rfl rfl

private theorem cost_2510_558_join0_4 : P1_7_1_3.blockEstimate 2510 558 1070 256 = 96015578053 :=
  @P1_7_1_3.block_append 2510 558 1070 1198 128 128 256 41113692677 54901885376 96015578053 cost_2510_558_block4 cost_2510_558_block5 rfl rfl rfl

private theorem cost_2510_558_join0_6 : P1_7_1_3.blockEstimate 2510 558 1326 256 = 141886542720 :=
  @P1_7_1_3.block_append 2510 558 1326 1454 128 128 256 66377681344 75508861376 141886542720 cost_2510_558_block6 cost_2510_558_block7 rfl rfl rfl

private theorem cost_2510_558_join0_8 : P1_7_1_3.blockEstimate 2510 558 1582 256 = 169032799104 :=
  @P1_7_1_3.block_append 2510 558 1582 1710 128 128 256 82295425472 86737373632 169032799104 cost_2510_558_block8 cost_2510_558_block9 rfl rfl rfl

private theorem cost_2510_558_join0_10 : P1_7_1_3.blockEstimate 2510 558 1838 256 = 177422128000 :=
  @P1_7_1_3.block_append 2510 558 1838 1966 128 128 256 88834705856 88587422144 177422128000 cost_2510_558_block10 cost_2510_558_block11 rfl rfl rfl

private theorem cost_2510_558_join0_12 : P1_7_1_3.blockEstimate 2510 558 2094 256 = 167054529408 :=
  @P1_7_1_3.block_append 2510 558 2094 2222 128 128 256 85995522496 81059006912 167054529408 cost_2510_558_block12 cost_2510_558_block13 rfl rfl rfl

private theorem cost_2510_558_join0_14 : P1_7_1_3.blockEstimate 2510 558 2350 256 = 138042368439 :=
  @P1_7_1_3.block_append 2510 558 2350 2478 128 128 256 73777875392 64264493047 138042368439 cost_2510_558_block14 cost_2510_558_block15 rfl rfl rfl

private theorem cost_2510_558_join0_16 : P1_7_1_3.blockEstimate 2510 558 2606 256 = 96409007499 :=
  @P1_7_1_3.block_append 2510 558 2606 2734 128 128 256 53615041146 42793966353 96409007499 cost_2510_558_block16 cost_2510_558_block17 rfl rfl rfl

private theorem cost_2510_558_join0_18 : P1_7_1_3.blockEstimate 2510 558 2862 256 = 55011427940 :=
  @P1_7_1_3.block_append 2510 558 2862 2990 128 128 256 32327922297 22683505643 55011427940 cost_2510_558_block18 cost_2510_558_block19 rfl rfl rfl

private theorem cost_2510_558_join0_20 : P1_7_1_3.blockEstimate 2510 558 3118 256 = 21799417920 :=
  @P1_7_1_3.block_append 2510 558 3118 3246 128 128 256 14254676000 7544741920 21799417920 cost_2510_558_block20 cost_2510_558_block21 rfl rfl rfl

private theorem cost_2510_558_join0_22 : P1_7_1_3.blockEstimate 2510 558 3374 252 = 3247885935 :=
  @P1_7_1_3.block_append 2510 558 3374 3502 128 124 252 2843944992 403940943 3247885935 cost_2510_558_block22 cost_2510_558_block23 rfl rfl rfl

private theorem cost_2510_558_join1_0 : P1_7_1_3.blockEstimate 2510 558 558 512 = 47853712512 :=
  @P1_7_1_3.block_append 2510 558 558 814 256 256 512 6559873600 41293838912 47853712512 cost_2510_558_join0_0 cost_2510_558_join0_2 rfl rfl rfl

private theorem cost_2510_558_join1_2 : P1_7_1_3.blockEstimate 2510 558 1070 512 = 237902120773 :=
  @P1_7_1_3.block_append 2510 558 1070 1326 256 256 512 96015578053 141886542720 237902120773 cost_2510_558_join0_4 cost_2510_558_join0_6 rfl rfl rfl

private theorem cost_2510_558_join1_4 : P1_7_1_3.blockEstimate 2510 558 1582 512 = 346454927104 :=
  @P1_7_1_3.block_append 2510 558 1582 1838 256 256 512 169032799104 177422128000 346454927104 cost_2510_558_join0_8 cost_2510_558_join0_10 rfl rfl rfl

private theorem cost_2510_558_join1_6 : P1_7_1_3.blockEstimate 2510 558 2094 512 = 305096897847 :=
  @P1_7_1_3.block_append 2510 558 2094 2350 256 256 512 167054529408 138042368439 305096897847 cost_2510_558_join0_12 cost_2510_558_join0_14 rfl rfl rfl

private theorem cost_2510_558_join1_8 : P1_7_1_3.blockEstimate 2510 558 2606 512 = 151420435439 :=
  @P1_7_1_3.block_append 2510 558 2606 2862 256 256 512 96409007499 55011427940 151420435439 cost_2510_558_join0_16 cost_2510_558_join0_18 rfl rfl rfl

private theorem cost_2510_558_join1_10 : P1_7_1_3.blockEstimate 2510 558 3118 508 = 25047303855 :=
  @P1_7_1_3.block_append 2510 558 3118 3374 256 252 508 21799417920 3247885935 25047303855 cost_2510_558_join0_20 cost_2510_558_join0_22 rfl rfl rfl

private theorem cost_2510_558_join2_0 : P1_7_1_3.blockEstimate 2510 558 558 1024 = 285755833285 :=
  @P1_7_1_3.block_append 2510 558 558 1070 512 512 1024 47853712512 237902120773 285755833285 cost_2510_558_join1_0 cost_2510_558_join1_2 rfl rfl rfl

private theorem cost_2510_558_join2_2 : P1_7_1_3.blockEstimate 2510 558 1582 1024 = 651551824951 :=
  @P1_7_1_3.block_append 2510 558 1582 2094 512 512 1024 346454927104 305096897847 651551824951 cost_2510_558_join1_4 cost_2510_558_join1_6 rfl rfl rfl

private theorem cost_2510_558_join2_4 : P1_7_1_3.blockEstimate 2510 558 2606 1020 = 176467739294 :=
  @P1_7_1_3.block_append 2510 558 2606 3118 512 508 1020 151420435439 25047303855 176467739294 cost_2510_558_join1_8 cost_2510_558_join1_10 rfl rfl rfl

private theorem cost_2510_558_join3_0 : P1_7_1_3.blockEstimate 2510 558 558 2048 = 937307658236 :=
  @P1_7_1_3.block_append 2510 558 558 1582 1024 1024 2048 285755833285 651551824951 937307658236 cost_2510_558_join2_0 cost_2510_558_join2_2 rfl rfl rfl

private theorem cost_2510_558_join4_0 : P1_7_1_3.blockEstimate 2510 558 558 3068 = 1113775397530 :=
  @P1_7_1_3.block_append 2510 558 558 2606 2048 1020 3068 937307658236 176467739294 1113775397530 cost_2510_558_join3_0 cost_2510_558_join2_4 rfl rfl rfl

private theorem cost_2510_558_total : P1_7_1_3.momentEstimate 2510 558 = 1113775397530 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2510 + 558 = 3068 by decide]
  exact cost_2510_558_join4_0

theorem moment2510_558 : P1_7_1.groupedPoleMoment 2510 558 ≤ 1113775397530 :=
  (P1_7_1_3.grouped_bound 2510 558).trans_eq cost_2510_558_total
private theorem cost_2511_546_block0 : P1_7_1_3.blockEstimate 2511 546 546 128 = 864258720 := by decide +kernel

private theorem cost_2511_546_block1 : P1_7_1_3.blockEstimate 2511 546 674 128 = 5698443936 := by decide +kernel

private theorem cost_2511_546_block2 : P1_7_1_3.blockEstimate 2511 546 802 128 = 14587472544 := by decide +kernel

private theorem cost_2511_546_block3 : P1_7_1_3.blockEstimate 2511 546 930 128 = 26726038176 := by decide +kernel

private theorem cost_2511_546_block4 : P1_7_1_3.blockEstimate 2511 546 1058 128 = 41046538039 := by decide +kernel

private theorem cost_2511_546_block5 : P1_7_1_3.blockEstimate 2511 546 1186 128 = 54512427136 := by decide +kernel

private theorem cost_2511_546_block6 : P1_7_1_3.blockEstimate 2511 546 1314 128 = 65697063040 := by decide +kernel

private theorem cost_2511_546_block7 : P1_7_1_3.blockEstimate 2511 546 1442 128 = 74587414656 := by decide +kernel

private theorem cost_2511_546_block8 : P1_7_1_3.blockEstimate 2511 546 1570 128 = 81183481984 := by decide +kernel

private theorem cost_2511_546_block9 : P1_7_1_3.blockEstimate 2511 546 1698 128 = 85485265024 := by decide +kernel

private theorem cost_2511_546_block10 : P1_7_1_3.blockEstimate 2511 546 1826 128 = 87492763776 := by decide +kernel

private theorem cost_2511_546_block11 : P1_7_1_3.blockEstimate 2511 546 1954 128 = 87205978240 := by decide +kernel

private theorem cost_2511_546_block12 : P1_7_1_3.blockEstimate 2511 546 2082 128 = 84624908416 := by decide +kernel

private theorem cost_2511_546_block13 : P1_7_1_3.blockEstimate 2511 546 2210 128 = 79749554304 := by decide +kernel

private theorem cost_2511_546_block14 : P1_7_1_3.blockEstimate 2511 546 2338 128 = 72579915904 := by decide +kernel

private theorem cost_2511_546_block15 : P1_7_1_3.blockEstimate 2511 546 2466 128 = 63189301461 := by decide +kernel

private theorem cost_2511_546_block16 : P1_7_1_3.blockEstimate 2511 546 2594 128 = 52585528506 := by decide +kernel

private theorem cost_2511_546_block17 : P1_7_1_3.blockEstimate 2511 546 2722 128 = 41823665102 := by decide +kernel

private theorem cost_2511_546_block18 : P1_7_1_3.blockEstimate 2511 546 2850 128 = 31439882892 := by decide +kernel

private theorem cost_2511_546_block19 : P1_7_1_3.blockEstimate 2511 546 2978 128 = 21903614308 := by decide +kernel

private theorem cost_2511_546_block20 : P1_7_1_3.blockEstimate 2511 546 3106 128 = 13611521168 := by decide +kernel

private theorem cost_2511_546_block21 : P1_7_1_3.blockEstimate 2511 546 3234 128 = 7061328016 := by decide +kernel

private theorem cost_2511_546_block22 : P1_7_1_3.blockEstimate 2511 546 3362 128 = 2542947472 := by decide +kernel

private theorem cost_2511_546_block23 : P1_7_1_3.blockEstimate 2511 546 3490 113 = 307526469 := by decide +kernel

private theorem cost_2511_546_join0_0 : P1_7_1_3.blockEstimate 2511 546 546 256 = 6562702656 :=
  @P1_7_1_3.block_append 2511 546 546 674 128 128 256 864258720 5698443936 6562702656 cost_2511_546_block0 cost_2511_546_block1 rfl rfl rfl

private theorem cost_2511_546_join0_2 : P1_7_1_3.blockEstimate 2511 546 802 256 = 41313510720 :=
  @P1_7_1_3.block_append 2511 546 802 930 128 128 256 14587472544 26726038176 41313510720 cost_2511_546_block2 cost_2511_546_block3 rfl rfl rfl

private theorem cost_2511_546_join0_4 : P1_7_1_3.blockEstimate 2511 546 1058 256 = 95558965175 :=
  @P1_7_1_3.block_append 2511 546 1058 1186 128 128 256 41046538039 54512427136 95558965175 cost_2511_546_block4 cost_2511_546_block5 rfl rfl rfl

private theorem cost_2511_546_join0_6 : P1_7_1_3.blockEstimate 2511 546 1314 256 = 140284477696 :=
  @P1_7_1_3.block_append 2511 546 1314 1442 128 128 256 65697063040 74587414656 140284477696 cost_2511_546_block6 cost_2511_546_block7 rfl rfl rfl

private theorem cost_2511_546_join0_8 : P1_7_1_3.blockEstimate 2511 546 1570 256 = 166668747008 :=
  @P1_7_1_3.block_append 2511 546 1570 1698 128 128 256 81183481984 85485265024 166668747008 cost_2511_546_block8 cost_2511_546_block9 rfl rfl rfl

private theorem cost_2511_546_join0_10 : P1_7_1_3.blockEstimate 2511 546 1826 256 = 174698742016 :=
  @P1_7_1_3.block_append 2511 546 1826 1954 128 128 256 87492763776 87205978240 174698742016 cost_2511_546_block10 cost_2511_546_block11 rfl rfl rfl

private theorem cost_2511_546_join0_12 : P1_7_1_3.blockEstimate 2511 546 2082 256 = 164374462720 :=
  @P1_7_1_3.block_append 2511 546 2082 2210 128 128 256 84624908416 79749554304 164374462720 cost_2511_546_block12 cost_2511_546_block13 rfl rfl rfl

private theorem cost_2511_546_join0_14 : P1_7_1_3.blockEstimate 2511 546 2338 256 = 135769217365 :=
  @P1_7_1_3.block_append 2511 546 2338 2466 128 128 256 72579915904 63189301461 135769217365 cost_2511_546_block14 cost_2511_546_block15 rfl rfl rfl

private theorem cost_2511_546_join0_16 : P1_7_1_3.blockEstimate 2511 546 2594 256 = 94409193608 :=
  @P1_7_1_3.block_append 2511 546 2594 2722 128 128 256 52585528506 41823665102 94409193608 cost_2511_546_block16 cost_2511_546_block17 rfl rfl rfl

private theorem cost_2511_546_join0_18 : P1_7_1_3.blockEstimate 2511 546 2850 256 = 53343497200 :=
  @P1_7_1_3.block_append 2511 546 2850 2978 128 128 256 31439882892 21903614308 53343497200 cost_2511_546_block18 cost_2511_546_block19 rfl rfl rfl

private theorem cost_2511_546_join0_20 : P1_7_1_3.blockEstimate 2511 546 3106 256 = 20672849184 :=
  @P1_7_1_3.block_append 2511 546 3106 3234 128 128 256 13611521168 7061328016 20672849184 cost_2511_546_block20 cost_2511_546_block21 rfl rfl rfl

private theorem cost_2511_546_join0_22 : P1_7_1_3.blockEstimate 2511 546 3362 241 = 2850473941 :=
  @P1_7_1_3.block_append 2511 546 3362 3490 128 113 241 2542947472 307526469 2850473941 cost_2511_546_block22 cost_2511_546_block23 rfl rfl rfl

private theorem cost_2511_546_join1_0 : P1_7_1_3.blockEstimate 2511 546 546 512 = 47876213376 :=
  @P1_7_1_3.block_append 2511 546 546 802 256 256 512 6562702656 41313510720 47876213376 cost_2511_546_join0_0 cost_2511_546_join0_2 rfl rfl rfl

private theorem cost_2511_546_join1_2 : P1_7_1_3.blockEstimate 2511 546 1058 512 = 235843442871 :=
  @P1_7_1_3.block_append 2511 546 1058 1314 256 256 512 95558965175 140284477696 235843442871 cost_2511_546_join0_4 cost_2511_546_join0_6 rfl rfl rfl

private theorem cost_2511_546_join1_4 : P1_7_1_3.blockEstimate 2511 546 1570 512 = 341367489024 :=
  @P1_7_1_3.block_append 2511 546 1570 1826 256 256 512 166668747008 174698742016 341367489024 cost_2511_546_join0_8 cost_2511_546_join0_10 rfl rfl rfl

private theorem cost_2511_546_join1_6 : P1_7_1_3.blockEstimate 2511 546 2082 512 = 300143680085 :=
  @P1_7_1_3.block_append 2511 546 2082 2338 256 256 512 164374462720 135769217365 300143680085 cost_2511_546_join0_12 cost_2511_546_join0_14 rfl rfl rfl

private theorem cost_2511_546_join1_8 : P1_7_1_3.blockEstimate 2511 546 2594 512 = 147752690808 :=
  @P1_7_1_3.block_append 2511 546 2594 2850 256 256 512 94409193608 53343497200 147752690808 cost_2511_546_join0_16 cost_2511_546_join0_18 rfl rfl rfl

private theorem cost_2511_546_join1_10 : P1_7_1_3.blockEstimate 2511 546 3106 497 = 23523323125 :=
  @P1_7_1_3.block_append 2511 546 3106 3362 256 241 497 20672849184 2850473941 23523323125 cost_2511_546_join0_20 cost_2511_546_join0_22 rfl rfl rfl

private theorem cost_2511_546_join2_0 : P1_7_1_3.blockEstimate 2511 546 546 1024 = 283719656247 :=
  @P1_7_1_3.block_append 2511 546 546 1058 512 512 1024 47876213376 235843442871 283719656247 cost_2511_546_join1_0 cost_2511_546_join1_2 rfl rfl rfl

private theorem cost_2511_546_join2_2 : P1_7_1_3.blockEstimate 2511 546 1570 1024 = 641511169109 :=
  @P1_7_1_3.block_append 2511 546 1570 2082 512 512 1024 341367489024 300143680085 641511169109 cost_2511_546_join1_4 cost_2511_546_join1_6 rfl rfl rfl

private theorem cost_2511_546_join2_4 : P1_7_1_3.blockEstimate 2511 546 2594 1009 = 171276013933 :=
  @P1_7_1_3.block_append 2511 546 2594 3106 512 497 1009 147752690808 23523323125 171276013933 cost_2511_546_join1_8 cost_2511_546_join1_10 rfl rfl rfl

private theorem cost_2511_546_join3_0 : P1_7_1_3.blockEstimate 2511 546 546 2048 = 925230825356 :=
  @P1_7_1_3.block_append 2511 546 546 1570 1024 1024 2048 283719656247 641511169109 925230825356 cost_2511_546_join2_0 cost_2511_546_join2_2 rfl rfl rfl

private theorem cost_2511_546_join4_0 : P1_7_1_3.blockEstimate 2511 546 546 3057 = 1096506839289 :=
  @P1_7_1_3.block_append 2511 546 546 2594 2048 1009 3057 925230825356 171276013933 1096506839289 cost_2511_546_join3_0 cost_2511_546_join2_4 rfl rfl rfl

private theorem cost_2511_546_total : P1_7_1_3.momentEstimate 2511 546 = 1096506839289 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2511 + 546 = 3057 by decide]
  exact cost_2511_546_join4_0

theorem moment2511_546 : P1_7_1.groupedPoleMoment 2511 546 ≤ 1096506839289 :=
  (P1_7_1_3.grouped_bound 2511 546).trans_eq cost_2511_546_total
private theorem cost_2512_546_block0 : P1_7_1_3.blockEstimate 2512 546 546 128 = 864616480 := by decide +kernel

private theorem cost_2512_546_block1 : P1_7_1_3.blockEstimate 2512 546 674 128 = 5700915232 := by decide +kernel

private theorem cost_2512_546_block2 : P1_7_1_3.blockEstimate 2512 546 802 128 = 14594154528 := by decide +kernel

private theorem cost_2512_546_block3 : P1_7_1_3.blockEstimate 2512 546 930 128 = 26739028000 := by decide +kernel

private theorem cost_2512_546_block4 : P1_7_1_3.blockEstimate 2512 546 1058 128 = 41067794440 := by decide +kernel

private theorem cost_2512_546_block5 : P1_7_1_3.blockEstimate 2512 546 1186 128 = 54542639040 := by decide +kernel

private theorem cost_2512_546_block6 : P1_7_1_3.blockEstimate 2512 546 1314 128 = 65736236992 := by decide +kernel

private theorem cost_2512_546_block7 : P1_7_1_3.blockEstimate 2512 546 1442 128 = 74635550656 := by decide +kernel

private theorem cost_2512_546_block8 : P1_7_1_3.blockEstimate 2512 546 1570 128 = 81240580032 := by decide +kernel

private theorem cost_2512_546_block9 : P1_7_1_3.blockEstimate 2512 546 1698 128 = 85551325120 := by decide +kernel

private theorem cost_2512_546_block10 : P1_7_1_3.blockEstimate 2512 546 1826 128 = 87567785920 := by decide +kernel

private theorem cost_2512_546_block11 : P1_7_1_3.blockEstimate 2512 546 1954 128 = 87289962432 := by decide +kernel

private theorem cost_2512_546_block12 : P1_7_1_3.blockEstimate 2512 546 2082 128 = 84717854656 := by decide +kernel

private theorem cost_2512_546_block13 : P1_7_1_3.blockEstimate 2512 546 2210 128 = 79851462592 := by decide +kernel

private theorem cost_2512_546_block14 : P1_7_1_3.blockEstimate 2512 546 2338 128 = 72690786240 := by decide +kernel

private theorem cost_2512_546_block15 : P1_7_1_3.blockEstimate 2512 546 2466 128 = 63306526325 := by decide +kernel

private theorem cost_2512_546_block16 : P1_7_1_3.blockEstimate 2512 546 2594 128 = 52698510448 := by decide +kernel

private theorem cost_2512_546_block17 : P1_7_1_3.blockEstimate 2512 546 2722 128 = 41928465566 := by decide +kernel

private theorem cost_2512_546_block18 : P1_7_1_3.blockEstimate 2512 546 2850 128 = 31533622614 := by decide +kernel

private theorem cost_2512_546_block19 : P1_7_1_3.blockEstimate 2512 546 2978 128 = 21984130556 := by decide +kernel

private theorem cost_2512_546_block20 : P1_7_1_3.blockEstimate 2512 546 3106 128 = 13676143088 := by decide +kernel

private theorem cost_2512_546_block21 : P1_7_1_3.blockEstimate 2512 546 3234 128 = 7108023792 := by decide +kernel

private theorem cost_2512_546_block22 : P1_7_1_3.blockEstimate 2512 546 3362 128 = 2570799600 := by decide +kernel

private theorem cost_2512_546_block23 : P1_7_1_3.blockEstimate 2512 546 3490 114 = 315723145 := by decide +kernel

private theorem cost_2512_546_join0_0 : P1_7_1_3.blockEstimate 2512 546 546 256 = 6565531712 :=
  @P1_7_1_3.block_append 2512 546 546 674 128 128 256 864616480 5700915232 6565531712 cost_2512_546_block0 cost_2512_546_block1 rfl rfl rfl

private theorem cost_2512_546_join0_2 : P1_7_1_3.blockEstimate 2512 546 802 256 = 41333182528 :=
  @P1_7_1_3.block_append 2512 546 802 930 128 128 256 14594154528 26739028000 41333182528 cost_2512_546_block2 cost_2512_546_block3 rfl rfl rfl

private theorem cost_2512_546_join0_4 : P1_7_1_3.blockEstimate 2512 546 1058 256 = 95610433480 :=
  @P1_7_1_3.block_append 2512 546 1058 1186 128 128 256 41067794440 54542639040 95610433480 cost_2512_546_block4 cost_2512_546_block5 rfl rfl rfl

private theorem cost_2512_546_join0_6 : P1_7_1_3.blockEstimate 2512 546 1314 256 = 140371787648 :=
  @P1_7_1_3.block_append 2512 546 1314 1442 128 128 256 65736236992 74635550656 140371787648 cost_2512_546_block6 cost_2512_546_block7 rfl rfl rfl

private theorem cost_2512_546_join0_8 : P1_7_1_3.blockEstimate 2512 546 1570 256 = 166791905152 :=
  @P1_7_1_3.block_append 2512 546 1570 1698 128 128 256 81240580032 85551325120 166791905152 cost_2512_546_block8 cost_2512_546_block9 rfl rfl rfl

private theorem cost_2512_546_join0_10 : P1_7_1_3.blockEstimate 2512 546 1826 256 = 174857748352 :=
  @P1_7_1_3.block_append 2512 546 1826 1954 128 128 256 87567785920 87289962432 174857748352 cost_2512_546_block10 cost_2512_546_block11 rfl rfl rfl

private theorem cost_2512_546_join0_12 : P1_7_1_3.blockEstimate 2512 546 2082 256 = 164569317248 :=
  @P1_7_1_3.block_append 2512 546 2082 2210 128 128 256 84717854656 79851462592 164569317248 cost_2512_546_block12 cost_2512_546_block13 rfl rfl rfl

private theorem cost_2512_546_join0_14 : P1_7_1_3.blockEstimate 2512 546 2338 256 = 135997312565 :=
  @P1_7_1_3.block_append 2512 546 2338 2466 128 128 256 72690786240 63306526325 135997312565 cost_2512_546_block14 cost_2512_546_block15 rfl rfl rfl

private theorem cost_2512_546_join0_16 : P1_7_1_3.blockEstimate 2512 546 2594 256 = 94626976014 :=
  @P1_7_1_3.block_append 2512 546 2594 2722 128 128 256 52698510448 41928465566 94626976014 cost_2512_546_block16 cost_2512_546_block17 rfl rfl rfl

private theorem cost_2512_546_join0_18 : P1_7_1_3.blockEstimate 2512 546 2850 256 = 53517753170 :=
  @P1_7_1_3.block_append 2512 546 2850 2978 128 128 256 31533622614 21984130556 53517753170 cost_2512_546_block18 cost_2512_546_block19 rfl rfl rfl

private theorem cost_2512_546_join0_20 : P1_7_1_3.blockEstimate 2512 546 3106 256 = 20784166880 :=
  @P1_7_1_3.block_append 2512 546 3106 3234 128 128 256 13676143088 7108023792 20784166880 cost_2512_546_block20 cost_2512_546_block21 rfl rfl rfl

private theorem cost_2512_546_join0_22 : P1_7_1_3.blockEstimate 2512 546 3362 242 = 2886522745 :=
  @P1_7_1_3.block_append 2512 546 3362 3490 128 114 242 2570799600 315723145 2886522745 cost_2512_546_block22 cost_2512_546_block23 rfl rfl rfl

private theorem cost_2512_546_join1_0 : P1_7_1_3.blockEstimate 2512 546 546 512 = 47898714240 :=
  @P1_7_1_3.block_append 2512 546 546 802 256 256 512 6565531712 41333182528 47898714240 cost_2512_546_join0_0 cost_2512_546_join0_2 rfl rfl rfl

private theorem cost_2512_546_join1_2 : P1_7_1_3.blockEstimate 2512 546 1058 512 = 235982221128 :=
  @P1_7_1_3.block_append 2512 546 1058 1314 256 256 512 95610433480 140371787648 235982221128 cost_2512_546_join0_4 cost_2512_546_join0_6 rfl rfl rfl

private theorem cost_2512_546_join1_4 : P1_7_1_3.blockEstimate 2512 546 1570 512 = 341649653504 :=
  @P1_7_1_3.block_append 2512 546 1570 1826 256 256 512 166791905152 174857748352 341649653504 cost_2512_546_join0_8 cost_2512_546_join0_10 rfl rfl rfl

private theorem cost_2512_546_join1_6 : P1_7_1_3.blockEstimate 2512 546 2082 512 = 300566629813 :=
  @P1_7_1_3.block_append 2512 546 2082 2338 256 256 512 164569317248 135997312565 300566629813 cost_2512_546_join0_12 cost_2512_546_join0_14 rfl rfl rfl

private theorem cost_2512_546_join1_8 : P1_7_1_3.blockEstimate 2512 546 2594 512 = 148144729184 :=
  @P1_7_1_3.block_append 2512 546 2594 2850 256 256 512 94626976014 53517753170 148144729184 cost_2512_546_join0_16 cost_2512_546_join0_18 rfl rfl rfl

private theorem cost_2512_546_join1_10 : P1_7_1_3.blockEstimate 2512 546 3106 498 = 23670689625 :=
  @P1_7_1_3.block_append 2512 546 3106 3362 256 242 498 20784166880 2886522745 23670689625 cost_2512_546_join0_20 cost_2512_546_join0_22 rfl rfl rfl

private theorem cost_2512_546_join2_0 : P1_7_1_3.blockEstimate 2512 546 546 1024 = 283880935368 :=
  @P1_7_1_3.block_append 2512 546 546 1058 512 512 1024 47898714240 235982221128 283880935368 cost_2512_546_join1_0 cost_2512_546_join1_2 rfl rfl rfl

private theorem cost_2512_546_join2_2 : P1_7_1_3.blockEstimate 2512 546 1570 1024 = 642216283317 :=
  @P1_7_1_3.block_append 2512 546 1570 2082 512 512 1024 341649653504 300566629813 642216283317 cost_2512_546_join1_4 cost_2512_546_join1_6 rfl rfl rfl

private theorem cost_2512_546_join2_4 : P1_7_1_3.blockEstimate 2512 546 2594 1010 = 171815418809 :=
  @P1_7_1_3.block_append 2512 546 2594 3106 512 498 1010 148144729184 23670689625 171815418809 cost_2512_546_join1_8 cost_2512_546_join1_10 rfl rfl rfl

private theorem cost_2512_546_join3_0 : P1_7_1_3.blockEstimate 2512 546 546 2048 = 926097218685 :=
  @P1_7_1_3.block_append 2512 546 546 1570 1024 1024 2048 283880935368 642216283317 926097218685 cost_2512_546_join2_0 cost_2512_546_join2_2 rfl rfl rfl

private theorem cost_2512_546_join4_0 : P1_7_1_3.blockEstimate 2512 546 546 3058 = 1097912637494 :=
  @P1_7_1_3.block_append 2512 546 546 2594 2048 1010 3058 926097218685 171815418809 1097912637494 cost_2512_546_join3_0 cost_2512_546_join2_4 rfl rfl rfl

private theorem cost_2512_546_total : P1_7_1_3.momentEstimate 2512 546 = 1097912637494 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2512 + 546 = 3058 by decide]
  exact cost_2512_546_join4_0

theorem moment2512_546 : P1_7_1.groupedPoleMoment 2512 546 ≤ 1097912637494 :=
  (P1_7_1_3.grouped_bound 2512 546).trans_eq cost_2512_546_total
private theorem cost_2565_551_block0 : P1_7_1_3.blockEstimate 2565 551 551 128 = 883577760 := by decide +kernel

private theorem cost_2565_551_block1 : P1_7_1_3.blockEstimate 2565 551 679 128 = 5831893920 := by decide +kernel

private theorem cost_2565_551_block2 : P1_7_1_3.blockEstimate 2565 551 807 128 = 14948299680 := by decide +kernel

private theorem cost_2565_551_block3 : P1_7_1_3.blockEstimate 2565 551 935 128 = 27427488672 := by decide +kernel

private theorem cost_2565_551_block4 : P1_7_1_3.blockEstimate 2565 551 1063 128 = 42235332858 := by decide +kernel

private theorem cost_2565_551_block5 : P1_7_1_3.blockEstimate 2565 551 1191 128 = 56328252672 := by decide +kernel

private theorem cost_2565_551_block6 : P1_7_1_3.blockEstimate 2565 551 1319 128 = 68126108928 := by decide +kernel

private theorem cost_2565_551_block7 : P1_7_1_3.blockEstimate 2565 551 1447 128 = 77608709376 := by decide +kernel

private theorem cost_2565_551_block8 : P1_7_1_3.blockEstimate 2565 551 1575 128 = 84776054016 := by decide +kernel

private theorem cost_2565_551_block9 : P1_7_1_3.blockEstimate 2565 551 1703 128 = 89628142848 := by decide +kernel

private theorem cost_2565_551_block10 : P1_7_1_3.blockEstimate 2565 551 1831 128 = 92164975872 := by decide +kernel

private theorem cost_2565_551_block11 : P1_7_1_3.blockEstimate 2565 551 1959 128 = 92386553088 := by decide +kernel

private theorem cost_2565_551_block12 : P1_7_1_3.blockEstimate 2565 551 2087 128 = 90292874496 := by decide +kernel

private theorem cost_2565_551_block13 : P1_7_1_3.blockEstimate 2565 551 2215 128 = 85883940096 := by decide +kernel

private theorem cost_2565_551_block14 : P1_7_1_3.blockEstimate 2565 551 2343 128 = 79159749888 := by decide +kernel

private theorem cost_2565_551_block15 : P1_7_1_3.blockEstimate 2565 551 2471 128 = 70125432177 := by decide +kernel

private theorem cost_2565_551_block16 : P1_7_1_3.blockEstimate 2565 551 2599 128 = 59347484091 := by decide +kernel

private theorem cost_2565_551_block17 : P1_7_1_3.blockEstimate 2565 551 2727 128 = 48140594770 := by decide +kernel

private theorem cost_2565_551_block18 : P1_7_1_3.blockEstimate 2565 551 2855 128 = 37141827764 := by decide +kernel

private theorem cost_2565_551_block19 : P1_7_1_3.blockEstimate 2565 551 2983 128 = 26849211137 := by decide +kernel

private theorem cost_2565_551_block20 : P1_7_1_3.blockEstimate 2565 551 3111 128 = 17668456984 := by decide +kernel

private theorem cost_2565_551_block21 : P1_7_1_3.blockEstimate 2565 551 3239 128 = 10076559040 := by decide +kernel

private theorem cost_2565_551_block22 : P1_7_1_3.blockEstimate 2565 551 3367 128 = 4457000640 := by decide +kernel

private theorem cost_2565_551_block23 : P1_7_1_3.blockEstimate 2565 551 3495 128 = 1061537472 := by decide +kernel

private theorem cost_2565_551_block24 : P1_7_1_3.blockEstimate 2565 551 3623 44 = 19960688 := by decide +kernel

private theorem cost_2565_551_join0_0 : P1_7_1_3.blockEstimate 2565 551 551 256 = 6715471680 :=
  @P1_7_1_3.block_append 2565 551 551 679 128 128 256 883577760 5831893920 6715471680 cost_2565_551_block0 cost_2565_551_block1 rfl rfl rfl

private theorem cost_2565_551_join0_2 : P1_7_1_3.blockEstimate 2565 551 807 256 = 42375788352 :=
  @P1_7_1_3.block_append 2565 551 807 935 128 128 256 14948299680 27427488672 42375788352 cost_2565_551_block2 cost_2565_551_block3 rfl rfl rfl

private theorem cost_2565_551_join0_4 : P1_7_1_3.blockEstimate 2565 551 1063 256 = 98563585530 :=
  @P1_7_1_3.block_append 2565 551 1063 1191 128 128 256 42235332858 56328252672 98563585530 cost_2565_551_block4 cost_2565_551_block5 rfl rfl rfl

private theorem cost_2565_551_join0_6 : P1_7_1_3.blockEstimate 2565 551 1319 256 = 145734818304 :=
  @P1_7_1_3.block_append 2565 551 1319 1447 128 128 256 68126108928 77608709376 145734818304 cost_2565_551_block6 cost_2565_551_block7 rfl rfl rfl

private theorem cost_2565_551_join0_8 : P1_7_1_3.blockEstimate 2565 551 1575 256 = 174404196864 :=
  @P1_7_1_3.block_append 2565 551 1575 1703 128 128 256 84776054016 89628142848 174404196864 cost_2565_551_block8 cost_2565_551_block9 rfl rfl rfl

private theorem cost_2565_551_join0_10 : P1_7_1_3.blockEstimate 2565 551 1831 256 = 184551528960 :=
  @P1_7_1_3.block_append 2565 551 1831 1959 128 128 256 92164975872 92386553088 184551528960 cost_2565_551_block10 cost_2565_551_block11 rfl rfl rfl

private theorem cost_2565_551_join0_12 : P1_7_1_3.blockEstimate 2565 551 2087 256 = 176176814592 :=
  @P1_7_1_3.block_append 2565 551 2087 2215 128 128 256 90292874496 85883940096 176176814592 cost_2565_551_block12 cost_2565_551_block13 rfl rfl rfl

private theorem cost_2565_551_join0_14 : P1_7_1_3.blockEstimate 2565 551 2343 256 = 149285182065 :=
  @P1_7_1_3.block_append 2565 551 2343 2471 128 128 256 79159749888 70125432177 149285182065 cost_2565_551_block14 cost_2565_551_block15 rfl rfl rfl

private theorem cost_2565_551_join0_16 : P1_7_1_3.blockEstimate 2565 551 2599 256 = 107488078861 :=
  @P1_7_1_3.block_append 2565 551 2599 2727 128 128 256 59347484091 48140594770 107488078861 cost_2565_551_block16 cost_2565_551_block17 rfl rfl rfl

private theorem cost_2565_551_join0_18 : P1_7_1_3.blockEstimate 2565 551 2855 256 = 63991038901 :=
  @P1_7_1_3.block_append 2565 551 2855 2983 128 128 256 37141827764 26849211137 63991038901 cost_2565_551_block18 cost_2565_551_block19 rfl rfl rfl

private theorem cost_2565_551_join0_20 : P1_7_1_3.blockEstimate 2565 551 3111 256 = 27745016024 :=
  @P1_7_1_3.block_append 2565 551 3111 3239 128 128 256 17668456984 10076559040 27745016024 cost_2565_551_block20 cost_2565_551_block21 rfl rfl rfl

private theorem cost_2565_551_join0_22 : P1_7_1_3.blockEstimate 2565 551 3367 256 = 5518538112 :=
  @P1_7_1_3.block_append 2565 551 3367 3495 128 128 256 4457000640 1061537472 5518538112 cost_2565_551_block22 cost_2565_551_block23 rfl rfl rfl

private theorem cost_2565_551_join1_0 : P1_7_1_3.blockEstimate 2565 551 551 512 = 49091260032 :=
  @P1_7_1_3.block_append 2565 551 551 807 256 256 512 6715471680 42375788352 49091260032 cost_2565_551_join0_0 cost_2565_551_join0_2 rfl rfl rfl

private theorem cost_2565_551_join1_2 : P1_7_1_3.blockEstimate 2565 551 1063 512 = 244298403834 :=
  @P1_7_1_3.block_append 2565 551 1063 1319 256 256 512 98563585530 145734818304 244298403834 cost_2565_551_join0_4 cost_2565_551_join0_6 rfl rfl rfl

private theorem cost_2565_551_join1_4 : P1_7_1_3.blockEstimate 2565 551 1575 512 = 358955725824 :=
  @P1_7_1_3.block_append 2565 551 1575 1831 256 256 512 174404196864 184551528960 358955725824 cost_2565_551_join0_8 cost_2565_551_join0_10 rfl rfl rfl

private theorem cost_2565_551_join1_6 : P1_7_1_3.blockEstimate 2565 551 2087 512 = 325461996657 :=
  @P1_7_1_3.block_append 2565 551 2087 2343 256 256 512 176176814592 149285182065 325461996657 cost_2565_551_join0_12 cost_2565_551_join0_14 rfl rfl rfl

private theorem cost_2565_551_join1_8 : P1_7_1_3.blockEstimate 2565 551 2599 512 = 171479117762 :=
  @P1_7_1_3.block_append 2565 551 2599 2855 256 256 512 107488078861 63991038901 171479117762 cost_2565_551_join0_16 cost_2565_551_join0_18 rfl rfl rfl

private theorem cost_2565_551_join1_10 : P1_7_1_3.blockEstimate 2565 551 3111 512 = 33263554136 :=
  @P1_7_1_3.block_append 2565 551 3111 3367 256 256 512 27745016024 5518538112 33263554136 cost_2565_551_join0_20 cost_2565_551_join0_22 rfl rfl rfl

private theorem cost_2565_551_join2_0 : P1_7_1_3.blockEstimate 2565 551 551 1024 = 293389663866 :=
  @P1_7_1_3.block_append 2565 551 551 1063 512 512 1024 49091260032 244298403834 293389663866 cost_2565_551_join1_0 cost_2565_551_join1_2 rfl rfl rfl

private theorem cost_2565_551_join2_2 : P1_7_1_3.blockEstimate 2565 551 1575 1024 = 684417722481 :=
  @P1_7_1_3.block_append 2565 551 1575 2087 512 512 1024 358955725824 325461996657 684417722481 cost_2565_551_join1_4 cost_2565_551_join1_6 rfl rfl rfl

private theorem cost_2565_551_join2_4 : P1_7_1_3.blockEstimate 2565 551 2599 1024 = 204742671898 :=
  @P1_7_1_3.block_append 2565 551 2599 3111 512 512 1024 171479117762 33263554136 204742671898 cost_2565_551_join1_8 cost_2565_551_join1_10 rfl rfl rfl

private theorem cost_2565_551_join3_0 : P1_7_1_3.blockEstimate 2565 551 551 2048 = 977807386347 :=
  @P1_7_1_3.block_append 2565 551 551 1575 1024 1024 2048 293389663866 684417722481 977807386347 cost_2565_551_join2_0 cost_2565_551_join2_2 rfl rfl rfl

private theorem cost_2565_551_join3_2 : P1_7_1_3.blockEstimate 2565 551 2599 1068 = 204762632586 :=
  @P1_7_1_3.block_append 2565 551 2599 3623 1024 44 1068 204742671898 19960688 204762632586 cost_2565_551_join2_4 cost_2565_551_block24 rfl rfl rfl

private theorem cost_2565_551_join4_0 : P1_7_1_3.blockEstimate 2565 551 551 3116 = 1182570018933 :=
  @P1_7_1_3.block_append 2565 551 551 2599 2048 1068 3116 977807386347 204762632586 1182570018933 cost_2565_551_join3_0 cost_2565_551_join3_2 rfl rfl rfl

private theorem cost_2565_551_total : P1_7_1_3.momentEstimate 2565 551 = 1182570018933 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2565 + 551 = 3116 by decide]
  exact cost_2565_551_join4_0

theorem moment2565_551 : P1_7_1.groupedPoleMoment 2565 551 ≤ 1182570018933 :=
  (P1_7_1_3.grouped_bound 2565 551).trans_eq cost_2565_551_total
private theorem cost_2628_565_block0 : P1_7_1_3.blockEstimate 2628 565 565 128 = 906116640 := by decide +kernel

private theorem cost_2628_565_block1 : P1_7_1_3.blockEstimate 2628 565 693 128 = 5987585568 := by decide +kernel

private theorem cost_2628_565_block2 : P1_7_1_3.blockEstimate 2628 565 821 128 = 15369264672 := by decide +kernel

private theorem cost_2628_565_block3 : P1_7_1_3.blockEstimate 2628 565 949 128 = 28245847584 := by decide +kernel

private theorem cost_2628_565_block4 : P1_7_1_3.blockEstimate 2628 565 1077 128 = 43670918261 := by decide +kernel

private theorem cost_2628_565_block5 : P1_7_1_3.blockEstimate 2628 565 1205 128 = 58738936640 := by decide +kernel

private theorem cost_2628_565_block6 : P1_7_1_3.blockEstimate 2628 565 1333 128 = 71485147968 := by decide +kernel

private theorem cost_2628_565_block7 : P1_7_1_3.blockEstimate 2628 565 1461 128 = 81857383232 := by decide +kernel

private theorem cost_2628_565_block8 : P1_7_1_3.blockEstimate 2628 565 1589 128 = 89855642432 := by decide +kernel

private theorem cost_2628_565_block9 : P1_7_1_3.blockEstimate 2628 565 1717 128 = 95479925568 := by decide +kernel

private theorem cost_2628_565_block10 : P1_7_1_3.blockEstimate 2628 565 1845 128 = 98730232640 := by decide +kernel

private theorem cost_2628_565_block11 : P1_7_1_3.blockEstimate 2628 565 1973 128 = 99606563648 := by decide +kernel

private theorem cost_2628_565_block12 : P1_7_1_3.blockEstimate 2628 565 2101 128 = 98108918592 := by decide +kernel

private theorem cost_2628_565_block13 : P1_7_1_3.blockEstimate 2628 565 2229 128 = 94237297472 := by decide +kernel

private theorem cost_2628_565_block14 : P1_7_1_3.blockEstimate 2628 565 2357 128 = 87991700288 := by decide +kernel

private theorem cost_2628_565_block15 : P1_7_1_3.blockEstimate 2628 565 2485 128 = 79372127040 := by decide +kernel

private theorem cost_2628_565_block16 : P1_7_1_3.blockEstimate 2628 565 2613 128 = 68576358483 := by decide +kernel

private theorem cost_2628_565_block17 : P1_7_1_3.blockEstimate 2628 565 2741 128 = 56880686893 := by decide +kernel

private theorem cost_2628_565_block18 : P1_7_1_3.blockEstimate 2628 565 2869 128 = 45168992264 := by decide +kernel

private theorem cost_2628_565_block19 : P1_7_1_3.blockEstimate 2628 565 2997 128 = 33959724831 := by decide +kernel

private theorem cost_2628_565_block20 : P1_7_1_3.blockEstimate 2628 565 3125 128 = 23710612695 := by decide +kernel

private theorem cost_2628_565_block21 : P1_7_1_3.blockEstimate 2628 565 3253 128 = 14820834352 := by decide +kernel

private theorem cost_2628_565_block22 : P1_7_1_3.blockEstimate 2628 565 3381 128 = 7789230128 := by decide +kernel

private theorem cost_2628_565_block23 : P1_7_1_3.blockEstimate 2628 565 3509 128 = 2896393264 := by decide +kernel

private theorem cost_2628_565_block24 : P1_7_1_3.blockEstimate 2628 565 3637 121 = 393947783 := by decide +kernel

private theorem cost_2628_565_join0_0 : P1_7_1_3.blockEstimate 2628 565 565 256 = 6893702208 :=
  @P1_7_1_3.block_append 2628 565 565 693 128 128 256 906116640 5987585568 6893702208 cost_2628_565_block0 cost_2628_565_block1 rfl rfl rfl

private theorem cost_2628_565_join0_2 : P1_7_1_3.blockEstimate 2628 565 821 256 = 43615112256 :=
  @P1_7_1_3.block_append 2628 565 821 949 128 128 256 15369264672 28245847584 43615112256 cost_2628_565_block2 cost_2628_565_block3 rfl rfl rfl

private theorem cost_2628_565_join0_4 : P1_7_1_3.blockEstimate 2628 565 1077 256 = 102409854901 :=
  @P1_7_1_3.block_append 2628 565 1077 1205 128 128 256 43670918261 58738936640 102409854901 cost_2628_565_block4 cost_2628_565_block5 rfl rfl rfl

private theorem cost_2628_565_join0_6 : P1_7_1_3.blockEstimate 2628 565 1333 256 = 153342531200 :=
  @P1_7_1_3.block_append 2628 565 1333 1461 128 128 256 71485147968 81857383232 153342531200 cost_2628_565_block6 cost_2628_565_block7 rfl rfl rfl

private theorem cost_2628_565_join0_8 : P1_7_1_3.blockEstimate 2628 565 1589 256 = 185335568000 :=
  @P1_7_1_3.block_append 2628 565 1589 1717 128 128 256 89855642432 95479925568 185335568000 cost_2628_565_block8 cost_2628_565_block9 rfl rfl rfl

private theorem cost_2628_565_join0_10 : P1_7_1_3.blockEstimate 2628 565 1845 256 = 198336796288 :=
  @P1_7_1_3.block_append 2628 565 1845 1973 128 128 256 98730232640 99606563648 198336796288 cost_2628_565_block10 cost_2628_565_block11 rfl rfl rfl

private theorem cost_2628_565_join0_12 : P1_7_1_3.blockEstimate 2628 565 2101 256 = 192346216064 :=
  @P1_7_1_3.block_append 2628 565 2101 2229 128 128 256 98108918592 94237297472 192346216064 cost_2628_565_block12 cost_2628_565_block13 rfl rfl rfl

private theorem cost_2628_565_join0_14 : P1_7_1_3.blockEstimate 2628 565 2357 256 = 167363827328 :=
  @P1_7_1_3.block_append 2628 565 2357 2485 128 128 256 87991700288 79372127040 167363827328 cost_2628_565_block14 cost_2628_565_block15 rfl rfl rfl

private theorem cost_2628_565_join0_16 : P1_7_1_3.blockEstimate 2628 565 2613 256 = 125457045376 :=
  @P1_7_1_3.block_append 2628 565 2613 2741 128 128 256 68576358483 56880686893 125457045376 cost_2628_565_block16 cost_2628_565_block17 rfl rfl rfl

private theorem cost_2628_565_join0_18 : P1_7_1_3.blockEstimate 2628 565 2869 256 = 79128717095 :=
  @P1_7_1_3.block_append 2628 565 2869 2997 128 128 256 45168992264 33959724831 79128717095 cost_2628_565_block18 cost_2628_565_block19 rfl rfl rfl

private theorem cost_2628_565_join0_20 : P1_7_1_3.blockEstimate 2628 565 3125 256 = 38531447047 :=
  @P1_7_1_3.block_append 2628 565 3125 3253 128 128 256 23710612695 14820834352 38531447047 cost_2628_565_block20 cost_2628_565_block21 rfl rfl rfl

private theorem cost_2628_565_join0_22 : P1_7_1_3.blockEstimate 2628 565 3381 256 = 10685623392 :=
  @P1_7_1_3.block_append 2628 565 3381 3509 128 128 256 7789230128 2896393264 10685623392 cost_2628_565_block22 cost_2628_565_block23 rfl rfl rfl

private theorem cost_2628_565_join1_0 : P1_7_1_3.blockEstimate 2628 565 565 512 = 50508814464 :=
  @P1_7_1_3.block_append 2628 565 565 821 256 256 512 6893702208 43615112256 50508814464 cost_2628_565_join0_0 cost_2628_565_join0_2 rfl rfl rfl

private theorem cost_2628_565_join1_2 : P1_7_1_3.blockEstimate 2628 565 1077 512 = 255752386101 :=
  @P1_7_1_3.block_append 2628 565 1077 1333 256 256 512 102409854901 153342531200 255752386101 cost_2628_565_join0_4 cost_2628_565_join0_6 rfl rfl rfl

private theorem cost_2628_565_join1_4 : P1_7_1_3.blockEstimate 2628 565 1589 512 = 383672364288 :=
  @P1_7_1_3.block_append 2628 565 1589 1845 256 256 512 185335568000 198336796288 383672364288 cost_2628_565_join0_8 cost_2628_565_join0_10 rfl rfl rfl

private theorem cost_2628_565_join1_6 : P1_7_1_3.blockEstimate 2628 565 2101 512 = 359710043392 :=
  @P1_7_1_3.block_append 2628 565 2101 2357 256 256 512 192346216064 167363827328 359710043392 cost_2628_565_join0_12 cost_2628_565_join0_14 rfl rfl rfl

private theorem cost_2628_565_join1_8 : P1_7_1_3.blockEstimate 2628 565 2613 512 = 204585762471 :=
  @P1_7_1_3.block_append 2628 565 2613 2869 256 256 512 125457045376 79128717095 204585762471 cost_2628_565_join0_16 cost_2628_565_join0_18 rfl rfl rfl

private theorem cost_2628_565_join1_10 : P1_7_1_3.blockEstimate 2628 565 3125 512 = 49217070439 :=
  @P1_7_1_3.block_append 2628 565 3125 3381 256 256 512 38531447047 10685623392 49217070439 cost_2628_565_join0_20 cost_2628_565_join0_22 rfl rfl rfl

private theorem cost_2628_565_join2_0 : P1_7_1_3.blockEstimate 2628 565 565 1024 = 306261200565 :=
  @P1_7_1_3.block_append 2628 565 565 1077 512 512 1024 50508814464 255752386101 306261200565 cost_2628_565_join1_0 cost_2628_565_join1_2 rfl rfl rfl

private theorem cost_2628_565_join2_2 : P1_7_1_3.blockEstimate 2628 565 1589 1024 = 743382407680 :=
  @P1_7_1_3.block_append 2628 565 1589 2101 512 512 1024 383672364288 359710043392 743382407680 cost_2628_565_join1_4 cost_2628_565_join1_6 rfl rfl rfl

private theorem cost_2628_565_join2_4 : P1_7_1_3.blockEstimate 2628 565 2613 1024 = 253802832910 :=
  @P1_7_1_3.block_append 2628 565 2613 3125 512 512 1024 204585762471 49217070439 253802832910 cost_2628_565_join1_8 cost_2628_565_join1_10 rfl rfl rfl

private theorem cost_2628_565_join3_0 : P1_7_1_3.blockEstimate 2628 565 565 2048 = 1049643608245 :=
  @P1_7_1_3.block_append 2628 565 565 1589 1024 1024 2048 306261200565 743382407680 1049643608245 cost_2628_565_join2_0 cost_2628_565_join2_2 rfl rfl rfl

private theorem cost_2628_565_join3_2 : P1_7_1_3.blockEstimate 2628 565 2613 1145 = 254196780693 :=
  @P1_7_1_3.block_append 2628 565 2613 3637 1024 121 1145 253802832910 393947783 254196780693 cost_2628_565_join2_4 cost_2628_565_block24 rfl rfl rfl

private theorem cost_2628_565_join4_0 : P1_7_1_3.blockEstimate 2628 565 565 3193 = 1303840388938 :=
  @P1_7_1_3.block_append 2628 565 565 2613 2048 1145 3193 1049643608245 254196780693 1303840388938 cost_2628_565_join3_0 cost_2628_565_join3_2 rfl rfl rfl

private theorem cost_2628_565_total : P1_7_1_3.momentEstimate 2628 565 = 1303840388938 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2628 + 565 = 3193 by decide]
  exact cost_2628_565_join4_0

theorem moment2628_565 : P1_7_1.groupedPoleMoment 2628 565 ≤ 1303840388938 :=
  (P1_7_1_3.grouped_bound 2628 565).trans_eq cost_2628_565_total
private theorem cost_2631_566_block0 : P1_7_1_3.blockEstimate 2631 566 566 128 = 907189920 := by decide +kernel

private theorem cost_2631_566_block1 : P1_7_1_3.blockEstimate 2631 566 694 128 = 5994999456 := by decide +kernel

private theorem cost_2631_566_block2 : P1_7_1_3.blockEstimate 2631 566 822 128 = 15389310624 := by decide +kernel

private theorem cost_2631_566_block3 : P1_7_1_3.blockEstimate 2631 566 950 128 = 28284817056 := by decide +kernel

private theorem cost_2631_566_block4 : P1_7_1_3.blockEstimate 2631 566 1078 128 = 43740487134 := by decide +kernel

private theorem cost_2631_566_block5 : P1_7_1_3.blockEstimate 2631 566 1206 128 = 58864651776 := by decide +kernel

private theorem cost_2631_566_block6 : P1_7_1_3.blockEstimate 2631 566 1334 128 = 71665896960 := by decide +kernel

private theorem cost_2631_566_block7 : P1_7_1_3.blockEstimate 2631 566 1462 128 = 82088971776 := by decide +kernel

private theorem cost_2631_566_block8 : P1_7_1_3.blockEstimate 2631 566 1590 128 = 90133876224 := by decide +kernel

private theorem cost_2631_566_block9 : P1_7_1_3.blockEstimate 2631 566 1718 128 = 95800610304 := by decide +kernel

private theorem cost_2631_566_block10 : P1_7_1_3.blockEstimate 2631 566 1846 128 = 99089174016 := by decide +kernel

private theorem cost_2631_566_block11 : P1_7_1_3.blockEstimate 2631 566 1974 128 = 99999567360 := by decide +kernel

private theorem cost_2631_566_block12 : P1_7_1_3.blockEstimate 2631 566 2102 128 = 98531790336 := by decide +kernel

private theorem cost_2631_566_block13 : P1_7_1_3.blockEstimate 2631 566 2230 128 = 94685842944 := by decide +kernel

private theorem cost_2631_566_block14 : P1_7_1_3.blockEstimate 2631 566 2358 128 = 88461725184 := by decide +kernel

private theorem cost_2631_566_block15 : P1_7_1_3.blockEstimate 2631 566 2486 128 = 79859437056 := by decide +kernel

private theorem cost_2631_566_block16 : P1_7_1_3.blockEstimate 2631 566 2614 128 = 69066348895 := by decide +kernel

private theorem cost_2631_566_block17 : P1_7_1_3.blockEstimate 2631 566 2742 128 = 57348183637 := by decide +kernel

private theorem cost_2631_566_block18 : P1_7_1_3.blockEstimate 2631 566 2870 128 = 45602301744 := by decide +kernel

private theorem cost_2631_566_block19 : P1_7_1_3.blockEstimate 2631 566 2998 128 = 34348192481 := by decide +kernel

private theorem cost_2631_566_block20 : P1_7_1_3.blockEstimate 2631 566 3126 128 = 24045755975 := by decide +kernel

private theorem cost_2631_566_block21 : P1_7_1_3.blockEstimate 2631 566 3254 128 = 15091558736 := by decide +kernel

private theorem cost_2631_566_block22 : P1_7_1_3.blockEstimate 2631 566 3382 128 = 7987772752 := by decide +kernel

private theorem cost_2631_566_block23 : P1_7_1_3.blockEstimate 2631 566 3510 128 = 3018035536 := by decide +kernel

private theorem cost_2631_566_block24 : P1_7_1_3.blockEstimate 2631 566 3638 125 = 434005328 := by decide +kernel

private theorem cost_2631_566_join0_0 : P1_7_1_3.blockEstimate 2631 566 566 256 = 6902189376 :=
  @P1_7_1_3.block_append 2631 566 566 694 128 128 256 907189920 5994999456 6902189376 cost_2631_566_block0 cost_2631_566_block1 rfl rfl rfl

private theorem cost_2631_566_join0_2 : P1_7_1_3.blockEstimate 2631 566 822 256 = 43674127680 :=
  @P1_7_1_3.block_append 2631 566 822 950 128 128 256 15389310624 28284817056 43674127680 cost_2631_566_block2 cost_2631_566_block3 rfl rfl rfl

private theorem cost_2631_566_join0_4 : P1_7_1_3.blockEstimate 2631 566 1078 256 = 102605138910 :=
  @P1_7_1_3.block_append 2631 566 1078 1206 128 128 256 43740487134 58864651776 102605138910 cost_2631_566_block4 cost_2631_566_block5 rfl rfl rfl

private theorem cost_2631_566_join0_6 : P1_7_1_3.blockEstimate 2631 566 1334 256 = 153754868736 :=
  @P1_7_1_3.block_append 2631 566 1334 1462 128 128 256 71665896960 82088971776 153754868736 cost_2631_566_block6 cost_2631_566_block7 rfl rfl rfl

private theorem cost_2631_566_join0_8 : P1_7_1_3.blockEstimate 2631 566 1590 256 = 185934486528 :=
  @P1_7_1_3.block_append 2631 566 1590 1718 128 128 256 90133876224 95800610304 185934486528 cost_2631_566_block8 cost_2631_566_block9 rfl rfl rfl

private theorem cost_2631_566_join0_10 : P1_7_1_3.blockEstimate 2631 566 1846 256 = 199088741376 :=
  @P1_7_1_3.block_append 2631 566 1846 1974 128 128 256 99089174016 99999567360 199088741376 cost_2631_566_block10 cost_2631_566_block11 rfl rfl rfl

private theorem cost_2631_566_join0_12 : P1_7_1_3.blockEstimate 2631 566 2102 256 = 193217633280 :=
  @P1_7_1_3.block_append 2631 566 2102 2230 128 128 256 98531790336 94685842944 193217633280 cost_2631_566_block12 cost_2631_566_block13 rfl rfl rfl

private theorem cost_2631_566_join0_14 : P1_7_1_3.blockEstimate 2631 566 2358 256 = 168321162240 :=
  @P1_7_1_3.block_append 2631 566 2358 2486 128 128 256 88461725184 79859437056 168321162240 cost_2631_566_block14 cost_2631_566_block15 rfl rfl rfl

private theorem cost_2631_566_join0_16 : P1_7_1_3.blockEstimate 2631 566 2614 256 = 126414532532 :=
  @P1_7_1_3.block_append 2631 566 2614 2742 128 128 256 69066348895 57348183637 126414532532 cost_2631_566_block16 cost_2631_566_block17 rfl rfl rfl

private theorem cost_2631_566_join0_18 : P1_7_1_3.blockEstimate 2631 566 2870 256 = 79950494225 :=
  @P1_7_1_3.block_append 2631 566 2870 2998 128 128 256 45602301744 34348192481 79950494225 cost_2631_566_block18 cost_2631_566_block19 rfl rfl rfl

private theorem cost_2631_566_join0_20 : P1_7_1_3.blockEstimate 2631 566 3126 256 = 39137314711 :=
  @P1_7_1_3.block_append 2631 566 3126 3254 128 128 256 24045755975 15091558736 39137314711 cost_2631_566_block20 cost_2631_566_block21 rfl rfl rfl

private theorem cost_2631_566_join0_22 : P1_7_1_3.blockEstimate 2631 566 3382 256 = 11005808288 :=
  @P1_7_1_3.block_append 2631 566 3382 3510 128 128 256 7987772752 3018035536 11005808288 cost_2631_566_block22 cost_2631_566_block23 rfl rfl rfl

private theorem cost_2631_566_join1_0 : P1_7_1_3.blockEstimate 2631 566 566 512 = 50576317056 :=
  @P1_7_1_3.block_append 2631 566 566 822 256 256 512 6902189376 43674127680 50576317056 cost_2631_566_join0_0 cost_2631_566_join0_2 rfl rfl rfl

private theorem cost_2631_566_join1_2 : P1_7_1_3.blockEstimate 2631 566 1078 512 = 256360007646 :=
  @P1_7_1_3.block_append 2631 566 1078 1334 256 256 512 102605138910 153754868736 256360007646 cost_2631_566_join0_4 cost_2631_566_join0_6 rfl rfl rfl

private theorem cost_2631_566_join1_4 : P1_7_1_3.blockEstimate 2631 566 1590 512 = 385023227904 :=
  @P1_7_1_3.block_append 2631 566 1590 1846 256 256 512 185934486528 199088741376 385023227904 cost_2631_566_join0_8 cost_2631_566_join0_10 rfl rfl rfl

private theorem cost_2631_566_join1_6 : P1_7_1_3.blockEstimate 2631 566 2102 512 = 361538795520 :=
  @P1_7_1_3.block_append 2631 566 2102 2358 256 256 512 193217633280 168321162240 361538795520 cost_2631_566_join0_12 cost_2631_566_join0_14 rfl rfl rfl

private theorem cost_2631_566_join1_8 : P1_7_1_3.blockEstimate 2631 566 2614 512 = 206365026757 :=
  @P1_7_1_3.block_append 2631 566 2614 2870 256 256 512 126414532532 79950494225 206365026757 cost_2631_566_join0_16 cost_2631_566_join0_18 rfl rfl rfl

private theorem cost_2631_566_join1_10 : P1_7_1_3.blockEstimate 2631 566 3126 512 = 50143122999 :=
  @P1_7_1_3.block_append 2631 566 3126 3382 256 256 512 39137314711 11005808288 50143122999 cost_2631_566_join0_20 cost_2631_566_join0_22 rfl rfl rfl

private theorem cost_2631_566_join2_0 : P1_7_1_3.blockEstimate 2631 566 566 1024 = 306936324702 :=
  @P1_7_1_3.block_append 2631 566 566 1078 512 512 1024 50576317056 256360007646 306936324702 cost_2631_566_join1_0 cost_2631_566_join1_2 rfl rfl rfl

private theorem cost_2631_566_join2_2 : P1_7_1_3.blockEstimate 2631 566 1590 1024 = 746562023424 :=
  @P1_7_1_3.block_append 2631 566 1590 2102 512 512 1024 385023227904 361538795520 746562023424 cost_2631_566_join1_4 cost_2631_566_join1_6 rfl rfl rfl

private theorem cost_2631_566_join2_4 : P1_7_1_3.blockEstimate 2631 566 2614 1024 = 256508149756 :=
  @P1_7_1_3.block_append 2631 566 2614 3126 512 512 1024 206365026757 50143122999 256508149756 cost_2631_566_join1_8 cost_2631_566_join1_10 rfl rfl rfl

private theorem cost_2631_566_join3_0 : P1_7_1_3.blockEstimate 2631 566 566 2048 = 1053498348126 :=
  @P1_7_1_3.block_append 2631 566 566 1590 1024 1024 2048 306936324702 746562023424 1053498348126 cost_2631_566_join2_0 cost_2631_566_join2_2 rfl rfl rfl

private theorem cost_2631_566_join3_2 : P1_7_1_3.blockEstimate 2631 566 2614 1149 = 256942155084 :=
  @P1_7_1_3.block_append 2631 566 2614 3638 1024 125 1149 256508149756 434005328 256942155084 cost_2631_566_join2_4 cost_2631_566_block24 rfl rfl rfl

private theorem cost_2631_566_join4_0 : P1_7_1_3.blockEstimate 2631 566 566 3197 = 1310440503210 :=
  @P1_7_1_3.block_append 2631 566 566 2614 2048 1149 3197 1053498348126 256942155084 1310440503210 cost_2631_566_join3_0 cost_2631_566_join3_2 rfl rfl rfl

private theorem cost_2631_566_total : P1_7_1_3.momentEstimate 2631 566 = 1310440503210 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2631 + 566 = 3197 by decide]
  exact cost_2631_566_join4_0

theorem moment2631_566 : P1_7_1.groupedPoleMoment 2631 566 ≤ 1310440503210 :=
  (P1_7_1_3.grouped_bound 2631 566).trans_eq cost_2631_566_total

end Research6966.HelperRescueCatalogue

end Merged6967_Near6967RescueMoment19

section Merged6967_Near6967RescueMoment2
set_option Elab.async false


set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem cost_348_76_block0 : P1_7_1_3.blockEstimate 348 76 76 128 = 84953869 := by decide +kernel

private theorem cost_348_76_block1 : P1_7_1_3.blockEstimate 348 76 204 128 = 224854784 := by decide +kernel

private theorem cost_348_76_block2 : P1_7_1_3.blockEstimate 348 76 332 128 = 102596793 := by decide +kernel

private theorem cost_348_76_block3 : P1_7_1_3.blockEstimate 348 76 460 40 = 1962940 := by decide +kernel

private theorem cost_348_76_join0_0 : P1_7_1_3.blockEstimate 348 76 76 256 = 309808653 :=
  @P1_7_1_3.block_append 348 76 76 204 128 128 256 84953869 224854784 309808653 cost_348_76_block0 cost_348_76_block1 rfl rfl rfl

private theorem cost_348_76_join0_2 : P1_7_1_3.blockEstimate 348 76 332 168 = 104559733 :=
  @P1_7_1_3.block_append 348 76 332 460 128 40 168 102596793 1962940 104559733 cost_348_76_block2 cost_348_76_block3 rfl rfl rfl

private theorem cost_348_76_join1_0 : P1_7_1_3.blockEstimate 348 76 76 424 = 414368386 :=
  @P1_7_1_3.block_append 348 76 76 332 256 168 424 309808653 104559733 414368386 cost_348_76_join0_0 cost_348_76_join0_2 rfl rfl rfl

private theorem cost_348_76_total : P1_7_1_3.momentEstimate 348 76 = 414368386 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 348 + 76 = 424 by decide]
  exact cost_348_76_join1_0

theorem moment348_76 : P1_7_1.groupedPoleMoment 348 76 ≤ 414368386 :=
  (P1_7_1_3.grouped_bound 348 76).trans_eq cost_348_76_total
private theorem cost_348_78_block0 : P1_7_1_3.blockEstimate 348 78 78 128 = 85571615 := by decide +kernel

private theorem cost_348_78_block1 : P1_7_1_3.blockEstimate 348 78 206 128 = 229112640 := by decide +kernel

private theorem cost_348_78_block2 : P1_7_1_3.blockEstimate 348 78 334 128 = 105777710 := by decide +kernel

private theorem cost_348_78_block3 : P1_7_1_3.blockEstimate 348 78 462 42 = 2254428 := by decide +kernel

private theorem cost_348_78_join0_0 : P1_7_1_3.blockEstimate 348 78 78 256 = 314684255 :=
  @P1_7_1_3.block_append 348 78 78 206 128 128 256 85571615 229112640 314684255 cost_348_78_block0 cost_348_78_block1 rfl rfl rfl

private theorem cost_348_78_join0_2 : P1_7_1_3.blockEstimate 348 78 334 170 = 108032138 :=
  @P1_7_1_3.block_append 348 78 334 462 128 42 170 105777710 2254428 108032138 cost_348_78_block2 cost_348_78_block3 rfl rfl rfl

private theorem cost_348_78_join1_0 : P1_7_1_3.blockEstimate 348 78 78 426 = 422716393 :=
  @P1_7_1_3.block_append 348 78 78 334 256 170 426 314684255 108032138 422716393 cost_348_78_join0_0 cost_348_78_join0_2 rfl rfl rfl

private theorem cost_348_78_total : P1_7_1_3.momentEstimate 348 78 = 422716393 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 348 + 78 = 426 by decide]
  exact cost_348_78_join1_0

theorem moment348_78 : P1_7_1.groupedPoleMoment 348 78 ≤ 422716393 :=
  (P1_7_1_3.grouped_bound 348 78).trans_eq cost_348_78_total
private theorem cost_349_74_block0 : P1_7_1_3.blockEstimate 349 74 74 128 = 84616375 := by decide +kernel

private theorem cost_349_74_block1 : P1_7_1_3.blockEstimate 349 74 202 128 = 222009600 := by decide +kernel

private theorem cost_349_74_block2 : P1_7_1_3.blockEstimate 349 74 330 128 = 101237359 := by decide +kernel

private theorem cost_349_74_block3 : P1_7_1_3.blockEstimate 349 74 458 39 = 1832500 := by decide +kernel

private theorem cost_349_74_join0_0 : P1_7_1_3.blockEstimate 349 74 74 256 = 306625975 :=
  @P1_7_1_3.block_append 349 74 74 202 128 128 256 84616375 222009600 306625975 cost_349_74_block0 cost_349_74_block1 rfl rfl rfl

private theorem cost_349_74_join0_2 : P1_7_1_3.blockEstimate 349 74 330 167 = 103069859 :=
  @P1_7_1_3.block_append 349 74 330 458 128 39 167 101237359 1832500 103069859 cost_349_74_block2 cost_349_74_block3 rfl rfl rfl

private theorem cost_349_74_join1_0 : P1_7_1_3.blockEstimate 349 74 74 423 = 409695834 :=
  @P1_7_1_3.block_append 349 74 74 330 256 167 423 306625975 103069859 409695834 cost_349_74_join0_0 cost_349_74_join0_2 rfl rfl rfl

private theorem cost_349_74_total : P1_7_1_3.momentEstimate 349 74 = 409695834 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 349 + 74 = 423 by decide]
  exact cost_349_74_join1_0

theorem moment349_74 : P1_7_1.groupedPoleMoment 349 74 ≤ 409695834 :=
  (P1_7_1_3.grouped_bound 349 74).trans_eq cost_349_74_total
private theorem cost_349_76_block0 : P1_7_1_3.blockEstimate 349 76 76 128 = 85288203 := by decide +kernel

private theorem cost_349_76_block1 : P1_7_1_3.blockEstimate 349 76 204 128 = 226377536 := by decide +kernel

private theorem cost_349_76_block2 : P1_7_1_3.blockEstimate 349 76 332 128 = 104421650 := by decide +kernel

private theorem cost_349_76_block3 : P1_7_1_3.blockEstimate 349 76 460 41 = 2111824 := by decide +kernel

private theorem cost_349_76_join0_0 : P1_7_1_3.blockEstimate 349 76 76 256 = 311665739 :=
  @P1_7_1_3.block_append 349 76 76 204 128 128 256 85288203 226377536 311665739 cost_349_76_block0 cost_349_76_block1 rfl rfl rfl

private theorem cost_349_76_join0_2 : P1_7_1_3.blockEstimate 349 76 332 169 = 106533474 :=
  @P1_7_1_3.block_append 349 76 332 460 128 41 169 104421650 2111824 106533474 cost_349_76_block2 cost_349_76_block3 rfl rfl rfl

private theorem cost_349_76_join1_0 : P1_7_1_3.blockEstimate 349 76 76 425 = 418199213 :=
  @P1_7_1_3.block_append 349 76 76 332 256 169 425 311665739 106533474 418199213 cost_349_76_join0_0 cost_349_76_join0_2 rfl rfl rfl

private theorem cost_349_76_total : P1_7_1_3.momentEstimate 349 76 = 418199213 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 349 + 76 = 425 by decide]
  exact cost_349_76_join1_0

theorem moment349_76 : P1_7_1.groupedPoleMoment 349 76 ≤ 418199213 :=
  (P1_7_1_3.grouped_bound 349 76).trans_eq cost_349_76_total
private theorem cost_349_78_block0 : P1_7_1_3.blockEstimate 349 78 78 128 = 85908550 := by decide +kernel

private theorem cost_349_78_block1 : P1_7_1_3.blockEstimate 349 78 206 128 = 230664832 := by decide +kernel

private theorem cost_349_78_block2 : P1_7_1_3.blockEstimate 349 78 334 128 = 107636359 := by decide +kernel

private theorem cost_349_78_block3 : P1_7_1_3.blockEstimate 349 78 462 43 = 2417547 := by decide +kernel

private theorem cost_349_78_join0_0 : P1_7_1_3.blockEstimate 349 78 78 256 = 316573382 :=
  @P1_7_1_3.block_append 349 78 78 206 128 128 256 85908550 230664832 316573382 cost_349_78_block0 cost_349_78_block1 rfl rfl rfl

private theorem cost_349_78_join0_2 : P1_7_1_3.blockEstimate 349 78 334 171 = 110053906 :=
  @P1_7_1_3.block_append 349 78 334 462 128 43 171 107636359 2417547 110053906 cost_349_78_block2 cost_349_78_block3 rfl rfl rfl

private theorem cost_349_78_join1_0 : P1_7_1_3.blockEstimate 349 78 78 427 = 426627288 :=
  @P1_7_1_3.block_append 349 78 78 334 256 171 427 316573382 110053906 426627288 cost_349_78_join0_0 cost_349_78_join0_2 rfl rfl rfl

private theorem cost_349_78_total : P1_7_1_3.momentEstimate 349 78 = 426627288 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 349 + 78 = 427 by decide]
  exact cost_349_78_join1_0

theorem moment349_78 : P1_7_1.groupedPoleMoment 349 78 ≤ 426627288 :=
  (P1_7_1_3.grouped_bound 349 78).trans_eq cost_349_78_total
private theorem cost_369_80_block0 : P1_7_1_3.blockEstimate 369 80 80 128 = 93266316 := by decide +kernel

private theorem cost_369_80_block1 : P1_7_1_3.blockEstimate 369 80 208 128 = 266493888 := by decide +kernel

private theorem cost_369_80_block2 : P1_7_1_3.blockEstimate 369 80 336 128 = 152098567 := by decide +kernel

private theorem cost_369_80_block3 : P1_7_1_3.blockEstimate 369 80 464 65 = 8309209 := by decide +kernel

private theorem cost_369_80_join0_0 : P1_7_1_3.blockEstimate 369 80 80 256 = 359760204 :=
  @P1_7_1_3.block_append 369 80 80 208 128 128 256 93266316 266493888 359760204 cost_369_80_block0 cost_369_80_block1 rfl rfl rfl

private theorem cost_369_80_join0_2 : P1_7_1_3.blockEstimate 369 80 336 193 = 160407776 :=
  @P1_7_1_3.block_append 369 80 336 464 128 65 193 152098567 8309209 160407776 cost_369_80_block2 cost_369_80_block3 rfl rfl rfl

private theorem cost_369_80_join1_0 : P1_7_1_3.blockEstimate 369 80 80 449 = 520167980 :=
  @P1_7_1_3.block_append 369 80 80 336 256 193 449 359760204 160407776 520167980 cost_369_80_join0_0 cost_369_80_join0_2 rfl rfl rfl

private theorem cost_369_80_total : P1_7_1_3.momentEstimate 369 80 = 520167980 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 369 + 80 = 449 by decide]
  exact cost_369_80_join1_0

theorem moment369_80 : P1_7_1.groupedPoleMoment 369 80 ≤ 520167980 :=
  (P1_7_1_3.grouped_bound 369 80).trans_eq cost_369_80_total
private theorem cost_369_82_block0 : P1_7_1_3.blockEstimate 369 82 82 128 = 93834405 := by decide +kernel

private theorem cost_369_82_block1 : P1_7_1_3.blockEstimate 369 82 210 128 = 271188224 := by decide +kernel

private theorem cost_369_82_block2 : P1_7_1_3.blockEstimate 369 82 338 128 = 156061936 := by decide +kernel

private theorem cost_369_82_block3 : P1_7_1_3.blockEstimate 369 82 466 67 = 9056801 := by decide +kernel

private theorem cost_369_82_join0_0 : P1_7_1_3.blockEstimate 369 82 82 256 = 365022629 :=
  @P1_7_1_3.block_append 369 82 82 210 128 128 256 93834405 271188224 365022629 cost_369_82_block0 cost_369_82_block1 rfl rfl rfl

private theorem cost_369_82_join0_2 : P1_7_1_3.blockEstimate 369 82 338 195 = 165118737 :=
  @P1_7_1_3.block_append 369 82 338 466 128 67 195 156061936 9056801 165118737 cost_369_82_block2 cost_369_82_block3 rfl rfl rfl

private theorem cost_369_82_join1_0 : P1_7_1_3.blockEstimate 369 82 82 451 = 530141366 :=
  @P1_7_1_3.block_append 369 82 82 338 256 195 451 365022629 165118737 530141366 cost_369_82_join0_0 cost_369_82_join0_2 rfl rfl rfl

private theorem cost_369_82_total : P1_7_1_3.momentEstimate 369 82 = 530141366 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 369 + 82 = 451 by decide]
  exact cost_369_82_join1_0

theorem moment369_82 : P1_7_1.groupedPoleMoment 369 82 ≤ 530141366 :=
  (P1_7_1_3.grouped_bound 369 82).trans_eq cost_369_82_total
private theorem cost_372_81_block0 : P1_7_1_3.blockEstimate 372 81 81 128 = 94577980 := by decide +kernel

private theorem cost_372_81_block1 : P1_7_1_3.blockEstimate 372 81 209 128 = 273638592 := by decide +kernel

private theorem cost_372_81_block2 : P1_7_1_3.blockEstimate 372 81 337 128 = 160835205 := by decide +kernel

private theorem cost_372_81_block3 : P1_7_1_3.blockEstimate 372 81 465 69 = 9933897 := by decide +kernel

private theorem cost_372_81_join0_0 : P1_7_1_3.blockEstimate 372 81 81 256 = 368216572 :=
  @P1_7_1_3.block_append 372 81 81 209 128 128 256 94577980 273638592 368216572 cost_372_81_block0 cost_372_81_block1 rfl rfl rfl

private theorem cost_372_81_join0_2 : P1_7_1_3.blockEstimate 372 81 337 197 = 170769102 :=
  @P1_7_1_3.block_append 372 81 337 465 128 69 197 160835205 9933897 170769102 cost_372_81_block2 cost_372_81_block3 rfl rfl rfl

private theorem cost_372_81_join1_0 : P1_7_1_3.blockEstimate 372 81 81 453 = 538985674 :=
  @P1_7_1_3.block_append 372 81 81 337 256 197 453 368216572 170769102 538985674 cost_372_81_join0_0 cost_372_81_join0_2 rfl rfl rfl

private theorem cost_372_81_total : P1_7_1_3.momentEstimate 372 81 = 538985674 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 372 + 81 = 453 by decide]
  exact cost_372_81_join1_0

theorem moment372_81 : P1_7_1.groupedPoleMoment 372 81 ≤ 538985674 :=
  (P1_7_1_3.grouped_bound 372 81).trans_eq cost_372_81_total
private theorem cost_372_83_block0 : P1_7_1_3.blockEstimate 372 83 83 128 = 95127795 := by decide +kernel

private theorem cost_372_83_block1 : P1_7_1_3.blockEstimate 372 83 211 128 = 278371968 := by decide +kernel

private theorem cost_372_83_block2 : P1_7_1_3.blockEstimate 372 83 339 128 = 164915408 := by decide +kernel

private theorem cost_372_83_block3 : P1_7_1_3.blockEstimate 372 83 467 71 = 10774002 := by decide +kernel

private theorem cost_372_83_join0_0 : P1_7_1_3.blockEstimate 372 83 83 256 = 373499763 :=
  @P1_7_1_3.block_append 372 83 83 211 128 128 256 95127795 278371968 373499763 cost_372_83_block0 cost_372_83_block1 rfl rfl rfl

private theorem cost_372_83_join0_2 : P1_7_1_3.blockEstimate 372 83 339 199 = 175689410 :=
  @P1_7_1_3.block_append 372 83 339 467 128 71 199 164915408 10774002 175689410 cost_372_83_block2 cost_372_83_block3 rfl rfl rfl

private theorem cost_372_83_join1_0 : P1_7_1_3.blockEstimate 372 83 83 455 = 549189173 :=
  @P1_7_1_3.block_append 372 83 83 339 256 199 455 373499763 175689410 549189173 cost_372_83_join0_0 cost_372_83_join0_2 rfl rfl rfl

private theorem cost_372_83_total : P1_7_1_3.momentEstimate 372 83 = 549189173 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 372 + 83 = 455 by decide]
  exact cost_372_83_join1_0

theorem moment372_83 : P1_7_1.groupedPoleMoment 372 83 ≤ 549189173 :=
  (P1_7_1_3.grouped_bound 372 83).trans_eq cost_372_83_total
private theorem cost_373_83_block0 : P1_7_1_3.blockEstimate 373 83 83 128 = 95470375 := by decide +kernel

private theorem cost_373_83_block1 : P1_7_1_3.blockEstimate 373 83 211 128 = 279995520 := by decide +kernel

private theorem cost_373_83_block2 : P1_7_1_3.blockEstimate 373 83 339 128 = 167232504 := by decide +kernel

private theorem cost_373_83_block3 : P1_7_1_3.blockEstimate 373 83 467 72 = 11243634 := by decide +kernel

private theorem cost_373_83_join0_0 : P1_7_1_3.blockEstimate 373 83 83 256 = 375465895 :=
  @P1_7_1_3.block_append 373 83 83 211 128 128 256 95470375 279995520 375465895 cost_373_83_block0 cost_373_83_block1 rfl rfl rfl

private theorem cost_373_83_join0_2 : P1_7_1_3.blockEstimate 373 83 339 200 = 178476138 :=
  @P1_7_1_3.block_append 373 83 339 467 128 72 200 167232504 11243634 178476138 cost_373_83_block2 cost_373_83_block3 rfl rfl rfl

private theorem cost_373_83_join1_0 : P1_7_1_3.blockEstimate 373 83 83 456 = 553942033 :=
  @P1_7_1_3.block_append 373 83 83 339 256 200 456 375465895 178476138 553942033 cost_373_83_join0_0 cost_373_83_join0_2 rfl rfl rfl

private theorem cost_373_83_total : P1_7_1_3.momentEstimate 373 83 = 553942033 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 373 + 83 = 456 by decide]
  exact cost_373_83_join1_0

theorem moment373_83 : P1_7_1.groupedPoleMoment 373 83 ≤ 553942033 :=
  (P1_7_1_3.grouped_bound 373 83).trans_eq cost_373_83_total
private theorem cost_390_87_block0 : P1_7_1_3.blockEstimate 390 87 87 128 = 102318590 := by decide +kernel

private theorem cost_390_87_block1 : P1_7_1_3.blockEstimate 390 87 215 128 = 317771520 := by decide +kernel

private theorem cost_390_87_block2 : P1_7_1_3.blockEstimate 390 87 343 128 = 218189305 := by decide +kernel

private theorem cost_390_87_block3 : P1_7_1_3.blockEstimate 390 87 471 93 = 24398974 := by decide +kernel

private theorem cost_390_87_join0_0 : P1_7_1_3.blockEstimate 390 87 87 256 = 420090110 :=
  @P1_7_1_3.block_append 390 87 87 215 128 128 256 102318590 317771520 420090110 cost_390_87_block0 cost_390_87_block1 rfl rfl rfl

private theorem cost_390_87_join0_2 : P1_7_1_3.blockEstimate 390 87 343 221 = 242588279 :=
  @P1_7_1_3.block_append 390 87 343 471 128 93 221 218189305 24398974 242588279 cost_390_87_block2 cost_390_87_block3 rfl rfl rfl

private theorem cost_390_87_join1_0 : P1_7_1_3.blockEstimate 390 87 87 477 = 662678389 :=
  @P1_7_1_3.block_append 390 87 87 343 256 221 477 420090110 242588279 662678389 cost_390_87_join0_0 cost_390_87_join0_2 rfl rfl rfl

private theorem cost_390_87_total : P1_7_1_3.momentEstimate 390 87 = 662678389 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 390 + 87 = 477 by decide]
  exact cost_390_87_join1_0

theorem moment390_87 : P1_7_1.groupedPoleMoment 390 87 ≤ 662678389 :=
  (P1_7_1_3.grouped_bound 390 87).trans_eq cost_390_87_total
private theorem cost_408_91_block0 : P1_7_1_3.blockEstimate 408 91 91 128 = 109445109 := by decide +kernel

private theorem cost_408_91_block1 : P1_7_1_3.blockEstimate 408 91 219 128 = 358699904 := by decide +kernel

private theorem cost_408_91_block2 : P1_7_1_3.blockEstimate 408 91 347 128 = 278148219 := by decide +kernel

private theorem cost_408_91_block3 : P1_7_1_3.blockEstimate 408 91 475 115 = 46616221 := by decide +kernel

private theorem cost_408_91_join0_0 : P1_7_1_3.blockEstimate 408 91 91 256 = 468145013 :=
  @P1_7_1_3.block_append 408 91 91 219 128 128 256 109445109 358699904 468145013 cost_408_91_block0 cost_408_91_block1 rfl rfl rfl

private theorem cost_408_91_join0_2 : P1_7_1_3.blockEstimate 408 91 347 243 = 324764440 :=
  @P1_7_1_3.block_append 408 91 347 475 128 115 243 278148219 46616221 324764440 cost_408_91_block2 cost_408_91_block3 rfl rfl rfl

private theorem cost_408_91_join1_0 : P1_7_1_3.blockEstimate 408 91 91 499 = 792909453 :=
  @P1_7_1_3.block_append 408 91 91 347 256 243 499 468145013 324764440 792909453 cost_408_91_join0_0 cost_408_91_join0_2 rfl rfl rfl

private theorem cost_408_91_total : P1_7_1_3.momentEstimate 408 91 = 792909453 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 408 + 91 = 499 by decide]
  exact cost_408_91_join1_0

theorem moment408_91 : P1_7_1.groupedPoleMoment 408 91 ≤ 792909453 :=
  (P1_7_1_3.grouped_bound 408 91).trans_eq cost_408_91_total

end Research6966.HelperRescueCatalogue

end Merged6967_Near6967RescueMoment2

section Merged6967_Near6967RescueMoment20
set_option Elab.async false


set_option Elab.async false
namespace Research6966.HelperRescueCatalogue
open HelperRescueSource
set_option maxRecDepth 16000
set_option maxHeartbeats 0

private theorem cost_2649_589_block0 : P1_7_1_3.blockEstimate 2649 589 589 128 = 913629600 := by decide +kernel

private theorem cost_2649_589_block1 : P1_7_1_3.blockEstimate 2649 589 717 128 = 6039482784 := by decide +kernel

private theorem cost_2649_589_block2 : P1_7_1_3.blockEstimate 2649 589 845 128 = 15509586336 := by decide +kernel

private theorem cost_2649_589_block3 : P1_7_1_3.blockEstimate 2649 589 973 128 = 28518633888 := by decide +kernel

private theorem cost_2649_589_block4 : P1_7_1_3.blockEstimate 2649 589 1101 128 = 44216627347 := by decide +kernel

private theorem cost_2649_589_block5 : P1_7_1_3.blockEstimate 2649 589 1229 128 = 60135801920 := by decide +kernel

private theorem cost_2649_589_block6 : P1_7_1_3.blockEstimate 2649 589 1357 128 = 73741485120 := by decide +kernel

private theorem cost_2649_589_block7 : P1_7_1_3.blockEstimate 2649 589 1485 128 = 84872528960 := by decide +kernel

private theorem cost_2649_589_block8 : P1_7_1_3.blockEstimate 2649 589 1613 128 = 93528933440 := by decide +kernel

private theorem cost_2649_589_block9 : P1_7_1_3.blockEstimate 2649 589 1741 128 = 99710698560 := by decide +kernel

private theorem cost_2649_589_block10 : P1_7_1_3.blockEstimate 2649 589 1869 128 = 103417824320 := by decide +kernel

private theorem cost_2649_589_block11 : P1_7_1_3.blockEstimate 2649 589 1997 128 = 104650310720 := by decide +kernel

private theorem cost_2649_589_block12 : P1_7_1_3.blockEstimate 2649 589 2125 128 = 103408157760 := by decide +kernel

private theorem cost_2649_589_block13 : P1_7_1_3.blockEstimate 2649 589 2253 128 = 99691365440 := by decide +kernel

private theorem cost_2649_589_block14 : P1_7_1_3.blockEstimate 2649 589 2381 128 = 93499933760 := by decide +kernel

private theorem cost_2649_589_block15 : P1_7_1_3.blockEstimate 2649 589 2509 128 = 84833862720 := by decide +kernel

private theorem cost_2649_589_block16 : P1_7_1_3.blockEstimate 2649 589 2637 128 = 73903921118 := by decide +kernel

private theorem cost_2649_589_block17 : P1_7_1_3.blockEstimate 2649 589 2765 128 = 61983840511 := by decide +kernel

private theorem cost_2649_589_block18 : P1_7_1_3.blockEstimate 2649 589 2893 128 = 49933689265 := by decide +kernel

private theorem cost_2649_589_block19 : P1_7_1_3.blockEstimate 2649 589 3021 128 = 38274197601 := by decide +kernel

private theorem cost_2649_589_block20 : P1_7_1_3.blockEstimate 2649 589 3149 128 = 27474779136 := by decide +kernel

private theorem cost_2649_589_block21 : P1_7_1_3.blockEstimate 2649 589 3277 128 = 17914766096 := by decide +kernel

private theorem cost_2649_589_block22 : P1_7_1_3.blockEstimate 2649 589 3405 128 = 10118184720 := by decide +kernel

private theorem cost_2649_589_block23 : P1_7_1_3.blockEstimate 2649 589 3533 128 = 4393917200 := by decide +kernel

private theorem cost_2649_589_block24 : P1_7_1_3.blockEstimate 2649 589 3661 128 = 993621776 := by decide +kernel

private theorem cost_2649_589_block25 : P1_7_1_3.blockEstimate 2649 589 3789 38 = 13501355 := by decide +kernel

private theorem cost_2649_589_join0_0 : P1_7_1_3.blockEstimate 2649 589 589 256 = 6953112384 :=
  @P1_7_1_3.block_append 2649 589 589 717 128 128 256 913629600 6039482784 6953112384 cost_2649_589_block0 cost_2649_589_block1 rfl rfl rfl

private theorem cost_2649_589_join0_2 : P1_7_1_3.blockEstimate 2649 589 845 256 = 44028220224 :=
  @P1_7_1_3.block_append 2649 589 845 973 128 128 256 15509586336 28518633888 44028220224 cost_2649_589_block2 cost_2649_589_block3 rfl rfl rfl

private theorem cost_2649_589_join0_4 : P1_7_1_3.blockEstimate 2649 589 1101 256 = 104352429267 :=
  @P1_7_1_3.block_append 2649 589 1101 1229 128 128 256 44216627347 60135801920 104352429267 cost_2649_589_block4 cost_2649_589_block5 rfl rfl rfl

private theorem cost_2649_589_join0_6 : P1_7_1_3.blockEstimate 2649 589 1357 256 = 158614014080 :=
  @P1_7_1_3.block_append 2649 589 1357 1485 128 128 256 73741485120 84872528960 158614014080 cost_2649_589_block6 cost_2649_589_block7 rfl rfl rfl

private theorem cost_2649_589_join0_8 : P1_7_1_3.blockEstimate 2649 589 1613 256 = 193239632000 :=
  @P1_7_1_3.block_append 2649 589 1613 1741 128 128 256 93528933440 99710698560 193239632000 cost_2649_589_block8 cost_2649_589_block9 rfl rfl rfl

private theorem cost_2649_589_join0_10 : P1_7_1_3.blockEstimate 2649 589 1869 256 = 208068135040 :=
  @P1_7_1_3.block_append 2649 589 1869 1997 128 128 256 103417824320 104650310720 208068135040 cost_2649_589_block10 cost_2649_589_block11 rfl rfl rfl

private theorem cost_2649_589_join0_12 : P1_7_1_3.blockEstimate 2649 589 2125 256 = 203099523200 :=
  @P1_7_1_3.block_append 2649 589 2125 2253 128 128 256 103408157760 99691365440 203099523200 cost_2649_589_block12 cost_2649_589_block13 rfl rfl rfl

private theorem cost_2649_589_join0_14 : P1_7_1_3.blockEstimate 2649 589 2381 256 = 178333796480 :=
  @P1_7_1_3.block_append 2649 589 2381 2509 128 128 256 93499933760 84833862720 178333796480 cost_2649_589_block14 cost_2649_589_block15 rfl rfl rfl

private theorem cost_2649_589_join0_16 : P1_7_1_3.blockEstimate 2649 589 2637 256 = 135887761629 :=
  @P1_7_1_3.block_append 2649 589 2637 2765 128 128 256 73903921118 61983840511 135887761629 cost_2649_589_block16 cost_2649_589_block17 rfl rfl rfl

private theorem cost_2649_589_join0_18 : P1_7_1_3.blockEstimate 2649 589 2893 256 = 88207886866 :=
  @P1_7_1_3.block_append 2649 589 2893 3021 128 128 256 49933689265 38274197601 88207886866 cost_2649_589_block18 cost_2649_589_block19 rfl rfl rfl

private theorem cost_2649_589_join0_20 : P1_7_1_3.blockEstimate 2649 589 3149 256 = 45389545232 :=
  @P1_7_1_3.block_append 2649 589 3149 3277 128 128 256 27474779136 17914766096 45389545232 cost_2649_589_block20 cost_2649_589_block21 rfl rfl rfl

private theorem cost_2649_589_join0_22 : P1_7_1_3.blockEstimate 2649 589 3405 256 = 14512101920 :=
  @P1_7_1_3.block_append 2649 589 3405 3533 128 128 256 10118184720 4393917200 14512101920 cost_2649_589_block22 cost_2649_589_block23 rfl rfl rfl

private theorem cost_2649_589_join0_24 : P1_7_1_3.blockEstimate 2649 589 3661 166 = 1007123131 :=
  @P1_7_1_3.block_append 2649 589 3661 3789 128 38 166 993621776 13501355 1007123131 cost_2649_589_block24 cost_2649_589_block25 rfl rfl rfl

private theorem cost_2649_589_join1_0 : P1_7_1_3.blockEstimate 2649 589 589 512 = 50981332608 :=
  @P1_7_1_3.block_append 2649 589 589 845 256 256 512 6953112384 44028220224 50981332608 cost_2649_589_join0_0 cost_2649_589_join0_2 rfl rfl rfl

private theorem cost_2649_589_join1_2 : P1_7_1_3.blockEstimate 2649 589 1101 512 = 262966443347 :=
  @P1_7_1_3.block_append 2649 589 1101 1357 256 256 512 104352429267 158614014080 262966443347 cost_2649_589_join0_4 cost_2649_589_join0_6 rfl rfl rfl

private theorem cost_2649_589_join1_4 : P1_7_1_3.blockEstimate 2649 589 1613 512 = 401307767040 :=
  @P1_7_1_3.block_append 2649 589 1613 1869 256 256 512 193239632000 208068135040 401307767040 cost_2649_589_join0_8 cost_2649_589_join0_10 rfl rfl rfl

private theorem cost_2649_589_join1_6 : P1_7_1_3.blockEstimate 2649 589 2125 512 = 381433319680 :=
  @P1_7_1_3.block_append 2649 589 2125 2381 256 256 512 203099523200 178333796480 381433319680 cost_2649_589_join0_12 cost_2649_589_join0_14 rfl rfl rfl

private theorem cost_2649_589_join1_8 : P1_7_1_3.blockEstimate 2649 589 2637 512 = 224095648495 :=
  @P1_7_1_3.block_append 2649 589 2637 2893 256 256 512 135887761629 88207886866 224095648495 cost_2649_589_join0_16 cost_2649_589_join0_18 rfl rfl rfl

private theorem cost_2649_589_join1_10 : P1_7_1_3.blockEstimate 2649 589 3149 512 = 59901647152 :=
  @P1_7_1_3.block_append 2649 589 3149 3405 256 256 512 45389545232 14512101920 59901647152 cost_2649_589_join0_20 cost_2649_589_join0_22 rfl rfl rfl

private theorem cost_2649_589_join2_0 : P1_7_1_3.blockEstimate 2649 589 589 1024 = 313947775955 :=
  @P1_7_1_3.block_append 2649 589 589 1101 512 512 1024 50981332608 262966443347 313947775955 cost_2649_589_join1_0 cost_2649_589_join1_2 rfl rfl rfl

private theorem cost_2649_589_join2_2 : P1_7_1_3.blockEstimate 2649 589 1613 1024 = 782741086720 :=
  @P1_7_1_3.block_append 2649 589 1613 2125 512 512 1024 401307767040 381433319680 782741086720 cost_2649_589_join1_4 cost_2649_589_join1_6 rfl rfl rfl

private theorem cost_2649_589_join2_4 : P1_7_1_3.blockEstimate 2649 589 2637 1024 = 283997295647 :=
  @P1_7_1_3.block_append 2649 589 2637 3149 512 512 1024 224095648495 59901647152 283997295647 cost_2649_589_join1_8 cost_2649_589_join1_10 rfl rfl rfl

private theorem cost_2649_589_join3_0 : P1_7_1_3.blockEstimate 2649 589 589 2048 = 1096688862675 :=
  @P1_7_1_3.block_append 2649 589 589 1613 1024 1024 2048 313947775955 782741086720 1096688862675 cost_2649_589_join2_0 cost_2649_589_join2_2 rfl rfl rfl

private theorem cost_2649_589_join3_2 : P1_7_1_3.blockEstimate 2649 589 2637 1190 = 285004418778 :=
  @P1_7_1_3.block_append 2649 589 2637 3661 1024 166 1190 283997295647 1007123131 285004418778 cost_2649_589_join2_4 cost_2649_589_join0_24 rfl rfl rfl

private theorem cost_2649_589_join4_0 : P1_7_1_3.blockEstimate 2649 589 589 3238 = 1381693281453 :=
  @P1_7_1_3.block_append 2649 589 589 2637 2048 1190 3238 1096688862675 285004418778 1381693281453 cost_2649_589_join3_0 cost_2649_589_join3_2 rfl rfl rfl

private theorem cost_2649_589_total : P1_7_1_3.momentEstimate 2649 589 = 1381693281453 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2649 + 589 = 3238 by decide]
  exact cost_2649_589_join4_0

theorem moment2649_589 : P1_7_1.groupedPoleMoment 2649 589 ≤ 1381693281453 :=
  (P1_7_1_3.grouped_bound 2649 589).trans_eq cost_2649_589_total
private theorem cost_2650_589_block0 : P1_7_1_3.blockEstimate 2650 589 589 128 = 913987360 := by decide +kernel

private theorem cost_2650_589_block1 : P1_7_1_3.blockEstimate 2650 589 717 128 = 6041954080 := by decide +kernel

private theorem cost_2650_589_block2 : P1_7_1_3.blockEstimate 2650 589 845 128 = 15516268320 := by decide +kernel

private theorem cost_2650_589_block3 : P1_7_1_3.blockEstimate 2650 589 973 128 = 28531623712 := by decide +kernel

private theorem cost_2650_589_block4 : P1_7_1_3.blockEstimate 2650 589 1101 128 = 44238000063 := by decide +kernel

private theorem cost_2650_589_block5 : P1_7_1_3.blockEstimate 2650 589 1229 128 = 60166765120 := by decide +kernel

private theorem cost_2650_589_block6 : P1_7_1_3.blockEstimate 2650 589 1357 128 = 73782114880 := by decide +kernel

private theorem cost_2650_589_block7 : P1_7_1_3.blockEstimate 2650 589 1485 128 = 84922825280 := by decide +kernel

private theorem cost_2650_589_block8 : P1_7_1_3.blockEstimate 2650 589 1613 128 = 93588896320 := by decide +kernel

private theorem cost_2650_589_block9 : P1_7_1_3.blockEstimate 2650 589 1741 128 = 99780328000 := by decide +kernel

private theorem cost_2650_589_block10 : P1_7_1_3.blockEstimate 2650 589 1869 128 = 103497120320 := by decide +kernel

private theorem cost_2650_589_block11 : P1_7_1_3.blockEstimate 2650 589 1997 128 = 104739273280 := by decide +kernel

private theorem cost_2650_589_block12 : P1_7_1_3.blockEstimate 2650 589 2125 128 = 103506786880 := by decide +kernel

private theorem cost_2650_589_block13 : P1_7_1_3.blockEstimate 2650 589 2253 128 = 99799661120 := by decide +kernel

private theorem cost_2650_589_block14 : P1_7_1_3.blockEstimate 2650 589 2381 128 = 93617896000 := by decide +kernel

private theorem cost_2650_589_block15 : P1_7_1_3.blockEstimate 2650 589 2509 128 = 84961491520 := by decide +kernel

private theorem cost_2650_589_block16 : P1_7_1_3.blockEstimate 2650 589 2637 128 = 74035822415 := by decide +kernel

private theorem cost_2650_589_block17 : P1_7_1_3.blockEstimate 2650 589 2765 128 = 62110252923 := by decide +kernel

private theorem cost_2650_589_block18 : P1_7_1_3.blockEstimate 2650 589 2893 128 = 50051370281 := by decide +kernel

private theorem cost_2650_589_block19 : P1_7_1_3.blockEstimate 2650 589 3021 128 = 38380298201 := by decide +kernel

private theorem cost_2650_589_block20 : P1_7_1_3.blockEstimate 2650 589 3149 128 = 27567139843 := by decide +kernel

private theorem cost_2650_589_block21 : P1_7_1_3.blockEstimate 2650 589 3277 128 = 17990851936 := by decide +kernel

private theorem cost_2650_589_block22 : P1_7_1_3.blockEstimate 2650 589 3405 128 = 10175593824 := by decide +kernel

private theorem cost_2650_589_block23 : P1_7_1_3.blockEstimate 2650 589 3533 128 = 4431732064 := by decide +kernel

private theorem cost_2650_589_block24 : P1_7_1_3.blockEstimate 2650 589 3661 128 = 1010924896 := by decide +kernel

private theorem cost_2650_589_block25 : P1_7_1_3.blockEstimate 2650 589 3789 39 = 14557030 := by decide +kernel

private theorem cost_2650_589_join0_0 : P1_7_1_3.blockEstimate 2650 589 589 256 = 6955941440 :=
  @P1_7_1_3.block_append 2650 589 589 717 128 128 256 913987360 6041954080 6955941440 cost_2650_589_block0 cost_2650_589_block1 rfl rfl rfl

private theorem cost_2650_589_join0_2 : P1_7_1_3.blockEstimate 2650 589 845 256 = 44047892032 :=
  @P1_7_1_3.block_append 2650 589 845 973 128 128 256 15516268320 28531623712 44047892032 cost_2650_589_block2 cost_2650_589_block3 rfl rfl rfl

private theorem cost_2650_589_join0_4 : P1_7_1_3.blockEstimate 2650 589 1101 256 = 104404765183 :=
  @P1_7_1_3.block_append 2650 589 1101 1229 128 128 256 44238000063 60166765120 104404765183 cost_2650_589_block4 cost_2650_589_block5 rfl rfl rfl

private theorem cost_2650_589_join0_6 : P1_7_1_3.blockEstimate 2650 589 1357 256 = 158704940160 :=
  @P1_7_1_3.block_append 2650 589 1357 1485 128 128 256 73782114880 84922825280 158704940160 cost_2650_589_block6 cost_2650_589_block7 rfl rfl rfl

private theorem cost_2650_589_join0_8 : P1_7_1_3.blockEstimate 2650 589 1613 256 = 193369224320 :=
  @P1_7_1_3.block_append 2650 589 1613 1741 128 128 256 93588896320 99780328000 193369224320 cost_2650_589_block8 cost_2650_589_block9 rfl rfl rfl

private theorem cost_2650_589_join0_10 : P1_7_1_3.blockEstimate 2650 589 1869 256 = 208236393600 :=
  @P1_7_1_3.block_append 2650 589 1869 1997 128 128 256 103497120320 104739273280 208236393600 cost_2650_589_block10 cost_2650_589_block11 rfl rfl rfl

private theorem cost_2650_589_join0_12 : P1_7_1_3.blockEstimate 2650 589 2125 256 = 203306448000 :=
  @P1_7_1_3.block_append 2650 589 2125 2253 128 128 256 103506786880 99799661120 203306448000 cost_2650_589_block12 cost_2650_589_block13 rfl rfl rfl

private theorem cost_2650_589_join0_14 : P1_7_1_3.blockEstimate 2650 589 2381 256 = 178579387520 :=
  @P1_7_1_3.block_append 2650 589 2381 2509 128 128 256 93617896000 84961491520 178579387520 cost_2650_589_block14 cost_2650_589_block15 rfl rfl rfl

private theorem cost_2650_589_join0_16 : P1_7_1_3.blockEstimate 2650 589 2637 256 = 136146075338 :=
  @P1_7_1_3.block_append 2650 589 2637 2765 128 128 256 74035822415 62110252923 136146075338 cost_2650_589_block16 cost_2650_589_block17 rfl rfl rfl

private theorem cost_2650_589_join0_18 : P1_7_1_3.blockEstimate 2650 589 2893 256 = 88431668482 :=
  @P1_7_1_3.block_append 2650 589 2893 3021 128 128 256 50051370281 38380298201 88431668482 cost_2650_589_block18 cost_2650_589_block19 rfl rfl rfl

private theorem cost_2650_589_join0_20 : P1_7_1_3.blockEstimate 2650 589 3149 256 = 45557991779 :=
  @P1_7_1_3.block_append 2650 589 3149 3277 128 128 256 27567139843 17990851936 45557991779 cost_2650_589_block20 cost_2650_589_block21 rfl rfl rfl

private theorem cost_2650_589_join0_22 : P1_7_1_3.blockEstimate 2650 589 3405 256 = 14607325888 :=
  @P1_7_1_3.block_append 2650 589 3405 3533 128 128 256 10175593824 4431732064 14607325888 cost_2650_589_block22 cost_2650_589_block23 rfl rfl rfl

private theorem cost_2650_589_join0_24 : P1_7_1_3.blockEstimate 2650 589 3661 167 = 1025481926 :=
  @P1_7_1_3.block_append 2650 589 3661 3789 128 39 167 1010924896 14557030 1025481926 cost_2650_589_block24 cost_2650_589_block25 rfl rfl rfl

private theorem cost_2650_589_join1_0 : P1_7_1_3.blockEstimate 2650 589 589 512 = 51003833472 :=
  @P1_7_1_3.block_append 2650 589 589 845 256 256 512 6955941440 44047892032 51003833472 cost_2650_589_join0_0 cost_2650_589_join0_2 rfl rfl rfl

private theorem cost_2650_589_join1_2 : P1_7_1_3.blockEstimate 2650 589 1101 512 = 263109705343 :=
  @P1_7_1_3.block_append 2650 589 1101 1357 256 256 512 104404765183 158704940160 263109705343 cost_2650_589_join0_4 cost_2650_589_join0_6 rfl rfl rfl

private theorem cost_2650_589_join1_4 : P1_7_1_3.blockEstimate 2650 589 1613 512 = 401605617920 :=
  @P1_7_1_3.block_append 2650 589 1613 1869 256 256 512 193369224320 208236393600 401605617920 cost_2650_589_join0_8 cost_2650_589_join0_10 rfl rfl rfl

private theorem cost_2650_589_join1_6 : P1_7_1_3.blockEstimate 2650 589 2125 512 = 381885835520 :=
  @P1_7_1_3.block_append 2650 589 2125 2381 256 256 512 203306448000 178579387520 381885835520 cost_2650_589_join0_12 cost_2650_589_join0_14 rfl rfl rfl

private theorem cost_2650_589_join1_8 : P1_7_1_3.blockEstimate 2650 589 2637 512 = 224577743820 :=
  @P1_7_1_3.block_append 2650 589 2637 2893 256 256 512 136146075338 88431668482 224577743820 cost_2650_589_join0_16 cost_2650_589_join0_18 rfl rfl rfl

private theorem cost_2650_589_join1_10 : P1_7_1_3.blockEstimate 2650 589 3149 512 = 60165317667 :=
  @P1_7_1_3.block_append 2650 589 3149 3405 256 256 512 45557991779 14607325888 60165317667 cost_2650_589_join0_20 cost_2650_589_join0_22 rfl rfl rfl

private theorem cost_2650_589_join2_0 : P1_7_1_3.blockEstimate 2650 589 589 1024 = 314113538815 :=
  @P1_7_1_3.block_append 2650 589 589 1101 512 512 1024 51003833472 263109705343 314113538815 cost_2650_589_join1_0 cost_2650_589_join1_2 rfl rfl rfl

private theorem cost_2650_589_join2_2 : P1_7_1_3.blockEstimate 2650 589 1613 1024 = 783491453440 :=
  @P1_7_1_3.block_append 2650 589 1613 2125 512 512 1024 401605617920 381885835520 783491453440 cost_2650_589_join1_4 cost_2650_589_join1_6 rfl rfl rfl

private theorem cost_2650_589_join2_4 : P1_7_1_3.blockEstimate 2650 589 2637 1024 = 284743061487 :=
  @P1_7_1_3.block_append 2650 589 2637 3149 512 512 1024 224577743820 60165317667 284743061487 cost_2650_589_join1_8 cost_2650_589_join1_10 rfl rfl rfl

private theorem cost_2650_589_join3_0 : P1_7_1_3.blockEstimate 2650 589 589 2048 = 1097604992255 :=
  @P1_7_1_3.block_append 2650 589 589 1613 1024 1024 2048 314113538815 783491453440 1097604992255 cost_2650_589_join2_0 cost_2650_589_join2_2 rfl rfl rfl

private theorem cost_2650_589_join3_2 : P1_7_1_3.blockEstimate 2650 589 2637 1191 = 285768543413 :=
  @P1_7_1_3.block_append 2650 589 2637 3661 1024 167 1191 284743061487 1025481926 285768543413 cost_2650_589_join2_4 cost_2650_589_join0_24 rfl rfl rfl

private theorem cost_2650_589_join4_0 : P1_7_1_3.blockEstimate 2650 589 589 3239 = 1383373535668 :=
  @P1_7_1_3.block_append 2650 589 589 2637 2048 1191 3239 1097604992255 285768543413 1383373535668 cost_2650_589_join3_0 cost_2650_589_join3_2 rfl rfl rfl

private theorem cost_2650_589_total : P1_7_1_3.momentEstimate 2650 589 = 1383373535668 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2650 + 589 = 3239 by decide]
  exact cost_2650_589_join4_0

theorem moment2650_589 : P1_7_1.groupedPoleMoment 2650 589 ≤ 1383373535668 :=
  (P1_7_1_3.grouped_bound 2650 589).trans_eq cost_2650_589_total
private theorem cost_2650_591_block0 : P1_7_1_3.blockEstimate 2650 591 591 128 = 913987360 := by decide +kernel

private theorem cost_2650_591_block1 : P1_7_1_3.blockEstimate 2650 591 719 128 = 6041954080 := by decide +kernel

private theorem cost_2650_591_block2 : P1_7_1_3.blockEstimate 2650 591 847 128 = 15516268320 := by decide +kernel

private theorem cost_2650_591_block3 : P1_7_1_3.blockEstimate 2650 591 975 128 = 28531623712 := by decide +kernel

private theorem cost_2650_591_block4 : P1_7_1_3.blockEstimate 2650 591 1103 128 = 44243067988 := by decide +kernel

private theorem cost_2650_591_block5 : P1_7_1_3.blockEstimate 2650 591 1231 128 = 60223222272 := by decide +kernel

private theorem cost_2650_591_block6 : P1_7_1_3.blockEstimate 2650 591 1359 128 = 73894425088 := by decide +kernel

private theorem cost_2650_591_block7 : P1_7_1_3.blockEstimate 2650 591 1487 128 = 85082599936 := by decide +kernel

private theorem cost_2650_591_block8 : P1_7_1_3.blockEstimate 2650 591 1615 128 = 93787746816 := by decide +kernel

private theorem cost_2650_591_block9 : P1_7_1_3.blockEstimate 2650 591 1743 128 = 100009865728 := by decide +kernel

private theorem cost_2650_591_block10 : P1_7_1_3.blockEstimate 2650 591 1871 128 = 103748956672 := by decide +kernel

private theorem cost_2650_591_block11 : P1_7_1_3.blockEstimate 2650 591 1999 128 = 105005019648 := by decide +kernel

private theorem cost_2650_591_block12 : P1_7_1_3.blockEstimate 2650 591 2127 128 = 103778054656 := by decide +kernel

private theorem cost_2650_591_block13 : P1_7_1_3.blockEstimate 2650 591 2255 128 = 100068061696 := by decide +kernel

private theorem cost_2650_591_block14 : P1_7_1_3.blockEstimate 2650 591 2383 128 = 93875040768 := by decide +kernel

private theorem cost_2650_591_block15 : P1_7_1_3.blockEstimate 2650 591 2511 128 = 85198991872 := by decide +kernel

private theorem cost_2650_591_block16 : P1_7_1_3.blockEstimate 2650 591 2639 128 = 74255901722 := by decide +kernel

private theorem cost_2650_591_block17 : P1_7_1_3.blockEstimate 2650 591 2767 128 = 62322353207 := by decide +kernel

private theorem cost_2650_591_block18 : P1_7_1_3.blockEstimate 2650 591 2895 128 = 50251646582 := by decide +kernel

private theorem cost_2650_591_block19 : P1_7_1_3.blockEstimate 2650 591 3023 128 = 38564409755 := by decide +kernel

private theorem cost_2650_591_block20 : P1_7_1_3.blockEstimate 2650 591 3151 128 = 27730442445 := by decide +kernel

private theorem cost_2650_591_block21 : P1_7_1_3.blockEstimate 2650 591 3279 128 = 18128059376 := by decide +kernel

private theorem cost_2650_591_block22 : P1_7_1_3.blockEstimate 2650 591 3407 128 = 10282432496 := by decide +kernel

private theorem cost_2650_591_block23 : P1_7_1_3.blockEstimate 2650 591 3535 128 = 4504269808 := by decide +kernel

private theorem cost_2650_591_block24 : P1_7_1_3.blockEstimate 2650 591 3663 128 = 1045229552 := by decide +kernel

private theorem cost_2650_591_block25 : P1_7_1_3.blockEstimate 2650 591 3791 41 = 16817515 := by decide +kernel

private theorem cost_2650_591_join0_0 : P1_7_1_3.blockEstimate 2650 591 591 256 = 6955941440 :=
  @P1_7_1_3.block_append 2650 591 591 719 128 128 256 913987360 6041954080 6955941440 cost_2650_591_block0 cost_2650_591_block1 rfl rfl rfl

private theorem cost_2650_591_join0_2 : P1_7_1_3.blockEstimate 2650 591 847 256 = 44047892032 :=
  @P1_7_1_3.block_append 2650 591 847 975 128 128 256 15516268320 28531623712 44047892032 cost_2650_591_block2 cost_2650_591_block3 rfl rfl rfl

private theorem cost_2650_591_join0_4 : P1_7_1_3.blockEstimate 2650 591 1103 256 = 104466290260 :=
  @P1_7_1_3.block_append 2650 591 1103 1231 128 128 256 44243067988 60223222272 104466290260 cost_2650_591_block4 cost_2650_591_block5 rfl rfl rfl

private theorem cost_2650_591_join0_6 : P1_7_1_3.blockEstimate 2650 591 1359 256 = 158977025024 :=
  @P1_7_1_3.block_append 2650 591 1359 1487 128 128 256 73894425088 85082599936 158977025024 cost_2650_591_block6 cost_2650_591_block7 rfl rfl rfl

private theorem cost_2650_591_join0_8 : P1_7_1_3.blockEstimate 2650 591 1615 256 = 193797612544 :=
  @P1_7_1_3.block_append 2650 591 1615 1743 128 128 256 93787746816 100009865728 193797612544 cost_2650_591_block8 cost_2650_591_block9 rfl rfl rfl

private theorem cost_2650_591_join0_10 : P1_7_1_3.blockEstimate 2650 591 1871 256 = 208753976320 :=
  @P1_7_1_3.block_append 2650 591 1871 1999 128 128 256 103748956672 105005019648 208753976320 cost_2650_591_block10 cost_2650_591_block11 rfl rfl rfl

private theorem cost_2650_591_join0_12 : P1_7_1_3.blockEstimate 2650 591 2127 256 = 203846116352 :=
  @P1_7_1_3.block_append 2650 591 2127 2255 128 128 256 103778054656 100068061696 203846116352 cost_2650_591_block12 cost_2650_591_block13 rfl rfl rfl

private theorem cost_2650_591_join0_14 : P1_7_1_3.blockEstimate 2650 591 2383 256 = 179074032640 :=
  @P1_7_1_3.block_append 2650 591 2383 2511 128 128 256 93875040768 85198991872 179074032640 cost_2650_591_block14 cost_2650_591_block15 rfl rfl rfl

private theorem cost_2650_591_join0_16 : P1_7_1_3.blockEstimate 2650 591 2639 256 = 136578254929 :=
  @P1_7_1_3.block_append 2650 591 2639 2767 128 128 256 74255901722 62322353207 136578254929 cost_2650_591_block16 cost_2650_591_block17 rfl rfl rfl

private theorem cost_2650_591_join0_18 : P1_7_1_3.blockEstimate 2650 591 2895 256 = 88816056337 :=
  @P1_7_1_3.block_append 2650 591 2895 3023 128 128 256 50251646582 38564409755 88816056337 cost_2650_591_block18 cost_2650_591_block19 rfl rfl rfl

private theorem cost_2650_591_join0_20 : P1_7_1_3.blockEstimate 2650 591 3151 256 = 45858501821 :=
  @P1_7_1_3.block_append 2650 591 3151 3279 128 128 256 27730442445 18128059376 45858501821 cost_2650_591_block20 cost_2650_591_block21 rfl rfl rfl

private theorem cost_2650_591_join0_22 : P1_7_1_3.blockEstimate 2650 591 3407 256 = 14786702304 :=
  @P1_7_1_3.block_append 2650 591 3407 3535 128 128 256 10282432496 4504269808 14786702304 cost_2650_591_block22 cost_2650_591_block23 rfl rfl rfl

private theorem cost_2650_591_join0_24 : P1_7_1_3.blockEstimate 2650 591 3663 169 = 1062047067 :=
  @P1_7_1_3.block_append 2650 591 3663 3791 128 41 169 1045229552 16817515 1062047067 cost_2650_591_block24 cost_2650_591_block25 rfl rfl rfl

private theorem cost_2650_591_join1_0 : P1_7_1_3.blockEstimate 2650 591 591 512 = 51003833472 :=
  @P1_7_1_3.block_append 2650 591 591 847 256 256 512 6955941440 44047892032 51003833472 cost_2650_591_join0_0 cost_2650_591_join0_2 rfl rfl rfl

private theorem cost_2650_591_join1_2 : P1_7_1_3.blockEstimate 2650 591 1103 512 = 263443315284 :=
  @P1_7_1_3.block_append 2650 591 1103 1359 256 256 512 104466290260 158977025024 263443315284 cost_2650_591_join0_4 cost_2650_591_join0_6 rfl rfl rfl

private theorem cost_2650_591_join1_4 : P1_7_1_3.blockEstimate 2650 591 1615 512 = 402551588864 :=
  @P1_7_1_3.block_append 2650 591 1615 1871 256 256 512 193797612544 208753976320 402551588864 cost_2650_591_join0_8 cost_2650_591_join0_10 rfl rfl rfl

private theorem cost_2650_591_join1_6 : P1_7_1_3.blockEstimate 2650 591 2127 512 = 382920148992 :=
  @P1_7_1_3.block_append 2650 591 2127 2383 256 256 512 203846116352 179074032640 382920148992 cost_2650_591_join0_12 cost_2650_591_join0_14 rfl rfl rfl

private theorem cost_2650_591_join1_8 : P1_7_1_3.blockEstimate 2650 591 2639 512 = 225394311266 :=
  @P1_7_1_3.block_append 2650 591 2639 2895 256 256 512 136578254929 88816056337 225394311266 cost_2650_591_join0_16 cost_2650_591_join0_18 rfl rfl rfl

private theorem cost_2650_591_join1_10 : P1_7_1_3.blockEstimate 2650 591 3151 512 = 60645204125 :=
  @P1_7_1_3.block_append 2650 591 3151 3407 256 256 512 45858501821 14786702304 60645204125 cost_2650_591_join0_20 cost_2650_591_join0_22 rfl rfl rfl

private theorem cost_2650_591_join2_0 : P1_7_1_3.blockEstimate 2650 591 591 1024 = 314447148756 :=
  @P1_7_1_3.block_append 2650 591 591 1103 512 512 1024 51003833472 263443315284 314447148756 cost_2650_591_join1_0 cost_2650_591_join1_2 rfl rfl rfl

private theorem cost_2650_591_join2_2 : P1_7_1_3.blockEstimate 2650 591 1615 1024 = 785471737856 :=
  @P1_7_1_3.block_append 2650 591 1615 2127 512 512 1024 402551588864 382920148992 785471737856 cost_2650_591_join1_4 cost_2650_591_join1_6 rfl rfl rfl

private theorem cost_2650_591_join2_4 : P1_7_1_3.blockEstimate 2650 591 2639 1024 = 286039515391 :=
  @P1_7_1_3.block_append 2650 591 2639 3151 512 512 1024 225394311266 60645204125 286039515391 cost_2650_591_join1_8 cost_2650_591_join1_10 rfl rfl rfl

private theorem cost_2650_591_join3_0 : P1_7_1_3.blockEstimate 2650 591 591 2048 = 1099918886612 :=
  @P1_7_1_3.block_append 2650 591 591 1615 1024 1024 2048 314447148756 785471737856 1099918886612 cost_2650_591_join2_0 cost_2650_591_join2_2 rfl rfl rfl

private theorem cost_2650_591_join3_2 : P1_7_1_3.blockEstimate 2650 591 2639 1193 = 287101562458 :=
  @P1_7_1_3.block_append 2650 591 2639 3663 1024 169 1193 286039515391 1062047067 287101562458 cost_2650_591_join2_4 cost_2650_591_join0_24 rfl rfl rfl

private theorem cost_2650_591_join4_0 : P1_7_1_3.blockEstimate 2650 591 591 3241 = 1387020449070 :=
  @P1_7_1_3.block_append 2650 591 591 2639 2048 1193 3241 1099918886612 287101562458 1387020449070 cost_2650_591_join3_0 cost_2650_591_join3_2 rfl rfl rfl

private theorem cost_2650_591_total : P1_7_1_3.momentEstimate 2650 591 = 1387020449070 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2650 + 591 = 3241 by decide]
  exact cost_2650_591_join4_0

theorem moment2650_591 : P1_7_1.groupedPoleMoment 2650 591 ≤ 1387020449070 :=
  (P1_7_1_3.grouped_bound 2650 591).trans_eq cost_2650_591_total
private theorem cost_2651_587_block0 : P1_7_1_3.blockEstimate 2651 587 587 128 = 914345120 := by decide +kernel

private theorem cost_2651_587_block1 : P1_7_1_3.blockEstimate 2651 587 715 128 = 6044425376 := by decide +kernel

private theorem cost_2651_587_block2 : P1_7_1_3.blockEstimate 2651 587 843 128 = 15522950304 := by decide +kernel

private theorem cost_2651_587_block3 : P1_7_1_3.blockEstimate 2651 587 971 128 = 28544613536 := by decide +kernel

private theorem cost_2651_587_block4 : P1_7_1_3.blockEstimate 2651 587 1099 128 = 44253886805 := by decide +kernel

private theorem cost_2651_587_block5 : P1_7_1_3.blockEstimate 2651 587 1227 128 = 60140244864 := by decide +kernel

private theorem cost_2651_587_block6 : P1_7_1_3.blockEstimate 2651 587 1355 128 = 73709440896 := by decide +kernel

private theorem cost_2651_587_block7 : P1_7_1_3.blockEstimate 2651 587 1483 128 = 84812386176 := by decide +kernel

private theorem cost_2651_587_block8 : P1_7_1_3.blockEstimate 2651 587 1611 128 = 93449080704 := by decide +kernel

private theorem cost_2651_587_block9 : P1_7_1_3.blockEstimate 2651 587 1739 128 = 99619524480 := by decide +kernel

private theorem cost_2651_587_block10 : P1_7_1_3.blockEstimate 2651 587 1867 128 = 103323717504 := by decide +kernel

private theorem cost_2651_587_block11 : P1_7_1_3.blockEstimate 2651 587 1995 128 = 104561659776 := by decide +kernel

private theorem cost_2651_587_block12 : P1_7_1_3.blockEstimate 2651 587 2123 128 = 103333351296 := by decide +kernel

private theorem cost_2651_587_block13 : P1_7_1_3.blockEstimate 2651 587 2251 128 = 99638792064 := by decide +kernel

private theorem cost_2651_587_block14 : P1_7_1_3.blockEstimate 2651 587 2379 128 = 93477982080 := by decide +kernel

private theorem cost_2651_587_block15 : P1_7_1_3.blockEstimate 2651 587 2507 128 = 84850921344 := by decide +kernel

private theorem cost_2651_587_block16 : P1_7_1_3.blockEstimate 2651 587 2635 128 = 73947594579 := by decide +kernel

private theorem cost_2651_587_block17 : P1_7_1_3.blockEstimate 2651 587 2763 128 = 62024661020 := by decide +kernel

private theorem cost_2651_587_block18 : P1_7_1_3.blockEstimate 2651 587 2891 128 = 49968939568 := by decide +kernel

private theorem cost_2651_587_block19 : P1_7_1_3.blockEstimate 2651 587 3019 128 = 38302512568 := by decide +kernel

private theorem cost_2651_587_block20 : P1_7_1_3.blockEstimate 2651 587 3147 128 = 27496468805 := by decide +kernel

private theorem cost_2651_587_block21 : P1_7_1_3.blockEstimate 2651 587 3275 128 = 17930063440 := by decide +kernel

private theorem cost_2651_587_block22 : P1_7_1_3.blockEstimate 2651 587 3403 128 = 10126543440 := by decide +kernel

private theorem cost_2651_587_block23 : P1_7_1_3.blockEstimate 2651 587 3531 128 = 4397434448 := by decide +kernel

private theorem cost_2651_587_block24 : P1_7_1_3.blockEstimate 2651 587 3659 128 = 994394704 := by decide +kernel

private theorem cost_2651_587_block25 : P1_7_1_3.blockEstimate 2651 587 3787 38 = 13511615 := by decide +kernel

private theorem cost_2651_587_join0_0 : P1_7_1_3.blockEstimate 2651 587 587 256 = 6958770496 :=
  @P1_7_1_3.block_append 2651 587 587 715 128 128 256 914345120 6044425376 6958770496 cost_2651_587_block0 cost_2651_587_block1 rfl rfl rfl

private theorem cost_2651_587_join0_2 : P1_7_1_3.blockEstimate 2651 587 843 256 = 44067563840 :=
  @P1_7_1_3.block_append 2651 587 843 971 128 128 256 15522950304 28544613536 44067563840 cost_2651_587_block2 cost_2651_587_block3 rfl rfl rfl

private theorem cost_2651_587_join0_4 : P1_7_1_3.blockEstimate 2651 587 1099 256 = 104394131669 :=
  @P1_7_1_3.block_append 2651 587 1099 1227 128 128 256 44253886805 60140244864 104394131669 cost_2651_587_block4 cost_2651_587_block5 rfl rfl rfl

private theorem cost_2651_587_join0_6 : P1_7_1_3.blockEstimate 2651 587 1355 256 = 158521827072 :=
  @P1_7_1_3.block_append 2651 587 1355 1483 128 128 256 73709440896 84812386176 158521827072 cost_2651_587_block6 cost_2651_587_block7 rfl rfl rfl

private theorem cost_2651_587_join0_8 : P1_7_1_3.blockEstimate 2651 587 1611 256 = 193068605184 :=
  @P1_7_1_3.block_append 2651 587 1611 1739 128 128 256 93449080704 99619524480 193068605184 cost_2651_587_block8 cost_2651_587_block9 rfl rfl rfl

private theorem cost_2651_587_join0_10 : P1_7_1_3.blockEstimate 2651 587 1867 256 = 207885377280 :=
  @P1_7_1_3.block_append 2651 587 1867 1995 128 128 256 103323717504 104561659776 207885377280 cost_2651_587_block10 cost_2651_587_block11 rfl rfl rfl

private theorem cost_2651_587_join0_12 : P1_7_1_3.blockEstimate 2651 587 2123 256 = 202972143360 :=
  @P1_7_1_3.block_append 2651 587 2123 2251 128 128 256 103333351296 99638792064 202972143360 cost_2651_587_block12 cost_2651_587_block13 rfl rfl rfl

private theorem cost_2651_587_join0_14 : P1_7_1_3.blockEstimate 2651 587 2379 256 = 178328903424 :=
  @P1_7_1_3.block_append 2651 587 2379 2507 128 128 256 93477982080 84850921344 178328903424 cost_2651_587_block14 cost_2651_587_block15 rfl rfl rfl

private theorem cost_2651_587_join0_16 : P1_7_1_3.blockEstimate 2651 587 2635 256 = 135972255599 :=
  @P1_7_1_3.block_append 2651 587 2635 2763 128 128 256 73947594579 62024661020 135972255599 cost_2651_587_block16 cost_2651_587_block17 rfl rfl rfl

private theorem cost_2651_587_join0_18 : P1_7_1_3.blockEstimate 2651 587 2891 256 = 88271452136 :=
  @P1_7_1_3.block_append 2651 587 2891 3019 128 128 256 49968939568 38302512568 88271452136 cost_2651_587_block18 cost_2651_587_block19 rfl rfl rfl

private theorem cost_2651_587_join0_20 : P1_7_1_3.blockEstimate 2651 587 3147 256 = 45426532245 :=
  @P1_7_1_3.block_append 2651 587 3147 3275 128 128 256 27496468805 17930063440 45426532245 cost_2651_587_block20 cost_2651_587_block21 rfl rfl rfl

private theorem cost_2651_587_join0_22 : P1_7_1_3.blockEstimate 2651 587 3403 256 = 14523977888 :=
  @P1_7_1_3.block_append 2651 587 3403 3531 128 128 256 10126543440 4397434448 14523977888 cost_2651_587_block22 cost_2651_587_block23 rfl rfl rfl

private theorem cost_2651_587_join0_24 : P1_7_1_3.blockEstimate 2651 587 3659 166 = 1007906319 :=
  @P1_7_1_3.block_append 2651 587 3659 3787 128 38 166 994394704 13511615 1007906319 cost_2651_587_block24 cost_2651_587_block25 rfl rfl rfl

private theorem cost_2651_587_join1_0 : P1_7_1_3.blockEstimate 2651 587 587 512 = 51026334336 :=
  @P1_7_1_3.block_append 2651 587 587 843 256 256 512 6958770496 44067563840 51026334336 cost_2651_587_join0_0 cost_2651_587_join0_2 rfl rfl rfl

private theorem cost_2651_587_join1_2 : P1_7_1_3.blockEstimate 2651 587 1099 512 = 262915958741 :=
  @P1_7_1_3.block_append 2651 587 1099 1355 256 256 512 104394131669 158521827072 262915958741 cost_2651_587_join0_4 cost_2651_587_join0_6 rfl rfl rfl

private theorem cost_2651_587_join1_4 : P1_7_1_3.blockEstimate 2651 587 1611 512 = 400953982464 :=
  @P1_7_1_3.block_append 2651 587 1611 1867 256 256 512 193068605184 207885377280 400953982464 cost_2651_587_join0_8 cost_2651_587_join0_10 rfl rfl rfl

private theorem cost_2651_587_join1_6 : P1_7_1_3.blockEstimate 2651 587 2123 512 = 381301046784 :=
  @P1_7_1_3.block_append 2651 587 2123 2379 256 256 512 202972143360 178328903424 381301046784 cost_2651_587_join0_12 cost_2651_587_join0_14 rfl rfl rfl

private theorem cost_2651_587_join1_8 : P1_7_1_3.blockEstimate 2651 587 2635 512 = 224243707735 :=
  @P1_7_1_3.block_append 2651 587 2635 2891 256 256 512 135972255599 88271452136 224243707735 cost_2651_587_join0_16 cost_2651_587_join0_18 rfl rfl rfl

private theorem cost_2651_587_join1_10 : P1_7_1_3.blockEstimate 2651 587 3147 512 = 59950510133 :=
  @P1_7_1_3.block_append 2651 587 3147 3403 256 256 512 45426532245 14523977888 59950510133 cost_2651_587_join0_20 cost_2651_587_join0_22 rfl rfl rfl

private theorem cost_2651_587_join2_0 : P1_7_1_3.blockEstimate 2651 587 587 1024 = 313942293077 :=
  @P1_7_1_3.block_append 2651 587 587 1099 512 512 1024 51026334336 262915958741 313942293077 cost_2651_587_join1_0 cost_2651_587_join1_2 rfl rfl rfl

private theorem cost_2651_587_join2_2 : P1_7_1_3.blockEstimate 2651 587 1611 1024 = 782255029248 :=
  @P1_7_1_3.block_append 2651 587 1611 2123 512 512 1024 400953982464 381301046784 782255029248 cost_2651_587_join1_4 cost_2651_587_join1_6 rfl rfl rfl

private theorem cost_2651_587_join2_4 : P1_7_1_3.blockEstimate 2651 587 2635 1024 = 284194217868 :=
  @P1_7_1_3.block_append 2651 587 2635 3147 512 512 1024 224243707735 59950510133 284194217868 cost_2651_587_join1_8 cost_2651_587_join1_10 rfl rfl rfl

private theorem cost_2651_587_join3_0 : P1_7_1_3.blockEstimate 2651 587 587 2048 = 1096197322325 :=
  @P1_7_1_3.block_append 2651 587 587 1611 1024 1024 2048 313942293077 782255029248 1096197322325 cost_2651_587_join2_0 cost_2651_587_join2_2 rfl rfl rfl

private theorem cost_2651_587_join3_2 : P1_7_1_3.blockEstimate 2651 587 2635 1190 = 285202124187 :=
  @P1_7_1_3.block_append 2651 587 2635 3659 1024 166 1190 284194217868 1007906319 285202124187 cost_2651_587_join2_4 cost_2651_587_join0_24 rfl rfl rfl

private theorem cost_2651_587_join4_0 : P1_7_1_3.blockEstimate 2651 587 587 3238 = 1381399446512 :=
  @P1_7_1_3.block_append 2651 587 587 2635 2048 1190 3238 1096197322325 285202124187 1381399446512 cost_2651_587_join3_0 cost_2651_587_join3_2 rfl rfl rfl

private theorem cost_2651_587_total : P1_7_1_3.momentEstimate 2651 587 = 1381399446512 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2651 + 587 = 3238 by decide]
  exact cost_2651_587_join4_0

theorem moment2651_587 : P1_7_1.groupedPoleMoment 2651 587 ≤ 1381399446512 :=
  (P1_7_1_3.grouped_bound 2651 587).trans_eq cost_2651_587_total
private theorem cost_2677_582_block0 : P1_7_1_3.blockEstimate 2677 582 582 128 = 923646880 := by decide +kernel

private theorem cost_2677_582_block1 : P1_7_1_3.blockEstimate 2677 582 710 128 = 6108679072 := by decide +kernel

private theorem cost_2677_582_block2 : P1_7_1_3.blockEstimate 2677 582 838 128 = 15696681888 := by decide +kernel

private theorem cost_2677_582_block3 : P1_7_1_3.blockEstimate 2677 582 966 128 = 28882348960 := by decide +kernel

private theorem cost_2677_582_block4 : P1_7_1_3.blockEstimate 2677 582 1094 128 = 44793665452 := by decide +kernel

private theorem cost_2677_582_block5 : P1_7_1_3.blockEstimate 2677 582 1222 128 = 60794456448 := by decide +kernel

private theorem cost_2677_582_block6 : P1_7_1_3.blockEstimate 2677 582 1350 128 = 74472737152 := by decide +kernel

private theorem cost_2677_582_block7 : P1_7_1_3.blockEstimate 2677 582 1478 128 = 85705738624 := by decide +kernel

private theorem cost_2677_582_block8 : P1_7_1_3.blockEstimate 2677 582 1606 128 = 94493460864 := by decide +kernel

private theorem cost_2677_582_block9 : P1_7_1_3.blockEstimate 2677 582 1734 128 = 100835903872 := by decide +kernel

private theorem cost_2677_582_block10 : P1_7_1_3.blockEstimate 2677 582 1862 128 = 104733067648 := by decide +kernel

private theorem cost_2677_582_block11 : P1_7_1_3.blockEstimate 2677 582 1990 128 = 106184952192 := by decide +kernel

private theorem cost_2677_582_block12 : P1_7_1_3.blockEstimate 2677 582 2118 128 = 105191557504 := by decide +kernel

private theorem cost_2677_582_block13 : P1_7_1_3.blockEstimate 2677 582 2246 128 = 101752883584 := by decide +kernel

private theorem cost_2677_582_block14 : P1_7_1_3.blockEstimate 2677 582 2374 128 = 95868930432 := by decide +kernel

private theorem cost_2677_582_block15 : P1_7_1_3.blockEstimate 2677 582 2502 128 = 87539698048 := by decide +kernel

private theorem cost_2677_582_block16 : P1_7_1_3.blockEstimate 2677 582 2630 128 = 76837493364 := by decide +kernel

private theorem cost_2677_582_block17 : P1_7_1_3.blockEstimate 2677 582 2758 128 = 64808249986 := by decide +kernel

private theorem cost_2677_582_block18 : P1_7_1_3.blockEstimate 2677 582 2886 128 = 52559951632 := by decide +kernel

private theorem cost_2677_582_block19 : P1_7_1_3.blockEstimate 2677 582 3014 128 = 40636451621 := by decide +kernel

private theorem cost_2677_582_block20 : P1_7_1_3.blockEstimate 2677 582 3142 128 = 29524502644 := by decide +kernel

private theorem cost_2677_582_block21 : P1_7_1_3.blockEstimate 2677 582 3270 128 = 19607345824 := by decide +kernel

private theorem cost_2677_582_block22 : P1_7_1_3.blockEstimate 2677 582 3398 128 = 11392848544 := by decide +kernel

private theorem cost_2677_582_block23 : P1_7_1_3.blockEstimate 2677 582 3526 128 = 5238737568 := by decide +kernel

private theorem cost_2677_582_block24 : P1_7_1_3.blockEstimate 2677 582 3654 128 = 1396671136 := by decide +kernel

private theorem cost_2677_582_block25 : P1_7_1_3.blockEstimate 2677 582 3782 59 = 48879335 := by decide +kernel

private theorem cost_2677_582_join0_0 : P1_7_1_3.blockEstimate 2677 582 582 256 = 7032325952 :=
  @P1_7_1_3.block_append 2677 582 582 710 128 128 256 923646880 6108679072 7032325952 cost_2677_582_block0 cost_2677_582_block1 rfl rfl rfl

private theorem cost_2677_582_join0_2 : P1_7_1_3.blockEstimate 2677 582 838 256 = 44579030848 :=
  @P1_7_1_3.block_append 2677 582 838 966 128 128 256 15696681888 28882348960 44579030848 cost_2677_582_block2 cost_2677_582_block3 rfl rfl rfl

private theorem cost_2677_582_join0_4 : P1_7_1_3.blockEstimate 2677 582 1094 256 = 105588121900 :=
  @P1_7_1_3.block_append 2677 582 1094 1222 128 128 256 44793665452 60794456448 105588121900 cost_2677_582_block4 cost_2677_582_block5 rfl rfl rfl

private theorem cost_2677_582_join0_6 : P1_7_1_3.blockEstimate 2677 582 1350 256 = 160178475776 :=
  @P1_7_1_3.block_append 2677 582 1350 1478 128 128 256 74472737152 85705738624 160178475776 cost_2677_582_block6 cost_2677_582_block7 rfl rfl rfl

private theorem cost_2677_582_join0_8 : P1_7_1_3.blockEstimate 2677 582 1606 256 = 195329364736 :=
  @P1_7_1_3.block_append 2677 582 1606 1734 128 128 256 94493460864 100835903872 195329364736 cost_2677_582_block8 cost_2677_582_block9 rfl rfl rfl

private theorem cost_2677_582_join0_10 : P1_7_1_3.blockEstimate 2677 582 1862 256 = 210918019840 :=
  @P1_7_1_3.block_append 2677 582 1862 1990 128 128 256 104733067648 106184952192 210918019840 cost_2677_582_block10 cost_2677_582_block11 rfl rfl rfl

private theorem cost_2677_582_join0_12 : P1_7_1_3.blockEstimate 2677 582 2118 256 = 206944441088 :=
  @P1_7_1_3.block_append 2677 582 2118 2246 128 128 256 105191557504 101752883584 206944441088 cost_2677_582_block12 cost_2677_582_block13 rfl rfl rfl

private theorem cost_2677_582_join0_14 : P1_7_1_3.blockEstimate 2677 582 2374 256 = 183408628480 :=
  @P1_7_1_3.block_append 2677 582 2374 2502 128 128 256 95868930432 87539698048 183408628480 cost_2677_582_block14 cost_2677_582_block15 rfl rfl rfl

private theorem cost_2677_582_join0_16 : P1_7_1_3.blockEstimate 2677 582 2630 256 = 141645743350 :=
  @P1_7_1_3.block_append 2677 582 2630 2758 128 128 256 76837493364 64808249986 141645743350 cost_2677_582_block16 cost_2677_582_block17 rfl rfl rfl

private theorem cost_2677_582_join0_18 : P1_7_1_3.blockEstimate 2677 582 2886 256 = 93196403253 :=
  @P1_7_1_3.block_append 2677 582 2886 3014 128 128 256 52559951632 40636451621 93196403253 cost_2677_582_block18 cost_2677_582_block19 rfl rfl rfl

private theorem cost_2677_582_join0_20 : P1_7_1_3.blockEstimate 2677 582 3142 256 = 49131848468 :=
  @P1_7_1_3.block_append 2677 582 3142 3270 128 128 256 29524502644 19607345824 49131848468 cost_2677_582_block20 cost_2677_582_block21 rfl rfl rfl

private theorem cost_2677_582_join0_22 : P1_7_1_3.blockEstimate 2677 582 3398 256 = 16631586112 :=
  @P1_7_1_3.block_append 2677 582 3398 3526 128 128 256 11392848544 5238737568 16631586112 cost_2677_582_block22 cost_2677_582_block23 rfl rfl rfl

private theorem cost_2677_582_join0_24 : P1_7_1_3.blockEstimate 2677 582 3654 187 = 1445550471 :=
  @P1_7_1_3.block_append 2677 582 3654 3782 128 59 187 1396671136 48879335 1445550471 cost_2677_582_block24 cost_2677_582_block25 rfl rfl rfl

private theorem cost_2677_582_join1_0 : P1_7_1_3.blockEstimate 2677 582 582 512 = 51611356800 :=
  @P1_7_1_3.block_append 2677 582 582 838 256 256 512 7032325952 44579030848 51611356800 cost_2677_582_join0_0 cost_2677_582_join0_2 rfl rfl rfl

private theorem cost_2677_582_join1_2 : P1_7_1_3.blockEstimate 2677 582 1094 512 = 265766597676 :=
  @P1_7_1_3.block_append 2677 582 1094 1350 256 256 512 105588121900 160178475776 265766597676 cost_2677_582_join0_4 cost_2677_582_join0_6 rfl rfl rfl

private theorem cost_2677_582_join1_4 : P1_7_1_3.blockEstimate 2677 582 1606 512 = 406247384576 :=
  @P1_7_1_3.block_append 2677 582 1606 1862 256 256 512 195329364736 210918019840 406247384576 cost_2677_582_join0_8 cost_2677_582_join0_10 rfl rfl rfl

private theorem cost_2677_582_join1_6 : P1_7_1_3.blockEstimate 2677 582 2118 512 = 390353069568 :=
  @P1_7_1_3.block_append 2677 582 2118 2374 256 256 512 206944441088 183408628480 390353069568 cost_2677_582_join0_12 cost_2677_582_join0_14 rfl rfl rfl

private theorem cost_2677_582_join1_8 : P1_7_1_3.blockEstimate 2677 582 2630 512 = 234842146603 :=
  @P1_7_1_3.block_append 2677 582 2630 2886 256 256 512 141645743350 93196403253 234842146603 cost_2677_582_join0_16 cost_2677_582_join0_18 rfl rfl rfl

private theorem cost_2677_582_join1_10 : P1_7_1_3.blockEstimate 2677 582 3142 512 = 65763434580 :=
  @P1_7_1_3.block_append 2677 582 3142 3398 256 256 512 49131848468 16631586112 65763434580 cost_2677_582_join0_20 cost_2677_582_join0_22 rfl rfl rfl

private theorem cost_2677_582_join2_0 : P1_7_1_3.blockEstimate 2677 582 582 1024 = 317377954476 :=
  @P1_7_1_3.block_append 2677 582 582 1094 512 512 1024 51611356800 265766597676 317377954476 cost_2677_582_join1_0 cost_2677_582_join1_2 rfl rfl rfl

private theorem cost_2677_582_join2_2 : P1_7_1_3.blockEstimate 2677 582 1606 1024 = 796600454144 :=
  @P1_7_1_3.block_append 2677 582 1606 2118 512 512 1024 406247384576 390353069568 796600454144 cost_2677_582_join1_4 cost_2677_582_join1_6 rfl rfl rfl

private theorem cost_2677_582_join2_4 : P1_7_1_3.blockEstimate 2677 582 2630 1024 = 300605581183 :=
  @P1_7_1_3.block_append 2677 582 2630 3142 512 512 1024 234842146603 65763434580 300605581183 cost_2677_582_join1_8 cost_2677_582_join1_10 rfl rfl rfl

private theorem cost_2677_582_join3_0 : P1_7_1_3.blockEstimate 2677 582 582 2048 = 1113978408620 :=
  @P1_7_1_3.block_append 2677 582 582 1606 1024 1024 2048 317377954476 796600454144 1113978408620 cost_2677_582_join2_0 cost_2677_582_join2_2 rfl rfl rfl

private theorem cost_2677_582_join3_2 : P1_7_1_3.blockEstimate 2677 582 2630 1211 = 302051131654 :=
  @P1_7_1_3.block_append 2677 582 2630 3654 1024 187 1211 300605581183 1445550471 302051131654 cost_2677_582_join2_4 cost_2677_582_join0_24 rfl rfl rfl

private theorem cost_2677_582_join4_0 : P1_7_1_3.blockEstimate 2677 582 582 3259 = 1416029540274 :=
  @P1_7_1_3.block_append 2677 582 582 2630 2048 1211 3259 1113978408620 302051131654 1416029540274 cost_2677_582_join3_0 cost_2677_582_join3_2 rfl rfl rfl

private theorem cost_2677_582_total : P1_7_1_3.momentEstimate 2677 582 = 1416029540274 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2677 + 582 = 3259 by decide]
  exact cost_2677_582_join4_0

theorem moment2677_582 : P1_7_1.groupedPoleMoment 2677 582 ≤ 1416029540274 :=
  (P1_7_1_3.grouped_bound 2677 582).trans_eq cost_2677_582_total
private theorem cost_2707_582_block0 : P1_7_1_3.blockEstimate 2707 582 582 128 = 934379680 := by decide +kernel

private theorem cost_2707_582_block1 : P1_7_1_3.blockEstimate 2707 582 710 128 = 6182817952 := by decide +kernel

private theorem cost_2707_582_block2 : P1_7_1_3.blockEstimate 2707 582 838 128 = 15897141408 := by decide +kernel

private theorem cost_2707_582_block3 : P1_7_1_3.blockEstimate 2707 582 966 128 = 29272043680 := by decide +kernel

private theorem cost_2707_582_block4 : P1_7_1_3.blockEstimate 2707 582 1094 128 = 45434534662 := by decide +kernel

private theorem cost_2707_582_block5 : P1_7_1_3.blockEstimate 2707 582 1222 128 = 61720167168 := by decide +kernel

private theorem cost_2707_582_block6 : P1_7_1_3.blockEstimate 2707 582 1350 128 = 75685004032 := by decide +kernel

private theorem cost_2707_582_block7 : P1_7_1_3.blockEstimate 2707 582 1478 128 = 87204561664 := by decide +kernel

private theorem cost_2707_582_block8 : P1_7_1_3.blockEstimate 2707 582 1606 128 = 96278840064 := by decide +kernel

private theorem cost_2707_582_block9 : P1_7_1_3.blockEstimate 2707 582 1734 128 = 102907839232 := by decide +kernel

private theorem cost_2707_582_block10 : P1_7_1_3.blockEstimate 2707 582 1862 128 = 107091559168 := by decide +kernel

private theorem cost_2707_582_block11 : P1_7_1_3.blockEstimate 2707 582 1990 128 = 108829999872 := by decide +kernel

private theorem cost_2707_582_block12 : P1_7_1_3.blockEstimate 2707 582 2118 128 = 108123161344 := by decide +kernel

private theorem cost_2707_582_block13 : P1_7_1_3.blockEstimate 2707 582 2246 128 = 104971043584 := by decide +kernel

private theorem cost_2707_582_block14 : P1_7_1_3.blockEstimate 2707 582 2374 128 = 99373646592 := by decide +kernel

private theorem cost_2707_582_block15 : P1_7_1_3.blockEstimate 2707 582 2502 128 = 91330970368 := by decide +kernel

private theorem cost_2707_582_block16 : P1_7_1_3.blockEstimate 2707 582 2630 128 = 80861214136 := by decide +kernel

private theorem cost_2707_582_block17 : P1_7_1_3.blockEstimate 2707 582 2758 128 = 68730281404 := by decide +kernel

private theorem cost_2707_582_block18 : P1_7_1_3.blockEstimate 2707 582 2886 128 = 56238687167 := by decide +kernel

private theorem cost_2707_582_block19 : P1_7_1_3.blockEstimate 2707 582 3014 128 = 43982712646 := by decide +kernel

private theorem cost_2707_582_block20 : P1_7_1_3.blockEstimate 2707 582 3142 128 = 32460149094 := by decide +kernel

private theorem cost_2707_582_block21 : P1_7_1_3.blockEstimate 2707 582 3270 128 = 22081293221 := by decide +kernel

private theorem cost_2707_582_block22 : P1_7_1_3.blockEstimate 2707 582 3398 128 = 13305630416 := by decide +kernel

private theorem cost_2707_582_block23 : P1_7_1_3.blockEstimate 2707 582 3526 128 = 6560881360 := by decide +kernel

private theorem cost_2707_582_block24 : P1_7_1_3.blockEstimate 2707 582 3654 128 = 2100651728 := by decide +kernel

private theorem cost_2707_582_block25 : P1_7_1_3.blockEstimate 2707 582 3782 89 = 164635472 := by decide +kernel

private theorem cost_2707_582_join0_0 : P1_7_1_3.blockEstimate 2707 582 582 256 = 7117197632 :=
  @P1_7_1_3.block_append 2707 582 582 710 128 128 256 934379680 6182817952 7117197632 cost_2707_582_block0 cost_2707_582_block1 rfl rfl rfl

private theorem cost_2707_582_join0_2 : P1_7_1_3.blockEstimate 2707 582 838 256 = 45169185088 :=
  @P1_7_1_3.block_append 2707 582 838 966 128 128 256 15897141408 29272043680 45169185088 cost_2707_582_block2 cost_2707_582_block3 rfl rfl rfl

private theorem cost_2707_582_join0_4 : P1_7_1_3.blockEstimate 2707 582 1094 256 = 107154701830 :=
  @P1_7_1_3.block_append 2707 582 1094 1222 128 128 256 45434534662 61720167168 107154701830 cost_2707_582_block4 cost_2707_582_block5 rfl rfl rfl

private theorem cost_2707_582_join0_6 : P1_7_1_3.blockEstimate 2707 582 1350 256 = 162889565696 :=
  @P1_7_1_3.block_append 2707 582 1350 1478 128 128 256 75685004032 87204561664 162889565696 cost_2707_582_block6 cost_2707_582_block7 rfl rfl rfl

private theorem cost_2707_582_join0_8 : P1_7_1_3.blockEstimate 2707 582 1606 256 = 199186679296 :=
  @P1_7_1_3.block_append 2707 582 1606 1734 128 128 256 96278840064 102907839232 199186679296 cost_2707_582_block8 cost_2707_582_block9 rfl rfl rfl

private theorem cost_2707_582_join0_10 : P1_7_1_3.blockEstimate 2707 582 1862 256 = 215921559040 :=
  @P1_7_1_3.block_append 2707 582 1862 1990 128 128 256 107091559168 108829999872 215921559040 cost_2707_582_block10 cost_2707_582_block11 rfl rfl rfl

private theorem cost_2707_582_join0_12 : P1_7_1_3.blockEstimate 2707 582 2118 256 = 213094204928 :=
  @P1_7_1_3.block_append 2707 582 2118 2246 128 128 256 108123161344 104971043584 213094204928 cost_2707_582_block12 cost_2707_582_block13 rfl rfl rfl

private theorem cost_2707_582_join0_14 : P1_7_1_3.blockEstimate 2707 582 2374 256 = 190704616960 :=
  @P1_7_1_3.block_append 2707 582 2374 2502 128 128 256 99373646592 91330970368 190704616960 cost_2707_582_block14 cost_2707_582_block15 rfl rfl rfl

private theorem cost_2707_582_join0_16 : P1_7_1_3.blockEstimate 2707 582 2630 256 = 149591495540 :=
  @P1_7_1_3.block_append 2707 582 2630 2758 128 128 256 80861214136 68730281404 149591495540 cost_2707_582_block16 cost_2707_582_block17 rfl rfl rfl

private theorem cost_2707_582_join0_18 : P1_7_1_3.blockEstimate 2707 582 2886 256 = 100221399813 :=
  @P1_7_1_3.block_append 2707 582 2886 3014 128 128 256 56238687167 43982712646 100221399813 cost_2707_582_block18 cost_2707_582_block19 rfl rfl rfl

private theorem cost_2707_582_join0_20 : P1_7_1_3.blockEstimate 2707 582 3142 256 = 54541442315 :=
  @P1_7_1_3.block_append 2707 582 3142 3270 128 128 256 32460149094 22081293221 54541442315 cost_2707_582_block20 cost_2707_582_block21 rfl rfl rfl

private theorem cost_2707_582_join0_22 : P1_7_1_3.blockEstimate 2707 582 3398 256 = 19866511776 :=
  @P1_7_1_3.block_append 2707 582 3398 3526 128 128 256 13305630416 6560881360 19866511776 cost_2707_582_block22 cost_2707_582_block23 rfl rfl rfl

private theorem cost_2707_582_join0_24 : P1_7_1_3.blockEstimate 2707 582 3654 217 = 2265287200 :=
  @P1_7_1_3.block_append 2707 582 3654 3782 128 89 217 2100651728 164635472 2265287200 cost_2707_582_block24 cost_2707_582_block25 rfl rfl rfl

private theorem cost_2707_582_join1_0 : P1_7_1_3.blockEstimate 2707 582 582 512 = 52286382720 :=
  @P1_7_1_3.block_append 2707 582 582 838 256 256 512 7117197632 45169185088 52286382720 cost_2707_582_join0_0 cost_2707_582_join0_2 rfl rfl rfl

private theorem cost_2707_582_join1_2 : P1_7_1_3.blockEstimate 2707 582 1094 512 = 270044267526 :=
  @P1_7_1_3.block_append 2707 582 1094 1350 256 256 512 107154701830 162889565696 270044267526 cost_2707_582_join0_4 cost_2707_582_join0_6 rfl rfl rfl

private theorem cost_2707_582_join1_4 : P1_7_1_3.blockEstimate 2707 582 1606 512 = 415108238336 :=
  @P1_7_1_3.block_append 2707 582 1606 1862 256 256 512 199186679296 215921559040 415108238336 cost_2707_582_join0_8 cost_2707_582_join0_10 rfl rfl rfl

private theorem cost_2707_582_join1_6 : P1_7_1_3.blockEstimate 2707 582 2118 512 = 403798821888 :=
  @P1_7_1_3.block_append 2707 582 2118 2374 256 256 512 213094204928 190704616960 403798821888 cost_2707_582_join0_12 cost_2707_582_join0_14 rfl rfl rfl

private theorem cost_2707_582_join1_8 : P1_7_1_3.blockEstimate 2707 582 2630 512 = 249812895353 :=
  @P1_7_1_3.block_append 2707 582 2630 2886 256 256 512 149591495540 100221399813 249812895353 cost_2707_582_join0_16 cost_2707_582_join0_18 rfl rfl rfl

private theorem cost_2707_582_join1_10 : P1_7_1_3.blockEstimate 2707 582 3142 512 = 74407954091 :=
  @P1_7_1_3.block_append 2707 582 3142 3398 256 256 512 54541442315 19866511776 74407954091 cost_2707_582_join0_20 cost_2707_582_join0_22 rfl rfl rfl

private theorem cost_2707_582_join2_0 : P1_7_1_3.blockEstimate 2707 582 582 1024 = 322330650246 :=
  @P1_7_1_3.block_append 2707 582 582 1094 512 512 1024 52286382720 270044267526 322330650246 cost_2707_582_join1_0 cost_2707_582_join1_2 rfl rfl rfl

private theorem cost_2707_582_join2_2 : P1_7_1_3.blockEstimate 2707 582 1606 1024 = 818907060224 :=
  @P1_7_1_3.block_append 2707 582 1606 2118 512 512 1024 415108238336 403798821888 818907060224 cost_2707_582_join1_4 cost_2707_582_join1_6 rfl rfl rfl

private theorem cost_2707_582_join2_4 : P1_7_1_3.blockEstimate 2707 582 2630 1024 = 324220849444 :=
  @P1_7_1_3.block_append 2707 582 2630 3142 512 512 1024 249812895353 74407954091 324220849444 cost_2707_582_join1_8 cost_2707_582_join1_10 rfl rfl rfl

private theorem cost_2707_582_join3_0 : P1_7_1_3.blockEstimate 2707 582 582 2048 = 1141237710470 :=
  @P1_7_1_3.block_append 2707 582 582 1606 1024 1024 2048 322330650246 818907060224 1141237710470 cost_2707_582_join2_0 cost_2707_582_join2_2 rfl rfl rfl

private theorem cost_2707_582_join3_2 : P1_7_1_3.blockEstimate 2707 582 2630 1241 = 326486136644 :=
  @P1_7_1_3.block_append 2707 582 2630 3654 1024 217 1241 324220849444 2265287200 326486136644 cost_2707_582_join2_4 cost_2707_582_join0_24 rfl rfl rfl

private theorem cost_2707_582_join4_0 : P1_7_1_3.blockEstimate 2707 582 582 3289 = 1467723847114 :=
  @P1_7_1_3.block_append 2707 582 582 2630 2048 1241 3289 1141237710470 326486136644 1467723847114 cost_2707_582_join3_0 cost_2707_582_join3_2 rfl rfl rfl

private theorem cost_2707_582_total : P1_7_1_3.momentEstimate 2707 582 = 1467723847114 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2707 + 582 = 3289 by decide]
  exact cost_2707_582_join4_0

theorem moment2707_582 : P1_7_1.groupedPoleMoment 2707 582 ≤ 1467723847114 :=
  (P1_7_1_3.grouped_bound 2707 582).trans_eq cost_2707_582_total
private theorem cost_2719_584_block0 : P1_7_1_3.blockEstimate 2719 584 584 128 = 938672800 := by decide +kernel

private theorem cost_2719_584_block1 : P1_7_1_3.blockEstimate 2719 584 712 128 = 6212473504 := by decide +kernel

private theorem cost_2719_584_block2 : P1_7_1_3.blockEstimate 2719 584 840 128 = 15977325216 := by decide +kernel

private theorem cost_2719_584_block3 : P1_7_1_3.blockEstimate 2719 584 968 128 = 29427921568 := by decide +kernel

private theorem cost_2719_584_block4 : P1_7_1_3.blockEstimate 2719 584 1096 128 = 45697700382 := by decide +kernel

private theorem cost_2719_584_block5 : P1_7_1_3.blockEstimate 2719 584 1224 128 = 62152534080 := by decide +kernel

private theorem cost_2719_584_block6 : P1_7_1_3.blockEstimate 2719 584 1352 128 = 76289878080 := by decide +kernel

private theorem cost_2719_584_block7 : P1_7_1_3.blockEstimate 2719 584 1480 128 = 87973554240 := by decide +kernel

private theorem cost_2719_584_block8 : P1_7_1_3.blockEstimate 2719 584 1608 128 = 97203562560 := by decide +kernel

private theorem cost_2719_584_block9 : P1_7_1_3.blockEstimate 2719 584 1736 128 = 103979903040 := by decide +kernel

private theorem cost_2719_584_block10 : P1_7_1_3.blockEstimate 2719 584 1864 128 = 108302575680 := by decide +kernel

private theorem cost_2719_584_block11 : P1_7_1_3.blockEstimate 2719 584 1992 128 = 110171580480 := by decide +kernel

private theorem cost_2719_584_block12 : P1_7_1_3.blockEstimate 2719 584 2120 128 = 109586917440 := by decide +kernel

private theorem cost_2719_584_block13 : P1_7_1_3.blockEstimate 2719 584 2248 128 = 106548586560 := by decide +kernel

private theorem cost_2719_584_block14 : P1_7_1_3.blockEstimate 2719 584 2376 128 = 101056587840 := by decide +kernel

private theorem cost_2719_584_block15 : P1_7_1_3.blockEstimate 2719 584 2504 128 = 93110921280 := by decide +kernel

private theorem cost_2719_584_block16 : P1_7_1_3.blockEstimate 2719 584 2632 128 = 82721087210 := by decide +kernel

private theorem cost_2719_584_block17 : P1_7_1_3.blockEstimate 2719 584 2760 128 = 70554139074 := by decide +kernel

private theorem cost_2719_584_block18 : P1_7_1_3.blockEstimate 2719 584 2888 128 = 57958380262 := by decide +kernel

private theorem cost_2719_584_block19 : P1_7_1_3.blockEstimate 2719 584 3016 128 = 45557760410 := by decide +kernel

private theorem cost_2719_584_block20 : P1_7_1_3.blockEstimate 2719 584 3144 128 = 33853874732 := by decide +kernel

private theorem cost_2719_584_block21 : P1_7_1_3.blockEstimate 2719 584 3272 128 = 23268081929 := by decide +kernel

private theorem cost_2719_584_block22 : P1_7_1_3.blockEstimate 2719 584 3400 128 = 14240922496 := by decide +kernel

private theorem cost_2719_584_block23 : P1_7_1_3.blockEstimate 2719 584 3528 128 = 7226133376 := by decide +kernel

private theorem cost_2719_584_block24 : P1_7_1_3.blockEstimate 2719 584 3656 128 = 2480921472 := by decide +kernel

private theorem cost_2719_584_block25 : P1_7_1_3.blockEstimate 2719 584 3784 103 = 254000552 := by decide +kernel

private theorem cost_2719_584_join0_0 : P1_7_1_3.blockEstimate 2719 584 584 256 = 7151146304 :=
  @P1_7_1_3.block_append 2719 584 584 712 128 128 256 938672800 6212473504 7151146304 cost_2719_584_block0 cost_2719_584_block1 rfl rfl rfl

private theorem cost_2719_584_join0_2 : P1_7_1_3.blockEstimate 2719 584 840 256 = 45405246784 :=
  @P1_7_1_3.block_append 2719 584 840 968 128 128 256 15977325216 29427921568 45405246784 cost_2719_584_block2 cost_2719_584_block3 rfl rfl rfl

private theorem cost_2719_584_join0_4 : P1_7_1_3.blockEstimate 2719 584 1096 256 = 107850234462 :=
  @P1_7_1_3.block_append 2719 584 1096 1224 128 128 256 45697700382 62152534080 107850234462 cost_2719_584_block4 cost_2719_584_block5 rfl rfl rfl

private theorem cost_2719_584_join0_6 : P1_7_1_3.blockEstimate 2719 584 1352 256 = 164263432320 :=
  @P1_7_1_3.block_append 2719 584 1352 1480 128 128 256 76289878080 87973554240 164263432320 cost_2719_584_block6 cost_2719_584_block7 rfl rfl rfl

private theorem cost_2719_584_join0_8 : P1_7_1_3.blockEstimate 2719 584 1608 256 = 201183465600 :=
  @P1_7_1_3.block_append 2719 584 1608 1736 128 128 256 97203562560 103979903040 201183465600 cost_2719_584_block8 cost_2719_584_block9 rfl rfl rfl

private theorem cost_2719_584_join0_10 : P1_7_1_3.blockEstimate 2719 584 1864 256 = 218474156160 :=
  @P1_7_1_3.block_append 2719 584 1864 1992 128 128 256 108302575680 110171580480 218474156160 cost_2719_584_block10 cost_2719_584_block11 rfl rfl rfl

private theorem cost_2719_584_join0_12 : P1_7_1_3.blockEstimate 2719 584 2120 256 = 216135504000 :=
  @P1_7_1_3.block_append 2719 584 2120 2248 128 128 256 109586917440 106548586560 216135504000 cost_2719_584_block12 cost_2719_584_block13 rfl rfl rfl

private theorem cost_2719_584_join0_14 : P1_7_1_3.blockEstimate 2719 584 2376 256 = 194167509120 :=
  @P1_7_1_3.block_append 2719 584 2376 2504 128 128 256 101056587840 93110921280 194167509120 cost_2719_584_block14 cost_2719_584_block15 rfl rfl rfl

private theorem cost_2719_584_join0_16 : P1_7_1_3.blockEstimate 2719 584 2632 256 = 153275226284 :=
  @P1_7_1_3.block_append 2719 584 2632 2760 128 128 256 82721087210 70554139074 153275226284 cost_2719_584_block16 cost_2719_584_block17 rfl rfl rfl

private theorem cost_2719_584_join0_18 : P1_7_1_3.blockEstimate 2719 584 2888 256 = 103516140672 :=
  @P1_7_1_3.block_append 2719 584 2888 3016 128 128 256 57958380262 45557760410 103516140672 cost_2719_584_block18 cost_2719_584_block19 rfl rfl rfl

private theorem cost_2719_584_join0_20 : P1_7_1_3.blockEstimate 2719 584 3144 256 = 57121956661 :=
  @P1_7_1_3.block_append 2719 584 3144 3272 128 128 256 33853874732 23268081929 57121956661 cost_2719_584_block20 cost_2719_584_block21 rfl rfl rfl

private theorem cost_2719_584_join0_22 : P1_7_1_3.blockEstimate 2719 584 3400 256 = 21467055872 :=
  @P1_7_1_3.block_append 2719 584 3400 3528 128 128 256 14240922496 7226133376 21467055872 cost_2719_584_block22 cost_2719_584_block23 rfl rfl rfl

private theorem cost_2719_584_join0_24 : P1_7_1_3.blockEstimate 2719 584 3656 231 = 2734922024 :=
  @P1_7_1_3.block_append 2719 584 3656 3784 128 103 231 2480921472 254000552 2734922024 cost_2719_584_block24 cost_2719_584_block25 rfl rfl rfl

private theorem cost_2719_584_join1_0 : P1_7_1_3.blockEstimate 2719 584 584 512 = 52556393088 :=
  @P1_7_1_3.block_append 2719 584 584 840 256 256 512 7151146304 45405246784 52556393088 cost_2719_584_join0_0 cost_2719_584_join0_2 rfl rfl rfl

private theorem cost_2719_584_join1_2 : P1_7_1_3.blockEstimate 2719 584 1096 512 = 272113666782 :=
  @P1_7_1_3.block_append 2719 584 1096 1352 256 256 512 107850234462 164263432320 272113666782 cost_2719_584_join0_4 cost_2719_584_join0_6 rfl rfl rfl

private theorem cost_2719_584_join1_4 : P1_7_1_3.blockEstimate 2719 584 1608 512 = 419657621760 :=
  @P1_7_1_3.block_append 2719 584 1608 1864 256 256 512 201183465600 218474156160 419657621760 cost_2719_584_join0_8 cost_2719_584_join0_10 rfl rfl rfl

private theorem cost_2719_584_join1_6 : P1_7_1_3.blockEstimate 2719 584 2120 512 = 410303013120 :=
  @P1_7_1_3.block_append 2719 584 2120 2376 256 256 512 216135504000 194167509120 410303013120 cost_2719_584_join0_12 cost_2719_584_join0_14 rfl rfl rfl

private theorem cost_2719_584_join1_8 : P1_7_1_3.blockEstimate 2719 584 2632 512 = 256791366956 :=
  @P1_7_1_3.block_append 2719 584 2632 2888 256 256 512 153275226284 103516140672 256791366956 cost_2719_584_join0_16 cost_2719_584_join0_18 rfl rfl rfl

private theorem cost_2719_584_join1_10 : P1_7_1_3.blockEstimate 2719 584 3144 512 = 78589012533 :=
  @P1_7_1_3.block_append 2719 584 3144 3400 256 256 512 57121956661 21467055872 78589012533 cost_2719_584_join0_20 cost_2719_584_join0_22 rfl rfl rfl

private theorem cost_2719_584_join2_0 : P1_7_1_3.blockEstimate 2719 584 584 1024 = 324670059870 :=
  @P1_7_1_3.block_append 2719 584 584 1096 512 512 1024 52556393088 272113666782 324670059870 cost_2719_584_join1_0 cost_2719_584_join1_2 rfl rfl rfl

private theorem cost_2719_584_join2_2 : P1_7_1_3.blockEstimate 2719 584 1608 1024 = 829960634880 :=
  @P1_7_1_3.block_append 2719 584 1608 2120 512 512 1024 419657621760 410303013120 829960634880 cost_2719_584_join1_4 cost_2719_584_join1_6 rfl rfl rfl

private theorem cost_2719_584_join2_4 : P1_7_1_3.blockEstimate 2719 584 2632 1024 = 335380379489 :=
  @P1_7_1_3.block_append 2719 584 2632 3144 512 512 1024 256791366956 78589012533 335380379489 cost_2719_584_join1_8 cost_2719_584_join1_10 rfl rfl rfl

private theorem cost_2719_584_join3_0 : P1_7_1_3.blockEstimate 2719 584 584 2048 = 1154630694750 :=
  @P1_7_1_3.block_append 2719 584 584 1608 1024 1024 2048 324670059870 829960634880 1154630694750 cost_2719_584_join2_0 cost_2719_584_join2_2 rfl rfl rfl

private theorem cost_2719_584_join3_2 : P1_7_1_3.blockEstimate 2719 584 2632 1255 = 338115301513 :=
  @P1_7_1_3.block_append 2719 584 2632 3656 1024 231 1255 335380379489 2734922024 338115301513 cost_2719_584_join2_4 cost_2719_584_join0_24 rfl rfl rfl

private theorem cost_2719_584_join4_0 : P1_7_1_3.blockEstimate 2719 584 584 3303 = 1492745996263 :=
  @P1_7_1_3.block_append 2719 584 584 2632 2048 1255 3303 1154630694750 338115301513 1492745996263 cost_2719_584_join3_0 cost_2719_584_join3_2 rfl rfl rfl

private theorem cost_2719_584_total : P1_7_1_3.momentEstimate 2719 584 = 1492745996263 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2719 + 584 = 3303 by decide]
  exact cost_2719_584_join4_0

theorem moment2719_584 : P1_7_1.groupedPoleMoment 2719 584 ≤ 1492745996263 :=
  (P1_7_1_3.grouped_bound 2719 584).trans_eq cost_2719_584_total
private theorem cost_2784_598_block0 : P1_7_1_3.blockEstimate 2784 598 598 128 = 961927200 := by decide +kernel

private theorem cost_2784_598_block1 : P1_7_1_3.blockEstimate 2784 598 726 128 = 6373107744 := by decide +kernel

private theorem cost_2784_598_block2 : P1_7_1_3.blockEstimate 2784 598 854 128 = 16411654176 := by decide +kernel

private theorem cost_2784_598_block3 : P1_7_1_3.blockEstimate 2784 598 982 128 = 30272260128 := by decide +kernel

private theorem cost_2784_598_block4 : P1_7_1_3.blockEstimate 2784 598 1110 128 = 47123024377 := by decide +kernel

private theorem cost_2784_598_block5 : P1_7_1_3.blockEstimate 2784 598 1238 128 = 64579100480 := by decide +kernel

private theorem cost_2784_598_block6 : P1_7_1_3.blockEstimate 2784 598 1366 128 = 79761383232 := by decide +kernel

private theorem cost_2784_598_block7 : P1_7_1_3.blockEstimate 2784 598 1494 128 = 92431277888 := by decide +kernel

private theorem cost_2784_598_block8 : P1_7_1_3.blockEstimate 2784 598 1622 128 = 102588784448 := by decide +kernel

private theorem cost_2784_598_block9 : P1_7_1_3.blockEstimate 2784 598 1750 128 = 110233902912 := by decide +kernel

private theorem cost_2784_598_block10 : P1_7_1_3.blockEstimate 2784 598 1878 128 = 115366633280 := by decide +kernel

private theorem cost_2784_598_block11 : P1_7_1_3.blockEstimate 2784 598 2006 128 = 117986975552 := by decide +kernel

private theorem cost_2784_598_block12 : P1_7_1_3.blockEstimate 2784 598 2134 128 = 118094929728 := by decide +kernel

private theorem cost_2784_598_block13 : P1_7_1_3.blockEstimate 2784 598 2262 128 = 115690495808 := by decide +kernel

private theorem cost_2784_598_block14 : P1_7_1_3.blockEstimate 2784 598 2390 128 = 110773673792 := by decide +kernel

private theorem cost_2784_598_block15 : P1_7_1_3.blockEstimate 2784 598 2518 128 = 103344463680 := by decide +kernel

private theorem cost_2784_598_block16 : P1_7_1_3.blockEstimate 2784 598 2646 128 = 93402865472 := by decide +kernel

private theorem cost_2784_598_block17 : P1_7_1_3.blockEstimate 2784 598 2774 128 = 81187220930 := by decide +kernel

private theorem cost_2784_598_block18 : P1_7_1_3.blockEstimate 2784 598 2902 128 = 68062170585 := by decide +kernel

private theorem cost_2784_598_block19 : P1_7_1_3.blockEstimate 2784 598 3030 128 = 54901274630 := by decide +kernel

private theorem cost_2784_598_block20 : P1_7_1_3.blockEstimate 2784 598 3158 128 = 42225772724 := by decide +kernel

private theorem cost_2784_598_block21 : P1_7_1_3.blockEstimate 2784 598 3286 128 = 30508433207 := by decide +kernel

private theorem cost_2784_598_block22 : P1_7_1_3.blockEstimate 2784 598 3414 128 = 20123583216 := by decide +kernel

private theorem cost_2784_598_block23 : P1_7_1_3.blockEstimate 2784 598 3542 128 = 11599605488 := by decide +kernel

private theorem cost_2784_598_block24 : P1_7_1_3.blockEstimate 2784 598 3670 128 = 5258042096 := by decide +kernel

private theorem cost_2784_598_block25 : P1_7_1_3.blockEstimate 2784 598 3798 128 = 1350551280 := by decide +kernel

private theorem cost_2784_598_block26 : P1_7_1_3.blockEstimate 2784 598 3926 54 = 39287591 := by decide +kernel

private theorem cost_2784_598_join0_0 : P1_7_1_3.blockEstimate 2784 598 598 256 = 7335034944 :=
  @P1_7_1_3.block_append 2784 598 598 726 128 128 256 961927200 6373107744 7335034944 cost_2784_598_block0 cost_2784_598_block1 rfl rfl rfl

private theorem cost_2784_598_join0_2 : P1_7_1_3.blockEstimate 2784 598 854 256 = 46683914304 :=
  @P1_7_1_3.block_append 2784 598 854 982 128 128 256 16411654176 30272260128 46683914304 cost_2784_598_block2 cost_2784_598_block3 rfl rfl rfl

private theorem cost_2784_598_join0_4 : P1_7_1_3.blockEstimate 2784 598 1110 256 = 111702124857 :=
  @P1_7_1_3.block_append 2784 598 1110 1238 128 128 256 47123024377 64579100480 111702124857 cost_2784_598_block4 cost_2784_598_block5 rfl rfl rfl

private theorem cost_2784_598_join0_6 : P1_7_1_3.blockEstimate 2784 598 1366 256 = 172192661120 :=
  @P1_7_1_3.block_append 2784 598 1366 1494 128 128 256 79761383232 92431277888 172192661120 cost_2784_598_block6 cost_2784_598_block7 rfl rfl rfl

private theorem cost_2784_598_join0_8 : P1_7_1_3.blockEstimate 2784 598 1622 256 = 212822687360 :=
  @P1_7_1_3.block_append 2784 598 1622 1750 128 128 256 102588784448 110233902912 212822687360 cost_2784_598_block8 cost_2784_598_block9 rfl rfl rfl

private theorem cost_2784_598_join0_10 : P1_7_1_3.blockEstimate 2784 598 1878 256 = 233353608832 :=
  @P1_7_1_3.block_append 2784 598 1878 2006 128 128 256 115366633280 117986975552 233353608832 cost_2784_598_block10 cost_2784_598_block11 rfl rfl rfl

private theorem cost_2784_598_join0_12 : P1_7_1_3.blockEstimate 2784 598 2134 256 = 233785425536 :=
  @P1_7_1_3.block_append 2784 598 2134 2262 128 128 256 118094929728 115690495808 233785425536 cost_2784_598_block12 cost_2784_598_block13 rfl rfl rfl

private theorem cost_2784_598_join0_14 : P1_7_1_3.blockEstimate 2784 598 2390 256 = 214118137472 :=
  @P1_7_1_3.block_append 2784 598 2390 2518 128 128 256 110773673792 103344463680 214118137472 cost_2784_598_block14 cost_2784_598_block15 rfl rfl rfl

private theorem cost_2784_598_join0_16 : P1_7_1_3.blockEstimate 2784 598 2646 256 = 174590086402 :=
  @P1_7_1_3.block_append 2784 598 2646 2774 128 128 256 93402865472 81187220930 174590086402 cost_2784_598_block16 cost_2784_598_block17 rfl rfl rfl

private theorem cost_2784_598_join0_18 : P1_7_1_3.blockEstimate 2784 598 2902 256 = 122963445215 :=
  @P1_7_1_3.block_append 2784 598 2902 3030 128 128 256 68062170585 54901274630 122963445215 cost_2784_598_block18 cost_2784_598_block19 rfl rfl rfl

private theorem cost_2784_598_join0_20 : P1_7_1_3.blockEstimate 2784 598 3158 256 = 72734205931 :=
  @P1_7_1_3.block_append 2784 598 3158 3286 128 128 256 42225772724 30508433207 72734205931 cost_2784_598_block20 cost_2784_598_block21 rfl rfl rfl

private theorem cost_2784_598_join0_22 : P1_7_1_3.blockEstimate 2784 598 3414 256 = 31723188704 :=
  @P1_7_1_3.block_append 2784 598 3414 3542 128 128 256 20123583216 11599605488 31723188704 cost_2784_598_block22 cost_2784_598_block23 rfl rfl rfl

private theorem cost_2784_598_join0_24 : P1_7_1_3.blockEstimate 2784 598 3670 256 = 6608593376 :=
  @P1_7_1_3.block_append 2784 598 3670 3798 128 128 256 5258042096 1350551280 6608593376 cost_2784_598_block24 cost_2784_598_block25 rfl rfl rfl

private theorem cost_2784_598_join1_0 : P1_7_1_3.blockEstimate 2784 598 598 512 = 54018949248 :=
  @P1_7_1_3.block_append 2784 598 598 854 256 256 512 7335034944 46683914304 54018949248 cost_2784_598_join0_0 cost_2784_598_join0_2 rfl rfl rfl

private theorem cost_2784_598_join1_2 : P1_7_1_3.blockEstimate 2784 598 1110 512 = 283894785977 :=
  @P1_7_1_3.block_append 2784 598 1110 1366 256 256 512 111702124857 172192661120 283894785977 cost_2784_598_join0_4 cost_2784_598_join0_6 rfl rfl rfl

private theorem cost_2784_598_join1_4 : P1_7_1_3.blockEstimate 2784 598 1622 512 = 446176296192 :=
  @P1_7_1_3.block_append 2784 598 1622 1878 256 256 512 212822687360 233353608832 446176296192 cost_2784_598_join0_8 cost_2784_598_join0_10 rfl rfl rfl

private theorem cost_2784_598_join1_6 : P1_7_1_3.blockEstimate 2784 598 2134 512 = 447903563008 :=
  @P1_7_1_3.block_append 2784 598 2134 2390 256 256 512 233785425536 214118137472 447903563008 cost_2784_598_join0_12 cost_2784_598_join0_14 rfl rfl rfl

private theorem cost_2784_598_join1_8 : P1_7_1_3.blockEstimate 2784 598 2646 512 = 297553531617 :=
  @P1_7_1_3.block_append 2784 598 2646 2902 256 256 512 174590086402 122963445215 297553531617 cost_2784_598_join0_16 cost_2784_598_join0_18 rfl rfl rfl

private theorem cost_2784_598_join1_10 : P1_7_1_3.blockEstimate 2784 598 3158 512 = 104457394635 :=
  @P1_7_1_3.block_append 2784 598 3158 3414 256 256 512 72734205931 31723188704 104457394635 cost_2784_598_join0_20 cost_2784_598_join0_22 rfl rfl rfl

private theorem cost_2784_598_join1_12 : P1_7_1_3.blockEstimate 2784 598 3670 310 = 6647880967 :=
  @P1_7_1_3.block_append 2784 598 3670 3926 256 54 310 6608593376 39287591 6647880967 cost_2784_598_join0_24 cost_2784_598_block26 rfl rfl rfl

private theorem cost_2784_598_join2_0 : P1_7_1_3.blockEstimate 2784 598 598 1024 = 337913735225 :=
  @P1_7_1_3.block_append 2784 598 598 1110 512 512 1024 54018949248 283894785977 337913735225 cost_2784_598_join1_0 cost_2784_598_join1_2 rfl rfl rfl

private theorem cost_2784_598_join2_2 : P1_7_1_3.blockEstimate 2784 598 1622 1024 = 894079859200 :=
  @P1_7_1_3.block_append 2784 598 1622 2134 512 512 1024 446176296192 447903563008 894079859200 cost_2784_598_join1_4 cost_2784_598_join1_6 rfl rfl rfl

private theorem cost_2784_598_join2_4 : P1_7_1_3.blockEstimate 2784 598 2646 1024 = 402010926252 :=
  @P1_7_1_3.block_append 2784 598 2646 3158 512 512 1024 297553531617 104457394635 402010926252 cost_2784_598_join1_8 cost_2784_598_join1_10 rfl rfl rfl

private theorem cost_2784_598_join3_0 : P1_7_1_3.blockEstimate 2784 598 598 2048 = 1231993594425 :=
  @P1_7_1_3.block_append 2784 598 598 1622 1024 1024 2048 337913735225 894079859200 1231993594425 cost_2784_598_join2_0 cost_2784_598_join2_2 rfl rfl rfl

private theorem cost_2784_598_join3_2 : P1_7_1_3.blockEstimate 2784 598 2646 1334 = 408658807219 :=
  @P1_7_1_3.block_append 2784 598 2646 3670 1024 310 1334 402010926252 6647880967 408658807219 cost_2784_598_join2_4 cost_2784_598_join1_12 rfl rfl rfl

private theorem cost_2784_598_join4_0 : P1_7_1_3.blockEstimate 2784 598 598 3382 = 1640652401644 :=
  @P1_7_1_3.block_append 2784 598 598 2646 2048 1334 3382 1231993594425 408658807219 1640652401644 cost_2784_598_join3_0 cost_2784_598_join3_2 rfl rfl rfl

private theorem cost_2784_598_total : P1_7_1_3.momentEstimate 2784 598 = 1640652401644 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2784 + 598 = 3382 by decide]
  exact cost_2784_598_join4_0

theorem moment2784_598 : P1_7_1.groupedPoleMoment 2784 598 ≤ 1640652401644 :=
  (P1_7_1_3.grouped_bound 2784 598).trans_eq cost_2784_598_total
private theorem cost_2786_606_block0 : P1_7_1_3.blockEstimate 2786 606 606 128 = 962642720 := by decide +kernel

private theorem cost_2786_606_block1 : P1_7_1_3.blockEstimate 2786 606 734 128 = 6378050336 := by decide +kernel

private theorem cost_2786_606_block2 : P1_7_1_3.blockEstimate 2786 606 862 128 = 16425018144 := by decide +kernel

private theorem cost_2786_606_block3 : P1_7_1_3.blockEstimate 2786 606 990 128 = 30298239776 := by decide +kernel

private theorem cost_2786_606_block4 : P1_7_1_3.blockEstimate 2786 606 1118 128 = 47178304389 := by decide +kernel

private theorem cost_2786_606_block5 : P1_7_1_3.blockEstimate 2786 606 1246 128 = 64857396416 := by decide +kernel

private theorem cost_2786_606_block6 : P1_7_1_3.blockEstimate 2786 606 1374 128 = 80302118080 := by decide +kernel

private theorem cost_2786_606_block7 : P1_7_1_3.blockEstimate 2786 606 1502 128 = 93200897216 := by decide +kernel

private theorem cost_2786_606_block8 : P1_7_1_3.blockEstimate 2786 606 1630 128 = 103553733824 := by decide +kernel

private theorem cost_2786_606_block9 : P1_7_1_3.blockEstimate 2786 606 1758 128 = 111360627904 := by decide +kernel

private theorem cost_2786_606_block10 : P1_7_1_3.blockEstimate 2786 606 1886 128 = 116621579456 := by decide +kernel

private theorem cost_2786_606_block11 : P1_7_1_3.blockEstimate 2786 606 2014 128 = 119336588480 := by decide +kernel

private theorem cost_2786_606_block12 : P1_7_1_3.blockEstimate 2786 606 2142 128 = 119505654976 := by decide +kernel

private theorem cost_2786_606_block13 : P1_7_1_3.blockEstimate 2786 606 2270 128 = 117128778944 := by decide +kernel

private theorem cost_2786_606_block14 : P1_7_1_3.blockEstimate 2786 606 2398 128 = 112205960384 := by decide +kernel

private theorem cost_2786_606_block15 : P1_7_1_3.blockEstimate 2786 606 2526 128 = 104737199296 := by decide +kernel

private theorem cost_2786_606_block16 : P1_7_1_3.blockEstimate 2786 606 2654 128 = 94722495680 := by decide +kernel

private theorem cost_2786_606_block17 : P1_7_1_3.blockEstimate 2786 606 2782 128 = 82437071904 := by decide +kernel

private theorem cost_2786_606_block18 : P1_7_1_3.blockEstimate 2786 606 2910 128 = 69261381970 := by decide +kernel

private theorem cost_2786_606_block19 : P1_7_1_3.blockEstimate 2786 606 3038 128 = 56027792188 := by decide +kernel

private theorem cost_2786_606_block20 : P1_7_1_3.blockEstimate 2786 606 3166 128 = 43256538599 := by decide +kernel

private theorem cost_2786_606_block21 : P1_7_1_3.blockEstimate 2786 606 3294 128 = 31420529629 := by decide +kernel

private theorem cost_2786_606_block22 : P1_7_1_3.blockEstimate 2786 606 3422 128 = 20891051136 := by decide +kernel

private theorem cost_2786_606_block23 : P1_7_1_3.blockEstimate 2786 606 3550 128 = 12199806080 := by decide +kernel

private theorem cost_2786_606_block24 : P1_7_1_3.blockEstimate 2786 606 3678 128 = 5673411712 := by decide +kernel

private theorem cost_2786_606_block25 : P1_7_1_3.blockEstimate 2786 606 3806 128 = 1563526272 := by decide +kernel

private theorem cost_2786_606_block26 : P1_7_1_3.blockEstimate 2786 606 3934 64 = 64527936 := by decide +kernel

private theorem cost_2786_606_join0_0 : P1_7_1_3.blockEstimate 2786 606 606 256 = 7340693056 :=
  @P1_7_1_3.block_append 2786 606 606 734 128 128 256 962642720 6378050336 7340693056 cost_2786_606_block0 cost_2786_606_block1 rfl rfl rfl

private theorem cost_2786_606_join0_2 : P1_7_1_3.blockEstimate 2786 606 862 256 = 46723257920 :=
  @P1_7_1_3.block_append 2786 606 862 990 128 128 256 16425018144 30298239776 46723257920 cost_2786_606_block2 cost_2786_606_block3 rfl rfl rfl

private theorem cost_2786_606_join0_4 : P1_7_1_3.blockEstimate 2786 606 1118 256 = 112035700805 :=
  @P1_7_1_3.block_append 2786 606 1118 1246 128 128 256 47178304389 64857396416 112035700805 cost_2786_606_block4 cost_2786_606_block5 rfl rfl rfl

private theorem cost_2786_606_join0_6 : P1_7_1_3.blockEstimate 2786 606 1374 256 = 173503015296 :=
  @P1_7_1_3.block_append 2786 606 1374 1502 128 128 256 80302118080 93200897216 173503015296 cost_2786_606_block6 cost_2786_606_block7 rfl rfl rfl

private theorem cost_2786_606_join0_8 : P1_7_1_3.blockEstimate 2786 606 1630 256 = 214914361728 :=
  @P1_7_1_3.block_append 2786 606 1630 1758 128 128 256 103553733824 111360627904 214914361728 cost_2786_606_block8 cost_2786_606_block9 rfl rfl rfl

private theorem cost_2786_606_join0_10 : P1_7_1_3.blockEstimate 2786 606 1886 256 = 235958167936 :=
  @P1_7_1_3.block_append 2786 606 1886 2014 128 128 256 116621579456 119336588480 235958167936 cost_2786_606_block10 cost_2786_606_block11 rfl rfl rfl

private theorem cost_2786_606_join0_12 : P1_7_1_3.blockEstimate 2786 606 2142 256 = 236634433920 :=
  @P1_7_1_3.block_append 2786 606 2142 2270 128 128 256 119505654976 117128778944 236634433920 cost_2786_606_block12 cost_2786_606_block13 rfl rfl rfl

private theorem cost_2786_606_join0_14 : P1_7_1_3.blockEstimate 2786 606 2398 256 = 216943159680 :=
  @P1_7_1_3.block_append 2786 606 2398 2526 128 128 256 112205960384 104737199296 216943159680 cost_2786_606_block14 cost_2786_606_block15 rfl rfl rfl

private theorem cost_2786_606_join0_16 : P1_7_1_3.blockEstimate 2786 606 2654 256 = 177159567584 :=
  @P1_7_1_3.block_append 2786 606 2654 2782 128 128 256 94722495680 82437071904 177159567584 cost_2786_606_block16 cost_2786_606_block17 rfl rfl rfl

private theorem cost_2786_606_join0_18 : P1_7_1_3.blockEstimate 2786 606 2910 256 = 125289174158 :=
  @P1_7_1_3.block_append 2786 606 2910 3038 128 128 256 69261381970 56027792188 125289174158 cost_2786_606_block18 cost_2786_606_block19 rfl rfl rfl

private theorem cost_2786_606_join0_20 : P1_7_1_3.blockEstimate 2786 606 3166 256 = 74677068228 :=
  @P1_7_1_3.block_append 2786 606 3166 3294 128 128 256 43256538599 31420529629 74677068228 cost_2786_606_block20 cost_2786_606_block21 rfl rfl rfl

private theorem cost_2786_606_join0_22 : P1_7_1_3.blockEstimate 2786 606 3422 256 = 33090857216 :=
  @P1_7_1_3.block_append 2786 606 3422 3550 128 128 256 20891051136 12199806080 33090857216 cost_2786_606_block22 cost_2786_606_block23 rfl rfl rfl

private theorem cost_2786_606_join0_24 : P1_7_1_3.blockEstimate 2786 606 3678 256 = 7236937984 :=
  @P1_7_1_3.block_append 2786 606 3678 3806 128 128 256 5673411712 1563526272 7236937984 cost_2786_606_block24 cost_2786_606_block25 rfl rfl rfl

private theorem cost_2786_606_join1_0 : P1_7_1_3.blockEstimate 2786 606 606 512 = 54063950976 :=
  @P1_7_1_3.block_append 2786 606 606 862 256 256 512 7340693056 46723257920 54063950976 cost_2786_606_join0_0 cost_2786_606_join0_2 rfl rfl rfl

private theorem cost_2786_606_join1_2 : P1_7_1_3.blockEstimate 2786 606 1118 512 = 285538716101 :=
  @P1_7_1_3.block_append 2786 606 1118 1374 256 256 512 112035700805 173503015296 285538716101 cost_2786_606_join0_4 cost_2786_606_join0_6 rfl rfl rfl

private theorem cost_2786_606_join1_4 : P1_7_1_3.blockEstimate 2786 606 1630 512 = 450872529664 :=
  @P1_7_1_3.block_append 2786 606 1630 1886 256 256 512 214914361728 235958167936 450872529664 cost_2786_606_join0_8 cost_2786_606_join0_10 rfl rfl rfl

private theorem cost_2786_606_join1_6 : P1_7_1_3.blockEstimate 2786 606 2142 512 = 453577593600 :=
  @P1_7_1_3.block_append 2786 606 2142 2398 256 256 512 236634433920 216943159680 453577593600 cost_2786_606_join0_12 cost_2786_606_join0_14 rfl rfl rfl

private theorem cost_2786_606_join1_8 : P1_7_1_3.blockEstimate 2786 606 2654 512 = 302448741742 :=
  @P1_7_1_3.block_append 2786 606 2654 2910 256 256 512 177159567584 125289174158 302448741742 cost_2786_606_join0_16 cost_2786_606_join0_18 rfl rfl rfl

private theorem cost_2786_606_join1_10 : P1_7_1_3.blockEstimate 2786 606 3166 512 = 107767925444 :=
  @P1_7_1_3.block_append 2786 606 3166 3422 256 256 512 74677068228 33090857216 107767925444 cost_2786_606_join0_20 cost_2786_606_join0_22 rfl rfl rfl

private theorem cost_2786_606_join1_12 : P1_7_1_3.blockEstimate 2786 606 3678 320 = 7301465920 :=
  @P1_7_1_3.block_append 2786 606 3678 3934 256 64 320 7236937984 64527936 7301465920 cost_2786_606_join0_24 cost_2786_606_block26 rfl rfl rfl

private theorem cost_2786_606_join2_0 : P1_7_1_3.blockEstimate 2786 606 606 1024 = 339602667077 :=
  @P1_7_1_3.block_append 2786 606 606 1118 512 512 1024 54063950976 285538716101 339602667077 cost_2786_606_join1_0 cost_2786_606_join1_2 rfl rfl rfl

private theorem cost_2786_606_join2_2 : P1_7_1_3.blockEstimate 2786 606 1630 1024 = 904450123264 :=
  @P1_7_1_3.block_append 2786 606 1630 2142 512 512 1024 450872529664 453577593600 904450123264 cost_2786_606_join1_4 cost_2786_606_join1_6 rfl rfl rfl

private theorem cost_2786_606_join2_4 : P1_7_1_3.blockEstimate 2786 606 2654 1024 = 410216667186 :=
  @P1_7_1_3.block_append 2786 606 2654 3166 512 512 1024 302448741742 107767925444 410216667186 cost_2786_606_join1_8 cost_2786_606_join1_10 rfl rfl rfl

private theorem cost_2786_606_join3_0 : P1_7_1_3.blockEstimate 2786 606 606 2048 = 1244052790341 :=
  @P1_7_1_3.block_append 2786 606 606 1630 1024 1024 2048 339602667077 904450123264 1244052790341 cost_2786_606_join2_0 cost_2786_606_join2_2 rfl rfl rfl

private theorem cost_2786_606_join3_2 : P1_7_1_3.blockEstimate 2786 606 2654 1344 = 417518133106 :=
  @P1_7_1_3.block_append 2786 606 2654 3678 1024 320 1344 410216667186 7301465920 417518133106 cost_2786_606_join2_4 cost_2786_606_join1_12 rfl rfl rfl

private theorem cost_2786_606_join4_0 : P1_7_1_3.blockEstimate 2786 606 606 3392 = 1661570923447 :=
  @P1_7_1_3.block_append 2786 606 606 2654 2048 1344 3392 1244052790341 417518133106 1661570923447 cost_2786_606_join3_0 cost_2786_606_join3_2 rfl rfl rfl

private theorem cost_2786_606_total : P1_7_1_3.momentEstimate 2786 606 = 1661570923447 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2786 + 606 = 3392 by decide]
  exact cost_2786_606_join4_0

theorem moment2786_606 : P1_7_1.groupedPoleMoment 2786 606 ≤ 1661570923447 :=
  (P1_7_1_3.grouped_bound 2786 606).trans_eq cost_2786_606_total
private theorem cost_2786_620_block0 : P1_7_1_3.blockEstimate 2786 620 620 128 = 962642720 := by decide +kernel

private theorem cost_2786_620_block1 : P1_7_1_3.blockEstimate 2786 620 748 128 = 6378050336 := by decide +kernel

private theorem cost_2786_620_block2 : P1_7_1_3.blockEstimate 2786 620 876 128 = 16425018144 := by decide +kernel

private theorem cost_2786_620_block3 : P1_7_1_3.blockEstimate 2786 620 1004 128 = 30298239776 := by decide +kernel

private theorem cost_2786_620_block4 : P1_7_1_3.blockEstimate 2786 620 1132 128 = 47189547369 := by decide +kernel

private theorem cost_2786_620_block5 : P1_7_1_3.blockEstimate 2786 620 1260 128 = 65194547328 := by decide +kernel

private theorem cost_2786_620_block6 : P1_7_1_3.blockEstimate 2786 620 1388 128 = 81066711168 := by decide +kernel

private theorem cost_2786_620_block7 : P1_7_1_3.blockEstimate 2786 620 1516 128 = 94334212224 := by decide +kernel

private theorem cost_2786_620_block8 : P1_7_1_3.blockEstimate 2786 620 1644 128 = 104997050496 := by decide +kernel

private theorem cost_2786_620_block9 : P1_7_1_3.blockEstimate 2786 620 1772 128 = 113055225984 := by decide +kernel

private theorem cost_2786_620_block10 : P1_7_1_3.blockEstimate 2786 620 1900 128 = 118508738688 := by decide +kernel

private theorem cost_2786_620_block11 : P1_7_1_3.blockEstimate 2786 620 2028 128 = 121357588608 := by decide +kernel

private theorem cost_2786_620_block12 : P1_7_1_3.blockEstimate 2786 620 2156 128 = 121601775744 := by decide +kernel

private theorem cost_2786_620_block13 : P1_7_1_3.blockEstimate 2786 620 2284 128 = 119241300096 := by decide +kernel

private theorem cost_2786_620_block14 : P1_7_1_3.blockEstimate 2786 620 2412 128 = 114276161664 := by decide +kernel

private theorem cost_2786_620_block15 : P1_7_1_3.blockEstimate 2786 620 2540 128 = 106706360448 := by decide +kernel

private theorem cost_2786_620_block16 : P1_7_1_3.blockEstimate 2786 620 2668 128 = 96532044348 := by decide +kernel

private theorem cost_2786_620_block17 : P1_7_1_3.blockEstimate 2786 620 2796 128 = 84128730749 := by decide +kernel

private theorem cost_2786_620_block18 : P1_7_1_3.blockEstimate 2786 620 2924 128 = 70889844313 := by decide +kernel

private theorem cost_2786_620_block19 : P1_7_1_3.blockEstimate 2786 620 3052 128 = 57565267125 := by decide +kernel

private theorem cost_2786_620_block20 : P1_7_1_3.blockEstimate 2786 620 3180 128 = 44672580452 := by decide +kernel

private theorem cost_2786_620_block21 : P1_7_1_3.blockEstimate 2786 620 3308 128 = 32682760873 := by decide +kernel

private theorem cost_2786_620_block22 : P1_7_1_3.blockEstimate 2786 620 3436 128 = 21962260080 := by decide +kernel

private theorem cost_2786_620_block23 : P1_7_1_3.blockEstimate 2786 620 3564 128 = 13049502320 := by decide +kernel

private theorem cost_2786_620_block24 : P1_7_1_3.blockEstimate 2786 620 3692 128 = 6274070128 := by decide +kernel

private theorem cost_2786_620_block25 : P1_7_1_3.blockEstimate 2786 620 3820 128 = 1887621744 := by decide +kernel

private theorem cost_2786_620_block26 : P1_7_1_3.blockEstimate 2786 620 3948 78 = 115119230 := by decide +kernel

private theorem cost_2786_620_join0_0 : P1_7_1_3.blockEstimate 2786 620 620 256 = 7340693056 :=
  @P1_7_1_3.block_append 2786 620 620 748 128 128 256 962642720 6378050336 7340693056 cost_2786_620_block0 cost_2786_620_block1 rfl rfl rfl

private theorem cost_2786_620_join0_2 : P1_7_1_3.blockEstimate 2786 620 876 256 = 46723257920 :=
  @P1_7_1_3.block_append 2786 620 876 1004 128 128 256 16425018144 30298239776 46723257920 cost_2786_620_block2 cost_2786_620_block3 rfl rfl rfl

private theorem cost_2786_620_join0_4 : P1_7_1_3.blockEstimate 2786 620 1132 256 = 112384094697 :=
  @P1_7_1_3.block_append 2786 620 1132 1260 128 128 256 47189547369 65194547328 112384094697 cost_2786_620_block4 cost_2786_620_block5 rfl rfl rfl

private theorem cost_2786_620_join0_6 : P1_7_1_3.blockEstimate 2786 620 1388 256 = 175400923392 :=
  @P1_7_1_3.block_append 2786 620 1388 1516 128 128 256 81066711168 94334212224 175400923392 cost_2786_620_block6 cost_2786_620_block7 rfl rfl rfl

private theorem cost_2786_620_join0_8 : P1_7_1_3.blockEstimate 2786 620 1644 256 = 218052276480 :=
  @P1_7_1_3.block_append 2786 620 1644 1772 128 128 256 104997050496 113055225984 218052276480 cost_2786_620_block8 cost_2786_620_block9 rfl rfl rfl

private theorem cost_2786_620_join0_10 : P1_7_1_3.blockEstimate 2786 620 1900 256 = 239866327296 :=
  @P1_7_1_3.block_append 2786 620 1900 2028 128 128 256 118508738688 121357588608 239866327296 cost_2786_620_block10 cost_2786_620_block11 rfl rfl rfl

private theorem cost_2786_620_join0_12 : P1_7_1_3.blockEstimate 2786 620 2156 256 = 240843075840 :=
  @P1_7_1_3.block_append 2786 620 2156 2284 128 128 256 121601775744 119241300096 240843075840 cost_2786_620_block12 cost_2786_620_block13 rfl rfl rfl

private theorem cost_2786_620_join0_14 : P1_7_1_3.blockEstimate 2786 620 2412 256 = 220982522112 :=
  @P1_7_1_3.block_append 2786 620 2412 2540 128 128 256 114276161664 106706360448 220982522112 cost_2786_620_block14 cost_2786_620_block15 rfl rfl rfl

private theorem cost_2786_620_join0_16 : P1_7_1_3.blockEstimate 2786 620 2668 256 = 180660775097 :=
  @P1_7_1_3.block_append 2786 620 2668 2796 128 128 256 96532044348 84128730749 180660775097 cost_2786_620_block16 cost_2786_620_block17 rfl rfl rfl

private theorem cost_2786_620_join0_18 : P1_7_1_3.blockEstimate 2786 620 2924 256 = 128455111438 :=
  @P1_7_1_3.block_append 2786 620 2924 3052 128 128 256 70889844313 57565267125 128455111438 cost_2786_620_block18 cost_2786_620_block19 rfl rfl rfl

private theorem cost_2786_620_join0_20 : P1_7_1_3.blockEstimate 2786 620 3180 256 = 77355341325 :=
  @P1_7_1_3.block_append 2786 620 3180 3308 128 128 256 44672580452 32682760873 77355341325 cost_2786_620_block20 cost_2786_620_block21 rfl rfl rfl

private theorem cost_2786_620_join0_22 : P1_7_1_3.blockEstimate 2786 620 3436 256 = 35011762400 :=
  @P1_7_1_3.block_append 2786 620 3436 3564 128 128 256 21962260080 13049502320 35011762400 cost_2786_620_block22 cost_2786_620_block23 rfl rfl rfl

private theorem cost_2786_620_join0_24 : P1_7_1_3.blockEstimate 2786 620 3692 256 = 8161691872 :=
  @P1_7_1_3.block_append 2786 620 3692 3820 128 128 256 6274070128 1887621744 8161691872 cost_2786_620_block24 cost_2786_620_block25 rfl rfl rfl

private theorem cost_2786_620_join1_0 : P1_7_1_3.blockEstimate 2786 620 620 512 = 54063950976 :=
  @P1_7_1_3.block_append 2786 620 620 876 256 256 512 7340693056 46723257920 54063950976 cost_2786_620_join0_0 cost_2786_620_join0_2 rfl rfl rfl

private theorem cost_2786_620_join1_2 : P1_7_1_3.blockEstimate 2786 620 1132 512 = 287785018089 :=
  @P1_7_1_3.block_append 2786 620 1132 1388 256 256 512 112384094697 175400923392 287785018089 cost_2786_620_join0_4 cost_2786_620_join0_6 rfl rfl rfl

private theorem cost_2786_620_join1_4 : P1_7_1_3.blockEstimate 2786 620 1644 512 = 457918603776 :=
  @P1_7_1_3.block_append 2786 620 1644 1900 256 256 512 218052276480 239866327296 457918603776 cost_2786_620_join0_8 cost_2786_620_join0_10 rfl rfl rfl

private theorem cost_2786_620_join1_6 : P1_7_1_3.blockEstimate 2786 620 2156 512 = 461825597952 :=
  @P1_7_1_3.block_append 2786 620 2156 2412 256 256 512 240843075840 220982522112 461825597952 cost_2786_620_join0_12 cost_2786_620_join0_14 rfl rfl rfl

private theorem cost_2786_620_join1_8 : P1_7_1_3.blockEstimate 2786 620 2668 512 = 309115886535 :=
  @P1_7_1_3.block_append 2786 620 2668 2924 256 256 512 180660775097 128455111438 309115886535 cost_2786_620_join0_16 cost_2786_620_join0_18 rfl rfl rfl

private theorem cost_2786_620_join1_10 : P1_7_1_3.blockEstimate 2786 620 3180 512 = 112367103725 :=
  @P1_7_1_3.block_append 2786 620 3180 3436 256 256 512 77355341325 35011762400 112367103725 cost_2786_620_join0_20 cost_2786_620_join0_22 rfl rfl rfl

private theorem cost_2786_620_join1_12 : P1_7_1_3.blockEstimate 2786 620 3692 334 = 8276811102 :=
  @P1_7_1_3.block_append 2786 620 3692 3948 256 78 334 8161691872 115119230 8276811102 cost_2786_620_join0_24 cost_2786_620_block26 rfl rfl rfl

private theorem cost_2786_620_join2_0 : P1_7_1_3.blockEstimate 2786 620 620 1024 = 341848969065 :=
  @P1_7_1_3.block_append 2786 620 620 1132 512 512 1024 54063950976 287785018089 341848969065 cost_2786_620_join1_0 cost_2786_620_join1_2 rfl rfl rfl

private theorem cost_2786_620_join2_2 : P1_7_1_3.blockEstimate 2786 620 1644 1024 = 919744201728 :=
  @P1_7_1_3.block_append 2786 620 1644 2156 512 512 1024 457918603776 461825597952 919744201728 cost_2786_620_join1_4 cost_2786_620_join1_6 rfl rfl rfl

private theorem cost_2786_620_join2_4 : P1_7_1_3.blockEstimate 2786 620 2668 1024 = 421482990260 :=
  @P1_7_1_3.block_append 2786 620 2668 3180 512 512 1024 309115886535 112367103725 421482990260 cost_2786_620_join1_8 cost_2786_620_join1_10 rfl rfl rfl

private theorem cost_2786_620_join3_0 : P1_7_1_3.blockEstimate 2786 620 620 2048 = 1261593170793 :=
  @P1_7_1_3.block_append 2786 620 620 1644 1024 1024 2048 341848969065 919744201728 1261593170793 cost_2786_620_join2_0 cost_2786_620_join2_2 rfl rfl rfl

private theorem cost_2786_620_join3_2 : P1_7_1_3.blockEstimate 2786 620 2668 1358 = 429759801362 :=
  @P1_7_1_3.block_append 2786 620 2668 3692 1024 334 1358 421482990260 8276811102 429759801362 cost_2786_620_join2_4 cost_2786_620_join1_12 rfl rfl rfl

private theorem cost_2786_620_join4_0 : P1_7_1_3.blockEstimate 2786 620 620 3406 = 1691352972155 :=
  @P1_7_1_3.block_append 2786 620 620 2668 2048 1358 3406 1261593170793 429759801362 1691352972155 cost_2786_620_join3_0 cost_2786_620_join3_2 rfl rfl rfl

private theorem cost_2786_620_total : P1_7_1_3.momentEstimate 2786 620 = 1691352972155 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2786 + 620 = 3406 by decide]
  exact cost_2786_620_join4_0

theorem moment2786_620 : P1_7_1.groupedPoleMoment 2786 620 ≤ 1691352972155 :=
  (P1_7_1_3.grouped_bound 2786 620).trans_eq cost_2786_620_total
private theorem cost_2786_622_block0 : P1_7_1_3.blockEstimate 2786 622 622 128 = 962642720 := by decide +kernel

private theorem cost_2786_622_block1 : P1_7_1_3.blockEstimate 2786 622 750 128 = 6378050336 := by decide +kernel

private theorem cost_2786_622_block2 : P1_7_1_3.blockEstimate 2786 622 878 128 = 16425018144 := by decide +kernel

private theorem cost_2786_622_block3 : P1_7_1_3.blockEstimate 2786 622 1006 128 = 30298239776 := by decide +kernel

private theorem cost_2786_622_block4 : P1_7_1_3.blockEstimate 2786 622 1134 128 = 47190324545 := by decide +kernel

private theorem cost_2786_622_block5 : P1_7_1_3.blockEstimate 2786 622 1262 128 = 65238446784 := by decide +kernel

private theorem cost_2786_622_block6 : P1_7_1_3.blockEstimate 2786 622 1390 128 = 81171935936 := by decide +kernel

private theorem cost_2786_622_block7 : P1_7_1_3.blockEstimate 2786 622 1518 128 = 94492373696 := by decide +kernel

private theorem cost_2786_622_block8 : P1_7_1_3.blockEstimate 2786 622 1646 128 = 105199760064 := by decide +kernel

private theorem cost_2786_622_block9 : P1_7_1_3.blockEstimate 2786 622 1774 128 = 113294095040 := by decide +kernel

private theorem cost_2786_622_block10 : P1_7_1_3.blockEstimate 2786 622 1902 128 = 118775378624 := by decide +kernel

private theorem cost_2786_622_block11 : P1_7_1_3.blockEstimate 2786 622 2030 128 = 121643610816 := by decide +kernel

private theorem cost_2786_622_block12 : P1_7_1_3.blockEstimate 2786 622 2158 128 = 121898791616 := by decide +kernel

private theorem cost_2786_622_block13 : P1_7_1_3.blockEstimate 2786 622 2286 128 = 119540921024 := by decide +kernel

private theorem cost_2786_622_block14 : P1_7_1_3.blockEstimate 2786 622 2414 128 = 114569999040 := by decide +kernel

private theorem cost_2786_622_block15 : P1_7_1_3.blockEstimate 2786 622 2542 128 = 106986025664 := by decide +kernel

private theorem cost_2786_622_block16 : P1_7_1_3.blockEstimate 2786 622 2670 128 = 96789251265 := by decide +kernel

private theorem cost_2786_622_block17 : P1_7_1_3.blockEstimate 2786 622 2798 128 = 84370896244 := by decide +kernel

private theorem cost_2786_622_block18 : P1_7_1_3.blockEstimate 2786 622 2926 128 = 71123276913 := by decide +kernel

private theorem cost_2786_622_block19 : P1_7_1_3.blockEstimate 2786 622 3054 128 = 57785976936 := by decide +kernel

private theorem cost_2786_622_block20 : P1_7_1_3.blockEstimate 2786 622 3182 128 = 44876208453 := by decide +kernel

private theorem cost_2786_622_block21 : P1_7_1_3.blockEstimate 2786 622 3310 128 = 32864678333 := by decide +kernel

private theorem cost_2786_622_block22 : P1_7_1_3.blockEstimate 2786 622 3438 128 = 22117139072 := by decide +kernel

private theorem cost_2786_622_block23 : P1_7_1_3.blockEstimate 2786 622 3566 128 = 13172982400 := by decide +kernel

private theorem cost_2786_622_block24 : P1_7_1_3.blockEstimate 2786 622 3694 128 = 6362219136 := by decide +kernel

private theorem cost_2786_622_block25 : P1_7_1_3.blockEstimate 2786 622 3822 128 = 1936507520 := by decide +kernel

private theorem cost_2786_622_block26 : P1_7_1_3.blockEstimate 2786 622 3950 80 = 123987280 := by decide +kernel

private theorem cost_2786_622_join0_0 : P1_7_1_3.blockEstimate 2786 622 622 256 = 7340693056 :=
  @P1_7_1_3.block_append 2786 622 622 750 128 128 256 962642720 6378050336 7340693056 cost_2786_622_block0 cost_2786_622_block1 rfl rfl rfl

private theorem cost_2786_622_join0_2 : P1_7_1_3.blockEstimate 2786 622 878 256 = 46723257920 :=
  @P1_7_1_3.block_append 2786 622 878 1006 128 128 256 16425018144 30298239776 46723257920 cost_2786_622_block2 cost_2786_622_block3 rfl rfl rfl

private theorem cost_2786_622_join0_4 : P1_7_1_3.blockEstimate 2786 622 1134 256 = 112428771329 :=
  @P1_7_1_3.block_append 2786 622 1134 1262 128 128 256 47190324545 65238446784 112428771329 cost_2786_622_block4 cost_2786_622_block5 rfl rfl rfl

private theorem cost_2786_622_join0_6 : P1_7_1_3.blockEstimate 2786 622 1390 256 = 175664309632 :=
  @P1_7_1_3.block_append 2786 622 1390 1518 128 128 256 81171935936 94492373696 175664309632 cost_2786_622_block6 cost_2786_622_block7 rfl rfl rfl

private theorem cost_2786_622_join0_8 : P1_7_1_3.blockEstimate 2786 622 1646 256 = 218493855104 :=
  @P1_7_1_3.block_append 2786 622 1646 1774 128 128 256 105199760064 113294095040 218493855104 cost_2786_622_block8 cost_2786_622_block9 rfl rfl rfl

private theorem cost_2786_622_join0_10 : P1_7_1_3.blockEstimate 2786 622 1902 256 = 240418989440 :=
  @P1_7_1_3.block_append 2786 622 1902 2030 128 128 256 118775378624 121643610816 240418989440 cost_2786_622_block10 cost_2786_622_block11 rfl rfl rfl

private theorem cost_2786_622_join0_12 : P1_7_1_3.blockEstimate 2786 622 2158 256 = 241439712640 :=
  @P1_7_1_3.block_append 2786 622 2158 2286 128 128 256 121898791616 119540921024 241439712640 cost_2786_622_block12 cost_2786_622_block13 rfl rfl rfl

private theorem cost_2786_622_join0_14 : P1_7_1_3.blockEstimate 2786 622 2414 256 = 221556024704 :=
  @P1_7_1_3.block_append 2786 622 2414 2542 128 128 256 114569999040 106986025664 221556024704 cost_2786_622_block14 cost_2786_622_block15 rfl rfl rfl

private theorem cost_2786_622_join0_16 : P1_7_1_3.blockEstimate 2786 622 2670 256 = 181160147509 :=
  @P1_7_1_3.block_append 2786 622 2670 2798 128 128 256 96789251265 84370896244 181160147509 cost_2786_622_block16 cost_2786_622_block17 rfl rfl rfl

private theorem cost_2786_622_join0_18 : P1_7_1_3.blockEstimate 2786 622 2926 256 = 128909253849 :=
  @P1_7_1_3.block_append 2786 622 2926 3054 128 128 256 71123276913 57785976936 128909253849 cost_2786_622_block18 cost_2786_622_block19 rfl rfl rfl

private theorem cost_2786_622_join0_20 : P1_7_1_3.blockEstimate 2786 622 3182 256 = 77740886786 :=
  @P1_7_1_3.block_append 2786 622 3182 3310 128 128 256 44876208453 32864678333 77740886786 cost_2786_622_block20 cost_2786_622_block21 rfl rfl rfl

private theorem cost_2786_622_join0_22 : P1_7_1_3.blockEstimate 2786 622 3438 256 = 35290121472 :=
  @P1_7_1_3.block_append 2786 622 3438 3566 128 128 256 22117139072 13172982400 35290121472 cost_2786_622_block22 cost_2786_622_block23 rfl rfl rfl

private theorem cost_2786_622_join0_24 : P1_7_1_3.blockEstimate 2786 622 3694 256 = 8298726656 :=
  @P1_7_1_3.block_append 2786 622 3694 3822 128 128 256 6362219136 1936507520 8298726656 cost_2786_622_block24 cost_2786_622_block25 rfl rfl rfl

private theorem cost_2786_622_join1_0 : P1_7_1_3.blockEstimate 2786 622 622 512 = 54063950976 :=
  @P1_7_1_3.block_append 2786 622 622 878 256 256 512 7340693056 46723257920 54063950976 cost_2786_622_join0_0 cost_2786_622_join0_2 rfl rfl rfl

private theorem cost_2786_622_join1_2 : P1_7_1_3.blockEstimate 2786 622 1134 512 = 288093080961 :=
  @P1_7_1_3.block_append 2786 622 1134 1390 256 256 512 112428771329 175664309632 288093080961 cost_2786_622_join0_4 cost_2786_622_join0_6 rfl rfl rfl

private theorem cost_2786_622_join1_4 : P1_7_1_3.blockEstimate 2786 622 1646 512 = 458912844544 :=
  @P1_7_1_3.block_append 2786 622 1646 1902 256 256 512 218493855104 240418989440 458912844544 cost_2786_622_join0_8 cost_2786_622_join0_10 rfl rfl rfl

private theorem cost_2786_622_join1_6 : P1_7_1_3.blockEstimate 2786 622 2158 512 = 462995737344 :=
  @P1_7_1_3.block_append 2786 622 2158 2414 256 256 512 241439712640 221556024704 462995737344 cost_2786_622_join0_12 cost_2786_622_join0_14 rfl rfl rfl

private theorem cost_2786_622_join1_8 : P1_7_1_3.blockEstimate 2786 622 2670 512 = 310069401358 :=
  @P1_7_1_3.block_append 2786 622 2670 2926 256 256 512 181160147509 128909253849 310069401358 cost_2786_622_join0_16 cost_2786_622_join0_18 rfl rfl rfl

private theorem cost_2786_622_join1_10 : P1_7_1_3.blockEstimate 2786 622 3182 512 = 113031008258 :=
  @P1_7_1_3.block_append 2786 622 3182 3438 256 256 512 77740886786 35290121472 113031008258 cost_2786_622_join0_20 cost_2786_622_join0_22 rfl rfl rfl

private theorem cost_2786_622_join1_12 : P1_7_1_3.blockEstimate 2786 622 3694 336 = 8422713936 :=
  @P1_7_1_3.block_append 2786 622 3694 3950 256 80 336 8298726656 123987280 8422713936 cost_2786_622_join0_24 cost_2786_622_block26 rfl rfl rfl

private theorem cost_2786_622_join2_0 : P1_7_1_3.blockEstimate 2786 622 622 1024 = 342157031937 :=
  @P1_7_1_3.block_append 2786 622 622 1134 512 512 1024 54063950976 288093080961 342157031937 cost_2786_622_join1_0 cost_2786_622_join1_2 rfl rfl rfl

private theorem cost_2786_622_join2_2 : P1_7_1_3.blockEstimate 2786 622 1646 1024 = 921908581888 :=
  @P1_7_1_3.block_append 2786 622 1646 2158 512 512 1024 458912844544 462995737344 921908581888 cost_2786_622_join1_4 cost_2786_622_join1_6 rfl rfl rfl

private theorem cost_2786_622_join2_4 : P1_7_1_3.blockEstimate 2786 622 2670 1024 = 423100409616 :=
  @P1_7_1_3.block_append 2786 622 2670 3182 512 512 1024 310069401358 113031008258 423100409616 cost_2786_622_join1_8 cost_2786_622_join1_10 rfl rfl rfl

private theorem cost_2786_622_join3_0 : P1_7_1_3.blockEstimate 2786 622 622 2048 = 1264065613825 :=
  @P1_7_1_3.block_append 2786 622 622 1646 1024 1024 2048 342157031937 921908581888 1264065613825 cost_2786_622_join2_0 cost_2786_622_join2_2 rfl rfl rfl

private theorem cost_2786_622_join3_2 : P1_7_1_3.blockEstimate 2786 622 2670 1360 = 431523123552 :=
  @P1_7_1_3.block_append 2786 622 2670 3694 1024 336 1360 423100409616 8422713936 431523123552 cost_2786_622_join2_4 cost_2786_622_join1_12 rfl rfl rfl

private theorem cost_2786_622_join4_0 : P1_7_1_3.blockEstimate 2786 622 622 3408 = 1695588737377 :=
  @P1_7_1_3.block_append 2786 622 622 2670 2048 1360 3408 1264065613825 431523123552 1695588737377 cost_2786_622_join3_0 cost_2786_622_join3_2 rfl rfl rfl

private theorem cost_2786_622_total : P1_7_1_3.momentEstimate 2786 622 = 1695588737377 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2786 + 622 = 3408 by decide]
  exact cost_2786_622_join4_0

theorem moment2786_622 : P1_7_1.groupedPoleMoment 2786 622 ≤ 1695588737377 :=
  (P1_7_1_3.grouped_bound 2786 622).trans_eq cost_2786_622_total
private theorem cost_2787_606_block0 : P1_7_1_3.blockEstimate 2787 606 606 128 = 963000480 := by decide +kernel

private theorem cost_2787_606_block1 : P1_7_1_3.blockEstimate 2787 606 734 128 = 6380521632 := by decide +kernel

private theorem cost_2787_606_block2 : P1_7_1_3.blockEstimate 2787 606 862 128 = 16431700128 := by decide +kernel

private theorem cost_2787_606_block3 : P1_7_1_3.blockEstimate 2787 606 990 128 = 30311229600 := by decide +kernel

private theorem cost_2787_606_block4 : P1_7_1_3.blockEstimate 2787 606 1118 128 = 47199692660 := by decide +kernel

private theorem cost_2787_606_block5 : P1_7_1_3.blockEstimate 2787 606 1246 128 = 64888591360 := by decide +kernel

private theorem cost_2787_606_block6 : P1_7_1_3.blockEstimate 2787 606 1374 128 = 80343258112 := by decide +kernel

private theorem cost_2787_606_block7 : P1_7_1_3.blockEstimate 2787 606 1502 128 = 93251982336 := by decide +kernel

private theorem cost_2787_606_block8 : P1_7_1_3.blockEstimate 2787 606 1630 128 = 103614764032 := by decide +kernel

private theorem cost_2787_606_block9 : P1_7_1_3.blockEstimate 2787 606 1758 128 = 111431603200 := by decide +kernel

private theorem cost_2787_606_block10 : P1_7_1_3.blockEstimate 2787 606 1886 128 = 116702499840 := by decide +kernel

private theorem cost_2787_606_block11 : P1_7_1_3.blockEstimate 2787 606 2014 128 = 119427453952 := by decide +kernel

private theorem cost_2787_606_block12 : P1_7_1_3.blockEstimate 2787 606 2142 128 = 119606465536 := by decide +kernel

private theorem cost_2787_606_block13 : P1_7_1_3.blockEstimate 2787 606 2270 128 = 117239534592 := by decide +kernel

private theorem cost_2787_606_block14 : P1_7_1_3.blockEstimate 2787 606 2398 128 = 112326661120 := by decide +kernel

private theorem cost_2787_606_block15 : P1_7_1_3.blockEstimate 2787 606 2526 128 = 104867845120 := by decide +kernel

private theorem cost_2787_606_block16 : P1_7_1_3.blockEstimate 2787 606 2654 128 = 94863086592 := by decide +kernel

private theorem cost_2787_606_block17 : P1_7_1_3.blockEstimate 2787 606 2782 128 = 82581013578 := by decide +kernel

private theorem cost_2787_606_block18 : P1_7_1_3.blockEstimate 2787 606 2910 128 = 69399008652 := by decide +kernel

private theorem cost_2787_606_block19 : P1_7_1_3.blockEstimate 2787 606 3038 128 = 56155914891 := by decide +kernel

private theorem cost_2787_606_block20 : P1_7_1_3.blockEstimate 2787 606 3166 128 = 43372306016 := by decide +kernel

private theorem cost_2787_606_block21 : P1_7_1_3.blockEstimate 2787 606 3294 128 = 31521721053 := by decide +kernel

private theorem cost_2787_606_block22 : P1_7_1_3.blockEstimate 2787 606 3422 128 = 20975325328 := by decide +kernel

private theorem cost_2787_606_block23 : P1_7_1_3.blockEstimate 2787 606 3550 128 = 12264467600 := by decide +kernel

private theorem cost_2787_606_block24 : P1_7_1_3.blockEstimate 2787 606 3678 128 = 5717543056 := by decide +kernel

private theorem cost_2787_606_block25 : P1_7_1_3.blockEstimate 2787 606 3806 128 = 1586209936 := by decide +kernel

private theorem cost_2787_606_block26 : P1_7_1_3.blockEstimate 2787 606 3934 65 = 67542955 := by decide +kernel

private theorem cost_2787_606_join0_0 : P1_7_1_3.blockEstimate 2787 606 606 256 = 7343522112 :=
  @P1_7_1_3.block_append 2787 606 606 734 128 128 256 963000480 6380521632 7343522112 cost_2787_606_block0 cost_2787_606_block1 rfl rfl rfl

private theorem cost_2787_606_join0_2 : P1_7_1_3.blockEstimate 2787 606 862 256 = 46742929728 :=
  @P1_7_1_3.block_append 2787 606 862 990 128 128 256 16431700128 30311229600 46742929728 cost_2787_606_block2 cost_2787_606_block3 rfl rfl rfl

private theorem cost_2787_606_join0_4 : P1_7_1_3.blockEstimate 2787 606 1118 256 = 112088284020 :=
  @P1_7_1_3.block_append 2787 606 1118 1246 128 128 256 47199692660 64888591360 112088284020 cost_2787_606_block4 cost_2787_606_block5 rfl rfl rfl

private theorem cost_2787_606_join0_6 : P1_7_1_3.blockEstimate 2787 606 1374 256 = 173595240448 :=
  @P1_7_1_3.block_append 2787 606 1374 1502 128 128 256 80343258112 93251982336 173595240448 cost_2787_606_block6 cost_2787_606_block7 rfl rfl rfl

private theorem cost_2787_606_join0_8 : P1_7_1_3.blockEstimate 2787 606 1630 256 = 215046367232 :=
  @P1_7_1_3.block_append 2787 606 1630 1758 128 128 256 103614764032 111431603200 215046367232 cost_2787_606_block8 cost_2787_606_block9 rfl rfl rfl

private theorem cost_2787_606_join0_10 : P1_7_1_3.blockEstimate 2787 606 1886 256 = 236129953792 :=
  @P1_7_1_3.block_append 2787 606 1886 2014 128 128 256 116702499840 119427453952 236129953792 cost_2787_606_block10 cost_2787_606_block11 rfl rfl rfl

private theorem cost_2787_606_join0_12 : P1_7_1_3.blockEstimate 2787 606 2142 256 = 236846000128 :=
  @P1_7_1_3.block_append 2787 606 2142 2270 128 128 256 119606465536 117239534592 236846000128 cost_2787_606_block12 cost_2787_606_block13 rfl rfl rfl

private theorem cost_2787_606_join0_14 : P1_7_1_3.blockEstimate 2787 606 2398 256 = 217194506240 :=
  @P1_7_1_3.block_append 2787 606 2398 2526 128 128 256 112326661120 104867845120 217194506240 cost_2787_606_block14 cost_2787_606_block15 rfl rfl rfl

private theorem cost_2787_606_join0_16 : P1_7_1_3.blockEstimate 2787 606 2654 256 = 177444100170 :=
  @P1_7_1_3.block_append 2787 606 2654 2782 128 128 256 94863086592 82581013578 177444100170 cost_2787_606_block16 cost_2787_606_block17 rfl rfl rfl

private theorem cost_2787_606_join0_18 : P1_7_1_3.blockEstimate 2787 606 2910 256 = 125554923543 :=
  @P1_7_1_3.block_append 2787 606 2910 3038 128 128 256 69399008652 56155914891 125554923543 cost_2787_606_block18 cost_2787_606_block19 rfl rfl rfl

private theorem cost_2787_606_join0_20 : P1_7_1_3.blockEstimate 2787 606 3166 256 = 74894027069 :=
  @P1_7_1_3.block_append 2787 606 3166 3294 128 128 256 43372306016 31521721053 74894027069 cost_2787_606_block20 cost_2787_606_block21 rfl rfl rfl

private theorem cost_2787_606_join0_22 : P1_7_1_3.blockEstimate 2787 606 3422 256 = 33239792928 :=
  @P1_7_1_3.block_append 2787 606 3422 3550 128 128 256 20975325328 12264467600 33239792928 cost_2787_606_block22 cost_2787_606_block23 rfl rfl rfl

private theorem cost_2787_606_join0_24 : P1_7_1_3.blockEstimate 2787 606 3678 256 = 7303752992 :=
  @P1_7_1_3.block_append 2787 606 3678 3806 128 128 256 5717543056 1586209936 7303752992 cost_2787_606_block24 cost_2787_606_block25 rfl rfl rfl

private theorem cost_2787_606_join1_0 : P1_7_1_3.blockEstimate 2787 606 606 512 = 54086451840 :=
  @P1_7_1_3.block_append 2787 606 606 862 256 256 512 7343522112 46742929728 54086451840 cost_2787_606_join0_0 cost_2787_606_join0_2 rfl rfl rfl

private theorem cost_2787_606_join1_2 : P1_7_1_3.blockEstimate 2787 606 1118 512 = 285683524468 :=
  @P1_7_1_3.block_append 2787 606 1118 1374 256 256 512 112088284020 173595240448 285683524468 cost_2787_606_join0_4 cost_2787_606_join0_6 rfl rfl rfl

private theorem cost_2787_606_join1_4 : P1_7_1_3.blockEstimate 2787 606 1630 512 = 451176321024 :=
  @P1_7_1_3.block_append 2787 606 1630 1886 256 256 512 215046367232 236129953792 451176321024 cost_2787_606_join0_8 cost_2787_606_join0_10 rfl rfl rfl

private theorem cost_2787_606_join1_6 : P1_7_1_3.blockEstimate 2787 606 2142 512 = 454040506368 :=
  @P1_7_1_3.block_append 2787 606 2142 2398 256 256 512 236846000128 217194506240 454040506368 cost_2787_606_join0_12 cost_2787_606_join0_14 rfl rfl rfl

private theorem cost_2787_606_join1_8 : P1_7_1_3.blockEstimate 2787 606 2654 512 = 302999023713 :=
  @P1_7_1_3.block_append 2787 606 2654 2910 256 256 512 177444100170 125554923543 302999023713 cost_2787_606_join0_16 cost_2787_606_join0_18 rfl rfl rfl

private theorem cost_2787_606_join1_10 : P1_7_1_3.blockEstimate 2787 606 3166 512 = 108133819997 :=
  @P1_7_1_3.block_append 2787 606 3166 3422 256 256 512 74894027069 33239792928 108133819997 cost_2787_606_join0_20 cost_2787_606_join0_22 rfl rfl rfl

private theorem cost_2787_606_join1_12 : P1_7_1_3.blockEstimate 2787 606 3678 321 = 7371295947 :=
  @P1_7_1_3.block_append 2787 606 3678 3934 256 65 321 7303752992 67542955 7371295947 cost_2787_606_join0_24 cost_2787_606_block26 rfl rfl rfl

private theorem cost_2787_606_join2_0 : P1_7_1_3.blockEstimate 2787 606 606 1024 = 339769976308 :=
  @P1_7_1_3.block_append 2787 606 606 1118 512 512 1024 54086451840 285683524468 339769976308 cost_2787_606_join1_0 cost_2787_606_join1_2 rfl rfl rfl

private theorem cost_2787_606_join2_2 : P1_7_1_3.blockEstimate 2787 606 1630 1024 = 905216827392 :=
  @P1_7_1_3.block_append 2787 606 1630 2142 512 512 1024 451176321024 454040506368 905216827392 cost_2787_606_join1_4 cost_2787_606_join1_6 rfl rfl rfl

private theorem cost_2787_606_join2_4 : P1_7_1_3.blockEstimate 2787 606 2654 1024 = 411132843710 :=
  @P1_7_1_3.block_append 2787 606 2654 3166 512 512 1024 302999023713 108133819997 411132843710 cost_2787_606_join1_8 cost_2787_606_join1_10 rfl rfl rfl

private theorem cost_2787_606_join3_0 : P1_7_1_3.blockEstimate 2787 606 606 2048 = 1244986803700 :=
  @P1_7_1_3.block_append 2787 606 606 1630 1024 1024 2048 339769976308 905216827392 1244986803700 cost_2787_606_join2_0 cost_2787_606_join2_2 rfl rfl rfl

private theorem cost_2787_606_join3_2 : P1_7_1_3.blockEstimate 2787 606 2654 1345 = 418504139657 :=
  @P1_7_1_3.block_append 2787 606 2654 3678 1024 321 1345 411132843710 7371295947 418504139657 cost_2787_606_join2_4 cost_2787_606_join1_12 rfl rfl rfl

private theorem cost_2787_606_join4_0 : P1_7_1_3.blockEstimate 2787 606 606 3393 = 1663490943357 :=
  @P1_7_1_3.block_append 2787 606 606 2654 2048 1345 3393 1244986803700 418504139657 1663490943357 cost_2787_606_join3_0 cost_2787_606_join3_2 rfl rfl rfl

private theorem cost_2787_606_total : P1_7_1_3.momentEstimate 2787 606 = 1663490943357 := by
  unfold P1_7_1_3.momentEstimate
  rw [show 2787 + 606 = 3393 by decide]
  exact cost_2787_606_join4_0

theorem moment2787_606 : P1_7_1.groupedPoleMoment 2787 606 ≤ 1663490943357 :=
  (P1_7_1_3.grouped_bound 2787 606).trans_eq cost_2787_606_total

end Research6966.HelperRescueCatalogue

end Merged6967_Near6967RescueMoment20
