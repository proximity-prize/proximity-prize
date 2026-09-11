import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked22

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_23_0_0 : C 23 0 0 := by decide +kernel
theorem cell_23_0_1 : C 23 0 1 := by decide +kernel
theorem cell_23_0_2 : C 23 0 2 := by decide +kernel
theorem cell_23_0_3 : C 23 0 3 := by decide +kernel
theorem cell_23_0_4 : C 23 0 4 := by decide +kernel
theorem cell_23_0_5 : C 23 0 5 := by decide +kernel
theorem row_23_0 : ThresholdAt 23 0 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 0 0 cell_23_0_0
  | exact S 23 0 1 cell_23_0_1
  | exact S 23 0 2 cell_23_0_2
  | exact S 23 0 3 cell_23_0_3
  | exact S 23 0 4 cell_23_0_4
  | exact S 23 0 5 cell_23_0_5
theorem cell_23_1_0 : C 23 1 0 := by decide +kernel
theorem cell_23_1_1 : C 23 1 1 := by decide +kernel
theorem cell_23_1_2 : C 23 1 2 := by decide +kernel
theorem cell_23_1_3 : C 23 1 3 := by decide +kernel
theorem cell_23_1_4 : C 23 1 4 := by decide +kernel
theorem cell_23_1_5 : C 23 1 5 := by decide +kernel
theorem row_23_1 : ThresholdAt 23 1 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 1 0 cell_23_1_0
  | exact S 23 1 1 cell_23_1_1
  | exact S 23 1 2 cell_23_1_2
  | exact S 23 1 3 cell_23_1_3
  | exact S 23 1 4 cell_23_1_4
  | exact S 23 1 5 cell_23_1_5
theorem cell_23_2_0 : C 23 2 0 := by decide +kernel
theorem cell_23_2_1 : C 23 2 1 := by decide +kernel
theorem cell_23_2_2 : C 23 2 2 := by decide +kernel
theorem cell_23_2_3 : C 23 2 3 := by decide +kernel
theorem cell_23_2_4 : C 23 2 4 := by decide +kernel
theorem cell_23_2_5 : C 23 2 5 := by decide +kernel
theorem row_23_2 : ThresholdAt 23 2 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 2 0 cell_23_2_0
  | exact S 23 2 1 cell_23_2_1
  | exact S 23 2 2 cell_23_2_2
  | exact S 23 2 3 cell_23_2_3
  | exact S 23 2 4 cell_23_2_4
  | exact S 23 2 5 cell_23_2_5
theorem cell_23_3_0 : C 23 3 0 := by decide +kernel
theorem cell_23_3_1 : C 23 3 1 := by decide +kernel
theorem cell_23_3_2 : C 23 3 2 := by decide +kernel
theorem cell_23_3_3 : C 23 3 3 := by decide +kernel
theorem cell_23_3_4 : C 23 3 4 := by decide +kernel
theorem cell_23_3_5 : C 23 3 5 := by decide +kernel
theorem row_23_3 : ThresholdAt 23 3 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 3 0 cell_23_3_0
  | exact S 23 3 1 cell_23_3_1
  | exact S 23 3 2 cell_23_3_2
  | exact S 23 3 3 cell_23_3_3
  | exact S 23 3 4 cell_23_3_4
  | exact S 23 3 5 cell_23_3_5
theorem cell_23_4_0 : C 23 4 0 := by decide +kernel
theorem cell_23_4_1 : C 23 4 1 := by decide +kernel
theorem cell_23_4_2 : C 23 4 2 := by decide +kernel
theorem cell_23_4_3 : C 23 4 3 := by decide +kernel
theorem cell_23_4_4 : C 23 4 4 := by decide +kernel
theorem cell_23_4_5 : C 23 4 5 := by decide +kernel
theorem row_23_4 : ThresholdAt 23 4 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 4 0 cell_23_4_0
  | exact S 23 4 1 cell_23_4_1
  | exact S 23 4 2 cell_23_4_2
  | exact S 23 4 3 cell_23_4_3
  | exact S 23 4 4 cell_23_4_4
  | exact S 23 4 5 cell_23_4_5
theorem cell_23_5_0 : C 23 5 0 := by decide +kernel
theorem cell_23_5_1 : C 23 5 1 := by decide +kernel
theorem cell_23_5_2 : C 23 5 2 := by decide +kernel
theorem cell_23_5_3 : C 23 5 3 := by decide +kernel
theorem cell_23_5_4 : C 23 5 4 := by decide +kernel
theorem cell_23_5_5 : C 23 5 5 := by decide +kernel
theorem row_23_5 : ThresholdAt 23 5 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 5 0 cell_23_5_0
  | exact S 23 5 1 cell_23_5_1
  | exact S 23 5 2 cell_23_5_2
  | exact S 23 5 3 cell_23_5_3
  | exact S 23 5 4 cell_23_5_4
  | exact S 23 5 5 cell_23_5_5
theorem cell_23_6_0 : C 23 6 0 := by decide +kernel
theorem cell_23_6_1 : C 23 6 1 := by decide +kernel
theorem cell_23_6_2 : C 23 6 2 := by decide +kernel
theorem cell_23_6_3 : C 23 6 3 := by decide +kernel
theorem cell_23_6_4 : C 23 6 4 := by decide +kernel
theorem cell_23_6_5 : C 23 6 5 := by decide +kernel
theorem row_23_6 : ThresholdAt 23 6 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 6 0 cell_23_6_0
  | exact S 23 6 1 cell_23_6_1
  | exact S 23 6 2 cell_23_6_2
  | exact S 23 6 3 cell_23_6_3
  | exact S 23 6 4 cell_23_6_4
  | exact S 23 6 5 cell_23_6_5
theorem cell_23_7_0 : C 23 7 0 := by decide +kernel
theorem cell_23_7_1 : C 23 7 1 := by decide +kernel
theorem cell_23_7_2 : C 23 7 2 := by decide +kernel
theorem cell_23_7_3 : C 23 7 3 := by decide +kernel
theorem cell_23_7_4 : C 23 7 4 := by decide +kernel
theorem cell_23_7_5 : C 23 7 5 := by decide +kernel
theorem row_23_7 : ThresholdAt 23 7 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 7 0 cell_23_7_0
  | exact S 23 7 1 cell_23_7_1
  | exact S 23 7 2 cell_23_7_2
  | exact S 23 7 3 cell_23_7_3
  | exact S 23 7 4 cell_23_7_4
  | exact S 23 7 5 cell_23_7_5
theorem cell_23_8_0 : C 23 8 0 := by decide +kernel
theorem cell_23_8_1 : C 23 8 1 := by decide +kernel
theorem cell_23_8_2 : C 23 8 2 := by decide +kernel
theorem cell_23_8_3 : C 23 8 3 := by decide +kernel
theorem cell_23_8_4 : C 23 8 4 := by decide +kernel
theorem cell_23_8_5 : C 23 8 5 := by decide +kernel
theorem row_23_8 : ThresholdAt 23 8 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 8 0 cell_23_8_0
  | exact S 23 8 1 cell_23_8_1
  | exact S 23 8 2 cell_23_8_2
  | exact S 23 8 3 cell_23_8_3
  | exact S 23 8 4 cell_23_8_4
  | exact S 23 8 5 cell_23_8_5
theorem cell_23_9_0 : C 23 9 0 := by decide +kernel
theorem cell_23_9_1 : C 23 9 1 := by decide +kernel
theorem cell_23_9_2 : C 23 9 2 := by decide +kernel
theorem cell_23_9_3 : C 23 9 3 := by decide +kernel
theorem cell_23_9_4 : C 23 9 4 := by decide +kernel
theorem cell_23_9_5 : C 23 9 5 := by decide +kernel
theorem row_23_9 : ThresholdAt 23 9 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 9 0 cell_23_9_0
  | exact S 23 9 1 cell_23_9_1
  | exact S 23 9 2 cell_23_9_2
  | exact S 23 9 3 cell_23_9_3
  | exact S 23 9 4 cell_23_9_4
  | exact S 23 9 5 cell_23_9_5
theorem cell_23_10_0 : C 23 10 0 := by decide +kernel
theorem cell_23_10_1 : C 23 10 1 := by decide +kernel
theorem cell_23_10_2 : C 23 10 2 := by decide +kernel
theorem cell_23_10_3 : C 23 10 3 := by decide +kernel
theorem cell_23_10_4 : C 23 10 4 := by decide +kernel
theorem cell_23_10_5 : C 23 10 5 := by decide +kernel
theorem row_23_10 : ThresholdAt 23 10 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 10 0 cell_23_10_0
  | exact S 23 10 1 cell_23_10_1
  | exact S 23 10 2 cell_23_10_2
  | exact S 23 10 3 cell_23_10_3
  | exact S 23 10 4 cell_23_10_4
  | exact S 23 10 5 cell_23_10_5
theorem cell_23_11_0 : C 23 11 0 := by decide +kernel
theorem cell_23_11_1 : C 23 11 1 := by decide +kernel
theorem cell_23_11_2 : C 23 11 2 := by decide +kernel
theorem cell_23_11_3 : C 23 11 3 := by decide +kernel
theorem cell_23_11_4 : C 23 11 4 := by decide +kernel
theorem cell_23_11_5 : C 23 11 5 := by decide +kernel
theorem row_23_11 : ThresholdAt 23 11 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 11 0 cell_23_11_0
  | exact S 23 11 1 cell_23_11_1
  | exact S 23 11 2 cell_23_11_2
  | exact S 23 11 3 cell_23_11_3
  | exact S 23 11 4 cell_23_11_4
  | exact S 23 11 5 cell_23_11_5
theorem cell_23_12_0 : C 23 12 0 := by decide +kernel
theorem cell_23_12_1 : C 23 12 1 := by decide +kernel
theorem cell_23_12_2 : C 23 12 2 := by decide +kernel
theorem cell_23_12_3 : C 23 12 3 := by decide +kernel
theorem cell_23_12_4 : C 23 12 4 := by decide +kernel
theorem cell_23_12_5 : C 23 12 5 := by decide +kernel
theorem row_23_12 : ThresholdAt 23 12 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 12 0 cell_23_12_0
  | exact S 23 12 1 cell_23_12_1
  | exact S 23 12 2 cell_23_12_2
  | exact S 23 12 3 cell_23_12_3
  | exact S 23 12 4 cell_23_12_4
  | exact S 23 12 5 cell_23_12_5
theorem cell_23_13_0 : C 23 13 0 := by decide +kernel
theorem cell_23_13_1 : C 23 13 1 := by decide +kernel
theorem cell_23_13_2 : C 23 13 2 := by decide +kernel
theorem cell_23_13_3 : C 23 13 3 := by decide +kernel
theorem cell_23_13_4 : C 23 13 4 := by decide +kernel
theorem cell_23_13_5 : C 23 13 5 := by decide +kernel
theorem row_23_13 : ThresholdAt 23 13 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 13 0 cell_23_13_0
  | exact S 23 13 1 cell_23_13_1
  | exact S 23 13 2 cell_23_13_2
  | exact S 23 13 3 cell_23_13_3
  | exact S 23 13 4 cell_23_13_4
  | exact S 23 13 5 cell_23_13_5
theorem cell_23_14_0 : C 23 14 0 := by decide +kernel
theorem cell_23_14_1 : C 23 14 1 := by decide +kernel
theorem cell_23_14_2 : C 23 14 2 := by decide +kernel
theorem cell_23_14_3 : C 23 14 3 := by decide +kernel
theorem cell_23_14_4 : C 23 14 4 := by decide +kernel
theorem cell_23_14_5 : C 23 14 5 := by decide +kernel
theorem row_23_14 : ThresholdAt 23 14 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 14 0 cell_23_14_0
  | exact S 23 14 1 cell_23_14_1
  | exact S 23 14 2 cell_23_14_2
  | exact S 23 14 3 cell_23_14_3
  | exact S 23 14 4 cell_23_14_4
  | exact S 23 14 5 cell_23_14_5
theorem cell_23_15_0 : C 23 15 0 := by decide +kernel
theorem cell_23_15_1 : C 23 15 1 := by decide +kernel
theorem cell_23_15_2 : C 23 15 2 := by decide +kernel
theorem cell_23_15_3 : C 23 15 3 := by decide +kernel
theorem cell_23_15_4 : C 23 15 4 := by decide +kernel
theorem cell_23_15_5 : C 23 15 5 := by decide +kernel
theorem row_23_15 : ThresholdAt 23 15 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 15 0 cell_23_15_0
  | exact S 23 15 1 cell_23_15_1
  | exact S 23 15 2 cell_23_15_2
  | exact S 23 15 3 cell_23_15_3
  | exact S 23 15 4 cell_23_15_4
  | exact S 23 15 5 cell_23_15_5
theorem cell_23_16_0 : C 23 16 0 := by decide +kernel
theorem cell_23_16_1 : C 23 16 1 := by decide +kernel
theorem cell_23_16_2 : C 23 16 2 := by decide +kernel
theorem cell_23_16_3 : C 23 16 3 := by decide +kernel
theorem cell_23_16_4 : C 23 16 4 := by decide +kernel
theorem cell_23_16_5 : C 23 16 5 := by decide +kernel
theorem row_23_16 : ThresholdAt 23 16 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 16 0 cell_23_16_0
  | exact S 23 16 1 cell_23_16_1
  | exact S 23 16 2 cell_23_16_2
  | exact S 23 16 3 cell_23_16_3
  | exact S 23 16 4 cell_23_16_4
  | exact S 23 16 5 cell_23_16_5
theorem cell_23_17_0 : C 23 17 0 := by decide +kernel
theorem cell_23_17_1 : C 23 17 1 := by decide +kernel
theorem cell_23_17_2 : C 23 17 2 := by decide +kernel
theorem cell_23_17_3 : C 23 17 3 := by decide +kernel
theorem cell_23_17_4 : C 23 17 4 := by decide +kernel
theorem cell_23_17_5 : C 23 17 5 := by decide +kernel
theorem row_23_17 : ThresholdAt 23 17 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 17 0 cell_23_17_0
  | exact S 23 17 1 cell_23_17_1
  | exact S 23 17 2 cell_23_17_2
  | exact S 23 17 3 cell_23_17_3
  | exact S 23 17 4 cell_23_17_4
  | exact S 23 17 5 cell_23_17_5
theorem cell_23_18_0 : C 23 18 0 := by decide +kernel
theorem cell_23_18_1 : C 23 18 1 := by decide +kernel
theorem cell_23_18_2 : C 23 18 2 := by decide +kernel
theorem cell_23_18_3 : C 23 18 3 := by decide +kernel
theorem cell_23_18_4 : C 23 18 4 := by decide +kernel
theorem cell_23_18_5 : C 23 18 5 := by decide +kernel
theorem row_23_18 : ThresholdAt 23 18 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 18 0 cell_23_18_0
  | exact S 23 18 1 cell_23_18_1
  | exact S 23 18 2 cell_23_18_2
  | exact S 23 18 3 cell_23_18_3
  | exact S 23 18 4 cell_23_18_4
  | exact S 23 18 5 cell_23_18_5
theorem cell_23_19_0 : C 23 19 0 := by decide +kernel
theorem cell_23_19_1 : C 23 19 1 := by decide +kernel
theorem cell_23_19_2 : C 23 19 2 := by decide +kernel
theorem cell_23_19_3 : C 23 19 3 := by decide +kernel
theorem cell_23_19_4 : C 23 19 4 := by decide +kernel
theorem cell_23_19_5 : C 23 19 5 := by decide +kernel
theorem row_23_19 : ThresholdAt 23 19 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 19 0 cell_23_19_0
  | exact S 23 19 1 cell_23_19_1
  | exact S 23 19 2 cell_23_19_2
  | exact S 23 19 3 cell_23_19_3
  | exact S 23 19 4 cell_23_19_4
  | exact S 23 19 5 cell_23_19_5
theorem cell_23_20_0 : C 23 20 0 := by decide +kernel
theorem cell_23_20_1 : C 23 20 1 := by decide +kernel
theorem cell_23_20_2 : C 23 20 2 := by decide +kernel
theorem cell_23_20_3 : C 23 20 3 := by decide +kernel
theorem cell_23_20_4 : C 23 20 4 := by decide +kernel
theorem cell_23_20_5 : C 23 20 5 := by decide +kernel
theorem row_23_20 : ThresholdAt 23 20 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 20 0 cell_23_20_0
  | exact S 23 20 1 cell_23_20_1
  | exact S 23 20 2 cell_23_20_2
  | exact S 23 20 3 cell_23_20_3
  | exact S 23 20 4 cell_23_20_4
  | exact S 23 20 5 cell_23_20_5
theorem cell_23_21_0 : C 23 21 0 := by decide +kernel
theorem cell_23_21_1 : C 23 21 1 := by decide +kernel
theorem cell_23_21_2 : C 23 21 2 := by decide +kernel
theorem cell_23_21_3 : C 23 21 3 := by decide +kernel
theorem cell_23_21_4 : C 23 21 4 := by decide +kernel
theorem cell_23_21_5 : C 23 21 5 := by decide +kernel
theorem row_23_21 : ThresholdAt 23 21 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 21 0 cell_23_21_0
  | exact S 23 21 1 cell_23_21_1
  | exact S 23 21 2 cell_23_21_2
  | exact S 23 21 3 cell_23_21_3
  | exact S 23 21 4 cell_23_21_4
  | exact S 23 21 5 cell_23_21_5
theorem cell_23_22_0 : C 23 22 0 := by decide +kernel
theorem cell_23_22_1 : C 23 22 1 := by decide +kernel
theorem cell_23_22_2 : C 23 22 2 := by decide +kernel
theorem cell_23_22_3 : C 23 22 3 := by decide +kernel
theorem cell_23_22_4 : C 23 22 4 := by decide +kernel
theorem cell_23_22_5 : C 23 22 5 := by decide +kernel
theorem row_23_22 : ThresholdAt 23 22 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 22 0 cell_23_22_0
  | exact S 23 22 1 cell_23_22_1
  | exact S 23 22 2 cell_23_22_2
  | exact S 23 22 3 cell_23_22_3
  | exact S 23 22 4 cell_23_22_4
  | exact S 23 22 5 cell_23_22_5
theorem cell_23_23_0 : C 23 23 0 := by decide +kernel
theorem cell_23_23_1 : C 23 23 1 := by decide +kernel
theorem cell_23_23_2 : C 23 23 2 := by decide +kernel
theorem cell_23_23_3 : C 23 23 3 := by decide +kernel
theorem cell_23_23_4 : C 23 23 4 := by decide +kernel
theorem cell_23_23_5 : C 23 23 5 := by decide +kernel
theorem row_23_23 : ThresholdAt 23 23 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 23 0 cell_23_23_0
  | exact S 23 23 1 cell_23_23_1
  | exact S 23 23 2 cell_23_23_2
  | exact S 23 23 3 cell_23_23_3
  | exact S 23 23 4 cell_23_23_4
  | exact S 23 23 5 cell_23_23_5
theorem cell_23_24_0 : C 23 24 0 := by decide +kernel
theorem cell_23_24_1 : C 23 24 1 := by decide +kernel
theorem cell_23_24_2 : C 23 24 2 := by decide +kernel
theorem cell_23_24_3 : C 23 24 3 := by decide +kernel
theorem cell_23_24_4 : C 23 24 4 := by decide +kernel
theorem cell_23_24_5 : C 23 24 5 := by decide +kernel
theorem row_23_24 : ThresholdAt 23 24 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 24 0 cell_23_24_0
  | exact S 23 24 1 cell_23_24_1
  | exact S 23 24 2 cell_23_24_2
  | exact S 23 24 3 cell_23_24_3
  | exact S 23 24 4 cell_23_24_4
  | exact S 23 24 5 cell_23_24_5
theorem cell_23_25_0 : C 23 25 0 := by decide +kernel
theorem cell_23_25_1 : C 23 25 1 := by decide +kernel
theorem cell_23_25_2 : C 23 25 2 := by decide +kernel
theorem cell_23_25_3 : C 23 25 3 := by decide +kernel
theorem cell_23_25_4 : C 23 25 4 := by decide +kernel
theorem cell_23_25_5 : C 23 25 5 := by decide +kernel
theorem row_23_25 : ThresholdAt 23 25 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 25 0 cell_23_25_0
  | exact S 23 25 1 cell_23_25_1
  | exact S 23 25 2 cell_23_25_2
  | exact S 23 25 3 cell_23_25_3
  | exact S 23 25 4 cell_23_25_4
  | exact S 23 25 5 cell_23_25_5
theorem cell_23_26_0 : C 23 26 0 := by decide +kernel
theorem cell_23_26_1 : C 23 26 1 := by decide +kernel
theorem cell_23_26_2 : C 23 26 2 := by decide +kernel
theorem cell_23_26_3 : C 23 26 3 := by decide +kernel
theorem cell_23_26_4 : C 23 26 4 := by decide +kernel
theorem cell_23_26_5 : C 23 26 5 := by decide +kernel
theorem row_23_26 : ThresholdAt 23 26 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 26 0 cell_23_26_0
  | exact S 23 26 1 cell_23_26_1
  | exact S 23 26 2 cell_23_26_2
  | exact S 23 26 3 cell_23_26_3
  | exact S 23 26 4 cell_23_26_4
  | exact S 23 26 5 cell_23_26_5
theorem cell_23_27_0 : C 23 27 0 := by decide +kernel
theorem cell_23_27_1 : C 23 27 1 := by decide +kernel
theorem cell_23_27_2 : C 23 27 2 := by decide +kernel
theorem cell_23_27_3 : C 23 27 3 := by decide +kernel
theorem cell_23_27_4 : C 23 27 4 := by decide +kernel
theorem cell_23_27_5 : C 23 27 5 := by decide +kernel
theorem row_23_27 : ThresholdAt 23 27 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 27 0 cell_23_27_0
  | exact S 23 27 1 cell_23_27_1
  | exact S 23 27 2 cell_23_27_2
  | exact S 23 27 3 cell_23_27_3
  | exact S 23 27 4 cell_23_27_4
  | exact S 23 27 5 cell_23_27_5
theorem cell_23_28_0 : C 23 28 0 := by decide +kernel
theorem cell_23_28_1 : C 23 28 1 := by decide +kernel
theorem cell_23_28_2 : C 23 28 2 := by decide +kernel
theorem cell_23_28_3 : C 23 28 3 := by decide +kernel
theorem cell_23_28_4 : C 23 28 4 := by decide +kernel
theorem cell_23_28_5 : C 23 28 5 := by decide +kernel
theorem row_23_28 : ThresholdAt 23 28 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 28 0 cell_23_28_0
  | exact S 23 28 1 cell_23_28_1
  | exact S 23 28 2 cell_23_28_2
  | exact S 23 28 3 cell_23_28_3
  | exact S 23 28 4 cell_23_28_4
  | exact S 23 28 5 cell_23_28_5
theorem cell_23_29_0 : C 23 29 0 := by decide +kernel
theorem cell_23_29_1 : C 23 29 1 := by decide +kernel
theorem cell_23_29_2 : C 23 29 2 := by decide +kernel
theorem cell_23_29_3 : C 23 29 3 := by decide +kernel
theorem cell_23_29_4 : C 23 29 4 := by decide +kernel
theorem cell_23_29_5 : C 23 29 5 := by decide +kernel
theorem row_23_29 : ThresholdAt 23 29 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 29 0 cell_23_29_0
  | exact S 23 29 1 cell_23_29_1
  | exact S 23 29 2 cell_23_29_2
  | exact S 23 29 3 cell_23_29_3
  | exact S 23 29 4 cell_23_29_4
  | exact S 23 29 5 cell_23_29_5
theorem cell_23_30_0 : C 23 30 0 := by decide +kernel
theorem cell_23_30_1 : C 23 30 1 := by decide +kernel
theorem cell_23_30_2 : C 23 30 2 := by decide +kernel
theorem cell_23_30_3 : C 23 30 3 := by decide +kernel
theorem cell_23_30_4 : C 23 30 4 := by decide +kernel
theorem cell_23_30_5 : C 23 30 5 := by decide +kernel
theorem row_23_30 : ThresholdAt 23 30 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 30 0 cell_23_30_0
  | exact S 23 30 1 cell_23_30_1
  | exact S 23 30 2 cell_23_30_2
  | exact S 23 30 3 cell_23_30_3
  | exact S 23 30 4 cell_23_30_4
  | exact S 23 30 5 cell_23_30_5
theorem cell_23_31_0 : C 23 31 0 := by decide +kernel
theorem cell_23_31_1 : C 23 31 1 := by decide +kernel
theorem cell_23_31_2 : C 23 31 2 := by decide +kernel
theorem cell_23_31_3 : C 23 31 3 := by decide +kernel
theorem cell_23_31_4 : C 23 31 4 := by decide +kernel
theorem cell_23_31_5 : C 23 31 5 := by decide +kernel
theorem row_23_31 : ThresholdAt 23 31 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 31 0 cell_23_31_0
  | exact S 23 31 1 cell_23_31_1
  | exact S 23 31 2 cell_23_31_2
  | exact S 23 31 3 cell_23_31_3
  | exact S 23 31 4 cell_23_31_4
  | exact S 23 31 5 cell_23_31_5
theorem cell_23_32_0 : C 23 32 0 := by decide +kernel
theorem cell_23_32_1 : C 23 32 1 := by decide +kernel
theorem cell_23_32_2 : C 23 32 2 := by decide +kernel
theorem cell_23_32_3 : C 23 32 3 := by decide +kernel
theorem cell_23_32_4 : C 23 32 4 := by decide +kernel
theorem cell_23_32_5 : C 23 32 5 := by decide +kernel
theorem row_23_32 : ThresholdAt 23 32 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 32 0 cell_23_32_0
  | exact S 23 32 1 cell_23_32_1
  | exact S 23 32 2 cell_23_32_2
  | exact S 23 32 3 cell_23_32_3
  | exact S 23 32 4 cell_23_32_4
  | exact S 23 32 5 cell_23_32_5
theorem cell_23_33_0 : C 23 33 0 := by decide +kernel
theorem cell_23_33_1 : C 23 33 1 := by decide +kernel
theorem cell_23_33_2 : C 23 33 2 := by decide +kernel
theorem cell_23_33_3 : C 23 33 3 := by decide +kernel
theorem cell_23_33_4 : C 23 33 4 := by decide +kernel
theorem cell_23_33_5 : C 23 33 5 := by decide +kernel
theorem row_23_33 : ThresholdAt 23 33 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 33 0 cell_23_33_0
  | exact S 23 33 1 cell_23_33_1
  | exact S 23 33 2 cell_23_33_2
  | exact S 23 33 3 cell_23_33_3
  | exact S 23 33 4 cell_23_33_4
  | exact S 23 33 5 cell_23_33_5
theorem cell_23_34_0 : C 23 34 0 := by decide +kernel
theorem cell_23_34_1 : C 23 34 1 := by decide +kernel
theorem cell_23_34_2 : C 23 34 2 := by decide +kernel
theorem cell_23_34_3 : C 23 34 3 := by decide +kernel
theorem cell_23_34_4 : C 23 34 4 := by decide +kernel
theorem cell_23_34_5 : C 23 34 5 := by decide +kernel
theorem row_23_34 : ThresholdAt 23 34 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 34 0 cell_23_34_0
  | exact S 23 34 1 cell_23_34_1
  | exact S 23 34 2 cell_23_34_2
  | exact S 23 34 3 cell_23_34_3
  | exact S 23 34 4 cell_23_34_4
  | exact S 23 34 5 cell_23_34_5
theorem cell_23_35_0 : C 23 35 0 := by decide +kernel
theorem cell_23_35_1 : C 23 35 1 := by decide +kernel
theorem cell_23_35_2 : C 23 35 2 := by decide +kernel
theorem cell_23_35_3 : C 23 35 3 := by decide +kernel
theorem cell_23_35_4 : C 23 35 4 := by decide +kernel
theorem cell_23_35_5 : C 23 35 5 := by decide +kernel
theorem row_23_35 : ThresholdAt 23 35 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 35 0 cell_23_35_0
  | exact S 23 35 1 cell_23_35_1
  | exact S 23 35 2 cell_23_35_2
  | exact S 23 35 3 cell_23_35_3
  | exact S 23 35 4 cell_23_35_4
  | exact S 23 35 5 cell_23_35_5
theorem cell_23_36_0 : C 23 36 0 := by decide +kernel
theorem cell_23_36_1 : C 23 36 1 := by decide +kernel
theorem cell_23_36_2 : C 23 36 2 := by decide +kernel
theorem cell_23_36_3 : C 23 36 3 := by decide +kernel
theorem cell_23_36_4 : C 23 36 4 := by decide +kernel
theorem cell_23_36_5 : C 23 36 5 := by decide +kernel
theorem row_23_36 : ThresholdAt 23 36 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 36 0 cell_23_36_0
  | exact S 23 36 1 cell_23_36_1
  | exact S 23 36 2 cell_23_36_2
  | exact S 23 36 3 cell_23_36_3
  | exact S 23 36 4 cell_23_36_4
  | exact S 23 36 5 cell_23_36_5
theorem cell_23_37_0 : C 23 37 0 := by decide +kernel
theorem cell_23_37_1 : C 23 37 1 := by decide +kernel
theorem cell_23_37_2 : C 23 37 2 := by decide +kernel
theorem cell_23_37_3 : C 23 37 3 := by decide +kernel
theorem cell_23_37_4 : C 23 37 4 := by decide +kernel
theorem cell_23_37_5 : C 23 37 5 := by decide +kernel
theorem row_23_37 : ThresholdAt 23 37 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 37 0 cell_23_37_0
  | exact S 23 37 1 cell_23_37_1
  | exact S 23 37 2 cell_23_37_2
  | exact S 23 37 3 cell_23_37_3
  | exact S 23 37 4 cell_23_37_4
  | exact S 23 37 5 cell_23_37_5
theorem cell_23_38_0 : C 23 38 0 := by decide +kernel
theorem cell_23_38_1 : C 23 38 1 := by decide +kernel
theorem cell_23_38_2 : C 23 38 2 := by decide +kernel
theorem cell_23_38_3 : C 23 38 3 := by decide +kernel
theorem cell_23_38_4 : C 23 38 4 := by decide +kernel
theorem cell_23_38_5 : C 23 38 5 := by decide +kernel
theorem row_23_38 : ThresholdAt 23 38 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 38 0 cell_23_38_0
  | exact S 23 38 1 cell_23_38_1
  | exact S 23 38 2 cell_23_38_2
  | exact S 23 38 3 cell_23_38_3
  | exact S 23 38 4 cell_23_38_4
  | exact S 23 38 5 cell_23_38_5
theorem cell_23_39_0 : C 23 39 0 := by decide +kernel
theorem cell_23_39_1 : C 23 39 1 := by decide +kernel
theorem cell_23_39_2 : C 23 39 2 := by decide +kernel
theorem cell_23_39_3 : C 23 39 3 := by decide +kernel
theorem cell_23_39_4 : C 23 39 4 := by decide +kernel
theorem cell_23_39_5 : C 23 39 5 := by decide +kernel
theorem row_23_39 : ThresholdAt 23 39 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 39 0 cell_23_39_0
  | exact S 23 39 1 cell_23_39_1
  | exact S 23 39 2 cell_23_39_2
  | exact S 23 39 3 cell_23_39_3
  | exact S 23 39 4 cell_23_39_4
  | exact S 23 39 5 cell_23_39_5
theorem cell_23_40_0 : C 23 40 0 := by decide +kernel
theorem cell_23_40_1 : C 23 40 1 := by decide +kernel
theorem cell_23_40_2 : C 23 40 2 := by decide +kernel
theorem cell_23_40_3 : C 23 40 3 := by decide +kernel
theorem cell_23_40_4 : C 23 40 4 := by decide +kernel
theorem cell_23_40_5 : C 23 40 5 := by decide +kernel
theorem row_23_40 : ThresholdAt 23 40 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 40 0 cell_23_40_0
  | exact S 23 40 1 cell_23_40_1
  | exact S 23 40 2 cell_23_40_2
  | exact S 23 40 3 cell_23_40_3
  | exact S 23 40 4 cell_23_40_4
  | exact S 23 40 5 cell_23_40_5
theorem cell_23_41_0 : C 23 41 0 := by decide +kernel
theorem cell_23_41_1 : C 23 41 1 := by decide +kernel
theorem cell_23_41_2 : C 23 41 2 := by decide +kernel
theorem cell_23_41_3 : C 23 41 3 := by decide +kernel
theorem cell_23_41_4 : C 23 41 4 := by decide +kernel
theorem cell_23_41_5 : C 23 41 5 := by decide +kernel
theorem row_23_41 : ThresholdAt 23 41 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 41 0 cell_23_41_0
  | exact S 23 41 1 cell_23_41_1
  | exact S 23 41 2 cell_23_41_2
  | exact S 23 41 3 cell_23_41_3
  | exact S 23 41 4 cell_23_41_4
  | exact S 23 41 5 cell_23_41_5
theorem cell_23_42_0 : C 23 42 0 := by decide +kernel
theorem cell_23_42_1 : C 23 42 1 := by decide +kernel
theorem cell_23_42_2 : C 23 42 2 := by decide +kernel
theorem cell_23_42_3 : C 23 42 3 := by decide +kernel
theorem cell_23_42_4 : C 23 42 4 := by decide +kernel
theorem cell_23_42_5 : C 23 42 5 := by decide +kernel
theorem row_23_42 : ThresholdAt 23 42 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 42 0 cell_23_42_0
  | exact S 23 42 1 cell_23_42_1
  | exact S 23 42 2 cell_23_42_2
  | exact S 23 42 3 cell_23_42_3
  | exact S 23 42 4 cell_23_42_4
  | exact S 23 42 5 cell_23_42_5
theorem cell_23_43_0 : C 23 43 0 := by decide +kernel
theorem cell_23_43_1 : C 23 43 1 := by decide +kernel
theorem cell_23_43_2 : C 23 43 2 := by decide +kernel
theorem cell_23_43_3 : C 23 43 3 := by decide +kernel
theorem cell_23_43_4 : C 23 43 4 := by decide +kernel
theorem cell_23_43_5 : C 23 43 5 := by decide +kernel
theorem row_23_43 : ThresholdAt 23 43 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 43 0 cell_23_43_0
  | exact S 23 43 1 cell_23_43_1
  | exact S 23 43 2 cell_23_43_2
  | exact S 23 43 3 cell_23_43_3
  | exact S 23 43 4 cell_23_43_4
  | exact S 23 43 5 cell_23_43_5
theorem cell_23_44_0 : C 23 44 0 := by decide +kernel
theorem cell_23_44_1 : C 23 44 1 := by decide +kernel
theorem cell_23_44_2 : C 23 44 2 := by decide +kernel
theorem cell_23_44_3 : C 23 44 3 := by decide +kernel
theorem cell_23_44_4 : C 23 44 4 := by decide +kernel
theorem cell_23_44_5 : C 23 44 5 := by decide +kernel
theorem row_23_44 : ThresholdAt 23 44 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 44 0 cell_23_44_0
  | exact S 23 44 1 cell_23_44_1
  | exact S 23 44 2 cell_23_44_2
  | exact S 23 44 3 cell_23_44_3
  | exact S 23 44 4 cell_23_44_4
  | exact S 23 44 5 cell_23_44_5
theorem cell_23_45_0 : C 23 45 0 := by decide +kernel
theorem cell_23_45_1 : C 23 45 1 := by decide +kernel
theorem cell_23_45_2 : C 23 45 2 := by decide +kernel
theorem cell_23_45_3 : C 23 45 3 := by decide +kernel
theorem cell_23_45_4 : C 23 45 4 := by decide +kernel
theorem cell_23_45_5 : C 23 45 5 := by decide +kernel
theorem row_23_45 : ThresholdAt 23 45 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 45 0 cell_23_45_0
  | exact S 23 45 1 cell_23_45_1
  | exact S 23 45 2 cell_23_45_2
  | exact S 23 45 3 cell_23_45_3
  | exact S 23 45 4 cell_23_45_4
  | exact S 23 45 5 cell_23_45_5
theorem cell_23_46_0 : C 23 46 0 := by decide +kernel
theorem cell_23_46_1 : C 23 46 1 := by decide +kernel
theorem cell_23_46_2 : C 23 46 2 := by decide +kernel
theorem cell_23_46_3 : C 23 46 3 := by decide +kernel
theorem cell_23_46_4 : C 23 46 4 := by decide +kernel
theorem cell_23_46_5 : C 23 46 5 := by decide +kernel
theorem row_23_46 : ThresholdAt 23 46 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 46 0 cell_23_46_0
  | exact S 23 46 1 cell_23_46_1
  | exact S 23 46 2 cell_23_46_2
  | exact S 23 46 3 cell_23_46_3
  | exact S 23 46 4 cell_23_46_4
  | exact S 23 46 5 cell_23_46_5
theorem cell_23_47_0 : C 23 47 0 := by decide +kernel
theorem cell_23_47_1 : C 23 47 1 := by decide +kernel
theorem cell_23_47_2 : C 23 47 2 := by decide +kernel
theorem cell_23_47_3 : C 23 47 3 := by decide +kernel
theorem cell_23_47_4 : C 23 47 4 := by decide +kernel
theorem cell_23_47_5 : C 23 47 5 := by decide +kernel
theorem row_23_47 : ThresholdAt 23 47 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 47 0 cell_23_47_0
  | exact S 23 47 1 cell_23_47_1
  | exact S 23 47 2 cell_23_47_2
  | exact S 23 47 3 cell_23_47_3
  | exact S 23 47 4 cell_23_47_4
  | exact S 23 47 5 cell_23_47_5
theorem cell_23_48_0 : C 23 48 0 := by decide +kernel
theorem cell_23_48_1 : C 23 48 1 := by decide +kernel
theorem cell_23_48_2 : C 23 48 2 := by decide +kernel
theorem cell_23_48_3 : C 23 48 3 := by decide +kernel
theorem cell_23_48_4 : C 23 48 4 := by decide +kernel
theorem cell_23_48_5 : C 23 48 5 := by decide +kernel
theorem row_23_48 : ThresholdAt 23 48 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 48 0 cell_23_48_0
  | exact S 23 48 1 cell_23_48_1
  | exact S 23 48 2 cell_23_48_2
  | exact S 23 48 3 cell_23_48_3
  | exact S 23 48 4 cell_23_48_4
  | exact S 23 48 5 cell_23_48_5
theorem cell_23_49_0 : C 23 49 0 := by decide +kernel
theorem cell_23_49_1 : C 23 49 1 := by decide +kernel
theorem cell_23_49_2 : C 23 49 2 := by decide +kernel
theorem cell_23_49_3 : C 23 49 3 := by decide +kernel
theorem cell_23_49_4 : C 23 49 4 := by decide +kernel
theorem cell_23_49_5 : C 23 49 5 := by decide +kernel
theorem row_23_49 : ThresholdAt 23 49 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 49 0 cell_23_49_0
  | exact S 23 49 1 cell_23_49_1
  | exact S 23 49 2 cell_23_49_2
  | exact S 23 49 3 cell_23_49_3
  | exact S 23 49 4 cell_23_49_4
  | exact S 23 49 5 cell_23_49_5
theorem cell_23_50_0 : C 23 50 0 := by decide +kernel
theorem cell_23_50_1 : C 23 50 1 := by decide +kernel
theorem cell_23_50_2 : C 23 50 2 := by decide +kernel
theorem cell_23_50_3 : C 23 50 3 := by decide +kernel
theorem cell_23_50_4 : C 23 50 4 := by decide +kernel
theorem cell_23_50_5 : C 23 50 5 := by decide +kernel
theorem row_23_50 : ThresholdAt 23 50 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 50 0 cell_23_50_0
  | exact S 23 50 1 cell_23_50_1
  | exact S 23 50 2 cell_23_50_2
  | exact S 23 50 3 cell_23_50_3
  | exact S 23 50 4 cell_23_50_4
  | exact S 23 50 5 cell_23_50_5
theorem cell_23_51_0 : C 23 51 0 := by decide +kernel
theorem cell_23_51_1 : C 23 51 1 := by decide +kernel
theorem cell_23_51_2 : C 23 51 2 := by decide +kernel
theorem cell_23_51_3 : C 23 51 3 := by decide +kernel
theorem cell_23_51_4 : C 23 51 4 := by decide +kernel
theorem cell_23_51_5 : C 23 51 5 := by decide +kernel
theorem row_23_51 : ThresholdAt 23 51 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 51 0 cell_23_51_0
  | exact S 23 51 1 cell_23_51_1
  | exact S 23 51 2 cell_23_51_2
  | exact S 23 51 3 cell_23_51_3
  | exact S 23 51 4 cell_23_51_4
  | exact S 23 51 5 cell_23_51_5
theorem cell_23_52_0 : C 23 52 0 := by decide +kernel
theorem cell_23_52_1 : C 23 52 1 := by decide +kernel
theorem cell_23_52_2 : C 23 52 2 := by decide +kernel
theorem cell_23_52_3 : C 23 52 3 := by decide +kernel
theorem cell_23_52_4 : C 23 52 4 := by decide +kernel
theorem cell_23_52_5 : C 23 52 5 := by decide +kernel
theorem row_23_52 : ThresholdAt 23 52 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 52 0 cell_23_52_0
  | exact S 23 52 1 cell_23_52_1
  | exact S 23 52 2 cell_23_52_2
  | exact S 23 52 3 cell_23_52_3
  | exact S 23 52 4 cell_23_52_4
  | exact S 23 52 5 cell_23_52_5
theorem cell_23_53_0 : C 23 53 0 := by decide +kernel
theorem cell_23_53_1 : C 23 53 1 := by decide +kernel
theorem cell_23_53_2 : C 23 53 2 := by decide +kernel
theorem cell_23_53_3 : C 23 53 3 := by decide +kernel
theorem cell_23_53_4 : C 23 53 4 := by decide +kernel
theorem cell_23_53_5 : C 23 53 5 := by decide +kernel
theorem row_23_53 : ThresholdAt 23 53 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 53 0 cell_23_53_0
  | exact S 23 53 1 cell_23_53_1
  | exact S 23 53 2 cell_23_53_2
  | exact S 23 53 3 cell_23_53_3
  | exact S 23 53 4 cell_23_53_4
  | exact S 23 53 5 cell_23_53_5
theorem cell_23_54_0 : C 23 54 0 := by decide +kernel
theorem cell_23_54_1 : C 23 54 1 := by decide +kernel
theorem cell_23_54_2 : C 23 54 2 := by decide +kernel
theorem cell_23_54_3 : C 23 54 3 := by decide +kernel
theorem cell_23_54_4 : C 23 54 4 := by decide +kernel
theorem cell_23_54_5 : C 23 54 5 := by decide +kernel
theorem row_23_54 : ThresholdAt 23 54 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 54 0 cell_23_54_0
  | exact S 23 54 1 cell_23_54_1
  | exact S 23 54 2 cell_23_54_2
  | exact S 23 54 3 cell_23_54_3
  | exact S 23 54 4 cell_23_54_4
  | exact S 23 54 5 cell_23_54_5
theorem cell_23_55_0 : C 23 55 0 := by decide +kernel
theorem cell_23_55_1 : C 23 55 1 := by decide +kernel
theorem cell_23_55_2 : C 23 55 2 := by decide +kernel
theorem cell_23_55_3 : C 23 55 3 := by decide +kernel
theorem cell_23_55_4 : C 23 55 4 := by decide +kernel
theorem cell_23_55_5 : C 23 55 5 := by decide +kernel
theorem row_23_55 : ThresholdAt 23 55 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 55 0 cell_23_55_0
  | exact S 23 55 1 cell_23_55_1
  | exact S 23 55 2 cell_23_55_2
  | exact S 23 55 3 cell_23_55_3
  | exact S 23 55 4 cell_23_55_4
  | exact S 23 55 5 cell_23_55_5
theorem cell_23_56_0 : C 23 56 0 := by decide +kernel
theorem cell_23_56_1 : C 23 56 1 := by decide +kernel
theorem cell_23_56_2 : C 23 56 2 := by decide +kernel
theorem cell_23_56_3 : C 23 56 3 := by decide +kernel
theorem cell_23_56_4 : C 23 56 4 := by decide +kernel
theorem cell_23_56_5 : C 23 56 5 := by decide +kernel
theorem row_23_56 : ThresholdAt 23 56 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 56 0 cell_23_56_0
  | exact S 23 56 1 cell_23_56_1
  | exact S 23 56 2 cell_23_56_2
  | exact S 23 56 3 cell_23_56_3
  | exact S 23 56 4 cell_23_56_4
  | exact S 23 56 5 cell_23_56_5
theorem cell_23_57_0 : C 23 57 0 := by decide +kernel
theorem cell_23_57_1 : C 23 57 1 := by decide +kernel
theorem cell_23_57_2 : C 23 57 2 := by decide +kernel
theorem cell_23_57_3 : C 23 57 3 := by decide +kernel
theorem cell_23_57_4 : C 23 57 4 := by decide +kernel
theorem cell_23_57_5 : C 23 57 5 := by decide +kernel
theorem row_23_57 : ThresholdAt 23 57 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 57 0 cell_23_57_0
  | exact S 23 57 1 cell_23_57_1
  | exact S 23 57 2 cell_23_57_2
  | exact S 23 57 3 cell_23_57_3
  | exact S 23 57 4 cell_23_57_4
  | exact S 23 57 5 cell_23_57_5
theorem cell_23_58_0 : C 23 58 0 := by decide +kernel
theorem cell_23_58_1 : C 23 58 1 := by decide +kernel
theorem cell_23_58_2 : C 23 58 2 := by decide +kernel
theorem cell_23_58_3 : C 23 58 3 := by decide +kernel
theorem cell_23_58_4 : C 23 58 4 := by decide +kernel
theorem cell_23_58_5 : C 23 58 5 := by decide +kernel
theorem row_23_58 : ThresholdAt 23 58 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 58 0 cell_23_58_0
  | exact S 23 58 1 cell_23_58_1
  | exact S 23 58 2 cell_23_58_2
  | exact S 23 58 3 cell_23_58_3
  | exact S 23 58 4 cell_23_58_4
  | exact S 23 58 5 cell_23_58_5
theorem cell_23_59_0 : C 23 59 0 := by decide +kernel
theorem cell_23_59_1 : C 23 59 1 := by decide +kernel
theorem cell_23_59_2 : C 23 59 2 := by decide +kernel
theorem cell_23_59_3 : C 23 59 3 := by decide +kernel
theorem cell_23_59_4 : C 23 59 4 := by decide +kernel
theorem cell_23_59_5 : C 23 59 5 := by decide +kernel
theorem row_23_59 : ThresholdAt 23 59 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 59 0 cell_23_59_0
  | exact S 23 59 1 cell_23_59_1
  | exact S 23 59 2 cell_23_59_2
  | exact S 23 59 3 cell_23_59_3
  | exact S 23 59 4 cell_23_59_4
  | exact S 23 59 5 cell_23_59_5
theorem cell_23_60_0 : C 23 60 0 := by decide +kernel
theorem cell_23_60_1 : C 23 60 1 := by decide +kernel
theorem cell_23_60_2 : C 23 60 2 := by decide +kernel
theorem cell_23_60_3 : C 23 60 3 := by decide +kernel
theorem cell_23_60_4 : C 23 60 4 := by decide +kernel
theorem cell_23_60_5 : C 23 60 5 := by decide +kernel
theorem row_23_60 : ThresholdAt 23 60 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 60 0 cell_23_60_0
  | exact S 23 60 1 cell_23_60_1
  | exact S 23 60 2 cell_23_60_2
  | exact S 23 60 3 cell_23_60_3
  | exact S 23 60 4 cell_23_60_4
  | exact S 23 60 5 cell_23_60_5
theorem cell_23_61_0 : C 23 61 0 := by decide +kernel
theorem cell_23_61_1 : C 23 61 1 := by decide +kernel
theorem cell_23_61_2 : C 23 61 2 := by decide +kernel
theorem cell_23_61_3 : C 23 61 3 := by decide +kernel
theorem cell_23_61_4 : C 23 61 4 := by decide +kernel
theorem cell_23_61_5 : C 23 61 5 := by decide +kernel
theorem row_23_61 : ThresholdAt 23 61 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 61 0 cell_23_61_0
  | exact S 23 61 1 cell_23_61_1
  | exact S 23 61 2 cell_23_61_2
  | exact S 23 61 3 cell_23_61_3
  | exact S 23 61 4 cell_23_61_4
  | exact S 23 61 5 cell_23_61_5
theorem cell_23_62_0 : C 23 62 0 := by decide +kernel
theorem cell_23_62_1 : C 23 62 1 := by decide +kernel
theorem cell_23_62_2 : C 23 62 2 := by decide +kernel
theorem cell_23_62_3 : C 23 62 3 := by decide +kernel
theorem cell_23_62_4 : C 23 62 4 := by decide +kernel
theorem cell_23_62_5 : C 23 62 5 := by decide +kernel
theorem row_23_62 : ThresholdAt 23 62 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 62 0 cell_23_62_0
  | exact S 23 62 1 cell_23_62_1
  | exact S 23 62 2 cell_23_62_2
  | exact S 23 62 3 cell_23_62_3
  | exact S 23 62 4 cell_23_62_4
  | exact S 23 62 5 cell_23_62_5
theorem cell_23_63_0 : C 23 63 0 := by decide +kernel
theorem cell_23_63_1 : C 23 63 1 := by decide +kernel
theorem cell_23_63_2 : C 23 63 2 := by decide +kernel
theorem cell_23_63_3 : C 23 63 3 := by decide +kernel
theorem cell_23_63_4 : C 23 63 4 := by decide +kernel
theorem cell_23_63_5 : C 23 63 5 := by decide +kernel
theorem row_23_63 : ThresholdAt 23 63 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 63 0 cell_23_63_0
  | exact S 23 63 1 cell_23_63_1
  | exact S 23 63 2 cell_23_63_2
  | exact S 23 63 3 cell_23_63_3
  | exact S 23 63 4 cell_23_63_4
  | exact S 23 63 5 cell_23_63_5
theorem cell_23_64_0 : C 23 64 0 := by decide +kernel
theorem cell_23_64_1 : C 23 64 1 := by decide +kernel
theorem cell_23_64_2 : C 23 64 2 := by decide +kernel
theorem cell_23_64_3 : C 23 64 3 := by decide +kernel
theorem cell_23_64_4 : C 23 64 4 := by decide +kernel
theorem cell_23_64_5 : C 23 64 5 := by decide +kernel
theorem row_23_64 : ThresholdAt 23 64 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 64 0 cell_23_64_0
  | exact S 23 64 1 cell_23_64_1
  | exact S 23 64 2 cell_23_64_2
  | exact S 23 64 3 cell_23_64_3
  | exact S 23 64 4 cell_23_64_4
  | exact S 23 64 5 cell_23_64_5
theorem cell_23_65_0 : C 23 65 0 := by decide +kernel
theorem cell_23_65_1 : C 23 65 1 := by decide +kernel
theorem cell_23_65_2 : C 23 65 2 := by decide +kernel
theorem cell_23_65_3 : C 23 65 3 := by decide +kernel
theorem cell_23_65_4 : C 23 65 4 := by decide +kernel
theorem cell_23_65_5 : C 23 65 5 := by decide +kernel
theorem row_23_65 : ThresholdAt 23 65 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 65 0 cell_23_65_0
  | exact S 23 65 1 cell_23_65_1
  | exact S 23 65 2 cell_23_65_2
  | exact S 23 65 3 cell_23_65_3
  | exact S 23 65 4 cell_23_65_4
  | exact S 23 65 5 cell_23_65_5
theorem cell_23_66_0 : C 23 66 0 := by decide +kernel
theorem cell_23_66_1 : C 23 66 1 := by decide +kernel
theorem cell_23_66_2 : C 23 66 2 := by decide +kernel
theorem cell_23_66_3 : C 23 66 3 := by decide +kernel
theorem cell_23_66_4 : C 23 66 4 := by decide +kernel
theorem cell_23_66_5 : C 23 66 5 := by decide +kernel
theorem row_23_66 : ThresholdAt 23 66 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 66 0 cell_23_66_0
  | exact S 23 66 1 cell_23_66_1
  | exact S 23 66 2 cell_23_66_2
  | exact S 23 66 3 cell_23_66_3
  | exact S 23 66 4 cell_23_66_4
  | exact S 23 66 5 cell_23_66_5
theorem cell_23_67_0 : C 23 67 0 := by decide +kernel
theorem cell_23_67_1 : C 23 67 1 := by decide +kernel
theorem cell_23_67_2 : C 23 67 2 := by decide +kernel
theorem cell_23_67_3 : C 23 67 3 := by decide +kernel
theorem cell_23_67_4 : C 23 67 4 := by decide +kernel
theorem cell_23_67_5 : C 23 67 5 := by decide +kernel
theorem row_23_67 : ThresholdAt 23 67 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 67 0 cell_23_67_0
  | exact S 23 67 1 cell_23_67_1
  | exact S 23 67 2 cell_23_67_2
  | exact S 23 67 3 cell_23_67_3
  | exact S 23 67 4 cell_23_67_4
  | exact S 23 67 5 cell_23_67_5
theorem cell_23_68_0 : C 23 68 0 := by decide +kernel
theorem cell_23_68_1 : C 23 68 1 := by decide +kernel
theorem cell_23_68_2 : C 23 68 2 := by decide +kernel
theorem cell_23_68_3 : C 23 68 3 := by decide +kernel
theorem cell_23_68_4 : C 23 68 4 := by decide +kernel
theorem cell_23_68_5 : C 23 68 5 := by decide +kernel
theorem row_23_68 : ThresholdAt 23 68 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 68 0 cell_23_68_0
  | exact S 23 68 1 cell_23_68_1
  | exact S 23 68 2 cell_23_68_2
  | exact S 23 68 3 cell_23_68_3
  | exact S 23 68 4 cell_23_68_4
  | exact S 23 68 5 cell_23_68_5
theorem cell_23_69_0 : C 23 69 0 := by decide +kernel
theorem cell_23_69_1 : C 23 69 1 := by decide +kernel
theorem cell_23_69_2 : C 23 69 2 := by decide +kernel
theorem cell_23_69_3 : C 23 69 3 := by decide +kernel
theorem cell_23_69_4 : C 23 69 4 := by decide +kernel
theorem cell_23_69_5 : C 23 69 5 := by decide +kernel
theorem row_23_69 : ThresholdAt 23 69 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 69 0 cell_23_69_0
  | exact S 23 69 1 cell_23_69_1
  | exact S 23 69 2 cell_23_69_2
  | exact S 23 69 3 cell_23_69_3
  | exact S 23 69 4 cell_23_69_4
  | exact S 23 69 5 cell_23_69_5
theorem cell_23_70_0 : C 23 70 0 := by decide +kernel
theorem cell_23_70_1 : C 23 70 1 := by decide +kernel
theorem cell_23_70_2 : C 23 70 2 := by decide +kernel
theorem cell_23_70_3 : C 23 70 3 := by decide +kernel
theorem cell_23_70_4 : C 23 70 4 := by decide +kernel
theorem cell_23_70_5 : C 23 70 5 := by decide +kernel
theorem row_23_70 : ThresholdAt 23 70 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 70 0 cell_23_70_0
  | exact S 23 70 1 cell_23_70_1
  | exact S 23 70 2 cell_23_70_2
  | exact S 23 70 3 cell_23_70_3
  | exact S 23 70 4 cell_23_70_4
  | exact S 23 70 5 cell_23_70_5
theorem cell_23_71_0 : C 23 71 0 := by decide +kernel
theorem cell_23_71_1 : C 23 71 1 := by decide +kernel
theorem cell_23_71_2 : C 23 71 2 := by decide +kernel
theorem cell_23_71_3 : C 23 71 3 := by decide +kernel
theorem cell_23_71_4 : C 23 71 4 := by decide +kernel
theorem cell_23_71_5 : C 23 71 5 := by decide +kernel
theorem row_23_71 : ThresholdAt 23 71 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 71 0 cell_23_71_0
  | exact S 23 71 1 cell_23_71_1
  | exact S 23 71 2 cell_23_71_2
  | exact S 23 71 3 cell_23_71_3
  | exact S 23 71 4 cell_23_71_4
  | exact S 23 71 5 cell_23_71_5
theorem cell_23_72_0 : C 23 72 0 := by decide +kernel
theorem cell_23_72_1 : C 23 72 1 := by decide +kernel
theorem cell_23_72_2 : C 23 72 2 := by decide +kernel
theorem cell_23_72_3 : C 23 72 3 := by decide +kernel
theorem cell_23_72_4 : C 23 72 4 := by decide +kernel
theorem cell_23_72_5 : C 23 72 5 := by decide +kernel
theorem row_23_72 : ThresholdAt 23 72 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 72 0 cell_23_72_0
  | exact S 23 72 1 cell_23_72_1
  | exact S 23 72 2 cell_23_72_2
  | exact S 23 72 3 cell_23_72_3
  | exact S 23 72 4 cell_23_72_4
  | exact S 23 72 5 cell_23_72_5
theorem cell_23_73_0 : C 23 73 0 := by decide +kernel
theorem cell_23_73_1 : C 23 73 1 := by decide +kernel
theorem cell_23_73_2 : C 23 73 2 := by decide +kernel
theorem cell_23_73_3 : C 23 73 3 := by decide +kernel
theorem cell_23_73_4 : C 23 73 4 := by decide +kernel
theorem cell_23_73_5 : C 23 73 5 := by decide +kernel
theorem row_23_73 : ThresholdAt 23 73 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 73 0 cell_23_73_0
  | exact S 23 73 1 cell_23_73_1
  | exact S 23 73 2 cell_23_73_2
  | exact S 23 73 3 cell_23_73_3
  | exact S 23 73 4 cell_23_73_4
  | exact S 23 73 5 cell_23_73_5
theorem cell_23_74_0 : C 23 74 0 := by decide +kernel
theorem cell_23_74_1 : C 23 74 1 := by decide +kernel
theorem cell_23_74_2 : C 23 74 2 := by decide +kernel
theorem cell_23_74_3 : C 23 74 3 := by decide +kernel
theorem cell_23_74_4 : C 23 74 4 := by decide +kernel
theorem cell_23_74_5 : C 23 74 5 := by decide +kernel
theorem row_23_74 : ThresholdAt 23 74 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 74 0 cell_23_74_0
  | exact S 23 74 1 cell_23_74_1
  | exact S 23 74 2 cell_23_74_2
  | exact S 23 74 3 cell_23_74_3
  | exact S 23 74 4 cell_23_74_4
  | exact S 23 74 5 cell_23_74_5
theorem cell_23_75_0 : C 23 75 0 := by decide +kernel
theorem cell_23_75_1 : C 23 75 1 := by decide +kernel
theorem cell_23_75_2 : C 23 75 2 := by decide +kernel
theorem cell_23_75_3 : C 23 75 3 := by decide +kernel
theorem cell_23_75_4 : C 23 75 4 := by decide +kernel
theorem cell_23_75_5 : C 23 75 5 := by decide +kernel
theorem row_23_75 : ThresholdAt 23 75 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 75 0 cell_23_75_0
  | exact S 23 75 1 cell_23_75_1
  | exact S 23 75 2 cell_23_75_2
  | exact S 23 75 3 cell_23_75_3
  | exact S 23 75 4 cell_23_75_4
  | exact S 23 75 5 cell_23_75_5
theorem cell_23_76_0 : C 23 76 0 := by decide +kernel
theorem cell_23_76_1 : C 23 76 1 := by decide +kernel
theorem cell_23_76_2 : C 23 76 2 := by decide +kernel
theorem cell_23_76_3 : C 23 76 3 := by decide +kernel
theorem cell_23_76_4 : C 23 76 4 := by decide +kernel
theorem cell_23_76_5 : C 23 76 5 := by decide +kernel
theorem row_23_76 : ThresholdAt 23 76 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 76 0 cell_23_76_0
  | exact S 23 76 1 cell_23_76_1
  | exact S 23 76 2 cell_23_76_2
  | exact S 23 76 3 cell_23_76_3
  | exact S 23 76 4 cell_23_76_4
  | exact S 23 76 5 cell_23_76_5
theorem cell_23_77_0 : C 23 77 0 := by decide +kernel
theorem cell_23_77_1 : C 23 77 1 := by decide +kernel
theorem cell_23_77_2 : C 23 77 2 := by decide +kernel
theorem cell_23_77_3 : C 23 77 3 := by decide +kernel
theorem cell_23_77_4 : C 23 77 4 := by decide +kernel
theorem cell_23_77_5 : C 23 77 5 := by decide +kernel
theorem row_23_77 : ThresholdAt 23 77 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 77 0 cell_23_77_0
  | exact S 23 77 1 cell_23_77_1
  | exact S 23 77 2 cell_23_77_2
  | exact S 23 77 3 cell_23_77_3
  | exact S 23 77 4 cell_23_77_4
  | exact S 23 77 5 cell_23_77_5
theorem cell_23_78_0 : C 23 78 0 := by decide +kernel
theorem cell_23_78_1 : C 23 78 1 := by decide +kernel
theorem cell_23_78_2 : C 23 78 2 := by decide +kernel
theorem cell_23_78_3 : C 23 78 3 := by decide +kernel
theorem cell_23_78_4 : C 23 78 4 := by decide +kernel
theorem cell_23_78_5 : C 23 78 5 := by decide +kernel
theorem row_23_78 : ThresholdAt 23 78 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 78 0 cell_23_78_0
  | exact S 23 78 1 cell_23_78_1
  | exact S 23 78 2 cell_23_78_2
  | exact S 23 78 3 cell_23_78_3
  | exact S 23 78 4 cell_23_78_4
  | exact S 23 78 5 cell_23_78_5
theorem cell_23_79_0 : C 23 79 0 := by decide +kernel
theorem cell_23_79_1 : C 23 79 1 := by decide +kernel
theorem cell_23_79_2 : C 23 79 2 := by decide +kernel
theorem cell_23_79_3 : C 23 79 3 := by decide +kernel
theorem cell_23_79_4 : C 23 79 4 := by decide +kernel
theorem cell_23_79_5 : C 23 79 5 := by decide +kernel
theorem row_23_79 : ThresholdAt 23 79 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 79 0 cell_23_79_0
  | exact S 23 79 1 cell_23_79_1
  | exact S 23 79 2 cell_23_79_2
  | exact S 23 79 3 cell_23_79_3
  | exact S 23 79 4 cell_23_79_4
  | exact S 23 79 5 cell_23_79_5
theorem cell_23_80_0 : C 23 80 0 := by decide +kernel
theorem cell_23_80_1 : C 23 80 1 := by decide +kernel
theorem cell_23_80_2 : C 23 80 2 := by decide +kernel
theorem cell_23_80_3 : C 23 80 3 := by decide +kernel
theorem cell_23_80_4 : C 23 80 4 := by decide +kernel
theorem cell_23_80_5 : C 23 80 5 := by decide +kernel
theorem row_23_80 : ThresholdAt 23 80 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 80 0 cell_23_80_0
  | exact S 23 80 1 cell_23_80_1
  | exact S 23 80 2 cell_23_80_2
  | exact S 23 80 3 cell_23_80_3
  | exact S 23 80 4 cell_23_80_4
  | exact S 23 80 5 cell_23_80_5
theorem cell_23_81_0 : C 23 81 0 := by decide +kernel
theorem cell_23_81_1 : C 23 81 1 := by decide +kernel
theorem cell_23_81_2 : C 23 81 2 := by decide +kernel
theorem cell_23_81_3 : C 23 81 3 := by decide +kernel
theorem cell_23_81_4 : C 23 81 4 := by decide +kernel
theorem cell_23_81_5 : C 23 81 5 := by decide +kernel
theorem row_23_81 : ThresholdAt 23 81 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 81 0 cell_23_81_0
  | exact S 23 81 1 cell_23_81_1
  | exact S 23 81 2 cell_23_81_2
  | exact S 23 81 3 cell_23_81_3
  | exact S 23 81 4 cell_23_81_4
  | exact S 23 81 5 cell_23_81_5
theorem cell_23_82_0 : C 23 82 0 := by decide +kernel
theorem cell_23_82_1 : C 23 82 1 := by decide +kernel
theorem cell_23_82_2 : C 23 82 2 := by decide +kernel
theorem cell_23_82_3 : C 23 82 3 := by decide +kernel
theorem cell_23_82_4 : C 23 82 4 := by decide +kernel
theorem cell_23_82_5 : C 23 82 5 := by decide +kernel
theorem row_23_82 : ThresholdAt 23 82 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 82 0 cell_23_82_0
  | exact S 23 82 1 cell_23_82_1
  | exact S 23 82 2 cell_23_82_2
  | exact S 23 82 3 cell_23_82_3
  | exact S 23 82 4 cell_23_82_4
  | exact S 23 82 5 cell_23_82_5
theorem cell_23_83_0 : C 23 83 0 := by decide +kernel
theorem cell_23_83_1 : C 23 83 1 := by decide +kernel
theorem cell_23_83_2 : C 23 83 2 := by decide +kernel
theorem cell_23_83_3 : C 23 83 3 := by decide +kernel
theorem cell_23_83_4 : C 23 83 4 := by decide +kernel
theorem cell_23_83_5 : C 23 83 5 := by decide +kernel
theorem row_23_83 : ThresholdAt 23 83 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 83 0 cell_23_83_0
  | exact S 23 83 1 cell_23_83_1
  | exact S 23 83 2 cell_23_83_2
  | exact S 23 83 3 cell_23_83_3
  | exact S 23 83 4 cell_23_83_4
  | exact S 23 83 5 cell_23_83_5
theorem cell_23_84_0 : C 23 84 0 := by decide +kernel
theorem cell_23_84_1 : C 23 84 1 := by decide +kernel
theorem cell_23_84_2 : C 23 84 2 := by decide +kernel
theorem cell_23_84_3 : C 23 84 3 := by decide +kernel
theorem cell_23_84_4 : C 23 84 4 := by decide +kernel
theorem cell_23_84_5 : C 23 84 5 := by decide +kernel
theorem row_23_84 : ThresholdAt 23 84 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 84 0 cell_23_84_0
  | exact S 23 84 1 cell_23_84_1
  | exact S 23 84 2 cell_23_84_2
  | exact S 23 84 3 cell_23_84_3
  | exact S 23 84 4 cell_23_84_4
  | exact S 23 84 5 cell_23_84_5
theorem cell_23_85_0 : C 23 85 0 := by decide +kernel
theorem cell_23_85_1 : C 23 85 1 := by decide +kernel
theorem cell_23_85_2 : C 23 85 2 := by decide +kernel
theorem cell_23_85_3 : C 23 85 3 := by decide +kernel
theorem cell_23_85_4 : C 23 85 4 := by decide +kernel
theorem cell_23_85_5 : C 23 85 5 := by decide +kernel
theorem row_23_85 : ThresholdAt 23 85 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 85 0 cell_23_85_0
  | exact S 23 85 1 cell_23_85_1
  | exact S 23 85 2 cell_23_85_2
  | exact S 23 85 3 cell_23_85_3
  | exact S 23 85 4 cell_23_85_4
  | exact S 23 85 5 cell_23_85_5
theorem cell_23_86_0 : C 23 86 0 := by decide +kernel
theorem cell_23_86_1 : C 23 86 1 := by decide +kernel
theorem cell_23_86_2 : C 23 86 2 := by decide +kernel
theorem cell_23_86_3 : C 23 86 3 := by decide +kernel
theorem cell_23_86_4 : C 23 86 4 := by decide +kernel
theorem cell_23_86_5 : C 23 86 5 := by decide +kernel
theorem row_23_86 : ThresholdAt 23 86 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 86 0 cell_23_86_0
  | exact S 23 86 1 cell_23_86_1
  | exact S 23 86 2 cell_23_86_2
  | exact S 23 86 3 cell_23_86_3
  | exact S 23 86 4 cell_23_86_4
  | exact S 23 86 5 cell_23_86_5
theorem cell_23_87_0 : C 23 87 0 := by decide +kernel
theorem cell_23_87_1 : C 23 87 1 := by decide +kernel
theorem cell_23_87_2 : C 23 87 2 := by decide +kernel
theorem cell_23_87_3 : C 23 87 3 := by decide +kernel
theorem cell_23_87_4 : C 23 87 4 := by decide +kernel
theorem cell_23_87_5 : C 23 87 5 := by decide +kernel
theorem row_23_87 : ThresholdAt 23 87 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 87 0 cell_23_87_0
  | exact S 23 87 1 cell_23_87_1
  | exact S 23 87 2 cell_23_87_2
  | exact S 23 87 3 cell_23_87_3
  | exact S 23 87 4 cell_23_87_4
  | exact S 23 87 5 cell_23_87_5
theorem cell_23_88_0 : C 23 88 0 := by decide +kernel
theorem cell_23_88_1 : C 23 88 1 := by decide +kernel
theorem cell_23_88_2 : C 23 88 2 := by decide +kernel
theorem cell_23_88_3 : C 23 88 3 := by decide +kernel
theorem cell_23_88_4 : C 23 88 4 := by decide +kernel
theorem cell_23_88_5 : C 23 88 5 := by decide +kernel
theorem row_23_88 : ThresholdAt 23 88 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 88 0 cell_23_88_0
  | exact S 23 88 1 cell_23_88_1
  | exact S 23 88 2 cell_23_88_2
  | exact S 23 88 3 cell_23_88_3
  | exact S 23 88 4 cell_23_88_4
  | exact S 23 88 5 cell_23_88_5
theorem cell_23_89_0 : C 23 89 0 := by decide +kernel
theorem cell_23_89_1 : C 23 89 1 := by decide +kernel
theorem cell_23_89_2 : C 23 89 2 := by decide +kernel
theorem cell_23_89_3 : C 23 89 3 := by decide +kernel
theorem cell_23_89_4 : C 23 89 4 := by decide +kernel
theorem cell_23_89_5 : C 23 89 5 := by decide +kernel
theorem row_23_89 : ThresholdAt 23 89 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 89 0 cell_23_89_0
  | exact S 23 89 1 cell_23_89_1
  | exact S 23 89 2 cell_23_89_2
  | exact S 23 89 3 cell_23_89_3
  | exact S 23 89 4 cell_23_89_4
  | exact S 23 89 5 cell_23_89_5
theorem cell_23_90_0 : C 23 90 0 := by decide +kernel
theorem cell_23_90_1 : C 23 90 1 := by decide +kernel
theorem cell_23_90_2 : C 23 90 2 := by decide +kernel
theorem cell_23_90_3 : C 23 90 3 := by decide +kernel
theorem cell_23_90_4 : C 23 90 4 := by decide +kernel
theorem cell_23_90_5 : C 23 90 5 := by decide +kernel
theorem row_23_90 : ThresholdAt 23 90 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 90 0 cell_23_90_0
  | exact S 23 90 1 cell_23_90_1
  | exact S 23 90 2 cell_23_90_2
  | exact S 23 90 3 cell_23_90_3
  | exact S 23 90 4 cell_23_90_4
  | exact S 23 90 5 cell_23_90_5
theorem cell_23_91_0 : C 23 91 0 := by decide +kernel
theorem cell_23_91_1 : C 23 91 1 := by decide +kernel
theorem cell_23_91_2 : C 23 91 2 := by decide +kernel
theorem cell_23_91_3 : C 23 91 3 := by decide +kernel
theorem cell_23_91_4 : C 23 91 4 := by decide +kernel
theorem cell_23_91_5 : C 23 91 5 := by decide +kernel
theorem row_23_91 : ThresholdAt 23 91 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 91 0 cell_23_91_0
  | exact S 23 91 1 cell_23_91_1
  | exact S 23 91 2 cell_23_91_2
  | exact S 23 91 3 cell_23_91_3
  | exact S 23 91 4 cell_23_91_4
  | exact S 23 91 5 cell_23_91_5
theorem cell_23_92_0 : C 23 92 0 := by decide +kernel
theorem cell_23_92_1 : C 23 92 1 := by decide +kernel
theorem cell_23_92_2 : C 23 92 2 := by decide +kernel
theorem cell_23_92_3 : C 23 92 3 := by decide +kernel
theorem cell_23_92_4 : C 23 92 4 := by decide +kernel
theorem cell_23_92_5 : C 23 92 5 := by decide +kernel
theorem row_23_92 : ThresholdAt 23 92 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 92 0 cell_23_92_0
  | exact S 23 92 1 cell_23_92_1
  | exact S 23 92 2 cell_23_92_2
  | exact S 23 92 3 cell_23_92_3
  | exact S 23 92 4 cell_23_92_4
  | exact S 23 92 5 cell_23_92_5
theorem cell_23_93_0 : C 23 93 0 := by decide +kernel
theorem cell_23_93_1 : C 23 93 1 := by decide +kernel
theorem cell_23_93_2 : C 23 93 2 := by decide +kernel
theorem cell_23_93_3 : C 23 93 3 := by decide +kernel
theorem cell_23_93_4 : C 23 93 4 := by decide +kernel
theorem cell_23_93_5 : C 23 93 5 := by decide +kernel
theorem row_23_93 : ThresholdAt 23 93 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 93 0 cell_23_93_0
  | exact S 23 93 1 cell_23_93_1
  | exact S 23 93 2 cell_23_93_2
  | exact S 23 93 3 cell_23_93_3
  | exact S 23 93 4 cell_23_93_4
  | exact S 23 93 5 cell_23_93_5
theorem cell_23_94_0 : C 23 94 0 := by decide +kernel
theorem cell_23_94_1 : C 23 94 1 := by decide +kernel
theorem cell_23_94_2 : C 23 94 2 := by decide +kernel
theorem cell_23_94_3 : C 23 94 3 := by decide +kernel
theorem cell_23_94_4 : C 23 94 4 := by decide +kernel
theorem cell_23_94_5 : C 23 94 5 := by decide +kernel
theorem row_23_94 : ThresholdAt 23 94 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 94 0 cell_23_94_0
  | exact S 23 94 1 cell_23_94_1
  | exact S 23 94 2 cell_23_94_2
  | exact S 23 94 3 cell_23_94_3
  | exact S 23 94 4 cell_23_94_4
  | exact S 23 94 5 cell_23_94_5
theorem cell_23_95_0 : C 23 95 0 := by decide +kernel
theorem cell_23_95_1 : C 23 95 1 := by decide +kernel
theorem cell_23_95_2 : C 23 95 2 := by decide +kernel
theorem cell_23_95_3 : C 23 95 3 := by decide +kernel
theorem cell_23_95_4 : C 23 95 4 := by decide +kernel
theorem cell_23_95_5 : C 23 95 5 := by decide +kernel
theorem row_23_95 : ThresholdAt 23 95 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 95 0 cell_23_95_0
  | exact S 23 95 1 cell_23_95_1
  | exact S 23 95 2 cell_23_95_2
  | exact S 23 95 3 cell_23_95_3
  | exact S 23 95 4 cell_23_95_4
  | exact S 23 95 5 cell_23_95_5
theorem cell_23_96_0 : C 23 96 0 := by decide +kernel
theorem cell_23_96_1 : C 23 96 1 := by decide +kernel
theorem cell_23_96_2 : C 23 96 2 := by decide +kernel
theorem cell_23_96_3 : C 23 96 3 := by decide +kernel
theorem cell_23_96_4 : C 23 96 4 := by decide +kernel
theorem cell_23_96_5 : C 23 96 5 := by decide +kernel
theorem row_23_96 : ThresholdAt 23 96 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 96 0 cell_23_96_0
  | exact S 23 96 1 cell_23_96_1
  | exact S 23 96 2 cell_23_96_2
  | exact S 23 96 3 cell_23_96_3
  | exact S 23 96 4 cell_23_96_4
  | exact S 23 96 5 cell_23_96_5
theorem cell_23_97_0 : C 23 97 0 := by decide +kernel
theorem cell_23_97_1 : C 23 97 1 := by decide +kernel
theorem cell_23_97_2 : C 23 97 2 := by decide +kernel
theorem cell_23_97_3 : C 23 97 3 := by decide +kernel
theorem cell_23_97_4 : C 23 97 4 := by decide +kernel
theorem cell_23_97_5 : C 23 97 5 := by decide +kernel
theorem row_23_97 : ThresholdAt 23 97 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 97 0 cell_23_97_0
  | exact S 23 97 1 cell_23_97_1
  | exact S 23 97 2 cell_23_97_2
  | exact S 23 97 3 cell_23_97_3
  | exact S 23 97 4 cell_23_97_4
  | exact S 23 97 5 cell_23_97_5
theorem cell_23_98_0 : C 23 98 0 := by decide +kernel
theorem cell_23_98_1 : C 23 98 1 := by decide +kernel
theorem cell_23_98_2 : C 23 98 2 := by decide +kernel
theorem cell_23_98_3 : C 23 98 3 := by decide +kernel
theorem cell_23_98_4 : C 23 98 4 := by decide +kernel
theorem cell_23_98_5 : C 23 98 5 := by decide +kernel
theorem row_23_98 : ThresholdAt 23 98 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 98 0 cell_23_98_0
  | exact S 23 98 1 cell_23_98_1
  | exact S 23 98 2 cell_23_98_2
  | exact S 23 98 3 cell_23_98_3
  | exact S 23 98 4 cell_23_98_4
  | exact S 23 98 5 cell_23_98_5
theorem cell_23_99_0 : C 23 99 0 := by decide +kernel
theorem cell_23_99_1 : C 23 99 1 := by decide +kernel
theorem cell_23_99_2 : C 23 99 2 := by decide +kernel
theorem cell_23_99_3 : C 23 99 3 := by decide +kernel
theorem cell_23_99_4 : C 23 99 4 := by decide +kernel
theorem cell_23_99_5 : C 23 99 5 := by decide +kernel
theorem row_23_99 : ThresholdAt 23 99 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 99 0 cell_23_99_0
  | exact S 23 99 1 cell_23_99_1
  | exact S 23 99 2 cell_23_99_2
  | exact S 23 99 3 cell_23_99_3
  | exact S 23 99 4 cell_23_99_4
  | exact S 23 99 5 cell_23_99_5
theorem cell_23_100_0 : C 23 100 0 := by decide +kernel
theorem cell_23_100_1 : C 23 100 1 := by decide +kernel
theorem cell_23_100_2 : C 23 100 2 := by decide +kernel
theorem cell_23_100_3 : C 23 100 3 := by decide +kernel
theorem cell_23_100_4 : C 23 100 4 := by decide +kernel
theorem cell_23_100_5 : C 23 100 5 := by decide +kernel
theorem row_23_100 : ThresholdAt 23 100 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 100 0 cell_23_100_0
  | exact S 23 100 1 cell_23_100_1
  | exact S 23 100 2 cell_23_100_2
  | exact S 23 100 3 cell_23_100_3
  | exact S 23 100 4 cell_23_100_4
  | exact S 23 100 5 cell_23_100_5
theorem cell_23_101_0 : C 23 101 0 := by decide +kernel
theorem cell_23_101_1 : C 23 101 1 := by decide +kernel
theorem cell_23_101_2 : C 23 101 2 := by decide +kernel
theorem cell_23_101_3 : C 23 101 3 := by decide +kernel
theorem cell_23_101_4 : C 23 101 4 := by decide +kernel
theorem cell_23_101_5 : C 23 101 5 := by decide +kernel
theorem row_23_101 : ThresholdAt 23 101 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 101 0 cell_23_101_0
  | exact S 23 101 1 cell_23_101_1
  | exact S 23 101 2 cell_23_101_2
  | exact S 23 101 3 cell_23_101_3
  | exact S 23 101 4 cell_23_101_4
  | exact S 23 101 5 cell_23_101_5
theorem cell_23_102_0 : C 23 102 0 := by decide +kernel
theorem cell_23_102_1 : C 23 102 1 := by decide +kernel
theorem cell_23_102_2 : C 23 102 2 := by decide +kernel
theorem cell_23_102_3 : C 23 102 3 := by decide +kernel
theorem cell_23_102_4 : C 23 102 4 := by decide +kernel
theorem cell_23_102_5 : C 23 102 5 := by decide +kernel
theorem row_23_102 : ThresholdAt 23 102 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 102 0 cell_23_102_0
  | exact S 23 102 1 cell_23_102_1
  | exact S 23 102 2 cell_23_102_2
  | exact S 23 102 3 cell_23_102_3
  | exact S 23 102 4 cell_23_102_4
  | exact S 23 102 5 cell_23_102_5
theorem cell_23_103_0 : C 23 103 0 := by decide +kernel
theorem cell_23_103_1 : C 23 103 1 := by decide +kernel
theorem cell_23_103_2 : C 23 103 2 := by decide +kernel
theorem cell_23_103_3 : C 23 103 3 := by decide +kernel
theorem cell_23_103_4 : C 23 103 4 := by decide +kernel
theorem cell_23_103_5 : C 23 103 5 := by decide +kernel
theorem row_23_103 : ThresholdAt 23 103 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 103 0 cell_23_103_0
  | exact S 23 103 1 cell_23_103_1
  | exact S 23 103 2 cell_23_103_2
  | exact S 23 103 3 cell_23_103_3
  | exact S 23 103 4 cell_23_103_4
  | exact S 23 103 5 cell_23_103_5
theorem cell_23_104_0 : C 23 104 0 := by decide +kernel
theorem cell_23_104_1 : C 23 104 1 := by decide +kernel
theorem cell_23_104_2 : C 23 104 2 := by decide +kernel
theorem cell_23_104_3 : C 23 104 3 := by decide +kernel
theorem cell_23_104_4 : C 23 104 4 := by decide +kernel
theorem cell_23_104_5 : C 23 104 5 := by decide +kernel
theorem row_23_104 : ThresholdAt 23 104 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 104 0 cell_23_104_0
  | exact S 23 104 1 cell_23_104_1
  | exact S 23 104 2 cell_23_104_2
  | exact S 23 104 3 cell_23_104_3
  | exact S 23 104 4 cell_23_104_4
  | exact S 23 104 5 cell_23_104_5
theorem cell_23_105_0 : C 23 105 0 := by decide +kernel
theorem cell_23_105_1 : C 23 105 1 := by decide +kernel
theorem cell_23_105_2 : C 23 105 2 := by decide +kernel
theorem cell_23_105_3 : C 23 105 3 := by decide +kernel
theorem cell_23_105_4 : C 23 105 4 := by decide +kernel
theorem cell_23_105_5 : C 23 105 5 := by decide +kernel
theorem row_23_105 : ThresholdAt 23 105 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 105 0 cell_23_105_0
  | exact S 23 105 1 cell_23_105_1
  | exact S 23 105 2 cell_23_105_2
  | exact S 23 105 3 cell_23_105_3
  | exact S 23 105 4 cell_23_105_4
  | exact S 23 105 5 cell_23_105_5
theorem cell_23_106_0 : C 23 106 0 := by decide +kernel
theorem cell_23_106_1 : C 23 106 1 := by decide +kernel
theorem cell_23_106_2 : C 23 106 2 := by decide +kernel
theorem cell_23_106_3 : C 23 106 3 := by decide +kernel
theorem cell_23_106_4 : C 23 106 4 := by decide +kernel
theorem cell_23_106_5 : C 23 106 5 := by decide +kernel
theorem row_23_106 : ThresholdAt 23 106 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 106 0 cell_23_106_0
  | exact S 23 106 1 cell_23_106_1
  | exact S 23 106 2 cell_23_106_2
  | exact S 23 106 3 cell_23_106_3
  | exact S 23 106 4 cell_23_106_4
  | exact S 23 106 5 cell_23_106_5
theorem cell_23_107_0 : C 23 107 0 := by decide +kernel
theorem cell_23_107_1 : C 23 107 1 := by decide +kernel
theorem cell_23_107_2 : C 23 107 2 := by decide +kernel
theorem cell_23_107_3 : C 23 107 3 := by decide +kernel
theorem cell_23_107_4 : C 23 107 4 := by decide +kernel
theorem cell_23_107_5 : C 23 107 5 := by decide +kernel
theorem row_23_107 : ThresholdAt 23 107 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 107 0 cell_23_107_0
  | exact S 23 107 1 cell_23_107_1
  | exact S 23 107 2 cell_23_107_2
  | exact S 23 107 3 cell_23_107_3
  | exact S 23 107 4 cell_23_107_4
  | exact S 23 107 5 cell_23_107_5
theorem cell_23_108_0 : C 23 108 0 := by decide +kernel
theorem cell_23_108_1 : C 23 108 1 := by decide +kernel
theorem cell_23_108_2 : C 23 108 2 := by decide +kernel
theorem cell_23_108_3 : C 23 108 3 := by decide +kernel
theorem cell_23_108_4 : C 23 108 4 := by decide +kernel
theorem cell_23_108_5 : C 23 108 5 := by decide +kernel
theorem row_23_108 : ThresholdAt 23 108 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 108 0 cell_23_108_0
  | exact S 23 108 1 cell_23_108_1
  | exact S 23 108 2 cell_23_108_2
  | exact S 23 108 3 cell_23_108_3
  | exact S 23 108 4 cell_23_108_4
  | exact S 23 108 5 cell_23_108_5
theorem cell_23_109_0 : C 23 109 0 := by decide +kernel
theorem cell_23_109_1 : C 23 109 1 := by decide +kernel
theorem cell_23_109_2 : C 23 109 2 := by decide +kernel
theorem cell_23_109_3 : C 23 109 3 := by decide +kernel
theorem cell_23_109_4 : C 23 109 4 := by decide +kernel
theorem cell_23_109_5 : C 23 109 5 := by decide +kernel
theorem row_23_109 : ThresholdAt 23 109 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 109 0 cell_23_109_0
  | exact S 23 109 1 cell_23_109_1
  | exact S 23 109 2 cell_23_109_2
  | exact S 23 109 3 cell_23_109_3
  | exact S 23 109 4 cell_23_109_4
  | exact S 23 109 5 cell_23_109_5
theorem cell_23_110_0 : C 23 110 0 := by decide +kernel
theorem cell_23_110_1 : C 23 110 1 := by decide +kernel
theorem cell_23_110_2 : C 23 110 2 := by decide +kernel
theorem cell_23_110_3 : C 23 110 3 := by decide +kernel
theorem cell_23_110_4 : C 23 110 4 := by decide +kernel
theorem cell_23_110_5 : C 23 110 5 := by decide +kernel
theorem row_23_110 : ThresholdAt 23 110 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 110 0 cell_23_110_0
  | exact S 23 110 1 cell_23_110_1
  | exact S 23 110 2 cell_23_110_2
  | exact S 23 110 3 cell_23_110_3
  | exact S 23 110 4 cell_23_110_4
  | exact S 23 110 5 cell_23_110_5
theorem cell_23_111_0 : C 23 111 0 := by decide +kernel
theorem cell_23_111_1 : C 23 111 1 := by decide +kernel
theorem cell_23_111_2 : C 23 111 2 := by decide +kernel
theorem cell_23_111_3 : C 23 111 3 := by decide +kernel
theorem cell_23_111_4 : C 23 111 4 := by decide +kernel
theorem cell_23_111_5 : C 23 111 5 := by decide +kernel
theorem row_23_111 : ThresholdAt 23 111 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 111 0 cell_23_111_0
  | exact S 23 111 1 cell_23_111_1
  | exact S 23 111 2 cell_23_111_2
  | exact S 23 111 3 cell_23_111_3
  | exact S 23 111 4 cell_23_111_4
  | exact S 23 111 5 cell_23_111_5
theorem cell_23_112_0 : C 23 112 0 := by decide +kernel
theorem cell_23_112_1 : C 23 112 1 := by decide +kernel
theorem cell_23_112_2 : C 23 112 2 := by decide +kernel
theorem cell_23_112_3 : C 23 112 3 := by decide +kernel
theorem cell_23_112_4 : C 23 112 4 := by decide +kernel
theorem cell_23_112_5 : C 23 112 5 := by decide +kernel
theorem row_23_112 : ThresholdAt 23 112 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 112 0 cell_23_112_0
  | exact S 23 112 1 cell_23_112_1
  | exact S 23 112 2 cell_23_112_2
  | exact S 23 112 3 cell_23_112_3
  | exact S 23 112 4 cell_23_112_4
  | exact S 23 112 5 cell_23_112_5
theorem cell_23_113_0 : C 23 113 0 := by decide +kernel
theorem cell_23_113_1 : C 23 113 1 := by decide +kernel
theorem cell_23_113_2 : C 23 113 2 := by decide +kernel
theorem cell_23_113_3 : C 23 113 3 := by decide +kernel
theorem cell_23_113_4 : C 23 113 4 := by decide +kernel
theorem cell_23_113_5 : C 23 113 5 := by decide +kernel
theorem row_23_113 : ThresholdAt 23 113 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 113 0 cell_23_113_0
  | exact S 23 113 1 cell_23_113_1
  | exact S 23 113 2 cell_23_113_2
  | exact S 23 113 3 cell_23_113_3
  | exact S 23 113 4 cell_23_113_4
  | exact S 23 113 5 cell_23_113_5
theorem cell_23_114_0 : C 23 114 0 := by decide +kernel
theorem cell_23_114_1 : C 23 114 1 := by decide +kernel
theorem cell_23_114_2 : C 23 114 2 := by decide +kernel
theorem cell_23_114_3 : C 23 114 3 := by decide +kernel
theorem cell_23_114_4 : C 23 114 4 := by decide +kernel
theorem cell_23_114_5 : C 23 114 5 := by decide +kernel
theorem row_23_114 : ThresholdAt 23 114 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 114 0 cell_23_114_0
  | exact S 23 114 1 cell_23_114_1
  | exact S 23 114 2 cell_23_114_2
  | exact S 23 114 3 cell_23_114_3
  | exact S 23 114 4 cell_23_114_4
  | exact S 23 114 5 cell_23_114_5
theorem cell_23_115_0 : C 23 115 0 := by decide +kernel
theorem cell_23_115_1 : C 23 115 1 := by decide +kernel
theorem cell_23_115_2 : C 23 115 2 := by decide +kernel
theorem cell_23_115_3 : C 23 115 3 := by decide +kernel
theorem cell_23_115_4 : C 23 115 4 := by decide +kernel
theorem cell_23_115_5 : C 23 115 5 := by decide +kernel
theorem row_23_115 : ThresholdAt 23 115 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 115 0 cell_23_115_0
  | exact S 23 115 1 cell_23_115_1
  | exact S 23 115 2 cell_23_115_2
  | exact S 23 115 3 cell_23_115_3
  | exact S 23 115 4 cell_23_115_4
  | exact S 23 115 5 cell_23_115_5
theorem cell_23_116_0 : C 23 116 0 := by decide +kernel
theorem cell_23_116_1 : C 23 116 1 := by decide +kernel
theorem cell_23_116_2 : C 23 116 2 := by decide +kernel
theorem cell_23_116_3 : C 23 116 3 := by decide +kernel
theorem cell_23_116_4 : C 23 116 4 := by decide +kernel
theorem cell_23_116_5 : C 23 116 5 := by decide +kernel
theorem row_23_116 : ThresholdAt 23 116 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 23 116 0 cell_23_116_0
  | exact S 23 116 1 cell_23_116_1
  | exact S 23 116 2 cell_23_116_2
  | exact S 23 116 3 cell_23_116_3
  | exact S 23 116 4 cell_23_116_4
  | exact S 23 116 5 cell_23_116_5
theorem checkedR23 : ∀ V ∈ List.range 117, ThresholdAt 23 V := by
  intro V hV
  have hv : V < 117 := List.mem_range.mp hV
  by_cases h0_117 : V < 58
  · by_cases h0_58 : V < 29
    · by_cases h0_29 : V < 14
      · by_cases h0_14 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have he : V = 0 := by omega
              subst V
              exact row_23_0
            · by_cases h1_3 : V < 2
              · have he : V = 1 := by omega
                subst V
                exact row_23_1
              · have he : V = 2 := by omega
                subst V
                exact row_23_2
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have he : V = 3 := by omega
                subst V
                exact row_23_3
              · have he : V = 4 := by omega
                subst V
                exact row_23_4
            · by_cases h5_7 : V < 6
              · have he : V = 5 := by omega
                subst V
                exact row_23_5
              · have he : V = 6 := by omega
                subst V
                exact row_23_6
        · by_cases h7_14 : V < 10
          · by_cases h7_10 : V < 8
            · have he : V = 7 := by omega
              subst V
              exact row_23_7
            · by_cases h8_10 : V < 9
              · have he : V = 8 := by omega
                subst V
                exact row_23_8
              · have he : V = 9 := by omega
                subst V
                exact row_23_9
          · by_cases h10_14 : V < 12
            · by_cases h10_12 : V < 11
              · have he : V = 10 := by omega
                subst V
                exact row_23_10
              · have he : V = 11 := by omega
                subst V
                exact row_23_11
            · by_cases h12_14 : V < 13
              · have he : V = 12 := by omega
                subst V
                exact row_23_12
              · have he : V = 13 := by omega
                subst V
                exact row_23_13
      · by_cases h14_29 : V < 21
        · by_cases h14_21 : V < 17
          · by_cases h14_17 : V < 15
            · have he : V = 14 := by omega
              subst V
              exact row_23_14
            · by_cases h15_17 : V < 16
              · have he : V = 15 := by omega
                subst V
                exact row_23_15
              · have he : V = 16 := by omega
                subst V
                exact row_23_16
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have he : V = 17 := by omega
                subst V
                exact row_23_17
              · have he : V = 18 := by omega
                subst V
                exact row_23_18
            · by_cases h19_21 : V < 20
              · have he : V = 19 := by omega
                subst V
                exact row_23_19
              · have he : V = 20 := by omega
                subst V
                exact row_23_20
        · by_cases h21_29 : V < 25
          · by_cases h21_25 : V < 23
            · by_cases h21_23 : V < 22
              · have he : V = 21 := by omega
                subst V
                exact row_23_21
              · have he : V = 22 := by omega
                subst V
                exact row_23_22
            · by_cases h23_25 : V < 24
              · have he : V = 23 := by omega
                subst V
                exact row_23_23
              · have he : V = 24 := by omega
                subst V
                exact row_23_24
          · by_cases h25_29 : V < 27
            · by_cases h25_27 : V < 26
              · have he : V = 25 := by omega
                subst V
                exact row_23_25
              · have he : V = 26 := by omega
                subst V
                exact row_23_26
            · by_cases h27_29 : V < 28
              · have he : V = 27 := by omega
                subst V
                exact row_23_27
              · have he : V = 28 := by omega
                subst V
                exact row_23_28
    · by_cases h29_58 : V < 43
      · by_cases h29_43 : V < 36
        · by_cases h29_36 : V < 32
          · by_cases h29_32 : V < 30
            · have he : V = 29 := by omega
              subst V
              exact row_23_29
            · by_cases h30_32 : V < 31
              · have he : V = 30 := by omega
                subst V
                exact row_23_30
              · have he : V = 31 := by omega
                subst V
                exact row_23_31
          · by_cases h32_36 : V < 34
            · by_cases h32_34 : V < 33
              · have he : V = 32 := by omega
                subst V
                exact row_23_32
              · have he : V = 33 := by omega
                subst V
                exact row_23_33
            · by_cases h34_36 : V < 35
              · have he : V = 34 := by omega
                subst V
                exact row_23_34
              · have he : V = 35 := by omega
                subst V
                exact row_23_35
        · by_cases h36_43 : V < 39
          · by_cases h36_39 : V < 37
            · have he : V = 36 := by omega
              subst V
              exact row_23_36
            · by_cases h37_39 : V < 38
              · have he : V = 37 := by omega
                subst V
                exact row_23_37
              · have he : V = 38 := by omega
                subst V
                exact row_23_38
          · by_cases h39_43 : V < 41
            · by_cases h39_41 : V < 40
              · have he : V = 39 := by omega
                subst V
                exact row_23_39
              · have he : V = 40 := by omega
                subst V
                exact row_23_40
            · by_cases h41_43 : V < 42
              · have he : V = 41 := by omega
                subst V
                exact row_23_41
              · have he : V = 42 := by omega
                subst V
                exact row_23_42
      · by_cases h43_58 : V < 50
        · by_cases h43_50 : V < 46
          · by_cases h43_46 : V < 44
            · have he : V = 43 := by omega
              subst V
              exact row_23_43
            · by_cases h44_46 : V < 45
              · have he : V = 44 := by omega
                subst V
                exact row_23_44
              · have he : V = 45 := by omega
                subst V
                exact row_23_45
          · by_cases h46_50 : V < 48
            · by_cases h46_48 : V < 47
              · have he : V = 46 := by omega
                subst V
                exact row_23_46
              · have he : V = 47 := by omega
                subst V
                exact row_23_47
            · by_cases h48_50 : V < 49
              · have he : V = 48 := by omega
                subst V
                exact row_23_48
              · have he : V = 49 := by omega
                subst V
                exact row_23_49
        · by_cases h50_58 : V < 54
          · by_cases h50_54 : V < 52
            · by_cases h50_52 : V < 51
              · have he : V = 50 := by omega
                subst V
                exact row_23_50
              · have he : V = 51 := by omega
                subst V
                exact row_23_51
            · by_cases h52_54 : V < 53
              · have he : V = 52 := by omega
                subst V
                exact row_23_52
              · have he : V = 53 := by omega
                subst V
                exact row_23_53
          · by_cases h54_58 : V < 56
            · by_cases h54_56 : V < 55
              · have he : V = 54 := by omega
                subst V
                exact row_23_54
              · have he : V = 55 := by omega
                subst V
                exact row_23_55
            · by_cases h56_58 : V < 57
              · have he : V = 56 := by omega
                subst V
                exact row_23_56
              · have he : V = 57 := by omega
                subst V
                exact row_23_57
  · by_cases h58_117 : V < 87
    · by_cases h58_87 : V < 72
      · by_cases h58_72 : V < 65
        · by_cases h58_65 : V < 61
          · by_cases h58_61 : V < 59
            · have he : V = 58 := by omega
              subst V
              exact row_23_58
            · by_cases h59_61 : V < 60
              · have he : V = 59 := by omega
                subst V
                exact row_23_59
              · have he : V = 60 := by omega
                subst V
                exact row_23_60
          · by_cases h61_65 : V < 63
            · by_cases h61_63 : V < 62
              · have he : V = 61 := by omega
                subst V
                exact row_23_61
              · have he : V = 62 := by omega
                subst V
                exact row_23_62
            · by_cases h63_65 : V < 64
              · have he : V = 63 := by omega
                subst V
                exact row_23_63
              · have he : V = 64 := by omega
                subst V
                exact row_23_64
        · by_cases h65_72 : V < 68
          · by_cases h65_68 : V < 66
            · have he : V = 65 := by omega
              subst V
              exact row_23_65
            · by_cases h66_68 : V < 67
              · have he : V = 66 := by omega
                subst V
                exact row_23_66
              · have he : V = 67 := by omega
                subst V
                exact row_23_67
          · by_cases h68_72 : V < 70
            · by_cases h68_70 : V < 69
              · have he : V = 68 := by omega
                subst V
                exact row_23_68
              · have he : V = 69 := by omega
                subst V
                exact row_23_69
            · by_cases h70_72 : V < 71
              · have he : V = 70 := by omega
                subst V
                exact row_23_70
              · have he : V = 71 := by omega
                subst V
                exact row_23_71
      · by_cases h72_87 : V < 79
        · by_cases h72_79 : V < 75
          · by_cases h72_75 : V < 73
            · have he : V = 72 := by omega
              subst V
              exact row_23_72
            · by_cases h73_75 : V < 74
              · have he : V = 73 := by omega
                subst V
                exact row_23_73
              · have he : V = 74 := by omega
                subst V
                exact row_23_74
          · by_cases h75_79 : V < 77
            · by_cases h75_77 : V < 76
              · have he : V = 75 := by omega
                subst V
                exact row_23_75
              · have he : V = 76 := by omega
                subst V
                exact row_23_76
            · by_cases h77_79 : V < 78
              · have he : V = 77 := by omega
                subst V
                exact row_23_77
              · have he : V = 78 := by omega
                subst V
                exact row_23_78
        · by_cases h79_87 : V < 83
          · by_cases h79_83 : V < 81
            · by_cases h79_81 : V < 80
              · have he : V = 79 := by omega
                subst V
                exact row_23_79
              · have he : V = 80 := by omega
                subst V
                exact row_23_80
            · by_cases h81_83 : V < 82
              · have he : V = 81 := by omega
                subst V
                exact row_23_81
              · have he : V = 82 := by omega
                subst V
                exact row_23_82
          · by_cases h83_87 : V < 85
            · by_cases h83_85 : V < 84
              · have he : V = 83 := by omega
                subst V
                exact row_23_83
              · have he : V = 84 := by omega
                subst V
                exact row_23_84
            · by_cases h85_87 : V < 86
              · have he : V = 85 := by omega
                subst V
                exact row_23_85
              · have he : V = 86 := by omega
                subst V
                exact row_23_86
    · by_cases h87_117 : V < 102
      · by_cases h87_102 : V < 94
        · by_cases h87_94 : V < 90
          · by_cases h87_90 : V < 88
            · have he : V = 87 := by omega
              subst V
              exact row_23_87
            · by_cases h88_90 : V < 89
              · have he : V = 88 := by omega
                subst V
                exact row_23_88
              · have he : V = 89 := by omega
                subst V
                exact row_23_89
          · by_cases h90_94 : V < 92
            · by_cases h90_92 : V < 91
              · have he : V = 90 := by omega
                subst V
                exact row_23_90
              · have he : V = 91 := by omega
                subst V
                exact row_23_91
            · by_cases h92_94 : V < 93
              · have he : V = 92 := by omega
                subst V
                exact row_23_92
              · have he : V = 93 := by omega
                subst V
                exact row_23_93
        · by_cases h94_102 : V < 98
          · by_cases h94_98 : V < 96
            · by_cases h94_96 : V < 95
              · have he : V = 94 := by omega
                subst V
                exact row_23_94
              · have he : V = 95 := by omega
                subst V
                exact row_23_95
            · by_cases h96_98 : V < 97
              · have he : V = 96 := by omega
                subst V
                exact row_23_96
              · have he : V = 97 := by omega
                subst V
                exact row_23_97
          · by_cases h98_102 : V < 100
            · by_cases h98_100 : V < 99
              · have he : V = 98 := by omega
                subst V
                exact row_23_98
              · have he : V = 99 := by omega
                subst V
                exact row_23_99
            · by_cases h100_102 : V < 101
              · have he : V = 100 := by omega
                subst V
                exact row_23_100
              · have he : V = 101 := by omega
                subst V
                exact row_23_101
      · by_cases h102_117 : V < 109
        · by_cases h102_109 : V < 105
          · by_cases h102_105 : V < 103
            · have he : V = 102 := by omega
              subst V
              exact row_23_102
            · by_cases h103_105 : V < 104
              · have he : V = 103 := by omega
                subst V
                exact row_23_103
              · have he : V = 104 := by omega
                subst V
                exact row_23_104
          · by_cases h105_109 : V < 107
            · by_cases h105_107 : V < 106
              · have he : V = 105 := by omega
                subst V
                exact row_23_105
              · have he : V = 106 := by omega
                subst V
                exact row_23_106
            · by_cases h107_109 : V < 108
              · have he : V = 107 := by omega
                subst V
                exact row_23_107
              · have he : V = 108 := by omega
                subst V
                exact row_23_108
        · by_cases h109_117 : V < 113
          · by_cases h109_113 : V < 111
            · by_cases h109_111 : V < 110
              · have he : V = 109 := by omega
                subst V
                exact row_23_109
              · have he : V = 110 := by omega
                subst V
                exact row_23_110
            · by_cases h111_113 : V < 112
              · have he : V = 111 := by omega
                subst V
                exact row_23_111
              · have he : V = 112 := by omega
                subst V
                exact row_23_112
          · by_cases h113_117 : V < 115
            · by_cases h113_115 : V < 114
              · have he : V = 113 := by omega
                subst V
                exact row_23_113
              · have he : V = 114 := by omega
                subst V
                exact row_23_114
            · by_cases h115_117 : V < 116
              · have he : V = 115 := by omega
                subst V
                exact row_23_115
              · have he : V = 116 := by omega
                subst V
                exact row_23_116
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
