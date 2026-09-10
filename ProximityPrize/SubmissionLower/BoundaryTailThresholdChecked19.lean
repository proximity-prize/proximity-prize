import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked18

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_19_0_0 : C 19 0 0 := by decide +kernel
theorem cell_19_0_1 : C 19 0 1 := by decide +kernel
theorem cell_19_0_2 : C 19 0 2 := by decide +kernel
theorem cell_19_0_3 : C 19 0 3 := by decide +kernel
theorem cell_19_0_4 : C 19 0 4 := by decide +kernel
theorem cell_19_0_5 : C 19 0 5 := by decide +kernel
theorem row_19_0 : ThresholdAt 19 0 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 0 0 cell_19_0_0
  | exact S 19 0 1 cell_19_0_1
  | exact S 19 0 2 cell_19_0_2
  | exact S 19 0 3 cell_19_0_3
  | exact S 19 0 4 cell_19_0_4
  | exact S 19 0 5 cell_19_0_5
theorem cell_19_1_0 : C 19 1 0 := by decide +kernel
theorem cell_19_1_1 : C 19 1 1 := by decide +kernel
theorem cell_19_1_2 : C 19 1 2 := by decide +kernel
theorem cell_19_1_3 : C 19 1 3 := by decide +kernel
theorem cell_19_1_4 : C 19 1 4 := by decide +kernel
theorem cell_19_1_5 : C 19 1 5 := by decide +kernel
theorem row_19_1 : ThresholdAt 19 1 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 1 0 cell_19_1_0
  | exact S 19 1 1 cell_19_1_1
  | exact S 19 1 2 cell_19_1_2
  | exact S 19 1 3 cell_19_1_3
  | exact S 19 1 4 cell_19_1_4
  | exact S 19 1 5 cell_19_1_5
theorem cell_19_2_0 : C 19 2 0 := by decide +kernel
theorem cell_19_2_1 : C 19 2 1 := by decide +kernel
theorem cell_19_2_2 : C 19 2 2 := by decide +kernel
theorem cell_19_2_3 : C 19 2 3 := by decide +kernel
theorem cell_19_2_4 : C 19 2 4 := by decide +kernel
theorem cell_19_2_5 : C 19 2 5 := by decide +kernel
theorem row_19_2 : ThresholdAt 19 2 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 2 0 cell_19_2_0
  | exact S 19 2 1 cell_19_2_1
  | exact S 19 2 2 cell_19_2_2
  | exact S 19 2 3 cell_19_2_3
  | exact S 19 2 4 cell_19_2_4
  | exact S 19 2 5 cell_19_2_5
theorem cell_19_3_0 : C 19 3 0 := by decide +kernel
theorem cell_19_3_1 : C 19 3 1 := by decide +kernel
theorem cell_19_3_2 : C 19 3 2 := by decide +kernel
theorem cell_19_3_3 : C 19 3 3 := by decide +kernel
theorem cell_19_3_4 : C 19 3 4 := by decide +kernel
theorem cell_19_3_5 : C 19 3 5 := by decide +kernel
theorem row_19_3 : ThresholdAt 19 3 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 3 0 cell_19_3_0
  | exact S 19 3 1 cell_19_3_1
  | exact S 19 3 2 cell_19_3_2
  | exact S 19 3 3 cell_19_3_3
  | exact S 19 3 4 cell_19_3_4
  | exact S 19 3 5 cell_19_3_5
theorem cell_19_4_0 : C 19 4 0 := by decide +kernel
theorem cell_19_4_1 : C 19 4 1 := by decide +kernel
theorem cell_19_4_2 : C 19 4 2 := by decide +kernel
theorem cell_19_4_3 : C 19 4 3 := by decide +kernel
theorem cell_19_4_4 : C 19 4 4 := by decide +kernel
theorem cell_19_4_5 : C 19 4 5 := by decide +kernel
theorem row_19_4 : ThresholdAt 19 4 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 4 0 cell_19_4_0
  | exact S 19 4 1 cell_19_4_1
  | exact S 19 4 2 cell_19_4_2
  | exact S 19 4 3 cell_19_4_3
  | exact S 19 4 4 cell_19_4_4
  | exact S 19 4 5 cell_19_4_5
theorem cell_19_5_0 : C 19 5 0 := by decide +kernel
theorem cell_19_5_1 : C 19 5 1 := by decide +kernel
theorem cell_19_5_2 : C 19 5 2 := by decide +kernel
theorem cell_19_5_3 : C 19 5 3 := by decide +kernel
theorem cell_19_5_4 : C 19 5 4 := by decide +kernel
theorem cell_19_5_5 : C 19 5 5 := by decide +kernel
theorem row_19_5 : ThresholdAt 19 5 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 5 0 cell_19_5_0
  | exact S 19 5 1 cell_19_5_1
  | exact S 19 5 2 cell_19_5_2
  | exact S 19 5 3 cell_19_5_3
  | exact S 19 5 4 cell_19_5_4
  | exact S 19 5 5 cell_19_5_5
theorem cell_19_6_0 : C 19 6 0 := by decide +kernel
theorem cell_19_6_1 : C 19 6 1 := by decide +kernel
theorem cell_19_6_2 : C 19 6 2 := by decide +kernel
theorem cell_19_6_3 : C 19 6 3 := by decide +kernel
theorem cell_19_6_4 : C 19 6 4 := by decide +kernel
theorem cell_19_6_5 : C 19 6 5 := by decide +kernel
theorem row_19_6 : ThresholdAt 19 6 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 6 0 cell_19_6_0
  | exact S 19 6 1 cell_19_6_1
  | exact S 19 6 2 cell_19_6_2
  | exact S 19 6 3 cell_19_6_3
  | exact S 19 6 4 cell_19_6_4
  | exact S 19 6 5 cell_19_6_5
theorem cell_19_7_0 : C 19 7 0 := by decide +kernel
theorem cell_19_7_1 : C 19 7 1 := by decide +kernel
theorem cell_19_7_2 : C 19 7 2 := by decide +kernel
theorem cell_19_7_3 : C 19 7 3 := by decide +kernel
theorem cell_19_7_4 : C 19 7 4 := by decide +kernel
theorem cell_19_7_5 : C 19 7 5 := by decide +kernel
theorem row_19_7 : ThresholdAt 19 7 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 7 0 cell_19_7_0
  | exact S 19 7 1 cell_19_7_1
  | exact S 19 7 2 cell_19_7_2
  | exact S 19 7 3 cell_19_7_3
  | exact S 19 7 4 cell_19_7_4
  | exact S 19 7 5 cell_19_7_5
theorem cell_19_8_0 : C 19 8 0 := by decide +kernel
theorem cell_19_8_1 : C 19 8 1 := by decide +kernel
theorem cell_19_8_2 : C 19 8 2 := by decide +kernel
theorem cell_19_8_3 : C 19 8 3 := by decide +kernel
theorem cell_19_8_4 : C 19 8 4 := by decide +kernel
theorem cell_19_8_5 : C 19 8 5 := by decide +kernel
theorem row_19_8 : ThresholdAt 19 8 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 8 0 cell_19_8_0
  | exact S 19 8 1 cell_19_8_1
  | exact S 19 8 2 cell_19_8_2
  | exact S 19 8 3 cell_19_8_3
  | exact S 19 8 4 cell_19_8_4
  | exact S 19 8 5 cell_19_8_5
theorem cell_19_9_0 : C 19 9 0 := by decide +kernel
theorem cell_19_9_1 : C 19 9 1 := by decide +kernel
theorem cell_19_9_2 : C 19 9 2 := by decide +kernel
theorem cell_19_9_3 : C 19 9 3 := by decide +kernel
theorem cell_19_9_4 : C 19 9 4 := by decide +kernel
theorem cell_19_9_5 : C 19 9 5 := by decide +kernel
theorem row_19_9 : ThresholdAt 19 9 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 9 0 cell_19_9_0
  | exact S 19 9 1 cell_19_9_1
  | exact S 19 9 2 cell_19_9_2
  | exact S 19 9 3 cell_19_9_3
  | exact S 19 9 4 cell_19_9_4
  | exact S 19 9 5 cell_19_9_5
theorem cell_19_10_0 : C 19 10 0 := by decide +kernel
theorem cell_19_10_1 : C 19 10 1 := by decide +kernel
theorem cell_19_10_2 : C 19 10 2 := by decide +kernel
theorem cell_19_10_3 : C 19 10 3 := by decide +kernel
theorem cell_19_10_4 : C 19 10 4 := by decide +kernel
theorem cell_19_10_5 : C 19 10 5 := by decide +kernel
theorem row_19_10 : ThresholdAt 19 10 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 10 0 cell_19_10_0
  | exact S 19 10 1 cell_19_10_1
  | exact S 19 10 2 cell_19_10_2
  | exact S 19 10 3 cell_19_10_3
  | exact S 19 10 4 cell_19_10_4
  | exact S 19 10 5 cell_19_10_5
theorem cell_19_11_0 : C 19 11 0 := by decide +kernel
theorem cell_19_11_1 : C 19 11 1 := by decide +kernel
theorem cell_19_11_2 : C 19 11 2 := by decide +kernel
theorem cell_19_11_3 : C 19 11 3 := by decide +kernel
theorem cell_19_11_4 : C 19 11 4 := by decide +kernel
theorem cell_19_11_5 : C 19 11 5 := by decide +kernel
theorem row_19_11 : ThresholdAt 19 11 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 11 0 cell_19_11_0
  | exact S 19 11 1 cell_19_11_1
  | exact S 19 11 2 cell_19_11_2
  | exact S 19 11 3 cell_19_11_3
  | exact S 19 11 4 cell_19_11_4
  | exact S 19 11 5 cell_19_11_5
theorem cell_19_12_0 : C 19 12 0 := by decide +kernel
theorem cell_19_12_1 : C 19 12 1 := by decide +kernel
theorem cell_19_12_2 : C 19 12 2 := by decide +kernel
theorem cell_19_12_3 : C 19 12 3 := by decide +kernel
theorem cell_19_12_4 : C 19 12 4 := by decide +kernel
theorem cell_19_12_5 : C 19 12 5 := by decide +kernel
theorem row_19_12 : ThresholdAt 19 12 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 12 0 cell_19_12_0
  | exact S 19 12 1 cell_19_12_1
  | exact S 19 12 2 cell_19_12_2
  | exact S 19 12 3 cell_19_12_3
  | exact S 19 12 4 cell_19_12_4
  | exact S 19 12 5 cell_19_12_5
theorem cell_19_13_0 : C 19 13 0 := by decide +kernel
theorem cell_19_13_1 : C 19 13 1 := by decide +kernel
theorem cell_19_13_2 : C 19 13 2 := by decide +kernel
theorem cell_19_13_3 : C 19 13 3 := by decide +kernel
theorem cell_19_13_4 : C 19 13 4 := by decide +kernel
theorem cell_19_13_5 : C 19 13 5 := by decide +kernel
theorem row_19_13 : ThresholdAt 19 13 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 13 0 cell_19_13_0
  | exact S 19 13 1 cell_19_13_1
  | exact S 19 13 2 cell_19_13_2
  | exact S 19 13 3 cell_19_13_3
  | exact S 19 13 4 cell_19_13_4
  | exact S 19 13 5 cell_19_13_5
theorem cell_19_14_0 : C 19 14 0 := by decide +kernel
theorem cell_19_14_1 : C 19 14 1 := by decide +kernel
theorem cell_19_14_2 : C 19 14 2 := by decide +kernel
theorem cell_19_14_3 : C 19 14 3 := by decide +kernel
theorem cell_19_14_4 : C 19 14 4 := by decide +kernel
theorem cell_19_14_5 : C 19 14 5 := by decide +kernel
theorem row_19_14 : ThresholdAt 19 14 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 14 0 cell_19_14_0
  | exact S 19 14 1 cell_19_14_1
  | exact S 19 14 2 cell_19_14_2
  | exact S 19 14 3 cell_19_14_3
  | exact S 19 14 4 cell_19_14_4
  | exact S 19 14 5 cell_19_14_5
theorem cell_19_15_0 : C 19 15 0 := by decide +kernel
theorem cell_19_15_1 : C 19 15 1 := by decide +kernel
theorem cell_19_15_2 : C 19 15 2 := by decide +kernel
theorem cell_19_15_3 : C 19 15 3 := by decide +kernel
theorem cell_19_15_4 : C 19 15 4 := by decide +kernel
theorem cell_19_15_5 : C 19 15 5 := by decide +kernel
theorem row_19_15 : ThresholdAt 19 15 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 15 0 cell_19_15_0
  | exact S 19 15 1 cell_19_15_1
  | exact S 19 15 2 cell_19_15_2
  | exact S 19 15 3 cell_19_15_3
  | exact S 19 15 4 cell_19_15_4
  | exact S 19 15 5 cell_19_15_5
theorem cell_19_16_0 : C 19 16 0 := by decide +kernel
theorem cell_19_16_1 : C 19 16 1 := by decide +kernel
theorem cell_19_16_2 : C 19 16 2 := by decide +kernel
theorem cell_19_16_3 : C 19 16 3 := by decide +kernel
theorem cell_19_16_4 : C 19 16 4 := by decide +kernel
theorem cell_19_16_5 : C 19 16 5 := by decide +kernel
theorem row_19_16 : ThresholdAt 19 16 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 16 0 cell_19_16_0
  | exact S 19 16 1 cell_19_16_1
  | exact S 19 16 2 cell_19_16_2
  | exact S 19 16 3 cell_19_16_3
  | exact S 19 16 4 cell_19_16_4
  | exact S 19 16 5 cell_19_16_5
theorem cell_19_17_0 : C 19 17 0 := by decide +kernel
theorem cell_19_17_1 : C 19 17 1 := by decide +kernel
theorem cell_19_17_2 : C 19 17 2 := by decide +kernel
theorem cell_19_17_3 : C 19 17 3 := by decide +kernel
theorem cell_19_17_4 : C 19 17 4 := by decide +kernel
theorem cell_19_17_5 : C 19 17 5 := by decide +kernel
theorem row_19_17 : ThresholdAt 19 17 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 17 0 cell_19_17_0
  | exact S 19 17 1 cell_19_17_1
  | exact S 19 17 2 cell_19_17_2
  | exact S 19 17 3 cell_19_17_3
  | exact S 19 17 4 cell_19_17_4
  | exact S 19 17 5 cell_19_17_5
theorem cell_19_18_0 : C 19 18 0 := by decide +kernel
theorem cell_19_18_1 : C 19 18 1 := by decide +kernel
theorem cell_19_18_2 : C 19 18 2 := by decide +kernel
theorem cell_19_18_3 : C 19 18 3 := by decide +kernel
theorem cell_19_18_4 : C 19 18 4 := by decide +kernel
theorem cell_19_18_5 : C 19 18 5 := by decide +kernel
theorem row_19_18 : ThresholdAt 19 18 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 18 0 cell_19_18_0
  | exact S 19 18 1 cell_19_18_1
  | exact S 19 18 2 cell_19_18_2
  | exact S 19 18 3 cell_19_18_3
  | exact S 19 18 4 cell_19_18_4
  | exact S 19 18 5 cell_19_18_5
theorem cell_19_19_0 : C 19 19 0 := by decide +kernel
theorem cell_19_19_1 : C 19 19 1 := by decide +kernel
theorem cell_19_19_2 : C 19 19 2 := by decide +kernel
theorem cell_19_19_3 : C 19 19 3 := by decide +kernel
theorem cell_19_19_4 : C 19 19 4 := by decide +kernel
theorem cell_19_19_5 : C 19 19 5 := by decide +kernel
theorem row_19_19 : ThresholdAt 19 19 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 19 0 cell_19_19_0
  | exact S 19 19 1 cell_19_19_1
  | exact S 19 19 2 cell_19_19_2
  | exact S 19 19 3 cell_19_19_3
  | exact S 19 19 4 cell_19_19_4
  | exact S 19 19 5 cell_19_19_5
theorem cell_19_20_0 : C 19 20 0 := by decide +kernel
theorem cell_19_20_1 : C 19 20 1 := by decide +kernel
theorem cell_19_20_2 : C 19 20 2 := by decide +kernel
theorem cell_19_20_3 : C 19 20 3 := by decide +kernel
theorem cell_19_20_4 : C 19 20 4 := by decide +kernel
theorem cell_19_20_5 : C 19 20 5 := by decide +kernel
theorem row_19_20 : ThresholdAt 19 20 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 20 0 cell_19_20_0
  | exact S 19 20 1 cell_19_20_1
  | exact S 19 20 2 cell_19_20_2
  | exact S 19 20 3 cell_19_20_3
  | exact S 19 20 4 cell_19_20_4
  | exact S 19 20 5 cell_19_20_5
theorem cell_19_21_0 : C 19 21 0 := by decide +kernel
theorem cell_19_21_1 : C 19 21 1 := by decide +kernel
theorem cell_19_21_2 : C 19 21 2 := by decide +kernel
theorem cell_19_21_3 : C 19 21 3 := by decide +kernel
theorem cell_19_21_4 : C 19 21 4 := by decide +kernel
theorem cell_19_21_5 : C 19 21 5 := by decide +kernel
theorem row_19_21 : ThresholdAt 19 21 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 21 0 cell_19_21_0
  | exact S 19 21 1 cell_19_21_1
  | exact S 19 21 2 cell_19_21_2
  | exact S 19 21 3 cell_19_21_3
  | exact S 19 21 4 cell_19_21_4
  | exact S 19 21 5 cell_19_21_5
theorem cell_19_22_0 : C 19 22 0 := by decide +kernel
theorem cell_19_22_1 : C 19 22 1 := by decide +kernel
theorem cell_19_22_2 : C 19 22 2 := by decide +kernel
theorem cell_19_22_3 : C 19 22 3 := by decide +kernel
theorem cell_19_22_4 : C 19 22 4 := by decide +kernel
theorem cell_19_22_5 : C 19 22 5 := by decide +kernel
theorem row_19_22 : ThresholdAt 19 22 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 22 0 cell_19_22_0
  | exact S 19 22 1 cell_19_22_1
  | exact S 19 22 2 cell_19_22_2
  | exact S 19 22 3 cell_19_22_3
  | exact S 19 22 4 cell_19_22_4
  | exact S 19 22 5 cell_19_22_5
theorem cell_19_23_0 : C 19 23 0 := by decide +kernel
theorem cell_19_23_1 : C 19 23 1 := by decide +kernel
theorem cell_19_23_2 : C 19 23 2 := by decide +kernel
theorem cell_19_23_3 : C 19 23 3 := by decide +kernel
theorem cell_19_23_4 : C 19 23 4 := by decide +kernel
theorem cell_19_23_5 : C 19 23 5 := by decide +kernel
theorem row_19_23 : ThresholdAt 19 23 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 23 0 cell_19_23_0
  | exact S 19 23 1 cell_19_23_1
  | exact S 19 23 2 cell_19_23_2
  | exact S 19 23 3 cell_19_23_3
  | exact S 19 23 4 cell_19_23_4
  | exact S 19 23 5 cell_19_23_5
theorem cell_19_24_0 : C 19 24 0 := by decide +kernel
theorem cell_19_24_1 : C 19 24 1 := by decide +kernel
theorem cell_19_24_2 : C 19 24 2 := by decide +kernel
theorem cell_19_24_3 : C 19 24 3 := by decide +kernel
theorem cell_19_24_4 : C 19 24 4 := by decide +kernel
theorem cell_19_24_5 : C 19 24 5 := by decide +kernel
theorem row_19_24 : ThresholdAt 19 24 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 24 0 cell_19_24_0
  | exact S 19 24 1 cell_19_24_1
  | exact S 19 24 2 cell_19_24_2
  | exact S 19 24 3 cell_19_24_3
  | exact S 19 24 4 cell_19_24_4
  | exact S 19 24 5 cell_19_24_5
theorem cell_19_25_0 : C 19 25 0 := by decide +kernel
theorem cell_19_25_1 : C 19 25 1 := by decide +kernel
theorem cell_19_25_2 : C 19 25 2 := by decide +kernel
theorem cell_19_25_3 : C 19 25 3 := by decide +kernel
theorem cell_19_25_4 : C 19 25 4 := by decide +kernel
theorem cell_19_25_5 : C 19 25 5 := by decide +kernel
theorem row_19_25 : ThresholdAt 19 25 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 25 0 cell_19_25_0
  | exact S 19 25 1 cell_19_25_1
  | exact S 19 25 2 cell_19_25_2
  | exact S 19 25 3 cell_19_25_3
  | exact S 19 25 4 cell_19_25_4
  | exact S 19 25 5 cell_19_25_5
theorem cell_19_26_0 : C 19 26 0 := by decide +kernel
theorem cell_19_26_1 : C 19 26 1 := by decide +kernel
theorem cell_19_26_2 : C 19 26 2 := by decide +kernel
theorem cell_19_26_3 : C 19 26 3 := by decide +kernel
theorem cell_19_26_4 : C 19 26 4 := by decide +kernel
theorem cell_19_26_5 : C 19 26 5 := by decide +kernel
theorem row_19_26 : ThresholdAt 19 26 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 26 0 cell_19_26_0
  | exact S 19 26 1 cell_19_26_1
  | exact S 19 26 2 cell_19_26_2
  | exact S 19 26 3 cell_19_26_3
  | exact S 19 26 4 cell_19_26_4
  | exact S 19 26 5 cell_19_26_5
theorem cell_19_27_0 : C 19 27 0 := by decide +kernel
theorem cell_19_27_1 : C 19 27 1 := by decide +kernel
theorem cell_19_27_2 : C 19 27 2 := by decide +kernel
theorem cell_19_27_3 : C 19 27 3 := by decide +kernel
theorem cell_19_27_4 : C 19 27 4 := by decide +kernel
theorem cell_19_27_5 : C 19 27 5 := by decide +kernel
theorem row_19_27 : ThresholdAt 19 27 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 27 0 cell_19_27_0
  | exact S 19 27 1 cell_19_27_1
  | exact S 19 27 2 cell_19_27_2
  | exact S 19 27 3 cell_19_27_3
  | exact S 19 27 4 cell_19_27_4
  | exact S 19 27 5 cell_19_27_5
theorem cell_19_28_0 : C 19 28 0 := by decide +kernel
theorem cell_19_28_1 : C 19 28 1 := by decide +kernel
theorem cell_19_28_2 : C 19 28 2 := by decide +kernel
theorem cell_19_28_3 : C 19 28 3 := by decide +kernel
theorem cell_19_28_4 : C 19 28 4 := by decide +kernel
theorem cell_19_28_5 : C 19 28 5 := by decide +kernel
theorem row_19_28 : ThresholdAt 19 28 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 28 0 cell_19_28_0
  | exact S 19 28 1 cell_19_28_1
  | exact S 19 28 2 cell_19_28_2
  | exact S 19 28 3 cell_19_28_3
  | exact S 19 28 4 cell_19_28_4
  | exact S 19 28 5 cell_19_28_5
theorem cell_19_29_0 : C 19 29 0 := by decide +kernel
theorem cell_19_29_1 : C 19 29 1 := by decide +kernel
theorem cell_19_29_2 : C 19 29 2 := by decide +kernel
theorem cell_19_29_3 : C 19 29 3 := by decide +kernel
theorem cell_19_29_4 : C 19 29 4 := by decide +kernel
theorem cell_19_29_5 : C 19 29 5 := by decide +kernel
theorem row_19_29 : ThresholdAt 19 29 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 29 0 cell_19_29_0
  | exact S 19 29 1 cell_19_29_1
  | exact S 19 29 2 cell_19_29_2
  | exact S 19 29 3 cell_19_29_3
  | exact S 19 29 4 cell_19_29_4
  | exact S 19 29 5 cell_19_29_5
theorem cell_19_30_0 : C 19 30 0 := by decide +kernel
theorem cell_19_30_1 : C 19 30 1 := by decide +kernel
theorem cell_19_30_2 : C 19 30 2 := by decide +kernel
theorem cell_19_30_3 : C 19 30 3 := by decide +kernel
theorem cell_19_30_4 : C 19 30 4 := by decide +kernel
theorem cell_19_30_5 : C 19 30 5 := by decide +kernel
theorem row_19_30 : ThresholdAt 19 30 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 30 0 cell_19_30_0
  | exact S 19 30 1 cell_19_30_1
  | exact S 19 30 2 cell_19_30_2
  | exact S 19 30 3 cell_19_30_3
  | exact S 19 30 4 cell_19_30_4
  | exact S 19 30 5 cell_19_30_5
theorem cell_19_31_0 : C 19 31 0 := by decide +kernel
theorem cell_19_31_1 : C 19 31 1 := by decide +kernel
theorem cell_19_31_2 : C 19 31 2 := by decide +kernel
theorem cell_19_31_3 : C 19 31 3 := by decide +kernel
theorem cell_19_31_4 : C 19 31 4 := by decide +kernel
theorem cell_19_31_5 : C 19 31 5 := by decide +kernel
theorem row_19_31 : ThresholdAt 19 31 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 31 0 cell_19_31_0
  | exact S 19 31 1 cell_19_31_1
  | exact S 19 31 2 cell_19_31_2
  | exact S 19 31 3 cell_19_31_3
  | exact S 19 31 4 cell_19_31_4
  | exact S 19 31 5 cell_19_31_5
theorem cell_19_32_0 : C 19 32 0 := by decide +kernel
theorem cell_19_32_1 : C 19 32 1 := by decide +kernel
theorem cell_19_32_2 : C 19 32 2 := by decide +kernel
theorem cell_19_32_3 : C 19 32 3 := by decide +kernel
theorem cell_19_32_4 : C 19 32 4 := by decide +kernel
theorem cell_19_32_5 : C 19 32 5 := by decide +kernel
theorem row_19_32 : ThresholdAt 19 32 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 32 0 cell_19_32_0
  | exact S 19 32 1 cell_19_32_1
  | exact S 19 32 2 cell_19_32_2
  | exact S 19 32 3 cell_19_32_3
  | exact S 19 32 4 cell_19_32_4
  | exact S 19 32 5 cell_19_32_5
theorem cell_19_33_0 : C 19 33 0 := by decide +kernel
theorem cell_19_33_1 : C 19 33 1 := by decide +kernel
theorem cell_19_33_2 : C 19 33 2 := by decide +kernel
theorem cell_19_33_3 : C 19 33 3 := by decide +kernel
theorem cell_19_33_4 : C 19 33 4 := by decide +kernel
theorem cell_19_33_5 : C 19 33 5 := by decide +kernel
theorem row_19_33 : ThresholdAt 19 33 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 33 0 cell_19_33_0
  | exact S 19 33 1 cell_19_33_1
  | exact S 19 33 2 cell_19_33_2
  | exact S 19 33 3 cell_19_33_3
  | exact S 19 33 4 cell_19_33_4
  | exact S 19 33 5 cell_19_33_5
theorem cell_19_34_0 : C 19 34 0 := by decide +kernel
theorem cell_19_34_1 : C 19 34 1 := by decide +kernel
theorem cell_19_34_2 : C 19 34 2 := by decide +kernel
theorem cell_19_34_3 : C 19 34 3 := by decide +kernel
theorem cell_19_34_4 : C 19 34 4 := by decide +kernel
theorem cell_19_34_5 : C 19 34 5 := by decide +kernel
theorem row_19_34 : ThresholdAt 19 34 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 34 0 cell_19_34_0
  | exact S 19 34 1 cell_19_34_1
  | exact S 19 34 2 cell_19_34_2
  | exact S 19 34 3 cell_19_34_3
  | exact S 19 34 4 cell_19_34_4
  | exact S 19 34 5 cell_19_34_5
theorem cell_19_35_0 : C 19 35 0 := by decide +kernel
theorem cell_19_35_1 : C 19 35 1 := by decide +kernel
theorem cell_19_35_2 : C 19 35 2 := by decide +kernel
theorem cell_19_35_3 : C 19 35 3 := by decide +kernel
theorem cell_19_35_4 : C 19 35 4 := by decide +kernel
theorem cell_19_35_5 : C 19 35 5 := by decide +kernel
theorem row_19_35 : ThresholdAt 19 35 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 35 0 cell_19_35_0
  | exact S 19 35 1 cell_19_35_1
  | exact S 19 35 2 cell_19_35_2
  | exact S 19 35 3 cell_19_35_3
  | exact S 19 35 4 cell_19_35_4
  | exact S 19 35 5 cell_19_35_5
theorem cell_19_36_0 : C 19 36 0 := by decide +kernel
theorem cell_19_36_1 : C 19 36 1 := by decide +kernel
theorem cell_19_36_2 : C 19 36 2 := by decide +kernel
theorem cell_19_36_3 : C 19 36 3 := by decide +kernel
theorem cell_19_36_4 : C 19 36 4 := by decide +kernel
theorem cell_19_36_5 : C 19 36 5 := by decide +kernel
theorem row_19_36 : ThresholdAt 19 36 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 36 0 cell_19_36_0
  | exact S 19 36 1 cell_19_36_1
  | exact S 19 36 2 cell_19_36_2
  | exact S 19 36 3 cell_19_36_3
  | exact S 19 36 4 cell_19_36_4
  | exact S 19 36 5 cell_19_36_5
theorem cell_19_37_0 : C 19 37 0 := by decide +kernel
theorem cell_19_37_1 : C 19 37 1 := by decide +kernel
theorem cell_19_37_2 : C 19 37 2 := by decide +kernel
theorem cell_19_37_3 : C 19 37 3 := by decide +kernel
theorem cell_19_37_4 : C 19 37 4 := by decide +kernel
theorem cell_19_37_5 : C 19 37 5 := by decide +kernel
theorem row_19_37 : ThresholdAt 19 37 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 37 0 cell_19_37_0
  | exact S 19 37 1 cell_19_37_1
  | exact S 19 37 2 cell_19_37_2
  | exact S 19 37 3 cell_19_37_3
  | exact S 19 37 4 cell_19_37_4
  | exact S 19 37 5 cell_19_37_5
theorem cell_19_38_0 : C 19 38 0 := by decide +kernel
theorem cell_19_38_1 : C 19 38 1 := by decide +kernel
theorem cell_19_38_2 : C 19 38 2 := by decide +kernel
theorem cell_19_38_3 : C 19 38 3 := by decide +kernel
theorem cell_19_38_4 : C 19 38 4 := by decide +kernel
theorem cell_19_38_5 : C 19 38 5 := by decide +kernel
theorem row_19_38 : ThresholdAt 19 38 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 38 0 cell_19_38_0
  | exact S 19 38 1 cell_19_38_1
  | exact S 19 38 2 cell_19_38_2
  | exact S 19 38 3 cell_19_38_3
  | exact S 19 38 4 cell_19_38_4
  | exact S 19 38 5 cell_19_38_5
theorem cell_19_39_0 : C 19 39 0 := by decide +kernel
theorem cell_19_39_1 : C 19 39 1 := by decide +kernel
theorem cell_19_39_2 : C 19 39 2 := by decide +kernel
theorem cell_19_39_3 : C 19 39 3 := by decide +kernel
theorem cell_19_39_4 : C 19 39 4 := by decide +kernel
theorem cell_19_39_5 : C 19 39 5 := by decide +kernel
theorem row_19_39 : ThresholdAt 19 39 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 39 0 cell_19_39_0
  | exact S 19 39 1 cell_19_39_1
  | exact S 19 39 2 cell_19_39_2
  | exact S 19 39 3 cell_19_39_3
  | exact S 19 39 4 cell_19_39_4
  | exact S 19 39 5 cell_19_39_5
theorem cell_19_40_0 : C 19 40 0 := by decide +kernel
theorem cell_19_40_1 : C 19 40 1 := by decide +kernel
theorem cell_19_40_2 : C 19 40 2 := by decide +kernel
theorem cell_19_40_3 : C 19 40 3 := by decide +kernel
theorem cell_19_40_4 : C 19 40 4 := by decide +kernel
theorem cell_19_40_5 : C 19 40 5 := by decide +kernel
theorem row_19_40 : ThresholdAt 19 40 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 40 0 cell_19_40_0
  | exact S 19 40 1 cell_19_40_1
  | exact S 19 40 2 cell_19_40_2
  | exact S 19 40 3 cell_19_40_3
  | exact S 19 40 4 cell_19_40_4
  | exact S 19 40 5 cell_19_40_5
theorem cell_19_41_0 : C 19 41 0 := by decide +kernel
theorem cell_19_41_1 : C 19 41 1 := by decide +kernel
theorem cell_19_41_2 : C 19 41 2 := by decide +kernel
theorem cell_19_41_3 : C 19 41 3 := by decide +kernel
theorem cell_19_41_4 : C 19 41 4 := by decide +kernel
theorem cell_19_41_5 : C 19 41 5 := by decide +kernel
theorem row_19_41 : ThresholdAt 19 41 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 41 0 cell_19_41_0
  | exact S 19 41 1 cell_19_41_1
  | exact S 19 41 2 cell_19_41_2
  | exact S 19 41 3 cell_19_41_3
  | exact S 19 41 4 cell_19_41_4
  | exact S 19 41 5 cell_19_41_5
theorem cell_19_42_0 : C 19 42 0 := by decide +kernel
theorem cell_19_42_1 : C 19 42 1 := by decide +kernel
theorem cell_19_42_2 : C 19 42 2 := by decide +kernel
theorem cell_19_42_3 : C 19 42 3 := by decide +kernel
theorem cell_19_42_4 : C 19 42 4 := by decide +kernel
theorem cell_19_42_5 : C 19 42 5 := by decide +kernel
theorem row_19_42 : ThresholdAt 19 42 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 42 0 cell_19_42_0
  | exact S 19 42 1 cell_19_42_1
  | exact S 19 42 2 cell_19_42_2
  | exact S 19 42 3 cell_19_42_3
  | exact S 19 42 4 cell_19_42_4
  | exact S 19 42 5 cell_19_42_5
theorem cell_19_43_0 : C 19 43 0 := by decide +kernel
theorem cell_19_43_1 : C 19 43 1 := by decide +kernel
theorem cell_19_43_2 : C 19 43 2 := by decide +kernel
theorem cell_19_43_3 : C 19 43 3 := by decide +kernel
theorem cell_19_43_4 : C 19 43 4 := by decide +kernel
theorem cell_19_43_5 : C 19 43 5 := by decide +kernel
theorem row_19_43 : ThresholdAt 19 43 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 43 0 cell_19_43_0
  | exact S 19 43 1 cell_19_43_1
  | exact S 19 43 2 cell_19_43_2
  | exact S 19 43 3 cell_19_43_3
  | exact S 19 43 4 cell_19_43_4
  | exact S 19 43 5 cell_19_43_5
theorem cell_19_44_0 : C 19 44 0 := by decide +kernel
theorem cell_19_44_1 : C 19 44 1 := by decide +kernel
theorem cell_19_44_2 : C 19 44 2 := by decide +kernel
theorem cell_19_44_3 : C 19 44 3 := by decide +kernel
theorem cell_19_44_4 : C 19 44 4 := by decide +kernel
theorem cell_19_44_5 : C 19 44 5 := by decide +kernel
theorem row_19_44 : ThresholdAt 19 44 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 44 0 cell_19_44_0
  | exact S 19 44 1 cell_19_44_1
  | exact S 19 44 2 cell_19_44_2
  | exact S 19 44 3 cell_19_44_3
  | exact S 19 44 4 cell_19_44_4
  | exact S 19 44 5 cell_19_44_5
theorem cell_19_45_0 : C 19 45 0 := by decide +kernel
theorem cell_19_45_1 : C 19 45 1 := by decide +kernel
theorem cell_19_45_2 : C 19 45 2 := by decide +kernel
theorem cell_19_45_3 : C 19 45 3 := by decide +kernel
theorem cell_19_45_4 : C 19 45 4 := by decide +kernel
theorem cell_19_45_5 : C 19 45 5 := by decide +kernel
theorem row_19_45 : ThresholdAt 19 45 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 45 0 cell_19_45_0
  | exact S 19 45 1 cell_19_45_1
  | exact S 19 45 2 cell_19_45_2
  | exact S 19 45 3 cell_19_45_3
  | exact S 19 45 4 cell_19_45_4
  | exact S 19 45 5 cell_19_45_5
theorem cell_19_46_0 : C 19 46 0 := by decide +kernel
theorem cell_19_46_1 : C 19 46 1 := by decide +kernel
theorem cell_19_46_2 : C 19 46 2 := by decide +kernel
theorem cell_19_46_3 : C 19 46 3 := by decide +kernel
theorem cell_19_46_4 : C 19 46 4 := by decide +kernel
theorem cell_19_46_5 : C 19 46 5 := by decide +kernel
theorem row_19_46 : ThresholdAt 19 46 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 46 0 cell_19_46_0
  | exact S 19 46 1 cell_19_46_1
  | exact S 19 46 2 cell_19_46_2
  | exact S 19 46 3 cell_19_46_3
  | exact S 19 46 4 cell_19_46_4
  | exact S 19 46 5 cell_19_46_5
theorem cell_19_47_0 : C 19 47 0 := by decide +kernel
theorem cell_19_47_1 : C 19 47 1 := by decide +kernel
theorem cell_19_47_2 : C 19 47 2 := by decide +kernel
theorem cell_19_47_3 : C 19 47 3 := by decide +kernel
theorem cell_19_47_4 : C 19 47 4 := by decide +kernel
theorem cell_19_47_5 : C 19 47 5 := by decide +kernel
theorem row_19_47 : ThresholdAt 19 47 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 47 0 cell_19_47_0
  | exact S 19 47 1 cell_19_47_1
  | exact S 19 47 2 cell_19_47_2
  | exact S 19 47 3 cell_19_47_3
  | exact S 19 47 4 cell_19_47_4
  | exact S 19 47 5 cell_19_47_5
theorem cell_19_48_0 : C 19 48 0 := by decide +kernel
theorem cell_19_48_1 : C 19 48 1 := by decide +kernel
theorem cell_19_48_2 : C 19 48 2 := by decide +kernel
theorem cell_19_48_3 : C 19 48 3 := by decide +kernel
theorem cell_19_48_4 : C 19 48 4 := by decide +kernel
theorem cell_19_48_5 : C 19 48 5 := by decide +kernel
theorem row_19_48 : ThresholdAt 19 48 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 48 0 cell_19_48_0
  | exact S 19 48 1 cell_19_48_1
  | exact S 19 48 2 cell_19_48_2
  | exact S 19 48 3 cell_19_48_3
  | exact S 19 48 4 cell_19_48_4
  | exact S 19 48 5 cell_19_48_5
theorem cell_19_49_0 : C 19 49 0 := by decide +kernel
theorem cell_19_49_1 : C 19 49 1 := by decide +kernel
theorem cell_19_49_2 : C 19 49 2 := by decide +kernel
theorem cell_19_49_3 : C 19 49 3 := by decide +kernel
theorem cell_19_49_4 : C 19 49 4 := by decide +kernel
theorem cell_19_49_5 : C 19 49 5 := by decide +kernel
theorem row_19_49 : ThresholdAt 19 49 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 49 0 cell_19_49_0
  | exact S 19 49 1 cell_19_49_1
  | exact S 19 49 2 cell_19_49_2
  | exact S 19 49 3 cell_19_49_3
  | exact S 19 49 4 cell_19_49_4
  | exact S 19 49 5 cell_19_49_5
theorem cell_19_50_0 : C 19 50 0 := by decide +kernel
theorem cell_19_50_1 : C 19 50 1 := by decide +kernel
theorem cell_19_50_2 : C 19 50 2 := by decide +kernel
theorem cell_19_50_3 : C 19 50 3 := by decide +kernel
theorem cell_19_50_4 : C 19 50 4 := by decide +kernel
theorem cell_19_50_5 : C 19 50 5 := by decide +kernel
theorem row_19_50 : ThresholdAt 19 50 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 50 0 cell_19_50_0
  | exact S 19 50 1 cell_19_50_1
  | exact S 19 50 2 cell_19_50_2
  | exact S 19 50 3 cell_19_50_3
  | exact S 19 50 4 cell_19_50_4
  | exact S 19 50 5 cell_19_50_5
theorem cell_19_51_0 : C 19 51 0 := by decide +kernel
theorem cell_19_51_1 : C 19 51 1 := by decide +kernel
theorem cell_19_51_2 : C 19 51 2 := by decide +kernel
theorem cell_19_51_3 : C 19 51 3 := by decide +kernel
theorem cell_19_51_4 : C 19 51 4 := by decide +kernel
theorem cell_19_51_5 : C 19 51 5 := by decide +kernel
theorem row_19_51 : ThresholdAt 19 51 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 51 0 cell_19_51_0
  | exact S 19 51 1 cell_19_51_1
  | exact S 19 51 2 cell_19_51_2
  | exact S 19 51 3 cell_19_51_3
  | exact S 19 51 4 cell_19_51_4
  | exact S 19 51 5 cell_19_51_5
theorem cell_19_52_0 : C 19 52 0 := by decide +kernel
theorem cell_19_52_1 : C 19 52 1 := by decide +kernel
theorem cell_19_52_2 : C 19 52 2 := by decide +kernel
theorem cell_19_52_3 : C 19 52 3 := by decide +kernel
theorem cell_19_52_4 : C 19 52 4 := by decide +kernel
theorem cell_19_52_5 : C 19 52 5 := by decide +kernel
theorem row_19_52 : ThresholdAt 19 52 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 52 0 cell_19_52_0
  | exact S 19 52 1 cell_19_52_1
  | exact S 19 52 2 cell_19_52_2
  | exact S 19 52 3 cell_19_52_3
  | exact S 19 52 4 cell_19_52_4
  | exact S 19 52 5 cell_19_52_5
theorem cell_19_53_0 : C 19 53 0 := by decide +kernel
theorem cell_19_53_1 : C 19 53 1 := by decide +kernel
theorem cell_19_53_2 : C 19 53 2 := by decide +kernel
theorem cell_19_53_3 : C 19 53 3 := by decide +kernel
theorem cell_19_53_4 : C 19 53 4 := by decide +kernel
theorem cell_19_53_5 : C 19 53 5 := by decide +kernel
theorem row_19_53 : ThresholdAt 19 53 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 53 0 cell_19_53_0
  | exact S 19 53 1 cell_19_53_1
  | exact S 19 53 2 cell_19_53_2
  | exact S 19 53 3 cell_19_53_3
  | exact S 19 53 4 cell_19_53_4
  | exact S 19 53 5 cell_19_53_5
theorem cell_19_54_0 : C 19 54 0 := by decide +kernel
theorem cell_19_54_1 : C 19 54 1 := by decide +kernel
theorem cell_19_54_2 : C 19 54 2 := by decide +kernel
theorem cell_19_54_3 : C 19 54 3 := by decide +kernel
theorem cell_19_54_4 : C 19 54 4 := by decide +kernel
theorem cell_19_54_5 : C 19 54 5 := by decide +kernel
theorem row_19_54 : ThresholdAt 19 54 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 54 0 cell_19_54_0
  | exact S 19 54 1 cell_19_54_1
  | exact S 19 54 2 cell_19_54_2
  | exact S 19 54 3 cell_19_54_3
  | exact S 19 54 4 cell_19_54_4
  | exact S 19 54 5 cell_19_54_5
theorem cell_19_55_0 : C 19 55 0 := by decide +kernel
theorem cell_19_55_1 : C 19 55 1 := by decide +kernel
theorem cell_19_55_2 : C 19 55 2 := by decide +kernel
theorem cell_19_55_3 : C 19 55 3 := by decide +kernel
theorem cell_19_55_4 : C 19 55 4 := by decide +kernel
theorem cell_19_55_5 : C 19 55 5 := by decide +kernel
theorem row_19_55 : ThresholdAt 19 55 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 55 0 cell_19_55_0
  | exact S 19 55 1 cell_19_55_1
  | exact S 19 55 2 cell_19_55_2
  | exact S 19 55 3 cell_19_55_3
  | exact S 19 55 4 cell_19_55_4
  | exact S 19 55 5 cell_19_55_5
theorem cell_19_56_0 : C 19 56 0 := by decide +kernel
theorem cell_19_56_1 : C 19 56 1 := by decide +kernel
theorem cell_19_56_2 : C 19 56 2 := by decide +kernel
theorem cell_19_56_3 : C 19 56 3 := by decide +kernel
theorem cell_19_56_4 : C 19 56 4 := by decide +kernel
theorem cell_19_56_5 : C 19 56 5 := by decide +kernel
theorem row_19_56 : ThresholdAt 19 56 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 56 0 cell_19_56_0
  | exact S 19 56 1 cell_19_56_1
  | exact S 19 56 2 cell_19_56_2
  | exact S 19 56 3 cell_19_56_3
  | exact S 19 56 4 cell_19_56_4
  | exact S 19 56 5 cell_19_56_5
theorem cell_19_57_0 : C 19 57 0 := by decide +kernel
theorem cell_19_57_1 : C 19 57 1 := by decide +kernel
theorem cell_19_57_2 : C 19 57 2 := by decide +kernel
theorem cell_19_57_3 : C 19 57 3 := by decide +kernel
theorem cell_19_57_4 : C 19 57 4 := by decide +kernel
theorem cell_19_57_5 : C 19 57 5 := by decide +kernel
theorem row_19_57 : ThresholdAt 19 57 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 57 0 cell_19_57_0
  | exact S 19 57 1 cell_19_57_1
  | exact S 19 57 2 cell_19_57_2
  | exact S 19 57 3 cell_19_57_3
  | exact S 19 57 4 cell_19_57_4
  | exact S 19 57 5 cell_19_57_5
theorem cell_19_58_0 : C 19 58 0 := by decide +kernel
theorem cell_19_58_1 : C 19 58 1 := by decide +kernel
theorem cell_19_58_2 : C 19 58 2 := by decide +kernel
theorem cell_19_58_3 : C 19 58 3 := by decide +kernel
theorem cell_19_58_4 : C 19 58 4 := by decide +kernel
theorem cell_19_58_5 : C 19 58 5 := by decide +kernel
theorem row_19_58 : ThresholdAt 19 58 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 58 0 cell_19_58_0
  | exact S 19 58 1 cell_19_58_1
  | exact S 19 58 2 cell_19_58_2
  | exact S 19 58 3 cell_19_58_3
  | exact S 19 58 4 cell_19_58_4
  | exact S 19 58 5 cell_19_58_5
theorem cell_19_59_0 : C 19 59 0 := by decide +kernel
theorem cell_19_59_1 : C 19 59 1 := by decide +kernel
theorem cell_19_59_2 : C 19 59 2 := by decide +kernel
theorem cell_19_59_3 : C 19 59 3 := by decide +kernel
theorem cell_19_59_4 : C 19 59 4 := by decide +kernel
theorem cell_19_59_5 : C 19 59 5 := by decide +kernel
theorem row_19_59 : ThresholdAt 19 59 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 59 0 cell_19_59_0
  | exact S 19 59 1 cell_19_59_1
  | exact S 19 59 2 cell_19_59_2
  | exact S 19 59 3 cell_19_59_3
  | exact S 19 59 4 cell_19_59_4
  | exact S 19 59 5 cell_19_59_5
theorem cell_19_60_0 : C 19 60 0 := by decide +kernel
theorem cell_19_60_1 : C 19 60 1 := by decide +kernel
theorem cell_19_60_2 : C 19 60 2 := by decide +kernel
theorem cell_19_60_3 : C 19 60 3 := by decide +kernel
theorem cell_19_60_4 : C 19 60 4 := by decide +kernel
theorem cell_19_60_5 : C 19 60 5 := by decide +kernel
theorem row_19_60 : ThresholdAt 19 60 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 60 0 cell_19_60_0
  | exact S 19 60 1 cell_19_60_1
  | exact S 19 60 2 cell_19_60_2
  | exact S 19 60 3 cell_19_60_3
  | exact S 19 60 4 cell_19_60_4
  | exact S 19 60 5 cell_19_60_5
theorem cell_19_61_0 : C 19 61 0 := by decide +kernel
theorem cell_19_61_1 : C 19 61 1 := by decide +kernel
theorem cell_19_61_2 : C 19 61 2 := by decide +kernel
theorem cell_19_61_3 : C 19 61 3 := by decide +kernel
theorem cell_19_61_4 : C 19 61 4 := by decide +kernel
theorem cell_19_61_5 : C 19 61 5 := by decide +kernel
theorem row_19_61 : ThresholdAt 19 61 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 61 0 cell_19_61_0
  | exact S 19 61 1 cell_19_61_1
  | exact S 19 61 2 cell_19_61_2
  | exact S 19 61 3 cell_19_61_3
  | exact S 19 61 4 cell_19_61_4
  | exact S 19 61 5 cell_19_61_5
theorem cell_19_62_0 : C 19 62 0 := by decide +kernel
theorem cell_19_62_1 : C 19 62 1 := by decide +kernel
theorem cell_19_62_2 : C 19 62 2 := by decide +kernel
theorem cell_19_62_3 : C 19 62 3 := by decide +kernel
theorem cell_19_62_4 : C 19 62 4 := by decide +kernel
theorem cell_19_62_5 : C 19 62 5 := by decide +kernel
theorem row_19_62 : ThresholdAt 19 62 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 62 0 cell_19_62_0
  | exact S 19 62 1 cell_19_62_1
  | exact S 19 62 2 cell_19_62_2
  | exact S 19 62 3 cell_19_62_3
  | exact S 19 62 4 cell_19_62_4
  | exact S 19 62 5 cell_19_62_5
theorem cell_19_63_0 : C 19 63 0 := by decide +kernel
theorem cell_19_63_1 : C 19 63 1 := by decide +kernel
theorem cell_19_63_2 : C 19 63 2 := by decide +kernel
theorem cell_19_63_3 : C 19 63 3 := by decide +kernel
theorem cell_19_63_4 : C 19 63 4 := by decide +kernel
theorem cell_19_63_5 : C 19 63 5 := by decide +kernel
theorem row_19_63 : ThresholdAt 19 63 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 63 0 cell_19_63_0
  | exact S 19 63 1 cell_19_63_1
  | exact S 19 63 2 cell_19_63_2
  | exact S 19 63 3 cell_19_63_3
  | exact S 19 63 4 cell_19_63_4
  | exact S 19 63 5 cell_19_63_5
theorem cell_19_64_0 : C 19 64 0 := by decide +kernel
theorem cell_19_64_1 : C 19 64 1 := by decide +kernel
theorem cell_19_64_2 : C 19 64 2 := by decide +kernel
theorem cell_19_64_3 : C 19 64 3 := by decide +kernel
theorem cell_19_64_4 : C 19 64 4 := by decide +kernel
theorem cell_19_64_5 : C 19 64 5 := by decide +kernel
theorem row_19_64 : ThresholdAt 19 64 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 64 0 cell_19_64_0
  | exact S 19 64 1 cell_19_64_1
  | exact S 19 64 2 cell_19_64_2
  | exact S 19 64 3 cell_19_64_3
  | exact S 19 64 4 cell_19_64_4
  | exact S 19 64 5 cell_19_64_5
theorem cell_19_65_0 : C 19 65 0 := by decide +kernel
theorem cell_19_65_1 : C 19 65 1 := by decide +kernel
theorem cell_19_65_2 : C 19 65 2 := by decide +kernel
theorem cell_19_65_3 : C 19 65 3 := by decide +kernel
theorem cell_19_65_4 : C 19 65 4 := by decide +kernel
theorem cell_19_65_5 : C 19 65 5 := by decide +kernel
theorem row_19_65 : ThresholdAt 19 65 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 65 0 cell_19_65_0
  | exact S 19 65 1 cell_19_65_1
  | exact S 19 65 2 cell_19_65_2
  | exact S 19 65 3 cell_19_65_3
  | exact S 19 65 4 cell_19_65_4
  | exact S 19 65 5 cell_19_65_5
theorem cell_19_66_0 : C 19 66 0 := by decide +kernel
theorem cell_19_66_1 : C 19 66 1 := by decide +kernel
theorem cell_19_66_2 : C 19 66 2 := by decide +kernel
theorem cell_19_66_3 : C 19 66 3 := by decide +kernel
theorem cell_19_66_4 : C 19 66 4 := by decide +kernel
theorem cell_19_66_5 : C 19 66 5 := by decide +kernel
theorem row_19_66 : ThresholdAt 19 66 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 66 0 cell_19_66_0
  | exact S 19 66 1 cell_19_66_1
  | exact S 19 66 2 cell_19_66_2
  | exact S 19 66 3 cell_19_66_3
  | exact S 19 66 4 cell_19_66_4
  | exact S 19 66 5 cell_19_66_5
theorem cell_19_67_0 : C 19 67 0 := by decide +kernel
theorem cell_19_67_1 : C 19 67 1 := by decide +kernel
theorem cell_19_67_2 : C 19 67 2 := by decide +kernel
theorem cell_19_67_3 : C 19 67 3 := by decide +kernel
theorem cell_19_67_4 : C 19 67 4 := by decide +kernel
theorem cell_19_67_5 : C 19 67 5 := by decide +kernel
theorem row_19_67 : ThresholdAt 19 67 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 67 0 cell_19_67_0
  | exact S 19 67 1 cell_19_67_1
  | exact S 19 67 2 cell_19_67_2
  | exact S 19 67 3 cell_19_67_3
  | exact S 19 67 4 cell_19_67_4
  | exact S 19 67 5 cell_19_67_5
theorem cell_19_68_0 : C 19 68 0 := by decide +kernel
theorem cell_19_68_1 : C 19 68 1 := by decide +kernel
theorem cell_19_68_2 : C 19 68 2 := by decide +kernel
theorem cell_19_68_3 : C 19 68 3 := by decide +kernel
theorem cell_19_68_4 : C 19 68 4 := by decide +kernel
theorem cell_19_68_5 : C 19 68 5 := by decide +kernel
theorem row_19_68 : ThresholdAt 19 68 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 68 0 cell_19_68_0
  | exact S 19 68 1 cell_19_68_1
  | exact S 19 68 2 cell_19_68_2
  | exact S 19 68 3 cell_19_68_3
  | exact S 19 68 4 cell_19_68_4
  | exact S 19 68 5 cell_19_68_5
theorem cell_19_69_0 : C 19 69 0 := by decide +kernel
theorem cell_19_69_1 : C 19 69 1 := by decide +kernel
theorem cell_19_69_2 : C 19 69 2 := by decide +kernel
theorem cell_19_69_3 : C 19 69 3 := by decide +kernel
theorem cell_19_69_4 : C 19 69 4 := by decide +kernel
theorem cell_19_69_5 : C 19 69 5 := by decide +kernel
theorem row_19_69 : ThresholdAt 19 69 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 69 0 cell_19_69_0
  | exact S 19 69 1 cell_19_69_1
  | exact S 19 69 2 cell_19_69_2
  | exact S 19 69 3 cell_19_69_3
  | exact S 19 69 4 cell_19_69_4
  | exact S 19 69 5 cell_19_69_5
theorem cell_19_70_0 : C 19 70 0 := by decide +kernel
theorem cell_19_70_1 : C 19 70 1 := by decide +kernel
theorem cell_19_70_2 : C 19 70 2 := by decide +kernel
theorem cell_19_70_3 : C 19 70 3 := by decide +kernel
theorem cell_19_70_4 : C 19 70 4 := by decide +kernel
theorem cell_19_70_5 : C 19 70 5 := by decide +kernel
theorem row_19_70 : ThresholdAt 19 70 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 70 0 cell_19_70_0
  | exact S 19 70 1 cell_19_70_1
  | exact S 19 70 2 cell_19_70_2
  | exact S 19 70 3 cell_19_70_3
  | exact S 19 70 4 cell_19_70_4
  | exact S 19 70 5 cell_19_70_5
theorem cell_19_71_0 : C 19 71 0 := by decide +kernel
theorem cell_19_71_1 : C 19 71 1 := by decide +kernel
theorem cell_19_71_2 : C 19 71 2 := by decide +kernel
theorem cell_19_71_3 : C 19 71 3 := by decide +kernel
theorem cell_19_71_4 : C 19 71 4 := by decide +kernel
theorem cell_19_71_5 : C 19 71 5 := by decide +kernel
theorem row_19_71 : ThresholdAt 19 71 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 71 0 cell_19_71_0
  | exact S 19 71 1 cell_19_71_1
  | exact S 19 71 2 cell_19_71_2
  | exact S 19 71 3 cell_19_71_3
  | exact S 19 71 4 cell_19_71_4
  | exact S 19 71 5 cell_19_71_5
theorem cell_19_72_0 : C 19 72 0 := by decide +kernel
theorem cell_19_72_1 : C 19 72 1 := by decide +kernel
theorem cell_19_72_2 : C 19 72 2 := by decide +kernel
theorem cell_19_72_3 : C 19 72 3 := by decide +kernel
theorem cell_19_72_4 : C 19 72 4 := by decide +kernel
theorem cell_19_72_5 : C 19 72 5 := by decide +kernel
theorem row_19_72 : ThresholdAt 19 72 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 72 0 cell_19_72_0
  | exact S 19 72 1 cell_19_72_1
  | exact S 19 72 2 cell_19_72_2
  | exact S 19 72 3 cell_19_72_3
  | exact S 19 72 4 cell_19_72_4
  | exact S 19 72 5 cell_19_72_5
theorem cell_19_73_0 : C 19 73 0 := by decide +kernel
theorem cell_19_73_1 : C 19 73 1 := by decide +kernel
theorem cell_19_73_2 : C 19 73 2 := by decide +kernel
theorem cell_19_73_3 : C 19 73 3 := by decide +kernel
theorem cell_19_73_4 : C 19 73 4 := by decide +kernel
theorem cell_19_73_5 : C 19 73 5 := by decide +kernel
theorem row_19_73 : ThresholdAt 19 73 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 73 0 cell_19_73_0
  | exact S 19 73 1 cell_19_73_1
  | exact S 19 73 2 cell_19_73_2
  | exact S 19 73 3 cell_19_73_3
  | exact S 19 73 4 cell_19_73_4
  | exact S 19 73 5 cell_19_73_5
theorem cell_19_74_0 : C 19 74 0 := by decide +kernel
theorem cell_19_74_1 : C 19 74 1 := by decide +kernel
theorem cell_19_74_2 : C 19 74 2 := by decide +kernel
theorem cell_19_74_3 : C 19 74 3 := by decide +kernel
theorem cell_19_74_4 : C 19 74 4 := by decide +kernel
theorem cell_19_74_5 : C 19 74 5 := by decide +kernel
theorem row_19_74 : ThresholdAt 19 74 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 74 0 cell_19_74_0
  | exact S 19 74 1 cell_19_74_1
  | exact S 19 74 2 cell_19_74_2
  | exact S 19 74 3 cell_19_74_3
  | exact S 19 74 4 cell_19_74_4
  | exact S 19 74 5 cell_19_74_5
theorem cell_19_75_0 : C 19 75 0 := by decide +kernel
theorem cell_19_75_1 : C 19 75 1 := by decide +kernel
theorem cell_19_75_2 : C 19 75 2 := by decide +kernel
theorem cell_19_75_3 : C 19 75 3 := by decide +kernel
theorem cell_19_75_4 : C 19 75 4 := by decide +kernel
theorem cell_19_75_5 : C 19 75 5 := by decide +kernel
theorem row_19_75 : ThresholdAt 19 75 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 75 0 cell_19_75_0
  | exact S 19 75 1 cell_19_75_1
  | exact S 19 75 2 cell_19_75_2
  | exact S 19 75 3 cell_19_75_3
  | exact S 19 75 4 cell_19_75_4
  | exact S 19 75 5 cell_19_75_5
theorem cell_19_76_0 : C 19 76 0 := by decide +kernel
theorem cell_19_76_1 : C 19 76 1 := by decide +kernel
theorem cell_19_76_2 : C 19 76 2 := by decide +kernel
theorem cell_19_76_3 : C 19 76 3 := by decide +kernel
theorem cell_19_76_4 : C 19 76 4 := by decide +kernel
theorem cell_19_76_5 : C 19 76 5 := by decide +kernel
theorem row_19_76 : ThresholdAt 19 76 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 76 0 cell_19_76_0
  | exact S 19 76 1 cell_19_76_1
  | exact S 19 76 2 cell_19_76_2
  | exact S 19 76 3 cell_19_76_3
  | exact S 19 76 4 cell_19_76_4
  | exact S 19 76 5 cell_19_76_5
theorem cell_19_77_0 : C 19 77 0 := by decide +kernel
theorem cell_19_77_1 : C 19 77 1 := by decide +kernel
theorem cell_19_77_2 : C 19 77 2 := by decide +kernel
theorem cell_19_77_3 : C 19 77 3 := by decide +kernel
theorem cell_19_77_4 : C 19 77 4 := by decide +kernel
theorem cell_19_77_5 : C 19 77 5 := by decide +kernel
theorem row_19_77 : ThresholdAt 19 77 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 77 0 cell_19_77_0
  | exact S 19 77 1 cell_19_77_1
  | exact S 19 77 2 cell_19_77_2
  | exact S 19 77 3 cell_19_77_3
  | exact S 19 77 4 cell_19_77_4
  | exact S 19 77 5 cell_19_77_5
theorem cell_19_78_0 : C 19 78 0 := by decide +kernel
theorem cell_19_78_1 : C 19 78 1 := by decide +kernel
theorem cell_19_78_2 : C 19 78 2 := by decide +kernel
theorem cell_19_78_3 : C 19 78 3 := by decide +kernel
theorem cell_19_78_4 : C 19 78 4 := by decide +kernel
theorem cell_19_78_5 : C 19 78 5 := by decide +kernel
theorem row_19_78 : ThresholdAt 19 78 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 78 0 cell_19_78_0
  | exact S 19 78 1 cell_19_78_1
  | exact S 19 78 2 cell_19_78_2
  | exact S 19 78 3 cell_19_78_3
  | exact S 19 78 4 cell_19_78_4
  | exact S 19 78 5 cell_19_78_5
theorem cell_19_79_0 : C 19 79 0 := by decide +kernel
theorem cell_19_79_1 : C 19 79 1 := by decide +kernel
theorem cell_19_79_2 : C 19 79 2 := by decide +kernel
theorem cell_19_79_3 : C 19 79 3 := by decide +kernel
theorem cell_19_79_4 : C 19 79 4 := by decide +kernel
theorem cell_19_79_5 : C 19 79 5 := by decide +kernel
theorem row_19_79 : ThresholdAt 19 79 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 79 0 cell_19_79_0
  | exact S 19 79 1 cell_19_79_1
  | exact S 19 79 2 cell_19_79_2
  | exact S 19 79 3 cell_19_79_3
  | exact S 19 79 4 cell_19_79_4
  | exact S 19 79 5 cell_19_79_5
theorem cell_19_80_0 : C 19 80 0 := by decide +kernel
theorem cell_19_80_1 : C 19 80 1 := by decide +kernel
theorem cell_19_80_2 : C 19 80 2 := by decide +kernel
theorem cell_19_80_3 : C 19 80 3 := by decide +kernel
theorem cell_19_80_4 : C 19 80 4 := by decide +kernel
theorem cell_19_80_5 : C 19 80 5 := by decide +kernel
theorem row_19_80 : ThresholdAt 19 80 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 80 0 cell_19_80_0
  | exact S 19 80 1 cell_19_80_1
  | exact S 19 80 2 cell_19_80_2
  | exact S 19 80 3 cell_19_80_3
  | exact S 19 80 4 cell_19_80_4
  | exact S 19 80 5 cell_19_80_5
theorem cell_19_81_0 : C 19 81 0 := by decide +kernel
theorem cell_19_81_1 : C 19 81 1 := by decide +kernel
theorem cell_19_81_2 : C 19 81 2 := by decide +kernel
theorem cell_19_81_3 : C 19 81 3 := by decide +kernel
theorem cell_19_81_4 : C 19 81 4 := by decide +kernel
theorem cell_19_81_5 : C 19 81 5 := by decide +kernel
theorem row_19_81 : ThresholdAt 19 81 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 81 0 cell_19_81_0
  | exact S 19 81 1 cell_19_81_1
  | exact S 19 81 2 cell_19_81_2
  | exact S 19 81 3 cell_19_81_3
  | exact S 19 81 4 cell_19_81_4
  | exact S 19 81 5 cell_19_81_5
theorem cell_19_82_0 : C 19 82 0 := by decide +kernel
theorem cell_19_82_1 : C 19 82 1 := by decide +kernel
theorem cell_19_82_2 : C 19 82 2 := by decide +kernel
theorem cell_19_82_3 : C 19 82 3 := by decide +kernel
theorem cell_19_82_4 : C 19 82 4 := by decide +kernel
theorem cell_19_82_5 : C 19 82 5 := by decide +kernel
theorem row_19_82 : ThresholdAt 19 82 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 82 0 cell_19_82_0
  | exact S 19 82 1 cell_19_82_1
  | exact S 19 82 2 cell_19_82_2
  | exact S 19 82 3 cell_19_82_3
  | exact S 19 82 4 cell_19_82_4
  | exact S 19 82 5 cell_19_82_5
theorem cell_19_83_0 : C 19 83 0 := by decide +kernel
theorem cell_19_83_1 : C 19 83 1 := by decide +kernel
theorem cell_19_83_2 : C 19 83 2 := by decide +kernel
theorem cell_19_83_3 : C 19 83 3 := by decide +kernel
theorem cell_19_83_4 : C 19 83 4 := by decide +kernel
theorem cell_19_83_5 : C 19 83 5 := by decide +kernel
theorem row_19_83 : ThresholdAt 19 83 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 83 0 cell_19_83_0
  | exact S 19 83 1 cell_19_83_1
  | exact S 19 83 2 cell_19_83_2
  | exact S 19 83 3 cell_19_83_3
  | exact S 19 83 4 cell_19_83_4
  | exact S 19 83 5 cell_19_83_5
theorem cell_19_84_0 : C 19 84 0 := by decide +kernel
theorem cell_19_84_1 : C 19 84 1 := by decide +kernel
theorem cell_19_84_2 : C 19 84 2 := by decide +kernel
theorem cell_19_84_3 : C 19 84 3 := by decide +kernel
theorem cell_19_84_4 : C 19 84 4 := by decide +kernel
theorem cell_19_84_5 : C 19 84 5 := by decide +kernel
theorem row_19_84 : ThresholdAt 19 84 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 84 0 cell_19_84_0
  | exact S 19 84 1 cell_19_84_1
  | exact S 19 84 2 cell_19_84_2
  | exact S 19 84 3 cell_19_84_3
  | exact S 19 84 4 cell_19_84_4
  | exact S 19 84 5 cell_19_84_5
theorem cell_19_85_0 : C 19 85 0 := by decide +kernel
theorem cell_19_85_1 : C 19 85 1 := by decide +kernel
theorem cell_19_85_2 : C 19 85 2 := by decide +kernel
theorem cell_19_85_3 : C 19 85 3 := by decide +kernel
theorem cell_19_85_4 : C 19 85 4 := by decide +kernel
theorem cell_19_85_5 : C 19 85 5 := by decide +kernel
theorem row_19_85 : ThresholdAt 19 85 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 85 0 cell_19_85_0
  | exact S 19 85 1 cell_19_85_1
  | exact S 19 85 2 cell_19_85_2
  | exact S 19 85 3 cell_19_85_3
  | exact S 19 85 4 cell_19_85_4
  | exact S 19 85 5 cell_19_85_5
theorem cell_19_86_0 : C 19 86 0 := by decide +kernel
theorem cell_19_86_1 : C 19 86 1 := by decide +kernel
theorem cell_19_86_2 : C 19 86 2 := by decide +kernel
theorem cell_19_86_3 : C 19 86 3 := by decide +kernel
theorem cell_19_86_4 : C 19 86 4 := by decide +kernel
theorem cell_19_86_5 : C 19 86 5 := by decide +kernel
theorem row_19_86 : ThresholdAt 19 86 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 86 0 cell_19_86_0
  | exact S 19 86 1 cell_19_86_1
  | exact S 19 86 2 cell_19_86_2
  | exact S 19 86 3 cell_19_86_3
  | exact S 19 86 4 cell_19_86_4
  | exact S 19 86 5 cell_19_86_5
theorem cell_19_87_0 : C 19 87 0 := by decide +kernel
theorem cell_19_87_1 : C 19 87 1 := by decide +kernel
theorem cell_19_87_2 : C 19 87 2 := by decide +kernel
theorem cell_19_87_3 : C 19 87 3 := by decide +kernel
theorem cell_19_87_4 : C 19 87 4 := by decide +kernel
theorem cell_19_87_5 : C 19 87 5 := by decide +kernel
theorem row_19_87 : ThresholdAt 19 87 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 87 0 cell_19_87_0
  | exact S 19 87 1 cell_19_87_1
  | exact S 19 87 2 cell_19_87_2
  | exact S 19 87 3 cell_19_87_3
  | exact S 19 87 4 cell_19_87_4
  | exact S 19 87 5 cell_19_87_5
theorem cell_19_88_0 : C 19 88 0 := by decide +kernel
theorem cell_19_88_1 : C 19 88 1 := by decide +kernel
theorem cell_19_88_2 : C 19 88 2 := by decide +kernel
theorem cell_19_88_3 : C 19 88 3 := by decide +kernel
theorem cell_19_88_4 : C 19 88 4 := by decide +kernel
theorem cell_19_88_5 : C 19 88 5 := by decide +kernel
theorem row_19_88 : ThresholdAt 19 88 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 88 0 cell_19_88_0
  | exact S 19 88 1 cell_19_88_1
  | exact S 19 88 2 cell_19_88_2
  | exact S 19 88 3 cell_19_88_3
  | exact S 19 88 4 cell_19_88_4
  | exact S 19 88 5 cell_19_88_5
theorem cell_19_89_0 : C 19 89 0 := by decide +kernel
theorem cell_19_89_1 : C 19 89 1 := by decide +kernel
theorem cell_19_89_2 : C 19 89 2 := by decide +kernel
theorem cell_19_89_3 : C 19 89 3 := by decide +kernel
theorem cell_19_89_4 : C 19 89 4 := by decide +kernel
theorem cell_19_89_5 : C 19 89 5 := by decide +kernel
theorem row_19_89 : ThresholdAt 19 89 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 89 0 cell_19_89_0
  | exact S 19 89 1 cell_19_89_1
  | exact S 19 89 2 cell_19_89_2
  | exact S 19 89 3 cell_19_89_3
  | exact S 19 89 4 cell_19_89_4
  | exact S 19 89 5 cell_19_89_5
theorem cell_19_90_0 : C 19 90 0 := by decide +kernel
theorem cell_19_90_1 : C 19 90 1 := by decide +kernel
theorem cell_19_90_2 : C 19 90 2 := by decide +kernel
theorem cell_19_90_3 : C 19 90 3 := by decide +kernel
theorem cell_19_90_4 : C 19 90 4 := by decide +kernel
theorem cell_19_90_5 : C 19 90 5 := by decide +kernel
theorem row_19_90 : ThresholdAt 19 90 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 90 0 cell_19_90_0
  | exact S 19 90 1 cell_19_90_1
  | exact S 19 90 2 cell_19_90_2
  | exact S 19 90 3 cell_19_90_3
  | exact S 19 90 4 cell_19_90_4
  | exact S 19 90 5 cell_19_90_5
theorem cell_19_91_0 : C 19 91 0 := by decide +kernel
theorem cell_19_91_1 : C 19 91 1 := by decide +kernel
theorem cell_19_91_2 : C 19 91 2 := by decide +kernel
theorem cell_19_91_3 : C 19 91 3 := by decide +kernel
theorem cell_19_91_4 : C 19 91 4 := by decide +kernel
theorem cell_19_91_5 : C 19 91 5 := by decide +kernel
theorem row_19_91 : ThresholdAt 19 91 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 91 0 cell_19_91_0
  | exact S 19 91 1 cell_19_91_1
  | exact S 19 91 2 cell_19_91_2
  | exact S 19 91 3 cell_19_91_3
  | exact S 19 91 4 cell_19_91_4
  | exact S 19 91 5 cell_19_91_5
theorem cell_19_92_0 : C 19 92 0 := by decide +kernel
theorem cell_19_92_1 : C 19 92 1 := by decide +kernel
theorem cell_19_92_2 : C 19 92 2 := by decide +kernel
theorem cell_19_92_3 : C 19 92 3 := by decide +kernel
theorem cell_19_92_4 : C 19 92 4 := by decide +kernel
theorem cell_19_92_5 : C 19 92 5 := by decide +kernel
theorem row_19_92 : ThresholdAt 19 92 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 92 0 cell_19_92_0
  | exact S 19 92 1 cell_19_92_1
  | exact S 19 92 2 cell_19_92_2
  | exact S 19 92 3 cell_19_92_3
  | exact S 19 92 4 cell_19_92_4
  | exact S 19 92 5 cell_19_92_5
theorem cell_19_93_0 : C 19 93 0 := by decide +kernel
theorem cell_19_93_1 : C 19 93 1 := by decide +kernel
theorem cell_19_93_2 : C 19 93 2 := by decide +kernel
theorem cell_19_93_3 : C 19 93 3 := by decide +kernel
theorem cell_19_93_4 : C 19 93 4 := by decide +kernel
theorem cell_19_93_5 : C 19 93 5 := by decide +kernel
theorem row_19_93 : ThresholdAt 19 93 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 93 0 cell_19_93_0
  | exact S 19 93 1 cell_19_93_1
  | exact S 19 93 2 cell_19_93_2
  | exact S 19 93 3 cell_19_93_3
  | exact S 19 93 4 cell_19_93_4
  | exact S 19 93 5 cell_19_93_5
theorem cell_19_94_0 : C 19 94 0 := by decide +kernel
theorem cell_19_94_1 : C 19 94 1 := by decide +kernel
theorem cell_19_94_2 : C 19 94 2 := by decide +kernel
theorem cell_19_94_3 : C 19 94 3 := by decide +kernel
theorem cell_19_94_4 : C 19 94 4 := by decide +kernel
theorem cell_19_94_5 : C 19 94 5 := by decide +kernel
theorem row_19_94 : ThresholdAt 19 94 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 94 0 cell_19_94_0
  | exact S 19 94 1 cell_19_94_1
  | exact S 19 94 2 cell_19_94_2
  | exact S 19 94 3 cell_19_94_3
  | exact S 19 94 4 cell_19_94_4
  | exact S 19 94 5 cell_19_94_5
theorem cell_19_95_0 : C 19 95 0 := by decide +kernel
theorem cell_19_95_1 : C 19 95 1 := by decide +kernel
theorem cell_19_95_2 : C 19 95 2 := by decide +kernel
theorem cell_19_95_3 : C 19 95 3 := by decide +kernel
theorem cell_19_95_4 : C 19 95 4 := by decide +kernel
theorem cell_19_95_5 : C 19 95 5 := by decide +kernel
theorem row_19_95 : ThresholdAt 19 95 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 95 0 cell_19_95_0
  | exact S 19 95 1 cell_19_95_1
  | exact S 19 95 2 cell_19_95_2
  | exact S 19 95 3 cell_19_95_3
  | exact S 19 95 4 cell_19_95_4
  | exact S 19 95 5 cell_19_95_5
theorem cell_19_96_0 : C 19 96 0 := by decide +kernel
theorem cell_19_96_1 : C 19 96 1 := by decide +kernel
theorem cell_19_96_2 : C 19 96 2 := by decide +kernel
theorem cell_19_96_3 : C 19 96 3 := by decide +kernel
theorem cell_19_96_4 : C 19 96 4 := by decide +kernel
theorem cell_19_96_5 : C 19 96 5 := by decide +kernel
theorem row_19_96 : ThresholdAt 19 96 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 96 0 cell_19_96_0
  | exact S 19 96 1 cell_19_96_1
  | exact S 19 96 2 cell_19_96_2
  | exact S 19 96 3 cell_19_96_3
  | exact S 19 96 4 cell_19_96_4
  | exact S 19 96 5 cell_19_96_5
theorem cell_19_97_0 : C 19 97 0 := by decide +kernel
theorem cell_19_97_1 : C 19 97 1 := by decide +kernel
theorem cell_19_97_2 : C 19 97 2 := by decide +kernel
theorem cell_19_97_3 : C 19 97 3 := by decide +kernel
theorem cell_19_97_4 : C 19 97 4 := by decide +kernel
theorem cell_19_97_5 : C 19 97 5 := by decide +kernel
theorem row_19_97 : ThresholdAt 19 97 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 97 0 cell_19_97_0
  | exact S 19 97 1 cell_19_97_1
  | exact S 19 97 2 cell_19_97_2
  | exact S 19 97 3 cell_19_97_3
  | exact S 19 97 4 cell_19_97_4
  | exact S 19 97 5 cell_19_97_5
theorem cell_19_98_0 : C 19 98 0 := by decide +kernel
theorem cell_19_98_1 : C 19 98 1 := by decide +kernel
theorem cell_19_98_2 : C 19 98 2 := by decide +kernel
theorem cell_19_98_3 : C 19 98 3 := by decide +kernel
theorem cell_19_98_4 : C 19 98 4 := by decide +kernel
theorem cell_19_98_5 : C 19 98 5 := by decide +kernel
theorem row_19_98 : ThresholdAt 19 98 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 98 0 cell_19_98_0
  | exact S 19 98 1 cell_19_98_1
  | exact S 19 98 2 cell_19_98_2
  | exact S 19 98 3 cell_19_98_3
  | exact S 19 98 4 cell_19_98_4
  | exact S 19 98 5 cell_19_98_5
theorem cell_19_99_0 : C 19 99 0 := by decide +kernel
theorem cell_19_99_1 : C 19 99 1 := by decide +kernel
theorem cell_19_99_2 : C 19 99 2 := by decide +kernel
theorem cell_19_99_3 : C 19 99 3 := by decide +kernel
theorem cell_19_99_4 : C 19 99 4 := by decide +kernel
theorem cell_19_99_5 : C 19 99 5 := by decide +kernel
theorem row_19_99 : ThresholdAt 19 99 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 99 0 cell_19_99_0
  | exact S 19 99 1 cell_19_99_1
  | exact S 19 99 2 cell_19_99_2
  | exact S 19 99 3 cell_19_99_3
  | exact S 19 99 4 cell_19_99_4
  | exact S 19 99 5 cell_19_99_5
theorem cell_19_100_0 : C 19 100 0 := by decide +kernel
theorem cell_19_100_1 : C 19 100 1 := by decide +kernel
theorem cell_19_100_2 : C 19 100 2 := by decide +kernel
theorem cell_19_100_3 : C 19 100 3 := by decide +kernel
theorem cell_19_100_4 : C 19 100 4 := by decide +kernel
theorem cell_19_100_5 : C 19 100 5 := by decide +kernel
theorem row_19_100 : ThresholdAt 19 100 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 100 0 cell_19_100_0
  | exact S 19 100 1 cell_19_100_1
  | exact S 19 100 2 cell_19_100_2
  | exact S 19 100 3 cell_19_100_3
  | exact S 19 100 4 cell_19_100_4
  | exact S 19 100 5 cell_19_100_5
theorem cell_19_101_0 : C 19 101 0 := by decide +kernel
theorem cell_19_101_1 : C 19 101 1 := by decide +kernel
theorem cell_19_101_2 : C 19 101 2 := by decide +kernel
theorem cell_19_101_3 : C 19 101 3 := by decide +kernel
theorem cell_19_101_4 : C 19 101 4 := by decide +kernel
theorem cell_19_101_5 : C 19 101 5 := by decide +kernel
theorem row_19_101 : ThresholdAt 19 101 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 101 0 cell_19_101_0
  | exact S 19 101 1 cell_19_101_1
  | exact S 19 101 2 cell_19_101_2
  | exact S 19 101 3 cell_19_101_3
  | exact S 19 101 4 cell_19_101_4
  | exact S 19 101 5 cell_19_101_5
theorem cell_19_102_0 : C 19 102 0 := by decide +kernel
theorem cell_19_102_1 : C 19 102 1 := by decide +kernel
theorem cell_19_102_2 : C 19 102 2 := by decide +kernel
theorem cell_19_102_3 : C 19 102 3 := by decide +kernel
theorem cell_19_102_4 : C 19 102 4 := by decide +kernel
theorem cell_19_102_5 : C 19 102 5 := by decide +kernel
theorem row_19_102 : ThresholdAt 19 102 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 102 0 cell_19_102_0
  | exact S 19 102 1 cell_19_102_1
  | exact S 19 102 2 cell_19_102_2
  | exact S 19 102 3 cell_19_102_3
  | exact S 19 102 4 cell_19_102_4
  | exact S 19 102 5 cell_19_102_5
theorem cell_19_103_0 : C 19 103 0 := by decide +kernel
theorem cell_19_103_1 : C 19 103 1 := by decide +kernel
theorem cell_19_103_2 : C 19 103 2 := by decide +kernel
theorem cell_19_103_3 : C 19 103 3 := by decide +kernel
theorem cell_19_103_4 : C 19 103 4 := by decide +kernel
theorem cell_19_103_5 : C 19 103 5 := by decide +kernel
theorem row_19_103 : ThresholdAt 19 103 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 103 0 cell_19_103_0
  | exact S 19 103 1 cell_19_103_1
  | exact S 19 103 2 cell_19_103_2
  | exact S 19 103 3 cell_19_103_3
  | exact S 19 103 4 cell_19_103_4
  | exact S 19 103 5 cell_19_103_5
theorem cell_19_104_0 : C 19 104 0 := by decide +kernel
theorem cell_19_104_1 : C 19 104 1 := by decide +kernel
theorem cell_19_104_2 : C 19 104 2 := by decide +kernel
theorem cell_19_104_3 : C 19 104 3 := by decide +kernel
theorem cell_19_104_4 : C 19 104 4 := by decide +kernel
theorem cell_19_104_5 : C 19 104 5 := by decide +kernel
theorem row_19_104 : ThresholdAt 19 104 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 104 0 cell_19_104_0
  | exact S 19 104 1 cell_19_104_1
  | exact S 19 104 2 cell_19_104_2
  | exact S 19 104 3 cell_19_104_3
  | exact S 19 104 4 cell_19_104_4
  | exact S 19 104 5 cell_19_104_5
theorem cell_19_105_0 : C 19 105 0 := by decide +kernel
theorem cell_19_105_1 : C 19 105 1 := by decide +kernel
theorem cell_19_105_2 : C 19 105 2 := by decide +kernel
theorem cell_19_105_3 : C 19 105 3 := by decide +kernel
theorem cell_19_105_4 : C 19 105 4 := by decide +kernel
theorem cell_19_105_5 : C 19 105 5 := by decide +kernel
theorem row_19_105 : ThresholdAt 19 105 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 105 0 cell_19_105_0
  | exact S 19 105 1 cell_19_105_1
  | exact S 19 105 2 cell_19_105_2
  | exact S 19 105 3 cell_19_105_3
  | exact S 19 105 4 cell_19_105_4
  | exact S 19 105 5 cell_19_105_5
theorem cell_19_106_0 : C 19 106 0 := by decide +kernel
theorem cell_19_106_1 : C 19 106 1 := by decide +kernel
theorem cell_19_106_2 : C 19 106 2 := by decide +kernel
theorem cell_19_106_3 : C 19 106 3 := by decide +kernel
theorem cell_19_106_4 : C 19 106 4 := by decide +kernel
theorem cell_19_106_5 : C 19 106 5 := by decide +kernel
theorem row_19_106 : ThresholdAt 19 106 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 106 0 cell_19_106_0
  | exact S 19 106 1 cell_19_106_1
  | exact S 19 106 2 cell_19_106_2
  | exact S 19 106 3 cell_19_106_3
  | exact S 19 106 4 cell_19_106_4
  | exact S 19 106 5 cell_19_106_5
theorem cell_19_107_0 : C 19 107 0 := by decide +kernel
theorem cell_19_107_1 : C 19 107 1 := by decide +kernel
theorem cell_19_107_2 : C 19 107 2 := by decide +kernel
theorem cell_19_107_3 : C 19 107 3 := by decide +kernel
theorem cell_19_107_4 : C 19 107 4 := by decide +kernel
theorem cell_19_107_5 : C 19 107 5 := by decide +kernel
theorem row_19_107 : ThresholdAt 19 107 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 107 0 cell_19_107_0
  | exact S 19 107 1 cell_19_107_1
  | exact S 19 107 2 cell_19_107_2
  | exact S 19 107 3 cell_19_107_3
  | exact S 19 107 4 cell_19_107_4
  | exact S 19 107 5 cell_19_107_5
theorem cell_19_108_0 : C 19 108 0 := by decide +kernel
theorem cell_19_108_1 : C 19 108 1 := by decide +kernel
theorem cell_19_108_2 : C 19 108 2 := by decide +kernel
theorem cell_19_108_3 : C 19 108 3 := by decide +kernel
theorem cell_19_108_4 : C 19 108 4 := by decide +kernel
theorem cell_19_108_5 : C 19 108 5 := by decide +kernel
theorem row_19_108 : ThresholdAt 19 108 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 108 0 cell_19_108_0
  | exact S 19 108 1 cell_19_108_1
  | exact S 19 108 2 cell_19_108_2
  | exact S 19 108 3 cell_19_108_3
  | exact S 19 108 4 cell_19_108_4
  | exact S 19 108 5 cell_19_108_5
theorem cell_19_109_0 : C 19 109 0 := by decide +kernel
theorem cell_19_109_1 : C 19 109 1 := by decide +kernel
theorem cell_19_109_2 : C 19 109 2 := by decide +kernel
theorem cell_19_109_3 : C 19 109 3 := by decide +kernel
theorem cell_19_109_4 : C 19 109 4 := by decide +kernel
theorem cell_19_109_5 : C 19 109 5 := by decide +kernel
theorem row_19_109 : ThresholdAt 19 109 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 109 0 cell_19_109_0
  | exact S 19 109 1 cell_19_109_1
  | exact S 19 109 2 cell_19_109_2
  | exact S 19 109 3 cell_19_109_3
  | exact S 19 109 4 cell_19_109_4
  | exact S 19 109 5 cell_19_109_5
theorem cell_19_110_0 : C 19 110 0 := by decide +kernel
theorem cell_19_110_1 : C 19 110 1 := by decide +kernel
theorem cell_19_110_2 : C 19 110 2 := by decide +kernel
theorem cell_19_110_3 : C 19 110 3 := by decide +kernel
theorem cell_19_110_4 : C 19 110 4 := by decide +kernel
theorem cell_19_110_5 : C 19 110 5 := by decide +kernel
theorem row_19_110 : ThresholdAt 19 110 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 110 0 cell_19_110_0
  | exact S 19 110 1 cell_19_110_1
  | exact S 19 110 2 cell_19_110_2
  | exact S 19 110 3 cell_19_110_3
  | exact S 19 110 4 cell_19_110_4
  | exact S 19 110 5 cell_19_110_5
theorem cell_19_111_0 : C 19 111 0 := by decide +kernel
theorem cell_19_111_1 : C 19 111 1 := by decide +kernel
theorem cell_19_111_2 : C 19 111 2 := by decide +kernel
theorem cell_19_111_3 : C 19 111 3 := by decide +kernel
theorem cell_19_111_4 : C 19 111 4 := by decide +kernel
theorem cell_19_111_5 : C 19 111 5 := by decide +kernel
theorem row_19_111 : ThresholdAt 19 111 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 111 0 cell_19_111_0
  | exact S 19 111 1 cell_19_111_1
  | exact S 19 111 2 cell_19_111_2
  | exact S 19 111 3 cell_19_111_3
  | exact S 19 111 4 cell_19_111_4
  | exact S 19 111 5 cell_19_111_5
theorem cell_19_112_0 : C 19 112 0 := by decide +kernel
theorem cell_19_112_1 : C 19 112 1 := by decide +kernel
theorem cell_19_112_2 : C 19 112 2 := by decide +kernel
theorem cell_19_112_3 : C 19 112 3 := by decide +kernel
theorem cell_19_112_4 : C 19 112 4 := by decide +kernel
theorem cell_19_112_5 : C 19 112 5 := by decide +kernel
theorem row_19_112 : ThresholdAt 19 112 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 112 0 cell_19_112_0
  | exact S 19 112 1 cell_19_112_1
  | exact S 19 112 2 cell_19_112_2
  | exact S 19 112 3 cell_19_112_3
  | exact S 19 112 4 cell_19_112_4
  | exact S 19 112 5 cell_19_112_5
theorem cell_19_113_0 : C 19 113 0 := by decide +kernel
theorem cell_19_113_1 : C 19 113 1 := by decide +kernel
theorem cell_19_113_2 : C 19 113 2 := by decide +kernel
theorem cell_19_113_3 : C 19 113 3 := by decide +kernel
theorem cell_19_113_4 : C 19 113 4 := by decide +kernel
theorem cell_19_113_5 : C 19 113 5 := by decide +kernel
theorem row_19_113 : ThresholdAt 19 113 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 113 0 cell_19_113_0
  | exact S 19 113 1 cell_19_113_1
  | exact S 19 113 2 cell_19_113_2
  | exact S 19 113 3 cell_19_113_3
  | exact S 19 113 4 cell_19_113_4
  | exact S 19 113 5 cell_19_113_5
theorem cell_19_114_0 : C 19 114 0 := by decide +kernel
theorem cell_19_114_1 : C 19 114 1 := by decide +kernel
theorem cell_19_114_2 : C 19 114 2 := by decide +kernel
theorem cell_19_114_3 : C 19 114 3 := by decide +kernel
theorem cell_19_114_4 : C 19 114 4 := by decide +kernel
theorem cell_19_114_5 : C 19 114 5 := by decide +kernel
theorem row_19_114 : ThresholdAt 19 114 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 114 0 cell_19_114_0
  | exact S 19 114 1 cell_19_114_1
  | exact S 19 114 2 cell_19_114_2
  | exact S 19 114 3 cell_19_114_3
  | exact S 19 114 4 cell_19_114_4
  | exact S 19 114 5 cell_19_114_5
theorem cell_19_115_0 : C 19 115 0 := by decide +kernel
theorem cell_19_115_1 : C 19 115 1 := by decide +kernel
theorem cell_19_115_2 : C 19 115 2 := by decide +kernel
theorem cell_19_115_3 : C 19 115 3 := by decide +kernel
theorem cell_19_115_4 : C 19 115 4 := by decide +kernel
theorem cell_19_115_5 : C 19 115 5 := by decide +kernel
theorem row_19_115 : ThresholdAt 19 115 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 115 0 cell_19_115_0
  | exact S 19 115 1 cell_19_115_1
  | exact S 19 115 2 cell_19_115_2
  | exact S 19 115 3 cell_19_115_3
  | exact S 19 115 4 cell_19_115_4
  | exact S 19 115 5 cell_19_115_5
theorem cell_19_116_0 : C 19 116 0 := by decide +kernel
theorem cell_19_116_1 : C 19 116 1 := by decide +kernel
theorem cell_19_116_2 : C 19 116 2 := by decide +kernel
theorem cell_19_116_3 : C 19 116 3 := by decide +kernel
theorem cell_19_116_4 : C 19 116 4 := by decide +kernel
theorem cell_19_116_5 : C 19 116 5 := by decide +kernel
theorem row_19_116 : ThresholdAt 19 116 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 116 0 cell_19_116_0
  | exact S 19 116 1 cell_19_116_1
  | exact S 19 116 2 cell_19_116_2
  | exact S 19 116 3 cell_19_116_3
  | exact S 19 116 4 cell_19_116_4
  | exact S 19 116 5 cell_19_116_5
theorem cell_19_117_0 : C 19 117 0 := by decide +kernel
theorem cell_19_117_1 : C 19 117 1 := by decide +kernel
theorem cell_19_117_2 : C 19 117 2 := by decide +kernel
theorem cell_19_117_3 : C 19 117 3 := by decide +kernel
theorem cell_19_117_4 : C 19 117 4 := by decide +kernel
theorem cell_19_117_5 : C 19 117 5 := by decide +kernel
theorem row_19_117 : ThresholdAt 19 117 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 117 0 cell_19_117_0
  | exact S 19 117 1 cell_19_117_1
  | exact S 19 117 2 cell_19_117_2
  | exact S 19 117 3 cell_19_117_3
  | exact S 19 117 4 cell_19_117_4
  | exact S 19 117 5 cell_19_117_5
theorem cell_19_118_0 : C 19 118 0 := by decide +kernel
theorem cell_19_118_1 : C 19 118 1 := by decide +kernel
theorem cell_19_118_2 : C 19 118 2 := by decide +kernel
theorem cell_19_118_3 : C 19 118 3 := by decide +kernel
theorem cell_19_118_4 : C 19 118 4 := by decide +kernel
theorem cell_19_118_5 : C 19 118 5 := by decide +kernel
theorem row_19_118 : ThresholdAt 19 118 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 118 0 cell_19_118_0
  | exact S 19 118 1 cell_19_118_1
  | exact S 19 118 2 cell_19_118_2
  | exact S 19 118 3 cell_19_118_3
  | exact S 19 118 4 cell_19_118_4
  | exact S 19 118 5 cell_19_118_5
theorem cell_19_119_0 : C 19 119 0 := by decide +kernel
theorem cell_19_119_1 : C 19 119 1 := by decide +kernel
theorem cell_19_119_2 : C 19 119 2 := by decide +kernel
theorem cell_19_119_3 : C 19 119 3 := by decide +kernel
theorem cell_19_119_4 : C 19 119 4 := by decide +kernel
theorem cell_19_119_5 : C 19 119 5 := by decide +kernel
theorem row_19_119 : ThresholdAt 19 119 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 119 0 cell_19_119_0
  | exact S 19 119 1 cell_19_119_1
  | exact S 19 119 2 cell_19_119_2
  | exact S 19 119 3 cell_19_119_3
  | exact S 19 119 4 cell_19_119_4
  | exact S 19 119 5 cell_19_119_5
theorem cell_19_120_0 : C 19 120 0 := by decide +kernel
theorem cell_19_120_1 : C 19 120 1 := by decide +kernel
theorem cell_19_120_2 : C 19 120 2 := by decide +kernel
theorem cell_19_120_3 : C 19 120 3 := by decide +kernel
theorem cell_19_120_4 : C 19 120 4 := by decide +kernel
theorem cell_19_120_5 : C 19 120 5 := by decide +kernel
theorem row_19_120 : ThresholdAt 19 120 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 19 120 0 cell_19_120_0
  | exact S 19 120 1 cell_19_120_1
  | exact S 19 120 2 cell_19_120_2
  | exact S 19 120 3 cell_19_120_3
  | exact S 19 120 4 cell_19_120_4
  | exact S 19 120 5 cell_19_120_5
theorem checkedR19 : ∀ V ∈ List.range 121, ThresholdAt 19 V := by
  intro V hV
  have hv : V < 121 := List.mem_range.mp hV
  by_cases h0_121 : V < 60
  · by_cases h0_60 : V < 30
    · by_cases h0_30 : V < 15
      · by_cases h0_15 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have he : V = 0 := by omega
              subst V
              exact row_19_0
            · by_cases h1_3 : V < 2
              · have he : V = 1 := by omega
                subst V
                exact row_19_1
              · have he : V = 2 := by omega
                subst V
                exact row_19_2
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have he : V = 3 := by omega
                subst V
                exact row_19_3
              · have he : V = 4 := by omega
                subst V
                exact row_19_4
            · by_cases h5_7 : V < 6
              · have he : V = 5 := by omega
                subst V
                exact row_19_5
              · have he : V = 6 := by omega
                subst V
                exact row_19_6
        · by_cases h7_15 : V < 11
          · by_cases h7_11 : V < 9
            · by_cases h7_9 : V < 8
              · have he : V = 7 := by omega
                subst V
                exact row_19_7
              · have he : V = 8 := by omega
                subst V
                exact row_19_8
            · by_cases h9_11 : V < 10
              · have he : V = 9 := by omega
                subst V
                exact row_19_9
              · have he : V = 10 := by omega
                subst V
                exact row_19_10
          · by_cases h11_15 : V < 13
            · by_cases h11_13 : V < 12
              · have he : V = 11 := by omega
                subst V
                exact row_19_11
              · have he : V = 12 := by omega
                subst V
                exact row_19_12
            · by_cases h13_15 : V < 14
              · have he : V = 13 := by omega
                subst V
                exact row_19_13
              · have he : V = 14 := by omega
                subst V
                exact row_19_14
      · by_cases h15_30 : V < 22
        · by_cases h15_22 : V < 18
          · by_cases h15_18 : V < 16
            · have he : V = 15 := by omega
              subst V
              exact row_19_15
            · by_cases h16_18 : V < 17
              · have he : V = 16 := by omega
                subst V
                exact row_19_16
              · have he : V = 17 := by omega
                subst V
                exact row_19_17
          · by_cases h18_22 : V < 20
            · by_cases h18_20 : V < 19
              · have he : V = 18 := by omega
                subst V
                exact row_19_18
              · have he : V = 19 := by omega
                subst V
                exact row_19_19
            · by_cases h20_22 : V < 21
              · have he : V = 20 := by omega
                subst V
                exact row_19_20
              · have he : V = 21 := by omega
                subst V
                exact row_19_21
        · by_cases h22_30 : V < 26
          · by_cases h22_26 : V < 24
            · by_cases h22_24 : V < 23
              · have he : V = 22 := by omega
                subst V
                exact row_19_22
              · have he : V = 23 := by omega
                subst V
                exact row_19_23
            · by_cases h24_26 : V < 25
              · have he : V = 24 := by omega
                subst V
                exact row_19_24
              · have he : V = 25 := by omega
                subst V
                exact row_19_25
          · by_cases h26_30 : V < 28
            · by_cases h26_28 : V < 27
              · have he : V = 26 := by omega
                subst V
                exact row_19_26
              · have he : V = 27 := by omega
                subst V
                exact row_19_27
            · by_cases h28_30 : V < 29
              · have he : V = 28 := by omega
                subst V
                exact row_19_28
              · have he : V = 29 := by omega
                subst V
                exact row_19_29
    · by_cases h30_60 : V < 45
      · by_cases h30_45 : V < 37
        · by_cases h30_37 : V < 33
          · by_cases h30_33 : V < 31
            · have he : V = 30 := by omega
              subst V
              exact row_19_30
            · by_cases h31_33 : V < 32
              · have he : V = 31 := by omega
                subst V
                exact row_19_31
              · have he : V = 32 := by omega
                subst V
                exact row_19_32
          · by_cases h33_37 : V < 35
            · by_cases h33_35 : V < 34
              · have he : V = 33 := by omega
                subst V
                exact row_19_33
              · have he : V = 34 := by omega
                subst V
                exact row_19_34
            · by_cases h35_37 : V < 36
              · have he : V = 35 := by omega
                subst V
                exact row_19_35
              · have he : V = 36 := by omega
                subst V
                exact row_19_36
        · by_cases h37_45 : V < 41
          · by_cases h37_41 : V < 39
            · by_cases h37_39 : V < 38
              · have he : V = 37 := by omega
                subst V
                exact row_19_37
              · have he : V = 38 := by omega
                subst V
                exact row_19_38
            · by_cases h39_41 : V < 40
              · have he : V = 39 := by omega
                subst V
                exact row_19_39
              · have he : V = 40 := by omega
                subst V
                exact row_19_40
          · by_cases h41_45 : V < 43
            · by_cases h41_43 : V < 42
              · have he : V = 41 := by omega
                subst V
                exact row_19_41
              · have he : V = 42 := by omega
                subst V
                exact row_19_42
            · by_cases h43_45 : V < 44
              · have he : V = 43 := by omega
                subst V
                exact row_19_43
              · have he : V = 44 := by omega
                subst V
                exact row_19_44
      · by_cases h45_60 : V < 52
        · by_cases h45_52 : V < 48
          · by_cases h45_48 : V < 46
            · have he : V = 45 := by omega
              subst V
              exact row_19_45
            · by_cases h46_48 : V < 47
              · have he : V = 46 := by omega
                subst V
                exact row_19_46
              · have he : V = 47 := by omega
                subst V
                exact row_19_47
          · by_cases h48_52 : V < 50
            · by_cases h48_50 : V < 49
              · have he : V = 48 := by omega
                subst V
                exact row_19_48
              · have he : V = 49 := by omega
                subst V
                exact row_19_49
            · by_cases h50_52 : V < 51
              · have he : V = 50 := by omega
                subst V
                exact row_19_50
              · have he : V = 51 := by omega
                subst V
                exact row_19_51
        · by_cases h52_60 : V < 56
          · by_cases h52_56 : V < 54
            · by_cases h52_54 : V < 53
              · have he : V = 52 := by omega
                subst V
                exact row_19_52
              · have he : V = 53 := by omega
                subst V
                exact row_19_53
            · by_cases h54_56 : V < 55
              · have he : V = 54 := by omega
                subst V
                exact row_19_54
              · have he : V = 55 := by omega
                subst V
                exact row_19_55
          · by_cases h56_60 : V < 58
            · by_cases h56_58 : V < 57
              · have he : V = 56 := by omega
                subst V
                exact row_19_56
              · have he : V = 57 := by omega
                subst V
                exact row_19_57
            · by_cases h58_60 : V < 59
              · have he : V = 58 := by omega
                subst V
                exact row_19_58
              · have he : V = 59 := by omega
                subst V
                exact row_19_59
  · by_cases h60_121 : V < 90
    · by_cases h60_90 : V < 75
      · by_cases h60_75 : V < 67
        · by_cases h60_67 : V < 63
          · by_cases h60_63 : V < 61
            · have he : V = 60 := by omega
              subst V
              exact row_19_60
            · by_cases h61_63 : V < 62
              · have he : V = 61 := by omega
                subst V
                exact row_19_61
              · have he : V = 62 := by omega
                subst V
                exact row_19_62
          · by_cases h63_67 : V < 65
            · by_cases h63_65 : V < 64
              · have he : V = 63 := by omega
                subst V
                exact row_19_63
              · have he : V = 64 := by omega
                subst V
                exact row_19_64
            · by_cases h65_67 : V < 66
              · have he : V = 65 := by omega
                subst V
                exact row_19_65
              · have he : V = 66 := by omega
                subst V
                exact row_19_66
        · by_cases h67_75 : V < 71
          · by_cases h67_71 : V < 69
            · by_cases h67_69 : V < 68
              · have he : V = 67 := by omega
                subst V
                exact row_19_67
              · have he : V = 68 := by omega
                subst V
                exact row_19_68
            · by_cases h69_71 : V < 70
              · have he : V = 69 := by omega
                subst V
                exact row_19_69
              · have he : V = 70 := by omega
                subst V
                exact row_19_70
          · by_cases h71_75 : V < 73
            · by_cases h71_73 : V < 72
              · have he : V = 71 := by omega
                subst V
                exact row_19_71
              · have he : V = 72 := by omega
                subst V
                exact row_19_72
            · by_cases h73_75 : V < 74
              · have he : V = 73 := by omega
                subst V
                exact row_19_73
              · have he : V = 74 := by omega
                subst V
                exact row_19_74
      · by_cases h75_90 : V < 82
        · by_cases h75_82 : V < 78
          · by_cases h75_78 : V < 76
            · have he : V = 75 := by omega
              subst V
              exact row_19_75
            · by_cases h76_78 : V < 77
              · have he : V = 76 := by omega
                subst V
                exact row_19_76
              · have he : V = 77 := by omega
                subst V
                exact row_19_77
          · by_cases h78_82 : V < 80
            · by_cases h78_80 : V < 79
              · have he : V = 78 := by omega
                subst V
                exact row_19_78
              · have he : V = 79 := by omega
                subst V
                exact row_19_79
            · by_cases h80_82 : V < 81
              · have he : V = 80 := by omega
                subst V
                exact row_19_80
              · have he : V = 81 := by omega
                subst V
                exact row_19_81
        · by_cases h82_90 : V < 86
          · by_cases h82_86 : V < 84
            · by_cases h82_84 : V < 83
              · have he : V = 82 := by omega
                subst V
                exact row_19_82
              · have he : V = 83 := by omega
                subst V
                exact row_19_83
            · by_cases h84_86 : V < 85
              · have he : V = 84 := by omega
                subst V
                exact row_19_84
              · have he : V = 85 := by omega
                subst V
                exact row_19_85
          · by_cases h86_90 : V < 88
            · by_cases h86_88 : V < 87
              · have he : V = 86 := by omega
                subst V
                exact row_19_86
              · have he : V = 87 := by omega
                subst V
                exact row_19_87
            · by_cases h88_90 : V < 89
              · have he : V = 88 := by omega
                subst V
                exact row_19_88
              · have he : V = 89 := by omega
                subst V
                exact row_19_89
    · by_cases h90_121 : V < 105
      · by_cases h90_105 : V < 97
        · by_cases h90_97 : V < 93
          · by_cases h90_93 : V < 91
            · have he : V = 90 := by omega
              subst V
              exact row_19_90
            · by_cases h91_93 : V < 92
              · have he : V = 91 := by omega
                subst V
                exact row_19_91
              · have he : V = 92 := by omega
                subst V
                exact row_19_92
          · by_cases h93_97 : V < 95
            · by_cases h93_95 : V < 94
              · have he : V = 93 := by omega
                subst V
                exact row_19_93
              · have he : V = 94 := by omega
                subst V
                exact row_19_94
            · by_cases h95_97 : V < 96
              · have he : V = 95 := by omega
                subst V
                exact row_19_95
              · have he : V = 96 := by omega
                subst V
                exact row_19_96
        · by_cases h97_105 : V < 101
          · by_cases h97_101 : V < 99
            · by_cases h97_99 : V < 98
              · have he : V = 97 := by omega
                subst V
                exact row_19_97
              · have he : V = 98 := by omega
                subst V
                exact row_19_98
            · by_cases h99_101 : V < 100
              · have he : V = 99 := by omega
                subst V
                exact row_19_99
              · have he : V = 100 := by omega
                subst V
                exact row_19_100
          · by_cases h101_105 : V < 103
            · by_cases h101_103 : V < 102
              · have he : V = 101 := by omega
                subst V
                exact row_19_101
              · have he : V = 102 := by omega
                subst V
                exact row_19_102
            · by_cases h103_105 : V < 104
              · have he : V = 103 := by omega
                subst V
                exact row_19_103
              · have he : V = 104 := by omega
                subst V
                exact row_19_104
      · by_cases h105_121 : V < 113
        · by_cases h105_113 : V < 109
          · by_cases h105_109 : V < 107
            · by_cases h105_107 : V < 106
              · have he : V = 105 := by omega
                subst V
                exact row_19_105
              · have he : V = 106 := by omega
                subst V
                exact row_19_106
            · by_cases h107_109 : V < 108
              · have he : V = 107 := by omega
                subst V
                exact row_19_107
              · have he : V = 108 := by omega
                subst V
                exact row_19_108
          · by_cases h109_113 : V < 111
            · by_cases h109_111 : V < 110
              · have he : V = 109 := by omega
                subst V
                exact row_19_109
              · have he : V = 110 := by omega
                subst V
                exact row_19_110
            · by_cases h111_113 : V < 112
              · have he : V = 111 := by omega
                subst V
                exact row_19_111
              · have he : V = 112 := by omega
                subst V
                exact row_19_112
        · by_cases h113_121 : V < 117
          · by_cases h113_117 : V < 115
            · by_cases h113_115 : V < 114
              · have he : V = 113 := by omega
                subst V
                exact row_19_113
              · have he : V = 114 := by omega
                subst V
                exact row_19_114
            · by_cases h115_117 : V < 116
              · have he : V = 115 := by omega
                subst V
                exact row_19_115
              · have he : V = 116 := by omega
                subst V
                exact row_19_116
          · by_cases h117_121 : V < 119
            · by_cases h117_119 : V < 118
              · have he : V = 117 := by omega
                subst V
                exact row_19_117
              · have he : V = 118 := by omega
                subst V
                exact row_19_118
            · by_cases h119_121 : V < 120
              · have he : V = 119 := by omega
                subst V
                exact row_19_119
              · have he : V = 120 := by omega
                subst V
                exact row_19_120
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
