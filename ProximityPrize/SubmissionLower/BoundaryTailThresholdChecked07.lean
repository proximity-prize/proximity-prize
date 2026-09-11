import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked06

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_7_0_0 : C 7 0 0 := by decide +kernel
theorem cell_7_0_1 : C 7 0 1 := by decide +kernel
theorem cell_7_0_2 : C 7 0 2 := by decide +kernel
theorem cell_7_0_3 : C 7 0 3 := by decide +kernel
theorem cell_7_0_4 : C 7 0 4 := by decide +kernel
theorem cell_7_0_5 : C 7 0 5 := by decide +kernel
theorem row_7_0 : ThresholdAt 7 0 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 0 0 cell_7_0_0
  | exact S 7 0 1 cell_7_0_1
  | exact S 7 0 2 cell_7_0_2
  | exact S 7 0 3 cell_7_0_3
  | exact S 7 0 4 cell_7_0_4
  | exact S 7 0 5 cell_7_0_5
theorem cell_7_1_0 : C 7 1 0 := by decide +kernel
theorem cell_7_1_1 : C 7 1 1 := by decide +kernel
theorem cell_7_1_2 : C 7 1 2 := by decide +kernel
theorem cell_7_1_3 : C 7 1 3 := by decide +kernel
theorem cell_7_1_4 : C 7 1 4 := by decide +kernel
theorem cell_7_1_5 : C 7 1 5 := by decide +kernel
theorem row_7_1 : ThresholdAt 7 1 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 1 0 cell_7_1_0
  | exact S 7 1 1 cell_7_1_1
  | exact S 7 1 2 cell_7_1_2
  | exact S 7 1 3 cell_7_1_3
  | exact S 7 1 4 cell_7_1_4
  | exact S 7 1 5 cell_7_1_5
theorem cell_7_2_0 : C 7 2 0 := by decide +kernel
theorem cell_7_2_1 : C 7 2 1 := by decide +kernel
theorem cell_7_2_2 : C 7 2 2 := by decide +kernel
theorem cell_7_2_3 : C 7 2 3 := by decide +kernel
theorem cell_7_2_4 : C 7 2 4 := by decide +kernel
theorem cell_7_2_5 : C 7 2 5 := by decide +kernel
theorem row_7_2 : ThresholdAt 7 2 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 2 0 cell_7_2_0
  | exact S 7 2 1 cell_7_2_1
  | exact S 7 2 2 cell_7_2_2
  | exact S 7 2 3 cell_7_2_3
  | exact S 7 2 4 cell_7_2_4
  | exact S 7 2 5 cell_7_2_5
theorem cell_7_3_0 : C 7 3 0 := by decide +kernel
theorem cell_7_3_1 : C 7 3 1 := by decide +kernel
theorem cell_7_3_2 : C 7 3 2 := by decide +kernel
theorem cell_7_3_3 : C 7 3 3 := by decide +kernel
theorem cell_7_3_4 : C 7 3 4 := by decide +kernel
theorem cell_7_3_5 : C 7 3 5 := by decide +kernel
theorem row_7_3 : ThresholdAt 7 3 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 3 0 cell_7_3_0
  | exact S 7 3 1 cell_7_3_1
  | exact S 7 3 2 cell_7_3_2
  | exact S 7 3 3 cell_7_3_3
  | exact S 7 3 4 cell_7_3_4
  | exact S 7 3 5 cell_7_3_5
theorem cell_7_4_0 : C 7 4 0 := by decide +kernel
theorem cell_7_4_1 : C 7 4 1 := by decide +kernel
theorem cell_7_4_2 : C 7 4 2 := by decide +kernel
theorem cell_7_4_3 : C 7 4 3 := by decide +kernel
theorem cell_7_4_4 : C 7 4 4 := by decide +kernel
theorem cell_7_4_5 : C 7 4 5 := by decide +kernel
theorem row_7_4 : ThresholdAt 7 4 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 4 0 cell_7_4_0
  | exact S 7 4 1 cell_7_4_1
  | exact S 7 4 2 cell_7_4_2
  | exact S 7 4 3 cell_7_4_3
  | exact S 7 4 4 cell_7_4_4
  | exact S 7 4 5 cell_7_4_5
theorem cell_7_5_0 : C 7 5 0 := by decide +kernel
theorem cell_7_5_1 : C 7 5 1 := by decide +kernel
theorem cell_7_5_2 : C 7 5 2 := by decide +kernel
theorem cell_7_5_3 : C 7 5 3 := by decide +kernel
theorem cell_7_5_4 : C 7 5 4 := by decide +kernel
theorem cell_7_5_5 : C 7 5 5 := by decide +kernel
theorem row_7_5 : ThresholdAt 7 5 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 5 0 cell_7_5_0
  | exact S 7 5 1 cell_7_5_1
  | exact S 7 5 2 cell_7_5_2
  | exact S 7 5 3 cell_7_5_3
  | exact S 7 5 4 cell_7_5_4
  | exact S 7 5 5 cell_7_5_5
theorem cell_7_6_0 : C 7 6 0 := by decide +kernel
theorem cell_7_6_1 : C 7 6 1 := by decide +kernel
theorem cell_7_6_2 : C 7 6 2 := by decide +kernel
theorem cell_7_6_3 : C 7 6 3 := by decide +kernel
theorem cell_7_6_4 : C 7 6 4 := by decide +kernel
theorem cell_7_6_5 : C 7 6 5 := by decide +kernel
theorem row_7_6 : ThresholdAt 7 6 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 6 0 cell_7_6_0
  | exact S 7 6 1 cell_7_6_1
  | exact S 7 6 2 cell_7_6_2
  | exact S 7 6 3 cell_7_6_3
  | exact S 7 6 4 cell_7_6_4
  | exact S 7 6 5 cell_7_6_5
theorem cell_7_7_0 : C 7 7 0 := by decide +kernel
theorem cell_7_7_1 : C 7 7 1 := by decide +kernel
theorem cell_7_7_2 : C 7 7 2 := by decide +kernel
theorem cell_7_7_3 : C 7 7 3 := by decide +kernel
theorem cell_7_7_4 : C 7 7 4 := by decide +kernel
theorem cell_7_7_5 : C 7 7 5 := by decide +kernel
theorem row_7_7 : ThresholdAt 7 7 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 7 0 cell_7_7_0
  | exact S 7 7 1 cell_7_7_1
  | exact S 7 7 2 cell_7_7_2
  | exact S 7 7 3 cell_7_7_3
  | exact S 7 7 4 cell_7_7_4
  | exact S 7 7 5 cell_7_7_5
theorem cell_7_8_0 : C 7 8 0 := by decide +kernel
theorem cell_7_8_1 : C 7 8 1 := by decide +kernel
theorem cell_7_8_2 : C 7 8 2 := by decide +kernel
theorem cell_7_8_3 : C 7 8 3 := by decide +kernel
theorem cell_7_8_4 : C 7 8 4 := by decide +kernel
theorem cell_7_8_5 : C 7 8 5 := by decide +kernel
theorem row_7_8 : ThresholdAt 7 8 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 8 0 cell_7_8_0
  | exact S 7 8 1 cell_7_8_1
  | exact S 7 8 2 cell_7_8_2
  | exact S 7 8 3 cell_7_8_3
  | exact S 7 8 4 cell_7_8_4
  | exact S 7 8 5 cell_7_8_5
theorem cell_7_9_0 : C 7 9 0 := by decide +kernel
theorem cell_7_9_1 : C 7 9 1 := by decide +kernel
theorem cell_7_9_2 : C 7 9 2 := by decide +kernel
theorem cell_7_9_3 : C 7 9 3 := by decide +kernel
theorem cell_7_9_4 : C 7 9 4 := by decide +kernel
theorem cell_7_9_5 : C 7 9 5 := by decide +kernel
theorem row_7_9 : ThresholdAt 7 9 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 9 0 cell_7_9_0
  | exact S 7 9 1 cell_7_9_1
  | exact S 7 9 2 cell_7_9_2
  | exact S 7 9 3 cell_7_9_3
  | exact S 7 9 4 cell_7_9_4
  | exact S 7 9 5 cell_7_9_5
theorem cell_7_10_0 : C 7 10 0 := by decide +kernel
theorem cell_7_10_1 : C 7 10 1 := by decide +kernel
theorem cell_7_10_2 : C 7 10 2 := by decide +kernel
theorem cell_7_10_3 : C 7 10 3 := by decide +kernel
theorem cell_7_10_4 : C 7 10 4 := by decide +kernel
theorem cell_7_10_5 : C 7 10 5 := by decide +kernel
theorem row_7_10 : ThresholdAt 7 10 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 10 0 cell_7_10_0
  | exact S 7 10 1 cell_7_10_1
  | exact S 7 10 2 cell_7_10_2
  | exact S 7 10 3 cell_7_10_3
  | exact S 7 10 4 cell_7_10_4
  | exact S 7 10 5 cell_7_10_5
theorem cell_7_11_0 : C 7 11 0 := by decide +kernel
theorem cell_7_11_1 : C 7 11 1 := by decide +kernel
theorem cell_7_11_2 : C 7 11 2 := by decide +kernel
theorem cell_7_11_3 : C 7 11 3 := by decide +kernel
theorem cell_7_11_4 : C 7 11 4 := by decide +kernel
theorem cell_7_11_5 : C 7 11 5 := by decide +kernel
theorem row_7_11 : ThresholdAt 7 11 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 11 0 cell_7_11_0
  | exact S 7 11 1 cell_7_11_1
  | exact S 7 11 2 cell_7_11_2
  | exact S 7 11 3 cell_7_11_3
  | exact S 7 11 4 cell_7_11_4
  | exact S 7 11 5 cell_7_11_5
theorem cell_7_12_0 : C 7 12 0 := by decide +kernel
theorem cell_7_12_1 : C 7 12 1 := by decide +kernel
theorem cell_7_12_2 : C 7 12 2 := by decide +kernel
theorem cell_7_12_3 : C 7 12 3 := by decide +kernel
theorem cell_7_12_4 : C 7 12 4 := by decide +kernel
theorem cell_7_12_5 : C 7 12 5 := by decide +kernel
theorem row_7_12 : ThresholdAt 7 12 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 12 0 cell_7_12_0
  | exact S 7 12 1 cell_7_12_1
  | exact S 7 12 2 cell_7_12_2
  | exact S 7 12 3 cell_7_12_3
  | exact S 7 12 4 cell_7_12_4
  | exact S 7 12 5 cell_7_12_5
theorem cell_7_13_0 : C 7 13 0 := by decide +kernel
theorem cell_7_13_1 : C 7 13 1 := by decide +kernel
theorem cell_7_13_2 : C 7 13 2 := by decide +kernel
theorem cell_7_13_3 : C 7 13 3 := by decide +kernel
theorem cell_7_13_4 : C 7 13 4 := by decide +kernel
theorem cell_7_13_5 : C 7 13 5 := by decide +kernel
theorem row_7_13 : ThresholdAt 7 13 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 13 0 cell_7_13_0
  | exact S 7 13 1 cell_7_13_1
  | exact S 7 13 2 cell_7_13_2
  | exact S 7 13 3 cell_7_13_3
  | exact S 7 13 4 cell_7_13_4
  | exact S 7 13 5 cell_7_13_5
theorem cell_7_14_0 : C 7 14 0 := by decide +kernel
theorem cell_7_14_1 : C 7 14 1 := by decide +kernel
theorem cell_7_14_2 : C 7 14 2 := by decide +kernel
theorem cell_7_14_3 : C 7 14 3 := by decide +kernel
theorem cell_7_14_4 : C 7 14 4 := by decide +kernel
theorem cell_7_14_5 : C 7 14 5 := by decide +kernel
theorem row_7_14 : ThresholdAt 7 14 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 14 0 cell_7_14_0
  | exact S 7 14 1 cell_7_14_1
  | exact S 7 14 2 cell_7_14_2
  | exact S 7 14 3 cell_7_14_3
  | exact S 7 14 4 cell_7_14_4
  | exact S 7 14 5 cell_7_14_5
theorem cell_7_15_0 : C 7 15 0 := by decide +kernel
theorem cell_7_15_1 : C 7 15 1 := by decide +kernel
theorem cell_7_15_2 : C 7 15 2 := by decide +kernel
theorem cell_7_15_3 : C 7 15 3 := by decide +kernel
theorem cell_7_15_4 : C 7 15 4 := by decide +kernel
theorem cell_7_15_5 : C 7 15 5 := by decide +kernel
theorem row_7_15 : ThresholdAt 7 15 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 15 0 cell_7_15_0
  | exact S 7 15 1 cell_7_15_1
  | exact S 7 15 2 cell_7_15_2
  | exact S 7 15 3 cell_7_15_3
  | exact S 7 15 4 cell_7_15_4
  | exact S 7 15 5 cell_7_15_5
theorem cell_7_16_0 : C 7 16 0 := by decide +kernel
theorem cell_7_16_1 : C 7 16 1 := by decide +kernel
theorem cell_7_16_2 : C 7 16 2 := by decide +kernel
theorem cell_7_16_3 : C 7 16 3 := by decide +kernel
theorem cell_7_16_4 : C 7 16 4 := by decide +kernel
theorem cell_7_16_5 : C 7 16 5 := by decide +kernel
theorem row_7_16 : ThresholdAt 7 16 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 16 0 cell_7_16_0
  | exact S 7 16 1 cell_7_16_1
  | exact S 7 16 2 cell_7_16_2
  | exact S 7 16 3 cell_7_16_3
  | exact S 7 16 4 cell_7_16_4
  | exact S 7 16 5 cell_7_16_5
theorem cell_7_17_0 : C 7 17 0 := by decide +kernel
theorem cell_7_17_1 : C 7 17 1 := by decide +kernel
theorem cell_7_17_2 : C 7 17 2 := by decide +kernel
theorem cell_7_17_3 : C 7 17 3 := by decide +kernel
theorem cell_7_17_4 : C 7 17 4 := by decide +kernel
theorem cell_7_17_5 : C 7 17 5 := by decide +kernel
theorem row_7_17 : ThresholdAt 7 17 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 17 0 cell_7_17_0
  | exact S 7 17 1 cell_7_17_1
  | exact S 7 17 2 cell_7_17_2
  | exact S 7 17 3 cell_7_17_3
  | exact S 7 17 4 cell_7_17_4
  | exact S 7 17 5 cell_7_17_5
theorem cell_7_18_0 : C 7 18 0 := by decide +kernel
theorem cell_7_18_1 : C 7 18 1 := by decide +kernel
theorem cell_7_18_2 : C 7 18 2 := by decide +kernel
theorem cell_7_18_3 : C 7 18 3 := by decide +kernel
theorem cell_7_18_4 : C 7 18 4 := by decide +kernel
theorem cell_7_18_5 : C 7 18 5 := by decide +kernel
theorem row_7_18 : ThresholdAt 7 18 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 18 0 cell_7_18_0
  | exact S 7 18 1 cell_7_18_1
  | exact S 7 18 2 cell_7_18_2
  | exact S 7 18 3 cell_7_18_3
  | exact S 7 18 4 cell_7_18_4
  | exact S 7 18 5 cell_7_18_5
theorem cell_7_19_0 : C 7 19 0 := by decide +kernel
theorem cell_7_19_1 : C 7 19 1 := by decide +kernel
theorem cell_7_19_2 : C 7 19 2 := by decide +kernel
theorem cell_7_19_3 : C 7 19 3 := by decide +kernel
theorem cell_7_19_4 : C 7 19 4 := by decide +kernel
theorem cell_7_19_5 : C 7 19 5 := by decide +kernel
theorem row_7_19 : ThresholdAt 7 19 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 19 0 cell_7_19_0
  | exact S 7 19 1 cell_7_19_1
  | exact S 7 19 2 cell_7_19_2
  | exact S 7 19 3 cell_7_19_3
  | exact S 7 19 4 cell_7_19_4
  | exact S 7 19 5 cell_7_19_5
theorem cell_7_20_0 : C 7 20 0 := by decide +kernel
theorem cell_7_20_1 : C 7 20 1 := by decide +kernel
theorem cell_7_20_2 : C 7 20 2 := by decide +kernel
theorem cell_7_20_3 : C 7 20 3 := by decide +kernel
theorem cell_7_20_4 : C 7 20 4 := by decide +kernel
theorem cell_7_20_5 : C 7 20 5 := by decide +kernel
theorem row_7_20 : ThresholdAt 7 20 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 20 0 cell_7_20_0
  | exact S 7 20 1 cell_7_20_1
  | exact S 7 20 2 cell_7_20_2
  | exact S 7 20 3 cell_7_20_3
  | exact S 7 20 4 cell_7_20_4
  | exact S 7 20 5 cell_7_20_5
theorem cell_7_21_0 : C 7 21 0 := by decide +kernel
theorem cell_7_21_1 : C 7 21 1 := by decide +kernel
theorem cell_7_21_2 : C 7 21 2 := by decide +kernel
theorem cell_7_21_3 : C 7 21 3 := by decide +kernel
theorem cell_7_21_4 : C 7 21 4 := by decide +kernel
theorem cell_7_21_5 : C 7 21 5 := by decide +kernel
theorem row_7_21 : ThresholdAt 7 21 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 21 0 cell_7_21_0
  | exact S 7 21 1 cell_7_21_1
  | exact S 7 21 2 cell_7_21_2
  | exact S 7 21 3 cell_7_21_3
  | exact S 7 21 4 cell_7_21_4
  | exact S 7 21 5 cell_7_21_5
theorem cell_7_22_0 : C 7 22 0 := by decide +kernel
theorem cell_7_22_1 : C 7 22 1 := by decide +kernel
theorem cell_7_22_2 : C 7 22 2 := by decide +kernel
theorem cell_7_22_3 : C 7 22 3 := by decide +kernel
theorem cell_7_22_4 : C 7 22 4 := by decide +kernel
theorem cell_7_22_5 : C 7 22 5 := by decide +kernel
theorem row_7_22 : ThresholdAt 7 22 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 22 0 cell_7_22_0
  | exact S 7 22 1 cell_7_22_1
  | exact S 7 22 2 cell_7_22_2
  | exact S 7 22 3 cell_7_22_3
  | exact S 7 22 4 cell_7_22_4
  | exact S 7 22 5 cell_7_22_5
theorem cell_7_23_0 : C 7 23 0 := by decide +kernel
theorem cell_7_23_1 : C 7 23 1 := by decide +kernel
theorem cell_7_23_2 : C 7 23 2 := by decide +kernel
theorem cell_7_23_3 : C 7 23 3 := by decide +kernel
theorem cell_7_23_4 : C 7 23 4 := by decide +kernel
theorem cell_7_23_5 : C 7 23 5 := by decide +kernel
theorem row_7_23 : ThresholdAt 7 23 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 23 0 cell_7_23_0
  | exact S 7 23 1 cell_7_23_1
  | exact S 7 23 2 cell_7_23_2
  | exact S 7 23 3 cell_7_23_3
  | exact S 7 23 4 cell_7_23_4
  | exact S 7 23 5 cell_7_23_5
theorem cell_7_24_0 : C 7 24 0 := by decide +kernel
theorem cell_7_24_1 : C 7 24 1 := by decide +kernel
theorem cell_7_24_2 : C 7 24 2 := by decide +kernel
theorem cell_7_24_3 : C 7 24 3 := by decide +kernel
theorem cell_7_24_4 : C 7 24 4 := by decide +kernel
theorem cell_7_24_5 : C 7 24 5 := by decide +kernel
theorem row_7_24 : ThresholdAt 7 24 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 24 0 cell_7_24_0
  | exact S 7 24 1 cell_7_24_1
  | exact S 7 24 2 cell_7_24_2
  | exact S 7 24 3 cell_7_24_3
  | exact S 7 24 4 cell_7_24_4
  | exact S 7 24 5 cell_7_24_5
theorem cell_7_25_0 : C 7 25 0 := by decide +kernel
theorem cell_7_25_1 : C 7 25 1 := by decide +kernel
theorem cell_7_25_2 : C 7 25 2 := by decide +kernel
theorem cell_7_25_3 : C 7 25 3 := by decide +kernel
theorem cell_7_25_4 : C 7 25 4 := by decide +kernel
theorem cell_7_25_5 : C 7 25 5 := by decide +kernel
theorem row_7_25 : ThresholdAt 7 25 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 25 0 cell_7_25_0
  | exact S 7 25 1 cell_7_25_1
  | exact S 7 25 2 cell_7_25_2
  | exact S 7 25 3 cell_7_25_3
  | exact S 7 25 4 cell_7_25_4
  | exact S 7 25 5 cell_7_25_5
theorem cell_7_26_0 : C 7 26 0 := by decide +kernel
theorem cell_7_26_1 : C 7 26 1 := by decide +kernel
theorem cell_7_26_2 : C 7 26 2 := by decide +kernel
theorem cell_7_26_3 : C 7 26 3 := by decide +kernel
theorem cell_7_26_4 : C 7 26 4 := by decide +kernel
theorem cell_7_26_5 : C 7 26 5 := by decide +kernel
theorem row_7_26 : ThresholdAt 7 26 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 26 0 cell_7_26_0
  | exact S 7 26 1 cell_7_26_1
  | exact S 7 26 2 cell_7_26_2
  | exact S 7 26 3 cell_7_26_3
  | exact S 7 26 4 cell_7_26_4
  | exact S 7 26 5 cell_7_26_5
theorem cell_7_27_0 : C 7 27 0 := by decide +kernel
theorem cell_7_27_1 : C 7 27 1 := by decide +kernel
theorem cell_7_27_2 : C 7 27 2 := by decide +kernel
theorem cell_7_27_3 : C 7 27 3 := by decide +kernel
theorem cell_7_27_4 : C 7 27 4 := by decide +kernel
theorem cell_7_27_5 : C 7 27 5 := by decide +kernel
theorem row_7_27 : ThresholdAt 7 27 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 27 0 cell_7_27_0
  | exact S 7 27 1 cell_7_27_1
  | exact S 7 27 2 cell_7_27_2
  | exact S 7 27 3 cell_7_27_3
  | exact S 7 27 4 cell_7_27_4
  | exact S 7 27 5 cell_7_27_5
theorem cell_7_28_0 : C 7 28 0 := by decide +kernel
theorem cell_7_28_1 : C 7 28 1 := by decide +kernel
theorem cell_7_28_2 : C 7 28 2 := by decide +kernel
theorem cell_7_28_3 : C 7 28 3 := by decide +kernel
theorem cell_7_28_4 : C 7 28 4 := by decide +kernel
theorem cell_7_28_5 : C 7 28 5 := by decide +kernel
theorem row_7_28 : ThresholdAt 7 28 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 28 0 cell_7_28_0
  | exact S 7 28 1 cell_7_28_1
  | exact S 7 28 2 cell_7_28_2
  | exact S 7 28 3 cell_7_28_3
  | exact S 7 28 4 cell_7_28_4
  | exact S 7 28 5 cell_7_28_5
theorem cell_7_29_0 : C 7 29 0 := by decide +kernel
theorem cell_7_29_1 : C 7 29 1 := by decide +kernel
theorem cell_7_29_2 : C 7 29 2 := by decide +kernel
theorem cell_7_29_3 : C 7 29 3 := by decide +kernel
theorem cell_7_29_4 : C 7 29 4 := by decide +kernel
theorem cell_7_29_5 : C 7 29 5 := by decide +kernel
theorem row_7_29 : ThresholdAt 7 29 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 29 0 cell_7_29_0
  | exact S 7 29 1 cell_7_29_1
  | exact S 7 29 2 cell_7_29_2
  | exact S 7 29 3 cell_7_29_3
  | exact S 7 29 4 cell_7_29_4
  | exact S 7 29 5 cell_7_29_5
theorem cell_7_30_0 : C 7 30 0 := by decide +kernel
theorem cell_7_30_1 : C 7 30 1 := by decide +kernel
theorem cell_7_30_2 : C 7 30 2 := by decide +kernel
theorem cell_7_30_3 : C 7 30 3 := by decide +kernel
theorem cell_7_30_4 : C 7 30 4 := by decide +kernel
theorem cell_7_30_5 : C 7 30 5 := by decide +kernel
theorem row_7_30 : ThresholdAt 7 30 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 30 0 cell_7_30_0
  | exact S 7 30 1 cell_7_30_1
  | exact S 7 30 2 cell_7_30_2
  | exact S 7 30 3 cell_7_30_3
  | exact S 7 30 4 cell_7_30_4
  | exact S 7 30 5 cell_7_30_5
theorem cell_7_31_0 : C 7 31 0 := by decide +kernel
theorem cell_7_31_1 : C 7 31 1 := by decide +kernel
theorem cell_7_31_2 : C 7 31 2 := by decide +kernel
theorem cell_7_31_3 : C 7 31 3 := by decide +kernel
theorem cell_7_31_4 : C 7 31 4 := by decide +kernel
theorem cell_7_31_5 : C 7 31 5 := by decide +kernel
theorem row_7_31 : ThresholdAt 7 31 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 31 0 cell_7_31_0
  | exact S 7 31 1 cell_7_31_1
  | exact S 7 31 2 cell_7_31_2
  | exact S 7 31 3 cell_7_31_3
  | exact S 7 31 4 cell_7_31_4
  | exact S 7 31 5 cell_7_31_5
theorem cell_7_32_0 : C 7 32 0 := by decide +kernel
theorem cell_7_32_1 : C 7 32 1 := by decide +kernel
theorem cell_7_32_2 : C 7 32 2 := by decide +kernel
theorem cell_7_32_3 : C 7 32 3 := by decide +kernel
theorem cell_7_32_4 : C 7 32 4 := by decide +kernel
theorem cell_7_32_5 : C 7 32 5 := by decide +kernel
theorem row_7_32 : ThresholdAt 7 32 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 32 0 cell_7_32_0
  | exact S 7 32 1 cell_7_32_1
  | exact S 7 32 2 cell_7_32_2
  | exact S 7 32 3 cell_7_32_3
  | exact S 7 32 4 cell_7_32_4
  | exact S 7 32 5 cell_7_32_5
theorem cell_7_33_0 : C 7 33 0 := by decide +kernel
theorem cell_7_33_1 : C 7 33 1 := by decide +kernel
theorem cell_7_33_2 : C 7 33 2 := by decide +kernel
theorem cell_7_33_3 : C 7 33 3 := by decide +kernel
theorem cell_7_33_4 : C 7 33 4 := by decide +kernel
theorem cell_7_33_5 : C 7 33 5 := by decide +kernel
theorem row_7_33 : ThresholdAt 7 33 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 33 0 cell_7_33_0
  | exact S 7 33 1 cell_7_33_1
  | exact S 7 33 2 cell_7_33_2
  | exact S 7 33 3 cell_7_33_3
  | exact S 7 33 4 cell_7_33_4
  | exact S 7 33 5 cell_7_33_5
theorem cell_7_34_0 : C 7 34 0 := by decide +kernel
theorem cell_7_34_1 : C 7 34 1 := by decide +kernel
theorem cell_7_34_2 : C 7 34 2 := by decide +kernel
theorem cell_7_34_3 : C 7 34 3 := by decide +kernel
theorem cell_7_34_4 : C 7 34 4 := by decide +kernel
theorem cell_7_34_5 : C 7 34 5 := by decide +kernel
theorem row_7_34 : ThresholdAt 7 34 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 34 0 cell_7_34_0
  | exact S 7 34 1 cell_7_34_1
  | exact S 7 34 2 cell_7_34_2
  | exact S 7 34 3 cell_7_34_3
  | exact S 7 34 4 cell_7_34_4
  | exact S 7 34 5 cell_7_34_5
theorem cell_7_35_0 : C 7 35 0 := by decide +kernel
theorem cell_7_35_1 : C 7 35 1 := by decide +kernel
theorem cell_7_35_2 : C 7 35 2 := by decide +kernel
theorem cell_7_35_3 : C 7 35 3 := by decide +kernel
theorem cell_7_35_4 : C 7 35 4 := by decide +kernel
theorem cell_7_35_5 : C 7 35 5 := by decide +kernel
theorem row_7_35 : ThresholdAt 7 35 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 35 0 cell_7_35_0
  | exact S 7 35 1 cell_7_35_1
  | exact S 7 35 2 cell_7_35_2
  | exact S 7 35 3 cell_7_35_3
  | exact S 7 35 4 cell_7_35_4
  | exact S 7 35 5 cell_7_35_5
theorem cell_7_36_0 : C 7 36 0 := by decide +kernel
theorem cell_7_36_1 : C 7 36 1 := by decide +kernel
theorem cell_7_36_2 : C 7 36 2 := by decide +kernel
theorem cell_7_36_3 : C 7 36 3 := by decide +kernel
theorem cell_7_36_4 : C 7 36 4 := by decide +kernel
theorem cell_7_36_5 : C 7 36 5 := by decide +kernel
theorem row_7_36 : ThresholdAt 7 36 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 36 0 cell_7_36_0
  | exact S 7 36 1 cell_7_36_1
  | exact S 7 36 2 cell_7_36_2
  | exact S 7 36 3 cell_7_36_3
  | exact S 7 36 4 cell_7_36_4
  | exact S 7 36 5 cell_7_36_5
theorem cell_7_37_0 : C 7 37 0 := by decide +kernel
theorem cell_7_37_1 : C 7 37 1 := by decide +kernel
theorem cell_7_37_2 : C 7 37 2 := by decide +kernel
theorem cell_7_37_3 : C 7 37 3 := by decide +kernel
theorem cell_7_37_4 : C 7 37 4 := by decide +kernel
theorem cell_7_37_5 : C 7 37 5 := by decide +kernel
theorem row_7_37 : ThresholdAt 7 37 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 37 0 cell_7_37_0
  | exact S 7 37 1 cell_7_37_1
  | exact S 7 37 2 cell_7_37_2
  | exact S 7 37 3 cell_7_37_3
  | exact S 7 37 4 cell_7_37_4
  | exact S 7 37 5 cell_7_37_5
theorem cell_7_38_0 : C 7 38 0 := by decide +kernel
theorem cell_7_38_1 : C 7 38 1 := by decide +kernel
theorem cell_7_38_2 : C 7 38 2 := by decide +kernel
theorem cell_7_38_3 : C 7 38 3 := by decide +kernel
theorem cell_7_38_4 : C 7 38 4 := by decide +kernel
theorem cell_7_38_5 : C 7 38 5 := by decide +kernel
theorem row_7_38 : ThresholdAt 7 38 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 38 0 cell_7_38_0
  | exact S 7 38 1 cell_7_38_1
  | exact S 7 38 2 cell_7_38_2
  | exact S 7 38 3 cell_7_38_3
  | exact S 7 38 4 cell_7_38_4
  | exact S 7 38 5 cell_7_38_5
theorem cell_7_39_0 : C 7 39 0 := by decide +kernel
theorem cell_7_39_1 : C 7 39 1 := by decide +kernel
theorem cell_7_39_2 : C 7 39 2 := by decide +kernel
theorem cell_7_39_3 : C 7 39 3 := by decide +kernel
theorem cell_7_39_4 : C 7 39 4 := by decide +kernel
theorem cell_7_39_5 : C 7 39 5 := by decide +kernel
theorem row_7_39 : ThresholdAt 7 39 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 39 0 cell_7_39_0
  | exact S 7 39 1 cell_7_39_1
  | exact S 7 39 2 cell_7_39_2
  | exact S 7 39 3 cell_7_39_3
  | exact S 7 39 4 cell_7_39_4
  | exact S 7 39 5 cell_7_39_5
theorem cell_7_40_0 : C 7 40 0 := by decide +kernel
theorem cell_7_40_1 : C 7 40 1 := by decide +kernel
theorem cell_7_40_2 : C 7 40 2 := by decide +kernel
theorem cell_7_40_3 : C 7 40 3 := by decide +kernel
theorem cell_7_40_4 : C 7 40 4 := by decide +kernel
theorem cell_7_40_5 : C 7 40 5 := by decide +kernel
theorem row_7_40 : ThresholdAt 7 40 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 40 0 cell_7_40_0
  | exact S 7 40 1 cell_7_40_1
  | exact S 7 40 2 cell_7_40_2
  | exact S 7 40 3 cell_7_40_3
  | exact S 7 40 4 cell_7_40_4
  | exact S 7 40 5 cell_7_40_5
theorem cell_7_41_0 : C 7 41 0 := by decide +kernel
theorem cell_7_41_1 : C 7 41 1 := by decide +kernel
theorem cell_7_41_2 : C 7 41 2 := by decide +kernel
theorem cell_7_41_3 : C 7 41 3 := by decide +kernel
theorem cell_7_41_4 : C 7 41 4 := by decide +kernel
theorem cell_7_41_5 : C 7 41 5 := by decide +kernel
theorem row_7_41 : ThresholdAt 7 41 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 41 0 cell_7_41_0
  | exact S 7 41 1 cell_7_41_1
  | exact S 7 41 2 cell_7_41_2
  | exact S 7 41 3 cell_7_41_3
  | exact S 7 41 4 cell_7_41_4
  | exact S 7 41 5 cell_7_41_5
theorem cell_7_42_0 : C 7 42 0 := by decide +kernel
theorem cell_7_42_1 : C 7 42 1 := by decide +kernel
theorem cell_7_42_2 : C 7 42 2 := by decide +kernel
theorem cell_7_42_3 : C 7 42 3 := by decide +kernel
theorem cell_7_42_4 : C 7 42 4 := by decide +kernel
theorem cell_7_42_5 : C 7 42 5 := by decide +kernel
theorem row_7_42 : ThresholdAt 7 42 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 42 0 cell_7_42_0
  | exact S 7 42 1 cell_7_42_1
  | exact S 7 42 2 cell_7_42_2
  | exact S 7 42 3 cell_7_42_3
  | exact S 7 42 4 cell_7_42_4
  | exact S 7 42 5 cell_7_42_5
theorem cell_7_43_0 : C 7 43 0 := by decide +kernel
theorem cell_7_43_1 : C 7 43 1 := by decide +kernel
theorem cell_7_43_2 : C 7 43 2 := by decide +kernel
theorem cell_7_43_3 : C 7 43 3 := by decide +kernel
theorem cell_7_43_4 : C 7 43 4 := by decide +kernel
theorem cell_7_43_5 : C 7 43 5 := by decide +kernel
theorem row_7_43 : ThresholdAt 7 43 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 43 0 cell_7_43_0
  | exact S 7 43 1 cell_7_43_1
  | exact S 7 43 2 cell_7_43_2
  | exact S 7 43 3 cell_7_43_3
  | exact S 7 43 4 cell_7_43_4
  | exact S 7 43 5 cell_7_43_5
theorem cell_7_44_0 : C 7 44 0 := by decide +kernel
theorem cell_7_44_1 : C 7 44 1 := by decide +kernel
theorem cell_7_44_2 : C 7 44 2 := by decide +kernel
theorem cell_7_44_3 : C 7 44 3 := by decide +kernel
theorem cell_7_44_4 : C 7 44 4 := by decide +kernel
theorem cell_7_44_5 : C 7 44 5 := by decide +kernel
theorem row_7_44 : ThresholdAt 7 44 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 44 0 cell_7_44_0
  | exact S 7 44 1 cell_7_44_1
  | exact S 7 44 2 cell_7_44_2
  | exact S 7 44 3 cell_7_44_3
  | exact S 7 44 4 cell_7_44_4
  | exact S 7 44 5 cell_7_44_5
theorem cell_7_45_0 : C 7 45 0 := by decide +kernel
theorem cell_7_45_1 : C 7 45 1 := by decide +kernel
theorem cell_7_45_2 : C 7 45 2 := by decide +kernel
theorem cell_7_45_3 : C 7 45 3 := by decide +kernel
theorem cell_7_45_4 : C 7 45 4 := by decide +kernel
theorem cell_7_45_5 : C 7 45 5 := by decide +kernel
theorem row_7_45 : ThresholdAt 7 45 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 45 0 cell_7_45_0
  | exact S 7 45 1 cell_7_45_1
  | exact S 7 45 2 cell_7_45_2
  | exact S 7 45 3 cell_7_45_3
  | exact S 7 45 4 cell_7_45_4
  | exact S 7 45 5 cell_7_45_5
theorem cell_7_46_0 : C 7 46 0 := by decide +kernel
theorem cell_7_46_1 : C 7 46 1 := by decide +kernel
theorem cell_7_46_2 : C 7 46 2 := by decide +kernel
theorem cell_7_46_3 : C 7 46 3 := by decide +kernel
theorem cell_7_46_4 : C 7 46 4 := by decide +kernel
theorem cell_7_46_5 : C 7 46 5 := by decide +kernel
theorem row_7_46 : ThresholdAt 7 46 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 46 0 cell_7_46_0
  | exact S 7 46 1 cell_7_46_1
  | exact S 7 46 2 cell_7_46_2
  | exact S 7 46 3 cell_7_46_3
  | exact S 7 46 4 cell_7_46_4
  | exact S 7 46 5 cell_7_46_5
theorem cell_7_47_0 : C 7 47 0 := by decide +kernel
theorem cell_7_47_1 : C 7 47 1 := by decide +kernel
theorem cell_7_47_2 : C 7 47 2 := by decide +kernel
theorem cell_7_47_3 : C 7 47 3 := by decide +kernel
theorem cell_7_47_4 : C 7 47 4 := by decide +kernel
theorem cell_7_47_5 : C 7 47 5 := by decide +kernel
theorem row_7_47 : ThresholdAt 7 47 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 47 0 cell_7_47_0
  | exact S 7 47 1 cell_7_47_1
  | exact S 7 47 2 cell_7_47_2
  | exact S 7 47 3 cell_7_47_3
  | exact S 7 47 4 cell_7_47_4
  | exact S 7 47 5 cell_7_47_5
theorem cell_7_48_0 : C 7 48 0 := by decide +kernel
theorem cell_7_48_1 : C 7 48 1 := by decide +kernel
theorem cell_7_48_2 : C 7 48 2 := by decide +kernel
theorem cell_7_48_3 : C 7 48 3 := by decide +kernel
theorem cell_7_48_4 : C 7 48 4 := by decide +kernel
theorem cell_7_48_5 : C 7 48 5 := by decide +kernel
theorem row_7_48 : ThresholdAt 7 48 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 48 0 cell_7_48_0
  | exact S 7 48 1 cell_7_48_1
  | exact S 7 48 2 cell_7_48_2
  | exact S 7 48 3 cell_7_48_3
  | exact S 7 48 4 cell_7_48_4
  | exact S 7 48 5 cell_7_48_5
theorem cell_7_49_0 : C 7 49 0 := by decide +kernel
theorem cell_7_49_1 : C 7 49 1 := by decide +kernel
theorem cell_7_49_2 : C 7 49 2 := by decide +kernel
theorem cell_7_49_3 : C 7 49 3 := by decide +kernel
theorem cell_7_49_4 : C 7 49 4 := by decide +kernel
theorem cell_7_49_5 : C 7 49 5 := by decide +kernel
theorem row_7_49 : ThresholdAt 7 49 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 49 0 cell_7_49_0
  | exact S 7 49 1 cell_7_49_1
  | exact S 7 49 2 cell_7_49_2
  | exact S 7 49 3 cell_7_49_3
  | exact S 7 49 4 cell_7_49_4
  | exact S 7 49 5 cell_7_49_5
theorem cell_7_50_0 : C 7 50 0 := by decide +kernel
theorem cell_7_50_1 : C 7 50 1 := by decide +kernel
theorem cell_7_50_2 : C 7 50 2 := by decide +kernel
theorem cell_7_50_3 : C 7 50 3 := by decide +kernel
theorem cell_7_50_4 : C 7 50 4 := by decide +kernel
theorem cell_7_50_5 : C 7 50 5 := by decide +kernel
theorem row_7_50 : ThresholdAt 7 50 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 50 0 cell_7_50_0
  | exact S 7 50 1 cell_7_50_1
  | exact S 7 50 2 cell_7_50_2
  | exact S 7 50 3 cell_7_50_3
  | exact S 7 50 4 cell_7_50_4
  | exact S 7 50 5 cell_7_50_5
theorem cell_7_51_0 : C 7 51 0 := by decide +kernel
theorem cell_7_51_1 : C 7 51 1 := by decide +kernel
theorem cell_7_51_2 : C 7 51 2 := by decide +kernel
theorem cell_7_51_3 : C 7 51 3 := by decide +kernel
theorem cell_7_51_4 : C 7 51 4 := by decide +kernel
theorem cell_7_51_5 : C 7 51 5 := by decide +kernel
theorem row_7_51 : ThresholdAt 7 51 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 51 0 cell_7_51_0
  | exact S 7 51 1 cell_7_51_1
  | exact S 7 51 2 cell_7_51_2
  | exact S 7 51 3 cell_7_51_3
  | exact S 7 51 4 cell_7_51_4
  | exact S 7 51 5 cell_7_51_5
theorem cell_7_52_0 : C 7 52 0 := by decide +kernel
theorem cell_7_52_1 : C 7 52 1 := by decide +kernel
theorem cell_7_52_2 : C 7 52 2 := by decide +kernel
theorem cell_7_52_3 : C 7 52 3 := by decide +kernel
theorem cell_7_52_4 : C 7 52 4 := by decide +kernel
theorem cell_7_52_5 : C 7 52 5 := by decide +kernel
theorem row_7_52 : ThresholdAt 7 52 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 52 0 cell_7_52_0
  | exact S 7 52 1 cell_7_52_1
  | exact S 7 52 2 cell_7_52_2
  | exact S 7 52 3 cell_7_52_3
  | exact S 7 52 4 cell_7_52_4
  | exact S 7 52 5 cell_7_52_5
theorem cell_7_53_0 : C 7 53 0 := by decide +kernel
theorem cell_7_53_1 : C 7 53 1 := by decide +kernel
theorem cell_7_53_2 : C 7 53 2 := by decide +kernel
theorem cell_7_53_3 : C 7 53 3 := by decide +kernel
theorem cell_7_53_4 : C 7 53 4 := by decide +kernel
theorem cell_7_53_5 : C 7 53 5 := by decide +kernel
theorem row_7_53 : ThresholdAt 7 53 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 53 0 cell_7_53_0
  | exact S 7 53 1 cell_7_53_1
  | exact S 7 53 2 cell_7_53_2
  | exact S 7 53 3 cell_7_53_3
  | exact S 7 53 4 cell_7_53_4
  | exact S 7 53 5 cell_7_53_5
theorem cell_7_54_0 : C 7 54 0 := by decide +kernel
theorem cell_7_54_1 : C 7 54 1 := by decide +kernel
theorem cell_7_54_2 : C 7 54 2 := by decide +kernel
theorem cell_7_54_3 : C 7 54 3 := by decide +kernel
theorem cell_7_54_4 : C 7 54 4 := by decide +kernel
theorem cell_7_54_5 : C 7 54 5 := by decide +kernel
theorem row_7_54 : ThresholdAt 7 54 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 54 0 cell_7_54_0
  | exact S 7 54 1 cell_7_54_1
  | exact S 7 54 2 cell_7_54_2
  | exact S 7 54 3 cell_7_54_3
  | exact S 7 54 4 cell_7_54_4
  | exact S 7 54 5 cell_7_54_5
theorem cell_7_55_0 : C 7 55 0 := by decide +kernel
theorem cell_7_55_1 : C 7 55 1 := by decide +kernel
theorem cell_7_55_2 : C 7 55 2 := by decide +kernel
theorem cell_7_55_3 : C 7 55 3 := by decide +kernel
theorem cell_7_55_4 : C 7 55 4 := by decide +kernel
theorem cell_7_55_5 : C 7 55 5 := by decide +kernel
theorem row_7_55 : ThresholdAt 7 55 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 55 0 cell_7_55_0
  | exact S 7 55 1 cell_7_55_1
  | exact S 7 55 2 cell_7_55_2
  | exact S 7 55 3 cell_7_55_3
  | exact S 7 55 4 cell_7_55_4
  | exact S 7 55 5 cell_7_55_5
theorem cell_7_56_0 : C 7 56 0 := by decide +kernel
theorem cell_7_56_1 : C 7 56 1 := by decide +kernel
theorem cell_7_56_2 : C 7 56 2 := by decide +kernel
theorem cell_7_56_3 : C 7 56 3 := by decide +kernel
theorem cell_7_56_4 : C 7 56 4 := by decide +kernel
theorem cell_7_56_5 : C 7 56 5 := by decide +kernel
theorem row_7_56 : ThresholdAt 7 56 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 56 0 cell_7_56_0
  | exact S 7 56 1 cell_7_56_1
  | exact S 7 56 2 cell_7_56_2
  | exact S 7 56 3 cell_7_56_3
  | exact S 7 56 4 cell_7_56_4
  | exact S 7 56 5 cell_7_56_5
theorem cell_7_57_0 : C 7 57 0 := by decide +kernel
theorem cell_7_57_1 : C 7 57 1 := by decide +kernel
theorem cell_7_57_2 : C 7 57 2 := by decide +kernel
theorem cell_7_57_3 : C 7 57 3 := by decide +kernel
theorem cell_7_57_4 : C 7 57 4 := by decide +kernel
theorem cell_7_57_5 : C 7 57 5 := by decide +kernel
theorem row_7_57 : ThresholdAt 7 57 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 57 0 cell_7_57_0
  | exact S 7 57 1 cell_7_57_1
  | exact S 7 57 2 cell_7_57_2
  | exact S 7 57 3 cell_7_57_3
  | exact S 7 57 4 cell_7_57_4
  | exact S 7 57 5 cell_7_57_5
theorem cell_7_58_0 : C 7 58 0 := by decide +kernel
theorem cell_7_58_1 : C 7 58 1 := by decide +kernel
theorem cell_7_58_2 : C 7 58 2 := by decide +kernel
theorem cell_7_58_3 : C 7 58 3 := by decide +kernel
theorem cell_7_58_4 : C 7 58 4 := by decide +kernel
theorem cell_7_58_5 : C 7 58 5 := by decide +kernel
theorem row_7_58 : ThresholdAt 7 58 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 58 0 cell_7_58_0
  | exact S 7 58 1 cell_7_58_1
  | exact S 7 58 2 cell_7_58_2
  | exact S 7 58 3 cell_7_58_3
  | exact S 7 58 4 cell_7_58_4
  | exact S 7 58 5 cell_7_58_5
theorem cell_7_59_0 : C 7 59 0 := by decide +kernel
theorem cell_7_59_1 : C 7 59 1 := by decide +kernel
theorem cell_7_59_2 : C 7 59 2 := by decide +kernel
theorem cell_7_59_3 : C 7 59 3 := by decide +kernel
theorem cell_7_59_4 : C 7 59 4 := by decide +kernel
theorem cell_7_59_5 : C 7 59 5 := by decide +kernel
theorem row_7_59 : ThresholdAt 7 59 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 59 0 cell_7_59_0
  | exact S 7 59 1 cell_7_59_1
  | exact S 7 59 2 cell_7_59_2
  | exact S 7 59 3 cell_7_59_3
  | exact S 7 59 4 cell_7_59_4
  | exact S 7 59 5 cell_7_59_5
theorem cell_7_60_0 : C 7 60 0 := by decide +kernel
theorem cell_7_60_1 : C 7 60 1 := by decide +kernel
theorem cell_7_60_2 : C 7 60 2 := by decide +kernel
theorem cell_7_60_3 : C 7 60 3 := by decide +kernel
theorem cell_7_60_4 : C 7 60 4 := by decide +kernel
theorem cell_7_60_5 : C 7 60 5 := by decide +kernel
theorem row_7_60 : ThresholdAt 7 60 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 60 0 cell_7_60_0
  | exact S 7 60 1 cell_7_60_1
  | exact S 7 60 2 cell_7_60_2
  | exact S 7 60 3 cell_7_60_3
  | exact S 7 60 4 cell_7_60_4
  | exact S 7 60 5 cell_7_60_5
theorem cell_7_61_0 : C 7 61 0 := by decide +kernel
theorem cell_7_61_1 : C 7 61 1 := by decide +kernel
theorem cell_7_61_2 : C 7 61 2 := by decide +kernel
theorem cell_7_61_3 : C 7 61 3 := by decide +kernel
theorem cell_7_61_4 : C 7 61 4 := by decide +kernel
theorem cell_7_61_5 : C 7 61 5 := by decide +kernel
theorem row_7_61 : ThresholdAt 7 61 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 61 0 cell_7_61_0
  | exact S 7 61 1 cell_7_61_1
  | exact S 7 61 2 cell_7_61_2
  | exact S 7 61 3 cell_7_61_3
  | exact S 7 61 4 cell_7_61_4
  | exact S 7 61 5 cell_7_61_5
theorem cell_7_62_0 : C 7 62 0 := by decide +kernel
theorem cell_7_62_1 : C 7 62 1 := by decide +kernel
theorem cell_7_62_2 : C 7 62 2 := by decide +kernel
theorem cell_7_62_3 : C 7 62 3 := by decide +kernel
theorem cell_7_62_4 : C 7 62 4 := by decide +kernel
theorem cell_7_62_5 : C 7 62 5 := by decide +kernel
theorem row_7_62 : ThresholdAt 7 62 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 62 0 cell_7_62_0
  | exact S 7 62 1 cell_7_62_1
  | exact S 7 62 2 cell_7_62_2
  | exact S 7 62 3 cell_7_62_3
  | exact S 7 62 4 cell_7_62_4
  | exact S 7 62 5 cell_7_62_5
theorem cell_7_63_0 : C 7 63 0 := by decide +kernel
theorem cell_7_63_1 : C 7 63 1 := by decide +kernel
theorem cell_7_63_2 : C 7 63 2 := by decide +kernel
theorem cell_7_63_3 : C 7 63 3 := by decide +kernel
theorem cell_7_63_4 : C 7 63 4 := by decide +kernel
theorem cell_7_63_5 : C 7 63 5 := by decide +kernel
theorem row_7_63 : ThresholdAt 7 63 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 63 0 cell_7_63_0
  | exact S 7 63 1 cell_7_63_1
  | exact S 7 63 2 cell_7_63_2
  | exact S 7 63 3 cell_7_63_3
  | exact S 7 63 4 cell_7_63_4
  | exact S 7 63 5 cell_7_63_5
theorem cell_7_64_0 : C 7 64 0 := by decide +kernel
theorem cell_7_64_1 : C 7 64 1 := by decide +kernel
theorem cell_7_64_2 : C 7 64 2 := by decide +kernel
theorem cell_7_64_3 : C 7 64 3 := by decide +kernel
theorem cell_7_64_4 : C 7 64 4 := by decide +kernel
theorem cell_7_64_5 : C 7 64 5 := by decide +kernel
theorem row_7_64 : ThresholdAt 7 64 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 64 0 cell_7_64_0
  | exact S 7 64 1 cell_7_64_1
  | exact S 7 64 2 cell_7_64_2
  | exact S 7 64 3 cell_7_64_3
  | exact S 7 64 4 cell_7_64_4
  | exact S 7 64 5 cell_7_64_5
theorem cell_7_65_0 : C 7 65 0 := by decide +kernel
theorem cell_7_65_1 : C 7 65 1 := by decide +kernel
theorem cell_7_65_2 : C 7 65 2 := by decide +kernel
theorem cell_7_65_3 : C 7 65 3 := by decide +kernel
theorem cell_7_65_4 : C 7 65 4 := by decide +kernel
theorem cell_7_65_5 : C 7 65 5 := by decide +kernel
theorem row_7_65 : ThresholdAt 7 65 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 65 0 cell_7_65_0
  | exact S 7 65 1 cell_7_65_1
  | exact S 7 65 2 cell_7_65_2
  | exact S 7 65 3 cell_7_65_3
  | exact S 7 65 4 cell_7_65_4
  | exact S 7 65 5 cell_7_65_5
theorem cell_7_66_0 : C 7 66 0 := by decide +kernel
theorem cell_7_66_1 : C 7 66 1 := by decide +kernel
theorem cell_7_66_2 : C 7 66 2 := by decide +kernel
theorem cell_7_66_3 : C 7 66 3 := by decide +kernel
theorem cell_7_66_4 : C 7 66 4 := by decide +kernel
theorem cell_7_66_5 : C 7 66 5 := by decide +kernel
theorem row_7_66 : ThresholdAt 7 66 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 66 0 cell_7_66_0
  | exact S 7 66 1 cell_7_66_1
  | exact S 7 66 2 cell_7_66_2
  | exact S 7 66 3 cell_7_66_3
  | exact S 7 66 4 cell_7_66_4
  | exact S 7 66 5 cell_7_66_5
theorem cell_7_67_0 : C 7 67 0 := by decide +kernel
theorem cell_7_67_1 : C 7 67 1 := by decide +kernel
theorem cell_7_67_2 : C 7 67 2 := by decide +kernel
theorem cell_7_67_3 : C 7 67 3 := by decide +kernel
theorem cell_7_67_4 : C 7 67 4 := by decide +kernel
theorem cell_7_67_5 : C 7 67 5 := by decide +kernel
theorem row_7_67 : ThresholdAt 7 67 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 67 0 cell_7_67_0
  | exact S 7 67 1 cell_7_67_1
  | exact S 7 67 2 cell_7_67_2
  | exact S 7 67 3 cell_7_67_3
  | exact S 7 67 4 cell_7_67_4
  | exact S 7 67 5 cell_7_67_5
theorem cell_7_68_0 : C 7 68 0 := by decide +kernel
theorem cell_7_68_1 : C 7 68 1 := by decide +kernel
theorem cell_7_68_2 : C 7 68 2 := by decide +kernel
theorem cell_7_68_3 : C 7 68 3 := by decide +kernel
theorem cell_7_68_4 : C 7 68 4 := by decide +kernel
theorem cell_7_68_5 : C 7 68 5 := by decide +kernel
theorem row_7_68 : ThresholdAt 7 68 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 68 0 cell_7_68_0
  | exact S 7 68 1 cell_7_68_1
  | exact S 7 68 2 cell_7_68_2
  | exact S 7 68 3 cell_7_68_3
  | exact S 7 68 4 cell_7_68_4
  | exact S 7 68 5 cell_7_68_5
theorem cell_7_69_0 : C 7 69 0 := by decide +kernel
theorem cell_7_69_1 : C 7 69 1 := by decide +kernel
theorem cell_7_69_2 : C 7 69 2 := by decide +kernel
theorem cell_7_69_3 : C 7 69 3 := by decide +kernel
theorem cell_7_69_4 : C 7 69 4 := by decide +kernel
theorem cell_7_69_5 : C 7 69 5 := by decide +kernel
theorem row_7_69 : ThresholdAt 7 69 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 69 0 cell_7_69_0
  | exact S 7 69 1 cell_7_69_1
  | exact S 7 69 2 cell_7_69_2
  | exact S 7 69 3 cell_7_69_3
  | exact S 7 69 4 cell_7_69_4
  | exact S 7 69 5 cell_7_69_5
theorem cell_7_70_0 : C 7 70 0 := by decide +kernel
theorem cell_7_70_1 : C 7 70 1 := by decide +kernel
theorem cell_7_70_2 : C 7 70 2 := by decide +kernel
theorem cell_7_70_3 : C 7 70 3 := by decide +kernel
theorem cell_7_70_4 : C 7 70 4 := by decide +kernel
theorem cell_7_70_5 : C 7 70 5 := by decide +kernel
theorem row_7_70 : ThresholdAt 7 70 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 70 0 cell_7_70_0
  | exact S 7 70 1 cell_7_70_1
  | exact S 7 70 2 cell_7_70_2
  | exact S 7 70 3 cell_7_70_3
  | exact S 7 70 4 cell_7_70_4
  | exact S 7 70 5 cell_7_70_5
theorem cell_7_71_0 : C 7 71 0 := by decide +kernel
theorem cell_7_71_1 : C 7 71 1 := by decide +kernel
theorem cell_7_71_2 : C 7 71 2 := by decide +kernel
theorem cell_7_71_3 : C 7 71 3 := by decide +kernel
theorem cell_7_71_4 : C 7 71 4 := by decide +kernel
theorem cell_7_71_5 : C 7 71 5 := by decide +kernel
theorem row_7_71 : ThresholdAt 7 71 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 71 0 cell_7_71_0
  | exact S 7 71 1 cell_7_71_1
  | exact S 7 71 2 cell_7_71_2
  | exact S 7 71 3 cell_7_71_3
  | exact S 7 71 4 cell_7_71_4
  | exact S 7 71 5 cell_7_71_5
theorem cell_7_72_0 : C 7 72 0 := by decide +kernel
theorem cell_7_72_1 : C 7 72 1 := by decide +kernel
theorem cell_7_72_2 : C 7 72 2 := by decide +kernel
theorem cell_7_72_3 : C 7 72 3 := by decide +kernel
theorem cell_7_72_4 : C 7 72 4 := by decide +kernel
theorem cell_7_72_5 : C 7 72 5 := by decide +kernel
theorem row_7_72 : ThresholdAt 7 72 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 72 0 cell_7_72_0
  | exact S 7 72 1 cell_7_72_1
  | exact S 7 72 2 cell_7_72_2
  | exact S 7 72 3 cell_7_72_3
  | exact S 7 72 4 cell_7_72_4
  | exact S 7 72 5 cell_7_72_5
theorem cell_7_73_0 : C 7 73 0 := by decide +kernel
theorem cell_7_73_1 : C 7 73 1 := by decide +kernel
theorem cell_7_73_2 : C 7 73 2 := by decide +kernel
theorem cell_7_73_3 : C 7 73 3 := by decide +kernel
theorem cell_7_73_4 : C 7 73 4 := by decide +kernel
theorem cell_7_73_5 : C 7 73 5 := by decide +kernel
theorem row_7_73 : ThresholdAt 7 73 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 73 0 cell_7_73_0
  | exact S 7 73 1 cell_7_73_1
  | exact S 7 73 2 cell_7_73_2
  | exact S 7 73 3 cell_7_73_3
  | exact S 7 73 4 cell_7_73_4
  | exact S 7 73 5 cell_7_73_5
theorem cell_7_74_0 : C 7 74 0 := by decide +kernel
theorem cell_7_74_1 : C 7 74 1 := by decide +kernel
theorem cell_7_74_2 : C 7 74 2 := by decide +kernel
theorem cell_7_74_3 : C 7 74 3 := by decide +kernel
theorem cell_7_74_4 : C 7 74 4 := by decide +kernel
theorem cell_7_74_5 : C 7 74 5 := by decide +kernel
theorem row_7_74 : ThresholdAt 7 74 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 74 0 cell_7_74_0
  | exact S 7 74 1 cell_7_74_1
  | exact S 7 74 2 cell_7_74_2
  | exact S 7 74 3 cell_7_74_3
  | exact S 7 74 4 cell_7_74_4
  | exact S 7 74 5 cell_7_74_5
theorem cell_7_75_0 : C 7 75 0 := by decide +kernel
theorem cell_7_75_1 : C 7 75 1 := by decide +kernel
theorem cell_7_75_2 : C 7 75 2 := by decide +kernel
theorem cell_7_75_3 : C 7 75 3 := by decide +kernel
theorem cell_7_75_4 : C 7 75 4 := by decide +kernel
theorem cell_7_75_5 : C 7 75 5 := by decide +kernel
theorem row_7_75 : ThresholdAt 7 75 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 75 0 cell_7_75_0
  | exact S 7 75 1 cell_7_75_1
  | exact S 7 75 2 cell_7_75_2
  | exact S 7 75 3 cell_7_75_3
  | exact S 7 75 4 cell_7_75_4
  | exact S 7 75 5 cell_7_75_5
theorem cell_7_76_0 : C 7 76 0 := by decide +kernel
theorem cell_7_76_1 : C 7 76 1 := by decide +kernel
theorem cell_7_76_2 : C 7 76 2 := by decide +kernel
theorem cell_7_76_3 : C 7 76 3 := by decide +kernel
theorem cell_7_76_4 : C 7 76 4 := by decide +kernel
theorem cell_7_76_5 : C 7 76 5 := by decide +kernel
theorem row_7_76 : ThresholdAt 7 76 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 76 0 cell_7_76_0
  | exact S 7 76 1 cell_7_76_1
  | exact S 7 76 2 cell_7_76_2
  | exact S 7 76 3 cell_7_76_3
  | exact S 7 76 4 cell_7_76_4
  | exact S 7 76 5 cell_7_76_5
theorem cell_7_77_0 : C 7 77 0 := by decide +kernel
theorem cell_7_77_1 : C 7 77 1 := by decide +kernel
theorem cell_7_77_2 : C 7 77 2 := by decide +kernel
theorem cell_7_77_3 : C 7 77 3 := by decide +kernel
theorem cell_7_77_4 : C 7 77 4 := by decide +kernel
theorem cell_7_77_5 : C 7 77 5 := by decide +kernel
theorem row_7_77 : ThresholdAt 7 77 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 77 0 cell_7_77_0
  | exact S 7 77 1 cell_7_77_1
  | exact S 7 77 2 cell_7_77_2
  | exact S 7 77 3 cell_7_77_3
  | exact S 7 77 4 cell_7_77_4
  | exact S 7 77 5 cell_7_77_5
theorem cell_7_78_0 : C 7 78 0 := by decide +kernel
theorem cell_7_78_1 : C 7 78 1 := by decide +kernel
theorem cell_7_78_2 : C 7 78 2 := by decide +kernel
theorem cell_7_78_3 : C 7 78 3 := by decide +kernel
theorem cell_7_78_4 : C 7 78 4 := by decide +kernel
theorem cell_7_78_5 : C 7 78 5 := by decide +kernel
theorem row_7_78 : ThresholdAt 7 78 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 78 0 cell_7_78_0
  | exact S 7 78 1 cell_7_78_1
  | exact S 7 78 2 cell_7_78_2
  | exact S 7 78 3 cell_7_78_3
  | exact S 7 78 4 cell_7_78_4
  | exact S 7 78 5 cell_7_78_5
theorem cell_7_79_0 : C 7 79 0 := by decide +kernel
theorem cell_7_79_1 : C 7 79 1 := by decide +kernel
theorem cell_7_79_2 : C 7 79 2 := by decide +kernel
theorem cell_7_79_3 : C 7 79 3 := by decide +kernel
theorem cell_7_79_4 : C 7 79 4 := by decide +kernel
theorem cell_7_79_5 : C 7 79 5 := by decide +kernel
theorem row_7_79 : ThresholdAt 7 79 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 79 0 cell_7_79_0
  | exact S 7 79 1 cell_7_79_1
  | exact S 7 79 2 cell_7_79_2
  | exact S 7 79 3 cell_7_79_3
  | exact S 7 79 4 cell_7_79_4
  | exact S 7 79 5 cell_7_79_5
theorem cell_7_80_0 : C 7 80 0 := by decide +kernel
theorem cell_7_80_1 : C 7 80 1 := by decide +kernel
theorem cell_7_80_2 : C 7 80 2 := by decide +kernel
theorem cell_7_80_3 : C 7 80 3 := by decide +kernel
theorem cell_7_80_4 : C 7 80 4 := by decide +kernel
theorem cell_7_80_5 : C 7 80 5 := by decide +kernel
theorem row_7_80 : ThresholdAt 7 80 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 80 0 cell_7_80_0
  | exact S 7 80 1 cell_7_80_1
  | exact S 7 80 2 cell_7_80_2
  | exact S 7 80 3 cell_7_80_3
  | exact S 7 80 4 cell_7_80_4
  | exact S 7 80 5 cell_7_80_5
theorem cell_7_81_0 : C 7 81 0 := by decide +kernel
theorem cell_7_81_1 : C 7 81 1 := by decide +kernel
theorem cell_7_81_2 : C 7 81 2 := by decide +kernel
theorem cell_7_81_3 : C 7 81 3 := by decide +kernel
theorem cell_7_81_4 : C 7 81 4 := by decide +kernel
theorem cell_7_81_5 : C 7 81 5 := by decide +kernel
theorem row_7_81 : ThresholdAt 7 81 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 81 0 cell_7_81_0
  | exact S 7 81 1 cell_7_81_1
  | exact S 7 81 2 cell_7_81_2
  | exact S 7 81 3 cell_7_81_3
  | exact S 7 81 4 cell_7_81_4
  | exact S 7 81 5 cell_7_81_5
theorem cell_7_82_0 : C 7 82 0 := by decide +kernel
theorem cell_7_82_1 : C 7 82 1 := by decide +kernel
theorem cell_7_82_2 : C 7 82 2 := by decide +kernel
theorem cell_7_82_3 : C 7 82 3 := by decide +kernel
theorem cell_7_82_4 : C 7 82 4 := by decide +kernel
theorem cell_7_82_5 : C 7 82 5 := by decide +kernel
theorem row_7_82 : ThresholdAt 7 82 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 82 0 cell_7_82_0
  | exact S 7 82 1 cell_7_82_1
  | exact S 7 82 2 cell_7_82_2
  | exact S 7 82 3 cell_7_82_3
  | exact S 7 82 4 cell_7_82_4
  | exact S 7 82 5 cell_7_82_5
theorem cell_7_83_0 : C 7 83 0 := by decide +kernel
theorem cell_7_83_1 : C 7 83 1 := by decide +kernel
theorem cell_7_83_2 : C 7 83 2 := by decide +kernel
theorem cell_7_83_3 : C 7 83 3 := by decide +kernel
theorem cell_7_83_4 : C 7 83 4 := by decide +kernel
theorem cell_7_83_5 : C 7 83 5 := by decide +kernel
theorem row_7_83 : ThresholdAt 7 83 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 83 0 cell_7_83_0
  | exact S 7 83 1 cell_7_83_1
  | exact S 7 83 2 cell_7_83_2
  | exact S 7 83 3 cell_7_83_3
  | exact S 7 83 4 cell_7_83_4
  | exact S 7 83 5 cell_7_83_5
theorem cell_7_84_0 : C 7 84 0 := by decide +kernel
theorem cell_7_84_1 : C 7 84 1 := by decide +kernel
theorem cell_7_84_2 : C 7 84 2 := by decide +kernel
theorem cell_7_84_3 : C 7 84 3 := by decide +kernel
theorem cell_7_84_4 : C 7 84 4 := by decide +kernel
theorem cell_7_84_5 : C 7 84 5 := by decide +kernel
theorem row_7_84 : ThresholdAt 7 84 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 84 0 cell_7_84_0
  | exact S 7 84 1 cell_7_84_1
  | exact S 7 84 2 cell_7_84_2
  | exact S 7 84 3 cell_7_84_3
  | exact S 7 84 4 cell_7_84_4
  | exact S 7 84 5 cell_7_84_5
theorem cell_7_85_0 : C 7 85 0 := by decide +kernel
theorem cell_7_85_1 : C 7 85 1 := by decide +kernel
theorem cell_7_85_2 : C 7 85 2 := by decide +kernel
theorem cell_7_85_3 : C 7 85 3 := by decide +kernel
theorem cell_7_85_4 : C 7 85 4 := by decide +kernel
theorem cell_7_85_5 : C 7 85 5 := by decide +kernel
theorem row_7_85 : ThresholdAt 7 85 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 85 0 cell_7_85_0
  | exact S 7 85 1 cell_7_85_1
  | exact S 7 85 2 cell_7_85_2
  | exact S 7 85 3 cell_7_85_3
  | exact S 7 85 4 cell_7_85_4
  | exact S 7 85 5 cell_7_85_5
theorem cell_7_86_0 : C 7 86 0 := by decide +kernel
theorem cell_7_86_1 : C 7 86 1 := by decide +kernel
theorem cell_7_86_2 : C 7 86 2 := by decide +kernel
theorem cell_7_86_3 : C 7 86 3 := by decide +kernel
theorem cell_7_86_4 : C 7 86 4 := by decide +kernel
theorem cell_7_86_5 : C 7 86 5 := by decide +kernel
theorem row_7_86 : ThresholdAt 7 86 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 86 0 cell_7_86_0
  | exact S 7 86 1 cell_7_86_1
  | exact S 7 86 2 cell_7_86_2
  | exact S 7 86 3 cell_7_86_3
  | exact S 7 86 4 cell_7_86_4
  | exact S 7 86 5 cell_7_86_5
theorem cell_7_87_0 : C 7 87 0 := by decide +kernel
theorem cell_7_87_1 : C 7 87 1 := by decide +kernel
theorem cell_7_87_2 : C 7 87 2 := by decide +kernel
theorem cell_7_87_3 : C 7 87 3 := by decide +kernel
theorem cell_7_87_4 : C 7 87 4 := by decide +kernel
theorem cell_7_87_5 : C 7 87 5 := by decide +kernel
theorem row_7_87 : ThresholdAt 7 87 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 87 0 cell_7_87_0
  | exact S 7 87 1 cell_7_87_1
  | exact S 7 87 2 cell_7_87_2
  | exact S 7 87 3 cell_7_87_3
  | exact S 7 87 4 cell_7_87_4
  | exact S 7 87 5 cell_7_87_5
theorem cell_7_88_0 : C 7 88 0 := by decide +kernel
theorem cell_7_88_1 : C 7 88 1 := by decide +kernel
theorem cell_7_88_2 : C 7 88 2 := by decide +kernel
theorem cell_7_88_3 : C 7 88 3 := by decide +kernel
theorem cell_7_88_4 : C 7 88 4 := by decide +kernel
theorem cell_7_88_5 : C 7 88 5 := by decide +kernel
theorem row_7_88 : ThresholdAt 7 88 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 88 0 cell_7_88_0
  | exact S 7 88 1 cell_7_88_1
  | exact S 7 88 2 cell_7_88_2
  | exact S 7 88 3 cell_7_88_3
  | exact S 7 88 4 cell_7_88_4
  | exact S 7 88 5 cell_7_88_5
theorem cell_7_89_0 : C 7 89 0 := by decide +kernel
theorem cell_7_89_1 : C 7 89 1 := by decide +kernel
theorem cell_7_89_2 : C 7 89 2 := by decide +kernel
theorem cell_7_89_3 : C 7 89 3 := by decide +kernel
theorem cell_7_89_4 : C 7 89 4 := by decide +kernel
theorem cell_7_89_5 : C 7 89 5 := by decide +kernel
theorem row_7_89 : ThresholdAt 7 89 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 89 0 cell_7_89_0
  | exact S 7 89 1 cell_7_89_1
  | exact S 7 89 2 cell_7_89_2
  | exact S 7 89 3 cell_7_89_3
  | exact S 7 89 4 cell_7_89_4
  | exact S 7 89 5 cell_7_89_5
theorem cell_7_90_0 : C 7 90 0 := by decide +kernel
theorem cell_7_90_1 : C 7 90 1 := by decide +kernel
theorem cell_7_90_2 : C 7 90 2 := by decide +kernel
theorem cell_7_90_3 : C 7 90 3 := by decide +kernel
theorem cell_7_90_4 : C 7 90 4 := by decide +kernel
theorem cell_7_90_5 : C 7 90 5 := by decide +kernel
theorem row_7_90 : ThresholdAt 7 90 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 90 0 cell_7_90_0
  | exact S 7 90 1 cell_7_90_1
  | exact S 7 90 2 cell_7_90_2
  | exact S 7 90 3 cell_7_90_3
  | exact S 7 90 4 cell_7_90_4
  | exact S 7 90 5 cell_7_90_5
theorem cell_7_91_0 : C 7 91 0 := by decide +kernel
theorem cell_7_91_1 : C 7 91 1 := by decide +kernel
theorem cell_7_91_2 : C 7 91 2 := by decide +kernel
theorem cell_7_91_3 : C 7 91 3 := by decide +kernel
theorem cell_7_91_4 : C 7 91 4 := by decide +kernel
theorem cell_7_91_5 : C 7 91 5 := by decide +kernel
theorem row_7_91 : ThresholdAt 7 91 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 91 0 cell_7_91_0
  | exact S 7 91 1 cell_7_91_1
  | exact S 7 91 2 cell_7_91_2
  | exact S 7 91 3 cell_7_91_3
  | exact S 7 91 4 cell_7_91_4
  | exact S 7 91 5 cell_7_91_5
theorem cell_7_92_0 : C 7 92 0 := by decide +kernel
theorem cell_7_92_1 : C 7 92 1 := by decide +kernel
theorem cell_7_92_2 : C 7 92 2 := by decide +kernel
theorem cell_7_92_3 : C 7 92 3 := by decide +kernel
theorem cell_7_92_4 : C 7 92 4 := by decide +kernel
theorem cell_7_92_5 : C 7 92 5 := by decide +kernel
theorem row_7_92 : ThresholdAt 7 92 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 92 0 cell_7_92_0
  | exact S 7 92 1 cell_7_92_1
  | exact S 7 92 2 cell_7_92_2
  | exact S 7 92 3 cell_7_92_3
  | exact S 7 92 4 cell_7_92_4
  | exact S 7 92 5 cell_7_92_5
theorem cell_7_93_0 : C 7 93 0 := by decide +kernel
theorem cell_7_93_1 : C 7 93 1 := by decide +kernel
theorem cell_7_93_2 : C 7 93 2 := by decide +kernel
theorem cell_7_93_3 : C 7 93 3 := by decide +kernel
theorem cell_7_93_4 : C 7 93 4 := by decide +kernel
theorem cell_7_93_5 : C 7 93 5 := by decide +kernel
theorem row_7_93 : ThresholdAt 7 93 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 93 0 cell_7_93_0
  | exact S 7 93 1 cell_7_93_1
  | exact S 7 93 2 cell_7_93_2
  | exact S 7 93 3 cell_7_93_3
  | exact S 7 93 4 cell_7_93_4
  | exact S 7 93 5 cell_7_93_5
theorem cell_7_94_0 : C 7 94 0 := by decide +kernel
theorem cell_7_94_1 : C 7 94 1 := by decide +kernel
theorem cell_7_94_2 : C 7 94 2 := by decide +kernel
theorem cell_7_94_3 : C 7 94 3 := by decide +kernel
theorem cell_7_94_4 : C 7 94 4 := by decide +kernel
theorem cell_7_94_5 : C 7 94 5 := by decide +kernel
theorem row_7_94 : ThresholdAt 7 94 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 94 0 cell_7_94_0
  | exact S 7 94 1 cell_7_94_1
  | exact S 7 94 2 cell_7_94_2
  | exact S 7 94 3 cell_7_94_3
  | exact S 7 94 4 cell_7_94_4
  | exact S 7 94 5 cell_7_94_5
theorem cell_7_95_0 : C 7 95 0 := by decide +kernel
theorem cell_7_95_1 : C 7 95 1 := by decide +kernel
theorem cell_7_95_2 : C 7 95 2 := by decide +kernel
theorem cell_7_95_3 : C 7 95 3 := by decide +kernel
theorem cell_7_95_4 : C 7 95 4 := by decide +kernel
theorem cell_7_95_5 : C 7 95 5 := by decide +kernel
theorem row_7_95 : ThresholdAt 7 95 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 95 0 cell_7_95_0
  | exact S 7 95 1 cell_7_95_1
  | exact S 7 95 2 cell_7_95_2
  | exact S 7 95 3 cell_7_95_3
  | exact S 7 95 4 cell_7_95_4
  | exact S 7 95 5 cell_7_95_5
theorem cell_7_96_0 : C 7 96 0 := by decide +kernel
theorem cell_7_96_1 : C 7 96 1 := by decide +kernel
theorem cell_7_96_2 : C 7 96 2 := by decide +kernel
theorem cell_7_96_3 : C 7 96 3 := by decide +kernel
theorem cell_7_96_4 : C 7 96 4 := by decide +kernel
theorem cell_7_96_5 : C 7 96 5 := by decide +kernel
theorem row_7_96 : ThresholdAt 7 96 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 96 0 cell_7_96_0
  | exact S 7 96 1 cell_7_96_1
  | exact S 7 96 2 cell_7_96_2
  | exact S 7 96 3 cell_7_96_3
  | exact S 7 96 4 cell_7_96_4
  | exact S 7 96 5 cell_7_96_5
theorem cell_7_97_0 : C 7 97 0 := by decide +kernel
theorem cell_7_97_1 : C 7 97 1 := by decide +kernel
theorem cell_7_97_2 : C 7 97 2 := by decide +kernel
theorem cell_7_97_3 : C 7 97 3 := by decide +kernel
theorem cell_7_97_4 : C 7 97 4 := by decide +kernel
theorem cell_7_97_5 : C 7 97 5 := by decide +kernel
theorem row_7_97 : ThresholdAt 7 97 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 97 0 cell_7_97_0
  | exact S 7 97 1 cell_7_97_1
  | exact S 7 97 2 cell_7_97_2
  | exact S 7 97 3 cell_7_97_3
  | exact S 7 97 4 cell_7_97_4
  | exact S 7 97 5 cell_7_97_5
theorem cell_7_98_0 : C 7 98 0 := by decide +kernel
theorem cell_7_98_1 : C 7 98 1 := by decide +kernel
theorem cell_7_98_2 : C 7 98 2 := by decide +kernel
theorem cell_7_98_3 : C 7 98 3 := by decide +kernel
theorem cell_7_98_4 : C 7 98 4 := by decide +kernel
theorem cell_7_98_5 : C 7 98 5 := by decide +kernel
theorem row_7_98 : ThresholdAt 7 98 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 98 0 cell_7_98_0
  | exact S 7 98 1 cell_7_98_1
  | exact S 7 98 2 cell_7_98_2
  | exact S 7 98 3 cell_7_98_3
  | exact S 7 98 4 cell_7_98_4
  | exact S 7 98 5 cell_7_98_5
theorem cell_7_99_0 : C 7 99 0 := by decide +kernel
theorem cell_7_99_1 : C 7 99 1 := by decide +kernel
theorem cell_7_99_2 : C 7 99 2 := by decide +kernel
theorem cell_7_99_3 : C 7 99 3 := by decide +kernel
theorem cell_7_99_4 : C 7 99 4 := by decide +kernel
theorem cell_7_99_5 : C 7 99 5 := by decide +kernel
theorem row_7_99 : ThresholdAt 7 99 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 99 0 cell_7_99_0
  | exact S 7 99 1 cell_7_99_1
  | exact S 7 99 2 cell_7_99_2
  | exact S 7 99 3 cell_7_99_3
  | exact S 7 99 4 cell_7_99_4
  | exact S 7 99 5 cell_7_99_5
theorem cell_7_100_0 : C 7 100 0 := by decide +kernel
theorem cell_7_100_1 : C 7 100 1 := by decide +kernel
theorem cell_7_100_2 : C 7 100 2 := by decide +kernel
theorem cell_7_100_3 : C 7 100 3 := by decide +kernel
theorem cell_7_100_4 : C 7 100 4 := by decide +kernel
theorem cell_7_100_5 : C 7 100 5 := by decide +kernel
theorem row_7_100 : ThresholdAt 7 100 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 100 0 cell_7_100_0
  | exact S 7 100 1 cell_7_100_1
  | exact S 7 100 2 cell_7_100_2
  | exact S 7 100 3 cell_7_100_3
  | exact S 7 100 4 cell_7_100_4
  | exact S 7 100 5 cell_7_100_5
theorem cell_7_101_0 : C 7 101 0 := by decide +kernel
theorem cell_7_101_1 : C 7 101 1 := by decide +kernel
theorem cell_7_101_2 : C 7 101 2 := by decide +kernel
theorem cell_7_101_3 : C 7 101 3 := by decide +kernel
theorem cell_7_101_4 : C 7 101 4 := by decide +kernel
theorem cell_7_101_5 : C 7 101 5 := by decide +kernel
theorem row_7_101 : ThresholdAt 7 101 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 101 0 cell_7_101_0
  | exact S 7 101 1 cell_7_101_1
  | exact S 7 101 2 cell_7_101_2
  | exact S 7 101 3 cell_7_101_3
  | exact S 7 101 4 cell_7_101_4
  | exact S 7 101 5 cell_7_101_5
theorem cell_7_102_0 : C 7 102 0 := by decide +kernel
theorem cell_7_102_1 : C 7 102 1 := by decide +kernel
theorem cell_7_102_2 : C 7 102 2 := by decide +kernel
theorem cell_7_102_3 : C 7 102 3 := by decide +kernel
theorem cell_7_102_4 : C 7 102 4 := by decide +kernel
theorem cell_7_102_5 : C 7 102 5 := by decide +kernel
theorem row_7_102 : ThresholdAt 7 102 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 102 0 cell_7_102_0
  | exact S 7 102 1 cell_7_102_1
  | exact S 7 102 2 cell_7_102_2
  | exact S 7 102 3 cell_7_102_3
  | exact S 7 102 4 cell_7_102_4
  | exact S 7 102 5 cell_7_102_5
theorem cell_7_103_0 : C 7 103 0 := by decide +kernel
theorem cell_7_103_1 : C 7 103 1 := by decide +kernel
theorem cell_7_103_2 : C 7 103 2 := by decide +kernel
theorem cell_7_103_3 : C 7 103 3 := by decide +kernel
theorem cell_7_103_4 : C 7 103 4 := by decide +kernel
theorem cell_7_103_5 : C 7 103 5 := by decide +kernel
theorem row_7_103 : ThresholdAt 7 103 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 103 0 cell_7_103_0
  | exact S 7 103 1 cell_7_103_1
  | exact S 7 103 2 cell_7_103_2
  | exact S 7 103 3 cell_7_103_3
  | exact S 7 103 4 cell_7_103_4
  | exact S 7 103 5 cell_7_103_5
theorem cell_7_104_0 : C 7 104 0 := by decide +kernel
theorem cell_7_104_1 : C 7 104 1 := by decide +kernel
theorem cell_7_104_2 : C 7 104 2 := by decide +kernel
theorem cell_7_104_3 : C 7 104 3 := by decide +kernel
theorem cell_7_104_4 : C 7 104 4 := by decide +kernel
theorem cell_7_104_5 : C 7 104 5 := by decide +kernel
theorem row_7_104 : ThresholdAt 7 104 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 104 0 cell_7_104_0
  | exact S 7 104 1 cell_7_104_1
  | exact S 7 104 2 cell_7_104_2
  | exact S 7 104 3 cell_7_104_3
  | exact S 7 104 4 cell_7_104_4
  | exact S 7 104 5 cell_7_104_5
theorem cell_7_105_0 : C 7 105 0 := by decide +kernel
theorem cell_7_105_1 : C 7 105 1 := by decide +kernel
theorem cell_7_105_2 : C 7 105 2 := by decide +kernel
theorem cell_7_105_3 : C 7 105 3 := by decide +kernel
theorem cell_7_105_4 : C 7 105 4 := by decide +kernel
theorem cell_7_105_5 : C 7 105 5 := by decide +kernel
theorem row_7_105 : ThresholdAt 7 105 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 105 0 cell_7_105_0
  | exact S 7 105 1 cell_7_105_1
  | exact S 7 105 2 cell_7_105_2
  | exact S 7 105 3 cell_7_105_3
  | exact S 7 105 4 cell_7_105_4
  | exact S 7 105 5 cell_7_105_5
theorem cell_7_106_0 : C 7 106 0 := by decide +kernel
theorem cell_7_106_1 : C 7 106 1 := by decide +kernel
theorem cell_7_106_2 : C 7 106 2 := by decide +kernel
theorem cell_7_106_3 : C 7 106 3 := by decide +kernel
theorem cell_7_106_4 : C 7 106 4 := by decide +kernel
theorem cell_7_106_5 : C 7 106 5 := by decide +kernel
theorem row_7_106 : ThresholdAt 7 106 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 106 0 cell_7_106_0
  | exact S 7 106 1 cell_7_106_1
  | exact S 7 106 2 cell_7_106_2
  | exact S 7 106 3 cell_7_106_3
  | exact S 7 106 4 cell_7_106_4
  | exact S 7 106 5 cell_7_106_5
theorem cell_7_107_0 : C 7 107 0 := by decide +kernel
theorem cell_7_107_1 : C 7 107 1 := by decide +kernel
theorem cell_7_107_2 : C 7 107 2 := by decide +kernel
theorem cell_7_107_3 : C 7 107 3 := by decide +kernel
theorem cell_7_107_4 : C 7 107 4 := by decide +kernel
theorem cell_7_107_5 : C 7 107 5 := by decide +kernel
theorem row_7_107 : ThresholdAt 7 107 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 107 0 cell_7_107_0
  | exact S 7 107 1 cell_7_107_1
  | exact S 7 107 2 cell_7_107_2
  | exact S 7 107 3 cell_7_107_3
  | exact S 7 107 4 cell_7_107_4
  | exact S 7 107 5 cell_7_107_5
theorem cell_7_108_0 : C 7 108 0 := by decide +kernel
theorem cell_7_108_1 : C 7 108 1 := by decide +kernel
theorem cell_7_108_2 : C 7 108 2 := by decide +kernel
theorem cell_7_108_3 : C 7 108 3 := by decide +kernel
theorem cell_7_108_4 : C 7 108 4 := by decide +kernel
theorem cell_7_108_5 : C 7 108 5 := by decide +kernel
theorem row_7_108 : ThresholdAt 7 108 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 108 0 cell_7_108_0
  | exact S 7 108 1 cell_7_108_1
  | exact S 7 108 2 cell_7_108_2
  | exact S 7 108 3 cell_7_108_3
  | exact S 7 108 4 cell_7_108_4
  | exact S 7 108 5 cell_7_108_5
theorem cell_7_109_0 : C 7 109 0 := by decide +kernel
theorem cell_7_109_1 : C 7 109 1 := by decide +kernel
theorem cell_7_109_2 : C 7 109 2 := by decide +kernel
theorem cell_7_109_3 : C 7 109 3 := by decide +kernel
theorem cell_7_109_4 : C 7 109 4 := by decide +kernel
theorem cell_7_109_5 : C 7 109 5 := by decide +kernel
theorem row_7_109 : ThresholdAt 7 109 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 109 0 cell_7_109_0
  | exact S 7 109 1 cell_7_109_1
  | exact S 7 109 2 cell_7_109_2
  | exact S 7 109 3 cell_7_109_3
  | exact S 7 109 4 cell_7_109_4
  | exact S 7 109 5 cell_7_109_5
theorem cell_7_110_0 : C 7 110 0 := by decide +kernel
theorem cell_7_110_1 : C 7 110 1 := by decide +kernel
theorem cell_7_110_2 : C 7 110 2 := by decide +kernel
theorem cell_7_110_3 : C 7 110 3 := by decide +kernel
theorem cell_7_110_4 : C 7 110 4 := by decide +kernel
theorem cell_7_110_5 : C 7 110 5 := by decide +kernel
theorem row_7_110 : ThresholdAt 7 110 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 110 0 cell_7_110_0
  | exact S 7 110 1 cell_7_110_1
  | exact S 7 110 2 cell_7_110_2
  | exact S 7 110 3 cell_7_110_3
  | exact S 7 110 4 cell_7_110_4
  | exact S 7 110 5 cell_7_110_5
theorem cell_7_111_0 : C 7 111 0 := by decide +kernel
theorem cell_7_111_1 : C 7 111 1 := by decide +kernel
theorem cell_7_111_2 : C 7 111 2 := by decide +kernel
theorem cell_7_111_3 : C 7 111 3 := by decide +kernel
theorem cell_7_111_4 : C 7 111 4 := by decide +kernel
theorem cell_7_111_5 : C 7 111 5 := by decide +kernel
theorem row_7_111 : ThresholdAt 7 111 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 111 0 cell_7_111_0
  | exact S 7 111 1 cell_7_111_1
  | exact S 7 111 2 cell_7_111_2
  | exact S 7 111 3 cell_7_111_3
  | exact S 7 111 4 cell_7_111_4
  | exact S 7 111 5 cell_7_111_5
theorem cell_7_112_0 : C 7 112 0 := by decide +kernel
theorem cell_7_112_1 : C 7 112 1 := by decide +kernel
theorem cell_7_112_2 : C 7 112 2 := by decide +kernel
theorem cell_7_112_3 : C 7 112 3 := by decide +kernel
theorem cell_7_112_4 : C 7 112 4 := by decide +kernel
theorem cell_7_112_5 : C 7 112 5 := by decide +kernel
theorem row_7_112 : ThresholdAt 7 112 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 112 0 cell_7_112_0
  | exact S 7 112 1 cell_7_112_1
  | exact S 7 112 2 cell_7_112_2
  | exact S 7 112 3 cell_7_112_3
  | exact S 7 112 4 cell_7_112_4
  | exact S 7 112 5 cell_7_112_5
theorem cell_7_113_0 : C 7 113 0 := by decide +kernel
theorem cell_7_113_1 : C 7 113 1 := by decide +kernel
theorem cell_7_113_2 : C 7 113 2 := by decide +kernel
theorem cell_7_113_3 : C 7 113 3 := by decide +kernel
theorem cell_7_113_4 : C 7 113 4 := by decide +kernel
theorem cell_7_113_5 : C 7 113 5 := by decide +kernel
theorem row_7_113 : ThresholdAt 7 113 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 113 0 cell_7_113_0
  | exact S 7 113 1 cell_7_113_1
  | exact S 7 113 2 cell_7_113_2
  | exact S 7 113 3 cell_7_113_3
  | exact S 7 113 4 cell_7_113_4
  | exact S 7 113 5 cell_7_113_5
theorem cell_7_114_0 : C 7 114 0 := by decide +kernel
theorem cell_7_114_1 : C 7 114 1 := by decide +kernel
theorem cell_7_114_2 : C 7 114 2 := by decide +kernel
theorem cell_7_114_3 : C 7 114 3 := by decide +kernel
theorem cell_7_114_4 : C 7 114 4 := by decide +kernel
theorem cell_7_114_5 : C 7 114 5 := by decide +kernel
theorem row_7_114 : ThresholdAt 7 114 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 114 0 cell_7_114_0
  | exact S 7 114 1 cell_7_114_1
  | exact S 7 114 2 cell_7_114_2
  | exact S 7 114 3 cell_7_114_3
  | exact S 7 114 4 cell_7_114_4
  | exact S 7 114 5 cell_7_114_5
theorem cell_7_115_0 : C 7 115 0 := by decide +kernel
theorem cell_7_115_1 : C 7 115 1 := by decide +kernel
theorem cell_7_115_2 : C 7 115 2 := by decide +kernel
theorem cell_7_115_3 : C 7 115 3 := by decide +kernel
theorem cell_7_115_4 : C 7 115 4 := by decide +kernel
theorem cell_7_115_5 : C 7 115 5 := by decide +kernel
theorem row_7_115 : ThresholdAt 7 115 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 115 0 cell_7_115_0
  | exact S 7 115 1 cell_7_115_1
  | exact S 7 115 2 cell_7_115_2
  | exact S 7 115 3 cell_7_115_3
  | exact S 7 115 4 cell_7_115_4
  | exact S 7 115 5 cell_7_115_5
theorem cell_7_116_0 : C 7 116 0 := by decide +kernel
theorem cell_7_116_1 : C 7 116 1 := by decide +kernel
theorem cell_7_116_2 : C 7 116 2 := by decide +kernel
theorem cell_7_116_3 : C 7 116 3 := by decide +kernel
theorem cell_7_116_4 : C 7 116 4 := by decide +kernel
theorem cell_7_116_5 : C 7 116 5 := by decide +kernel
theorem row_7_116 : ThresholdAt 7 116 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 116 0 cell_7_116_0
  | exact S 7 116 1 cell_7_116_1
  | exact S 7 116 2 cell_7_116_2
  | exact S 7 116 3 cell_7_116_3
  | exact S 7 116 4 cell_7_116_4
  | exact S 7 116 5 cell_7_116_5
theorem cell_7_117_0 : C 7 117 0 := by decide +kernel
theorem cell_7_117_1 : C 7 117 1 := by decide +kernel
theorem cell_7_117_2 : C 7 117 2 := by decide +kernel
theorem cell_7_117_3 : C 7 117 3 := by decide +kernel
theorem cell_7_117_4 : C 7 117 4 := by decide +kernel
theorem cell_7_117_5 : C 7 117 5 := by decide +kernel
theorem row_7_117 : ThresholdAt 7 117 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 117 0 cell_7_117_0
  | exact S 7 117 1 cell_7_117_1
  | exact S 7 117 2 cell_7_117_2
  | exact S 7 117 3 cell_7_117_3
  | exact S 7 117 4 cell_7_117_4
  | exact S 7 117 5 cell_7_117_5
theorem cell_7_118_0 : C 7 118 0 := by decide +kernel
theorem cell_7_118_1 : C 7 118 1 := by decide +kernel
theorem cell_7_118_2 : C 7 118 2 := by decide +kernel
theorem cell_7_118_3 : C 7 118 3 := by decide +kernel
theorem cell_7_118_4 : C 7 118 4 := by decide +kernel
theorem cell_7_118_5 : C 7 118 5 := by decide +kernel
theorem row_7_118 : ThresholdAt 7 118 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 118 0 cell_7_118_0
  | exact S 7 118 1 cell_7_118_1
  | exact S 7 118 2 cell_7_118_2
  | exact S 7 118 3 cell_7_118_3
  | exact S 7 118 4 cell_7_118_4
  | exact S 7 118 5 cell_7_118_5
theorem cell_7_119_0 : C 7 119 0 := by decide +kernel
theorem cell_7_119_1 : C 7 119 1 := by decide +kernel
theorem cell_7_119_2 : C 7 119 2 := by decide +kernel
theorem cell_7_119_3 : C 7 119 3 := by decide +kernel
theorem cell_7_119_4 : C 7 119 4 := by decide +kernel
theorem cell_7_119_5 : C 7 119 5 := by decide +kernel
theorem row_7_119 : ThresholdAt 7 119 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 119 0 cell_7_119_0
  | exact S 7 119 1 cell_7_119_1
  | exact S 7 119 2 cell_7_119_2
  | exact S 7 119 3 cell_7_119_3
  | exact S 7 119 4 cell_7_119_4
  | exact S 7 119 5 cell_7_119_5
theorem cell_7_120_0 : C 7 120 0 := by decide +kernel
theorem cell_7_120_1 : C 7 120 1 := by decide +kernel
theorem cell_7_120_2 : C 7 120 2 := by decide +kernel
theorem cell_7_120_3 : C 7 120 3 := by decide +kernel
theorem cell_7_120_4 : C 7 120 4 := by decide +kernel
theorem cell_7_120_5 : C 7 120 5 := by decide +kernel
theorem row_7_120 : ThresholdAt 7 120 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 120 0 cell_7_120_0
  | exact S 7 120 1 cell_7_120_1
  | exact S 7 120 2 cell_7_120_2
  | exact S 7 120 3 cell_7_120_3
  | exact S 7 120 4 cell_7_120_4
  | exact S 7 120 5 cell_7_120_5
theorem cell_7_121_0 : C 7 121 0 := by decide +kernel
theorem cell_7_121_1 : C 7 121 1 := by decide +kernel
theorem cell_7_121_2 : C 7 121 2 := by decide +kernel
theorem cell_7_121_3 : C 7 121 3 := by decide +kernel
theorem cell_7_121_4 : C 7 121 4 := by decide +kernel
theorem cell_7_121_5 : C 7 121 5 := by decide +kernel
theorem row_7_121 : ThresholdAt 7 121 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 121 0 cell_7_121_0
  | exact S 7 121 1 cell_7_121_1
  | exact S 7 121 2 cell_7_121_2
  | exact S 7 121 3 cell_7_121_3
  | exact S 7 121 4 cell_7_121_4
  | exact S 7 121 5 cell_7_121_5
theorem cell_7_122_0 : C 7 122 0 := by decide +kernel
theorem cell_7_122_1 : C 7 122 1 := by decide +kernel
theorem cell_7_122_2 : C 7 122 2 := by decide +kernel
theorem cell_7_122_3 : C 7 122 3 := by decide +kernel
theorem cell_7_122_4 : C 7 122 4 := by decide +kernel
theorem cell_7_122_5 : C 7 122 5 := by decide +kernel
theorem row_7_122 : ThresholdAt 7 122 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 122 0 cell_7_122_0
  | exact S 7 122 1 cell_7_122_1
  | exact S 7 122 2 cell_7_122_2
  | exact S 7 122 3 cell_7_122_3
  | exact S 7 122 4 cell_7_122_4
  | exact S 7 122 5 cell_7_122_5
theorem cell_7_123_0 : C 7 123 0 := by decide +kernel
theorem cell_7_123_1 : C 7 123 1 := by decide +kernel
theorem cell_7_123_2 : C 7 123 2 := by decide +kernel
theorem cell_7_123_3 : C 7 123 3 := by decide +kernel
theorem cell_7_123_4 : C 7 123 4 := by decide +kernel
theorem cell_7_123_5 : C 7 123 5 := by decide +kernel
theorem row_7_123 : ThresholdAt 7 123 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 123 0 cell_7_123_0
  | exact S 7 123 1 cell_7_123_1
  | exact S 7 123 2 cell_7_123_2
  | exact S 7 123 3 cell_7_123_3
  | exact S 7 123 4 cell_7_123_4
  | exact S 7 123 5 cell_7_123_5
theorem cell_7_124_0 : C 7 124 0 := by decide +kernel
theorem cell_7_124_1 : C 7 124 1 := by decide +kernel
theorem cell_7_124_2 : C 7 124 2 := by decide +kernel
theorem cell_7_124_3 : C 7 124 3 := by decide +kernel
theorem cell_7_124_4 : C 7 124 4 := by decide +kernel
theorem cell_7_124_5 : C 7 124 5 := by decide +kernel
theorem row_7_124 : ThresholdAt 7 124 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 124 0 cell_7_124_0
  | exact S 7 124 1 cell_7_124_1
  | exact S 7 124 2 cell_7_124_2
  | exact S 7 124 3 cell_7_124_3
  | exact S 7 124 4 cell_7_124_4
  | exact S 7 124 5 cell_7_124_5
theorem cell_7_125_0 : C 7 125 0 := by decide +kernel
theorem cell_7_125_1 : C 7 125 1 := by decide +kernel
theorem cell_7_125_2 : C 7 125 2 := by decide +kernel
theorem cell_7_125_3 : C 7 125 3 := by decide +kernel
theorem cell_7_125_4 : C 7 125 4 := by decide +kernel
theorem cell_7_125_5 : C 7 125 5 := by decide +kernel
theorem row_7_125 : ThresholdAt 7 125 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 125 0 cell_7_125_0
  | exact S 7 125 1 cell_7_125_1
  | exact S 7 125 2 cell_7_125_2
  | exact S 7 125 3 cell_7_125_3
  | exact S 7 125 4 cell_7_125_4
  | exact S 7 125 5 cell_7_125_5
theorem cell_7_126_0 : C 7 126 0 := by decide +kernel
theorem cell_7_126_1 : C 7 126 1 := by decide +kernel
theorem cell_7_126_2 : C 7 126 2 := by decide +kernel
theorem cell_7_126_3 : C 7 126 3 := by decide +kernel
theorem cell_7_126_4 : C 7 126 4 := by decide +kernel
theorem cell_7_126_5 : C 7 126 5 := by decide +kernel
theorem row_7_126 : ThresholdAt 7 126 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 126 0 cell_7_126_0
  | exact S 7 126 1 cell_7_126_1
  | exact S 7 126 2 cell_7_126_2
  | exact S 7 126 3 cell_7_126_3
  | exact S 7 126 4 cell_7_126_4
  | exact S 7 126 5 cell_7_126_5
theorem cell_7_127_0 : C 7 127 0 := by decide +kernel
theorem cell_7_127_1 : C 7 127 1 := by decide +kernel
theorem cell_7_127_2 : C 7 127 2 := by decide +kernel
theorem cell_7_127_3 : C 7 127 3 := by decide +kernel
theorem cell_7_127_4 : C 7 127 4 := by decide +kernel
theorem cell_7_127_5 : C 7 127 5 := by decide +kernel
theorem row_7_127 : ThresholdAt 7 127 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 127 0 cell_7_127_0
  | exact S 7 127 1 cell_7_127_1
  | exact S 7 127 2 cell_7_127_2
  | exact S 7 127 3 cell_7_127_3
  | exact S 7 127 4 cell_7_127_4
  | exact S 7 127 5 cell_7_127_5
theorem cell_7_128_0 : C 7 128 0 := by decide +kernel
theorem cell_7_128_1 : C 7 128 1 := by decide +kernel
theorem cell_7_128_2 : C 7 128 2 := by decide +kernel
theorem cell_7_128_3 : C 7 128 3 := by decide +kernel
theorem cell_7_128_4 : C 7 128 4 := by decide +kernel
theorem cell_7_128_5 : C 7 128 5 := by decide +kernel
theorem row_7_128 : ThresholdAt 7 128 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 128 0 cell_7_128_0
  | exact S 7 128 1 cell_7_128_1
  | exact S 7 128 2 cell_7_128_2
  | exact S 7 128 3 cell_7_128_3
  | exact S 7 128 4 cell_7_128_4
  | exact S 7 128 5 cell_7_128_5
theorem cell_7_129_0 : C 7 129 0 := by decide +kernel
theorem cell_7_129_1 : C 7 129 1 := by decide +kernel
theorem cell_7_129_2 : C 7 129 2 := by decide +kernel
theorem cell_7_129_3 : C 7 129 3 := by decide +kernel
theorem cell_7_129_4 : C 7 129 4 := by decide +kernel
theorem cell_7_129_5 : C 7 129 5 := by decide +kernel
theorem row_7_129 : ThresholdAt 7 129 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 129 0 cell_7_129_0
  | exact S 7 129 1 cell_7_129_1
  | exact S 7 129 2 cell_7_129_2
  | exact S 7 129 3 cell_7_129_3
  | exact S 7 129 4 cell_7_129_4
  | exact S 7 129 5 cell_7_129_5
theorem cell_7_130_0 : C 7 130 0 := by decide +kernel
theorem cell_7_130_1 : C 7 130 1 := by decide +kernel
theorem cell_7_130_2 : C 7 130 2 := by decide +kernel
theorem cell_7_130_3 : C 7 130 3 := by decide +kernel
theorem cell_7_130_4 : C 7 130 4 := by decide +kernel
theorem cell_7_130_5 : C 7 130 5 := by decide +kernel
theorem row_7_130 : ThresholdAt 7 130 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 130 0 cell_7_130_0
  | exact S 7 130 1 cell_7_130_1
  | exact S 7 130 2 cell_7_130_2
  | exact S 7 130 3 cell_7_130_3
  | exact S 7 130 4 cell_7_130_4
  | exact S 7 130 5 cell_7_130_5
theorem cell_7_131_0 : C 7 131 0 := by decide +kernel
theorem cell_7_131_1 : C 7 131 1 := by decide +kernel
theorem cell_7_131_2 : C 7 131 2 := by decide +kernel
theorem cell_7_131_3 : C 7 131 3 := by decide +kernel
theorem cell_7_131_4 : C 7 131 4 := by decide +kernel
theorem cell_7_131_5 : C 7 131 5 := by decide +kernel
theorem row_7_131 : ThresholdAt 7 131 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 131 0 cell_7_131_0
  | exact S 7 131 1 cell_7_131_1
  | exact S 7 131 2 cell_7_131_2
  | exact S 7 131 3 cell_7_131_3
  | exact S 7 131 4 cell_7_131_4
  | exact S 7 131 5 cell_7_131_5
theorem cell_7_132_0 : C 7 132 0 := by decide +kernel
theorem cell_7_132_1 : C 7 132 1 := by decide +kernel
theorem cell_7_132_2 : C 7 132 2 := by decide +kernel
theorem cell_7_132_3 : C 7 132 3 := by decide +kernel
theorem cell_7_132_4 : C 7 132 4 := by decide +kernel
theorem cell_7_132_5 : C 7 132 5 := by decide +kernel
theorem row_7_132 : ThresholdAt 7 132 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 7 132 0 cell_7_132_0
  | exact S 7 132 1 cell_7_132_1
  | exact S 7 132 2 cell_7_132_2
  | exact S 7 132 3 cell_7_132_3
  | exact S 7 132 4 cell_7_132_4
  | exact S 7 132 5 cell_7_132_5
theorem checkedR7 : ∀ V ∈ List.range 133, ThresholdAt 7 V := by
  intro V hV
  have hv : V < 133 := List.mem_range.mp hV
  by_cases h0_133 : V < 66
  · by_cases h0_66 : V < 33
    · by_cases h0_33 : V < 16
      · by_cases h0_16 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have he : V = 0 := by omega
                subst V
                exact row_7_0
              · have he : V = 1 := by omega
                subst V
                exact row_7_1
            · by_cases h2_4 : V < 3
              · have he : V = 2 := by omega
                subst V
                exact row_7_2
              · have he : V = 3 := by omega
                subst V
                exact row_7_3
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have he : V = 4 := by omega
                subst V
                exact row_7_4
              · have he : V = 5 := by omega
                subst V
                exact row_7_5
            · by_cases h6_8 : V < 7
              · have he : V = 6 := by omega
                subst V
                exact row_7_6
              · have he : V = 7 := by omega
                subst V
                exact row_7_7
        · by_cases h8_16 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have he : V = 8 := by omega
                subst V
                exact row_7_8
              · have he : V = 9 := by omega
                subst V
                exact row_7_9
            · by_cases h10_12 : V < 11
              · have he : V = 10 := by omega
                subst V
                exact row_7_10
              · have he : V = 11 := by omega
                subst V
                exact row_7_11
          · by_cases h12_16 : V < 14
            · by_cases h12_14 : V < 13
              · have he : V = 12 := by omega
                subst V
                exact row_7_12
              · have he : V = 13 := by omega
                subst V
                exact row_7_13
            · by_cases h14_16 : V < 15
              · have he : V = 14 := by omega
                subst V
                exact row_7_14
              · have he : V = 15 := by omega
                subst V
                exact row_7_15
      · by_cases h16_33 : V < 24
        · by_cases h16_24 : V < 20
          · by_cases h16_20 : V < 18
            · by_cases h16_18 : V < 17
              · have he : V = 16 := by omega
                subst V
                exact row_7_16
              · have he : V = 17 := by omega
                subst V
                exact row_7_17
            · by_cases h18_20 : V < 19
              · have he : V = 18 := by omega
                subst V
                exact row_7_18
              · have he : V = 19 := by omega
                subst V
                exact row_7_19
          · by_cases h20_24 : V < 22
            · by_cases h20_22 : V < 21
              · have he : V = 20 := by omega
                subst V
                exact row_7_20
              · have he : V = 21 := by omega
                subst V
                exact row_7_21
            · by_cases h22_24 : V < 23
              · have he : V = 22 := by omega
                subst V
                exact row_7_22
              · have he : V = 23 := by omega
                subst V
                exact row_7_23
        · by_cases h24_33 : V < 28
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have he : V = 24 := by omega
                subst V
                exact row_7_24
              · have he : V = 25 := by omega
                subst V
                exact row_7_25
            · by_cases h26_28 : V < 27
              · have he : V = 26 := by omega
                subst V
                exact row_7_26
              · have he : V = 27 := by omega
                subst V
                exact row_7_27
          · by_cases h28_33 : V < 30
            · by_cases h28_30 : V < 29
              · have he : V = 28 := by omega
                subst V
                exact row_7_28
              · have he : V = 29 := by omega
                subst V
                exact row_7_29
            · by_cases h30_33 : V < 31
              · have he : V = 30 := by omega
                subst V
                exact row_7_30
              · by_cases h31_33 : V < 32
                · have he : V = 31 := by omega
                  subst V
                  exact row_7_31
                · have he : V = 32 := by omega
                  subst V
                  exact row_7_32
    · by_cases h33_66 : V < 49
      · by_cases h33_49 : V < 41
        · by_cases h33_41 : V < 37
          · by_cases h33_37 : V < 35
            · by_cases h33_35 : V < 34
              · have he : V = 33 := by omega
                subst V
                exact row_7_33
              · have he : V = 34 := by omega
                subst V
                exact row_7_34
            · by_cases h35_37 : V < 36
              · have he : V = 35 := by omega
                subst V
                exact row_7_35
              · have he : V = 36 := by omega
                subst V
                exact row_7_36
          · by_cases h37_41 : V < 39
            · by_cases h37_39 : V < 38
              · have he : V = 37 := by omega
                subst V
                exact row_7_37
              · have he : V = 38 := by omega
                subst V
                exact row_7_38
            · by_cases h39_41 : V < 40
              · have he : V = 39 := by omega
                subst V
                exact row_7_39
              · have he : V = 40 := by omega
                subst V
                exact row_7_40
        · by_cases h41_49 : V < 45
          · by_cases h41_45 : V < 43
            · by_cases h41_43 : V < 42
              · have he : V = 41 := by omega
                subst V
                exact row_7_41
              · have he : V = 42 := by omega
                subst V
                exact row_7_42
            · by_cases h43_45 : V < 44
              · have he : V = 43 := by omega
                subst V
                exact row_7_43
              · have he : V = 44 := by omega
                subst V
                exact row_7_44
          · by_cases h45_49 : V < 47
            · by_cases h45_47 : V < 46
              · have he : V = 45 := by omega
                subst V
                exact row_7_45
              · have he : V = 46 := by omega
                subst V
                exact row_7_46
            · by_cases h47_49 : V < 48
              · have he : V = 47 := by omega
                subst V
                exact row_7_47
              · have he : V = 48 := by omega
                subst V
                exact row_7_48
      · by_cases h49_66 : V < 57
        · by_cases h49_57 : V < 53
          · by_cases h49_53 : V < 51
            · by_cases h49_51 : V < 50
              · have he : V = 49 := by omega
                subst V
                exact row_7_49
              · have he : V = 50 := by omega
                subst V
                exact row_7_50
            · by_cases h51_53 : V < 52
              · have he : V = 51 := by omega
                subst V
                exact row_7_51
              · have he : V = 52 := by omega
                subst V
                exact row_7_52
          · by_cases h53_57 : V < 55
            · by_cases h53_55 : V < 54
              · have he : V = 53 := by omega
                subst V
                exact row_7_53
              · have he : V = 54 := by omega
                subst V
                exact row_7_54
            · by_cases h55_57 : V < 56
              · have he : V = 55 := by omega
                subst V
                exact row_7_55
              · have he : V = 56 := by omega
                subst V
                exact row_7_56
        · by_cases h57_66 : V < 61
          · by_cases h57_61 : V < 59
            · by_cases h57_59 : V < 58
              · have he : V = 57 := by omega
                subst V
                exact row_7_57
              · have he : V = 58 := by omega
                subst V
                exact row_7_58
            · by_cases h59_61 : V < 60
              · have he : V = 59 := by omega
                subst V
                exact row_7_59
              · have he : V = 60 := by omega
                subst V
                exact row_7_60
          · by_cases h61_66 : V < 63
            · by_cases h61_63 : V < 62
              · have he : V = 61 := by omega
                subst V
                exact row_7_61
              · have he : V = 62 := by omega
                subst V
                exact row_7_62
            · by_cases h63_66 : V < 64
              · have he : V = 63 := by omega
                subst V
                exact row_7_63
              · by_cases h64_66 : V < 65
                · have he : V = 64 := by omega
                  subst V
                  exact row_7_64
                · have he : V = 65 := by omega
                  subst V
                  exact row_7_65
  · by_cases h66_133 : V < 99
    · by_cases h66_99 : V < 82
      · by_cases h66_82 : V < 74
        · by_cases h66_74 : V < 70
          · by_cases h66_70 : V < 68
            · by_cases h66_68 : V < 67
              · have he : V = 66 := by omega
                subst V
                exact row_7_66
              · have he : V = 67 := by omega
                subst V
                exact row_7_67
            · by_cases h68_70 : V < 69
              · have he : V = 68 := by omega
                subst V
                exact row_7_68
              · have he : V = 69 := by omega
                subst V
                exact row_7_69
          · by_cases h70_74 : V < 72
            · by_cases h70_72 : V < 71
              · have he : V = 70 := by omega
                subst V
                exact row_7_70
              · have he : V = 71 := by omega
                subst V
                exact row_7_71
            · by_cases h72_74 : V < 73
              · have he : V = 72 := by omega
                subst V
                exact row_7_72
              · have he : V = 73 := by omega
                subst V
                exact row_7_73
        · by_cases h74_82 : V < 78
          · by_cases h74_78 : V < 76
            · by_cases h74_76 : V < 75
              · have he : V = 74 := by omega
                subst V
                exact row_7_74
              · have he : V = 75 := by omega
                subst V
                exact row_7_75
            · by_cases h76_78 : V < 77
              · have he : V = 76 := by omega
                subst V
                exact row_7_76
              · have he : V = 77 := by omega
                subst V
                exact row_7_77
          · by_cases h78_82 : V < 80
            · by_cases h78_80 : V < 79
              · have he : V = 78 := by omega
                subst V
                exact row_7_78
              · have he : V = 79 := by omega
                subst V
                exact row_7_79
            · by_cases h80_82 : V < 81
              · have he : V = 80 := by omega
                subst V
                exact row_7_80
              · have he : V = 81 := by omega
                subst V
                exact row_7_81
      · by_cases h82_99 : V < 90
        · by_cases h82_90 : V < 86
          · by_cases h82_86 : V < 84
            · by_cases h82_84 : V < 83
              · have he : V = 82 := by omega
                subst V
                exact row_7_82
              · have he : V = 83 := by omega
                subst V
                exact row_7_83
            · by_cases h84_86 : V < 85
              · have he : V = 84 := by omega
                subst V
                exact row_7_84
              · have he : V = 85 := by omega
                subst V
                exact row_7_85
          · by_cases h86_90 : V < 88
            · by_cases h86_88 : V < 87
              · have he : V = 86 := by omega
                subst V
                exact row_7_86
              · have he : V = 87 := by omega
                subst V
                exact row_7_87
            · by_cases h88_90 : V < 89
              · have he : V = 88 := by omega
                subst V
                exact row_7_88
              · have he : V = 89 := by omega
                subst V
                exact row_7_89
        · by_cases h90_99 : V < 94
          · by_cases h90_94 : V < 92
            · by_cases h90_92 : V < 91
              · have he : V = 90 := by omega
                subst V
                exact row_7_90
              · have he : V = 91 := by omega
                subst V
                exact row_7_91
            · by_cases h92_94 : V < 93
              · have he : V = 92 := by omega
                subst V
                exact row_7_92
              · have he : V = 93 := by omega
                subst V
                exact row_7_93
          · by_cases h94_99 : V < 96
            · by_cases h94_96 : V < 95
              · have he : V = 94 := by omega
                subst V
                exact row_7_94
              · have he : V = 95 := by omega
                subst V
                exact row_7_95
            · by_cases h96_99 : V < 97
              · have he : V = 96 := by omega
                subst V
                exact row_7_96
              · by_cases h97_99 : V < 98
                · have he : V = 97 := by omega
                  subst V
                  exact row_7_97
                · have he : V = 98 := by omega
                  subst V
                  exact row_7_98
    · by_cases h99_133 : V < 116
      · by_cases h99_116 : V < 107
        · by_cases h99_107 : V < 103
          · by_cases h99_103 : V < 101
            · by_cases h99_101 : V < 100
              · have he : V = 99 := by omega
                subst V
                exact row_7_99
              · have he : V = 100 := by omega
                subst V
                exact row_7_100
            · by_cases h101_103 : V < 102
              · have he : V = 101 := by omega
                subst V
                exact row_7_101
              · have he : V = 102 := by omega
                subst V
                exact row_7_102
          · by_cases h103_107 : V < 105
            · by_cases h103_105 : V < 104
              · have he : V = 103 := by omega
                subst V
                exact row_7_103
              · have he : V = 104 := by omega
                subst V
                exact row_7_104
            · by_cases h105_107 : V < 106
              · have he : V = 105 := by omega
                subst V
                exact row_7_105
              · have he : V = 106 := by omega
                subst V
                exact row_7_106
        · by_cases h107_116 : V < 111
          · by_cases h107_111 : V < 109
            · by_cases h107_109 : V < 108
              · have he : V = 107 := by omega
                subst V
                exact row_7_107
              · have he : V = 108 := by omega
                subst V
                exact row_7_108
            · by_cases h109_111 : V < 110
              · have he : V = 109 := by omega
                subst V
                exact row_7_109
              · have he : V = 110 := by omega
                subst V
                exact row_7_110
          · by_cases h111_116 : V < 113
            · by_cases h111_113 : V < 112
              · have he : V = 111 := by omega
                subst V
                exact row_7_111
              · have he : V = 112 := by omega
                subst V
                exact row_7_112
            · by_cases h113_116 : V < 114
              · have he : V = 113 := by omega
                subst V
                exact row_7_113
              · by_cases h114_116 : V < 115
                · have he : V = 114 := by omega
                  subst V
                  exact row_7_114
                · have he : V = 115 := by omega
                  subst V
                  exact row_7_115
      · by_cases h116_133 : V < 124
        · by_cases h116_124 : V < 120
          · by_cases h116_120 : V < 118
            · by_cases h116_118 : V < 117
              · have he : V = 116 := by omega
                subst V
                exact row_7_116
              · have he : V = 117 := by omega
                subst V
                exact row_7_117
            · by_cases h118_120 : V < 119
              · have he : V = 118 := by omega
                subst V
                exact row_7_118
              · have he : V = 119 := by omega
                subst V
                exact row_7_119
          · by_cases h120_124 : V < 122
            · by_cases h120_122 : V < 121
              · have he : V = 120 := by omega
                subst V
                exact row_7_120
              · have he : V = 121 := by omega
                subst V
                exact row_7_121
            · by_cases h122_124 : V < 123
              · have he : V = 122 := by omega
                subst V
                exact row_7_122
              · have he : V = 123 := by omega
                subst V
                exact row_7_123
        · by_cases h124_133 : V < 128
          · by_cases h124_128 : V < 126
            · by_cases h124_126 : V < 125
              · have he : V = 124 := by omega
                subst V
                exact row_7_124
              · have he : V = 125 := by omega
                subst V
                exact row_7_125
            · by_cases h126_128 : V < 127
              · have he : V = 126 := by omega
                subst V
                exact row_7_126
              · have he : V = 127 := by omega
                subst V
                exact row_7_127
          · by_cases h128_133 : V < 130
            · by_cases h128_130 : V < 129
              · have he : V = 128 := by omega
                subst V
                exact row_7_128
              · have he : V = 129 := by omega
                subst V
                exact row_7_129
            · by_cases h130_133 : V < 131
              · have he : V = 130 := by omega
                subst V
                exact row_7_130
              · by_cases h131_133 : V < 132
                · have he : V = 131 := by omega
                  subst V
                  exact row_7_131
                · have he : V = 132 := by omega
                  subst V
                  exact row_7_132
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
