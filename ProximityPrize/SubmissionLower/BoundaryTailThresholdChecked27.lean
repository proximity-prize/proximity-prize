import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked26

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_27_0_0 : C 27 0 0 := by decide +kernel
theorem cell_27_0_1 : C 27 0 1 := by decide +kernel
theorem cell_27_0_2 : C 27 0 2 := by decide +kernel
theorem cell_27_0_3 : C 27 0 3 := by decide +kernel
theorem cell_27_0_4 : C 27 0 4 := by decide +kernel
theorem cell_27_0_5 : C 27 0 5 := by decide +kernel
theorem row_27_0 : ThresholdAt 27 0 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 0 0 cell_27_0_0
  | exact S 27 0 1 cell_27_0_1
  | exact S 27 0 2 cell_27_0_2
  | exact S 27 0 3 cell_27_0_3
  | exact S 27 0 4 cell_27_0_4
  | exact S 27 0 5 cell_27_0_5
theorem cell_27_1_0 : C 27 1 0 := by decide +kernel
theorem cell_27_1_1 : C 27 1 1 := by decide +kernel
theorem cell_27_1_2 : C 27 1 2 := by decide +kernel
theorem cell_27_1_3 : C 27 1 3 := by decide +kernel
theorem cell_27_1_4 : C 27 1 4 := by decide +kernel
theorem cell_27_1_5 : C 27 1 5 := by decide +kernel
theorem row_27_1 : ThresholdAt 27 1 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 1 0 cell_27_1_0
  | exact S 27 1 1 cell_27_1_1
  | exact S 27 1 2 cell_27_1_2
  | exact S 27 1 3 cell_27_1_3
  | exact S 27 1 4 cell_27_1_4
  | exact S 27 1 5 cell_27_1_5
theorem cell_27_2_0 : C 27 2 0 := by decide +kernel
theorem cell_27_2_1 : C 27 2 1 := by decide +kernel
theorem cell_27_2_2 : C 27 2 2 := by decide +kernel
theorem cell_27_2_3 : C 27 2 3 := by decide +kernel
theorem cell_27_2_4 : C 27 2 4 := by decide +kernel
theorem cell_27_2_5 : C 27 2 5 := by decide +kernel
theorem row_27_2 : ThresholdAt 27 2 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 2 0 cell_27_2_0
  | exact S 27 2 1 cell_27_2_1
  | exact S 27 2 2 cell_27_2_2
  | exact S 27 2 3 cell_27_2_3
  | exact S 27 2 4 cell_27_2_4
  | exact S 27 2 5 cell_27_2_5
theorem cell_27_3_0 : C 27 3 0 := by decide +kernel
theorem cell_27_3_1 : C 27 3 1 := by decide +kernel
theorem cell_27_3_2 : C 27 3 2 := by decide +kernel
theorem cell_27_3_3 : C 27 3 3 := by decide +kernel
theorem cell_27_3_4 : C 27 3 4 := by decide +kernel
theorem cell_27_3_5 : C 27 3 5 := by decide +kernel
theorem row_27_3 : ThresholdAt 27 3 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 3 0 cell_27_3_0
  | exact S 27 3 1 cell_27_3_1
  | exact S 27 3 2 cell_27_3_2
  | exact S 27 3 3 cell_27_3_3
  | exact S 27 3 4 cell_27_3_4
  | exact S 27 3 5 cell_27_3_5
theorem cell_27_4_0 : C 27 4 0 := by decide +kernel
theorem cell_27_4_1 : C 27 4 1 := by decide +kernel
theorem cell_27_4_2 : C 27 4 2 := by decide +kernel
theorem cell_27_4_3 : C 27 4 3 := by decide +kernel
theorem cell_27_4_4 : C 27 4 4 := by decide +kernel
theorem cell_27_4_5 : C 27 4 5 := by decide +kernel
theorem row_27_4 : ThresholdAt 27 4 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 4 0 cell_27_4_0
  | exact S 27 4 1 cell_27_4_1
  | exact S 27 4 2 cell_27_4_2
  | exact S 27 4 3 cell_27_4_3
  | exact S 27 4 4 cell_27_4_4
  | exact S 27 4 5 cell_27_4_5
theorem cell_27_5_0 : C 27 5 0 := by decide +kernel
theorem cell_27_5_1 : C 27 5 1 := by decide +kernel
theorem cell_27_5_2 : C 27 5 2 := by decide +kernel
theorem cell_27_5_3 : C 27 5 3 := by decide +kernel
theorem cell_27_5_4 : C 27 5 4 := by decide +kernel
theorem cell_27_5_5 : C 27 5 5 := by decide +kernel
theorem row_27_5 : ThresholdAt 27 5 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 5 0 cell_27_5_0
  | exact S 27 5 1 cell_27_5_1
  | exact S 27 5 2 cell_27_5_2
  | exact S 27 5 3 cell_27_5_3
  | exact S 27 5 4 cell_27_5_4
  | exact S 27 5 5 cell_27_5_5
theorem cell_27_6_0 : C 27 6 0 := by decide +kernel
theorem cell_27_6_1 : C 27 6 1 := by decide +kernel
theorem cell_27_6_2 : C 27 6 2 := by decide +kernel
theorem cell_27_6_3 : C 27 6 3 := by decide +kernel
theorem cell_27_6_4 : C 27 6 4 := by decide +kernel
theorem cell_27_6_5 : C 27 6 5 := by decide +kernel
theorem row_27_6 : ThresholdAt 27 6 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 6 0 cell_27_6_0
  | exact S 27 6 1 cell_27_6_1
  | exact S 27 6 2 cell_27_6_2
  | exact S 27 6 3 cell_27_6_3
  | exact S 27 6 4 cell_27_6_4
  | exact S 27 6 5 cell_27_6_5
theorem cell_27_7_0 : C 27 7 0 := by decide +kernel
theorem cell_27_7_1 : C 27 7 1 := by decide +kernel
theorem cell_27_7_2 : C 27 7 2 := by decide +kernel
theorem cell_27_7_3 : C 27 7 3 := by decide +kernel
theorem cell_27_7_4 : C 27 7 4 := by decide +kernel
theorem cell_27_7_5 : C 27 7 5 := by decide +kernel
theorem row_27_7 : ThresholdAt 27 7 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 7 0 cell_27_7_0
  | exact S 27 7 1 cell_27_7_1
  | exact S 27 7 2 cell_27_7_2
  | exact S 27 7 3 cell_27_7_3
  | exact S 27 7 4 cell_27_7_4
  | exact S 27 7 5 cell_27_7_5
theorem cell_27_8_0 : C 27 8 0 := by decide +kernel
theorem cell_27_8_1 : C 27 8 1 := by decide +kernel
theorem cell_27_8_2 : C 27 8 2 := by decide +kernel
theorem cell_27_8_3 : C 27 8 3 := by decide +kernel
theorem cell_27_8_4 : C 27 8 4 := by decide +kernel
theorem cell_27_8_5 : C 27 8 5 := by decide +kernel
theorem row_27_8 : ThresholdAt 27 8 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 8 0 cell_27_8_0
  | exact S 27 8 1 cell_27_8_1
  | exact S 27 8 2 cell_27_8_2
  | exact S 27 8 3 cell_27_8_3
  | exact S 27 8 4 cell_27_8_4
  | exact S 27 8 5 cell_27_8_5
theorem cell_27_9_0 : C 27 9 0 := by decide +kernel
theorem cell_27_9_1 : C 27 9 1 := by decide +kernel
theorem cell_27_9_2 : C 27 9 2 := by decide +kernel
theorem cell_27_9_3 : C 27 9 3 := by decide +kernel
theorem cell_27_9_4 : C 27 9 4 := by decide +kernel
theorem cell_27_9_5 : C 27 9 5 := by decide +kernel
theorem row_27_9 : ThresholdAt 27 9 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 9 0 cell_27_9_0
  | exact S 27 9 1 cell_27_9_1
  | exact S 27 9 2 cell_27_9_2
  | exact S 27 9 3 cell_27_9_3
  | exact S 27 9 4 cell_27_9_4
  | exact S 27 9 5 cell_27_9_5
theorem cell_27_10_0 : C 27 10 0 := by decide +kernel
theorem cell_27_10_1 : C 27 10 1 := by decide +kernel
theorem cell_27_10_2 : C 27 10 2 := by decide +kernel
theorem cell_27_10_3 : C 27 10 3 := by decide +kernel
theorem cell_27_10_4 : C 27 10 4 := by decide +kernel
theorem cell_27_10_5 : C 27 10 5 := by decide +kernel
theorem row_27_10 : ThresholdAt 27 10 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 10 0 cell_27_10_0
  | exact S 27 10 1 cell_27_10_1
  | exact S 27 10 2 cell_27_10_2
  | exact S 27 10 3 cell_27_10_3
  | exact S 27 10 4 cell_27_10_4
  | exact S 27 10 5 cell_27_10_5
theorem cell_27_11_0 : C 27 11 0 := by decide +kernel
theorem cell_27_11_1 : C 27 11 1 := by decide +kernel
theorem cell_27_11_2 : C 27 11 2 := by decide +kernel
theorem cell_27_11_3 : C 27 11 3 := by decide +kernel
theorem cell_27_11_4 : C 27 11 4 := by decide +kernel
theorem cell_27_11_5 : C 27 11 5 := by decide +kernel
theorem row_27_11 : ThresholdAt 27 11 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 11 0 cell_27_11_0
  | exact S 27 11 1 cell_27_11_1
  | exact S 27 11 2 cell_27_11_2
  | exact S 27 11 3 cell_27_11_3
  | exact S 27 11 4 cell_27_11_4
  | exact S 27 11 5 cell_27_11_5
theorem cell_27_12_0 : C 27 12 0 := by decide +kernel
theorem cell_27_12_1 : C 27 12 1 := by decide +kernel
theorem cell_27_12_2 : C 27 12 2 := by decide +kernel
theorem cell_27_12_3 : C 27 12 3 := by decide +kernel
theorem cell_27_12_4 : C 27 12 4 := by decide +kernel
theorem cell_27_12_5 : C 27 12 5 := by decide +kernel
theorem row_27_12 : ThresholdAt 27 12 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 12 0 cell_27_12_0
  | exact S 27 12 1 cell_27_12_1
  | exact S 27 12 2 cell_27_12_2
  | exact S 27 12 3 cell_27_12_3
  | exact S 27 12 4 cell_27_12_4
  | exact S 27 12 5 cell_27_12_5
theorem cell_27_13_0 : C 27 13 0 := by decide +kernel
theorem cell_27_13_1 : C 27 13 1 := by decide +kernel
theorem cell_27_13_2 : C 27 13 2 := by decide +kernel
theorem cell_27_13_3 : C 27 13 3 := by decide +kernel
theorem cell_27_13_4 : C 27 13 4 := by decide +kernel
theorem cell_27_13_5 : C 27 13 5 := by decide +kernel
theorem row_27_13 : ThresholdAt 27 13 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 13 0 cell_27_13_0
  | exact S 27 13 1 cell_27_13_1
  | exact S 27 13 2 cell_27_13_2
  | exact S 27 13 3 cell_27_13_3
  | exact S 27 13 4 cell_27_13_4
  | exact S 27 13 5 cell_27_13_5
theorem cell_27_14_0 : C 27 14 0 := by decide +kernel
theorem cell_27_14_1 : C 27 14 1 := by decide +kernel
theorem cell_27_14_2 : C 27 14 2 := by decide +kernel
theorem cell_27_14_3 : C 27 14 3 := by decide +kernel
theorem cell_27_14_4 : C 27 14 4 := by decide +kernel
theorem cell_27_14_5 : C 27 14 5 := by decide +kernel
theorem row_27_14 : ThresholdAt 27 14 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 14 0 cell_27_14_0
  | exact S 27 14 1 cell_27_14_1
  | exact S 27 14 2 cell_27_14_2
  | exact S 27 14 3 cell_27_14_3
  | exact S 27 14 4 cell_27_14_4
  | exact S 27 14 5 cell_27_14_5
theorem cell_27_15_0 : C 27 15 0 := by decide +kernel
theorem cell_27_15_1 : C 27 15 1 := by decide +kernel
theorem cell_27_15_2 : C 27 15 2 := by decide +kernel
theorem cell_27_15_3 : C 27 15 3 := by decide +kernel
theorem cell_27_15_4 : C 27 15 4 := by decide +kernel
theorem cell_27_15_5 : C 27 15 5 := by decide +kernel
theorem row_27_15 : ThresholdAt 27 15 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 15 0 cell_27_15_0
  | exact S 27 15 1 cell_27_15_1
  | exact S 27 15 2 cell_27_15_2
  | exact S 27 15 3 cell_27_15_3
  | exact S 27 15 4 cell_27_15_4
  | exact S 27 15 5 cell_27_15_5
theorem cell_27_16_0 : C 27 16 0 := by decide +kernel
theorem cell_27_16_1 : C 27 16 1 := by decide +kernel
theorem cell_27_16_2 : C 27 16 2 := by decide +kernel
theorem cell_27_16_3 : C 27 16 3 := by decide +kernel
theorem cell_27_16_4 : C 27 16 4 := by decide +kernel
theorem cell_27_16_5 : C 27 16 5 := by decide +kernel
theorem row_27_16 : ThresholdAt 27 16 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 16 0 cell_27_16_0
  | exact S 27 16 1 cell_27_16_1
  | exact S 27 16 2 cell_27_16_2
  | exact S 27 16 3 cell_27_16_3
  | exact S 27 16 4 cell_27_16_4
  | exact S 27 16 5 cell_27_16_5
theorem cell_27_17_0 : C 27 17 0 := by decide +kernel
theorem cell_27_17_1 : C 27 17 1 := by decide +kernel
theorem cell_27_17_2 : C 27 17 2 := by decide +kernel
theorem cell_27_17_3 : C 27 17 3 := by decide +kernel
theorem cell_27_17_4 : C 27 17 4 := by decide +kernel
theorem cell_27_17_5 : C 27 17 5 := by decide +kernel
theorem row_27_17 : ThresholdAt 27 17 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 17 0 cell_27_17_0
  | exact S 27 17 1 cell_27_17_1
  | exact S 27 17 2 cell_27_17_2
  | exact S 27 17 3 cell_27_17_3
  | exact S 27 17 4 cell_27_17_4
  | exact S 27 17 5 cell_27_17_5
theorem cell_27_18_0 : C 27 18 0 := by decide +kernel
theorem cell_27_18_1 : C 27 18 1 := by decide +kernel
theorem cell_27_18_2 : C 27 18 2 := by decide +kernel
theorem cell_27_18_3 : C 27 18 3 := by decide +kernel
theorem cell_27_18_4 : C 27 18 4 := by decide +kernel
theorem cell_27_18_5 : C 27 18 5 := by decide +kernel
theorem row_27_18 : ThresholdAt 27 18 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 18 0 cell_27_18_0
  | exact S 27 18 1 cell_27_18_1
  | exact S 27 18 2 cell_27_18_2
  | exact S 27 18 3 cell_27_18_3
  | exact S 27 18 4 cell_27_18_4
  | exact S 27 18 5 cell_27_18_5
theorem cell_27_19_0 : C 27 19 0 := by decide +kernel
theorem cell_27_19_1 : C 27 19 1 := by decide +kernel
theorem cell_27_19_2 : C 27 19 2 := by decide +kernel
theorem cell_27_19_3 : C 27 19 3 := by decide +kernel
theorem cell_27_19_4 : C 27 19 4 := by decide +kernel
theorem cell_27_19_5 : C 27 19 5 := by decide +kernel
theorem row_27_19 : ThresholdAt 27 19 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 19 0 cell_27_19_0
  | exact S 27 19 1 cell_27_19_1
  | exact S 27 19 2 cell_27_19_2
  | exact S 27 19 3 cell_27_19_3
  | exact S 27 19 4 cell_27_19_4
  | exact S 27 19 5 cell_27_19_5
theorem cell_27_20_0 : C 27 20 0 := by decide +kernel
theorem cell_27_20_1 : C 27 20 1 := by decide +kernel
theorem cell_27_20_2 : C 27 20 2 := by decide +kernel
theorem cell_27_20_3 : C 27 20 3 := by decide +kernel
theorem cell_27_20_4 : C 27 20 4 := by decide +kernel
theorem cell_27_20_5 : C 27 20 5 := by decide +kernel
theorem row_27_20 : ThresholdAt 27 20 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 20 0 cell_27_20_0
  | exact S 27 20 1 cell_27_20_1
  | exact S 27 20 2 cell_27_20_2
  | exact S 27 20 3 cell_27_20_3
  | exact S 27 20 4 cell_27_20_4
  | exact S 27 20 5 cell_27_20_5
theorem cell_27_21_0 : C 27 21 0 := by decide +kernel
theorem cell_27_21_1 : C 27 21 1 := by decide +kernel
theorem cell_27_21_2 : C 27 21 2 := by decide +kernel
theorem cell_27_21_3 : C 27 21 3 := by decide +kernel
theorem cell_27_21_4 : C 27 21 4 := by decide +kernel
theorem cell_27_21_5 : C 27 21 5 := by decide +kernel
theorem row_27_21 : ThresholdAt 27 21 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 21 0 cell_27_21_0
  | exact S 27 21 1 cell_27_21_1
  | exact S 27 21 2 cell_27_21_2
  | exact S 27 21 3 cell_27_21_3
  | exact S 27 21 4 cell_27_21_4
  | exact S 27 21 5 cell_27_21_5
theorem cell_27_22_0 : C 27 22 0 := by decide +kernel
theorem cell_27_22_1 : C 27 22 1 := by decide +kernel
theorem cell_27_22_2 : C 27 22 2 := by decide +kernel
theorem cell_27_22_3 : C 27 22 3 := by decide +kernel
theorem cell_27_22_4 : C 27 22 4 := by decide +kernel
theorem cell_27_22_5 : C 27 22 5 := by decide +kernel
theorem row_27_22 : ThresholdAt 27 22 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 22 0 cell_27_22_0
  | exact S 27 22 1 cell_27_22_1
  | exact S 27 22 2 cell_27_22_2
  | exact S 27 22 3 cell_27_22_3
  | exact S 27 22 4 cell_27_22_4
  | exact S 27 22 5 cell_27_22_5
theorem cell_27_23_0 : C 27 23 0 := by decide +kernel
theorem cell_27_23_1 : C 27 23 1 := by decide +kernel
theorem cell_27_23_2 : C 27 23 2 := by decide +kernel
theorem cell_27_23_3 : C 27 23 3 := by decide +kernel
theorem cell_27_23_4 : C 27 23 4 := by decide +kernel
theorem cell_27_23_5 : C 27 23 5 := by decide +kernel
theorem row_27_23 : ThresholdAt 27 23 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 23 0 cell_27_23_0
  | exact S 27 23 1 cell_27_23_1
  | exact S 27 23 2 cell_27_23_2
  | exact S 27 23 3 cell_27_23_3
  | exact S 27 23 4 cell_27_23_4
  | exact S 27 23 5 cell_27_23_5
theorem cell_27_24_0 : C 27 24 0 := by decide +kernel
theorem cell_27_24_1 : C 27 24 1 := by decide +kernel
theorem cell_27_24_2 : C 27 24 2 := by decide +kernel
theorem cell_27_24_3 : C 27 24 3 := by decide +kernel
theorem cell_27_24_4 : C 27 24 4 := by decide +kernel
theorem cell_27_24_5 : C 27 24 5 := by decide +kernel
theorem row_27_24 : ThresholdAt 27 24 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 24 0 cell_27_24_0
  | exact S 27 24 1 cell_27_24_1
  | exact S 27 24 2 cell_27_24_2
  | exact S 27 24 3 cell_27_24_3
  | exact S 27 24 4 cell_27_24_4
  | exact S 27 24 5 cell_27_24_5
theorem cell_27_25_0 : C 27 25 0 := by decide +kernel
theorem cell_27_25_1 : C 27 25 1 := by decide +kernel
theorem cell_27_25_2 : C 27 25 2 := by decide +kernel
theorem cell_27_25_3 : C 27 25 3 := by decide +kernel
theorem cell_27_25_4 : C 27 25 4 := by decide +kernel
theorem cell_27_25_5 : C 27 25 5 := by decide +kernel
theorem row_27_25 : ThresholdAt 27 25 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 25 0 cell_27_25_0
  | exact S 27 25 1 cell_27_25_1
  | exact S 27 25 2 cell_27_25_2
  | exact S 27 25 3 cell_27_25_3
  | exact S 27 25 4 cell_27_25_4
  | exact S 27 25 5 cell_27_25_5
theorem cell_27_26_0 : C 27 26 0 := by decide +kernel
theorem cell_27_26_1 : C 27 26 1 := by decide +kernel
theorem cell_27_26_2 : C 27 26 2 := by decide +kernel
theorem cell_27_26_3 : C 27 26 3 := by decide +kernel
theorem cell_27_26_4 : C 27 26 4 := by decide +kernel
theorem cell_27_26_5 : C 27 26 5 := by decide +kernel
theorem row_27_26 : ThresholdAt 27 26 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 26 0 cell_27_26_0
  | exact S 27 26 1 cell_27_26_1
  | exact S 27 26 2 cell_27_26_2
  | exact S 27 26 3 cell_27_26_3
  | exact S 27 26 4 cell_27_26_4
  | exact S 27 26 5 cell_27_26_5
theorem cell_27_27_0 : C 27 27 0 := by decide +kernel
theorem cell_27_27_1 : C 27 27 1 := by decide +kernel
theorem cell_27_27_2 : C 27 27 2 := by decide +kernel
theorem cell_27_27_3 : C 27 27 3 := by decide +kernel
theorem cell_27_27_4 : C 27 27 4 := by decide +kernel
theorem cell_27_27_5 : C 27 27 5 := by decide +kernel
theorem row_27_27 : ThresholdAt 27 27 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 27 0 cell_27_27_0
  | exact S 27 27 1 cell_27_27_1
  | exact S 27 27 2 cell_27_27_2
  | exact S 27 27 3 cell_27_27_3
  | exact S 27 27 4 cell_27_27_4
  | exact S 27 27 5 cell_27_27_5
theorem cell_27_28_0 : C 27 28 0 := by decide +kernel
theorem cell_27_28_1 : C 27 28 1 := by decide +kernel
theorem cell_27_28_2 : C 27 28 2 := by decide +kernel
theorem cell_27_28_3 : C 27 28 3 := by decide +kernel
theorem cell_27_28_4 : C 27 28 4 := by decide +kernel
theorem cell_27_28_5 : C 27 28 5 := by decide +kernel
theorem row_27_28 : ThresholdAt 27 28 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 28 0 cell_27_28_0
  | exact S 27 28 1 cell_27_28_1
  | exact S 27 28 2 cell_27_28_2
  | exact S 27 28 3 cell_27_28_3
  | exact S 27 28 4 cell_27_28_4
  | exact S 27 28 5 cell_27_28_5
theorem cell_27_29_0 : C 27 29 0 := by decide +kernel
theorem cell_27_29_1 : C 27 29 1 := by decide +kernel
theorem cell_27_29_2 : C 27 29 2 := by decide +kernel
theorem cell_27_29_3 : C 27 29 3 := by decide +kernel
theorem cell_27_29_4 : C 27 29 4 := by decide +kernel
theorem cell_27_29_5 : C 27 29 5 := by decide +kernel
theorem row_27_29 : ThresholdAt 27 29 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 29 0 cell_27_29_0
  | exact S 27 29 1 cell_27_29_1
  | exact S 27 29 2 cell_27_29_2
  | exact S 27 29 3 cell_27_29_3
  | exact S 27 29 4 cell_27_29_4
  | exact S 27 29 5 cell_27_29_5
theorem cell_27_30_0 : C 27 30 0 := by decide +kernel
theorem cell_27_30_1 : C 27 30 1 := by decide +kernel
theorem cell_27_30_2 : C 27 30 2 := by decide +kernel
theorem cell_27_30_3 : C 27 30 3 := by decide +kernel
theorem cell_27_30_4 : C 27 30 4 := by decide +kernel
theorem cell_27_30_5 : C 27 30 5 := by decide +kernel
theorem row_27_30 : ThresholdAt 27 30 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 30 0 cell_27_30_0
  | exact S 27 30 1 cell_27_30_1
  | exact S 27 30 2 cell_27_30_2
  | exact S 27 30 3 cell_27_30_3
  | exact S 27 30 4 cell_27_30_4
  | exact S 27 30 5 cell_27_30_5
theorem cell_27_31_0 : C 27 31 0 := by decide +kernel
theorem cell_27_31_1 : C 27 31 1 := by decide +kernel
theorem cell_27_31_2 : C 27 31 2 := by decide +kernel
theorem cell_27_31_3 : C 27 31 3 := by decide +kernel
theorem cell_27_31_4 : C 27 31 4 := by decide +kernel
theorem cell_27_31_5 : C 27 31 5 := by decide +kernel
theorem row_27_31 : ThresholdAt 27 31 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 31 0 cell_27_31_0
  | exact S 27 31 1 cell_27_31_1
  | exact S 27 31 2 cell_27_31_2
  | exact S 27 31 3 cell_27_31_3
  | exact S 27 31 4 cell_27_31_4
  | exact S 27 31 5 cell_27_31_5
theorem cell_27_32_0 : C 27 32 0 := by decide +kernel
theorem cell_27_32_1 : C 27 32 1 := by decide +kernel
theorem cell_27_32_2 : C 27 32 2 := by decide +kernel
theorem cell_27_32_3 : C 27 32 3 := by decide +kernel
theorem cell_27_32_4 : C 27 32 4 := by decide +kernel
theorem cell_27_32_5 : C 27 32 5 := by decide +kernel
theorem row_27_32 : ThresholdAt 27 32 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 32 0 cell_27_32_0
  | exact S 27 32 1 cell_27_32_1
  | exact S 27 32 2 cell_27_32_2
  | exact S 27 32 3 cell_27_32_3
  | exact S 27 32 4 cell_27_32_4
  | exact S 27 32 5 cell_27_32_5
theorem cell_27_33_0 : C 27 33 0 := by decide +kernel
theorem cell_27_33_1 : C 27 33 1 := by decide +kernel
theorem cell_27_33_2 : C 27 33 2 := by decide +kernel
theorem cell_27_33_3 : C 27 33 3 := by decide +kernel
theorem cell_27_33_4 : C 27 33 4 := by decide +kernel
theorem cell_27_33_5 : C 27 33 5 := by decide +kernel
theorem row_27_33 : ThresholdAt 27 33 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 33 0 cell_27_33_0
  | exact S 27 33 1 cell_27_33_1
  | exact S 27 33 2 cell_27_33_2
  | exact S 27 33 3 cell_27_33_3
  | exact S 27 33 4 cell_27_33_4
  | exact S 27 33 5 cell_27_33_5
theorem cell_27_34_0 : C 27 34 0 := by decide +kernel
theorem cell_27_34_1 : C 27 34 1 := by decide +kernel
theorem cell_27_34_2 : C 27 34 2 := by decide +kernel
theorem cell_27_34_3 : C 27 34 3 := by decide +kernel
theorem cell_27_34_4 : C 27 34 4 := by decide +kernel
theorem cell_27_34_5 : C 27 34 5 := by decide +kernel
theorem row_27_34 : ThresholdAt 27 34 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 34 0 cell_27_34_0
  | exact S 27 34 1 cell_27_34_1
  | exact S 27 34 2 cell_27_34_2
  | exact S 27 34 3 cell_27_34_3
  | exact S 27 34 4 cell_27_34_4
  | exact S 27 34 5 cell_27_34_5
theorem cell_27_35_0 : C 27 35 0 := by decide +kernel
theorem cell_27_35_1 : C 27 35 1 := by decide +kernel
theorem cell_27_35_2 : C 27 35 2 := by decide +kernel
theorem cell_27_35_3 : C 27 35 3 := by decide +kernel
theorem cell_27_35_4 : C 27 35 4 := by decide +kernel
theorem cell_27_35_5 : C 27 35 5 := by decide +kernel
theorem row_27_35 : ThresholdAt 27 35 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 35 0 cell_27_35_0
  | exact S 27 35 1 cell_27_35_1
  | exact S 27 35 2 cell_27_35_2
  | exact S 27 35 3 cell_27_35_3
  | exact S 27 35 4 cell_27_35_4
  | exact S 27 35 5 cell_27_35_5
theorem cell_27_36_0 : C 27 36 0 := by decide +kernel
theorem cell_27_36_1 : C 27 36 1 := by decide +kernel
theorem cell_27_36_2 : C 27 36 2 := by decide +kernel
theorem cell_27_36_3 : C 27 36 3 := by decide +kernel
theorem cell_27_36_4 : C 27 36 4 := by decide +kernel
theorem cell_27_36_5 : C 27 36 5 := by decide +kernel
theorem row_27_36 : ThresholdAt 27 36 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 36 0 cell_27_36_0
  | exact S 27 36 1 cell_27_36_1
  | exact S 27 36 2 cell_27_36_2
  | exact S 27 36 3 cell_27_36_3
  | exact S 27 36 4 cell_27_36_4
  | exact S 27 36 5 cell_27_36_5
theorem cell_27_37_0 : C 27 37 0 := by decide +kernel
theorem cell_27_37_1 : C 27 37 1 := by decide +kernel
theorem cell_27_37_2 : C 27 37 2 := by decide +kernel
theorem cell_27_37_3 : C 27 37 3 := by decide +kernel
theorem cell_27_37_4 : C 27 37 4 := by decide +kernel
theorem cell_27_37_5 : C 27 37 5 := by decide +kernel
theorem row_27_37 : ThresholdAt 27 37 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 37 0 cell_27_37_0
  | exact S 27 37 1 cell_27_37_1
  | exact S 27 37 2 cell_27_37_2
  | exact S 27 37 3 cell_27_37_3
  | exact S 27 37 4 cell_27_37_4
  | exact S 27 37 5 cell_27_37_5
theorem cell_27_38_0 : C 27 38 0 := by decide +kernel
theorem cell_27_38_1 : C 27 38 1 := by decide +kernel
theorem cell_27_38_2 : C 27 38 2 := by decide +kernel
theorem cell_27_38_3 : C 27 38 3 := by decide +kernel
theorem cell_27_38_4 : C 27 38 4 := by decide +kernel
theorem cell_27_38_5 : C 27 38 5 := by decide +kernel
theorem row_27_38 : ThresholdAt 27 38 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 38 0 cell_27_38_0
  | exact S 27 38 1 cell_27_38_1
  | exact S 27 38 2 cell_27_38_2
  | exact S 27 38 3 cell_27_38_3
  | exact S 27 38 4 cell_27_38_4
  | exact S 27 38 5 cell_27_38_5
theorem cell_27_39_0 : C 27 39 0 := by decide +kernel
theorem cell_27_39_1 : C 27 39 1 := by decide +kernel
theorem cell_27_39_2 : C 27 39 2 := by decide +kernel
theorem cell_27_39_3 : C 27 39 3 := by decide +kernel
theorem cell_27_39_4 : C 27 39 4 := by decide +kernel
theorem cell_27_39_5 : C 27 39 5 := by decide +kernel
theorem row_27_39 : ThresholdAt 27 39 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 39 0 cell_27_39_0
  | exact S 27 39 1 cell_27_39_1
  | exact S 27 39 2 cell_27_39_2
  | exact S 27 39 3 cell_27_39_3
  | exact S 27 39 4 cell_27_39_4
  | exact S 27 39 5 cell_27_39_5
theorem cell_27_40_0 : C 27 40 0 := by decide +kernel
theorem cell_27_40_1 : C 27 40 1 := by decide +kernel
theorem cell_27_40_2 : C 27 40 2 := by decide +kernel
theorem cell_27_40_3 : C 27 40 3 := by decide +kernel
theorem cell_27_40_4 : C 27 40 4 := by decide +kernel
theorem cell_27_40_5 : C 27 40 5 := by decide +kernel
theorem row_27_40 : ThresholdAt 27 40 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 40 0 cell_27_40_0
  | exact S 27 40 1 cell_27_40_1
  | exact S 27 40 2 cell_27_40_2
  | exact S 27 40 3 cell_27_40_3
  | exact S 27 40 4 cell_27_40_4
  | exact S 27 40 5 cell_27_40_5
theorem cell_27_41_0 : C 27 41 0 := by decide +kernel
theorem cell_27_41_1 : C 27 41 1 := by decide +kernel
theorem cell_27_41_2 : C 27 41 2 := by decide +kernel
theorem cell_27_41_3 : C 27 41 3 := by decide +kernel
theorem cell_27_41_4 : C 27 41 4 := by decide +kernel
theorem cell_27_41_5 : C 27 41 5 := by decide +kernel
theorem row_27_41 : ThresholdAt 27 41 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 41 0 cell_27_41_0
  | exact S 27 41 1 cell_27_41_1
  | exact S 27 41 2 cell_27_41_2
  | exact S 27 41 3 cell_27_41_3
  | exact S 27 41 4 cell_27_41_4
  | exact S 27 41 5 cell_27_41_5
theorem cell_27_42_0 : C 27 42 0 := by decide +kernel
theorem cell_27_42_1 : C 27 42 1 := by decide +kernel
theorem cell_27_42_2 : C 27 42 2 := by decide +kernel
theorem cell_27_42_3 : C 27 42 3 := by decide +kernel
theorem cell_27_42_4 : C 27 42 4 := by decide +kernel
theorem cell_27_42_5 : C 27 42 5 := by decide +kernel
theorem row_27_42 : ThresholdAt 27 42 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 42 0 cell_27_42_0
  | exact S 27 42 1 cell_27_42_1
  | exact S 27 42 2 cell_27_42_2
  | exact S 27 42 3 cell_27_42_3
  | exact S 27 42 4 cell_27_42_4
  | exact S 27 42 5 cell_27_42_5
theorem cell_27_43_0 : C 27 43 0 := by decide +kernel
theorem cell_27_43_1 : C 27 43 1 := by decide +kernel
theorem cell_27_43_2 : C 27 43 2 := by decide +kernel
theorem cell_27_43_3 : C 27 43 3 := by decide +kernel
theorem cell_27_43_4 : C 27 43 4 := by decide +kernel
theorem cell_27_43_5 : C 27 43 5 := by decide +kernel
theorem row_27_43 : ThresholdAt 27 43 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 43 0 cell_27_43_0
  | exact S 27 43 1 cell_27_43_1
  | exact S 27 43 2 cell_27_43_2
  | exact S 27 43 3 cell_27_43_3
  | exact S 27 43 4 cell_27_43_4
  | exact S 27 43 5 cell_27_43_5
theorem cell_27_44_0 : C 27 44 0 := by decide +kernel
theorem cell_27_44_1 : C 27 44 1 := by decide +kernel
theorem cell_27_44_2 : C 27 44 2 := by decide +kernel
theorem cell_27_44_3 : C 27 44 3 := by decide +kernel
theorem cell_27_44_4 : C 27 44 4 := by decide +kernel
theorem cell_27_44_5 : C 27 44 5 := by decide +kernel
theorem row_27_44 : ThresholdAt 27 44 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 44 0 cell_27_44_0
  | exact S 27 44 1 cell_27_44_1
  | exact S 27 44 2 cell_27_44_2
  | exact S 27 44 3 cell_27_44_3
  | exact S 27 44 4 cell_27_44_4
  | exact S 27 44 5 cell_27_44_5
theorem cell_27_45_0 : C 27 45 0 := by decide +kernel
theorem cell_27_45_1 : C 27 45 1 := by decide +kernel
theorem cell_27_45_2 : C 27 45 2 := by decide +kernel
theorem cell_27_45_3 : C 27 45 3 := by decide +kernel
theorem cell_27_45_4 : C 27 45 4 := by decide +kernel
theorem cell_27_45_5 : C 27 45 5 := by decide +kernel
theorem row_27_45 : ThresholdAt 27 45 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 45 0 cell_27_45_0
  | exact S 27 45 1 cell_27_45_1
  | exact S 27 45 2 cell_27_45_2
  | exact S 27 45 3 cell_27_45_3
  | exact S 27 45 4 cell_27_45_4
  | exact S 27 45 5 cell_27_45_5
theorem cell_27_46_0 : C 27 46 0 := by decide +kernel
theorem cell_27_46_1 : C 27 46 1 := by decide +kernel
theorem cell_27_46_2 : C 27 46 2 := by decide +kernel
theorem cell_27_46_3 : C 27 46 3 := by decide +kernel
theorem cell_27_46_4 : C 27 46 4 := by decide +kernel
theorem cell_27_46_5 : C 27 46 5 := by decide +kernel
theorem row_27_46 : ThresholdAt 27 46 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 46 0 cell_27_46_0
  | exact S 27 46 1 cell_27_46_1
  | exact S 27 46 2 cell_27_46_2
  | exact S 27 46 3 cell_27_46_3
  | exact S 27 46 4 cell_27_46_4
  | exact S 27 46 5 cell_27_46_5
theorem cell_27_47_0 : C 27 47 0 := by decide +kernel
theorem cell_27_47_1 : C 27 47 1 := by decide +kernel
theorem cell_27_47_2 : C 27 47 2 := by decide +kernel
theorem cell_27_47_3 : C 27 47 3 := by decide +kernel
theorem cell_27_47_4 : C 27 47 4 := by decide +kernel
theorem cell_27_47_5 : C 27 47 5 := by decide +kernel
theorem row_27_47 : ThresholdAt 27 47 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 47 0 cell_27_47_0
  | exact S 27 47 1 cell_27_47_1
  | exact S 27 47 2 cell_27_47_2
  | exact S 27 47 3 cell_27_47_3
  | exact S 27 47 4 cell_27_47_4
  | exact S 27 47 5 cell_27_47_5
theorem cell_27_48_0 : C 27 48 0 := by decide +kernel
theorem cell_27_48_1 : C 27 48 1 := by decide +kernel
theorem cell_27_48_2 : C 27 48 2 := by decide +kernel
theorem cell_27_48_3 : C 27 48 3 := by decide +kernel
theorem cell_27_48_4 : C 27 48 4 := by decide +kernel
theorem cell_27_48_5 : C 27 48 5 := by decide +kernel
theorem row_27_48 : ThresholdAt 27 48 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 48 0 cell_27_48_0
  | exact S 27 48 1 cell_27_48_1
  | exact S 27 48 2 cell_27_48_2
  | exact S 27 48 3 cell_27_48_3
  | exact S 27 48 4 cell_27_48_4
  | exact S 27 48 5 cell_27_48_5
theorem cell_27_49_0 : C 27 49 0 := by decide +kernel
theorem cell_27_49_1 : C 27 49 1 := by decide +kernel
theorem cell_27_49_2 : C 27 49 2 := by decide +kernel
theorem cell_27_49_3 : C 27 49 3 := by decide +kernel
theorem cell_27_49_4 : C 27 49 4 := by decide +kernel
theorem cell_27_49_5 : C 27 49 5 := by decide +kernel
theorem row_27_49 : ThresholdAt 27 49 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 49 0 cell_27_49_0
  | exact S 27 49 1 cell_27_49_1
  | exact S 27 49 2 cell_27_49_2
  | exact S 27 49 3 cell_27_49_3
  | exact S 27 49 4 cell_27_49_4
  | exact S 27 49 5 cell_27_49_5
theorem cell_27_50_0 : C 27 50 0 := by decide +kernel
theorem cell_27_50_1 : C 27 50 1 := by decide +kernel
theorem cell_27_50_2 : C 27 50 2 := by decide +kernel
theorem cell_27_50_3 : C 27 50 3 := by decide +kernel
theorem cell_27_50_4 : C 27 50 4 := by decide +kernel
theorem cell_27_50_5 : C 27 50 5 := by decide +kernel
theorem row_27_50 : ThresholdAt 27 50 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 50 0 cell_27_50_0
  | exact S 27 50 1 cell_27_50_1
  | exact S 27 50 2 cell_27_50_2
  | exact S 27 50 3 cell_27_50_3
  | exact S 27 50 4 cell_27_50_4
  | exact S 27 50 5 cell_27_50_5
theorem cell_27_51_0 : C 27 51 0 := by decide +kernel
theorem cell_27_51_1 : C 27 51 1 := by decide +kernel
theorem cell_27_51_2 : C 27 51 2 := by decide +kernel
theorem cell_27_51_3 : C 27 51 3 := by decide +kernel
theorem cell_27_51_4 : C 27 51 4 := by decide +kernel
theorem cell_27_51_5 : C 27 51 5 := by decide +kernel
theorem row_27_51 : ThresholdAt 27 51 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 51 0 cell_27_51_0
  | exact S 27 51 1 cell_27_51_1
  | exact S 27 51 2 cell_27_51_2
  | exact S 27 51 3 cell_27_51_3
  | exact S 27 51 4 cell_27_51_4
  | exact S 27 51 5 cell_27_51_5
theorem cell_27_52_0 : C 27 52 0 := by decide +kernel
theorem cell_27_52_1 : C 27 52 1 := by decide +kernel
theorem cell_27_52_2 : C 27 52 2 := by decide +kernel
theorem cell_27_52_3 : C 27 52 3 := by decide +kernel
theorem cell_27_52_4 : C 27 52 4 := by decide +kernel
theorem cell_27_52_5 : C 27 52 5 := by decide +kernel
theorem row_27_52 : ThresholdAt 27 52 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 52 0 cell_27_52_0
  | exact S 27 52 1 cell_27_52_1
  | exact S 27 52 2 cell_27_52_2
  | exact S 27 52 3 cell_27_52_3
  | exact S 27 52 4 cell_27_52_4
  | exact S 27 52 5 cell_27_52_5
theorem cell_27_53_0 : C 27 53 0 := by decide +kernel
theorem cell_27_53_1 : C 27 53 1 := by decide +kernel
theorem cell_27_53_2 : C 27 53 2 := by decide +kernel
theorem cell_27_53_3 : C 27 53 3 := by decide +kernel
theorem cell_27_53_4 : C 27 53 4 := by decide +kernel
theorem cell_27_53_5 : C 27 53 5 := by decide +kernel
theorem row_27_53 : ThresholdAt 27 53 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 53 0 cell_27_53_0
  | exact S 27 53 1 cell_27_53_1
  | exact S 27 53 2 cell_27_53_2
  | exact S 27 53 3 cell_27_53_3
  | exact S 27 53 4 cell_27_53_4
  | exact S 27 53 5 cell_27_53_5
theorem cell_27_54_0 : C 27 54 0 := by decide +kernel
theorem cell_27_54_1 : C 27 54 1 := by decide +kernel
theorem cell_27_54_2 : C 27 54 2 := by decide +kernel
theorem cell_27_54_3 : C 27 54 3 := by decide +kernel
theorem cell_27_54_4 : C 27 54 4 := by decide +kernel
theorem cell_27_54_5 : C 27 54 5 := by decide +kernel
theorem row_27_54 : ThresholdAt 27 54 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 54 0 cell_27_54_0
  | exact S 27 54 1 cell_27_54_1
  | exact S 27 54 2 cell_27_54_2
  | exact S 27 54 3 cell_27_54_3
  | exact S 27 54 4 cell_27_54_4
  | exact S 27 54 5 cell_27_54_5
theorem cell_27_55_0 : C 27 55 0 := by decide +kernel
theorem cell_27_55_1 : C 27 55 1 := by decide +kernel
theorem cell_27_55_2 : C 27 55 2 := by decide +kernel
theorem cell_27_55_3 : C 27 55 3 := by decide +kernel
theorem cell_27_55_4 : C 27 55 4 := by decide +kernel
theorem cell_27_55_5 : C 27 55 5 := by decide +kernel
theorem row_27_55 : ThresholdAt 27 55 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 55 0 cell_27_55_0
  | exact S 27 55 1 cell_27_55_1
  | exact S 27 55 2 cell_27_55_2
  | exact S 27 55 3 cell_27_55_3
  | exact S 27 55 4 cell_27_55_4
  | exact S 27 55 5 cell_27_55_5
theorem cell_27_56_0 : C 27 56 0 := by decide +kernel
theorem cell_27_56_1 : C 27 56 1 := by decide +kernel
theorem cell_27_56_2 : C 27 56 2 := by decide +kernel
theorem cell_27_56_3 : C 27 56 3 := by decide +kernel
theorem cell_27_56_4 : C 27 56 4 := by decide +kernel
theorem cell_27_56_5 : C 27 56 5 := by decide +kernel
theorem row_27_56 : ThresholdAt 27 56 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 56 0 cell_27_56_0
  | exact S 27 56 1 cell_27_56_1
  | exact S 27 56 2 cell_27_56_2
  | exact S 27 56 3 cell_27_56_3
  | exact S 27 56 4 cell_27_56_4
  | exact S 27 56 5 cell_27_56_5
theorem cell_27_57_0 : C 27 57 0 := by decide +kernel
theorem cell_27_57_1 : C 27 57 1 := by decide +kernel
theorem cell_27_57_2 : C 27 57 2 := by decide +kernel
theorem cell_27_57_3 : C 27 57 3 := by decide +kernel
theorem cell_27_57_4 : C 27 57 4 := by decide +kernel
theorem cell_27_57_5 : C 27 57 5 := by decide +kernel
theorem row_27_57 : ThresholdAt 27 57 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 57 0 cell_27_57_0
  | exact S 27 57 1 cell_27_57_1
  | exact S 27 57 2 cell_27_57_2
  | exact S 27 57 3 cell_27_57_3
  | exact S 27 57 4 cell_27_57_4
  | exact S 27 57 5 cell_27_57_5
theorem cell_27_58_0 : C 27 58 0 := by decide +kernel
theorem cell_27_58_1 : C 27 58 1 := by decide +kernel
theorem cell_27_58_2 : C 27 58 2 := by decide +kernel
theorem cell_27_58_3 : C 27 58 3 := by decide +kernel
theorem cell_27_58_4 : C 27 58 4 := by decide +kernel
theorem cell_27_58_5 : C 27 58 5 := by decide +kernel
theorem row_27_58 : ThresholdAt 27 58 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 58 0 cell_27_58_0
  | exact S 27 58 1 cell_27_58_1
  | exact S 27 58 2 cell_27_58_2
  | exact S 27 58 3 cell_27_58_3
  | exact S 27 58 4 cell_27_58_4
  | exact S 27 58 5 cell_27_58_5
theorem cell_27_59_0 : C 27 59 0 := by decide +kernel
theorem cell_27_59_1 : C 27 59 1 := by decide +kernel
theorem cell_27_59_2 : C 27 59 2 := by decide +kernel
theorem cell_27_59_3 : C 27 59 3 := by decide +kernel
theorem cell_27_59_4 : C 27 59 4 := by decide +kernel
theorem cell_27_59_5 : C 27 59 5 := by decide +kernel
theorem row_27_59 : ThresholdAt 27 59 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 59 0 cell_27_59_0
  | exact S 27 59 1 cell_27_59_1
  | exact S 27 59 2 cell_27_59_2
  | exact S 27 59 3 cell_27_59_3
  | exact S 27 59 4 cell_27_59_4
  | exact S 27 59 5 cell_27_59_5
theorem cell_27_60_0 : C 27 60 0 := by decide +kernel
theorem cell_27_60_1 : C 27 60 1 := by decide +kernel
theorem cell_27_60_2 : C 27 60 2 := by decide +kernel
theorem cell_27_60_3 : C 27 60 3 := by decide +kernel
theorem cell_27_60_4 : C 27 60 4 := by decide +kernel
theorem cell_27_60_5 : C 27 60 5 := by decide +kernel
theorem row_27_60 : ThresholdAt 27 60 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 60 0 cell_27_60_0
  | exact S 27 60 1 cell_27_60_1
  | exact S 27 60 2 cell_27_60_2
  | exact S 27 60 3 cell_27_60_3
  | exact S 27 60 4 cell_27_60_4
  | exact S 27 60 5 cell_27_60_5
theorem cell_27_61_0 : C 27 61 0 := by decide +kernel
theorem cell_27_61_1 : C 27 61 1 := by decide +kernel
theorem cell_27_61_2 : C 27 61 2 := by decide +kernel
theorem cell_27_61_3 : C 27 61 3 := by decide +kernel
theorem cell_27_61_4 : C 27 61 4 := by decide +kernel
theorem cell_27_61_5 : C 27 61 5 := by decide +kernel
theorem row_27_61 : ThresholdAt 27 61 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 61 0 cell_27_61_0
  | exact S 27 61 1 cell_27_61_1
  | exact S 27 61 2 cell_27_61_2
  | exact S 27 61 3 cell_27_61_3
  | exact S 27 61 4 cell_27_61_4
  | exact S 27 61 5 cell_27_61_5
theorem cell_27_62_0 : C 27 62 0 := by decide +kernel
theorem cell_27_62_1 : C 27 62 1 := by decide +kernel
theorem cell_27_62_2 : C 27 62 2 := by decide +kernel
theorem cell_27_62_3 : C 27 62 3 := by decide +kernel
theorem cell_27_62_4 : C 27 62 4 := by decide +kernel
theorem cell_27_62_5 : C 27 62 5 := by decide +kernel
theorem row_27_62 : ThresholdAt 27 62 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 62 0 cell_27_62_0
  | exact S 27 62 1 cell_27_62_1
  | exact S 27 62 2 cell_27_62_2
  | exact S 27 62 3 cell_27_62_3
  | exact S 27 62 4 cell_27_62_4
  | exact S 27 62 5 cell_27_62_5
theorem cell_27_63_0 : C 27 63 0 := by decide +kernel
theorem cell_27_63_1 : C 27 63 1 := by decide +kernel
theorem cell_27_63_2 : C 27 63 2 := by decide +kernel
theorem cell_27_63_3 : C 27 63 3 := by decide +kernel
theorem cell_27_63_4 : C 27 63 4 := by decide +kernel
theorem cell_27_63_5 : C 27 63 5 := by decide +kernel
theorem row_27_63 : ThresholdAt 27 63 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 63 0 cell_27_63_0
  | exact S 27 63 1 cell_27_63_1
  | exact S 27 63 2 cell_27_63_2
  | exact S 27 63 3 cell_27_63_3
  | exact S 27 63 4 cell_27_63_4
  | exact S 27 63 5 cell_27_63_5
theorem cell_27_64_0 : C 27 64 0 := by decide +kernel
theorem cell_27_64_1 : C 27 64 1 := by decide +kernel
theorem cell_27_64_2 : C 27 64 2 := by decide +kernel
theorem cell_27_64_3 : C 27 64 3 := by decide +kernel
theorem cell_27_64_4 : C 27 64 4 := by decide +kernel
theorem cell_27_64_5 : C 27 64 5 := by decide +kernel
theorem row_27_64 : ThresholdAt 27 64 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 64 0 cell_27_64_0
  | exact S 27 64 1 cell_27_64_1
  | exact S 27 64 2 cell_27_64_2
  | exact S 27 64 3 cell_27_64_3
  | exact S 27 64 4 cell_27_64_4
  | exact S 27 64 5 cell_27_64_5
theorem cell_27_65_0 : C 27 65 0 := by decide +kernel
theorem cell_27_65_1 : C 27 65 1 := by decide +kernel
theorem cell_27_65_2 : C 27 65 2 := by decide +kernel
theorem cell_27_65_3 : C 27 65 3 := by decide +kernel
theorem cell_27_65_4 : C 27 65 4 := by decide +kernel
theorem cell_27_65_5 : C 27 65 5 := by decide +kernel
theorem row_27_65 : ThresholdAt 27 65 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 65 0 cell_27_65_0
  | exact S 27 65 1 cell_27_65_1
  | exact S 27 65 2 cell_27_65_2
  | exact S 27 65 3 cell_27_65_3
  | exact S 27 65 4 cell_27_65_4
  | exact S 27 65 5 cell_27_65_5
theorem cell_27_66_0 : C 27 66 0 := by decide +kernel
theorem cell_27_66_1 : C 27 66 1 := by decide +kernel
theorem cell_27_66_2 : C 27 66 2 := by decide +kernel
theorem cell_27_66_3 : C 27 66 3 := by decide +kernel
theorem cell_27_66_4 : C 27 66 4 := by decide +kernel
theorem cell_27_66_5 : C 27 66 5 := by decide +kernel
theorem row_27_66 : ThresholdAt 27 66 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 66 0 cell_27_66_0
  | exact S 27 66 1 cell_27_66_1
  | exact S 27 66 2 cell_27_66_2
  | exact S 27 66 3 cell_27_66_3
  | exact S 27 66 4 cell_27_66_4
  | exact S 27 66 5 cell_27_66_5
theorem cell_27_67_0 : C 27 67 0 := by decide +kernel
theorem cell_27_67_1 : C 27 67 1 := by decide +kernel
theorem cell_27_67_2 : C 27 67 2 := by decide +kernel
theorem cell_27_67_3 : C 27 67 3 := by decide +kernel
theorem cell_27_67_4 : C 27 67 4 := by decide +kernel
theorem cell_27_67_5 : C 27 67 5 := by decide +kernel
theorem row_27_67 : ThresholdAt 27 67 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 67 0 cell_27_67_0
  | exact S 27 67 1 cell_27_67_1
  | exact S 27 67 2 cell_27_67_2
  | exact S 27 67 3 cell_27_67_3
  | exact S 27 67 4 cell_27_67_4
  | exact S 27 67 5 cell_27_67_5
theorem cell_27_68_0 : C 27 68 0 := by decide +kernel
theorem cell_27_68_1 : C 27 68 1 := by decide +kernel
theorem cell_27_68_2 : C 27 68 2 := by decide +kernel
theorem cell_27_68_3 : C 27 68 3 := by decide +kernel
theorem cell_27_68_4 : C 27 68 4 := by decide +kernel
theorem cell_27_68_5 : C 27 68 5 := by decide +kernel
theorem row_27_68 : ThresholdAt 27 68 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 68 0 cell_27_68_0
  | exact S 27 68 1 cell_27_68_1
  | exact S 27 68 2 cell_27_68_2
  | exact S 27 68 3 cell_27_68_3
  | exact S 27 68 4 cell_27_68_4
  | exact S 27 68 5 cell_27_68_5
theorem cell_27_69_0 : C 27 69 0 := by decide +kernel
theorem cell_27_69_1 : C 27 69 1 := by decide +kernel
theorem cell_27_69_2 : C 27 69 2 := by decide +kernel
theorem cell_27_69_3 : C 27 69 3 := by decide +kernel
theorem cell_27_69_4 : C 27 69 4 := by decide +kernel
theorem cell_27_69_5 : C 27 69 5 := by decide +kernel
theorem row_27_69 : ThresholdAt 27 69 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 69 0 cell_27_69_0
  | exact S 27 69 1 cell_27_69_1
  | exact S 27 69 2 cell_27_69_2
  | exact S 27 69 3 cell_27_69_3
  | exact S 27 69 4 cell_27_69_4
  | exact S 27 69 5 cell_27_69_5
theorem cell_27_70_0 : C 27 70 0 := by decide +kernel
theorem cell_27_70_1 : C 27 70 1 := by decide +kernel
theorem cell_27_70_2 : C 27 70 2 := by decide +kernel
theorem cell_27_70_3 : C 27 70 3 := by decide +kernel
theorem cell_27_70_4 : C 27 70 4 := by decide +kernel
theorem cell_27_70_5 : C 27 70 5 := by decide +kernel
theorem row_27_70 : ThresholdAt 27 70 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 70 0 cell_27_70_0
  | exact S 27 70 1 cell_27_70_1
  | exact S 27 70 2 cell_27_70_2
  | exact S 27 70 3 cell_27_70_3
  | exact S 27 70 4 cell_27_70_4
  | exact S 27 70 5 cell_27_70_5
theorem cell_27_71_0 : C 27 71 0 := by decide +kernel
theorem cell_27_71_1 : C 27 71 1 := by decide +kernel
theorem cell_27_71_2 : C 27 71 2 := by decide +kernel
theorem cell_27_71_3 : C 27 71 3 := by decide +kernel
theorem cell_27_71_4 : C 27 71 4 := by decide +kernel
theorem cell_27_71_5 : C 27 71 5 := by decide +kernel
theorem row_27_71 : ThresholdAt 27 71 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 71 0 cell_27_71_0
  | exact S 27 71 1 cell_27_71_1
  | exact S 27 71 2 cell_27_71_2
  | exact S 27 71 3 cell_27_71_3
  | exact S 27 71 4 cell_27_71_4
  | exact S 27 71 5 cell_27_71_5
theorem cell_27_72_0 : C 27 72 0 := by decide +kernel
theorem cell_27_72_1 : C 27 72 1 := by decide +kernel
theorem cell_27_72_2 : C 27 72 2 := by decide +kernel
theorem cell_27_72_3 : C 27 72 3 := by decide +kernel
theorem cell_27_72_4 : C 27 72 4 := by decide +kernel
theorem cell_27_72_5 : C 27 72 5 := by decide +kernel
theorem row_27_72 : ThresholdAt 27 72 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 72 0 cell_27_72_0
  | exact S 27 72 1 cell_27_72_1
  | exact S 27 72 2 cell_27_72_2
  | exact S 27 72 3 cell_27_72_3
  | exact S 27 72 4 cell_27_72_4
  | exact S 27 72 5 cell_27_72_5
theorem cell_27_73_0 : C 27 73 0 := by decide +kernel
theorem cell_27_73_1 : C 27 73 1 := by decide +kernel
theorem cell_27_73_2 : C 27 73 2 := by decide +kernel
theorem cell_27_73_3 : C 27 73 3 := by decide +kernel
theorem cell_27_73_4 : C 27 73 4 := by decide +kernel
theorem cell_27_73_5 : C 27 73 5 := by decide +kernel
theorem row_27_73 : ThresholdAt 27 73 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 73 0 cell_27_73_0
  | exact S 27 73 1 cell_27_73_1
  | exact S 27 73 2 cell_27_73_2
  | exact S 27 73 3 cell_27_73_3
  | exact S 27 73 4 cell_27_73_4
  | exact S 27 73 5 cell_27_73_5
theorem cell_27_74_0 : C 27 74 0 := by decide +kernel
theorem cell_27_74_1 : C 27 74 1 := by decide +kernel
theorem cell_27_74_2 : C 27 74 2 := by decide +kernel
theorem cell_27_74_3 : C 27 74 3 := by decide +kernel
theorem cell_27_74_4 : C 27 74 4 := by decide +kernel
theorem cell_27_74_5 : C 27 74 5 := by decide +kernel
theorem row_27_74 : ThresholdAt 27 74 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 74 0 cell_27_74_0
  | exact S 27 74 1 cell_27_74_1
  | exact S 27 74 2 cell_27_74_2
  | exact S 27 74 3 cell_27_74_3
  | exact S 27 74 4 cell_27_74_4
  | exact S 27 74 5 cell_27_74_5
theorem cell_27_75_0 : C 27 75 0 := by decide +kernel
theorem cell_27_75_1 : C 27 75 1 := by decide +kernel
theorem cell_27_75_2 : C 27 75 2 := by decide +kernel
theorem cell_27_75_3 : C 27 75 3 := by decide +kernel
theorem cell_27_75_4 : C 27 75 4 := by decide +kernel
theorem cell_27_75_5 : C 27 75 5 := by decide +kernel
theorem row_27_75 : ThresholdAt 27 75 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 75 0 cell_27_75_0
  | exact S 27 75 1 cell_27_75_1
  | exact S 27 75 2 cell_27_75_2
  | exact S 27 75 3 cell_27_75_3
  | exact S 27 75 4 cell_27_75_4
  | exact S 27 75 5 cell_27_75_5
theorem cell_27_76_0 : C 27 76 0 := by decide +kernel
theorem cell_27_76_1 : C 27 76 1 := by decide +kernel
theorem cell_27_76_2 : C 27 76 2 := by decide +kernel
theorem cell_27_76_3 : C 27 76 3 := by decide +kernel
theorem cell_27_76_4 : C 27 76 4 := by decide +kernel
theorem cell_27_76_5 : C 27 76 5 := by decide +kernel
theorem row_27_76 : ThresholdAt 27 76 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 76 0 cell_27_76_0
  | exact S 27 76 1 cell_27_76_1
  | exact S 27 76 2 cell_27_76_2
  | exact S 27 76 3 cell_27_76_3
  | exact S 27 76 4 cell_27_76_4
  | exact S 27 76 5 cell_27_76_5
theorem cell_27_77_0 : C 27 77 0 := by decide +kernel
theorem cell_27_77_1 : C 27 77 1 := by decide +kernel
theorem cell_27_77_2 : C 27 77 2 := by decide +kernel
theorem cell_27_77_3 : C 27 77 3 := by decide +kernel
theorem cell_27_77_4 : C 27 77 4 := by decide +kernel
theorem cell_27_77_5 : C 27 77 5 := by decide +kernel
theorem row_27_77 : ThresholdAt 27 77 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 77 0 cell_27_77_0
  | exact S 27 77 1 cell_27_77_1
  | exact S 27 77 2 cell_27_77_2
  | exact S 27 77 3 cell_27_77_3
  | exact S 27 77 4 cell_27_77_4
  | exact S 27 77 5 cell_27_77_5
theorem cell_27_78_0 : C 27 78 0 := by decide +kernel
theorem cell_27_78_1 : C 27 78 1 := by decide +kernel
theorem cell_27_78_2 : C 27 78 2 := by decide +kernel
theorem cell_27_78_3 : C 27 78 3 := by decide +kernel
theorem cell_27_78_4 : C 27 78 4 := by decide +kernel
theorem cell_27_78_5 : C 27 78 5 := by decide +kernel
theorem row_27_78 : ThresholdAt 27 78 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 78 0 cell_27_78_0
  | exact S 27 78 1 cell_27_78_1
  | exact S 27 78 2 cell_27_78_2
  | exact S 27 78 3 cell_27_78_3
  | exact S 27 78 4 cell_27_78_4
  | exact S 27 78 5 cell_27_78_5
theorem cell_27_79_0 : C 27 79 0 := by decide +kernel
theorem cell_27_79_1 : C 27 79 1 := by decide +kernel
theorem cell_27_79_2 : C 27 79 2 := by decide +kernel
theorem cell_27_79_3 : C 27 79 3 := by decide +kernel
theorem cell_27_79_4 : C 27 79 4 := by decide +kernel
theorem cell_27_79_5 : C 27 79 5 := by decide +kernel
theorem row_27_79 : ThresholdAt 27 79 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 79 0 cell_27_79_0
  | exact S 27 79 1 cell_27_79_1
  | exact S 27 79 2 cell_27_79_2
  | exact S 27 79 3 cell_27_79_3
  | exact S 27 79 4 cell_27_79_4
  | exact S 27 79 5 cell_27_79_5
theorem cell_27_80_0 : C 27 80 0 := by decide +kernel
theorem cell_27_80_1 : C 27 80 1 := by decide +kernel
theorem cell_27_80_2 : C 27 80 2 := by decide +kernel
theorem cell_27_80_3 : C 27 80 3 := by decide +kernel
theorem cell_27_80_4 : C 27 80 4 := by decide +kernel
theorem cell_27_80_5 : C 27 80 5 := by decide +kernel
theorem row_27_80 : ThresholdAt 27 80 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 80 0 cell_27_80_0
  | exact S 27 80 1 cell_27_80_1
  | exact S 27 80 2 cell_27_80_2
  | exact S 27 80 3 cell_27_80_3
  | exact S 27 80 4 cell_27_80_4
  | exact S 27 80 5 cell_27_80_5
theorem cell_27_81_0 : C 27 81 0 := by decide +kernel
theorem cell_27_81_1 : C 27 81 1 := by decide +kernel
theorem cell_27_81_2 : C 27 81 2 := by decide +kernel
theorem cell_27_81_3 : C 27 81 3 := by decide +kernel
theorem cell_27_81_4 : C 27 81 4 := by decide +kernel
theorem cell_27_81_5 : C 27 81 5 := by decide +kernel
theorem row_27_81 : ThresholdAt 27 81 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 81 0 cell_27_81_0
  | exact S 27 81 1 cell_27_81_1
  | exact S 27 81 2 cell_27_81_2
  | exact S 27 81 3 cell_27_81_3
  | exact S 27 81 4 cell_27_81_4
  | exact S 27 81 5 cell_27_81_5
theorem cell_27_82_0 : C 27 82 0 := by decide +kernel
theorem cell_27_82_1 : C 27 82 1 := by decide +kernel
theorem cell_27_82_2 : C 27 82 2 := by decide +kernel
theorem cell_27_82_3 : C 27 82 3 := by decide +kernel
theorem cell_27_82_4 : C 27 82 4 := by decide +kernel
theorem cell_27_82_5 : C 27 82 5 := by decide +kernel
theorem row_27_82 : ThresholdAt 27 82 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 82 0 cell_27_82_0
  | exact S 27 82 1 cell_27_82_1
  | exact S 27 82 2 cell_27_82_2
  | exact S 27 82 3 cell_27_82_3
  | exact S 27 82 4 cell_27_82_4
  | exact S 27 82 5 cell_27_82_5
theorem cell_27_83_0 : C 27 83 0 := by decide +kernel
theorem cell_27_83_1 : C 27 83 1 := by decide +kernel
theorem cell_27_83_2 : C 27 83 2 := by decide +kernel
theorem cell_27_83_3 : C 27 83 3 := by decide +kernel
theorem cell_27_83_4 : C 27 83 4 := by decide +kernel
theorem cell_27_83_5 : C 27 83 5 := by decide +kernel
theorem row_27_83 : ThresholdAt 27 83 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 83 0 cell_27_83_0
  | exact S 27 83 1 cell_27_83_1
  | exact S 27 83 2 cell_27_83_2
  | exact S 27 83 3 cell_27_83_3
  | exact S 27 83 4 cell_27_83_4
  | exact S 27 83 5 cell_27_83_5
theorem cell_27_84_0 : C 27 84 0 := by decide +kernel
theorem cell_27_84_1 : C 27 84 1 := by decide +kernel
theorem cell_27_84_2 : C 27 84 2 := by decide +kernel
theorem cell_27_84_3 : C 27 84 3 := by decide +kernel
theorem cell_27_84_4 : C 27 84 4 := by decide +kernel
theorem cell_27_84_5 : C 27 84 5 := by decide +kernel
theorem row_27_84 : ThresholdAt 27 84 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 84 0 cell_27_84_0
  | exact S 27 84 1 cell_27_84_1
  | exact S 27 84 2 cell_27_84_2
  | exact S 27 84 3 cell_27_84_3
  | exact S 27 84 4 cell_27_84_4
  | exact S 27 84 5 cell_27_84_5
theorem cell_27_85_0 : C 27 85 0 := by decide +kernel
theorem cell_27_85_1 : C 27 85 1 := by decide +kernel
theorem cell_27_85_2 : C 27 85 2 := by decide +kernel
theorem cell_27_85_3 : C 27 85 3 := by decide +kernel
theorem cell_27_85_4 : C 27 85 4 := by decide +kernel
theorem cell_27_85_5 : C 27 85 5 := by decide +kernel
theorem row_27_85 : ThresholdAt 27 85 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 85 0 cell_27_85_0
  | exact S 27 85 1 cell_27_85_1
  | exact S 27 85 2 cell_27_85_2
  | exact S 27 85 3 cell_27_85_3
  | exact S 27 85 4 cell_27_85_4
  | exact S 27 85 5 cell_27_85_5
theorem cell_27_86_0 : C 27 86 0 := by decide +kernel
theorem cell_27_86_1 : C 27 86 1 := by decide +kernel
theorem cell_27_86_2 : C 27 86 2 := by decide +kernel
theorem cell_27_86_3 : C 27 86 3 := by decide +kernel
theorem cell_27_86_4 : C 27 86 4 := by decide +kernel
theorem cell_27_86_5 : C 27 86 5 := by decide +kernel
theorem row_27_86 : ThresholdAt 27 86 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 86 0 cell_27_86_0
  | exact S 27 86 1 cell_27_86_1
  | exact S 27 86 2 cell_27_86_2
  | exact S 27 86 3 cell_27_86_3
  | exact S 27 86 4 cell_27_86_4
  | exact S 27 86 5 cell_27_86_5
theorem cell_27_87_0 : C 27 87 0 := by decide +kernel
theorem cell_27_87_1 : C 27 87 1 := by decide +kernel
theorem cell_27_87_2 : C 27 87 2 := by decide +kernel
theorem cell_27_87_3 : C 27 87 3 := by decide +kernel
theorem cell_27_87_4 : C 27 87 4 := by decide +kernel
theorem cell_27_87_5 : C 27 87 5 := by decide +kernel
theorem row_27_87 : ThresholdAt 27 87 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 87 0 cell_27_87_0
  | exact S 27 87 1 cell_27_87_1
  | exact S 27 87 2 cell_27_87_2
  | exact S 27 87 3 cell_27_87_3
  | exact S 27 87 4 cell_27_87_4
  | exact S 27 87 5 cell_27_87_5
theorem cell_27_88_0 : C 27 88 0 := by decide +kernel
theorem cell_27_88_1 : C 27 88 1 := by decide +kernel
theorem cell_27_88_2 : C 27 88 2 := by decide +kernel
theorem cell_27_88_3 : C 27 88 3 := by decide +kernel
theorem cell_27_88_4 : C 27 88 4 := by decide +kernel
theorem cell_27_88_5 : C 27 88 5 := by decide +kernel
theorem row_27_88 : ThresholdAt 27 88 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 88 0 cell_27_88_0
  | exact S 27 88 1 cell_27_88_1
  | exact S 27 88 2 cell_27_88_2
  | exact S 27 88 3 cell_27_88_3
  | exact S 27 88 4 cell_27_88_4
  | exact S 27 88 5 cell_27_88_5
theorem cell_27_89_0 : C 27 89 0 := by decide +kernel
theorem cell_27_89_1 : C 27 89 1 := by decide +kernel
theorem cell_27_89_2 : C 27 89 2 := by decide +kernel
theorem cell_27_89_3 : C 27 89 3 := by decide +kernel
theorem cell_27_89_4 : C 27 89 4 := by decide +kernel
theorem cell_27_89_5 : C 27 89 5 := by decide +kernel
theorem row_27_89 : ThresholdAt 27 89 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 89 0 cell_27_89_0
  | exact S 27 89 1 cell_27_89_1
  | exact S 27 89 2 cell_27_89_2
  | exact S 27 89 3 cell_27_89_3
  | exact S 27 89 4 cell_27_89_4
  | exact S 27 89 5 cell_27_89_5
theorem cell_27_90_0 : C 27 90 0 := by decide +kernel
theorem cell_27_90_1 : C 27 90 1 := by decide +kernel
theorem cell_27_90_2 : C 27 90 2 := by decide +kernel
theorem cell_27_90_3 : C 27 90 3 := by decide +kernel
theorem cell_27_90_4 : C 27 90 4 := by decide +kernel
theorem cell_27_90_5 : C 27 90 5 := by decide +kernel
theorem row_27_90 : ThresholdAt 27 90 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 90 0 cell_27_90_0
  | exact S 27 90 1 cell_27_90_1
  | exact S 27 90 2 cell_27_90_2
  | exact S 27 90 3 cell_27_90_3
  | exact S 27 90 4 cell_27_90_4
  | exact S 27 90 5 cell_27_90_5
theorem cell_27_91_0 : C 27 91 0 := by decide +kernel
theorem cell_27_91_1 : C 27 91 1 := by decide +kernel
theorem cell_27_91_2 : C 27 91 2 := by decide +kernel
theorem cell_27_91_3 : C 27 91 3 := by decide +kernel
theorem cell_27_91_4 : C 27 91 4 := by decide +kernel
theorem cell_27_91_5 : C 27 91 5 := by decide +kernel
theorem row_27_91 : ThresholdAt 27 91 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 91 0 cell_27_91_0
  | exact S 27 91 1 cell_27_91_1
  | exact S 27 91 2 cell_27_91_2
  | exact S 27 91 3 cell_27_91_3
  | exact S 27 91 4 cell_27_91_4
  | exact S 27 91 5 cell_27_91_5
theorem cell_27_92_0 : C 27 92 0 := by decide +kernel
theorem cell_27_92_1 : C 27 92 1 := by decide +kernel
theorem cell_27_92_2 : C 27 92 2 := by decide +kernel
theorem cell_27_92_3 : C 27 92 3 := by decide +kernel
theorem cell_27_92_4 : C 27 92 4 := by decide +kernel
theorem cell_27_92_5 : C 27 92 5 := by decide +kernel
theorem row_27_92 : ThresholdAt 27 92 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 92 0 cell_27_92_0
  | exact S 27 92 1 cell_27_92_1
  | exact S 27 92 2 cell_27_92_2
  | exact S 27 92 3 cell_27_92_3
  | exact S 27 92 4 cell_27_92_4
  | exact S 27 92 5 cell_27_92_5
theorem cell_27_93_0 : C 27 93 0 := by decide +kernel
theorem cell_27_93_1 : C 27 93 1 := by decide +kernel
theorem cell_27_93_2 : C 27 93 2 := by decide +kernel
theorem cell_27_93_3 : C 27 93 3 := by decide +kernel
theorem cell_27_93_4 : C 27 93 4 := by decide +kernel
theorem cell_27_93_5 : C 27 93 5 := by decide +kernel
theorem row_27_93 : ThresholdAt 27 93 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 93 0 cell_27_93_0
  | exact S 27 93 1 cell_27_93_1
  | exact S 27 93 2 cell_27_93_2
  | exact S 27 93 3 cell_27_93_3
  | exact S 27 93 4 cell_27_93_4
  | exact S 27 93 5 cell_27_93_5
theorem cell_27_94_0 : C 27 94 0 := by decide +kernel
theorem cell_27_94_1 : C 27 94 1 := by decide +kernel
theorem cell_27_94_2 : C 27 94 2 := by decide +kernel
theorem cell_27_94_3 : C 27 94 3 := by decide +kernel
theorem cell_27_94_4 : C 27 94 4 := by decide +kernel
theorem cell_27_94_5 : C 27 94 5 := by decide +kernel
theorem row_27_94 : ThresholdAt 27 94 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 94 0 cell_27_94_0
  | exact S 27 94 1 cell_27_94_1
  | exact S 27 94 2 cell_27_94_2
  | exact S 27 94 3 cell_27_94_3
  | exact S 27 94 4 cell_27_94_4
  | exact S 27 94 5 cell_27_94_5
theorem cell_27_95_0 : C 27 95 0 := by decide +kernel
theorem cell_27_95_1 : C 27 95 1 := by decide +kernel
theorem cell_27_95_2 : C 27 95 2 := by decide +kernel
theorem cell_27_95_3 : C 27 95 3 := by decide +kernel
theorem cell_27_95_4 : C 27 95 4 := by decide +kernel
theorem cell_27_95_5 : C 27 95 5 := by decide +kernel
theorem row_27_95 : ThresholdAt 27 95 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 95 0 cell_27_95_0
  | exact S 27 95 1 cell_27_95_1
  | exact S 27 95 2 cell_27_95_2
  | exact S 27 95 3 cell_27_95_3
  | exact S 27 95 4 cell_27_95_4
  | exact S 27 95 5 cell_27_95_5
theorem cell_27_96_0 : C 27 96 0 := by decide +kernel
theorem cell_27_96_1 : C 27 96 1 := by decide +kernel
theorem cell_27_96_2 : C 27 96 2 := by decide +kernel
theorem cell_27_96_3 : C 27 96 3 := by decide +kernel
theorem cell_27_96_4 : C 27 96 4 := by decide +kernel
theorem cell_27_96_5 : C 27 96 5 := by decide +kernel
theorem row_27_96 : ThresholdAt 27 96 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 96 0 cell_27_96_0
  | exact S 27 96 1 cell_27_96_1
  | exact S 27 96 2 cell_27_96_2
  | exact S 27 96 3 cell_27_96_3
  | exact S 27 96 4 cell_27_96_4
  | exact S 27 96 5 cell_27_96_5
theorem cell_27_97_0 : C 27 97 0 := by decide +kernel
theorem cell_27_97_1 : C 27 97 1 := by decide +kernel
theorem cell_27_97_2 : C 27 97 2 := by decide +kernel
theorem cell_27_97_3 : C 27 97 3 := by decide +kernel
theorem cell_27_97_4 : C 27 97 4 := by decide +kernel
theorem cell_27_97_5 : C 27 97 5 := by decide +kernel
theorem row_27_97 : ThresholdAt 27 97 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 97 0 cell_27_97_0
  | exact S 27 97 1 cell_27_97_1
  | exact S 27 97 2 cell_27_97_2
  | exact S 27 97 3 cell_27_97_3
  | exact S 27 97 4 cell_27_97_4
  | exact S 27 97 5 cell_27_97_5
theorem cell_27_98_0 : C 27 98 0 := by decide +kernel
theorem cell_27_98_1 : C 27 98 1 := by decide +kernel
theorem cell_27_98_2 : C 27 98 2 := by decide +kernel
theorem cell_27_98_3 : C 27 98 3 := by decide +kernel
theorem cell_27_98_4 : C 27 98 4 := by decide +kernel
theorem cell_27_98_5 : C 27 98 5 := by decide +kernel
theorem row_27_98 : ThresholdAt 27 98 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 98 0 cell_27_98_0
  | exact S 27 98 1 cell_27_98_1
  | exact S 27 98 2 cell_27_98_2
  | exact S 27 98 3 cell_27_98_3
  | exact S 27 98 4 cell_27_98_4
  | exact S 27 98 5 cell_27_98_5
theorem cell_27_99_0 : C 27 99 0 := by decide +kernel
theorem cell_27_99_1 : C 27 99 1 := by decide +kernel
theorem cell_27_99_2 : C 27 99 2 := by decide +kernel
theorem cell_27_99_3 : C 27 99 3 := by decide +kernel
theorem cell_27_99_4 : C 27 99 4 := by decide +kernel
theorem cell_27_99_5 : C 27 99 5 := by decide +kernel
theorem row_27_99 : ThresholdAt 27 99 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 99 0 cell_27_99_0
  | exact S 27 99 1 cell_27_99_1
  | exact S 27 99 2 cell_27_99_2
  | exact S 27 99 3 cell_27_99_3
  | exact S 27 99 4 cell_27_99_4
  | exact S 27 99 5 cell_27_99_5
theorem cell_27_100_0 : C 27 100 0 := by decide +kernel
theorem cell_27_100_1 : C 27 100 1 := by decide +kernel
theorem cell_27_100_2 : C 27 100 2 := by decide +kernel
theorem cell_27_100_3 : C 27 100 3 := by decide +kernel
theorem cell_27_100_4 : C 27 100 4 := by decide +kernel
theorem cell_27_100_5 : C 27 100 5 := by decide +kernel
theorem row_27_100 : ThresholdAt 27 100 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 100 0 cell_27_100_0
  | exact S 27 100 1 cell_27_100_1
  | exact S 27 100 2 cell_27_100_2
  | exact S 27 100 3 cell_27_100_3
  | exact S 27 100 4 cell_27_100_4
  | exact S 27 100 5 cell_27_100_5
theorem cell_27_101_0 : C 27 101 0 := by decide +kernel
theorem cell_27_101_1 : C 27 101 1 := by decide +kernel
theorem cell_27_101_2 : C 27 101 2 := by decide +kernel
theorem cell_27_101_3 : C 27 101 3 := by decide +kernel
theorem cell_27_101_4 : C 27 101 4 := by decide +kernel
theorem cell_27_101_5 : C 27 101 5 := by decide +kernel
theorem row_27_101 : ThresholdAt 27 101 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 101 0 cell_27_101_0
  | exact S 27 101 1 cell_27_101_1
  | exact S 27 101 2 cell_27_101_2
  | exact S 27 101 3 cell_27_101_3
  | exact S 27 101 4 cell_27_101_4
  | exact S 27 101 5 cell_27_101_5
theorem cell_27_102_0 : C 27 102 0 := by decide +kernel
theorem cell_27_102_1 : C 27 102 1 := by decide +kernel
theorem cell_27_102_2 : C 27 102 2 := by decide +kernel
theorem cell_27_102_3 : C 27 102 3 := by decide +kernel
theorem cell_27_102_4 : C 27 102 4 := by decide +kernel
theorem cell_27_102_5 : C 27 102 5 := by decide +kernel
theorem row_27_102 : ThresholdAt 27 102 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 102 0 cell_27_102_0
  | exact S 27 102 1 cell_27_102_1
  | exact S 27 102 2 cell_27_102_2
  | exact S 27 102 3 cell_27_102_3
  | exact S 27 102 4 cell_27_102_4
  | exact S 27 102 5 cell_27_102_5
theorem cell_27_103_0 : C 27 103 0 := by decide +kernel
theorem cell_27_103_1 : C 27 103 1 := by decide +kernel
theorem cell_27_103_2 : C 27 103 2 := by decide +kernel
theorem cell_27_103_3 : C 27 103 3 := by decide +kernel
theorem cell_27_103_4 : C 27 103 4 := by decide +kernel
theorem cell_27_103_5 : C 27 103 5 := by decide +kernel
theorem row_27_103 : ThresholdAt 27 103 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 103 0 cell_27_103_0
  | exact S 27 103 1 cell_27_103_1
  | exact S 27 103 2 cell_27_103_2
  | exact S 27 103 3 cell_27_103_3
  | exact S 27 103 4 cell_27_103_4
  | exact S 27 103 5 cell_27_103_5
theorem cell_27_104_0 : C 27 104 0 := by decide +kernel
theorem cell_27_104_1 : C 27 104 1 := by decide +kernel
theorem cell_27_104_2 : C 27 104 2 := by decide +kernel
theorem cell_27_104_3 : C 27 104 3 := by decide +kernel
theorem cell_27_104_4 : C 27 104 4 := by decide +kernel
theorem cell_27_104_5 : C 27 104 5 := by decide +kernel
theorem row_27_104 : ThresholdAt 27 104 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 104 0 cell_27_104_0
  | exact S 27 104 1 cell_27_104_1
  | exact S 27 104 2 cell_27_104_2
  | exact S 27 104 3 cell_27_104_3
  | exact S 27 104 4 cell_27_104_4
  | exact S 27 104 5 cell_27_104_5
theorem cell_27_105_0 : C 27 105 0 := by decide +kernel
theorem cell_27_105_1 : C 27 105 1 := by decide +kernel
theorem cell_27_105_2 : C 27 105 2 := by decide +kernel
theorem cell_27_105_3 : C 27 105 3 := by decide +kernel
theorem cell_27_105_4 : C 27 105 4 := by decide +kernel
theorem cell_27_105_5 : C 27 105 5 := by decide +kernel
theorem row_27_105 : ThresholdAt 27 105 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 105 0 cell_27_105_0
  | exact S 27 105 1 cell_27_105_1
  | exact S 27 105 2 cell_27_105_2
  | exact S 27 105 3 cell_27_105_3
  | exact S 27 105 4 cell_27_105_4
  | exact S 27 105 5 cell_27_105_5
theorem cell_27_106_0 : C 27 106 0 := by decide +kernel
theorem cell_27_106_1 : C 27 106 1 := by decide +kernel
theorem cell_27_106_2 : C 27 106 2 := by decide +kernel
theorem cell_27_106_3 : C 27 106 3 := by decide +kernel
theorem cell_27_106_4 : C 27 106 4 := by decide +kernel
theorem cell_27_106_5 : C 27 106 5 := by decide +kernel
theorem row_27_106 : ThresholdAt 27 106 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 106 0 cell_27_106_0
  | exact S 27 106 1 cell_27_106_1
  | exact S 27 106 2 cell_27_106_2
  | exact S 27 106 3 cell_27_106_3
  | exact S 27 106 4 cell_27_106_4
  | exact S 27 106 5 cell_27_106_5
theorem cell_27_107_0 : C 27 107 0 := by decide +kernel
theorem cell_27_107_1 : C 27 107 1 := by decide +kernel
theorem cell_27_107_2 : C 27 107 2 := by decide +kernel
theorem cell_27_107_3 : C 27 107 3 := by decide +kernel
theorem cell_27_107_4 : C 27 107 4 := by decide +kernel
theorem cell_27_107_5 : C 27 107 5 := by decide +kernel
theorem row_27_107 : ThresholdAt 27 107 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 107 0 cell_27_107_0
  | exact S 27 107 1 cell_27_107_1
  | exact S 27 107 2 cell_27_107_2
  | exact S 27 107 3 cell_27_107_3
  | exact S 27 107 4 cell_27_107_4
  | exact S 27 107 5 cell_27_107_5
theorem cell_27_108_0 : C 27 108 0 := by decide +kernel
theorem cell_27_108_1 : C 27 108 1 := by decide +kernel
theorem cell_27_108_2 : C 27 108 2 := by decide +kernel
theorem cell_27_108_3 : C 27 108 3 := by decide +kernel
theorem cell_27_108_4 : C 27 108 4 := by decide +kernel
theorem cell_27_108_5 : C 27 108 5 := by decide +kernel
theorem row_27_108 : ThresholdAt 27 108 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 108 0 cell_27_108_0
  | exact S 27 108 1 cell_27_108_1
  | exact S 27 108 2 cell_27_108_2
  | exact S 27 108 3 cell_27_108_3
  | exact S 27 108 4 cell_27_108_4
  | exact S 27 108 5 cell_27_108_5
theorem cell_27_109_0 : C 27 109 0 := by decide +kernel
theorem cell_27_109_1 : C 27 109 1 := by decide +kernel
theorem cell_27_109_2 : C 27 109 2 := by decide +kernel
theorem cell_27_109_3 : C 27 109 3 := by decide +kernel
theorem cell_27_109_4 : C 27 109 4 := by decide +kernel
theorem cell_27_109_5 : C 27 109 5 := by decide +kernel
theorem row_27_109 : ThresholdAt 27 109 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 109 0 cell_27_109_0
  | exact S 27 109 1 cell_27_109_1
  | exact S 27 109 2 cell_27_109_2
  | exact S 27 109 3 cell_27_109_3
  | exact S 27 109 4 cell_27_109_4
  | exact S 27 109 5 cell_27_109_5
theorem cell_27_110_0 : C 27 110 0 := by decide +kernel
theorem cell_27_110_1 : C 27 110 1 := by decide +kernel
theorem cell_27_110_2 : C 27 110 2 := by decide +kernel
theorem cell_27_110_3 : C 27 110 3 := by decide +kernel
theorem cell_27_110_4 : C 27 110 4 := by decide +kernel
theorem cell_27_110_5 : C 27 110 5 := by decide +kernel
theorem row_27_110 : ThresholdAt 27 110 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 110 0 cell_27_110_0
  | exact S 27 110 1 cell_27_110_1
  | exact S 27 110 2 cell_27_110_2
  | exact S 27 110 3 cell_27_110_3
  | exact S 27 110 4 cell_27_110_4
  | exact S 27 110 5 cell_27_110_5
theorem cell_27_111_0 : C 27 111 0 := by decide +kernel
theorem cell_27_111_1 : C 27 111 1 := by decide +kernel
theorem cell_27_111_2 : C 27 111 2 := by decide +kernel
theorem cell_27_111_3 : C 27 111 3 := by decide +kernel
theorem cell_27_111_4 : C 27 111 4 := by decide +kernel
theorem cell_27_111_5 : C 27 111 5 := by decide +kernel
theorem row_27_111 : ThresholdAt 27 111 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 111 0 cell_27_111_0
  | exact S 27 111 1 cell_27_111_1
  | exact S 27 111 2 cell_27_111_2
  | exact S 27 111 3 cell_27_111_3
  | exact S 27 111 4 cell_27_111_4
  | exact S 27 111 5 cell_27_111_5
theorem cell_27_112_0 : C 27 112 0 := by decide +kernel
theorem cell_27_112_1 : C 27 112 1 := by decide +kernel
theorem cell_27_112_2 : C 27 112 2 := by decide +kernel
theorem cell_27_112_3 : C 27 112 3 := by decide +kernel
theorem cell_27_112_4 : C 27 112 4 := by decide +kernel
theorem cell_27_112_5 : C 27 112 5 := by decide +kernel
theorem row_27_112 : ThresholdAt 27 112 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 27 112 0 cell_27_112_0
  | exact S 27 112 1 cell_27_112_1
  | exact S 27 112 2 cell_27_112_2
  | exact S 27 112 3 cell_27_112_3
  | exact S 27 112 4 cell_27_112_4
  | exact S 27 112 5 cell_27_112_5
theorem checkedR27 : ∀ V ∈ List.range 113, ThresholdAt 27 V := by
  intro V hV
  have hv : V < 113 := List.mem_range.mp hV
  by_cases h0_113 : V < 56
  · by_cases h0_56 : V < 28
    · by_cases h0_28 : V < 14
      · by_cases h0_14 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have he : V = 0 := by omega
              subst V
              exact row_27_0
            · by_cases h1_3 : V < 2
              · have he : V = 1 := by omega
                subst V
                exact row_27_1
              · have he : V = 2 := by omega
                subst V
                exact row_27_2
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have he : V = 3 := by omega
                subst V
                exact row_27_3
              · have he : V = 4 := by omega
                subst V
                exact row_27_4
            · by_cases h5_7 : V < 6
              · have he : V = 5 := by omega
                subst V
                exact row_27_5
              · have he : V = 6 := by omega
                subst V
                exact row_27_6
        · by_cases h7_14 : V < 10
          · by_cases h7_10 : V < 8
            · have he : V = 7 := by omega
              subst V
              exact row_27_7
            · by_cases h8_10 : V < 9
              · have he : V = 8 := by omega
                subst V
                exact row_27_8
              · have he : V = 9 := by omega
                subst V
                exact row_27_9
          · by_cases h10_14 : V < 12
            · by_cases h10_12 : V < 11
              · have he : V = 10 := by omega
                subst V
                exact row_27_10
              · have he : V = 11 := by omega
                subst V
                exact row_27_11
            · by_cases h12_14 : V < 13
              · have he : V = 12 := by omega
                subst V
                exact row_27_12
              · have he : V = 13 := by omega
                subst V
                exact row_27_13
      · by_cases h14_28 : V < 21
        · by_cases h14_21 : V < 17
          · by_cases h14_17 : V < 15
            · have he : V = 14 := by omega
              subst V
              exact row_27_14
            · by_cases h15_17 : V < 16
              · have he : V = 15 := by omega
                subst V
                exact row_27_15
              · have he : V = 16 := by omega
                subst V
                exact row_27_16
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have he : V = 17 := by omega
                subst V
                exact row_27_17
              · have he : V = 18 := by omega
                subst V
                exact row_27_18
            · by_cases h19_21 : V < 20
              · have he : V = 19 := by omega
                subst V
                exact row_27_19
              · have he : V = 20 := by omega
                subst V
                exact row_27_20
        · by_cases h21_28 : V < 24
          · by_cases h21_24 : V < 22
            · have he : V = 21 := by omega
              subst V
              exact row_27_21
            · by_cases h22_24 : V < 23
              · have he : V = 22 := by omega
                subst V
                exact row_27_22
              · have he : V = 23 := by omega
                subst V
                exact row_27_23
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have he : V = 24 := by omega
                subst V
                exact row_27_24
              · have he : V = 25 := by omega
                subst V
                exact row_27_25
            · by_cases h26_28 : V < 27
              · have he : V = 26 := by omega
                subst V
                exact row_27_26
              · have he : V = 27 := by omega
                subst V
                exact row_27_27
    · by_cases h28_56 : V < 42
      · by_cases h28_42 : V < 35
        · by_cases h28_35 : V < 31
          · by_cases h28_31 : V < 29
            · have he : V = 28 := by omega
              subst V
              exact row_27_28
            · by_cases h29_31 : V < 30
              · have he : V = 29 := by omega
                subst V
                exact row_27_29
              · have he : V = 30 := by omega
                subst V
                exact row_27_30
          · by_cases h31_35 : V < 33
            · by_cases h31_33 : V < 32
              · have he : V = 31 := by omega
                subst V
                exact row_27_31
              · have he : V = 32 := by omega
                subst V
                exact row_27_32
            · by_cases h33_35 : V < 34
              · have he : V = 33 := by omega
                subst V
                exact row_27_33
              · have he : V = 34 := by omega
                subst V
                exact row_27_34
        · by_cases h35_42 : V < 38
          · by_cases h35_38 : V < 36
            · have he : V = 35 := by omega
              subst V
              exact row_27_35
            · by_cases h36_38 : V < 37
              · have he : V = 36 := by omega
                subst V
                exact row_27_36
              · have he : V = 37 := by omega
                subst V
                exact row_27_37
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have he : V = 38 := by omega
                subst V
                exact row_27_38
              · have he : V = 39 := by omega
                subst V
                exact row_27_39
            · by_cases h40_42 : V < 41
              · have he : V = 40 := by omega
                subst V
                exact row_27_40
              · have he : V = 41 := by omega
                subst V
                exact row_27_41
      · by_cases h42_56 : V < 49
        · by_cases h42_49 : V < 45
          · by_cases h42_45 : V < 43
            · have he : V = 42 := by omega
              subst V
              exact row_27_42
            · by_cases h43_45 : V < 44
              · have he : V = 43 := by omega
                subst V
                exact row_27_43
              · have he : V = 44 := by omega
                subst V
                exact row_27_44
          · by_cases h45_49 : V < 47
            · by_cases h45_47 : V < 46
              · have he : V = 45 := by omega
                subst V
                exact row_27_45
              · have he : V = 46 := by omega
                subst V
                exact row_27_46
            · by_cases h47_49 : V < 48
              · have he : V = 47 := by omega
                subst V
                exact row_27_47
              · have he : V = 48 := by omega
                subst V
                exact row_27_48
        · by_cases h49_56 : V < 52
          · by_cases h49_52 : V < 50
            · have he : V = 49 := by omega
              subst V
              exact row_27_49
            · by_cases h50_52 : V < 51
              · have he : V = 50 := by omega
                subst V
                exact row_27_50
              · have he : V = 51 := by omega
                subst V
                exact row_27_51
          · by_cases h52_56 : V < 54
            · by_cases h52_54 : V < 53
              · have he : V = 52 := by omega
                subst V
                exact row_27_52
              · have he : V = 53 := by omega
                subst V
                exact row_27_53
            · by_cases h54_56 : V < 55
              · have he : V = 54 := by omega
                subst V
                exact row_27_54
              · have he : V = 55 := by omega
                subst V
                exact row_27_55
  · by_cases h56_113 : V < 84
    · by_cases h56_84 : V < 70
      · by_cases h56_70 : V < 63
        · by_cases h56_63 : V < 59
          · by_cases h56_59 : V < 57
            · have he : V = 56 := by omega
              subst V
              exact row_27_56
            · by_cases h57_59 : V < 58
              · have he : V = 57 := by omega
                subst V
                exact row_27_57
              · have he : V = 58 := by omega
                subst V
                exact row_27_58
          · by_cases h59_63 : V < 61
            · by_cases h59_61 : V < 60
              · have he : V = 59 := by omega
                subst V
                exact row_27_59
              · have he : V = 60 := by omega
                subst V
                exact row_27_60
            · by_cases h61_63 : V < 62
              · have he : V = 61 := by omega
                subst V
                exact row_27_61
              · have he : V = 62 := by omega
                subst V
                exact row_27_62
        · by_cases h63_70 : V < 66
          · by_cases h63_66 : V < 64
            · have he : V = 63 := by omega
              subst V
              exact row_27_63
            · by_cases h64_66 : V < 65
              · have he : V = 64 := by omega
                subst V
                exact row_27_64
              · have he : V = 65 := by omega
                subst V
                exact row_27_65
          · by_cases h66_70 : V < 68
            · by_cases h66_68 : V < 67
              · have he : V = 66 := by omega
                subst V
                exact row_27_66
              · have he : V = 67 := by omega
                subst V
                exact row_27_67
            · by_cases h68_70 : V < 69
              · have he : V = 68 := by omega
                subst V
                exact row_27_68
              · have he : V = 69 := by omega
                subst V
                exact row_27_69
      · by_cases h70_84 : V < 77
        · by_cases h70_77 : V < 73
          · by_cases h70_73 : V < 71
            · have he : V = 70 := by omega
              subst V
              exact row_27_70
            · by_cases h71_73 : V < 72
              · have he : V = 71 := by omega
                subst V
                exact row_27_71
              · have he : V = 72 := by omega
                subst V
                exact row_27_72
          · by_cases h73_77 : V < 75
            · by_cases h73_75 : V < 74
              · have he : V = 73 := by omega
                subst V
                exact row_27_73
              · have he : V = 74 := by omega
                subst V
                exact row_27_74
            · by_cases h75_77 : V < 76
              · have he : V = 75 := by omega
                subst V
                exact row_27_75
              · have he : V = 76 := by omega
                subst V
                exact row_27_76
        · by_cases h77_84 : V < 80
          · by_cases h77_80 : V < 78
            · have he : V = 77 := by omega
              subst V
              exact row_27_77
            · by_cases h78_80 : V < 79
              · have he : V = 78 := by omega
                subst V
                exact row_27_78
              · have he : V = 79 := by omega
                subst V
                exact row_27_79
          · by_cases h80_84 : V < 82
            · by_cases h80_82 : V < 81
              · have he : V = 80 := by omega
                subst V
                exact row_27_80
              · have he : V = 81 := by omega
                subst V
                exact row_27_81
            · by_cases h82_84 : V < 83
              · have he : V = 82 := by omega
                subst V
                exact row_27_82
              · have he : V = 83 := by omega
                subst V
                exact row_27_83
    · by_cases h84_113 : V < 98
      · by_cases h84_98 : V < 91
        · by_cases h84_91 : V < 87
          · by_cases h84_87 : V < 85
            · have he : V = 84 := by omega
              subst V
              exact row_27_84
            · by_cases h85_87 : V < 86
              · have he : V = 85 := by omega
                subst V
                exact row_27_85
              · have he : V = 86 := by omega
                subst V
                exact row_27_86
          · by_cases h87_91 : V < 89
            · by_cases h87_89 : V < 88
              · have he : V = 87 := by omega
                subst V
                exact row_27_87
              · have he : V = 88 := by omega
                subst V
                exact row_27_88
            · by_cases h89_91 : V < 90
              · have he : V = 89 := by omega
                subst V
                exact row_27_89
              · have he : V = 90 := by omega
                subst V
                exact row_27_90
        · by_cases h91_98 : V < 94
          · by_cases h91_94 : V < 92
            · have he : V = 91 := by omega
              subst V
              exact row_27_91
            · by_cases h92_94 : V < 93
              · have he : V = 92 := by omega
                subst V
                exact row_27_92
              · have he : V = 93 := by omega
                subst V
                exact row_27_93
          · by_cases h94_98 : V < 96
            · by_cases h94_96 : V < 95
              · have he : V = 94 := by omega
                subst V
                exact row_27_94
              · have he : V = 95 := by omega
                subst V
                exact row_27_95
            · by_cases h96_98 : V < 97
              · have he : V = 96 := by omega
                subst V
                exact row_27_96
              · have he : V = 97 := by omega
                subst V
                exact row_27_97
      · by_cases h98_113 : V < 105
        · by_cases h98_105 : V < 101
          · by_cases h98_101 : V < 99
            · have he : V = 98 := by omega
              subst V
              exact row_27_98
            · by_cases h99_101 : V < 100
              · have he : V = 99 := by omega
                subst V
                exact row_27_99
              · have he : V = 100 := by omega
                subst V
                exact row_27_100
          · by_cases h101_105 : V < 103
            · by_cases h101_103 : V < 102
              · have he : V = 101 := by omega
                subst V
                exact row_27_101
              · have he : V = 102 := by omega
                subst V
                exact row_27_102
            · by_cases h103_105 : V < 104
              · have he : V = 103 := by omega
                subst V
                exact row_27_103
              · have he : V = 104 := by omega
                subst V
                exact row_27_104
        · by_cases h105_113 : V < 109
          · by_cases h105_109 : V < 107
            · by_cases h105_107 : V < 106
              · have he : V = 105 := by omega
                subst V
                exact row_27_105
              · have he : V = 106 := by omega
                subst V
                exact row_27_106
            · by_cases h107_109 : V < 108
              · have he : V = 107 := by omega
                subst V
                exact row_27_107
              · have he : V = 108 := by omega
                subst V
                exact row_27_108
          · by_cases h109_113 : V < 111
            · by_cases h109_111 : V < 110
              · have he : V = 109 := by omega
                subst V
                exact row_27_109
              · have he : V = 110 := by omega
                subst V
                exact row_27_110
            · by_cases h111_113 : V < 112
              · have he : V = 111 := by omega
                subst V
                exact row_27_111
              · have he : V = 112 := by omega
                subst V
                exact row_27_112
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
