import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked03

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_4_0_0 : C 4 0 0 := by decide +kernel
theorem cell_4_0_1 : C 4 0 1 := by decide +kernel
theorem cell_4_0_2 : C 4 0 2 := by decide +kernel
theorem cell_4_0_3 : C 4 0 3 := by decide +kernel
theorem cell_4_0_4 : C 4 0 4 := by decide +kernel
theorem cell_4_0_5 : C 4 0 5 := by decide +kernel
theorem row_4_0 : ThresholdAt 4 0 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 0 0 cell_4_0_0
  | exact S 4 0 1 cell_4_0_1
  | exact S 4 0 2 cell_4_0_2
  | exact S 4 0 3 cell_4_0_3
  | exact S 4 0 4 cell_4_0_4
  | exact S 4 0 5 cell_4_0_5
theorem cell_4_1_0 : C 4 1 0 := by decide +kernel
theorem cell_4_1_1 : C 4 1 1 := by decide +kernel
theorem cell_4_1_2 : C 4 1 2 := by decide +kernel
theorem cell_4_1_3 : C 4 1 3 := by decide +kernel
theorem cell_4_1_4 : C 4 1 4 := by decide +kernel
theorem cell_4_1_5 : C 4 1 5 := by decide +kernel
theorem row_4_1 : ThresholdAt 4 1 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 1 0 cell_4_1_0
  | exact S 4 1 1 cell_4_1_1
  | exact S 4 1 2 cell_4_1_2
  | exact S 4 1 3 cell_4_1_3
  | exact S 4 1 4 cell_4_1_4
  | exact S 4 1 5 cell_4_1_5
theorem cell_4_2_0 : C 4 2 0 := by decide +kernel
theorem cell_4_2_1 : C 4 2 1 := by decide +kernel
theorem cell_4_2_2 : C 4 2 2 := by decide +kernel
theorem cell_4_2_3 : C 4 2 3 := by decide +kernel
theorem cell_4_2_4 : C 4 2 4 := by decide +kernel
theorem cell_4_2_5 : C 4 2 5 := by decide +kernel
theorem row_4_2 : ThresholdAt 4 2 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 2 0 cell_4_2_0
  | exact S 4 2 1 cell_4_2_1
  | exact S 4 2 2 cell_4_2_2
  | exact S 4 2 3 cell_4_2_3
  | exact S 4 2 4 cell_4_2_4
  | exact S 4 2 5 cell_4_2_5
theorem cell_4_3_0 : C 4 3 0 := by decide +kernel
theorem cell_4_3_1 : C 4 3 1 := by decide +kernel
theorem cell_4_3_2 : C 4 3 2 := by decide +kernel
theorem cell_4_3_3 : C 4 3 3 := by decide +kernel
theorem cell_4_3_4 : C 4 3 4 := by decide +kernel
theorem cell_4_3_5 : C 4 3 5 := by decide +kernel
theorem row_4_3 : ThresholdAt 4 3 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 3 0 cell_4_3_0
  | exact S 4 3 1 cell_4_3_1
  | exact S 4 3 2 cell_4_3_2
  | exact S 4 3 3 cell_4_3_3
  | exact S 4 3 4 cell_4_3_4
  | exact S 4 3 5 cell_4_3_5
theorem cell_4_4_0 : C 4 4 0 := by decide +kernel
theorem cell_4_4_1 : C 4 4 1 := by decide +kernel
theorem cell_4_4_2 : C 4 4 2 := by decide +kernel
theorem cell_4_4_3 : C 4 4 3 := by decide +kernel
theorem cell_4_4_4 : C 4 4 4 := by decide +kernel
theorem cell_4_4_5 : C 4 4 5 := by decide +kernel
theorem row_4_4 : ThresholdAt 4 4 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 4 0 cell_4_4_0
  | exact S 4 4 1 cell_4_4_1
  | exact S 4 4 2 cell_4_4_2
  | exact S 4 4 3 cell_4_4_3
  | exact S 4 4 4 cell_4_4_4
  | exact S 4 4 5 cell_4_4_5
theorem cell_4_5_0 : C 4 5 0 := by decide +kernel
theorem cell_4_5_1 : C 4 5 1 := by decide +kernel
theorem cell_4_5_2 : C 4 5 2 := by decide +kernel
theorem cell_4_5_3 : C 4 5 3 := by decide +kernel
theorem cell_4_5_4 : C 4 5 4 := by decide +kernel
theorem cell_4_5_5 : C 4 5 5 := by decide +kernel
theorem row_4_5 : ThresholdAt 4 5 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 5 0 cell_4_5_0
  | exact S 4 5 1 cell_4_5_1
  | exact S 4 5 2 cell_4_5_2
  | exact S 4 5 3 cell_4_5_3
  | exact S 4 5 4 cell_4_5_4
  | exact S 4 5 5 cell_4_5_5
theorem cell_4_6_0 : C 4 6 0 := by decide +kernel
theorem cell_4_6_1 : C 4 6 1 := by decide +kernel
theorem cell_4_6_2 : C 4 6 2 := by decide +kernel
theorem cell_4_6_3 : C 4 6 3 := by decide +kernel
theorem cell_4_6_4 : C 4 6 4 := by decide +kernel
theorem cell_4_6_5 : C 4 6 5 := by decide +kernel
theorem row_4_6 : ThresholdAt 4 6 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 6 0 cell_4_6_0
  | exact S 4 6 1 cell_4_6_1
  | exact S 4 6 2 cell_4_6_2
  | exact S 4 6 3 cell_4_6_3
  | exact S 4 6 4 cell_4_6_4
  | exact S 4 6 5 cell_4_6_5
theorem cell_4_7_0 : C 4 7 0 := by decide +kernel
theorem cell_4_7_1 : C 4 7 1 := by decide +kernel
theorem cell_4_7_2 : C 4 7 2 := by decide +kernel
theorem cell_4_7_3 : C 4 7 3 := by decide +kernel
theorem cell_4_7_4 : C 4 7 4 := by decide +kernel
theorem cell_4_7_5 : C 4 7 5 := by decide +kernel
theorem row_4_7 : ThresholdAt 4 7 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 7 0 cell_4_7_0
  | exact S 4 7 1 cell_4_7_1
  | exact S 4 7 2 cell_4_7_2
  | exact S 4 7 3 cell_4_7_3
  | exact S 4 7 4 cell_4_7_4
  | exact S 4 7 5 cell_4_7_5
theorem cell_4_8_0 : C 4 8 0 := by decide +kernel
theorem cell_4_8_1 : C 4 8 1 := by decide +kernel
theorem cell_4_8_2 : C 4 8 2 := by decide +kernel
theorem cell_4_8_3 : C 4 8 3 := by decide +kernel
theorem cell_4_8_4 : C 4 8 4 := by decide +kernel
theorem cell_4_8_5 : C 4 8 5 := by decide +kernel
theorem row_4_8 : ThresholdAt 4 8 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 8 0 cell_4_8_0
  | exact S 4 8 1 cell_4_8_1
  | exact S 4 8 2 cell_4_8_2
  | exact S 4 8 3 cell_4_8_3
  | exact S 4 8 4 cell_4_8_4
  | exact S 4 8 5 cell_4_8_5
theorem cell_4_9_0 : C 4 9 0 := by decide +kernel
theorem cell_4_9_1 : C 4 9 1 := by decide +kernel
theorem cell_4_9_2 : C 4 9 2 := by decide +kernel
theorem cell_4_9_3 : C 4 9 3 := by decide +kernel
theorem cell_4_9_4 : C 4 9 4 := by decide +kernel
theorem cell_4_9_5 : C 4 9 5 := by decide +kernel
theorem row_4_9 : ThresholdAt 4 9 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 9 0 cell_4_9_0
  | exact S 4 9 1 cell_4_9_1
  | exact S 4 9 2 cell_4_9_2
  | exact S 4 9 3 cell_4_9_3
  | exact S 4 9 4 cell_4_9_4
  | exact S 4 9 5 cell_4_9_5
theorem cell_4_10_0 : C 4 10 0 := by decide +kernel
theorem cell_4_10_1 : C 4 10 1 := by decide +kernel
theorem cell_4_10_2 : C 4 10 2 := by decide +kernel
theorem cell_4_10_3 : C 4 10 3 := by decide +kernel
theorem cell_4_10_4 : C 4 10 4 := by decide +kernel
theorem cell_4_10_5 : C 4 10 5 := by decide +kernel
theorem row_4_10 : ThresholdAt 4 10 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 10 0 cell_4_10_0
  | exact S 4 10 1 cell_4_10_1
  | exact S 4 10 2 cell_4_10_2
  | exact S 4 10 3 cell_4_10_3
  | exact S 4 10 4 cell_4_10_4
  | exact S 4 10 5 cell_4_10_5
theorem cell_4_11_0 : C 4 11 0 := by decide +kernel
theorem cell_4_11_1 : C 4 11 1 := by decide +kernel
theorem cell_4_11_2 : C 4 11 2 := by decide +kernel
theorem cell_4_11_3 : C 4 11 3 := by decide +kernel
theorem cell_4_11_4 : C 4 11 4 := by decide +kernel
theorem cell_4_11_5 : C 4 11 5 := by decide +kernel
theorem row_4_11 : ThresholdAt 4 11 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 11 0 cell_4_11_0
  | exact S 4 11 1 cell_4_11_1
  | exact S 4 11 2 cell_4_11_2
  | exact S 4 11 3 cell_4_11_3
  | exact S 4 11 4 cell_4_11_4
  | exact S 4 11 5 cell_4_11_5
theorem cell_4_12_0 : C 4 12 0 := by decide +kernel
theorem cell_4_12_1 : C 4 12 1 := by decide +kernel
theorem cell_4_12_2 : C 4 12 2 := by decide +kernel
theorem cell_4_12_3 : C 4 12 3 := by decide +kernel
theorem cell_4_12_4 : C 4 12 4 := by decide +kernel
theorem cell_4_12_5 : C 4 12 5 := by decide +kernel
theorem row_4_12 : ThresholdAt 4 12 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 12 0 cell_4_12_0
  | exact S 4 12 1 cell_4_12_1
  | exact S 4 12 2 cell_4_12_2
  | exact S 4 12 3 cell_4_12_3
  | exact S 4 12 4 cell_4_12_4
  | exact S 4 12 5 cell_4_12_5
theorem cell_4_13_0 : C 4 13 0 := by decide +kernel
theorem cell_4_13_1 : C 4 13 1 := by decide +kernel
theorem cell_4_13_2 : C 4 13 2 := by decide +kernel
theorem cell_4_13_3 : C 4 13 3 := by decide +kernel
theorem cell_4_13_4 : C 4 13 4 := by decide +kernel
theorem cell_4_13_5 : C 4 13 5 := by decide +kernel
theorem row_4_13 : ThresholdAt 4 13 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 13 0 cell_4_13_0
  | exact S 4 13 1 cell_4_13_1
  | exact S 4 13 2 cell_4_13_2
  | exact S 4 13 3 cell_4_13_3
  | exact S 4 13 4 cell_4_13_4
  | exact S 4 13 5 cell_4_13_5
theorem cell_4_14_0 : C 4 14 0 := by decide +kernel
theorem cell_4_14_1 : C 4 14 1 := by decide +kernel
theorem cell_4_14_2 : C 4 14 2 := by decide +kernel
theorem cell_4_14_3 : C 4 14 3 := by decide +kernel
theorem cell_4_14_4 : C 4 14 4 := by decide +kernel
theorem cell_4_14_5 : C 4 14 5 := by decide +kernel
theorem row_4_14 : ThresholdAt 4 14 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 14 0 cell_4_14_0
  | exact S 4 14 1 cell_4_14_1
  | exact S 4 14 2 cell_4_14_2
  | exact S 4 14 3 cell_4_14_3
  | exact S 4 14 4 cell_4_14_4
  | exact S 4 14 5 cell_4_14_5
theorem cell_4_15_0 : C 4 15 0 := by decide +kernel
theorem cell_4_15_1 : C 4 15 1 := by decide +kernel
theorem cell_4_15_2 : C 4 15 2 := by decide +kernel
theorem cell_4_15_3 : C 4 15 3 := by decide +kernel
theorem cell_4_15_4 : C 4 15 4 := by decide +kernel
theorem cell_4_15_5 : C 4 15 5 := by decide +kernel
theorem row_4_15 : ThresholdAt 4 15 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 15 0 cell_4_15_0
  | exact S 4 15 1 cell_4_15_1
  | exact S 4 15 2 cell_4_15_2
  | exact S 4 15 3 cell_4_15_3
  | exact S 4 15 4 cell_4_15_4
  | exact S 4 15 5 cell_4_15_5
theorem cell_4_16_0 : C 4 16 0 := by decide +kernel
theorem cell_4_16_1 : C 4 16 1 := by decide +kernel
theorem cell_4_16_2 : C 4 16 2 := by decide +kernel
theorem cell_4_16_3 : C 4 16 3 := by decide +kernel
theorem cell_4_16_4 : C 4 16 4 := by decide +kernel
theorem cell_4_16_5 : C 4 16 5 := by decide +kernel
theorem row_4_16 : ThresholdAt 4 16 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 16 0 cell_4_16_0
  | exact S 4 16 1 cell_4_16_1
  | exact S 4 16 2 cell_4_16_2
  | exact S 4 16 3 cell_4_16_3
  | exact S 4 16 4 cell_4_16_4
  | exact S 4 16 5 cell_4_16_5
theorem cell_4_17_0 : C 4 17 0 := by decide +kernel
theorem cell_4_17_1 : C 4 17 1 := by decide +kernel
theorem cell_4_17_2 : C 4 17 2 := by decide +kernel
theorem cell_4_17_3 : C 4 17 3 := by decide +kernel
theorem cell_4_17_4 : C 4 17 4 := by decide +kernel
theorem cell_4_17_5 : C 4 17 5 := by decide +kernel
theorem row_4_17 : ThresholdAt 4 17 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 17 0 cell_4_17_0
  | exact S 4 17 1 cell_4_17_1
  | exact S 4 17 2 cell_4_17_2
  | exact S 4 17 3 cell_4_17_3
  | exact S 4 17 4 cell_4_17_4
  | exact S 4 17 5 cell_4_17_5
theorem cell_4_18_0 : C 4 18 0 := by decide +kernel
theorem cell_4_18_1 : C 4 18 1 := by decide +kernel
theorem cell_4_18_2 : C 4 18 2 := by decide +kernel
theorem cell_4_18_3 : C 4 18 3 := by decide +kernel
theorem cell_4_18_4 : C 4 18 4 := by decide +kernel
theorem cell_4_18_5 : C 4 18 5 := by decide +kernel
theorem row_4_18 : ThresholdAt 4 18 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 18 0 cell_4_18_0
  | exact S 4 18 1 cell_4_18_1
  | exact S 4 18 2 cell_4_18_2
  | exact S 4 18 3 cell_4_18_3
  | exact S 4 18 4 cell_4_18_4
  | exact S 4 18 5 cell_4_18_5
theorem cell_4_19_0 : C 4 19 0 := by decide +kernel
theorem cell_4_19_1 : C 4 19 1 := by decide +kernel
theorem cell_4_19_2 : C 4 19 2 := by decide +kernel
theorem cell_4_19_3 : C 4 19 3 := by decide +kernel
theorem cell_4_19_4 : C 4 19 4 := by decide +kernel
theorem cell_4_19_5 : C 4 19 5 := by decide +kernel
theorem row_4_19 : ThresholdAt 4 19 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 19 0 cell_4_19_0
  | exact S 4 19 1 cell_4_19_1
  | exact S 4 19 2 cell_4_19_2
  | exact S 4 19 3 cell_4_19_3
  | exact S 4 19 4 cell_4_19_4
  | exact S 4 19 5 cell_4_19_5
theorem cell_4_20_0 : C 4 20 0 := by decide +kernel
theorem cell_4_20_1 : C 4 20 1 := by decide +kernel
theorem cell_4_20_2 : C 4 20 2 := by decide +kernel
theorem cell_4_20_3 : C 4 20 3 := by decide +kernel
theorem cell_4_20_4 : C 4 20 4 := by decide +kernel
theorem cell_4_20_5 : C 4 20 5 := by decide +kernel
theorem row_4_20 : ThresholdAt 4 20 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 20 0 cell_4_20_0
  | exact S 4 20 1 cell_4_20_1
  | exact S 4 20 2 cell_4_20_2
  | exact S 4 20 3 cell_4_20_3
  | exact S 4 20 4 cell_4_20_4
  | exact S 4 20 5 cell_4_20_5
theorem cell_4_21_0 : C 4 21 0 := by decide +kernel
theorem cell_4_21_1 : C 4 21 1 := by decide +kernel
theorem cell_4_21_2 : C 4 21 2 := by decide +kernel
theorem cell_4_21_3 : C 4 21 3 := by decide +kernel
theorem cell_4_21_4 : C 4 21 4 := by decide +kernel
theorem cell_4_21_5 : C 4 21 5 := by decide +kernel
theorem row_4_21 : ThresholdAt 4 21 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 21 0 cell_4_21_0
  | exact S 4 21 1 cell_4_21_1
  | exact S 4 21 2 cell_4_21_2
  | exact S 4 21 3 cell_4_21_3
  | exact S 4 21 4 cell_4_21_4
  | exact S 4 21 5 cell_4_21_5
theorem cell_4_22_0 : C 4 22 0 := by decide +kernel
theorem cell_4_22_1 : C 4 22 1 := by decide +kernel
theorem cell_4_22_2 : C 4 22 2 := by decide +kernel
theorem cell_4_22_3 : C 4 22 3 := by decide +kernel
theorem cell_4_22_4 : C 4 22 4 := by decide +kernel
theorem cell_4_22_5 : C 4 22 5 := by decide +kernel
theorem row_4_22 : ThresholdAt 4 22 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 22 0 cell_4_22_0
  | exact S 4 22 1 cell_4_22_1
  | exact S 4 22 2 cell_4_22_2
  | exact S 4 22 3 cell_4_22_3
  | exact S 4 22 4 cell_4_22_4
  | exact S 4 22 5 cell_4_22_5
theorem cell_4_23_0 : C 4 23 0 := by decide +kernel
theorem cell_4_23_1 : C 4 23 1 := by decide +kernel
theorem cell_4_23_2 : C 4 23 2 := by decide +kernel
theorem cell_4_23_3 : C 4 23 3 := by decide +kernel
theorem cell_4_23_4 : C 4 23 4 := by decide +kernel
theorem cell_4_23_5 : C 4 23 5 := by decide +kernel
theorem row_4_23 : ThresholdAt 4 23 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 23 0 cell_4_23_0
  | exact S 4 23 1 cell_4_23_1
  | exact S 4 23 2 cell_4_23_2
  | exact S 4 23 3 cell_4_23_3
  | exact S 4 23 4 cell_4_23_4
  | exact S 4 23 5 cell_4_23_5
theorem cell_4_24_0 : C 4 24 0 := by decide +kernel
theorem cell_4_24_1 : C 4 24 1 := by decide +kernel
theorem cell_4_24_2 : C 4 24 2 := by decide +kernel
theorem cell_4_24_3 : C 4 24 3 := by decide +kernel
theorem cell_4_24_4 : C 4 24 4 := by decide +kernel
theorem cell_4_24_5 : C 4 24 5 := by decide +kernel
theorem row_4_24 : ThresholdAt 4 24 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 24 0 cell_4_24_0
  | exact S 4 24 1 cell_4_24_1
  | exact S 4 24 2 cell_4_24_2
  | exact S 4 24 3 cell_4_24_3
  | exact S 4 24 4 cell_4_24_4
  | exact S 4 24 5 cell_4_24_5
theorem cell_4_25_0 : C 4 25 0 := by decide +kernel
theorem cell_4_25_1 : C 4 25 1 := by decide +kernel
theorem cell_4_25_2 : C 4 25 2 := by decide +kernel
theorem cell_4_25_3 : C 4 25 3 := by decide +kernel
theorem cell_4_25_4 : C 4 25 4 := by decide +kernel
theorem cell_4_25_5 : C 4 25 5 := by decide +kernel
theorem row_4_25 : ThresholdAt 4 25 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 25 0 cell_4_25_0
  | exact S 4 25 1 cell_4_25_1
  | exact S 4 25 2 cell_4_25_2
  | exact S 4 25 3 cell_4_25_3
  | exact S 4 25 4 cell_4_25_4
  | exact S 4 25 5 cell_4_25_5
theorem cell_4_26_0 : C 4 26 0 := by decide +kernel
theorem cell_4_26_1 : C 4 26 1 := by decide +kernel
theorem cell_4_26_2 : C 4 26 2 := by decide +kernel
theorem cell_4_26_3 : C 4 26 3 := by decide +kernel
theorem cell_4_26_4 : C 4 26 4 := by decide +kernel
theorem cell_4_26_5 : C 4 26 5 := by decide +kernel
theorem row_4_26 : ThresholdAt 4 26 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 26 0 cell_4_26_0
  | exact S 4 26 1 cell_4_26_1
  | exact S 4 26 2 cell_4_26_2
  | exact S 4 26 3 cell_4_26_3
  | exact S 4 26 4 cell_4_26_4
  | exact S 4 26 5 cell_4_26_5
theorem cell_4_27_0 : C 4 27 0 := by decide +kernel
theorem cell_4_27_1 : C 4 27 1 := by decide +kernel
theorem cell_4_27_2 : C 4 27 2 := by decide +kernel
theorem cell_4_27_3 : C 4 27 3 := by decide +kernel
theorem cell_4_27_4 : C 4 27 4 := by decide +kernel
theorem cell_4_27_5 : C 4 27 5 := by decide +kernel
theorem row_4_27 : ThresholdAt 4 27 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 27 0 cell_4_27_0
  | exact S 4 27 1 cell_4_27_1
  | exact S 4 27 2 cell_4_27_2
  | exact S 4 27 3 cell_4_27_3
  | exact S 4 27 4 cell_4_27_4
  | exact S 4 27 5 cell_4_27_5
theorem cell_4_28_0 : C 4 28 0 := by decide +kernel
theorem cell_4_28_1 : C 4 28 1 := by decide +kernel
theorem cell_4_28_2 : C 4 28 2 := by decide +kernel
theorem cell_4_28_3 : C 4 28 3 := by decide +kernel
theorem cell_4_28_4 : C 4 28 4 := by decide +kernel
theorem cell_4_28_5 : C 4 28 5 := by decide +kernel
theorem row_4_28 : ThresholdAt 4 28 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 28 0 cell_4_28_0
  | exact S 4 28 1 cell_4_28_1
  | exact S 4 28 2 cell_4_28_2
  | exact S 4 28 3 cell_4_28_3
  | exact S 4 28 4 cell_4_28_4
  | exact S 4 28 5 cell_4_28_5
theorem cell_4_29_0 : C 4 29 0 := by decide +kernel
theorem cell_4_29_1 : C 4 29 1 := by decide +kernel
theorem cell_4_29_2 : C 4 29 2 := by decide +kernel
theorem cell_4_29_3 : C 4 29 3 := by decide +kernel
theorem cell_4_29_4 : C 4 29 4 := by decide +kernel
theorem cell_4_29_5 : C 4 29 5 := by decide +kernel
theorem row_4_29 : ThresholdAt 4 29 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 29 0 cell_4_29_0
  | exact S 4 29 1 cell_4_29_1
  | exact S 4 29 2 cell_4_29_2
  | exact S 4 29 3 cell_4_29_3
  | exact S 4 29 4 cell_4_29_4
  | exact S 4 29 5 cell_4_29_5
theorem cell_4_30_0 : C 4 30 0 := by decide +kernel
theorem cell_4_30_1 : C 4 30 1 := by decide +kernel
theorem cell_4_30_2 : C 4 30 2 := by decide +kernel
theorem cell_4_30_3 : C 4 30 3 := by decide +kernel
theorem cell_4_30_4 : C 4 30 4 := by decide +kernel
theorem cell_4_30_5 : C 4 30 5 := by decide +kernel
theorem row_4_30 : ThresholdAt 4 30 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 30 0 cell_4_30_0
  | exact S 4 30 1 cell_4_30_1
  | exact S 4 30 2 cell_4_30_2
  | exact S 4 30 3 cell_4_30_3
  | exact S 4 30 4 cell_4_30_4
  | exact S 4 30 5 cell_4_30_5
theorem cell_4_31_0 : C 4 31 0 := by decide +kernel
theorem cell_4_31_1 : C 4 31 1 := by decide +kernel
theorem cell_4_31_2 : C 4 31 2 := by decide +kernel
theorem cell_4_31_3 : C 4 31 3 := by decide +kernel
theorem cell_4_31_4 : C 4 31 4 := by decide +kernel
theorem cell_4_31_5 : C 4 31 5 := by decide +kernel
theorem row_4_31 : ThresholdAt 4 31 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 31 0 cell_4_31_0
  | exact S 4 31 1 cell_4_31_1
  | exact S 4 31 2 cell_4_31_2
  | exact S 4 31 3 cell_4_31_3
  | exact S 4 31 4 cell_4_31_4
  | exact S 4 31 5 cell_4_31_5
theorem cell_4_32_0 : C 4 32 0 := by decide +kernel
theorem cell_4_32_1 : C 4 32 1 := by decide +kernel
theorem cell_4_32_2 : C 4 32 2 := by decide +kernel
theorem cell_4_32_3 : C 4 32 3 := by decide +kernel
theorem cell_4_32_4 : C 4 32 4 := by decide +kernel
theorem cell_4_32_5 : C 4 32 5 := by decide +kernel
theorem row_4_32 : ThresholdAt 4 32 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 32 0 cell_4_32_0
  | exact S 4 32 1 cell_4_32_1
  | exact S 4 32 2 cell_4_32_2
  | exact S 4 32 3 cell_4_32_3
  | exact S 4 32 4 cell_4_32_4
  | exact S 4 32 5 cell_4_32_5
theorem cell_4_33_0 : C 4 33 0 := by decide +kernel
theorem cell_4_33_1 : C 4 33 1 := by decide +kernel
theorem cell_4_33_2 : C 4 33 2 := by decide +kernel
theorem cell_4_33_3 : C 4 33 3 := by decide +kernel
theorem cell_4_33_4 : C 4 33 4 := by decide +kernel
theorem cell_4_33_5 : C 4 33 5 := by decide +kernel
theorem row_4_33 : ThresholdAt 4 33 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 33 0 cell_4_33_0
  | exact S 4 33 1 cell_4_33_1
  | exact S 4 33 2 cell_4_33_2
  | exact S 4 33 3 cell_4_33_3
  | exact S 4 33 4 cell_4_33_4
  | exact S 4 33 5 cell_4_33_5
theorem cell_4_34_0 : C 4 34 0 := by decide +kernel
theorem cell_4_34_1 : C 4 34 1 := by decide +kernel
theorem cell_4_34_2 : C 4 34 2 := by decide +kernel
theorem cell_4_34_3 : C 4 34 3 := by decide +kernel
theorem cell_4_34_4 : C 4 34 4 := by decide +kernel
theorem cell_4_34_5 : C 4 34 5 := by decide +kernel
theorem row_4_34 : ThresholdAt 4 34 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 34 0 cell_4_34_0
  | exact S 4 34 1 cell_4_34_1
  | exact S 4 34 2 cell_4_34_2
  | exact S 4 34 3 cell_4_34_3
  | exact S 4 34 4 cell_4_34_4
  | exact S 4 34 5 cell_4_34_5
theorem cell_4_35_0 : C 4 35 0 := by decide +kernel
theorem cell_4_35_1 : C 4 35 1 := by decide +kernel
theorem cell_4_35_2 : C 4 35 2 := by decide +kernel
theorem cell_4_35_3 : C 4 35 3 := by decide +kernel
theorem cell_4_35_4 : C 4 35 4 := by decide +kernel
theorem cell_4_35_5 : C 4 35 5 := by decide +kernel
theorem row_4_35 : ThresholdAt 4 35 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 35 0 cell_4_35_0
  | exact S 4 35 1 cell_4_35_1
  | exact S 4 35 2 cell_4_35_2
  | exact S 4 35 3 cell_4_35_3
  | exact S 4 35 4 cell_4_35_4
  | exact S 4 35 5 cell_4_35_5
theorem cell_4_36_0 : C 4 36 0 := by decide +kernel
theorem cell_4_36_1 : C 4 36 1 := by decide +kernel
theorem cell_4_36_2 : C 4 36 2 := by decide +kernel
theorem cell_4_36_3 : C 4 36 3 := by decide +kernel
theorem cell_4_36_4 : C 4 36 4 := by decide +kernel
theorem cell_4_36_5 : C 4 36 5 := by decide +kernel
theorem row_4_36 : ThresholdAt 4 36 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 36 0 cell_4_36_0
  | exact S 4 36 1 cell_4_36_1
  | exact S 4 36 2 cell_4_36_2
  | exact S 4 36 3 cell_4_36_3
  | exact S 4 36 4 cell_4_36_4
  | exact S 4 36 5 cell_4_36_5
theorem cell_4_37_0 : C 4 37 0 := by decide +kernel
theorem cell_4_37_1 : C 4 37 1 := by decide +kernel
theorem cell_4_37_2 : C 4 37 2 := by decide +kernel
theorem cell_4_37_3 : C 4 37 3 := by decide +kernel
theorem cell_4_37_4 : C 4 37 4 := by decide +kernel
theorem cell_4_37_5 : C 4 37 5 := by decide +kernel
theorem row_4_37 : ThresholdAt 4 37 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 37 0 cell_4_37_0
  | exact S 4 37 1 cell_4_37_1
  | exact S 4 37 2 cell_4_37_2
  | exact S 4 37 3 cell_4_37_3
  | exact S 4 37 4 cell_4_37_4
  | exact S 4 37 5 cell_4_37_5
theorem cell_4_38_0 : C 4 38 0 := by decide +kernel
theorem cell_4_38_1 : C 4 38 1 := by decide +kernel
theorem cell_4_38_2 : C 4 38 2 := by decide +kernel
theorem cell_4_38_3 : C 4 38 3 := by decide +kernel
theorem cell_4_38_4 : C 4 38 4 := by decide +kernel
theorem cell_4_38_5 : C 4 38 5 := by decide +kernel
theorem row_4_38 : ThresholdAt 4 38 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 38 0 cell_4_38_0
  | exact S 4 38 1 cell_4_38_1
  | exact S 4 38 2 cell_4_38_2
  | exact S 4 38 3 cell_4_38_3
  | exact S 4 38 4 cell_4_38_4
  | exact S 4 38 5 cell_4_38_5
theorem cell_4_39_0 : C 4 39 0 := by decide +kernel
theorem cell_4_39_1 : C 4 39 1 := by decide +kernel
theorem cell_4_39_2 : C 4 39 2 := by decide +kernel
theorem cell_4_39_3 : C 4 39 3 := by decide +kernel
theorem cell_4_39_4 : C 4 39 4 := by decide +kernel
theorem cell_4_39_5 : C 4 39 5 := by decide +kernel
theorem row_4_39 : ThresholdAt 4 39 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 39 0 cell_4_39_0
  | exact S 4 39 1 cell_4_39_1
  | exact S 4 39 2 cell_4_39_2
  | exact S 4 39 3 cell_4_39_3
  | exact S 4 39 4 cell_4_39_4
  | exact S 4 39 5 cell_4_39_5
theorem cell_4_40_0 : C 4 40 0 := by decide +kernel
theorem cell_4_40_1 : C 4 40 1 := by decide +kernel
theorem cell_4_40_2 : C 4 40 2 := by decide +kernel
theorem cell_4_40_3 : C 4 40 3 := by decide +kernel
theorem cell_4_40_4 : C 4 40 4 := by decide +kernel
theorem cell_4_40_5 : C 4 40 5 := by decide +kernel
theorem row_4_40 : ThresholdAt 4 40 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 40 0 cell_4_40_0
  | exact S 4 40 1 cell_4_40_1
  | exact S 4 40 2 cell_4_40_2
  | exact S 4 40 3 cell_4_40_3
  | exact S 4 40 4 cell_4_40_4
  | exact S 4 40 5 cell_4_40_5
theorem cell_4_41_0 : C 4 41 0 := by decide +kernel
theorem cell_4_41_1 : C 4 41 1 := by decide +kernel
theorem cell_4_41_2 : C 4 41 2 := by decide +kernel
theorem cell_4_41_3 : C 4 41 3 := by decide +kernel
theorem cell_4_41_4 : C 4 41 4 := by decide +kernel
theorem cell_4_41_5 : C 4 41 5 := by decide +kernel
theorem row_4_41 : ThresholdAt 4 41 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 41 0 cell_4_41_0
  | exact S 4 41 1 cell_4_41_1
  | exact S 4 41 2 cell_4_41_2
  | exact S 4 41 3 cell_4_41_3
  | exact S 4 41 4 cell_4_41_4
  | exact S 4 41 5 cell_4_41_5
theorem cell_4_42_0 : C 4 42 0 := by decide +kernel
theorem cell_4_42_1 : C 4 42 1 := by decide +kernel
theorem cell_4_42_2 : C 4 42 2 := by decide +kernel
theorem cell_4_42_3 : C 4 42 3 := by decide +kernel
theorem cell_4_42_4 : C 4 42 4 := by decide +kernel
theorem cell_4_42_5 : C 4 42 5 := by decide +kernel
theorem row_4_42 : ThresholdAt 4 42 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 42 0 cell_4_42_0
  | exact S 4 42 1 cell_4_42_1
  | exact S 4 42 2 cell_4_42_2
  | exact S 4 42 3 cell_4_42_3
  | exact S 4 42 4 cell_4_42_4
  | exact S 4 42 5 cell_4_42_5
theorem cell_4_43_0 : C 4 43 0 := by decide +kernel
theorem cell_4_43_1 : C 4 43 1 := by decide +kernel
theorem cell_4_43_2 : C 4 43 2 := by decide +kernel
theorem cell_4_43_3 : C 4 43 3 := by decide +kernel
theorem cell_4_43_4 : C 4 43 4 := by decide +kernel
theorem cell_4_43_5 : C 4 43 5 := by decide +kernel
theorem row_4_43 : ThresholdAt 4 43 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 43 0 cell_4_43_0
  | exact S 4 43 1 cell_4_43_1
  | exact S 4 43 2 cell_4_43_2
  | exact S 4 43 3 cell_4_43_3
  | exact S 4 43 4 cell_4_43_4
  | exact S 4 43 5 cell_4_43_5
theorem cell_4_44_0 : C 4 44 0 := by decide +kernel
theorem cell_4_44_1 : C 4 44 1 := by decide +kernel
theorem cell_4_44_2 : C 4 44 2 := by decide +kernel
theorem cell_4_44_3 : C 4 44 3 := by decide +kernel
theorem cell_4_44_4 : C 4 44 4 := by decide +kernel
theorem cell_4_44_5 : C 4 44 5 := by decide +kernel
theorem row_4_44 : ThresholdAt 4 44 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 44 0 cell_4_44_0
  | exact S 4 44 1 cell_4_44_1
  | exact S 4 44 2 cell_4_44_2
  | exact S 4 44 3 cell_4_44_3
  | exact S 4 44 4 cell_4_44_4
  | exact S 4 44 5 cell_4_44_5
theorem cell_4_45_0 : C 4 45 0 := by decide +kernel
theorem cell_4_45_1 : C 4 45 1 := by decide +kernel
theorem cell_4_45_2 : C 4 45 2 := by decide +kernel
theorem cell_4_45_3 : C 4 45 3 := by decide +kernel
theorem cell_4_45_4 : C 4 45 4 := by decide +kernel
theorem cell_4_45_5 : C 4 45 5 := by decide +kernel
theorem row_4_45 : ThresholdAt 4 45 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 45 0 cell_4_45_0
  | exact S 4 45 1 cell_4_45_1
  | exact S 4 45 2 cell_4_45_2
  | exact S 4 45 3 cell_4_45_3
  | exact S 4 45 4 cell_4_45_4
  | exact S 4 45 5 cell_4_45_5
theorem cell_4_46_0 : C 4 46 0 := by decide +kernel
theorem cell_4_46_1 : C 4 46 1 := by decide +kernel
theorem cell_4_46_2 : C 4 46 2 := by decide +kernel
theorem cell_4_46_3 : C 4 46 3 := by decide +kernel
theorem cell_4_46_4 : C 4 46 4 := by decide +kernel
theorem cell_4_46_5 : C 4 46 5 := by decide +kernel
theorem row_4_46 : ThresholdAt 4 46 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 46 0 cell_4_46_0
  | exact S 4 46 1 cell_4_46_1
  | exact S 4 46 2 cell_4_46_2
  | exact S 4 46 3 cell_4_46_3
  | exact S 4 46 4 cell_4_46_4
  | exact S 4 46 5 cell_4_46_5
theorem cell_4_47_0 : C 4 47 0 := by decide +kernel
theorem cell_4_47_1 : C 4 47 1 := by decide +kernel
theorem cell_4_47_2 : C 4 47 2 := by decide +kernel
theorem cell_4_47_3 : C 4 47 3 := by decide +kernel
theorem cell_4_47_4 : C 4 47 4 := by decide +kernel
theorem cell_4_47_5 : C 4 47 5 := by decide +kernel
theorem row_4_47 : ThresholdAt 4 47 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 47 0 cell_4_47_0
  | exact S 4 47 1 cell_4_47_1
  | exact S 4 47 2 cell_4_47_2
  | exact S 4 47 3 cell_4_47_3
  | exact S 4 47 4 cell_4_47_4
  | exact S 4 47 5 cell_4_47_5
theorem cell_4_48_0 : C 4 48 0 := by decide +kernel
theorem cell_4_48_1 : C 4 48 1 := by decide +kernel
theorem cell_4_48_2 : C 4 48 2 := by decide +kernel
theorem cell_4_48_3 : C 4 48 3 := by decide +kernel
theorem cell_4_48_4 : C 4 48 4 := by decide +kernel
theorem cell_4_48_5 : C 4 48 5 := by decide +kernel
theorem row_4_48 : ThresholdAt 4 48 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 48 0 cell_4_48_0
  | exact S 4 48 1 cell_4_48_1
  | exact S 4 48 2 cell_4_48_2
  | exact S 4 48 3 cell_4_48_3
  | exact S 4 48 4 cell_4_48_4
  | exact S 4 48 5 cell_4_48_5
theorem cell_4_49_0 : C 4 49 0 := by decide +kernel
theorem cell_4_49_1 : C 4 49 1 := by decide +kernel
theorem cell_4_49_2 : C 4 49 2 := by decide +kernel
theorem cell_4_49_3 : C 4 49 3 := by decide +kernel
theorem cell_4_49_4 : C 4 49 4 := by decide +kernel
theorem cell_4_49_5 : C 4 49 5 := by decide +kernel
theorem row_4_49 : ThresholdAt 4 49 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 49 0 cell_4_49_0
  | exact S 4 49 1 cell_4_49_1
  | exact S 4 49 2 cell_4_49_2
  | exact S 4 49 3 cell_4_49_3
  | exact S 4 49 4 cell_4_49_4
  | exact S 4 49 5 cell_4_49_5
theorem cell_4_50_0 : C 4 50 0 := by decide +kernel
theorem cell_4_50_1 : C 4 50 1 := by decide +kernel
theorem cell_4_50_2 : C 4 50 2 := by decide +kernel
theorem cell_4_50_3 : C 4 50 3 := by decide +kernel
theorem cell_4_50_4 : C 4 50 4 := by decide +kernel
theorem cell_4_50_5 : C 4 50 5 := by decide +kernel
theorem row_4_50 : ThresholdAt 4 50 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 50 0 cell_4_50_0
  | exact S 4 50 1 cell_4_50_1
  | exact S 4 50 2 cell_4_50_2
  | exact S 4 50 3 cell_4_50_3
  | exact S 4 50 4 cell_4_50_4
  | exact S 4 50 5 cell_4_50_5
theorem cell_4_51_0 : C 4 51 0 := by decide +kernel
theorem cell_4_51_1 : C 4 51 1 := by decide +kernel
theorem cell_4_51_2 : C 4 51 2 := by decide +kernel
theorem cell_4_51_3 : C 4 51 3 := by decide +kernel
theorem cell_4_51_4 : C 4 51 4 := by decide +kernel
theorem cell_4_51_5 : C 4 51 5 := by decide +kernel
theorem row_4_51 : ThresholdAt 4 51 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 51 0 cell_4_51_0
  | exact S 4 51 1 cell_4_51_1
  | exact S 4 51 2 cell_4_51_2
  | exact S 4 51 3 cell_4_51_3
  | exact S 4 51 4 cell_4_51_4
  | exact S 4 51 5 cell_4_51_5
theorem cell_4_52_0 : C 4 52 0 := by decide +kernel
theorem cell_4_52_1 : C 4 52 1 := by decide +kernel
theorem cell_4_52_2 : C 4 52 2 := by decide +kernel
theorem cell_4_52_3 : C 4 52 3 := by decide +kernel
theorem cell_4_52_4 : C 4 52 4 := by decide +kernel
theorem cell_4_52_5 : C 4 52 5 := by decide +kernel
theorem row_4_52 : ThresholdAt 4 52 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 52 0 cell_4_52_0
  | exact S 4 52 1 cell_4_52_1
  | exact S 4 52 2 cell_4_52_2
  | exact S 4 52 3 cell_4_52_3
  | exact S 4 52 4 cell_4_52_4
  | exact S 4 52 5 cell_4_52_5
theorem cell_4_53_0 : C 4 53 0 := by decide +kernel
theorem cell_4_53_1 : C 4 53 1 := by decide +kernel
theorem cell_4_53_2 : C 4 53 2 := by decide +kernel
theorem cell_4_53_3 : C 4 53 3 := by decide +kernel
theorem cell_4_53_4 : C 4 53 4 := by decide +kernel
theorem cell_4_53_5 : C 4 53 5 := by decide +kernel
theorem row_4_53 : ThresholdAt 4 53 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 53 0 cell_4_53_0
  | exact S 4 53 1 cell_4_53_1
  | exact S 4 53 2 cell_4_53_2
  | exact S 4 53 3 cell_4_53_3
  | exact S 4 53 4 cell_4_53_4
  | exact S 4 53 5 cell_4_53_5
theorem cell_4_54_0 : C 4 54 0 := by decide +kernel
theorem cell_4_54_1 : C 4 54 1 := by decide +kernel
theorem cell_4_54_2 : C 4 54 2 := by decide +kernel
theorem cell_4_54_3 : C 4 54 3 := by decide +kernel
theorem cell_4_54_4 : C 4 54 4 := by decide +kernel
theorem cell_4_54_5 : C 4 54 5 := by decide +kernel
theorem row_4_54 : ThresholdAt 4 54 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 54 0 cell_4_54_0
  | exact S 4 54 1 cell_4_54_1
  | exact S 4 54 2 cell_4_54_2
  | exact S 4 54 3 cell_4_54_3
  | exact S 4 54 4 cell_4_54_4
  | exact S 4 54 5 cell_4_54_5
theorem cell_4_55_0 : C 4 55 0 := by decide +kernel
theorem cell_4_55_1 : C 4 55 1 := by decide +kernel
theorem cell_4_55_2 : C 4 55 2 := by decide +kernel
theorem cell_4_55_3 : C 4 55 3 := by decide +kernel
theorem cell_4_55_4 : C 4 55 4 := by decide +kernel
theorem cell_4_55_5 : C 4 55 5 := by decide +kernel
theorem row_4_55 : ThresholdAt 4 55 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 55 0 cell_4_55_0
  | exact S 4 55 1 cell_4_55_1
  | exact S 4 55 2 cell_4_55_2
  | exact S 4 55 3 cell_4_55_3
  | exact S 4 55 4 cell_4_55_4
  | exact S 4 55 5 cell_4_55_5
theorem cell_4_56_0 : C 4 56 0 := by decide +kernel
theorem cell_4_56_1 : C 4 56 1 := by decide +kernel
theorem cell_4_56_2 : C 4 56 2 := by decide +kernel
theorem cell_4_56_3 : C 4 56 3 := by decide +kernel
theorem cell_4_56_4 : C 4 56 4 := by decide +kernel
theorem cell_4_56_5 : C 4 56 5 := by decide +kernel
theorem row_4_56 : ThresholdAt 4 56 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 56 0 cell_4_56_0
  | exact S 4 56 1 cell_4_56_1
  | exact S 4 56 2 cell_4_56_2
  | exact S 4 56 3 cell_4_56_3
  | exact S 4 56 4 cell_4_56_4
  | exact S 4 56 5 cell_4_56_5
theorem cell_4_57_0 : C 4 57 0 := by decide +kernel
theorem cell_4_57_1 : C 4 57 1 := by decide +kernel
theorem cell_4_57_2 : C 4 57 2 := by decide +kernel
theorem cell_4_57_3 : C 4 57 3 := by decide +kernel
theorem cell_4_57_4 : C 4 57 4 := by decide +kernel
theorem cell_4_57_5 : C 4 57 5 := by decide +kernel
theorem row_4_57 : ThresholdAt 4 57 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 57 0 cell_4_57_0
  | exact S 4 57 1 cell_4_57_1
  | exact S 4 57 2 cell_4_57_2
  | exact S 4 57 3 cell_4_57_3
  | exact S 4 57 4 cell_4_57_4
  | exact S 4 57 5 cell_4_57_5
theorem cell_4_58_0 : C 4 58 0 := by decide +kernel
theorem cell_4_58_1 : C 4 58 1 := by decide +kernel
theorem cell_4_58_2 : C 4 58 2 := by decide +kernel
theorem cell_4_58_3 : C 4 58 3 := by decide +kernel
theorem cell_4_58_4 : C 4 58 4 := by decide +kernel
theorem cell_4_58_5 : C 4 58 5 := by decide +kernel
theorem row_4_58 : ThresholdAt 4 58 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 58 0 cell_4_58_0
  | exact S 4 58 1 cell_4_58_1
  | exact S 4 58 2 cell_4_58_2
  | exact S 4 58 3 cell_4_58_3
  | exact S 4 58 4 cell_4_58_4
  | exact S 4 58 5 cell_4_58_5
theorem cell_4_59_0 : C 4 59 0 := by decide +kernel
theorem cell_4_59_1 : C 4 59 1 := by decide +kernel
theorem cell_4_59_2 : C 4 59 2 := by decide +kernel
theorem cell_4_59_3 : C 4 59 3 := by decide +kernel
theorem cell_4_59_4 : C 4 59 4 := by decide +kernel
theorem cell_4_59_5 : C 4 59 5 := by decide +kernel
theorem row_4_59 : ThresholdAt 4 59 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 59 0 cell_4_59_0
  | exact S 4 59 1 cell_4_59_1
  | exact S 4 59 2 cell_4_59_2
  | exact S 4 59 3 cell_4_59_3
  | exact S 4 59 4 cell_4_59_4
  | exact S 4 59 5 cell_4_59_5
theorem cell_4_60_0 : C 4 60 0 := by decide +kernel
theorem cell_4_60_1 : C 4 60 1 := by decide +kernel
theorem cell_4_60_2 : C 4 60 2 := by decide +kernel
theorem cell_4_60_3 : C 4 60 3 := by decide +kernel
theorem cell_4_60_4 : C 4 60 4 := by decide +kernel
theorem cell_4_60_5 : C 4 60 5 := by decide +kernel
theorem row_4_60 : ThresholdAt 4 60 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 60 0 cell_4_60_0
  | exact S 4 60 1 cell_4_60_1
  | exact S 4 60 2 cell_4_60_2
  | exact S 4 60 3 cell_4_60_3
  | exact S 4 60 4 cell_4_60_4
  | exact S 4 60 5 cell_4_60_5
theorem cell_4_61_0 : C 4 61 0 := by decide +kernel
theorem cell_4_61_1 : C 4 61 1 := by decide +kernel
theorem cell_4_61_2 : C 4 61 2 := by decide +kernel
theorem cell_4_61_3 : C 4 61 3 := by decide +kernel
theorem cell_4_61_4 : C 4 61 4 := by decide +kernel
theorem cell_4_61_5 : C 4 61 5 := by decide +kernel
theorem row_4_61 : ThresholdAt 4 61 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 61 0 cell_4_61_0
  | exact S 4 61 1 cell_4_61_1
  | exact S 4 61 2 cell_4_61_2
  | exact S 4 61 3 cell_4_61_3
  | exact S 4 61 4 cell_4_61_4
  | exact S 4 61 5 cell_4_61_5
theorem cell_4_62_0 : C 4 62 0 := by decide +kernel
theorem cell_4_62_1 : C 4 62 1 := by decide +kernel
theorem cell_4_62_2 : C 4 62 2 := by decide +kernel
theorem cell_4_62_3 : C 4 62 3 := by decide +kernel
theorem cell_4_62_4 : C 4 62 4 := by decide +kernel
theorem cell_4_62_5 : C 4 62 5 := by decide +kernel
theorem row_4_62 : ThresholdAt 4 62 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 62 0 cell_4_62_0
  | exact S 4 62 1 cell_4_62_1
  | exact S 4 62 2 cell_4_62_2
  | exact S 4 62 3 cell_4_62_3
  | exact S 4 62 4 cell_4_62_4
  | exact S 4 62 5 cell_4_62_5
theorem cell_4_63_0 : C 4 63 0 := by decide +kernel
theorem cell_4_63_1 : C 4 63 1 := by decide +kernel
theorem cell_4_63_2 : C 4 63 2 := by decide +kernel
theorem cell_4_63_3 : C 4 63 3 := by decide +kernel
theorem cell_4_63_4 : C 4 63 4 := by decide +kernel
theorem cell_4_63_5 : C 4 63 5 := by decide +kernel
theorem row_4_63 : ThresholdAt 4 63 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 63 0 cell_4_63_0
  | exact S 4 63 1 cell_4_63_1
  | exact S 4 63 2 cell_4_63_2
  | exact S 4 63 3 cell_4_63_3
  | exact S 4 63 4 cell_4_63_4
  | exact S 4 63 5 cell_4_63_5
theorem cell_4_64_0 : C 4 64 0 := by decide +kernel
theorem cell_4_64_1 : C 4 64 1 := by decide +kernel
theorem cell_4_64_2 : C 4 64 2 := by decide +kernel
theorem cell_4_64_3 : C 4 64 3 := by decide +kernel
theorem cell_4_64_4 : C 4 64 4 := by decide +kernel
theorem cell_4_64_5 : C 4 64 5 := by decide +kernel
theorem row_4_64 : ThresholdAt 4 64 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 64 0 cell_4_64_0
  | exact S 4 64 1 cell_4_64_1
  | exact S 4 64 2 cell_4_64_2
  | exact S 4 64 3 cell_4_64_3
  | exact S 4 64 4 cell_4_64_4
  | exact S 4 64 5 cell_4_64_5
theorem cell_4_65_0 : C 4 65 0 := by decide +kernel
theorem cell_4_65_1 : C 4 65 1 := by decide +kernel
theorem cell_4_65_2 : C 4 65 2 := by decide +kernel
theorem cell_4_65_3 : C 4 65 3 := by decide +kernel
theorem cell_4_65_4 : C 4 65 4 := by decide +kernel
theorem cell_4_65_5 : C 4 65 5 := by decide +kernel
theorem row_4_65 : ThresholdAt 4 65 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 65 0 cell_4_65_0
  | exact S 4 65 1 cell_4_65_1
  | exact S 4 65 2 cell_4_65_2
  | exact S 4 65 3 cell_4_65_3
  | exact S 4 65 4 cell_4_65_4
  | exact S 4 65 5 cell_4_65_5
theorem cell_4_66_0 : C 4 66 0 := by decide +kernel
theorem cell_4_66_1 : C 4 66 1 := by decide +kernel
theorem cell_4_66_2 : C 4 66 2 := by decide +kernel
theorem cell_4_66_3 : C 4 66 3 := by decide +kernel
theorem cell_4_66_4 : C 4 66 4 := by decide +kernel
theorem cell_4_66_5 : C 4 66 5 := by decide +kernel
theorem row_4_66 : ThresholdAt 4 66 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 66 0 cell_4_66_0
  | exact S 4 66 1 cell_4_66_1
  | exact S 4 66 2 cell_4_66_2
  | exact S 4 66 3 cell_4_66_3
  | exact S 4 66 4 cell_4_66_4
  | exact S 4 66 5 cell_4_66_5
theorem cell_4_67_0 : C 4 67 0 := by decide +kernel
theorem cell_4_67_1 : C 4 67 1 := by decide +kernel
theorem cell_4_67_2 : C 4 67 2 := by decide +kernel
theorem cell_4_67_3 : C 4 67 3 := by decide +kernel
theorem cell_4_67_4 : C 4 67 4 := by decide +kernel
theorem cell_4_67_5 : C 4 67 5 := by decide +kernel
theorem row_4_67 : ThresholdAt 4 67 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 67 0 cell_4_67_0
  | exact S 4 67 1 cell_4_67_1
  | exact S 4 67 2 cell_4_67_2
  | exact S 4 67 3 cell_4_67_3
  | exact S 4 67 4 cell_4_67_4
  | exact S 4 67 5 cell_4_67_5
theorem cell_4_68_0 : C 4 68 0 := by decide +kernel
theorem cell_4_68_1 : C 4 68 1 := by decide +kernel
theorem cell_4_68_2 : C 4 68 2 := by decide +kernel
theorem cell_4_68_3 : C 4 68 3 := by decide +kernel
theorem cell_4_68_4 : C 4 68 4 := by decide +kernel
theorem cell_4_68_5 : C 4 68 5 := by decide +kernel
theorem row_4_68 : ThresholdAt 4 68 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 68 0 cell_4_68_0
  | exact S 4 68 1 cell_4_68_1
  | exact S 4 68 2 cell_4_68_2
  | exact S 4 68 3 cell_4_68_3
  | exact S 4 68 4 cell_4_68_4
  | exact S 4 68 5 cell_4_68_5
theorem cell_4_69_0 : C 4 69 0 := by decide +kernel
theorem cell_4_69_1 : C 4 69 1 := by decide +kernel
theorem cell_4_69_2 : C 4 69 2 := by decide +kernel
theorem cell_4_69_3 : C 4 69 3 := by decide +kernel
theorem cell_4_69_4 : C 4 69 4 := by decide +kernel
theorem cell_4_69_5 : C 4 69 5 := by decide +kernel
theorem row_4_69 : ThresholdAt 4 69 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 69 0 cell_4_69_0
  | exact S 4 69 1 cell_4_69_1
  | exact S 4 69 2 cell_4_69_2
  | exact S 4 69 3 cell_4_69_3
  | exact S 4 69 4 cell_4_69_4
  | exact S 4 69 5 cell_4_69_5
theorem cell_4_70_0 : C 4 70 0 := by decide +kernel
theorem cell_4_70_1 : C 4 70 1 := by decide +kernel
theorem cell_4_70_2 : C 4 70 2 := by decide +kernel
theorem cell_4_70_3 : C 4 70 3 := by decide +kernel
theorem cell_4_70_4 : C 4 70 4 := by decide +kernel
theorem cell_4_70_5 : C 4 70 5 := by decide +kernel
theorem row_4_70 : ThresholdAt 4 70 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 70 0 cell_4_70_0
  | exact S 4 70 1 cell_4_70_1
  | exact S 4 70 2 cell_4_70_2
  | exact S 4 70 3 cell_4_70_3
  | exact S 4 70 4 cell_4_70_4
  | exact S 4 70 5 cell_4_70_5
theorem cell_4_71_0 : C 4 71 0 := by decide +kernel
theorem cell_4_71_1 : C 4 71 1 := by decide +kernel
theorem cell_4_71_2 : C 4 71 2 := by decide +kernel
theorem cell_4_71_3 : C 4 71 3 := by decide +kernel
theorem cell_4_71_4 : C 4 71 4 := by decide +kernel
theorem cell_4_71_5 : C 4 71 5 := by decide +kernel
theorem row_4_71 : ThresholdAt 4 71 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 71 0 cell_4_71_0
  | exact S 4 71 1 cell_4_71_1
  | exact S 4 71 2 cell_4_71_2
  | exact S 4 71 3 cell_4_71_3
  | exact S 4 71 4 cell_4_71_4
  | exact S 4 71 5 cell_4_71_5
theorem cell_4_72_0 : C 4 72 0 := by decide +kernel
theorem cell_4_72_1 : C 4 72 1 := by decide +kernel
theorem cell_4_72_2 : C 4 72 2 := by decide +kernel
theorem cell_4_72_3 : C 4 72 3 := by decide +kernel
theorem cell_4_72_4 : C 4 72 4 := by decide +kernel
theorem cell_4_72_5 : C 4 72 5 := by decide +kernel
theorem row_4_72 : ThresholdAt 4 72 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 72 0 cell_4_72_0
  | exact S 4 72 1 cell_4_72_1
  | exact S 4 72 2 cell_4_72_2
  | exact S 4 72 3 cell_4_72_3
  | exact S 4 72 4 cell_4_72_4
  | exact S 4 72 5 cell_4_72_5
theorem cell_4_73_0 : C 4 73 0 := by decide +kernel
theorem cell_4_73_1 : C 4 73 1 := by decide +kernel
theorem cell_4_73_2 : C 4 73 2 := by decide +kernel
theorem cell_4_73_3 : C 4 73 3 := by decide +kernel
theorem cell_4_73_4 : C 4 73 4 := by decide +kernel
theorem cell_4_73_5 : C 4 73 5 := by decide +kernel
theorem row_4_73 : ThresholdAt 4 73 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 73 0 cell_4_73_0
  | exact S 4 73 1 cell_4_73_1
  | exact S 4 73 2 cell_4_73_2
  | exact S 4 73 3 cell_4_73_3
  | exact S 4 73 4 cell_4_73_4
  | exact S 4 73 5 cell_4_73_5
theorem cell_4_74_0 : C 4 74 0 := by decide +kernel
theorem cell_4_74_1 : C 4 74 1 := by decide +kernel
theorem cell_4_74_2 : C 4 74 2 := by decide +kernel
theorem cell_4_74_3 : C 4 74 3 := by decide +kernel
theorem cell_4_74_4 : C 4 74 4 := by decide +kernel
theorem cell_4_74_5 : C 4 74 5 := by decide +kernel
theorem row_4_74 : ThresholdAt 4 74 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 74 0 cell_4_74_0
  | exact S 4 74 1 cell_4_74_1
  | exact S 4 74 2 cell_4_74_2
  | exact S 4 74 3 cell_4_74_3
  | exact S 4 74 4 cell_4_74_4
  | exact S 4 74 5 cell_4_74_5
theorem cell_4_75_0 : C 4 75 0 := by decide +kernel
theorem cell_4_75_1 : C 4 75 1 := by decide +kernel
theorem cell_4_75_2 : C 4 75 2 := by decide +kernel
theorem cell_4_75_3 : C 4 75 3 := by decide +kernel
theorem cell_4_75_4 : C 4 75 4 := by decide +kernel
theorem cell_4_75_5 : C 4 75 5 := by decide +kernel
theorem row_4_75 : ThresholdAt 4 75 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 75 0 cell_4_75_0
  | exact S 4 75 1 cell_4_75_1
  | exact S 4 75 2 cell_4_75_2
  | exact S 4 75 3 cell_4_75_3
  | exact S 4 75 4 cell_4_75_4
  | exact S 4 75 5 cell_4_75_5
theorem cell_4_76_0 : C 4 76 0 := by decide +kernel
theorem cell_4_76_1 : C 4 76 1 := by decide +kernel
theorem cell_4_76_2 : C 4 76 2 := by decide +kernel
theorem cell_4_76_3 : C 4 76 3 := by decide +kernel
theorem cell_4_76_4 : C 4 76 4 := by decide +kernel
theorem cell_4_76_5 : C 4 76 5 := by decide +kernel
theorem row_4_76 : ThresholdAt 4 76 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 76 0 cell_4_76_0
  | exact S 4 76 1 cell_4_76_1
  | exact S 4 76 2 cell_4_76_2
  | exact S 4 76 3 cell_4_76_3
  | exact S 4 76 4 cell_4_76_4
  | exact S 4 76 5 cell_4_76_5
theorem cell_4_77_0 : C 4 77 0 := by decide +kernel
theorem cell_4_77_1 : C 4 77 1 := by decide +kernel
theorem cell_4_77_2 : C 4 77 2 := by decide +kernel
theorem cell_4_77_3 : C 4 77 3 := by decide +kernel
theorem cell_4_77_4 : C 4 77 4 := by decide +kernel
theorem cell_4_77_5 : C 4 77 5 := by decide +kernel
theorem row_4_77 : ThresholdAt 4 77 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 77 0 cell_4_77_0
  | exact S 4 77 1 cell_4_77_1
  | exact S 4 77 2 cell_4_77_2
  | exact S 4 77 3 cell_4_77_3
  | exact S 4 77 4 cell_4_77_4
  | exact S 4 77 5 cell_4_77_5
theorem cell_4_78_0 : C 4 78 0 := by decide +kernel
theorem cell_4_78_1 : C 4 78 1 := by decide +kernel
theorem cell_4_78_2 : C 4 78 2 := by decide +kernel
theorem cell_4_78_3 : C 4 78 3 := by decide +kernel
theorem cell_4_78_4 : C 4 78 4 := by decide +kernel
theorem cell_4_78_5 : C 4 78 5 := by decide +kernel
theorem row_4_78 : ThresholdAt 4 78 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 78 0 cell_4_78_0
  | exact S 4 78 1 cell_4_78_1
  | exact S 4 78 2 cell_4_78_2
  | exact S 4 78 3 cell_4_78_3
  | exact S 4 78 4 cell_4_78_4
  | exact S 4 78 5 cell_4_78_5
theorem cell_4_79_0 : C 4 79 0 := by decide +kernel
theorem cell_4_79_1 : C 4 79 1 := by decide +kernel
theorem cell_4_79_2 : C 4 79 2 := by decide +kernel
theorem cell_4_79_3 : C 4 79 3 := by decide +kernel
theorem cell_4_79_4 : C 4 79 4 := by decide +kernel
theorem cell_4_79_5 : C 4 79 5 := by decide +kernel
theorem row_4_79 : ThresholdAt 4 79 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 79 0 cell_4_79_0
  | exact S 4 79 1 cell_4_79_1
  | exact S 4 79 2 cell_4_79_2
  | exact S 4 79 3 cell_4_79_3
  | exact S 4 79 4 cell_4_79_4
  | exact S 4 79 5 cell_4_79_5
theorem cell_4_80_0 : C 4 80 0 := by decide +kernel
theorem cell_4_80_1 : C 4 80 1 := by decide +kernel
theorem cell_4_80_2 : C 4 80 2 := by decide +kernel
theorem cell_4_80_3 : C 4 80 3 := by decide +kernel
theorem cell_4_80_4 : C 4 80 4 := by decide +kernel
theorem cell_4_80_5 : C 4 80 5 := by decide +kernel
theorem row_4_80 : ThresholdAt 4 80 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 80 0 cell_4_80_0
  | exact S 4 80 1 cell_4_80_1
  | exact S 4 80 2 cell_4_80_2
  | exact S 4 80 3 cell_4_80_3
  | exact S 4 80 4 cell_4_80_4
  | exact S 4 80 5 cell_4_80_5
theorem cell_4_81_0 : C 4 81 0 := by decide +kernel
theorem cell_4_81_1 : C 4 81 1 := by decide +kernel
theorem cell_4_81_2 : C 4 81 2 := by decide +kernel
theorem cell_4_81_3 : C 4 81 3 := by decide +kernel
theorem cell_4_81_4 : C 4 81 4 := by decide +kernel
theorem cell_4_81_5 : C 4 81 5 := by decide +kernel
theorem row_4_81 : ThresholdAt 4 81 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 81 0 cell_4_81_0
  | exact S 4 81 1 cell_4_81_1
  | exact S 4 81 2 cell_4_81_2
  | exact S 4 81 3 cell_4_81_3
  | exact S 4 81 4 cell_4_81_4
  | exact S 4 81 5 cell_4_81_5
theorem cell_4_82_0 : C 4 82 0 := by decide +kernel
theorem cell_4_82_1 : C 4 82 1 := by decide +kernel
theorem cell_4_82_2 : C 4 82 2 := by decide +kernel
theorem cell_4_82_3 : C 4 82 3 := by decide +kernel
theorem cell_4_82_4 : C 4 82 4 := by decide +kernel
theorem cell_4_82_5 : C 4 82 5 := by decide +kernel
theorem row_4_82 : ThresholdAt 4 82 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 82 0 cell_4_82_0
  | exact S 4 82 1 cell_4_82_1
  | exact S 4 82 2 cell_4_82_2
  | exact S 4 82 3 cell_4_82_3
  | exact S 4 82 4 cell_4_82_4
  | exact S 4 82 5 cell_4_82_5
theorem cell_4_83_0 : C 4 83 0 := by decide +kernel
theorem cell_4_83_1 : C 4 83 1 := by decide +kernel
theorem cell_4_83_2 : C 4 83 2 := by decide +kernel
theorem cell_4_83_3 : C 4 83 3 := by decide +kernel
theorem cell_4_83_4 : C 4 83 4 := by decide +kernel
theorem cell_4_83_5 : C 4 83 5 := by decide +kernel
theorem row_4_83 : ThresholdAt 4 83 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 83 0 cell_4_83_0
  | exact S 4 83 1 cell_4_83_1
  | exact S 4 83 2 cell_4_83_2
  | exact S 4 83 3 cell_4_83_3
  | exact S 4 83 4 cell_4_83_4
  | exact S 4 83 5 cell_4_83_5
theorem cell_4_84_0 : C 4 84 0 := by decide +kernel
theorem cell_4_84_1 : C 4 84 1 := by decide +kernel
theorem cell_4_84_2 : C 4 84 2 := by decide +kernel
theorem cell_4_84_3 : C 4 84 3 := by decide +kernel
theorem cell_4_84_4 : C 4 84 4 := by decide +kernel
theorem cell_4_84_5 : C 4 84 5 := by decide +kernel
theorem row_4_84 : ThresholdAt 4 84 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 84 0 cell_4_84_0
  | exact S 4 84 1 cell_4_84_1
  | exact S 4 84 2 cell_4_84_2
  | exact S 4 84 3 cell_4_84_3
  | exact S 4 84 4 cell_4_84_4
  | exact S 4 84 5 cell_4_84_5
theorem cell_4_85_0 : C 4 85 0 := by decide +kernel
theorem cell_4_85_1 : C 4 85 1 := by decide +kernel
theorem cell_4_85_2 : C 4 85 2 := by decide +kernel
theorem cell_4_85_3 : C 4 85 3 := by decide +kernel
theorem cell_4_85_4 : C 4 85 4 := by decide +kernel
theorem cell_4_85_5 : C 4 85 5 := by decide +kernel
theorem row_4_85 : ThresholdAt 4 85 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 85 0 cell_4_85_0
  | exact S 4 85 1 cell_4_85_1
  | exact S 4 85 2 cell_4_85_2
  | exact S 4 85 3 cell_4_85_3
  | exact S 4 85 4 cell_4_85_4
  | exact S 4 85 5 cell_4_85_5
theorem cell_4_86_0 : C 4 86 0 := by decide +kernel
theorem cell_4_86_1 : C 4 86 1 := by decide +kernel
theorem cell_4_86_2 : C 4 86 2 := by decide +kernel
theorem cell_4_86_3 : C 4 86 3 := by decide +kernel
theorem cell_4_86_4 : C 4 86 4 := by decide +kernel
theorem cell_4_86_5 : C 4 86 5 := by decide +kernel
theorem row_4_86 : ThresholdAt 4 86 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 86 0 cell_4_86_0
  | exact S 4 86 1 cell_4_86_1
  | exact S 4 86 2 cell_4_86_2
  | exact S 4 86 3 cell_4_86_3
  | exact S 4 86 4 cell_4_86_4
  | exact S 4 86 5 cell_4_86_5
theorem cell_4_87_0 : C 4 87 0 := by decide +kernel
theorem cell_4_87_1 : C 4 87 1 := by decide +kernel
theorem cell_4_87_2 : C 4 87 2 := by decide +kernel
theorem cell_4_87_3 : C 4 87 3 := by decide +kernel
theorem cell_4_87_4 : C 4 87 4 := by decide +kernel
theorem cell_4_87_5 : C 4 87 5 := by decide +kernel
theorem row_4_87 : ThresholdAt 4 87 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 87 0 cell_4_87_0
  | exact S 4 87 1 cell_4_87_1
  | exact S 4 87 2 cell_4_87_2
  | exact S 4 87 3 cell_4_87_3
  | exact S 4 87 4 cell_4_87_4
  | exact S 4 87 5 cell_4_87_5
theorem cell_4_88_0 : C 4 88 0 := by decide +kernel
theorem cell_4_88_1 : C 4 88 1 := by decide +kernel
theorem cell_4_88_2 : C 4 88 2 := by decide +kernel
theorem cell_4_88_3 : C 4 88 3 := by decide +kernel
theorem cell_4_88_4 : C 4 88 4 := by decide +kernel
theorem cell_4_88_5 : C 4 88 5 := by decide +kernel
theorem row_4_88 : ThresholdAt 4 88 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 88 0 cell_4_88_0
  | exact S 4 88 1 cell_4_88_1
  | exact S 4 88 2 cell_4_88_2
  | exact S 4 88 3 cell_4_88_3
  | exact S 4 88 4 cell_4_88_4
  | exact S 4 88 5 cell_4_88_5
theorem cell_4_89_0 : C 4 89 0 := by decide +kernel
theorem cell_4_89_1 : C 4 89 1 := by decide +kernel
theorem cell_4_89_2 : C 4 89 2 := by decide +kernel
theorem cell_4_89_3 : C 4 89 3 := by decide +kernel
theorem cell_4_89_4 : C 4 89 4 := by decide +kernel
theorem cell_4_89_5 : C 4 89 5 := by decide +kernel
theorem row_4_89 : ThresholdAt 4 89 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 89 0 cell_4_89_0
  | exact S 4 89 1 cell_4_89_1
  | exact S 4 89 2 cell_4_89_2
  | exact S 4 89 3 cell_4_89_3
  | exact S 4 89 4 cell_4_89_4
  | exact S 4 89 5 cell_4_89_5
theorem cell_4_90_0 : C 4 90 0 := by decide +kernel
theorem cell_4_90_1 : C 4 90 1 := by decide +kernel
theorem cell_4_90_2 : C 4 90 2 := by decide +kernel
theorem cell_4_90_3 : C 4 90 3 := by decide +kernel
theorem cell_4_90_4 : C 4 90 4 := by decide +kernel
theorem cell_4_90_5 : C 4 90 5 := by decide +kernel
theorem row_4_90 : ThresholdAt 4 90 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 90 0 cell_4_90_0
  | exact S 4 90 1 cell_4_90_1
  | exact S 4 90 2 cell_4_90_2
  | exact S 4 90 3 cell_4_90_3
  | exact S 4 90 4 cell_4_90_4
  | exact S 4 90 5 cell_4_90_5
theorem cell_4_91_0 : C 4 91 0 := by decide +kernel
theorem cell_4_91_1 : C 4 91 1 := by decide +kernel
theorem cell_4_91_2 : C 4 91 2 := by decide +kernel
theorem cell_4_91_3 : C 4 91 3 := by decide +kernel
theorem cell_4_91_4 : C 4 91 4 := by decide +kernel
theorem cell_4_91_5 : C 4 91 5 := by decide +kernel
theorem row_4_91 : ThresholdAt 4 91 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 91 0 cell_4_91_0
  | exact S 4 91 1 cell_4_91_1
  | exact S 4 91 2 cell_4_91_2
  | exact S 4 91 3 cell_4_91_3
  | exact S 4 91 4 cell_4_91_4
  | exact S 4 91 5 cell_4_91_5
theorem cell_4_92_0 : C 4 92 0 := by decide +kernel
theorem cell_4_92_1 : C 4 92 1 := by decide +kernel
theorem cell_4_92_2 : C 4 92 2 := by decide +kernel
theorem cell_4_92_3 : C 4 92 3 := by decide +kernel
theorem cell_4_92_4 : C 4 92 4 := by decide +kernel
theorem cell_4_92_5 : C 4 92 5 := by decide +kernel
theorem row_4_92 : ThresholdAt 4 92 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 92 0 cell_4_92_0
  | exact S 4 92 1 cell_4_92_1
  | exact S 4 92 2 cell_4_92_2
  | exact S 4 92 3 cell_4_92_3
  | exact S 4 92 4 cell_4_92_4
  | exact S 4 92 5 cell_4_92_5
theorem cell_4_93_0 : C 4 93 0 := by decide +kernel
theorem cell_4_93_1 : C 4 93 1 := by decide +kernel
theorem cell_4_93_2 : C 4 93 2 := by decide +kernel
theorem cell_4_93_3 : C 4 93 3 := by decide +kernel
theorem cell_4_93_4 : C 4 93 4 := by decide +kernel
theorem cell_4_93_5 : C 4 93 5 := by decide +kernel
theorem row_4_93 : ThresholdAt 4 93 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 93 0 cell_4_93_0
  | exact S 4 93 1 cell_4_93_1
  | exact S 4 93 2 cell_4_93_2
  | exact S 4 93 3 cell_4_93_3
  | exact S 4 93 4 cell_4_93_4
  | exact S 4 93 5 cell_4_93_5
theorem cell_4_94_0 : C 4 94 0 := by decide +kernel
theorem cell_4_94_1 : C 4 94 1 := by decide +kernel
theorem cell_4_94_2 : C 4 94 2 := by decide +kernel
theorem cell_4_94_3 : C 4 94 3 := by decide +kernel
theorem cell_4_94_4 : C 4 94 4 := by decide +kernel
theorem cell_4_94_5 : C 4 94 5 := by decide +kernel
theorem row_4_94 : ThresholdAt 4 94 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 94 0 cell_4_94_0
  | exact S 4 94 1 cell_4_94_1
  | exact S 4 94 2 cell_4_94_2
  | exact S 4 94 3 cell_4_94_3
  | exact S 4 94 4 cell_4_94_4
  | exact S 4 94 5 cell_4_94_5
theorem cell_4_95_0 : C 4 95 0 := by decide +kernel
theorem cell_4_95_1 : C 4 95 1 := by decide +kernel
theorem cell_4_95_2 : C 4 95 2 := by decide +kernel
theorem cell_4_95_3 : C 4 95 3 := by decide +kernel
theorem cell_4_95_4 : C 4 95 4 := by decide +kernel
theorem cell_4_95_5 : C 4 95 5 := by decide +kernel
theorem row_4_95 : ThresholdAt 4 95 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 95 0 cell_4_95_0
  | exact S 4 95 1 cell_4_95_1
  | exact S 4 95 2 cell_4_95_2
  | exact S 4 95 3 cell_4_95_3
  | exact S 4 95 4 cell_4_95_4
  | exact S 4 95 5 cell_4_95_5
theorem cell_4_96_0 : C 4 96 0 := by decide +kernel
theorem cell_4_96_1 : C 4 96 1 := by decide +kernel
theorem cell_4_96_2 : C 4 96 2 := by decide +kernel
theorem cell_4_96_3 : C 4 96 3 := by decide +kernel
theorem cell_4_96_4 : C 4 96 4 := by decide +kernel
theorem cell_4_96_5 : C 4 96 5 := by decide +kernel
theorem row_4_96 : ThresholdAt 4 96 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 96 0 cell_4_96_0
  | exact S 4 96 1 cell_4_96_1
  | exact S 4 96 2 cell_4_96_2
  | exact S 4 96 3 cell_4_96_3
  | exact S 4 96 4 cell_4_96_4
  | exact S 4 96 5 cell_4_96_5
theorem cell_4_97_0 : C 4 97 0 := by decide +kernel
theorem cell_4_97_1 : C 4 97 1 := by decide +kernel
theorem cell_4_97_2 : C 4 97 2 := by decide +kernel
theorem cell_4_97_3 : C 4 97 3 := by decide +kernel
theorem cell_4_97_4 : C 4 97 4 := by decide +kernel
theorem cell_4_97_5 : C 4 97 5 := by decide +kernel
theorem row_4_97 : ThresholdAt 4 97 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 97 0 cell_4_97_0
  | exact S 4 97 1 cell_4_97_1
  | exact S 4 97 2 cell_4_97_2
  | exact S 4 97 3 cell_4_97_3
  | exact S 4 97 4 cell_4_97_4
  | exact S 4 97 5 cell_4_97_5
theorem cell_4_98_0 : C 4 98 0 := by decide +kernel
theorem cell_4_98_1 : C 4 98 1 := by decide +kernel
theorem cell_4_98_2 : C 4 98 2 := by decide +kernel
theorem cell_4_98_3 : C 4 98 3 := by decide +kernel
theorem cell_4_98_4 : C 4 98 4 := by decide +kernel
theorem cell_4_98_5 : C 4 98 5 := by decide +kernel
theorem row_4_98 : ThresholdAt 4 98 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 98 0 cell_4_98_0
  | exact S 4 98 1 cell_4_98_1
  | exact S 4 98 2 cell_4_98_2
  | exact S 4 98 3 cell_4_98_3
  | exact S 4 98 4 cell_4_98_4
  | exact S 4 98 5 cell_4_98_5
theorem cell_4_99_0 : C 4 99 0 := by decide +kernel
theorem cell_4_99_1 : C 4 99 1 := by decide +kernel
theorem cell_4_99_2 : C 4 99 2 := by decide +kernel
theorem cell_4_99_3 : C 4 99 3 := by decide +kernel
theorem cell_4_99_4 : C 4 99 4 := by decide +kernel
theorem cell_4_99_5 : C 4 99 5 := by decide +kernel
theorem row_4_99 : ThresholdAt 4 99 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 99 0 cell_4_99_0
  | exact S 4 99 1 cell_4_99_1
  | exact S 4 99 2 cell_4_99_2
  | exact S 4 99 3 cell_4_99_3
  | exact S 4 99 4 cell_4_99_4
  | exact S 4 99 5 cell_4_99_5
theorem cell_4_100_0 : C 4 100 0 := by decide +kernel
theorem cell_4_100_1 : C 4 100 1 := by decide +kernel
theorem cell_4_100_2 : C 4 100 2 := by decide +kernel
theorem cell_4_100_3 : C 4 100 3 := by decide +kernel
theorem cell_4_100_4 : C 4 100 4 := by decide +kernel
theorem cell_4_100_5 : C 4 100 5 := by decide +kernel
theorem row_4_100 : ThresholdAt 4 100 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 100 0 cell_4_100_0
  | exact S 4 100 1 cell_4_100_1
  | exact S 4 100 2 cell_4_100_2
  | exact S 4 100 3 cell_4_100_3
  | exact S 4 100 4 cell_4_100_4
  | exact S 4 100 5 cell_4_100_5
theorem cell_4_101_0 : C 4 101 0 := by decide +kernel
theorem cell_4_101_1 : C 4 101 1 := by decide +kernel
theorem cell_4_101_2 : C 4 101 2 := by decide +kernel
theorem cell_4_101_3 : C 4 101 3 := by decide +kernel
theorem cell_4_101_4 : C 4 101 4 := by decide +kernel
theorem cell_4_101_5 : C 4 101 5 := by decide +kernel
theorem row_4_101 : ThresholdAt 4 101 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 101 0 cell_4_101_0
  | exact S 4 101 1 cell_4_101_1
  | exact S 4 101 2 cell_4_101_2
  | exact S 4 101 3 cell_4_101_3
  | exact S 4 101 4 cell_4_101_4
  | exact S 4 101 5 cell_4_101_5
theorem cell_4_102_0 : C 4 102 0 := by decide +kernel
theorem cell_4_102_1 : C 4 102 1 := by decide +kernel
theorem cell_4_102_2 : C 4 102 2 := by decide +kernel
theorem cell_4_102_3 : C 4 102 3 := by decide +kernel
theorem cell_4_102_4 : C 4 102 4 := by decide +kernel
theorem cell_4_102_5 : C 4 102 5 := by decide +kernel
theorem row_4_102 : ThresholdAt 4 102 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 102 0 cell_4_102_0
  | exact S 4 102 1 cell_4_102_1
  | exact S 4 102 2 cell_4_102_2
  | exact S 4 102 3 cell_4_102_3
  | exact S 4 102 4 cell_4_102_4
  | exact S 4 102 5 cell_4_102_5
theorem cell_4_103_0 : C 4 103 0 := by decide +kernel
theorem cell_4_103_1 : C 4 103 1 := by decide +kernel
theorem cell_4_103_2 : C 4 103 2 := by decide +kernel
theorem cell_4_103_3 : C 4 103 3 := by decide +kernel
theorem cell_4_103_4 : C 4 103 4 := by decide +kernel
theorem cell_4_103_5 : C 4 103 5 := by decide +kernel
theorem row_4_103 : ThresholdAt 4 103 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 103 0 cell_4_103_0
  | exact S 4 103 1 cell_4_103_1
  | exact S 4 103 2 cell_4_103_2
  | exact S 4 103 3 cell_4_103_3
  | exact S 4 103 4 cell_4_103_4
  | exact S 4 103 5 cell_4_103_5
theorem cell_4_104_0 : C 4 104 0 := by decide +kernel
theorem cell_4_104_1 : C 4 104 1 := by decide +kernel
theorem cell_4_104_2 : C 4 104 2 := by decide +kernel
theorem cell_4_104_3 : C 4 104 3 := by decide +kernel
theorem cell_4_104_4 : C 4 104 4 := by decide +kernel
theorem cell_4_104_5 : C 4 104 5 := by decide +kernel
theorem row_4_104 : ThresholdAt 4 104 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 104 0 cell_4_104_0
  | exact S 4 104 1 cell_4_104_1
  | exact S 4 104 2 cell_4_104_2
  | exact S 4 104 3 cell_4_104_3
  | exact S 4 104 4 cell_4_104_4
  | exact S 4 104 5 cell_4_104_5
theorem cell_4_105_0 : C 4 105 0 := by decide +kernel
theorem cell_4_105_1 : C 4 105 1 := by decide +kernel
theorem cell_4_105_2 : C 4 105 2 := by decide +kernel
theorem cell_4_105_3 : C 4 105 3 := by decide +kernel
theorem cell_4_105_4 : C 4 105 4 := by decide +kernel
theorem cell_4_105_5 : C 4 105 5 := by decide +kernel
theorem row_4_105 : ThresholdAt 4 105 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 105 0 cell_4_105_0
  | exact S 4 105 1 cell_4_105_1
  | exact S 4 105 2 cell_4_105_2
  | exact S 4 105 3 cell_4_105_3
  | exact S 4 105 4 cell_4_105_4
  | exact S 4 105 5 cell_4_105_5
theorem cell_4_106_0 : C 4 106 0 := by decide +kernel
theorem cell_4_106_1 : C 4 106 1 := by decide +kernel
theorem cell_4_106_2 : C 4 106 2 := by decide +kernel
theorem cell_4_106_3 : C 4 106 3 := by decide +kernel
theorem cell_4_106_4 : C 4 106 4 := by decide +kernel
theorem cell_4_106_5 : C 4 106 5 := by decide +kernel
theorem row_4_106 : ThresholdAt 4 106 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 106 0 cell_4_106_0
  | exact S 4 106 1 cell_4_106_1
  | exact S 4 106 2 cell_4_106_2
  | exact S 4 106 3 cell_4_106_3
  | exact S 4 106 4 cell_4_106_4
  | exact S 4 106 5 cell_4_106_5
theorem cell_4_107_0 : C 4 107 0 := by decide +kernel
theorem cell_4_107_1 : C 4 107 1 := by decide +kernel
theorem cell_4_107_2 : C 4 107 2 := by decide +kernel
theorem cell_4_107_3 : C 4 107 3 := by decide +kernel
theorem cell_4_107_4 : C 4 107 4 := by decide +kernel
theorem cell_4_107_5 : C 4 107 5 := by decide +kernel
theorem row_4_107 : ThresholdAt 4 107 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 107 0 cell_4_107_0
  | exact S 4 107 1 cell_4_107_1
  | exact S 4 107 2 cell_4_107_2
  | exact S 4 107 3 cell_4_107_3
  | exact S 4 107 4 cell_4_107_4
  | exact S 4 107 5 cell_4_107_5
theorem cell_4_108_0 : C 4 108 0 := by decide +kernel
theorem cell_4_108_1 : C 4 108 1 := by decide +kernel
theorem cell_4_108_2 : C 4 108 2 := by decide +kernel
theorem cell_4_108_3 : C 4 108 3 := by decide +kernel
theorem cell_4_108_4 : C 4 108 4 := by decide +kernel
theorem cell_4_108_5 : C 4 108 5 := by decide +kernel
theorem row_4_108 : ThresholdAt 4 108 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 108 0 cell_4_108_0
  | exact S 4 108 1 cell_4_108_1
  | exact S 4 108 2 cell_4_108_2
  | exact S 4 108 3 cell_4_108_3
  | exact S 4 108 4 cell_4_108_4
  | exact S 4 108 5 cell_4_108_5
theorem cell_4_109_0 : C 4 109 0 := by decide +kernel
theorem cell_4_109_1 : C 4 109 1 := by decide +kernel
theorem cell_4_109_2 : C 4 109 2 := by decide +kernel
theorem cell_4_109_3 : C 4 109 3 := by decide +kernel
theorem cell_4_109_4 : C 4 109 4 := by decide +kernel
theorem cell_4_109_5 : C 4 109 5 := by decide +kernel
theorem row_4_109 : ThresholdAt 4 109 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 109 0 cell_4_109_0
  | exact S 4 109 1 cell_4_109_1
  | exact S 4 109 2 cell_4_109_2
  | exact S 4 109 3 cell_4_109_3
  | exact S 4 109 4 cell_4_109_4
  | exact S 4 109 5 cell_4_109_5
theorem cell_4_110_0 : C 4 110 0 := by decide +kernel
theorem cell_4_110_1 : C 4 110 1 := by decide +kernel
theorem cell_4_110_2 : C 4 110 2 := by decide +kernel
theorem cell_4_110_3 : C 4 110 3 := by decide +kernel
theorem cell_4_110_4 : C 4 110 4 := by decide +kernel
theorem cell_4_110_5 : C 4 110 5 := by decide +kernel
theorem row_4_110 : ThresholdAt 4 110 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 110 0 cell_4_110_0
  | exact S 4 110 1 cell_4_110_1
  | exact S 4 110 2 cell_4_110_2
  | exact S 4 110 3 cell_4_110_3
  | exact S 4 110 4 cell_4_110_4
  | exact S 4 110 5 cell_4_110_5
theorem cell_4_111_0 : C 4 111 0 := by decide +kernel
theorem cell_4_111_1 : C 4 111 1 := by decide +kernel
theorem cell_4_111_2 : C 4 111 2 := by decide +kernel
theorem cell_4_111_3 : C 4 111 3 := by decide +kernel
theorem cell_4_111_4 : C 4 111 4 := by decide +kernel
theorem cell_4_111_5 : C 4 111 5 := by decide +kernel
theorem row_4_111 : ThresholdAt 4 111 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 111 0 cell_4_111_0
  | exact S 4 111 1 cell_4_111_1
  | exact S 4 111 2 cell_4_111_2
  | exact S 4 111 3 cell_4_111_3
  | exact S 4 111 4 cell_4_111_4
  | exact S 4 111 5 cell_4_111_5
theorem cell_4_112_0 : C 4 112 0 := by decide +kernel
theorem cell_4_112_1 : C 4 112 1 := by decide +kernel
theorem cell_4_112_2 : C 4 112 2 := by decide +kernel
theorem cell_4_112_3 : C 4 112 3 := by decide +kernel
theorem cell_4_112_4 : C 4 112 4 := by decide +kernel
theorem cell_4_112_5 : C 4 112 5 := by decide +kernel
theorem row_4_112 : ThresholdAt 4 112 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 112 0 cell_4_112_0
  | exact S 4 112 1 cell_4_112_1
  | exact S 4 112 2 cell_4_112_2
  | exact S 4 112 3 cell_4_112_3
  | exact S 4 112 4 cell_4_112_4
  | exact S 4 112 5 cell_4_112_5
theorem cell_4_113_0 : C 4 113 0 := by decide +kernel
theorem cell_4_113_1 : C 4 113 1 := by decide +kernel
theorem cell_4_113_2 : C 4 113 2 := by decide +kernel
theorem cell_4_113_3 : C 4 113 3 := by decide +kernel
theorem cell_4_113_4 : C 4 113 4 := by decide +kernel
theorem cell_4_113_5 : C 4 113 5 := by decide +kernel
theorem row_4_113 : ThresholdAt 4 113 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 113 0 cell_4_113_0
  | exact S 4 113 1 cell_4_113_1
  | exact S 4 113 2 cell_4_113_2
  | exact S 4 113 3 cell_4_113_3
  | exact S 4 113 4 cell_4_113_4
  | exact S 4 113 5 cell_4_113_5
theorem cell_4_114_0 : C 4 114 0 := by decide +kernel
theorem cell_4_114_1 : C 4 114 1 := by decide +kernel
theorem cell_4_114_2 : C 4 114 2 := by decide +kernel
theorem cell_4_114_3 : C 4 114 3 := by decide +kernel
theorem cell_4_114_4 : C 4 114 4 := by decide +kernel
theorem cell_4_114_5 : C 4 114 5 := by decide +kernel
theorem row_4_114 : ThresholdAt 4 114 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 114 0 cell_4_114_0
  | exact S 4 114 1 cell_4_114_1
  | exact S 4 114 2 cell_4_114_2
  | exact S 4 114 3 cell_4_114_3
  | exact S 4 114 4 cell_4_114_4
  | exact S 4 114 5 cell_4_114_5
theorem cell_4_115_0 : C 4 115 0 := by decide +kernel
theorem cell_4_115_1 : C 4 115 1 := by decide +kernel
theorem cell_4_115_2 : C 4 115 2 := by decide +kernel
theorem cell_4_115_3 : C 4 115 3 := by decide +kernel
theorem cell_4_115_4 : C 4 115 4 := by decide +kernel
theorem cell_4_115_5 : C 4 115 5 := by decide +kernel
theorem row_4_115 : ThresholdAt 4 115 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 115 0 cell_4_115_0
  | exact S 4 115 1 cell_4_115_1
  | exact S 4 115 2 cell_4_115_2
  | exact S 4 115 3 cell_4_115_3
  | exact S 4 115 4 cell_4_115_4
  | exact S 4 115 5 cell_4_115_5
theorem cell_4_116_0 : C 4 116 0 := by decide +kernel
theorem cell_4_116_1 : C 4 116 1 := by decide +kernel
theorem cell_4_116_2 : C 4 116 2 := by decide +kernel
theorem cell_4_116_3 : C 4 116 3 := by decide +kernel
theorem cell_4_116_4 : C 4 116 4 := by decide +kernel
theorem cell_4_116_5 : C 4 116 5 := by decide +kernel
theorem row_4_116 : ThresholdAt 4 116 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 116 0 cell_4_116_0
  | exact S 4 116 1 cell_4_116_1
  | exact S 4 116 2 cell_4_116_2
  | exact S 4 116 3 cell_4_116_3
  | exact S 4 116 4 cell_4_116_4
  | exact S 4 116 5 cell_4_116_5
theorem cell_4_117_0 : C 4 117 0 := by decide +kernel
theorem cell_4_117_1 : C 4 117 1 := by decide +kernel
theorem cell_4_117_2 : C 4 117 2 := by decide +kernel
theorem cell_4_117_3 : C 4 117 3 := by decide +kernel
theorem cell_4_117_4 : C 4 117 4 := by decide +kernel
theorem cell_4_117_5 : C 4 117 5 := by decide +kernel
theorem row_4_117 : ThresholdAt 4 117 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 117 0 cell_4_117_0
  | exact S 4 117 1 cell_4_117_1
  | exact S 4 117 2 cell_4_117_2
  | exact S 4 117 3 cell_4_117_3
  | exact S 4 117 4 cell_4_117_4
  | exact S 4 117 5 cell_4_117_5
theorem cell_4_118_0 : C 4 118 0 := by decide +kernel
theorem cell_4_118_1 : C 4 118 1 := by decide +kernel
theorem cell_4_118_2 : C 4 118 2 := by decide +kernel
theorem cell_4_118_3 : C 4 118 3 := by decide +kernel
theorem cell_4_118_4 : C 4 118 4 := by decide +kernel
theorem cell_4_118_5 : C 4 118 5 := by decide +kernel
theorem row_4_118 : ThresholdAt 4 118 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 118 0 cell_4_118_0
  | exact S 4 118 1 cell_4_118_1
  | exact S 4 118 2 cell_4_118_2
  | exact S 4 118 3 cell_4_118_3
  | exact S 4 118 4 cell_4_118_4
  | exact S 4 118 5 cell_4_118_5
theorem cell_4_119_0 : C 4 119 0 := by decide +kernel
theorem cell_4_119_1 : C 4 119 1 := by decide +kernel
theorem cell_4_119_2 : C 4 119 2 := by decide +kernel
theorem cell_4_119_3 : C 4 119 3 := by decide +kernel
theorem cell_4_119_4 : C 4 119 4 := by decide +kernel
theorem cell_4_119_5 : C 4 119 5 := by decide +kernel
theorem row_4_119 : ThresholdAt 4 119 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 119 0 cell_4_119_0
  | exact S 4 119 1 cell_4_119_1
  | exact S 4 119 2 cell_4_119_2
  | exact S 4 119 3 cell_4_119_3
  | exact S 4 119 4 cell_4_119_4
  | exact S 4 119 5 cell_4_119_5
theorem cell_4_120_0 : C 4 120 0 := by decide +kernel
theorem cell_4_120_1 : C 4 120 1 := by decide +kernel
theorem cell_4_120_2 : C 4 120 2 := by decide +kernel
theorem cell_4_120_3 : C 4 120 3 := by decide +kernel
theorem cell_4_120_4 : C 4 120 4 := by decide +kernel
theorem cell_4_120_5 : C 4 120 5 := by decide +kernel
theorem row_4_120 : ThresholdAt 4 120 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 120 0 cell_4_120_0
  | exact S 4 120 1 cell_4_120_1
  | exact S 4 120 2 cell_4_120_2
  | exact S 4 120 3 cell_4_120_3
  | exact S 4 120 4 cell_4_120_4
  | exact S 4 120 5 cell_4_120_5
theorem cell_4_121_0 : C 4 121 0 := by decide +kernel
theorem cell_4_121_1 : C 4 121 1 := by decide +kernel
theorem cell_4_121_2 : C 4 121 2 := by decide +kernel
theorem cell_4_121_3 : C 4 121 3 := by decide +kernel
theorem cell_4_121_4 : C 4 121 4 := by decide +kernel
theorem cell_4_121_5 : C 4 121 5 := by decide +kernel
theorem row_4_121 : ThresholdAt 4 121 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 121 0 cell_4_121_0
  | exact S 4 121 1 cell_4_121_1
  | exact S 4 121 2 cell_4_121_2
  | exact S 4 121 3 cell_4_121_3
  | exact S 4 121 4 cell_4_121_4
  | exact S 4 121 5 cell_4_121_5
theorem cell_4_122_0 : C 4 122 0 := by decide +kernel
theorem cell_4_122_1 : C 4 122 1 := by decide +kernel
theorem cell_4_122_2 : C 4 122 2 := by decide +kernel
theorem cell_4_122_3 : C 4 122 3 := by decide +kernel
theorem cell_4_122_4 : C 4 122 4 := by decide +kernel
theorem cell_4_122_5 : C 4 122 5 := by decide +kernel
theorem row_4_122 : ThresholdAt 4 122 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 122 0 cell_4_122_0
  | exact S 4 122 1 cell_4_122_1
  | exact S 4 122 2 cell_4_122_2
  | exact S 4 122 3 cell_4_122_3
  | exact S 4 122 4 cell_4_122_4
  | exact S 4 122 5 cell_4_122_5
theorem cell_4_123_0 : C 4 123 0 := by decide +kernel
theorem cell_4_123_1 : C 4 123 1 := by decide +kernel
theorem cell_4_123_2 : C 4 123 2 := by decide +kernel
theorem cell_4_123_3 : C 4 123 3 := by decide +kernel
theorem cell_4_123_4 : C 4 123 4 := by decide +kernel
theorem cell_4_123_5 : C 4 123 5 := by decide +kernel
theorem row_4_123 : ThresholdAt 4 123 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 123 0 cell_4_123_0
  | exact S 4 123 1 cell_4_123_1
  | exact S 4 123 2 cell_4_123_2
  | exact S 4 123 3 cell_4_123_3
  | exact S 4 123 4 cell_4_123_4
  | exact S 4 123 5 cell_4_123_5
theorem cell_4_124_0 : C 4 124 0 := by decide +kernel
theorem cell_4_124_1 : C 4 124 1 := by decide +kernel
theorem cell_4_124_2 : C 4 124 2 := by decide +kernel
theorem cell_4_124_3 : C 4 124 3 := by decide +kernel
theorem cell_4_124_4 : C 4 124 4 := by decide +kernel
theorem cell_4_124_5 : C 4 124 5 := by decide +kernel
theorem row_4_124 : ThresholdAt 4 124 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 124 0 cell_4_124_0
  | exact S 4 124 1 cell_4_124_1
  | exact S 4 124 2 cell_4_124_2
  | exact S 4 124 3 cell_4_124_3
  | exact S 4 124 4 cell_4_124_4
  | exact S 4 124 5 cell_4_124_5
theorem cell_4_125_0 : C 4 125 0 := by decide +kernel
theorem cell_4_125_1 : C 4 125 1 := by decide +kernel
theorem cell_4_125_2 : C 4 125 2 := by decide +kernel
theorem cell_4_125_3 : C 4 125 3 := by decide +kernel
theorem cell_4_125_4 : C 4 125 4 := by decide +kernel
theorem cell_4_125_5 : C 4 125 5 := by decide +kernel
theorem row_4_125 : ThresholdAt 4 125 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 125 0 cell_4_125_0
  | exact S 4 125 1 cell_4_125_1
  | exact S 4 125 2 cell_4_125_2
  | exact S 4 125 3 cell_4_125_3
  | exact S 4 125 4 cell_4_125_4
  | exact S 4 125 5 cell_4_125_5
theorem cell_4_126_0 : C 4 126 0 := by decide +kernel
theorem cell_4_126_1 : C 4 126 1 := by decide +kernel
theorem cell_4_126_2 : C 4 126 2 := by decide +kernel
theorem cell_4_126_3 : C 4 126 3 := by decide +kernel
theorem cell_4_126_4 : C 4 126 4 := by decide +kernel
theorem cell_4_126_5 : C 4 126 5 := by decide +kernel
theorem row_4_126 : ThresholdAt 4 126 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 126 0 cell_4_126_0
  | exact S 4 126 1 cell_4_126_1
  | exact S 4 126 2 cell_4_126_2
  | exact S 4 126 3 cell_4_126_3
  | exact S 4 126 4 cell_4_126_4
  | exact S 4 126 5 cell_4_126_5
theorem cell_4_127_0 : C 4 127 0 := by decide +kernel
theorem cell_4_127_1 : C 4 127 1 := by decide +kernel
theorem cell_4_127_2 : C 4 127 2 := by decide +kernel
theorem cell_4_127_3 : C 4 127 3 := by decide +kernel
theorem cell_4_127_4 : C 4 127 4 := by decide +kernel
theorem cell_4_127_5 : C 4 127 5 := by decide +kernel
theorem row_4_127 : ThresholdAt 4 127 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 127 0 cell_4_127_0
  | exact S 4 127 1 cell_4_127_1
  | exact S 4 127 2 cell_4_127_2
  | exact S 4 127 3 cell_4_127_3
  | exact S 4 127 4 cell_4_127_4
  | exact S 4 127 5 cell_4_127_5
theorem cell_4_128_0 : C 4 128 0 := by decide +kernel
theorem cell_4_128_1 : C 4 128 1 := by decide +kernel
theorem cell_4_128_2 : C 4 128 2 := by decide +kernel
theorem cell_4_128_3 : C 4 128 3 := by decide +kernel
theorem cell_4_128_4 : C 4 128 4 := by decide +kernel
theorem cell_4_128_5 : C 4 128 5 := by decide +kernel
theorem row_4_128 : ThresholdAt 4 128 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 128 0 cell_4_128_0
  | exact S 4 128 1 cell_4_128_1
  | exact S 4 128 2 cell_4_128_2
  | exact S 4 128 3 cell_4_128_3
  | exact S 4 128 4 cell_4_128_4
  | exact S 4 128 5 cell_4_128_5
theorem cell_4_129_0 : C 4 129 0 := by decide +kernel
theorem cell_4_129_1 : C 4 129 1 := by decide +kernel
theorem cell_4_129_2 : C 4 129 2 := by decide +kernel
theorem cell_4_129_3 : C 4 129 3 := by decide +kernel
theorem cell_4_129_4 : C 4 129 4 := by decide +kernel
theorem cell_4_129_5 : C 4 129 5 := by decide +kernel
theorem row_4_129 : ThresholdAt 4 129 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 129 0 cell_4_129_0
  | exact S 4 129 1 cell_4_129_1
  | exact S 4 129 2 cell_4_129_2
  | exact S 4 129 3 cell_4_129_3
  | exact S 4 129 4 cell_4_129_4
  | exact S 4 129 5 cell_4_129_5
theorem cell_4_130_0 : C 4 130 0 := by decide +kernel
theorem cell_4_130_1 : C 4 130 1 := by decide +kernel
theorem cell_4_130_2 : C 4 130 2 := by decide +kernel
theorem cell_4_130_3 : C 4 130 3 := by decide +kernel
theorem cell_4_130_4 : C 4 130 4 := by decide +kernel
theorem cell_4_130_5 : C 4 130 5 := by decide +kernel
theorem row_4_130 : ThresholdAt 4 130 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 130 0 cell_4_130_0
  | exact S 4 130 1 cell_4_130_1
  | exact S 4 130 2 cell_4_130_2
  | exact S 4 130 3 cell_4_130_3
  | exact S 4 130 4 cell_4_130_4
  | exact S 4 130 5 cell_4_130_5
theorem cell_4_131_0 : C 4 131 0 := by decide +kernel
theorem cell_4_131_1 : C 4 131 1 := by decide +kernel
theorem cell_4_131_2 : C 4 131 2 := by decide +kernel
theorem cell_4_131_3 : C 4 131 3 := by decide +kernel
theorem cell_4_131_4 : C 4 131 4 := by decide +kernel
theorem cell_4_131_5 : C 4 131 5 := by decide +kernel
theorem row_4_131 : ThresholdAt 4 131 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 131 0 cell_4_131_0
  | exact S 4 131 1 cell_4_131_1
  | exact S 4 131 2 cell_4_131_2
  | exact S 4 131 3 cell_4_131_3
  | exact S 4 131 4 cell_4_131_4
  | exact S 4 131 5 cell_4_131_5
theorem cell_4_132_0 : C 4 132 0 := by decide +kernel
theorem cell_4_132_1 : C 4 132 1 := by decide +kernel
theorem cell_4_132_2 : C 4 132 2 := by decide +kernel
theorem cell_4_132_3 : C 4 132 3 := by decide +kernel
theorem cell_4_132_4 : C 4 132 4 := by decide +kernel
theorem cell_4_132_5 : C 4 132 5 := by decide +kernel
theorem row_4_132 : ThresholdAt 4 132 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 132 0 cell_4_132_0
  | exact S 4 132 1 cell_4_132_1
  | exact S 4 132 2 cell_4_132_2
  | exact S 4 132 3 cell_4_132_3
  | exact S 4 132 4 cell_4_132_4
  | exact S 4 132 5 cell_4_132_5
theorem cell_4_133_0 : C 4 133 0 := by decide +kernel
theorem cell_4_133_1 : C 4 133 1 := by decide +kernel
theorem cell_4_133_2 : C 4 133 2 := by decide +kernel
theorem cell_4_133_3 : C 4 133 3 := by decide +kernel
theorem cell_4_133_4 : C 4 133 4 := by decide +kernel
theorem cell_4_133_5 : C 4 133 5 := by decide +kernel
theorem row_4_133 : ThresholdAt 4 133 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 133 0 cell_4_133_0
  | exact S 4 133 1 cell_4_133_1
  | exact S 4 133 2 cell_4_133_2
  | exact S 4 133 3 cell_4_133_3
  | exact S 4 133 4 cell_4_133_4
  | exact S 4 133 5 cell_4_133_5
theorem cell_4_134_0 : C 4 134 0 := by decide +kernel
theorem cell_4_134_1 : C 4 134 1 := by decide +kernel
theorem cell_4_134_2 : C 4 134 2 := by decide +kernel
theorem cell_4_134_3 : C 4 134 3 := by decide +kernel
theorem cell_4_134_4 : C 4 134 4 := by decide +kernel
theorem cell_4_134_5 : C 4 134 5 := by decide +kernel
theorem row_4_134 : ThresholdAt 4 134 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 134 0 cell_4_134_0
  | exact S 4 134 1 cell_4_134_1
  | exact S 4 134 2 cell_4_134_2
  | exact S 4 134 3 cell_4_134_3
  | exact S 4 134 4 cell_4_134_4
  | exact S 4 134 5 cell_4_134_5
theorem cell_4_135_0 : C 4 135 0 := by decide +kernel
theorem cell_4_135_1 : C 4 135 1 := by decide +kernel
theorem cell_4_135_2 : C 4 135 2 := by decide +kernel
theorem cell_4_135_3 : C 4 135 3 := by decide +kernel
theorem cell_4_135_4 : C 4 135 4 := by decide +kernel
theorem cell_4_135_5 : C 4 135 5 := by decide +kernel
theorem row_4_135 : ThresholdAt 4 135 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 4 135 0 cell_4_135_0
  | exact S 4 135 1 cell_4_135_1
  | exact S 4 135 2 cell_4_135_2
  | exact S 4 135 3 cell_4_135_3
  | exact S 4 135 4 cell_4_135_4
  | exact S 4 135 5 cell_4_135_5
theorem checkedR4 : ∀ V ∈ List.range 136, ThresholdAt 4 V := by
  intro V hV
  have hv : V < 136 := List.mem_range.mp hV
  by_cases h0_136 : V < 68
  · by_cases h0_68 : V < 34
    · by_cases h0_34 : V < 17
      · by_cases h0_17 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have he : V = 0 := by omega
                subst V
                exact row_4_0
              · have he : V = 1 := by omega
                subst V
                exact row_4_1
            · by_cases h2_4 : V < 3
              · have he : V = 2 := by omega
                subst V
                exact row_4_2
              · have he : V = 3 := by omega
                subst V
                exact row_4_3
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have he : V = 4 := by omega
                subst V
                exact row_4_4
              · have he : V = 5 := by omega
                subst V
                exact row_4_5
            · by_cases h6_8 : V < 7
              · have he : V = 6 := by omega
                subst V
                exact row_4_6
              · have he : V = 7 := by omega
                subst V
                exact row_4_7
        · by_cases h8_17 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have he : V = 8 := by omega
                subst V
                exact row_4_8
              · have he : V = 9 := by omega
                subst V
                exact row_4_9
            · by_cases h10_12 : V < 11
              · have he : V = 10 := by omega
                subst V
                exact row_4_10
              · have he : V = 11 := by omega
                subst V
                exact row_4_11
          · by_cases h12_17 : V < 14
            · by_cases h12_14 : V < 13
              · have he : V = 12 := by omega
                subst V
                exact row_4_12
              · have he : V = 13 := by omega
                subst V
                exact row_4_13
            · by_cases h14_17 : V < 15
              · have he : V = 14 := by omega
                subst V
                exact row_4_14
              · by_cases h15_17 : V < 16
                · have he : V = 15 := by omega
                  subst V
                  exact row_4_15
                · have he : V = 16 := by omega
                  subst V
                  exact row_4_16
      · by_cases h17_34 : V < 25
        · by_cases h17_25 : V < 21
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have he : V = 17 := by omega
                subst V
                exact row_4_17
              · have he : V = 18 := by omega
                subst V
                exact row_4_18
            · by_cases h19_21 : V < 20
              · have he : V = 19 := by omega
                subst V
                exact row_4_19
              · have he : V = 20 := by omega
                subst V
                exact row_4_20
          · by_cases h21_25 : V < 23
            · by_cases h21_23 : V < 22
              · have he : V = 21 := by omega
                subst V
                exact row_4_21
              · have he : V = 22 := by omega
                subst V
                exact row_4_22
            · by_cases h23_25 : V < 24
              · have he : V = 23 := by omega
                subst V
                exact row_4_23
              · have he : V = 24 := by omega
                subst V
                exact row_4_24
        · by_cases h25_34 : V < 29
          · by_cases h25_29 : V < 27
            · by_cases h25_27 : V < 26
              · have he : V = 25 := by omega
                subst V
                exact row_4_25
              · have he : V = 26 := by omega
                subst V
                exact row_4_26
            · by_cases h27_29 : V < 28
              · have he : V = 27 := by omega
                subst V
                exact row_4_27
              · have he : V = 28 := by omega
                subst V
                exact row_4_28
          · by_cases h29_34 : V < 31
            · by_cases h29_31 : V < 30
              · have he : V = 29 := by omega
                subst V
                exact row_4_29
              · have he : V = 30 := by omega
                subst V
                exact row_4_30
            · by_cases h31_34 : V < 32
              · have he : V = 31 := by omega
                subst V
                exact row_4_31
              · by_cases h32_34 : V < 33
                · have he : V = 32 := by omega
                  subst V
                  exact row_4_32
                · have he : V = 33 := by omega
                  subst V
                  exact row_4_33
    · by_cases h34_68 : V < 51
      · by_cases h34_51 : V < 42
        · by_cases h34_42 : V < 38
          · by_cases h34_38 : V < 36
            · by_cases h34_36 : V < 35
              · have he : V = 34 := by omega
                subst V
                exact row_4_34
              · have he : V = 35 := by omega
                subst V
                exact row_4_35
            · by_cases h36_38 : V < 37
              · have he : V = 36 := by omega
                subst V
                exact row_4_36
              · have he : V = 37 := by omega
                subst V
                exact row_4_37
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have he : V = 38 := by omega
                subst V
                exact row_4_38
              · have he : V = 39 := by omega
                subst V
                exact row_4_39
            · by_cases h40_42 : V < 41
              · have he : V = 40 := by omega
                subst V
                exact row_4_40
              · have he : V = 41 := by omega
                subst V
                exact row_4_41
        · by_cases h42_51 : V < 46
          · by_cases h42_46 : V < 44
            · by_cases h42_44 : V < 43
              · have he : V = 42 := by omega
                subst V
                exact row_4_42
              · have he : V = 43 := by omega
                subst V
                exact row_4_43
            · by_cases h44_46 : V < 45
              · have he : V = 44 := by omega
                subst V
                exact row_4_44
              · have he : V = 45 := by omega
                subst V
                exact row_4_45
          · by_cases h46_51 : V < 48
            · by_cases h46_48 : V < 47
              · have he : V = 46 := by omega
                subst V
                exact row_4_46
              · have he : V = 47 := by omega
                subst V
                exact row_4_47
            · by_cases h48_51 : V < 49
              · have he : V = 48 := by omega
                subst V
                exact row_4_48
              · by_cases h49_51 : V < 50
                · have he : V = 49 := by omega
                  subst V
                  exact row_4_49
                · have he : V = 50 := by omega
                  subst V
                  exact row_4_50
      · by_cases h51_68 : V < 59
        · by_cases h51_59 : V < 55
          · by_cases h51_55 : V < 53
            · by_cases h51_53 : V < 52
              · have he : V = 51 := by omega
                subst V
                exact row_4_51
              · have he : V = 52 := by omega
                subst V
                exact row_4_52
            · by_cases h53_55 : V < 54
              · have he : V = 53 := by omega
                subst V
                exact row_4_53
              · have he : V = 54 := by omega
                subst V
                exact row_4_54
          · by_cases h55_59 : V < 57
            · by_cases h55_57 : V < 56
              · have he : V = 55 := by omega
                subst V
                exact row_4_55
              · have he : V = 56 := by omega
                subst V
                exact row_4_56
            · by_cases h57_59 : V < 58
              · have he : V = 57 := by omega
                subst V
                exact row_4_57
              · have he : V = 58 := by omega
                subst V
                exact row_4_58
        · by_cases h59_68 : V < 63
          · by_cases h59_63 : V < 61
            · by_cases h59_61 : V < 60
              · have he : V = 59 := by omega
                subst V
                exact row_4_59
              · have he : V = 60 := by omega
                subst V
                exact row_4_60
            · by_cases h61_63 : V < 62
              · have he : V = 61 := by omega
                subst V
                exact row_4_61
              · have he : V = 62 := by omega
                subst V
                exact row_4_62
          · by_cases h63_68 : V < 65
            · by_cases h63_65 : V < 64
              · have he : V = 63 := by omega
                subst V
                exact row_4_63
              · have he : V = 64 := by omega
                subst V
                exact row_4_64
            · by_cases h65_68 : V < 66
              · have he : V = 65 := by omega
                subst V
                exact row_4_65
              · by_cases h66_68 : V < 67
                · have he : V = 66 := by omega
                  subst V
                  exact row_4_66
                · have he : V = 67 := by omega
                  subst V
                  exact row_4_67
  · by_cases h68_136 : V < 102
    · by_cases h68_102 : V < 85
      · by_cases h68_85 : V < 76
        · by_cases h68_76 : V < 72
          · by_cases h68_72 : V < 70
            · by_cases h68_70 : V < 69
              · have he : V = 68 := by omega
                subst V
                exact row_4_68
              · have he : V = 69 := by omega
                subst V
                exact row_4_69
            · by_cases h70_72 : V < 71
              · have he : V = 70 := by omega
                subst V
                exact row_4_70
              · have he : V = 71 := by omega
                subst V
                exact row_4_71
          · by_cases h72_76 : V < 74
            · by_cases h72_74 : V < 73
              · have he : V = 72 := by omega
                subst V
                exact row_4_72
              · have he : V = 73 := by omega
                subst V
                exact row_4_73
            · by_cases h74_76 : V < 75
              · have he : V = 74 := by omega
                subst V
                exact row_4_74
              · have he : V = 75 := by omega
                subst V
                exact row_4_75
        · by_cases h76_85 : V < 80
          · by_cases h76_80 : V < 78
            · by_cases h76_78 : V < 77
              · have he : V = 76 := by omega
                subst V
                exact row_4_76
              · have he : V = 77 := by omega
                subst V
                exact row_4_77
            · by_cases h78_80 : V < 79
              · have he : V = 78 := by omega
                subst V
                exact row_4_78
              · have he : V = 79 := by omega
                subst V
                exact row_4_79
          · by_cases h80_85 : V < 82
            · by_cases h80_82 : V < 81
              · have he : V = 80 := by omega
                subst V
                exact row_4_80
              · have he : V = 81 := by omega
                subst V
                exact row_4_81
            · by_cases h82_85 : V < 83
              · have he : V = 82 := by omega
                subst V
                exact row_4_82
              · by_cases h83_85 : V < 84
                · have he : V = 83 := by omega
                  subst V
                  exact row_4_83
                · have he : V = 84 := by omega
                  subst V
                  exact row_4_84
      · by_cases h85_102 : V < 93
        · by_cases h85_93 : V < 89
          · by_cases h85_89 : V < 87
            · by_cases h85_87 : V < 86
              · have he : V = 85 := by omega
                subst V
                exact row_4_85
              · have he : V = 86 := by omega
                subst V
                exact row_4_86
            · by_cases h87_89 : V < 88
              · have he : V = 87 := by omega
                subst V
                exact row_4_87
              · have he : V = 88 := by omega
                subst V
                exact row_4_88
          · by_cases h89_93 : V < 91
            · by_cases h89_91 : V < 90
              · have he : V = 89 := by omega
                subst V
                exact row_4_89
              · have he : V = 90 := by omega
                subst V
                exact row_4_90
            · by_cases h91_93 : V < 92
              · have he : V = 91 := by omega
                subst V
                exact row_4_91
              · have he : V = 92 := by omega
                subst V
                exact row_4_92
        · by_cases h93_102 : V < 97
          · by_cases h93_97 : V < 95
            · by_cases h93_95 : V < 94
              · have he : V = 93 := by omega
                subst V
                exact row_4_93
              · have he : V = 94 := by omega
                subst V
                exact row_4_94
            · by_cases h95_97 : V < 96
              · have he : V = 95 := by omega
                subst V
                exact row_4_95
              · have he : V = 96 := by omega
                subst V
                exact row_4_96
          · by_cases h97_102 : V < 99
            · by_cases h97_99 : V < 98
              · have he : V = 97 := by omega
                subst V
                exact row_4_97
              · have he : V = 98 := by omega
                subst V
                exact row_4_98
            · by_cases h99_102 : V < 100
              · have he : V = 99 := by omega
                subst V
                exact row_4_99
              · by_cases h100_102 : V < 101
                · have he : V = 100 := by omega
                  subst V
                  exact row_4_100
                · have he : V = 101 := by omega
                  subst V
                  exact row_4_101
    · by_cases h102_136 : V < 119
      · by_cases h102_119 : V < 110
        · by_cases h102_110 : V < 106
          · by_cases h102_106 : V < 104
            · by_cases h102_104 : V < 103
              · have he : V = 102 := by omega
                subst V
                exact row_4_102
              · have he : V = 103 := by omega
                subst V
                exact row_4_103
            · by_cases h104_106 : V < 105
              · have he : V = 104 := by omega
                subst V
                exact row_4_104
              · have he : V = 105 := by omega
                subst V
                exact row_4_105
          · by_cases h106_110 : V < 108
            · by_cases h106_108 : V < 107
              · have he : V = 106 := by omega
                subst V
                exact row_4_106
              · have he : V = 107 := by omega
                subst V
                exact row_4_107
            · by_cases h108_110 : V < 109
              · have he : V = 108 := by omega
                subst V
                exact row_4_108
              · have he : V = 109 := by omega
                subst V
                exact row_4_109
        · by_cases h110_119 : V < 114
          · by_cases h110_114 : V < 112
            · by_cases h110_112 : V < 111
              · have he : V = 110 := by omega
                subst V
                exact row_4_110
              · have he : V = 111 := by omega
                subst V
                exact row_4_111
            · by_cases h112_114 : V < 113
              · have he : V = 112 := by omega
                subst V
                exact row_4_112
              · have he : V = 113 := by omega
                subst V
                exact row_4_113
          · by_cases h114_119 : V < 116
            · by_cases h114_116 : V < 115
              · have he : V = 114 := by omega
                subst V
                exact row_4_114
              · have he : V = 115 := by omega
                subst V
                exact row_4_115
            · by_cases h116_119 : V < 117
              · have he : V = 116 := by omega
                subst V
                exact row_4_116
              · by_cases h117_119 : V < 118
                · have he : V = 117 := by omega
                  subst V
                  exact row_4_117
                · have he : V = 118 := by omega
                  subst V
                  exact row_4_118
      · by_cases h119_136 : V < 127
        · by_cases h119_127 : V < 123
          · by_cases h119_123 : V < 121
            · by_cases h119_121 : V < 120
              · have he : V = 119 := by omega
                subst V
                exact row_4_119
              · have he : V = 120 := by omega
                subst V
                exact row_4_120
            · by_cases h121_123 : V < 122
              · have he : V = 121 := by omega
                subst V
                exact row_4_121
              · have he : V = 122 := by omega
                subst V
                exact row_4_122
          · by_cases h123_127 : V < 125
            · by_cases h123_125 : V < 124
              · have he : V = 123 := by omega
                subst V
                exact row_4_123
              · have he : V = 124 := by omega
                subst V
                exact row_4_124
            · by_cases h125_127 : V < 126
              · have he : V = 125 := by omega
                subst V
                exact row_4_125
              · have he : V = 126 := by omega
                subst V
                exact row_4_126
        · by_cases h127_136 : V < 131
          · by_cases h127_131 : V < 129
            · by_cases h127_129 : V < 128
              · have he : V = 127 := by omega
                subst V
                exact row_4_127
              · have he : V = 128 := by omega
                subst V
                exact row_4_128
            · by_cases h129_131 : V < 130
              · have he : V = 129 := by omega
                subst V
                exact row_4_129
              · have he : V = 130 := by omega
                subst V
                exact row_4_130
          · by_cases h131_136 : V < 133
            · by_cases h131_133 : V < 132
              · have he : V = 131 := by omega
                subst V
                exact row_4_131
              · have he : V = 132 := by omega
                subst V
                exact row_4_132
            · by_cases h133_136 : V < 134
              · have he : V = 133 := by omega
                subst V
                exact row_4_133
              · by_cases h134_136 : V < 135
                · have he : V = 134 := by omega
                  subst V
                  exact row_4_134
                · have he : V = 135 := by omega
                  subst V
                  exact row_4_135
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
