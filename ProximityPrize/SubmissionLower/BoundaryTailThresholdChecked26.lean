import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked25

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_26_0_0 : C 26 0 0 := by decide +kernel
theorem cell_26_0_1 : C 26 0 1 := by decide +kernel
theorem cell_26_0_2 : C 26 0 2 := by decide +kernel
theorem cell_26_0_3 : C 26 0 3 := by decide +kernel
theorem cell_26_0_4 : C 26 0 4 := by decide +kernel
theorem cell_26_0_5 : C 26 0 5 := by decide +kernel
theorem row_26_0 : ThresholdAt 26 0 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 0 0 cell_26_0_0
  | exact S 26 0 1 cell_26_0_1
  | exact S 26 0 2 cell_26_0_2
  | exact S 26 0 3 cell_26_0_3
  | exact S 26 0 4 cell_26_0_4
  | exact S 26 0 5 cell_26_0_5
theorem cell_26_1_0 : C 26 1 0 := by decide +kernel
theorem cell_26_1_1 : C 26 1 1 := by decide +kernel
theorem cell_26_1_2 : C 26 1 2 := by decide +kernel
theorem cell_26_1_3 : C 26 1 3 := by decide +kernel
theorem cell_26_1_4 : C 26 1 4 := by decide +kernel
theorem cell_26_1_5 : C 26 1 5 := by decide +kernel
theorem row_26_1 : ThresholdAt 26 1 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 1 0 cell_26_1_0
  | exact S 26 1 1 cell_26_1_1
  | exact S 26 1 2 cell_26_1_2
  | exact S 26 1 3 cell_26_1_3
  | exact S 26 1 4 cell_26_1_4
  | exact S 26 1 5 cell_26_1_5
theorem cell_26_2_0 : C 26 2 0 := by decide +kernel
theorem cell_26_2_1 : C 26 2 1 := by decide +kernel
theorem cell_26_2_2 : C 26 2 2 := by decide +kernel
theorem cell_26_2_3 : C 26 2 3 := by decide +kernel
theorem cell_26_2_4 : C 26 2 4 := by decide +kernel
theorem cell_26_2_5 : C 26 2 5 := by decide +kernel
theorem row_26_2 : ThresholdAt 26 2 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 2 0 cell_26_2_0
  | exact S 26 2 1 cell_26_2_1
  | exact S 26 2 2 cell_26_2_2
  | exact S 26 2 3 cell_26_2_3
  | exact S 26 2 4 cell_26_2_4
  | exact S 26 2 5 cell_26_2_5
theorem cell_26_3_0 : C 26 3 0 := by decide +kernel
theorem cell_26_3_1 : C 26 3 1 := by decide +kernel
theorem cell_26_3_2 : C 26 3 2 := by decide +kernel
theorem cell_26_3_3 : C 26 3 3 := by decide +kernel
theorem cell_26_3_4 : C 26 3 4 := by decide +kernel
theorem cell_26_3_5 : C 26 3 5 := by decide +kernel
theorem row_26_3 : ThresholdAt 26 3 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 3 0 cell_26_3_0
  | exact S 26 3 1 cell_26_3_1
  | exact S 26 3 2 cell_26_3_2
  | exact S 26 3 3 cell_26_3_3
  | exact S 26 3 4 cell_26_3_4
  | exact S 26 3 5 cell_26_3_5
theorem cell_26_4_0 : C 26 4 0 := by decide +kernel
theorem cell_26_4_1 : C 26 4 1 := by decide +kernel
theorem cell_26_4_2 : C 26 4 2 := by decide +kernel
theorem cell_26_4_3 : C 26 4 3 := by decide +kernel
theorem cell_26_4_4 : C 26 4 4 := by decide +kernel
theorem cell_26_4_5 : C 26 4 5 := by decide +kernel
theorem row_26_4 : ThresholdAt 26 4 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 4 0 cell_26_4_0
  | exact S 26 4 1 cell_26_4_1
  | exact S 26 4 2 cell_26_4_2
  | exact S 26 4 3 cell_26_4_3
  | exact S 26 4 4 cell_26_4_4
  | exact S 26 4 5 cell_26_4_5
theorem cell_26_5_0 : C 26 5 0 := by decide +kernel
theorem cell_26_5_1 : C 26 5 1 := by decide +kernel
theorem cell_26_5_2 : C 26 5 2 := by decide +kernel
theorem cell_26_5_3 : C 26 5 3 := by decide +kernel
theorem cell_26_5_4 : C 26 5 4 := by decide +kernel
theorem cell_26_5_5 : C 26 5 5 := by decide +kernel
theorem row_26_5 : ThresholdAt 26 5 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 5 0 cell_26_5_0
  | exact S 26 5 1 cell_26_5_1
  | exact S 26 5 2 cell_26_5_2
  | exact S 26 5 3 cell_26_5_3
  | exact S 26 5 4 cell_26_5_4
  | exact S 26 5 5 cell_26_5_5
theorem cell_26_6_0 : C 26 6 0 := by decide +kernel
theorem cell_26_6_1 : C 26 6 1 := by decide +kernel
theorem cell_26_6_2 : C 26 6 2 := by decide +kernel
theorem cell_26_6_3 : C 26 6 3 := by decide +kernel
theorem cell_26_6_4 : C 26 6 4 := by decide +kernel
theorem cell_26_6_5 : C 26 6 5 := by decide +kernel
theorem row_26_6 : ThresholdAt 26 6 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 6 0 cell_26_6_0
  | exact S 26 6 1 cell_26_6_1
  | exact S 26 6 2 cell_26_6_2
  | exact S 26 6 3 cell_26_6_3
  | exact S 26 6 4 cell_26_6_4
  | exact S 26 6 5 cell_26_6_5
theorem cell_26_7_0 : C 26 7 0 := by decide +kernel
theorem cell_26_7_1 : C 26 7 1 := by decide +kernel
theorem cell_26_7_2 : C 26 7 2 := by decide +kernel
theorem cell_26_7_3 : C 26 7 3 := by decide +kernel
theorem cell_26_7_4 : C 26 7 4 := by decide +kernel
theorem cell_26_7_5 : C 26 7 5 := by decide +kernel
theorem row_26_7 : ThresholdAt 26 7 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 7 0 cell_26_7_0
  | exact S 26 7 1 cell_26_7_1
  | exact S 26 7 2 cell_26_7_2
  | exact S 26 7 3 cell_26_7_3
  | exact S 26 7 4 cell_26_7_4
  | exact S 26 7 5 cell_26_7_5
theorem cell_26_8_0 : C 26 8 0 := by decide +kernel
theorem cell_26_8_1 : C 26 8 1 := by decide +kernel
theorem cell_26_8_2 : C 26 8 2 := by decide +kernel
theorem cell_26_8_3 : C 26 8 3 := by decide +kernel
theorem cell_26_8_4 : C 26 8 4 := by decide +kernel
theorem cell_26_8_5 : C 26 8 5 := by decide +kernel
theorem row_26_8 : ThresholdAt 26 8 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 8 0 cell_26_8_0
  | exact S 26 8 1 cell_26_8_1
  | exact S 26 8 2 cell_26_8_2
  | exact S 26 8 3 cell_26_8_3
  | exact S 26 8 4 cell_26_8_4
  | exact S 26 8 5 cell_26_8_5
theorem cell_26_9_0 : C 26 9 0 := by decide +kernel
theorem cell_26_9_1 : C 26 9 1 := by decide +kernel
theorem cell_26_9_2 : C 26 9 2 := by decide +kernel
theorem cell_26_9_3 : C 26 9 3 := by decide +kernel
theorem cell_26_9_4 : C 26 9 4 := by decide +kernel
theorem cell_26_9_5 : C 26 9 5 := by decide +kernel
theorem row_26_9 : ThresholdAt 26 9 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 9 0 cell_26_9_0
  | exact S 26 9 1 cell_26_9_1
  | exact S 26 9 2 cell_26_9_2
  | exact S 26 9 3 cell_26_9_3
  | exact S 26 9 4 cell_26_9_4
  | exact S 26 9 5 cell_26_9_5
theorem cell_26_10_0 : C 26 10 0 := by decide +kernel
theorem cell_26_10_1 : C 26 10 1 := by decide +kernel
theorem cell_26_10_2 : C 26 10 2 := by decide +kernel
theorem cell_26_10_3 : C 26 10 3 := by decide +kernel
theorem cell_26_10_4 : C 26 10 4 := by decide +kernel
theorem cell_26_10_5 : C 26 10 5 := by decide +kernel
theorem row_26_10 : ThresholdAt 26 10 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 10 0 cell_26_10_0
  | exact S 26 10 1 cell_26_10_1
  | exact S 26 10 2 cell_26_10_2
  | exact S 26 10 3 cell_26_10_3
  | exact S 26 10 4 cell_26_10_4
  | exact S 26 10 5 cell_26_10_5
theorem cell_26_11_0 : C 26 11 0 := by decide +kernel
theorem cell_26_11_1 : C 26 11 1 := by decide +kernel
theorem cell_26_11_2 : C 26 11 2 := by decide +kernel
theorem cell_26_11_3 : C 26 11 3 := by decide +kernel
theorem cell_26_11_4 : C 26 11 4 := by decide +kernel
theorem cell_26_11_5 : C 26 11 5 := by decide +kernel
theorem row_26_11 : ThresholdAt 26 11 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 11 0 cell_26_11_0
  | exact S 26 11 1 cell_26_11_1
  | exact S 26 11 2 cell_26_11_2
  | exact S 26 11 3 cell_26_11_3
  | exact S 26 11 4 cell_26_11_4
  | exact S 26 11 5 cell_26_11_5
theorem cell_26_12_0 : C 26 12 0 := by decide +kernel
theorem cell_26_12_1 : C 26 12 1 := by decide +kernel
theorem cell_26_12_2 : C 26 12 2 := by decide +kernel
theorem cell_26_12_3 : C 26 12 3 := by decide +kernel
theorem cell_26_12_4 : C 26 12 4 := by decide +kernel
theorem cell_26_12_5 : C 26 12 5 := by decide +kernel
theorem row_26_12 : ThresholdAt 26 12 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 12 0 cell_26_12_0
  | exact S 26 12 1 cell_26_12_1
  | exact S 26 12 2 cell_26_12_2
  | exact S 26 12 3 cell_26_12_3
  | exact S 26 12 4 cell_26_12_4
  | exact S 26 12 5 cell_26_12_5
theorem cell_26_13_0 : C 26 13 0 := by decide +kernel
theorem cell_26_13_1 : C 26 13 1 := by decide +kernel
theorem cell_26_13_2 : C 26 13 2 := by decide +kernel
theorem cell_26_13_3 : C 26 13 3 := by decide +kernel
theorem cell_26_13_4 : C 26 13 4 := by decide +kernel
theorem cell_26_13_5 : C 26 13 5 := by decide +kernel
theorem row_26_13 : ThresholdAt 26 13 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 13 0 cell_26_13_0
  | exact S 26 13 1 cell_26_13_1
  | exact S 26 13 2 cell_26_13_2
  | exact S 26 13 3 cell_26_13_3
  | exact S 26 13 4 cell_26_13_4
  | exact S 26 13 5 cell_26_13_5
theorem cell_26_14_0 : C 26 14 0 := by decide +kernel
theorem cell_26_14_1 : C 26 14 1 := by decide +kernel
theorem cell_26_14_2 : C 26 14 2 := by decide +kernel
theorem cell_26_14_3 : C 26 14 3 := by decide +kernel
theorem cell_26_14_4 : C 26 14 4 := by decide +kernel
theorem cell_26_14_5 : C 26 14 5 := by decide +kernel
theorem row_26_14 : ThresholdAt 26 14 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 14 0 cell_26_14_0
  | exact S 26 14 1 cell_26_14_1
  | exact S 26 14 2 cell_26_14_2
  | exact S 26 14 3 cell_26_14_3
  | exact S 26 14 4 cell_26_14_4
  | exact S 26 14 5 cell_26_14_5
theorem cell_26_15_0 : C 26 15 0 := by decide +kernel
theorem cell_26_15_1 : C 26 15 1 := by decide +kernel
theorem cell_26_15_2 : C 26 15 2 := by decide +kernel
theorem cell_26_15_3 : C 26 15 3 := by decide +kernel
theorem cell_26_15_4 : C 26 15 4 := by decide +kernel
theorem cell_26_15_5 : C 26 15 5 := by decide +kernel
theorem row_26_15 : ThresholdAt 26 15 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 15 0 cell_26_15_0
  | exact S 26 15 1 cell_26_15_1
  | exact S 26 15 2 cell_26_15_2
  | exact S 26 15 3 cell_26_15_3
  | exact S 26 15 4 cell_26_15_4
  | exact S 26 15 5 cell_26_15_5
theorem cell_26_16_0 : C 26 16 0 := by decide +kernel
theorem cell_26_16_1 : C 26 16 1 := by decide +kernel
theorem cell_26_16_2 : C 26 16 2 := by decide +kernel
theorem cell_26_16_3 : C 26 16 3 := by decide +kernel
theorem cell_26_16_4 : C 26 16 4 := by decide +kernel
theorem cell_26_16_5 : C 26 16 5 := by decide +kernel
theorem row_26_16 : ThresholdAt 26 16 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 16 0 cell_26_16_0
  | exact S 26 16 1 cell_26_16_1
  | exact S 26 16 2 cell_26_16_2
  | exact S 26 16 3 cell_26_16_3
  | exact S 26 16 4 cell_26_16_4
  | exact S 26 16 5 cell_26_16_5
theorem cell_26_17_0 : C 26 17 0 := by decide +kernel
theorem cell_26_17_1 : C 26 17 1 := by decide +kernel
theorem cell_26_17_2 : C 26 17 2 := by decide +kernel
theorem cell_26_17_3 : C 26 17 3 := by decide +kernel
theorem cell_26_17_4 : C 26 17 4 := by decide +kernel
theorem cell_26_17_5 : C 26 17 5 := by decide +kernel
theorem row_26_17 : ThresholdAt 26 17 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 17 0 cell_26_17_0
  | exact S 26 17 1 cell_26_17_1
  | exact S 26 17 2 cell_26_17_2
  | exact S 26 17 3 cell_26_17_3
  | exact S 26 17 4 cell_26_17_4
  | exact S 26 17 5 cell_26_17_5
theorem cell_26_18_0 : C 26 18 0 := by decide +kernel
theorem cell_26_18_1 : C 26 18 1 := by decide +kernel
theorem cell_26_18_2 : C 26 18 2 := by decide +kernel
theorem cell_26_18_3 : C 26 18 3 := by decide +kernel
theorem cell_26_18_4 : C 26 18 4 := by decide +kernel
theorem cell_26_18_5 : C 26 18 5 := by decide +kernel
theorem row_26_18 : ThresholdAt 26 18 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 18 0 cell_26_18_0
  | exact S 26 18 1 cell_26_18_1
  | exact S 26 18 2 cell_26_18_2
  | exact S 26 18 3 cell_26_18_3
  | exact S 26 18 4 cell_26_18_4
  | exact S 26 18 5 cell_26_18_5
theorem cell_26_19_0 : C 26 19 0 := by decide +kernel
theorem cell_26_19_1 : C 26 19 1 := by decide +kernel
theorem cell_26_19_2 : C 26 19 2 := by decide +kernel
theorem cell_26_19_3 : C 26 19 3 := by decide +kernel
theorem cell_26_19_4 : C 26 19 4 := by decide +kernel
theorem cell_26_19_5 : C 26 19 5 := by decide +kernel
theorem row_26_19 : ThresholdAt 26 19 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 19 0 cell_26_19_0
  | exact S 26 19 1 cell_26_19_1
  | exact S 26 19 2 cell_26_19_2
  | exact S 26 19 3 cell_26_19_3
  | exact S 26 19 4 cell_26_19_4
  | exact S 26 19 5 cell_26_19_5
theorem cell_26_20_0 : C 26 20 0 := by decide +kernel
theorem cell_26_20_1 : C 26 20 1 := by decide +kernel
theorem cell_26_20_2 : C 26 20 2 := by decide +kernel
theorem cell_26_20_3 : C 26 20 3 := by decide +kernel
theorem cell_26_20_4 : C 26 20 4 := by decide +kernel
theorem cell_26_20_5 : C 26 20 5 := by decide +kernel
theorem row_26_20 : ThresholdAt 26 20 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 20 0 cell_26_20_0
  | exact S 26 20 1 cell_26_20_1
  | exact S 26 20 2 cell_26_20_2
  | exact S 26 20 3 cell_26_20_3
  | exact S 26 20 4 cell_26_20_4
  | exact S 26 20 5 cell_26_20_5
theorem cell_26_21_0 : C 26 21 0 := by decide +kernel
theorem cell_26_21_1 : C 26 21 1 := by decide +kernel
theorem cell_26_21_2 : C 26 21 2 := by decide +kernel
theorem cell_26_21_3 : C 26 21 3 := by decide +kernel
theorem cell_26_21_4 : C 26 21 4 := by decide +kernel
theorem cell_26_21_5 : C 26 21 5 := by decide +kernel
theorem row_26_21 : ThresholdAt 26 21 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 21 0 cell_26_21_0
  | exact S 26 21 1 cell_26_21_1
  | exact S 26 21 2 cell_26_21_2
  | exact S 26 21 3 cell_26_21_3
  | exact S 26 21 4 cell_26_21_4
  | exact S 26 21 5 cell_26_21_5
theorem cell_26_22_0 : C 26 22 0 := by decide +kernel
theorem cell_26_22_1 : C 26 22 1 := by decide +kernel
theorem cell_26_22_2 : C 26 22 2 := by decide +kernel
theorem cell_26_22_3 : C 26 22 3 := by decide +kernel
theorem cell_26_22_4 : C 26 22 4 := by decide +kernel
theorem cell_26_22_5 : C 26 22 5 := by decide +kernel
theorem row_26_22 : ThresholdAt 26 22 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 22 0 cell_26_22_0
  | exact S 26 22 1 cell_26_22_1
  | exact S 26 22 2 cell_26_22_2
  | exact S 26 22 3 cell_26_22_3
  | exact S 26 22 4 cell_26_22_4
  | exact S 26 22 5 cell_26_22_5
theorem cell_26_23_0 : C 26 23 0 := by decide +kernel
theorem cell_26_23_1 : C 26 23 1 := by decide +kernel
theorem cell_26_23_2 : C 26 23 2 := by decide +kernel
theorem cell_26_23_3 : C 26 23 3 := by decide +kernel
theorem cell_26_23_4 : C 26 23 4 := by decide +kernel
theorem cell_26_23_5 : C 26 23 5 := by decide +kernel
theorem row_26_23 : ThresholdAt 26 23 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 23 0 cell_26_23_0
  | exact S 26 23 1 cell_26_23_1
  | exact S 26 23 2 cell_26_23_2
  | exact S 26 23 3 cell_26_23_3
  | exact S 26 23 4 cell_26_23_4
  | exact S 26 23 5 cell_26_23_5
theorem cell_26_24_0 : C 26 24 0 := by decide +kernel
theorem cell_26_24_1 : C 26 24 1 := by decide +kernel
theorem cell_26_24_2 : C 26 24 2 := by decide +kernel
theorem cell_26_24_3 : C 26 24 3 := by decide +kernel
theorem cell_26_24_4 : C 26 24 4 := by decide +kernel
theorem cell_26_24_5 : C 26 24 5 := by decide +kernel
theorem row_26_24 : ThresholdAt 26 24 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 24 0 cell_26_24_0
  | exact S 26 24 1 cell_26_24_1
  | exact S 26 24 2 cell_26_24_2
  | exact S 26 24 3 cell_26_24_3
  | exact S 26 24 4 cell_26_24_4
  | exact S 26 24 5 cell_26_24_5
theorem cell_26_25_0 : C 26 25 0 := by decide +kernel
theorem cell_26_25_1 : C 26 25 1 := by decide +kernel
theorem cell_26_25_2 : C 26 25 2 := by decide +kernel
theorem cell_26_25_3 : C 26 25 3 := by decide +kernel
theorem cell_26_25_4 : C 26 25 4 := by decide +kernel
theorem cell_26_25_5 : C 26 25 5 := by decide +kernel
theorem row_26_25 : ThresholdAt 26 25 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 25 0 cell_26_25_0
  | exact S 26 25 1 cell_26_25_1
  | exact S 26 25 2 cell_26_25_2
  | exact S 26 25 3 cell_26_25_3
  | exact S 26 25 4 cell_26_25_4
  | exact S 26 25 5 cell_26_25_5
theorem cell_26_26_0 : C 26 26 0 := by decide +kernel
theorem cell_26_26_1 : C 26 26 1 := by decide +kernel
theorem cell_26_26_2 : C 26 26 2 := by decide +kernel
theorem cell_26_26_3 : C 26 26 3 := by decide +kernel
theorem cell_26_26_4 : C 26 26 4 := by decide +kernel
theorem cell_26_26_5 : C 26 26 5 := by decide +kernel
theorem row_26_26 : ThresholdAt 26 26 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 26 0 cell_26_26_0
  | exact S 26 26 1 cell_26_26_1
  | exact S 26 26 2 cell_26_26_2
  | exact S 26 26 3 cell_26_26_3
  | exact S 26 26 4 cell_26_26_4
  | exact S 26 26 5 cell_26_26_5
theorem cell_26_27_0 : C 26 27 0 := by decide +kernel
theorem cell_26_27_1 : C 26 27 1 := by decide +kernel
theorem cell_26_27_2 : C 26 27 2 := by decide +kernel
theorem cell_26_27_3 : C 26 27 3 := by decide +kernel
theorem cell_26_27_4 : C 26 27 4 := by decide +kernel
theorem cell_26_27_5 : C 26 27 5 := by decide +kernel
theorem row_26_27 : ThresholdAt 26 27 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 27 0 cell_26_27_0
  | exact S 26 27 1 cell_26_27_1
  | exact S 26 27 2 cell_26_27_2
  | exact S 26 27 3 cell_26_27_3
  | exact S 26 27 4 cell_26_27_4
  | exact S 26 27 5 cell_26_27_5
theorem cell_26_28_0 : C 26 28 0 := by decide +kernel
theorem cell_26_28_1 : C 26 28 1 := by decide +kernel
theorem cell_26_28_2 : C 26 28 2 := by decide +kernel
theorem cell_26_28_3 : C 26 28 3 := by decide +kernel
theorem cell_26_28_4 : C 26 28 4 := by decide +kernel
theorem cell_26_28_5 : C 26 28 5 := by decide +kernel
theorem row_26_28 : ThresholdAt 26 28 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 28 0 cell_26_28_0
  | exact S 26 28 1 cell_26_28_1
  | exact S 26 28 2 cell_26_28_2
  | exact S 26 28 3 cell_26_28_3
  | exact S 26 28 4 cell_26_28_4
  | exact S 26 28 5 cell_26_28_5
theorem cell_26_29_0 : C 26 29 0 := by decide +kernel
theorem cell_26_29_1 : C 26 29 1 := by decide +kernel
theorem cell_26_29_2 : C 26 29 2 := by decide +kernel
theorem cell_26_29_3 : C 26 29 3 := by decide +kernel
theorem cell_26_29_4 : C 26 29 4 := by decide +kernel
theorem cell_26_29_5 : C 26 29 5 := by decide +kernel
theorem row_26_29 : ThresholdAt 26 29 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 29 0 cell_26_29_0
  | exact S 26 29 1 cell_26_29_1
  | exact S 26 29 2 cell_26_29_2
  | exact S 26 29 3 cell_26_29_3
  | exact S 26 29 4 cell_26_29_4
  | exact S 26 29 5 cell_26_29_5
theorem cell_26_30_0 : C 26 30 0 := by decide +kernel
theorem cell_26_30_1 : C 26 30 1 := by decide +kernel
theorem cell_26_30_2 : C 26 30 2 := by decide +kernel
theorem cell_26_30_3 : C 26 30 3 := by decide +kernel
theorem cell_26_30_4 : C 26 30 4 := by decide +kernel
theorem cell_26_30_5 : C 26 30 5 := by decide +kernel
theorem row_26_30 : ThresholdAt 26 30 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 30 0 cell_26_30_0
  | exact S 26 30 1 cell_26_30_1
  | exact S 26 30 2 cell_26_30_2
  | exact S 26 30 3 cell_26_30_3
  | exact S 26 30 4 cell_26_30_4
  | exact S 26 30 5 cell_26_30_5
theorem cell_26_31_0 : C 26 31 0 := by decide +kernel
theorem cell_26_31_1 : C 26 31 1 := by decide +kernel
theorem cell_26_31_2 : C 26 31 2 := by decide +kernel
theorem cell_26_31_3 : C 26 31 3 := by decide +kernel
theorem cell_26_31_4 : C 26 31 4 := by decide +kernel
theorem cell_26_31_5 : C 26 31 5 := by decide +kernel
theorem row_26_31 : ThresholdAt 26 31 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 31 0 cell_26_31_0
  | exact S 26 31 1 cell_26_31_1
  | exact S 26 31 2 cell_26_31_2
  | exact S 26 31 3 cell_26_31_3
  | exact S 26 31 4 cell_26_31_4
  | exact S 26 31 5 cell_26_31_5
theorem cell_26_32_0 : C 26 32 0 := by decide +kernel
theorem cell_26_32_1 : C 26 32 1 := by decide +kernel
theorem cell_26_32_2 : C 26 32 2 := by decide +kernel
theorem cell_26_32_3 : C 26 32 3 := by decide +kernel
theorem cell_26_32_4 : C 26 32 4 := by decide +kernel
theorem cell_26_32_5 : C 26 32 5 := by decide +kernel
theorem row_26_32 : ThresholdAt 26 32 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 32 0 cell_26_32_0
  | exact S 26 32 1 cell_26_32_1
  | exact S 26 32 2 cell_26_32_2
  | exact S 26 32 3 cell_26_32_3
  | exact S 26 32 4 cell_26_32_4
  | exact S 26 32 5 cell_26_32_5
theorem cell_26_33_0 : C 26 33 0 := by decide +kernel
theorem cell_26_33_1 : C 26 33 1 := by decide +kernel
theorem cell_26_33_2 : C 26 33 2 := by decide +kernel
theorem cell_26_33_3 : C 26 33 3 := by decide +kernel
theorem cell_26_33_4 : C 26 33 4 := by decide +kernel
theorem cell_26_33_5 : C 26 33 5 := by decide +kernel
theorem row_26_33 : ThresholdAt 26 33 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 33 0 cell_26_33_0
  | exact S 26 33 1 cell_26_33_1
  | exact S 26 33 2 cell_26_33_2
  | exact S 26 33 3 cell_26_33_3
  | exact S 26 33 4 cell_26_33_4
  | exact S 26 33 5 cell_26_33_5
theorem cell_26_34_0 : C 26 34 0 := by decide +kernel
theorem cell_26_34_1 : C 26 34 1 := by decide +kernel
theorem cell_26_34_2 : C 26 34 2 := by decide +kernel
theorem cell_26_34_3 : C 26 34 3 := by decide +kernel
theorem cell_26_34_4 : C 26 34 4 := by decide +kernel
theorem cell_26_34_5 : C 26 34 5 := by decide +kernel
theorem row_26_34 : ThresholdAt 26 34 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 34 0 cell_26_34_0
  | exact S 26 34 1 cell_26_34_1
  | exact S 26 34 2 cell_26_34_2
  | exact S 26 34 3 cell_26_34_3
  | exact S 26 34 4 cell_26_34_4
  | exact S 26 34 5 cell_26_34_5
theorem cell_26_35_0 : C 26 35 0 := by decide +kernel
theorem cell_26_35_1 : C 26 35 1 := by decide +kernel
theorem cell_26_35_2 : C 26 35 2 := by decide +kernel
theorem cell_26_35_3 : C 26 35 3 := by decide +kernel
theorem cell_26_35_4 : C 26 35 4 := by decide +kernel
theorem cell_26_35_5 : C 26 35 5 := by decide +kernel
theorem row_26_35 : ThresholdAt 26 35 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 35 0 cell_26_35_0
  | exact S 26 35 1 cell_26_35_1
  | exact S 26 35 2 cell_26_35_2
  | exact S 26 35 3 cell_26_35_3
  | exact S 26 35 4 cell_26_35_4
  | exact S 26 35 5 cell_26_35_5
theorem cell_26_36_0 : C 26 36 0 := by decide +kernel
theorem cell_26_36_1 : C 26 36 1 := by decide +kernel
theorem cell_26_36_2 : C 26 36 2 := by decide +kernel
theorem cell_26_36_3 : C 26 36 3 := by decide +kernel
theorem cell_26_36_4 : C 26 36 4 := by decide +kernel
theorem cell_26_36_5 : C 26 36 5 := by decide +kernel
theorem row_26_36 : ThresholdAt 26 36 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 36 0 cell_26_36_0
  | exact S 26 36 1 cell_26_36_1
  | exact S 26 36 2 cell_26_36_2
  | exact S 26 36 3 cell_26_36_3
  | exact S 26 36 4 cell_26_36_4
  | exact S 26 36 5 cell_26_36_5
theorem cell_26_37_0 : C 26 37 0 := by decide +kernel
theorem cell_26_37_1 : C 26 37 1 := by decide +kernel
theorem cell_26_37_2 : C 26 37 2 := by decide +kernel
theorem cell_26_37_3 : C 26 37 3 := by decide +kernel
theorem cell_26_37_4 : C 26 37 4 := by decide +kernel
theorem cell_26_37_5 : C 26 37 5 := by decide +kernel
theorem row_26_37 : ThresholdAt 26 37 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 37 0 cell_26_37_0
  | exact S 26 37 1 cell_26_37_1
  | exact S 26 37 2 cell_26_37_2
  | exact S 26 37 3 cell_26_37_3
  | exact S 26 37 4 cell_26_37_4
  | exact S 26 37 5 cell_26_37_5
theorem cell_26_38_0 : C 26 38 0 := by decide +kernel
theorem cell_26_38_1 : C 26 38 1 := by decide +kernel
theorem cell_26_38_2 : C 26 38 2 := by decide +kernel
theorem cell_26_38_3 : C 26 38 3 := by decide +kernel
theorem cell_26_38_4 : C 26 38 4 := by decide +kernel
theorem cell_26_38_5 : C 26 38 5 := by decide +kernel
theorem row_26_38 : ThresholdAt 26 38 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 38 0 cell_26_38_0
  | exact S 26 38 1 cell_26_38_1
  | exact S 26 38 2 cell_26_38_2
  | exact S 26 38 3 cell_26_38_3
  | exact S 26 38 4 cell_26_38_4
  | exact S 26 38 5 cell_26_38_5
theorem cell_26_39_0 : C 26 39 0 := by decide +kernel
theorem cell_26_39_1 : C 26 39 1 := by decide +kernel
theorem cell_26_39_2 : C 26 39 2 := by decide +kernel
theorem cell_26_39_3 : C 26 39 3 := by decide +kernel
theorem cell_26_39_4 : C 26 39 4 := by decide +kernel
theorem cell_26_39_5 : C 26 39 5 := by decide +kernel
theorem row_26_39 : ThresholdAt 26 39 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 39 0 cell_26_39_0
  | exact S 26 39 1 cell_26_39_1
  | exact S 26 39 2 cell_26_39_2
  | exact S 26 39 3 cell_26_39_3
  | exact S 26 39 4 cell_26_39_4
  | exact S 26 39 5 cell_26_39_5
theorem cell_26_40_0 : C 26 40 0 := by decide +kernel
theorem cell_26_40_1 : C 26 40 1 := by decide +kernel
theorem cell_26_40_2 : C 26 40 2 := by decide +kernel
theorem cell_26_40_3 : C 26 40 3 := by decide +kernel
theorem cell_26_40_4 : C 26 40 4 := by decide +kernel
theorem cell_26_40_5 : C 26 40 5 := by decide +kernel
theorem row_26_40 : ThresholdAt 26 40 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 40 0 cell_26_40_0
  | exact S 26 40 1 cell_26_40_1
  | exact S 26 40 2 cell_26_40_2
  | exact S 26 40 3 cell_26_40_3
  | exact S 26 40 4 cell_26_40_4
  | exact S 26 40 5 cell_26_40_5
theorem cell_26_41_0 : C 26 41 0 := by decide +kernel
theorem cell_26_41_1 : C 26 41 1 := by decide +kernel
theorem cell_26_41_2 : C 26 41 2 := by decide +kernel
theorem cell_26_41_3 : C 26 41 3 := by decide +kernel
theorem cell_26_41_4 : C 26 41 4 := by decide +kernel
theorem cell_26_41_5 : C 26 41 5 := by decide +kernel
theorem row_26_41 : ThresholdAt 26 41 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 41 0 cell_26_41_0
  | exact S 26 41 1 cell_26_41_1
  | exact S 26 41 2 cell_26_41_2
  | exact S 26 41 3 cell_26_41_3
  | exact S 26 41 4 cell_26_41_4
  | exact S 26 41 5 cell_26_41_5
theorem cell_26_42_0 : C 26 42 0 := by decide +kernel
theorem cell_26_42_1 : C 26 42 1 := by decide +kernel
theorem cell_26_42_2 : C 26 42 2 := by decide +kernel
theorem cell_26_42_3 : C 26 42 3 := by decide +kernel
theorem cell_26_42_4 : C 26 42 4 := by decide +kernel
theorem cell_26_42_5 : C 26 42 5 := by decide +kernel
theorem row_26_42 : ThresholdAt 26 42 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 42 0 cell_26_42_0
  | exact S 26 42 1 cell_26_42_1
  | exact S 26 42 2 cell_26_42_2
  | exact S 26 42 3 cell_26_42_3
  | exact S 26 42 4 cell_26_42_4
  | exact S 26 42 5 cell_26_42_5
theorem cell_26_43_0 : C 26 43 0 := by decide +kernel
theorem cell_26_43_1 : C 26 43 1 := by decide +kernel
theorem cell_26_43_2 : C 26 43 2 := by decide +kernel
theorem cell_26_43_3 : C 26 43 3 := by decide +kernel
theorem cell_26_43_4 : C 26 43 4 := by decide +kernel
theorem cell_26_43_5 : C 26 43 5 := by decide +kernel
theorem row_26_43 : ThresholdAt 26 43 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 43 0 cell_26_43_0
  | exact S 26 43 1 cell_26_43_1
  | exact S 26 43 2 cell_26_43_2
  | exact S 26 43 3 cell_26_43_3
  | exact S 26 43 4 cell_26_43_4
  | exact S 26 43 5 cell_26_43_5
theorem cell_26_44_0 : C 26 44 0 := by decide +kernel
theorem cell_26_44_1 : C 26 44 1 := by decide +kernel
theorem cell_26_44_2 : C 26 44 2 := by decide +kernel
theorem cell_26_44_3 : C 26 44 3 := by decide +kernel
theorem cell_26_44_4 : C 26 44 4 := by decide +kernel
theorem cell_26_44_5 : C 26 44 5 := by decide +kernel
theorem row_26_44 : ThresholdAt 26 44 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 44 0 cell_26_44_0
  | exact S 26 44 1 cell_26_44_1
  | exact S 26 44 2 cell_26_44_2
  | exact S 26 44 3 cell_26_44_3
  | exact S 26 44 4 cell_26_44_4
  | exact S 26 44 5 cell_26_44_5
theorem cell_26_45_0 : C 26 45 0 := by decide +kernel
theorem cell_26_45_1 : C 26 45 1 := by decide +kernel
theorem cell_26_45_2 : C 26 45 2 := by decide +kernel
theorem cell_26_45_3 : C 26 45 3 := by decide +kernel
theorem cell_26_45_4 : C 26 45 4 := by decide +kernel
theorem cell_26_45_5 : C 26 45 5 := by decide +kernel
theorem row_26_45 : ThresholdAt 26 45 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 45 0 cell_26_45_0
  | exact S 26 45 1 cell_26_45_1
  | exact S 26 45 2 cell_26_45_2
  | exact S 26 45 3 cell_26_45_3
  | exact S 26 45 4 cell_26_45_4
  | exact S 26 45 5 cell_26_45_5
theorem cell_26_46_0 : C 26 46 0 := by decide +kernel
theorem cell_26_46_1 : C 26 46 1 := by decide +kernel
theorem cell_26_46_2 : C 26 46 2 := by decide +kernel
theorem cell_26_46_3 : C 26 46 3 := by decide +kernel
theorem cell_26_46_4 : C 26 46 4 := by decide +kernel
theorem cell_26_46_5 : C 26 46 5 := by decide +kernel
theorem row_26_46 : ThresholdAt 26 46 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 46 0 cell_26_46_0
  | exact S 26 46 1 cell_26_46_1
  | exact S 26 46 2 cell_26_46_2
  | exact S 26 46 3 cell_26_46_3
  | exact S 26 46 4 cell_26_46_4
  | exact S 26 46 5 cell_26_46_5
theorem cell_26_47_0 : C 26 47 0 := by decide +kernel
theorem cell_26_47_1 : C 26 47 1 := by decide +kernel
theorem cell_26_47_2 : C 26 47 2 := by decide +kernel
theorem cell_26_47_3 : C 26 47 3 := by decide +kernel
theorem cell_26_47_4 : C 26 47 4 := by decide +kernel
theorem cell_26_47_5 : C 26 47 5 := by decide +kernel
theorem row_26_47 : ThresholdAt 26 47 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 47 0 cell_26_47_0
  | exact S 26 47 1 cell_26_47_1
  | exact S 26 47 2 cell_26_47_2
  | exact S 26 47 3 cell_26_47_3
  | exact S 26 47 4 cell_26_47_4
  | exact S 26 47 5 cell_26_47_5
theorem cell_26_48_0 : C 26 48 0 := by decide +kernel
theorem cell_26_48_1 : C 26 48 1 := by decide +kernel
theorem cell_26_48_2 : C 26 48 2 := by decide +kernel
theorem cell_26_48_3 : C 26 48 3 := by decide +kernel
theorem cell_26_48_4 : C 26 48 4 := by decide +kernel
theorem cell_26_48_5 : C 26 48 5 := by decide +kernel
theorem row_26_48 : ThresholdAt 26 48 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 48 0 cell_26_48_0
  | exact S 26 48 1 cell_26_48_1
  | exact S 26 48 2 cell_26_48_2
  | exact S 26 48 3 cell_26_48_3
  | exact S 26 48 4 cell_26_48_4
  | exact S 26 48 5 cell_26_48_5
theorem cell_26_49_0 : C 26 49 0 := by decide +kernel
theorem cell_26_49_1 : C 26 49 1 := by decide +kernel
theorem cell_26_49_2 : C 26 49 2 := by decide +kernel
theorem cell_26_49_3 : C 26 49 3 := by decide +kernel
theorem cell_26_49_4 : C 26 49 4 := by decide +kernel
theorem cell_26_49_5 : C 26 49 5 := by decide +kernel
theorem row_26_49 : ThresholdAt 26 49 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 49 0 cell_26_49_0
  | exact S 26 49 1 cell_26_49_1
  | exact S 26 49 2 cell_26_49_2
  | exact S 26 49 3 cell_26_49_3
  | exact S 26 49 4 cell_26_49_4
  | exact S 26 49 5 cell_26_49_5
theorem cell_26_50_0 : C 26 50 0 := by decide +kernel
theorem cell_26_50_1 : C 26 50 1 := by decide +kernel
theorem cell_26_50_2 : C 26 50 2 := by decide +kernel
theorem cell_26_50_3 : C 26 50 3 := by decide +kernel
theorem cell_26_50_4 : C 26 50 4 := by decide +kernel
theorem cell_26_50_5 : C 26 50 5 := by decide +kernel
theorem row_26_50 : ThresholdAt 26 50 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 50 0 cell_26_50_0
  | exact S 26 50 1 cell_26_50_1
  | exact S 26 50 2 cell_26_50_2
  | exact S 26 50 3 cell_26_50_3
  | exact S 26 50 4 cell_26_50_4
  | exact S 26 50 5 cell_26_50_5
theorem cell_26_51_0 : C 26 51 0 := by decide +kernel
theorem cell_26_51_1 : C 26 51 1 := by decide +kernel
theorem cell_26_51_2 : C 26 51 2 := by decide +kernel
theorem cell_26_51_3 : C 26 51 3 := by decide +kernel
theorem cell_26_51_4 : C 26 51 4 := by decide +kernel
theorem cell_26_51_5 : C 26 51 5 := by decide +kernel
theorem row_26_51 : ThresholdAt 26 51 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 51 0 cell_26_51_0
  | exact S 26 51 1 cell_26_51_1
  | exact S 26 51 2 cell_26_51_2
  | exact S 26 51 3 cell_26_51_3
  | exact S 26 51 4 cell_26_51_4
  | exact S 26 51 5 cell_26_51_5
theorem cell_26_52_0 : C 26 52 0 := by decide +kernel
theorem cell_26_52_1 : C 26 52 1 := by decide +kernel
theorem cell_26_52_2 : C 26 52 2 := by decide +kernel
theorem cell_26_52_3 : C 26 52 3 := by decide +kernel
theorem cell_26_52_4 : C 26 52 4 := by decide +kernel
theorem cell_26_52_5 : C 26 52 5 := by decide +kernel
theorem row_26_52 : ThresholdAt 26 52 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 52 0 cell_26_52_0
  | exact S 26 52 1 cell_26_52_1
  | exact S 26 52 2 cell_26_52_2
  | exact S 26 52 3 cell_26_52_3
  | exact S 26 52 4 cell_26_52_4
  | exact S 26 52 5 cell_26_52_5
theorem cell_26_53_0 : C 26 53 0 := by decide +kernel
theorem cell_26_53_1 : C 26 53 1 := by decide +kernel
theorem cell_26_53_2 : C 26 53 2 := by decide +kernel
theorem cell_26_53_3 : C 26 53 3 := by decide +kernel
theorem cell_26_53_4 : C 26 53 4 := by decide +kernel
theorem cell_26_53_5 : C 26 53 5 := by decide +kernel
theorem row_26_53 : ThresholdAt 26 53 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 53 0 cell_26_53_0
  | exact S 26 53 1 cell_26_53_1
  | exact S 26 53 2 cell_26_53_2
  | exact S 26 53 3 cell_26_53_3
  | exact S 26 53 4 cell_26_53_4
  | exact S 26 53 5 cell_26_53_5
theorem cell_26_54_0 : C 26 54 0 := by decide +kernel
theorem cell_26_54_1 : C 26 54 1 := by decide +kernel
theorem cell_26_54_2 : C 26 54 2 := by decide +kernel
theorem cell_26_54_3 : C 26 54 3 := by decide +kernel
theorem cell_26_54_4 : C 26 54 4 := by decide +kernel
theorem cell_26_54_5 : C 26 54 5 := by decide +kernel
theorem row_26_54 : ThresholdAt 26 54 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 54 0 cell_26_54_0
  | exact S 26 54 1 cell_26_54_1
  | exact S 26 54 2 cell_26_54_2
  | exact S 26 54 3 cell_26_54_3
  | exact S 26 54 4 cell_26_54_4
  | exact S 26 54 5 cell_26_54_5
theorem cell_26_55_0 : C 26 55 0 := by decide +kernel
theorem cell_26_55_1 : C 26 55 1 := by decide +kernel
theorem cell_26_55_2 : C 26 55 2 := by decide +kernel
theorem cell_26_55_3 : C 26 55 3 := by decide +kernel
theorem cell_26_55_4 : C 26 55 4 := by decide +kernel
theorem cell_26_55_5 : C 26 55 5 := by decide +kernel
theorem row_26_55 : ThresholdAt 26 55 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 55 0 cell_26_55_0
  | exact S 26 55 1 cell_26_55_1
  | exact S 26 55 2 cell_26_55_2
  | exact S 26 55 3 cell_26_55_3
  | exact S 26 55 4 cell_26_55_4
  | exact S 26 55 5 cell_26_55_5
theorem cell_26_56_0 : C 26 56 0 := by decide +kernel
theorem cell_26_56_1 : C 26 56 1 := by decide +kernel
theorem cell_26_56_2 : C 26 56 2 := by decide +kernel
theorem cell_26_56_3 : C 26 56 3 := by decide +kernel
theorem cell_26_56_4 : C 26 56 4 := by decide +kernel
theorem cell_26_56_5 : C 26 56 5 := by decide +kernel
theorem row_26_56 : ThresholdAt 26 56 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 56 0 cell_26_56_0
  | exact S 26 56 1 cell_26_56_1
  | exact S 26 56 2 cell_26_56_2
  | exact S 26 56 3 cell_26_56_3
  | exact S 26 56 4 cell_26_56_4
  | exact S 26 56 5 cell_26_56_5
theorem cell_26_57_0 : C 26 57 0 := by decide +kernel
theorem cell_26_57_1 : C 26 57 1 := by decide +kernel
theorem cell_26_57_2 : C 26 57 2 := by decide +kernel
theorem cell_26_57_3 : C 26 57 3 := by decide +kernel
theorem cell_26_57_4 : C 26 57 4 := by decide +kernel
theorem cell_26_57_5 : C 26 57 5 := by decide +kernel
theorem row_26_57 : ThresholdAt 26 57 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 57 0 cell_26_57_0
  | exact S 26 57 1 cell_26_57_1
  | exact S 26 57 2 cell_26_57_2
  | exact S 26 57 3 cell_26_57_3
  | exact S 26 57 4 cell_26_57_4
  | exact S 26 57 5 cell_26_57_5
theorem cell_26_58_0 : C 26 58 0 := by decide +kernel
theorem cell_26_58_1 : C 26 58 1 := by decide +kernel
theorem cell_26_58_2 : C 26 58 2 := by decide +kernel
theorem cell_26_58_3 : C 26 58 3 := by decide +kernel
theorem cell_26_58_4 : C 26 58 4 := by decide +kernel
theorem cell_26_58_5 : C 26 58 5 := by decide +kernel
theorem row_26_58 : ThresholdAt 26 58 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 58 0 cell_26_58_0
  | exact S 26 58 1 cell_26_58_1
  | exact S 26 58 2 cell_26_58_2
  | exact S 26 58 3 cell_26_58_3
  | exact S 26 58 4 cell_26_58_4
  | exact S 26 58 5 cell_26_58_5
theorem cell_26_59_0 : C 26 59 0 := by decide +kernel
theorem cell_26_59_1 : C 26 59 1 := by decide +kernel
theorem cell_26_59_2 : C 26 59 2 := by decide +kernel
theorem cell_26_59_3 : C 26 59 3 := by decide +kernel
theorem cell_26_59_4 : C 26 59 4 := by decide +kernel
theorem cell_26_59_5 : C 26 59 5 := by decide +kernel
theorem row_26_59 : ThresholdAt 26 59 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 59 0 cell_26_59_0
  | exact S 26 59 1 cell_26_59_1
  | exact S 26 59 2 cell_26_59_2
  | exact S 26 59 3 cell_26_59_3
  | exact S 26 59 4 cell_26_59_4
  | exact S 26 59 5 cell_26_59_5
theorem cell_26_60_0 : C 26 60 0 := by decide +kernel
theorem cell_26_60_1 : C 26 60 1 := by decide +kernel
theorem cell_26_60_2 : C 26 60 2 := by decide +kernel
theorem cell_26_60_3 : C 26 60 3 := by decide +kernel
theorem cell_26_60_4 : C 26 60 4 := by decide +kernel
theorem cell_26_60_5 : C 26 60 5 := by decide +kernel
theorem row_26_60 : ThresholdAt 26 60 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 60 0 cell_26_60_0
  | exact S 26 60 1 cell_26_60_1
  | exact S 26 60 2 cell_26_60_2
  | exact S 26 60 3 cell_26_60_3
  | exact S 26 60 4 cell_26_60_4
  | exact S 26 60 5 cell_26_60_5
theorem cell_26_61_0 : C 26 61 0 := by decide +kernel
theorem cell_26_61_1 : C 26 61 1 := by decide +kernel
theorem cell_26_61_2 : C 26 61 2 := by decide +kernel
theorem cell_26_61_3 : C 26 61 3 := by decide +kernel
theorem cell_26_61_4 : C 26 61 4 := by decide +kernel
theorem cell_26_61_5 : C 26 61 5 := by decide +kernel
theorem row_26_61 : ThresholdAt 26 61 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 61 0 cell_26_61_0
  | exact S 26 61 1 cell_26_61_1
  | exact S 26 61 2 cell_26_61_2
  | exact S 26 61 3 cell_26_61_3
  | exact S 26 61 4 cell_26_61_4
  | exact S 26 61 5 cell_26_61_5
theorem cell_26_62_0 : C 26 62 0 := by decide +kernel
theorem cell_26_62_1 : C 26 62 1 := by decide +kernel
theorem cell_26_62_2 : C 26 62 2 := by decide +kernel
theorem cell_26_62_3 : C 26 62 3 := by decide +kernel
theorem cell_26_62_4 : C 26 62 4 := by decide +kernel
theorem cell_26_62_5 : C 26 62 5 := by decide +kernel
theorem row_26_62 : ThresholdAt 26 62 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 62 0 cell_26_62_0
  | exact S 26 62 1 cell_26_62_1
  | exact S 26 62 2 cell_26_62_2
  | exact S 26 62 3 cell_26_62_3
  | exact S 26 62 4 cell_26_62_4
  | exact S 26 62 5 cell_26_62_5
theorem cell_26_63_0 : C 26 63 0 := by decide +kernel
theorem cell_26_63_1 : C 26 63 1 := by decide +kernel
theorem cell_26_63_2 : C 26 63 2 := by decide +kernel
theorem cell_26_63_3 : C 26 63 3 := by decide +kernel
theorem cell_26_63_4 : C 26 63 4 := by decide +kernel
theorem cell_26_63_5 : C 26 63 5 := by decide +kernel
theorem row_26_63 : ThresholdAt 26 63 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 63 0 cell_26_63_0
  | exact S 26 63 1 cell_26_63_1
  | exact S 26 63 2 cell_26_63_2
  | exact S 26 63 3 cell_26_63_3
  | exact S 26 63 4 cell_26_63_4
  | exact S 26 63 5 cell_26_63_5
theorem cell_26_64_0 : C 26 64 0 := by decide +kernel
theorem cell_26_64_1 : C 26 64 1 := by decide +kernel
theorem cell_26_64_2 : C 26 64 2 := by decide +kernel
theorem cell_26_64_3 : C 26 64 3 := by decide +kernel
theorem cell_26_64_4 : C 26 64 4 := by decide +kernel
theorem cell_26_64_5 : C 26 64 5 := by decide +kernel
theorem row_26_64 : ThresholdAt 26 64 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 64 0 cell_26_64_0
  | exact S 26 64 1 cell_26_64_1
  | exact S 26 64 2 cell_26_64_2
  | exact S 26 64 3 cell_26_64_3
  | exact S 26 64 4 cell_26_64_4
  | exact S 26 64 5 cell_26_64_5
theorem cell_26_65_0 : C 26 65 0 := by decide +kernel
theorem cell_26_65_1 : C 26 65 1 := by decide +kernel
theorem cell_26_65_2 : C 26 65 2 := by decide +kernel
theorem cell_26_65_3 : C 26 65 3 := by decide +kernel
theorem cell_26_65_4 : C 26 65 4 := by decide +kernel
theorem cell_26_65_5 : C 26 65 5 := by decide +kernel
theorem row_26_65 : ThresholdAt 26 65 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 65 0 cell_26_65_0
  | exact S 26 65 1 cell_26_65_1
  | exact S 26 65 2 cell_26_65_2
  | exact S 26 65 3 cell_26_65_3
  | exact S 26 65 4 cell_26_65_4
  | exact S 26 65 5 cell_26_65_5
theorem cell_26_66_0 : C 26 66 0 := by decide +kernel
theorem cell_26_66_1 : C 26 66 1 := by decide +kernel
theorem cell_26_66_2 : C 26 66 2 := by decide +kernel
theorem cell_26_66_3 : C 26 66 3 := by decide +kernel
theorem cell_26_66_4 : C 26 66 4 := by decide +kernel
theorem cell_26_66_5 : C 26 66 5 := by decide +kernel
theorem row_26_66 : ThresholdAt 26 66 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 66 0 cell_26_66_0
  | exact S 26 66 1 cell_26_66_1
  | exact S 26 66 2 cell_26_66_2
  | exact S 26 66 3 cell_26_66_3
  | exact S 26 66 4 cell_26_66_4
  | exact S 26 66 5 cell_26_66_5
theorem cell_26_67_0 : C 26 67 0 := by decide +kernel
theorem cell_26_67_1 : C 26 67 1 := by decide +kernel
theorem cell_26_67_2 : C 26 67 2 := by decide +kernel
theorem cell_26_67_3 : C 26 67 3 := by decide +kernel
theorem cell_26_67_4 : C 26 67 4 := by decide +kernel
theorem cell_26_67_5 : C 26 67 5 := by decide +kernel
theorem row_26_67 : ThresholdAt 26 67 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 67 0 cell_26_67_0
  | exact S 26 67 1 cell_26_67_1
  | exact S 26 67 2 cell_26_67_2
  | exact S 26 67 3 cell_26_67_3
  | exact S 26 67 4 cell_26_67_4
  | exact S 26 67 5 cell_26_67_5
theorem cell_26_68_0 : C 26 68 0 := by decide +kernel
theorem cell_26_68_1 : C 26 68 1 := by decide +kernel
theorem cell_26_68_2 : C 26 68 2 := by decide +kernel
theorem cell_26_68_3 : C 26 68 3 := by decide +kernel
theorem cell_26_68_4 : C 26 68 4 := by decide +kernel
theorem cell_26_68_5 : C 26 68 5 := by decide +kernel
theorem row_26_68 : ThresholdAt 26 68 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 68 0 cell_26_68_0
  | exact S 26 68 1 cell_26_68_1
  | exact S 26 68 2 cell_26_68_2
  | exact S 26 68 3 cell_26_68_3
  | exact S 26 68 4 cell_26_68_4
  | exact S 26 68 5 cell_26_68_5
theorem cell_26_69_0 : C 26 69 0 := by decide +kernel
theorem cell_26_69_1 : C 26 69 1 := by decide +kernel
theorem cell_26_69_2 : C 26 69 2 := by decide +kernel
theorem cell_26_69_3 : C 26 69 3 := by decide +kernel
theorem cell_26_69_4 : C 26 69 4 := by decide +kernel
theorem cell_26_69_5 : C 26 69 5 := by decide +kernel
theorem row_26_69 : ThresholdAt 26 69 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 69 0 cell_26_69_0
  | exact S 26 69 1 cell_26_69_1
  | exact S 26 69 2 cell_26_69_2
  | exact S 26 69 3 cell_26_69_3
  | exact S 26 69 4 cell_26_69_4
  | exact S 26 69 5 cell_26_69_5
theorem cell_26_70_0 : C 26 70 0 := by decide +kernel
theorem cell_26_70_1 : C 26 70 1 := by decide +kernel
theorem cell_26_70_2 : C 26 70 2 := by decide +kernel
theorem cell_26_70_3 : C 26 70 3 := by decide +kernel
theorem cell_26_70_4 : C 26 70 4 := by decide +kernel
theorem cell_26_70_5 : C 26 70 5 := by decide +kernel
theorem row_26_70 : ThresholdAt 26 70 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 70 0 cell_26_70_0
  | exact S 26 70 1 cell_26_70_1
  | exact S 26 70 2 cell_26_70_2
  | exact S 26 70 3 cell_26_70_3
  | exact S 26 70 4 cell_26_70_4
  | exact S 26 70 5 cell_26_70_5
theorem cell_26_71_0 : C 26 71 0 := by decide +kernel
theorem cell_26_71_1 : C 26 71 1 := by decide +kernel
theorem cell_26_71_2 : C 26 71 2 := by decide +kernel
theorem cell_26_71_3 : C 26 71 3 := by decide +kernel
theorem cell_26_71_4 : C 26 71 4 := by decide +kernel
theorem cell_26_71_5 : C 26 71 5 := by decide +kernel
theorem row_26_71 : ThresholdAt 26 71 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 71 0 cell_26_71_0
  | exact S 26 71 1 cell_26_71_1
  | exact S 26 71 2 cell_26_71_2
  | exact S 26 71 3 cell_26_71_3
  | exact S 26 71 4 cell_26_71_4
  | exact S 26 71 5 cell_26_71_5
theorem cell_26_72_0 : C 26 72 0 := by decide +kernel
theorem cell_26_72_1 : C 26 72 1 := by decide +kernel
theorem cell_26_72_2 : C 26 72 2 := by decide +kernel
theorem cell_26_72_3 : C 26 72 3 := by decide +kernel
theorem cell_26_72_4 : C 26 72 4 := by decide +kernel
theorem cell_26_72_5 : C 26 72 5 := by decide +kernel
theorem row_26_72 : ThresholdAt 26 72 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 72 0 cell_26_72_0
  | exact S 26 72 1 cell_26_72_1
  | exact S 26 72 2 cell_26_72_2
  | exact S 26 72 3 cell_26_72_3
  | exact S 26 72 4 cell_26_72_4
  | exact S 26 72 5 cell_26_72_5
theorem cell_26_73_0 : C 26 73 0 := by decide +kernel
theorem cell_26_73_1 : C 26 73 1 := by decide +kernel
theorem cell_26_73_2 : C 26 73 2 := by decide +kernel
theorem cell_26_73_3 : C 26 73 3 := by decide +kernel
theorem cell_26_73_4 : C 26 73 4 := by decide +kernel
theorem cell_26_73_5 : C 26 73 5 := by decide +kernel
theorem row_26_73 : ThresholdAt 26 73 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 73 0 cell_26_73_0
  | exact S 26 73 1 cell_26_73_1
  | exact S 26 73 2 cell_26_73_2
  | exact S 26 73 3 cell_26_73_3
  | exact S 26 73 4 cell_26_73_4
  | exact S 26 73 5 cell_26_73_5
theorem cell_26_74_0 : C 26 74 0 := by decide +kernel
theorem cell_26_74_1 : C 26 74 1 := by decide +kernel
theorem cell_26_74_2 : C 26 74 2 := by decide +kernel
theorem cell_26_74_3 : C 26 74 3 := by decide +kernel
theorem cell_26_74_4 : C 26 74 4 := by decide +kernel
theorem cell_26_74_5 : C 26 74 5 := by decide +kernel
theorem row_26_74 : ThresholdAt 26 74 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 74 0 cell_26_74_0
  | exact S 26 74 1 cell_26_74_1
  | exact S 26 74 2 cell_26_74_2
  | exact S 26 74 3 cell_26_74_3
  | exact S 26 74 4 cell_26_74_4
  | exact S 26 74 5 cell_26_74_5
theorem cell_26_75_0 : C 26 75 0 := by decide +kernel
theorem cell_26_75_1 : C 26 75 1 := by decide +kernel
theorem cell_26_75_2 : C 26 75 2 := by decide +kernel
theorem cell_26_75_3 : C 26 75 3 := by decide +kernel
theorem cell_26_75_4 : C 26 75 4 := by decide +kernel
theorem cell_26_75_5 : C 26 75 5 := by decide +kernel
theorem row_26_75 : ThresholdAt 26 75 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 75 0 cell_26_75_0
  | exact S 26 75 1 cell_26_75_1
  | exact S 26 75 2 cell_26_75_2
  | exact S 26 75 3 cell_26_75_3
  | exact S 26 75 4 cell_26_75_4
  | exact S 26 75 5 cell_26_75_5
theorem cell_26_76_0 : C 26 76 0 := by decide +kernel
theorem cell_26_76_1 : C 26 76 1 := by decide +kernel
theorem cell_26_76_2 : C 26 76 2 := by decide +kernel
theorem cell_26_76_3 : C 26 76 3 := by decide +kernel
theorem cell_26_76_4 : C 26 76 4 := by decide +kernel
theorem cell_26_76_5 : C 26 76 5 := by decide +kernel
theorem row_26_76 : ThresholdAt 26 76 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 76 0 cell_26_76_0
  | exact S 26 76 1 cell_26_76_1
  | exact S 26 76 2 cell_26_76_2
  | exact S 26 76 3 cell_26_76_3
  | exact S 26 76 4 cell_26_76_4
  | exact S 26 76 5 cell_26_76_5
theorem cell_26_77_0 : C 26 77 0 := by decide +kernel
theorem cell_26_77_1 : C 26 77 1 := by decide +kernel
theorem cell_26_77_2 : C 26 77 2 := by decide +kernel
theorem cell_26_77_3 : C 26 77 3 := by decide +kernel
theorem cell_26_77_4 : C 26 77 4 := by decide +kernel
theorem cell_26_77_5 : C 26 77 5 := by decide +kernel
theorem row_26_77 : ThresholdAt 26 77 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 77 0 cell_26_77_0
  | exact S 26 77 1 cell_26_77_1
  | exact S 26 77 2 cell_26_77_2
  | exact S 26 77 3 cell_26_77_3
  | exact S 26 77 4 cell_26_77_4
  | exact S 26 77 5 cell_26_77_5
theorem cell_26_78_0 : C 26 78 0 := by decide +kernel
theorem cell_26_78_1 : C 26 78 1 := by decide +kernel
theorem cell_26_78_2 : C 26 78 2 := by decide +kernel
theorem cell_26_78_3 : C 26 78 3 := by decide +kernel
theorem cell_26_78_4 : C 26 78 4 := by decide +kernel
theorem cell_26_78_5 : C 26 78 5 := by decide +kernel
theorem row_26_78 : ThresholdAt 26 78 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 78 0 cell_26_78_0
  | exact S 26 78 1 cell_26_78_1
  | exact S 26 78 2 cell_26_78_2
  | exact S 26 78 3 cell_26_78_3
  | exact S 26 78 4 cell_26_78_4
  | exact S 26 78 5 cell_26_78_5
theorem cell_26_79_0 : C 26 79 0 := by decide +kernel
theorem cell_26_79_1 : C 26 79 1 := by decide +kernel
theorem cell_26_79_2 : C 26 79 2 := by decide +kernel
theorem cell_26_79_3 : C 26 79 3 := by decide +kernel
theorem cell_26_79_4 : C 26 79 4 := by decide +kernel
theorem cell_26_79_5 : C 26 79 5 := by decide +kernel
theorem row_26_79 : ThresholdAt 26 79 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 79 0 cell_26_79_0
  | exact S 26 79 1 cell_26_79_1
  | exact S 26 79 2 cell_26_79_2
  | exact S 26 79 3 cell_26_79_3
  | exact S 26 79 4 cell_26_79_4
  | exact S 26 79 5 cell_26_79_5
theorem cell_26_80_0 : C 26 80 0 := by decide +kernel
theorem cell_26_80_1 : C 26 80 1 := by decide +kernel
theorem cell_26_80_2 : C 26 80 2 := by decide +kernel
theorem cell_26_80_3 : C 26 80 3 := by decide +kernel
theorem cell_26_80_4 : C 26 80 4 := by decide +kernel
theorem cell_26_80_5 : C 26 80 5 := by decide +kernel
theorem row_26_80 : ThresholdAt 26 80 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 80 0 cell_26_80_0
  | exact S 26 80 1 cell_26_80_1
  | exact S 26 80 2 cell_26_80_2
  | exact S 26 80 3 cell_26_80_3
  | exact S 26 80 4 cell_26_80_4
  | exact S 26 80 5 cell_26_80_5
theorem cell_26_81_0 : C 26 81 0 := by decide +kernel
theorem cell_26_81_1 : C 26 81 1 := by decide +kernel
theorem cell_26_81_2 : C 26 81 2 := by decide +kernel
theorem cell_26_81_3 : C 26 81 3 := by decide +kernel
theorem cell_26_81_4 : C 26 81 4 := by decide +kernel
theorem cell_26_81_5 : C 26 81 5 := by decide +kernel
theorem row_26_81 : ThresholdAt 26 81 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 81 0 cell_26_81_0
  | exact S 26 81 1 cell_26_81_1
  | exact S 26 81 2 cell_26_81_2
  | exact S 26 81 3 cell_26_81_3
  | exact S 26 81 4 cell_26_81_4
  | exact S 26 81 5 cell_26_81_5
theorem cell_26_82_0 : C 26 82 0 := by decide +kernel
theorem cell_26_82_1 : C 26 82 1 := by decide +kernel
theorem cell_26_82_2 : C 26 82 2 := by decide +kernel
theorem cell_26_82_3 : C 26 82 3 := by decide +kernel
theorem cell_26_82_4 : C 26 82 4 := by decide +kernel
theorem cell_26_82_5 : C 26 82 5 := by decide +kernel
theorem row_26_82 : ThresholdAt 26 82 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 82 0 cell_26_82_0
  | exact S 26 82 1 cell_26_82_1
  | exact S 26 82 2 cell_26_82_2
  | exact S 26 82 3 cell_26_82_3
  | exact S 26 82 4 cell_26_82_4
  | exact S 26 82 5 cell_26_82_5
theorem cell_26_83_0 : C 26 83 0 := by decide +kernel
theorem cell_26_83_1 : C 26 83 1 := by decide +kernel
theorem cell_26_83_2 : C 26 83 2 := by decide +kernel
theorem cell_26_83_3 : C 26 83 3 := by decide +kernel
theorem cell_26_83_4 : C 26 83 4 := by decide +kernel
theorem cell_26_83_5 : C 26 83 5 := by decide +kernel
theorem row_26_83 : ThresholdAt 26 83 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 83 0 cell_26_83_0
  | exact S 26 83 1 cell_26_83_1
  | exact S 26 83 2 cell_26_83_2
  | exact S 26 83 3 cell_26_83_3
  | exact S 26 83 4 cell_26_83_4
  | exact S 26 83 5 cell_26_83_5
theorem cell_26_84_0 : C 26 84 0 := by decide +kernel
theorem cell_26_84_1 : C 26 84 1 := by decide +kernel
theorem cell_26_84_2 : C 26 84 2 := by decide +kernel
theorem cell_26_84_3 : C 26 84 3 := by decide +kernel
theorem cell_26_84_4 : C 26 84 4 := by decide +kernel
theorem cell_26_84_5 : C 26 84 5 := by decide +kernel
theorem row_26_84 : ThresholdAt 26 84 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 84 0 cell_26_84_0
  | exact S 26 84 1 cell_26_84_1
  | exact S 26 84 2 cell_26_84_2
  | exact S 26 84 3 cell_26_84_3
  | exact S 26 84 4 cell_26_84_4
  | exact S 26 84 5 cell_26_84_5
theorem cell_26_85_0 : C 26 85 0 := by decide +kernel
theorem cell_26_85_1 : C 26 85 1 := by decide +kernel
theorem cell_26_85_2 : C 26 85 2 := by decide +kernel
theorem cell_26_85_3 : C 26 85 3 := by decide +kernel
theorem cell_26_85_4 : C 26 85 4 := by decide +kernel
theorem cell_26_85_5 : C 26 85 5 := by decide +kernel
theorem row_26_85 : ThresholdAt 26 85 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 85 0 cell_26_85_0
  | exact S 26 85 1 cell_26_85_1
  | exact S 26 85 2 cell_26_85_2
  | exact S 26 85 3 cell_26_85_3
  | exact S 26 85 4 cell_26_85_4
  | exact S 26 85 5 cell_26_85_5
theorem cell_26_86_0 : C 26 86 0 := by decide +kernel
theorem cell_26_86_1 : C 26 86 1 := by decide +kernel
theorem cell_26_86_2 : C 26 86 2 := by decide +kernel
theorem cell_26_86_3 : C 26 86 3 := by decide +kernel
theorem cell_26_86_4 : C 26 86 4 := by decide +kernel
theorem cell_26_86_5 : C 26 86 5 := by decide +kernel
theorem row_26_86 : ThresholdAt 26 86 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 86 0 cell_26_86_0
  | exact S 26 86 1 cell_26_86_1
  | exact S 26 86 2 cell_26_86_2
  | exact S 26 86 3 cell_26_86_3
  | exact S 26 86 4 cell_26_86_4
  | exact S 26 86 5 cell_26_86_5
theorem cell_26_87_0 : C 26 87 0 := by decide +kernel
theorem cell_26_87_1 : C 26 87 1 := by decide +kernel
theorem cell_26_87_2 : C 26 87 2 := by decide +kernel
theorem cell_26_87_3 : C 26 87 3 := by decide +kernel
theorem cell_26_87_4 : C 26 87 4 := by decide +kernel
theorem cell_26_87_5 : C 26 87 5 := by decide +kernel
theorem row_26_87 : ThresholdAt 26 87 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 87 0 cell_26_87_0
  | exact S 26 87 1 cell_26_87_1
  | exact S 26 87 2 cell_26_87_2
  | exact S 26 87 3 cell_26_87_3
  | exact S 26 87 4 cell_26_87_4
  | exact S 26 87 5 cell_26_87_5
theorem cell_26_88_0 : C 26 88 0 := by decide +kernel
theorem cell_26_88_1 : C 26 88 1 := by decide +kernel
theorem cell_26_88_2 : C 26 88 2 := by decide +kernel
theorem cell_26_88_3 : C 26 88 3 := by decide +kernel
theorem cell_26_88_4 : C 26 88 4 := by decide +kernel
theorem cell_26_88_5 : C 26 88 5 := by decide +kernel
theorem row_26_88 : ThresholdAt 26 88 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 88 0 cell_26_88_0
  | exact S 26 88 1 cell_26_88_1
  | exact S 26 88 2 cell_26_88_2
  | exact S 26 88 3 cell_26_88_3
  | exact S 26 88 4 cell_26_88_4
  | exact S 26 88 5 cell_26_88_5
theorem cell_26_89_0 : C 26 89 0 := by decide +kernel
theorem cell_26_89_1 : C 26 89 1 := by decide +kernel
theorem cell_26_89_2 : C 26 89 2 := by decide +kernel
theorem cell_26_89_3 : C 26 89 3 := by decide +kernel
theorem cell_26_89_4 : C 26 89 4 := by decide +kernel
theorem cell_26_89_5 : C 26 89 5 := by decide +kernel
theorem row_26_89 : ThresholdAt 26 89 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 89 0 cell_26_89_0
  | exact S 26 89 1 cell_26_89_1
  | exact S 26 89 2 cell_26_89_2
  | exact S 26 89 3 cell_26_89_3
  | exact S 26 89 4 cell_26_89_4
  | exact S 26 89 5 cell_26_89_5
theorem cell_26_90_0 : C 26 90 0 := by decide +kernel
theorem cell_26_90_1 : C 26 90 1 := by decide +kernel
theorem cell_26_90_2 : C 26 90 2 := by decide +kernel
theorem cell_26_90_3 : C 26 90 3 := by decide +kernel
theorem cell_26_90_4 : C 26 90 4 := by decide +kernel
theorem cell_26_90_5 : C 26 90 5 := by decide +kernel
theorem row_26_90 : ThresholdAt 26 90 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 90 0 cell_26_90_0
  | exact S 26 90 1 cell_26_90_1
  | exact S 26 90 2 cell_26_90_2
  | exact S 26 90 3 cell_26_90_3
  | exact S 26 90 4 cell_26_90_4
  | exact S 26 90 5 cell_26_90_5
theorem cell_26_91_0 : C 26 91 0 := by decide +kernel
theorem cell_26_91_1 : C 26 91 1 := by decide +kernel
theorem cell_26_91_2 : C 26 91 2 := by decide +kernel
theorem cell_26_91_3 : C 26 91 3 := by decide +kernel
theorem cell_26_91_4 : C 26 91 4 := by decide +kernel
theorem cell_26_91_5 : C 26 91 5 := by decide +kernel
theorem row_26_91 : ThresholdAt 26 91 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 91 0 cell_26_91_0
  | exact S 26 91 1 cell_26_91_1
  | exact S 26 91 2 cell_26_91_2
  | exact S 26 91 3 cell_26_91_3
  | exact S 26 91 4 cell_26_91_4
  | exact S 26 91 5 cell_26_91_5
theorem cell_26_92_0 : C 26 92 0 := by decide +kernel
theorem cell_26_92_1 : C 26 92 1 := by decide +kernel
theorem cell_26_92_2 : C 26 92 2 := by decide +kernel
theorem cell_26_92_3 : C 26 92 3 := by decide +kernel
theorem cell_26_92_4 : C 26 92 4 := by decide +kernel
theorem cell_26_92_5 : C 26 92 5 := by decide +kernel
theorem row_26_92 : ThresholdAt 26 92 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 92 0 cell_26_92_0
  | exact S 26 92 1 cell_26_92_1
  | exact S 26 92 2 cell_26_92_2
  | exact S 26 92 3 cell_26_92_3
  | exact S 26 92 4 cell_26_92_4
  | exact S 26 92 5 cell_26_92_5
theorem cell_26_93_0 : C 26 93 0 := by decide +kernel
theorem cell_26_93_1 : C 26 93 1 := by decide +kernel
theorem cell_26_93_2 : C 26 93 2 := by decide +kernel
theorem cell_26_93_3 : C 26 93 3 := by decide +kernel
theorem cell_26_93_4 : C 26 93 4 := by decide +kernel
theorem cell_26_93_5 : C 26 93 5 := by decide +kernel
theorem row_26_93 : ThresholdAt 26 93 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 93 0 cell_26_93_0
  | exact S 26 93 1 cell_26_93_1
  | exact S 26 93 2 cell_26_93_2
  | exact S 26 93 3 cell_26_93_3
  | exact S 26 93 4 cell_26_93_4
  | exact S 26 93 5 cell_26_93_5
theorem cell_26_94_0 : C 26 94 0 := by decide +kernel
theorem cell_26_94_1 : C 26 94 1 := by decide +kernel
theorem cell_26_94_2 : C 26 94 2 := by decide +kernel
theorem cell_26_94_3 : C 26 94 3 := by decide +kernel
theorem cell_26_94_4 : C 26 94 4 := by decide +kernel
theorem cell_26_94_5 : C 26 94 5 := by decide +kernel
theorem row_26_94 : ThresholdAt 26 94 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 94 0 cell_26_94_0
  | exact S 26 94 1 cell_26_94_1
  | exact S 26 94 2 cell_26_94_2
  | exact S 26 94 3 cell_26_94_3
  | exact S 26 94 4 cell_26_94_4
  | exact S 26 94 5 cell_26_94_5
theorem cell_26_95_0 : C 26 95 0 := by decide +kernel
theorem cell_26_95_1 : C 26 95 1 := by decide +kernel
theorem cell_26_95_2 : C 26 95 2 := by decide +kernel
theorem cell_26_95_3 : C 26 95 3 := by decide +kernel
theorem cell_26_95_4 : C 26 95 4 := by decide +kernel
theorem cell_26_95_5 : C 26 95 5 := by decide +kernel
theorem row_26_95 : ThresholdAt 26 95 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 95 0 cell_26_95_0
  | exact S 26 95 1 cell_26_95_1
  | exact S 26 95 2 cell_26_95_2
  | exact S 26 95 3 cell_26_95_3
  | exact S 26 95 4 cell_26_95_4
  | exact S 26 95 5 cell_26_95_5
theorem cell_26_96_0 : C 26 96 0 := by decide +kernel
theorem cell_26_96_1 : C 26 96 1 := by decide +kernel
theorem cell_26_96_2 : C 26 96 2 := by decide +kernel
theorem cell_26_96_3 : C 26 96 3 := by decide +kernel
theorem cell_26_96_4 : C 26 96 4 := by decide +kernel
theorem cell_26_96_5 : C 26 96 5 := by decide +kernel
theorem row_26_96 : ThresholdAt 26 96 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 96 0 cell_26_96_0
  | exact S 26 96 1 cell_26_96_1
  | exact S 26 96 2 cell_26_96_2
  | exact S 26 96 3 cell_26_96_3
  | exact S 26 96 4 cell_26_96_4
  | exact S 26 96 5 cell_26_96_5
theorem cell_26_97_0 : C 26 97 0 := by decide +kernel
theorem cell_26_97_1 : C 26 97 1 := by decide +kernel
theorem cell_26_97_2 : C 26 97 2 := by decide +kernel
theorem cell_26_97_3 : C 26 97 3 := by decide +kernel
theorem cell_26_97_4 : C 26 97 4 := by decide +kernel
theorem cell_26_97_5 : C 26 97 5 := by decide +kernel
theorem row_26_97 : ThresholdAt 26 97 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 97 0 cell_26_97_0
  | exact S 26 97 1 cell_26_97_1
  | exact S 26 97 2 cell_26_97_2
  | exact S 26 97 3 cell_26_97_3
  | exact S 26 97 4 cell_26_97_4
  | exact S 26 97 5 cell_26_97_5
theorem cell_26_98_0 : C 26 98 0 := by decide +kernel
theorem cell_26_98_1 : C 26 98 1 := by decide +kernel
theorem cell_26_98_2 : C 26 98 2 := by decide +kernel
theorem cell_26_98_3 : C 26 98 3 := by decide +kernel
theorem cell_26_98_4 : C 26 98 4 := by decide +kernel
theorem cell_26_98_5 : C 26 98 5 := by decide +kernel
theorem row_26_98 : ThresholdAt 26 98 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 98 0 cell_26_98_0
  | exact S 26 98 1 cell_26_98_1
  | exact S 26 98 2 cell_26_98_2
  | exact S 26 98 3 cell_26_98_3
  | exact S 26 98 4 cell_26_98_4
  | exact S 26 98 5 cell_26_98_5
theorem cell_26_99_0 : C 26 99 0 := by decide +kernel
theorem cell_26_99_1 : C 26 99 1 := by decide +kernel
theorem cell_26_99_2 : C 26 99 2 := by decide +kernel
theorem cell_26_99_3 : C 26 99 3 := by decide +kernel
theorem cell_26_99_4 : C 26 99 4 := by decide +kernel
theorem cell_26_99_5 : C 26 99 5 := by decide +kernel
theorem row_26_99 : ThresholdAt 26 99 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 99 0 cell_26_99_0
  | exact S 26 99 1 cell_26_99_1
  | exact S 26 99 2 cell_26_99_2
  | exact S 26 99 3 cell_26_99_3
  | exact S 26 99 4 cell_26_99_4
  | exact S 26 99 5 cell_26_99_5
theorem cell_26_100_0 : C 26 100 0 := by decide +kernel
theorem cell_26_100_1 : C 26 100 1 := by decide +kernel
theorem cell_26_100_2 : C 26 100 2 := by decide +kernel
theorem cell_26_100_3 : C 26 100 3 := by decide +kernel
theorem cell_26_100_4 : C 26 100 4 := by decide +kernel
theorem cell_26_100_5 : C 26 100 5 := by decide +kernel
theorem row_26_100 : ThresholdAt 26 100 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 100 0 cell_26_100_0
  | exact S 26 100 1 cell_26_100_1
  | exact S 26 100 2 cell_26_100_2
  | exact S 26 100 3 cell_26_100_3
  | exact S 26 100 4 cell_26_100_4
  | exact S 26 100 5 cell_26_100_5
theorem cell_26_101_0 : C 26 101 0 := by decide +kernel
theorem cell_26_101_1 : C 26 101 1 := by decide +kernel
theorem cell_26_101_2 : C 26 101 2 := by decide +kernel
theorem cell_26_101_3 : C 26 101 3 := by decide +kernel
theorem cell_26_101_4 : C 26 101 4 := by decide +kernel
theorem cell_26_101_5 : C 26 101 5 := by decide +kernel
theorem row_26_101 : ThresholdAt 26 101 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 101 0 cell_26_101_0
  | exact S 26 101 1 cell_26_101_1
  | exact S 26 101 2 cell_26_101_2
  | exact S 26 101 3 cell_26_101_3
  | exact S 26 101 4 cell_26_101_4
  | exact S 26 101 5 cell_26_101_5
theorem cell_26_102_0 : C 26 102 0 := by decide +kernel
theorem cell_26_102_1 : C 26 102 1 := by decide +kernel
theorem cell_26_102_2 : C 26 102 2 := by decide +kernel
theorem cell_26_102_3 : C 26 102 3 := by decide +kernel
theorem cell_26_102_4 : C 26 102 4 := by decide +kernel
theorem cell_26_102_5 : C 26 102 5 := by decide +kernel
theorem row_26_102 : ThresholdAt 26 102 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 102 0 cell_26_102_0
  | exact S 26 102 1 cell_26_102_1
  | exact S 26 102 2 cell_26_102_2
  | exact S 26 102 3 cell_26_102_3
  | exact S 26 102 4 cell_26_102_4
  | exact S 26 102 5 cell_26_102_5
theorem cell_26_103_0 : C 26 103 0 := by decide +kernel
theorem cell_26_103_1 : C 26 103 1 := by decide +kernel
theorem cell_26_103_2 : C 26 103 2 := by decide +kernel
theorem cell_26_103_3 : C 26 103 3 := by decide +kernel
theorem cell_26_103_4 : C 26 103 4 := by decide +kernel
theorem cell_26_103_5 : C 26 103 5 := by decide +kernel
theorem row_26_103 : ThresholdAt 26 103 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 103 0 cell_26_103_0
  | exact S 26 103 1 cell_26_103_1
  | exact S 26 103 2 cell_26_103_2
  | exact S 26 103 3 cell_26_103_3
  | exact S 26 103 4 cell_26_103_4
  | exact S 26 103 5 cell_26_103_5
theorem cell_26_104_0 : C 26 104 0 := by decide +kernel
theorem cell_26_104_1 : C 26 104 1 := by decide +kernel
theorem cell_26_104_2 : C 26 104 2 := by decide +kernel
theorem cell_26_104_3 : C 26 104 3 := by decide +kernel
theorem cell_26_104_4 : C 26 104 4 := by decide +kernel
theorem cell_26_104_5 : C 26 104 5 := by decide +kernel
theorem row_26_104 : ThresholdAt 26 104 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 104 0 cell_26_104_0
  | exact S 26 104 1 cell_26_104_1
  | exact S 26 104 2 cell_26_104_2
  | exact S 26 104 3 cell_26_104_3
  | exact S 26 104 4 cell_26_104_4
  | exact S 26 104 5 cell_26_104_5
theorem cell_26_105_0 : C 26 105 0 := by decide +kernel
theorem cell_26_105_1 : C 26 105 1 := by decide +kernel
theorem cell_26_105_2 : C 26 105 2 := by decide +kernel
theorem cell_26_105_3 : C 26 105 3 := by decide +kernel
theorem cell_26_105_4 : C 26 105 4 := by decide +kernel
theorem cell_26_105_5 : C 26 105 5 := by decide +kernel
theorem row_26_105 : ThresholdAt 26 105 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 105 0 cell_26_105_0
  | exact S 26 105 1 cell_26_105_1
  | exact S 26 105 2 cell_26_105_2
  | exact S 26 105 3 cell_26_105_3
  | exact S 26 105 4 cell_26_105_4
  | exact S 26 105 5 cell_26_105_5
theorem cell_26_106_0 : C 26 106 0 := by decide +kernel
theorem cell_26_106_1 : C 26 106 1 := by decide +kernel
theorem cell_26_106_2 : C 26 106 2 := by decide +kernel
theorem cell_26_106_3 : C 26 106 3 := by decide +kernel
theorem cell_26_106_4 : C 26 106 4 := by decide +kernel
theorem cell_26_106_5 : C 26 106 5 := by decide +kernel
theorem row_26_106 : ThresholdAt 26 106 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 106 0 cell_26_106_0
  | exact S 26 106 1 cell_26_106_1
  | exact S 26 106 2 cell_26_106_2
  | exact S 26 106 3 cell_26_106_3
  | exact S 26 106 4 cell_26_106_4
  | exact S 26 106 5 cell_26_106_5
theorem cell_26_107_0 : C 26 107 0 := by decide +kernel
theorem cell_26_107_1 : C 26 107 1 := by decide +kernel
theorem cell_26_107_2 : C 26 107 2 := by decide +kernel
theorem cell_26_107_3 : C 26 107 3 := by decide +kernel
theorem cell_26_107_4 : C 26 107 4 := by decide +kernel
theorem cell_26_107_5 : C 26 107 5 := by decide +kernel
theorem row_26_107 : ThresholdAt 26 107 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 107 0 cell_26_107_0
  | exact S 26 107 1 cell_26_107_1
  | exact S 26 107 2 cell_26_107_2
  | exact S 26 107 3 cell_26_107_3
  | exact S 26 107 4 cell_26_107_4
  | exact S 26 107 5 cell_26_107_5
theorem cell_26_108_0 : C 26 108 0 := by decide +kernel
theorem cell_26_108_1 : C 26 108 1 := by decide +kernel
theorem cell_26_108_2 : C 26 108 2 := by decide +kernel
theorem cell_26_108_3 : C 26 108 3 := by decide +kernel
theorem cell_26_108_4 : C 26 108 4 := by decide +kernel
theorem cell_26_108_5 : C 26 108 5 := by decide +kernel
theorem row_26_108 : ThresholdAt 26 108 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 108 0 cell_26_108_0
  | exact S 26 108 1 cell_26_108_1
  | exact S 26 108 2 cell_26_108_2
  | exact S 26 108 3 cell_26_108_3
  | exact S 26 108 4 cell_26_108_4
  | exact S 26 108 5 cell_26_108_5
theorem cell_26_109_0 : C 26 109 0 := by decide +kernel
theorem cell_26_109_1 : C 26 109 1 := by decide +kernel
theorem cell_26_109_2 : C 26 109 2 := by decide +kernel
theorem cell_26_109_3 : C 26 109 3 := by decide +kernel
theorem cell_26_109_4 : C 26 109 4 := by decide +kernel
theorem cell_26_109_5 : C 26 109 5 := by decide +kernel
theorem row_26_109 : ThresholdAt 26 109 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 109 0 cell_26_109_0
  | exact S 26 109 1 cell_26_109_1
  | exact S 26 109 2 cell_26_109_2
  | exact S 26 109 3 cell_26_109_3
  | exact S 26 109 4 cell_26_109_4
  | exact S 26 109 5 cell_26_109_5
theorem cell_26_110_0 : C 26 110 0 := by decide +kernel
theorem cell_26_110_1 : C 26 110 1 := by decide +kernel
theorem cell_26_110_2 : C 26 110 2 := by decide +kernel
theorem cell_26_110_3 : C 26 110 3 := by decide +kernel
theorem cell_26_110_4 : C 26 110 4 := by decide +kernel
theorem cell_26_110_5 : C 26 110 5 := by decide +kernel
theorem row_26_110 : ThresholdAt 26 110 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 110 0 cell_26_110_0
  | exact S 26 110 1 cell_26_110_1
  | exact S 26 110 2 cell_26_110_2
  | exact S 26 110 3 cell_26_110_3
  | exact S 26 110 4 cell_26_110_4
  | exact S 26 110 5 cell_26_110_5
theorem cell_26_111_0 : C 26 111 0 := by decide +kernel
theorem cell_26_111_1 : C 26 111 1 := by decide +kernel
theorem cell_26_111_2 : C 26 111 2 := by decide +kernel
theorem cell_26_111_3 : C 26 111 3 := by decide +kernel
theorem cell_26_111_4 : C 26 111 4 := by decide +kernel
theorem cell_26_111_5 : C 26 111 5 := by decide +kernel
theorem row_26_111 : ThresholdAt 26 111 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 111 0 cell_26_111_0
  | exact S 26 111 1 cell_26_111_1
  | exact S 26 111 2 cell_26_111_2
  | exact S 26 111 3 cell_26_111_3
  | exact S 26 111 4 cell_26_111_4
  | exact S 26 111 5 cell_26_111_5
theorem cell_26_112_0 : C 26 112 0 := by decide +kernel
theorem cell_26_112_1 : C 26 112 1 := by decide +kernel
theorem cell_26_112_2 : C 26 112 2 := by decide +kernel
theorem cell_26_112_3 : C 26 112 3 := by decide +kernel
theorem cell_26_112_4 : C 26 112 4 := by decide +kernel
theorem cell_26_112_5 : C 26 112 5 := by decide +kernel
theorem row_26_112 : ThresholdAt 26 112 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 112 0 cell_26_112_0
  | exact S 26 112 1 cell_26_112_1
  | exact S 26 112 2 cell_26_112_2
  | exact S 26 112 3 cell_26_112_3
  | exact S 26 112 4 cell_26_112_4
  | exact S 26 112 5 cell_26_112_5
theorem cell_26_113_0 : C 26 113 0 := by decide +kernel
theorem cell_26_113_1 : C 26 113 1 := by decide +kernel
theorem cell_26_113_2 : C 26 113 2 := by decide +kernel
theorem cell_26_113_3 : C 26 113 3 := by decide +kernel
theorem cell_26_113_4 : C 26 113 4 := by decide +kernel
theorem cell_26_113_5 : C 26 113 5 := by decide +kernel
theorem row_26_113 : ThresholdAt 26 113 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 26 113 0 cell_26_113_0
  | exact S 26 113 1 cell_26_113_1
  | exact S 26 113 2 cell_26_113_2
  | exact S 26 113 3 cell_26_113_3
  | exact S 26 113 4 cell_26_113_4
  | exact S 26 113 5 cell_26_113_5
theorem checkedR26 : ∀ V ∈ List.range 114, ThresholdAt 26 V := by
  intro V hV
  have hv : V < 114 := List.mem_range.mp hV
  by_cases h0_114 : V < 57
  · by_cases h0_57 : V < 28
    · by_cases h0_28 : V < 14
      · by_cases h0_14 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have he : V = 0 := by omega
              subst V
              exact row_26_0
            · by_cases h1_3 : V < 2
              · have he : V = 1 := by omega
                subst V
                exact row_26_1
              · have he : V = 2 := by omega
                subst V
                exact row_26_2
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have he : V = 3 := by omega
                subst V
                exact row_26_3
              · have he : V = 4 := by omega
                subst V
                exact row_26_4
            · by_cases h5_7 : V < 6
              · have he : V = 5 := by omega
                subst V
                exact row_26_5
              · have he : V = 6 := by omega
                subst V
                exact row_26_6
        · by_cases h7_14 : V < 10
          · by_cases h7_10 : V < 8
            · have he : V = 7 := by omega
              subst V
              exact row_26_7
            · by_cases h8_10 : V < 9
              · have he : V = 8 := by omega
                subst V
                exact row_26_8
              · have he : V = 9 := by omega
                subst V
                exact row_26_9
          · by_cases h10_14 : V < 12
            · by_cases h10_12 : V < 11
              · have he : V = 10 := by omega
                subst V
                exact row_26_10
              · have he : V = 11 := by omega
                subst V
                exact row_26_11
            · by_cases h12_14 : V < 13
              · have he : V = 12 := by omega
                subst V
                exact row_26_12
              · have he : V = 13 := by omega
                subst V
                exact row_26_13
      · by_cases h14_28 : V < 21
        · by_cases h14_21 : V < 17
          · by_cases h14_17 : V < 15
            · have he : V = 14 := by omega
              subst V
              exact row_26_14
            · by_cases h15_17 : V < 16
              · have he : V = 15 := by omega
                subst V
                exact row_26_15
              · have he : V = 16 := by omega
                subst V
                exact row_26_16
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have he : V = 17 := by omega
                subst V
                exact row_26_17
              · have he : V = 18 := by omega
                subst V
                exact row_26_18
            · by_cases h19_21 : V < 20
              · have he : V = 19 := by omega
                subst V
                exact row_26_19
              · have he : V = 20 := by omega
                subst V
                exact row_26_20
        · by_cases h21_28 : V < 24
          · by_cases h21_24 : V < 22
            · have he : V = 21 := by omega
              subst V
              exact row_26_21
            · by_cases h22_24 : V < 23
              · have he : V = 22 := by omega
                subst V
                exact row_26_22
              · have he : V = 23 := by omega
                subst V
                exact row_26_23
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have he : V = 24 := by omega
                subst V
                exact row_26_24
              · have he : V = 25 := by omega
                subst V
                exact row_26_25
            · by_cases h26_28 : V < 27
              · have he : V = 26 := by omega
                subst V
                exact row_26_26
              · have he : V = 27 := by omega
                subst V
                exact row_26_27
    · by_cases h28_57 : V < 42
      · by_cases h28_42 : V < 35
        · by_cases h28_35 : V < 31
          · by_cases h28_31 : V < 29
            · have he : V = 28 := by omega
              subst V
              exact row_26_28
            · by_cases h29_31 : V < 30
              · have he : V = 29 := by omega
                subst V
                exact row_26_29
              · have he : V = 30 := by omega
                subst V
                exact row_26_30
          · by_cases h31_35 : V < 33
            · by_cases h31_33 : V < 32
              · have he : V = 31 := by omega
                subst V
                exact row_26_31
              · have he : V = 32 := by omega
                subst V
                exact row_26_32
            · by_cases h33_35 : V < 34
              · have he : V = 33 := by omega
                subst V
                exact row_26_33
              · have he : V = 34 := by omega
                subst V
                exact row_26_34
        · by_cases h35_42 : V < 38
          · by_cases h35_38 : V < 36
            · have he : V = 35 := by omega
              subst V
              exact row_26_35
            · by_cases h36_38 : V < 37
              · have he : V = 36 := by omega
                subst V
                exact row_26_36
              · have he : V = 37 := by omega
                subst V
                exact row_26_37
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have he : V = 38 := by omega
                subst V
                exact row_26_38
              · have he : V = 39 := by omega
                subst V
                exact row_26_39
            · by_cases h40_42 : V < 41
              · have he : V = 40 := by omega
                subst V
                exact row_26_40
              · have he : V = 41 := by omega
                subst V
                exact row_26_41
      · by_cases h42_57 : V < 49
        · by_cases h42_49 : V < 45
          · by_cases h42_45 : V < 43
            · have he : V = 42 := by omega
              subst V
              exact row_26_42
            · by_cases h43_45 : V < 44
              · have he : V = 43 := by omega
                subst V
                exact row_26_43
              · have he : V = 44 := by omega
                subst V
                exact row_26_44
          · by_cases h45_49 : V < 47
            · by_cases h45_47 : V < 46
              · have he : V = 45 := by omega
                subst V
                exact row_26_45
              · have he : V = 46 := by omega
                subst V
                exact row_26_46
            · by_cases h47_49 : V < 48
              · have he : V = 47 := by omega
                subst V
                exact row_26_47
              · have he : V = 48 := by omega
                subst V
                exact row_26_48
        · by_cases h49_57 : V < 53
          · by_cases h49_53 : V < 51
            · by_cases h49_51 : V < 50
              · have he : V = 49 := by omega
                subst V
                exact row_26_49
              · have he : V = 50 := by omega
                subst V
                exact row_26_50
            · by_cases h51_53 : V < 52
              · have he : V = 51 := by omega
                subst V
                exact row_26_51
              · have he : V = 52 := by omega
                subst V
                exact row_26_52
          · by_cases h53_57 : V < 55
            · by_cases h53_55 : V < 54
              · have he : V = 53 := by omega
                subst V
                exact row_26_53
              · have he : V = 54 := by omega
                subst V
                exact row_26_54
            · by_cases h55_57 : V < 56
              · have he : V = 55 := by omega
                subst V
                exact row_26_55
              · have he : V = 56 := by omega
                subst V
                exact row_26_56
  · by_cases h57_114 : V < 85
    · by_cases h57_85 : V < 71
      · by_cases h57_71 : V < 64
        · by_cases h57_64 : V < 60
          · by_cases h57_60 : V < 58
            · have he : V = 57 := by omega
              subst V
              exact row_26_57
            · by_cases h58_60 : V < 59
              · have he : V = 58 := by omega
                subst V
                exact row_26_58
              · have he : V = 59 := by omega
                subst V
                exact row_26_59
          · by_cases h60_64 : V < 62
            · by_cases h60_62 : V < 61
              · have he : V = 60 := by omega
                subst V
                exact row_26_60
              · have he : V = 61 := by omega
                subst V
                exact row_26_61
            · by_cases h62_64 : V < 63
              · have he : V = 62 := by omega
                subst V
                exact row_26_62
              · have he : V = 63 := by omega
                subst V
                exact row_26_63
        · by_cases h64_71 : V < 67
          · by_cases h64_67 : V < 65
            · have he : V = 64 := by omega
              subst V
              exact row_26_64
            · by_cases h65_67 : V < 66
              · have he : V = 65 := by omega
                subst V
                exact row_26_65
              · have he : V = 66 := by omega
                subst V
                exact row_26_66
          · by_cases h67_71 : V < 69
            · by_cases h67_69 : V < 68
              · have he : V = 67 := by omega
                subst V
                exact row_26_67
              · have he : V = 68 := by omega
                subst V
                exact row_26_68
            · by_cases h69_71 : V < 70
              · have he : V = 69 := by omega
                subst V
                exact row_26_69
              · have he : V = 70 := by omega
                subst V
                exact row_26_70
      · by_cases h71_85 : V < 78
        · by_cases h71_78 : V < 74
          · by_cases h71_74 : V < 72
            · have he : V = 71 := by omega
              subst V
              exact row_26_71
            · by_cases h72_74 : V < 73
              · have he : V = 72 := by omega
                subst V
                exact row_26_72
              · have he : V = 73 := by omega
                subst V
                exact row_26_73
          · by_cases h74_78 : V < 76
            · by_cases h74_76 : V < 75
              · have he : V = 74 := by omega
                subst V
                exact row_26_74
              · have he : V = 75 := by omega
                subst V
                exact row_26_75
            · by_cases h76_78 : V < 77
              · have he : V = 76 := by omega
                subst V
                exact row_26_76
              · have he : V = 77 := by omega
                subst V
                exact row_26_77
        · by_cases h78_85 : V < 81
          · by_cases h78_81 : V < 79
            · have he : V = 78 := by omega
              subst V
              exact row_26_78
            · by_cases h79_81 : V < 80
              · have he : V = 79 := by omega
                subst V
                exact row_26_79
              · have he : V = 80 := by omega
                subst V
                exact row_26_80
          · by_cases h81_85 : V < 83
            · by_cases h81_83 : V < 82
              · have he : V = 81 := by omega
                subst V
                exact row_26_81
              · have he : V = 82 := by omega
                subst V
                exact row_26_82
            · by_cases h83_85 : V < 84
              · have he : V = 83 := by omega
                subst V
                exact row_26_83
              · have he : V = 84 := by omega
                subst V
                exact row_26_84
    · by_cases h85_114 : V < 99
      · by_cases h85_99 : V < 92
        · by_cases h85_92 : V < 88
          · by_cases h85_88 : V < 86
            · have he : V = 85 := by omega
              subst V
              exact row_26_85
            · by_cases h86_88 : V < 87
              · have he : V = 86 := by omega
                subst V
                exact row_26_86
              · have he : V = 87 := by omega
                subst V
                exact row_26_87
          · by_cases h88_92 : V < 90
            · by_cases h88_90 : V < 89
              · have he : V = 88 := by omega
                subst V
                exact row_26_88
              · have he : V = 89 := by omega
                subst V
                exact row_26_89
            · by_cases h90_92 : V < 91
              · have he : V = 90 := by omega
                subst V
                exact row_26_90
              · have he : V = 91 := by omega
                subst V
                exact row_26_91
        · by_cases h92_99 : V < 95
          · by_cases h92_95 : V < 93
            · have he : V = 92 := by omega
              subst V
              exact row_26_92
            · by_cases h93_95 : V < 94
              · have he : V = 93 := by omega
                subst V
                exact row_26_93
              · have he : V = 94 := by omega
                subst V
                exact row_26_94
          · by_cases h95_99 : V < 97
            · by_cases h95_97 : V < 96
              · have he : V = 95 := by omega
                subst V
                exact row_26_95
              · have he : V = 96 := by omega
                subst V
                exact row_26_96
            · by_cases h97_99 : V < 98
              · have he : V = 97 := by omega
                subst V
                exact row_26_97
              · have he : V = 98 := by omega
                subst V
                exact row_26_98
      · by_cases h99_114 : V < 106
        · by_cases h99_106 : V < 102
          · by_cases h99_102 : V < 100
            · have he : V = 99 := by omega
              subst V
              exact row_26_99
            · by_cases h100_102 : V < 101
              · have he : V = 100 := by omega
                subst V
                exact row_26_100
              · have he : V = 101 := by omega
                subst V
                exact row_26_101
          · by_cases h102_106 : V < 104
            · by_cases h102_104 : V < 103
              · have he : V = 102 := by omega
                subst V
                exact row_26_102
              · have he : V = 103 := by omega
                subst V
                exact row_26_103
            · by_cases h104_106 : V < 105
              · have he : V = 104 := by omega
                subst V
                exact row_26_104
              · have he : V = 105 := by omega
                subst V
                exact row_26_105
        · by_cases h106_114 : V < 110
          · by_cases h106_110 : V < 108
            · by_cases h106_108 : V < 107
              · have he : V = 106 := by omega
                subst V
                exact row_26_106
              · have he : V = 107 := by omega
                subst V
                exact row_26_107
            · by_cases h108_110 : V < 109
              · have he : V = 108 := by omega
                subst V
                exact row_26_108
              · have he : V = 109 := by omega
                subst V
                exact row_26_109
          · by_cases h110_114 : V < 112
            · by_cases h110_112 : V < 111
              · have he : V = 110 := by omega
                subst V
                exact row_26_110
              · have he : V = 111 := by omega
                subst V
                exact row_26_111
            · by_cases h112_114 : V < 113
              · have he : V = 112 := by omega
                subst V
                exact row_26_112
              · have he : V = 113 := by omega
                subst V
                exact row_26_113
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
