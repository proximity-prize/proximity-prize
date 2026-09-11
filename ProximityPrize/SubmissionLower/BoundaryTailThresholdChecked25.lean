import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked24

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_25_0_0 : C 25 0 0 := by decide +kernel
theorem cell_25_0_1 : C 25 0 1 := by decide +kernel
theorem cell_25_0_2 : C 25 0 2 := by decide +kernel
theorem cell_25_0_3 : C 25 0 3 := by decide +kernel
theorem cell_25_0_4 : C 25 0 4 := by decide +kernel
theorem cell_25_0_5 : C 25 0 5 := by decide +kernel
theorem row_25_0 : ThresholdAt 25 0 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 0 0 cell_25_0_0
  | exact S 25 0 1 cell_25_0_1
  | exact S 25 0 2 cell_25_0_2
  | exact S 25 0 3 cell_25_0_3
  | exact S 25 0 4 cell_25_0_4
  | exact S 25 0 5 cell_25_0_5
theorem cell_25_1_0 : C 25 1 0 := by decide +kernel
theorem cell_25_1_1 : C 25 1 1 := by decide +kernel
theorem cell_25_1_2 : C 25 1 2 := by decide +kernel
theorem cell_25_1_3 : C 25 1 3 := by decide +kernel
theorem cell_25_1_4 : C 25 1 4 := by decide +kernel
theorem cell_25_1_5 : C 25 1 5 := by decide +kernel
theorem row_25_1 : ThresholdAt 25 1 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 1 0 cell_25_1_0
  | exact S 25 1 1 cell_25_1_1
  | exact S 25 1 2 cell_25_1_2
  | exact S 25 1 3 cell_25_1_3
  | exact S 25 1 4 cell_25_1_4
  | exact S 25 1 5 cell_25_1_5
theorem cell_25_2_0 : C 25 2 0 := by decide +kernel
theorem cell_25_2_1 : C 25 2 1 := by decide +kernel
theorem cell_25_2_2 : C 25 2 2 := by decide +kernel
theorem cell_25_2_3 : C 25 2 3 := by decide +kernel
theorem cell_25_2_4 : C 25 2 4 := by decide +kernel
theorem cell_25_2_5 : C 25 2 5 := by decide +kernel
theorem row_25_2 : ThresholdAt 25 2 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 2 0 cell_25_2_0
  | exact S 25 2 1 cell_25_2_1
  | exact S 25 2 2 cell_25_2_2
  | exact S 25 2 3 cell_25_2_3
  | exact S 25 2 4 cell_25_2_4
  | exact S 25 2 5 cell_25_2_5
theorem cell_25_3_0 : C 25 3 0 := by decide +kernel
theorem cell_25_3_1 : C 25 3 1 := by decide +kernel
theorem cell_25_3_2 : C 25 3 2 := by decide +kernel
theorem cell_25_3_3 : C 25 3 3 := by decide +kernel
theorem cell_25_3_4 : C 25 3 4 := by decide +kernel
theorem cell_25_3_5 : C 25 3 5 := by decide +kernel
theorem row_25_3 : ThresholdAt 25 3 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 3 0 cell_25_3_0
  | exact S 25 3 1 cell_25_3_1
  | exact S 25 3 2 cell_25_3_2
  | exact S 25 3 3 cell_25_3_3
  | exact S 25 3 4 cell_25_3_4
  | exact S 25 3 5 cell_25_3_5
theorem cell_25_4_0 : C 25 4 0 := by decide +kernel
theorem cell_25_4_1 : C 25 4 1 := by decide +kernel
theorem cell_25_4_2 : C 25 4 2 := by decide +kernel
theorem cell_25_4_3 : C 25 4 3 := by decide +kernel
theorem cell_25_4_4 : C 25 4 4 := by decide +kernel
theorem cell_25_4_5 : C 25 4 5 := by decide +kernel
theorem row_25_4 : ThresholdAt 25 4 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 4 0 cell_25_4_0
  | exact S 25 4 1 cell_25_4_1
  | exact S 25 4 2 cell_25_4_2
  | exact S 25 4 3 cell_25_4_3
  | exact S 25 4 4 cell_25_4_4
  | exact S 25 4 5 cell_25_4_5
theorem cell_25_5_0 : C 25 5 0 := by decide +kernel
theorem cell_25_5_1 : C 25 5 1 := by decide +kernel
theorem cell_25_5_2 : C 25 5 2 := by decide +kernel
theorem cell_25_5_3 : C 25 5 3 := by decide +kernel
theorem cell_25_5_4 : C 25 5 4 := by decide +kernel
theorem cell_25_5_5 : C 25 5 5 := by decide +kernel
theorem row_25_5 : ThresholdAt 25 5 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 5 0 cell_25_5_0
  | exact S 25 5 1 cell_25_5_1
  | exact S 25 5 2 cell_25_5_2
  | exact S 25 5 3 cell_25_5_3
  | exact S 25 5 4 cell_25_5_4
  | exact S 25 5 5 cell_25_5_5
theorem cell_25_6_0 : C 25 6 0 := by decide +kernel
theorem cell_25_6_1 : C 25 6 1 := by decide +kernel
theorem cell_25_6_2 : C 25 6 2 := by decide +kernel
theorem cell_25_6_3 : C 25 6 3 := by decide +kernel
theorem cell_25_6_4 : C 25 6 4 := by decide +kernel
theorem cell_25_6_5 : C 25 6 5 := by decide +kernel
theorem row_25_6 : ThresholdAt 25 6 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 6 0 cell_25_6_0
  | exact S 25 6 1 cell_25_6_1
  | exact S 25 6 2 cell_25_6_2
  | exact S 25 6 3 cell_25_6_3
  | exact S 25 6 4 cell_25_6_4
  | exact S 25 6 5 cell_25_6_5
theorem cell_25_7_0 : C 25 7 0 := by decide +kernel
theorem cell_25_7_1 : C 25 7 1 := by decide +kernel
theorem cell_25_7_2 : C 25 7 2 := by decide +kernel
theorem cell_25_7_3 : C 25 7 3 := by decide +kernel
theorem cell_25_7_4 : C 25 7 4 := by decide +kernel
theorem cell_25_7_5 : C 25 7 5 := by decide +kernel
theorem row_25_7 : ThresholdAt 25 7 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 7 0 cell_25_7_0
  | exact S 25 7 1 cell_25_7_1
  | exact S 25 7 2 cell_25_7_2
  | exact S 25 7 3 cell_25_7_3
  | exact S 25 7 4 cell_25_7_4
  | exact S 25 7 5 cell_25_7_5
theorem cell_25_8_0 : C 25 8 0 := by decide +kernel
theorem cell_25_8_1 : C 25 8 1 := by decide +kernel
theorem cell_25_8_2 : C 25 8 2 := by decide +kernel
theorem cell_25_8_3 : C 25 8 3 := by decide +kernel
theorem cell_25_8_4 : C 25 8 4 := by decide +kernel
theorem cell_25_8_5 : C 25 8 5 := by decide +kernel
theorem row_25_8 : ThresholdAt 25 8 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 8 0 cell_25_8_0
  | exact S 25 8 1 cell_25_8_1
  | exact S 25 8 2 cell_25_8_2
  | exact S 25 8 3 cell_25_8_3
  | exact S 25 8 4 cell_25_8_4
  | exact S 25 8 5 cell_25_8_5
theorem cell_25_9_0 : C 25 9 0 := by decide +kernel
theorem cell_25_9_1 : C 25 9 1 := by decide +kernel
theorem cell_25_9_2 : C 25 9 2 := by decide +kernel
theorem cell_25_9_3 : C 25 9 3 := by decide +kernel
theorem cell_25_9_4 : C 25 9 4 := by decide +kernel
theorem cell_25_9_5 : C 25 9 5 := by decide +kernel
theorem row_25_9 : ThresholdAt 25 9 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 9 0 cell_25_9_0
  | exact S 25 9 1 cell_25_9_1
  | exact S 25 9 2 cell_25_9_2
  | exact S 25 9 3 cell_25_9_3
  | exact S 25 9 4 cell_25_9_4
  | exact S 25 9 5 cell_25_9_5
theorem cell_25_10_0 : C 25 10 0 := by decide +kernel
theorem cell_25_10_1 : C 25 10 1 := by decide +kernel
theorem cell_25_10_2 : C 25 10 2 := by decide +kernel
theorem cell_25_10_3 : C 25 10 3 := by decide +kernel
theorem cell_25_10_4 : C 25 10 4 := by decide +kernel
theorem cell_25_10_5 : C 25 10 5 := by decide +kernel
theorem row_25_10 : ThresholdAt 25 10 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 10 0 cell_25_10_0
  | exact S 25 10 1 cell_25_10_1
  | exact S 25 10 2 cell_25_10_2
  | exact S 25 10 3 cell_25_10_3
  | exact S 25 10 4 cell_25_10_4
  | exact S 25 10 5 cell_25_10_5
theorem cell_25_11_0 : C 25 11 0 := by decide +kernel
theorem cell_25_11_1 : C 25 11 1 := by decide +kernel
theorem cell_25_11_2 : C 25 11 2 := by decide +kernel
theorem cell_25_11_3 : C 25 11 3 := by decide +kernel
theorem cell_25_11_4 : C 25 11 4 := by decide +kernel
theorem cell_25_11_5 : C 25 11 5 := by decide +kernel
theorem row_25_11 : ThresholdAt 25 11 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 11 0 cell_25_11_0
  | exact S 25 11 1 cell_25_11_1
  | exact S 25 11 2 cell_25_11_2
  | exact S 25 11 3 cell_25_11_3
  | exact S 25 11 4 cell_25_11_4
  | exact S 25 11 5 cell_25_11_5
theorem cell_25_12_0 : C 25 12 0 := by decide +kernel
theorem cell_25_12_1 : C 25 12 1 := by decide +kernel
theorem cell_25_12_2 : C 25 12 2 := by decide +kernel
theorem cell_25_12_3 : C 25 12 3 := by decide +kernel
theorem cell_25_12_4 : C 25 12 4 := by decide +kernel
theorem cell_25_12_5 : C 25 12 5 := by decide +kernel
theorem row_25_12 : ThresholdAt 25 12 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 12 0 cell_25_12_0
  | exact S 25 12 1 cell_25_12_1
  | exact S 25 12 2 cell_25_12_2
  | exact S 25 12 3 cell_25_12_3
  | exact S 25 12 4 cell_25_12_4
  | exact S 25 12 5 cell_25_12_5
theorem cell_25_13_0 : C 25 13 0 := by decide +kernel
theorem cell_25_13_1 : C 25 13 1 := by decide +kernel
theorem cell_25_13_2 : C 25 13 2 := by decide +kernel
theorem cell_25_13_3 : C 25 13 3 := by decide +kernel
theorem cell_25_13_4 : C 25 13 4 := by decide +kernel
theorem cell_25_13_5 : C 25 13 5 := by decide +kernel
theorem row_25_13 : ThresholdAt 25 13 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 13 0 cell_25_13_0
  | exact S 25 13 1 cell_25_13_1
  | exact S 25 13 2 cell_25_13_2
  | exact S 25 13 3 cell_25_13_3
  | exact S 25 13 4 cell_25_13_4
  | exact S 25 13 5 cell_25_13_5
theorem cell_25_14_0 : C 25 14 0 := by decide +kernel
theorem cell_25_14_1 : C 25 14 1 := by decide +kernel
theorem cell_25_14_2 : C 25 14 2 := by decide +kernel
theorem cell_25_14_3 : C 25 14 3 := by decide +kernel
theorem cell_25_14_4 : C 25 14 4 := by decide +kernel
theorem cell_25_14_5 : C 25 14 5 := by decide +kernel
theorem row_25_14 : ThresholdAt 25 14 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 14 0 cell_25_14_0
  | exact S 25 14 1 cell_25_14_1
  | exact S 25 14 2 cell_25_14_2
  | exact S 25 14 3 cell_25_14_3
  | exact S 25 14 4 cell_25_14_4
  | exact S 25 14 5 cell_25_14_5
theorem cell_25_15_0 : C 25 15 0 := by decide +kernel
theorem cell_25_15_1 : C 25 15 1 := by decide +kernel
theorem cell_25_15_2 : C 25 15 2 := by decide +kernel
theorem cell_25_15_3 : C 25 15 3 := by decide +kernel
theorem cell_25_15_4 : C 25 15 4 := by decide +kernel
theorem cell_25_15_5 : C 25 15 5 := by decide +kernel
theorem row_25_15 : ThresholdAt 25 15 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 15 0 cell_25_15_0
  | exact S 25 15 1 cell_25_15_1
  | exact S 25 15 2 cell_25_15_2
  | exact S 25 15 3 cell_25_15_3
  | exact S 25 15 4 cell_25_15_4
  | exact S 25 15 5 cell_25_15_5
theorem cell_25_16_0 : C 25 16 0 := by decide +kernel
theorem cell_25_16_1 : C 25 16 1 := by decide +kernel
theorem cell_25_16_2 : C 25 16 2 := by decide +kernel
theorem cell_25_16_3 : C 25 16 3 := by decide +kernel
theorem cell_25_16_4 : C 25 16 4 := by decide +kernel
theorem cell_25_16_5 : C 25 16 5 := by decide +kernel
theorem row_25_16 : ThresholdAt 25 16 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 16 0 cell_25_16_0
  | exact S 25 16 1 cell_25_16_1
  | exact S 25 16 2 cell_25_16_2
  | exact S 25 16 3 cell_25_16_3
  | exact S 25 16 4 cell_25_16_4
  | exact S 25 16 5 cell_25_16_5
theorem cell_25_17_0 : C 25 17 0 := by decide +kernel
theorem cell_25_17_1 : C 25 17 1 := by decide +kernel
theorem cell_25_17_2 : C 25 17 2 := by decide +kernel
theorem cell_25_17_3 : C 25 17 3 := by decide +kernel
theorem cell_25_17_4 : C 25 17 4 := by decide +kernel
theorem cell_25_17_5 : C 25 17 5 := by decide +kernel
theorem row_25_17 : ThresholdAt 25 17 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 17 0 cell_25_17_0
  | exact S 25 17 1 cell_25_17_1
  | exact S 25 17 2 cell_25_17_2
  | exact S 25 17 3 cell_25_17_3
  | exact S 25 17 4 cell_25_17_4
  | exact S 25 17 5 cell_25_17_5
theorem cell_25_18_0 : C 25 18 0 := by decide +kernel
theorem cell_25_18_1 : C 25 18 1 := by decide +kernel
theorem cell_25_18_2 : C 25 18 2 := by decide +kernel
theorem cell_25_18_3 : C 25 18 3 := by decide +kernel
theorem cell_25_18_4 : C 25 18 4 := by decide +kernel
theorem cell_25_18_5 : C 25 18 5 := by decide +kernel
theorem row_25_18 : ThresholdAt 25 18 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 18 0 cell_25_18_0
  | exact S 25 18 1 cell_25_18_1
  | exact S 25 18 2 cell_25_18_2
  | exact S 25 18 3 cell_25_18_3
  | exact S 25 18 4 cell_25_18_4
  | exact S 25 18 5 cell_25_18_5
theorem cell_25_19_0 : C 25 19 0 := by decide +kernel
theorem cell_25_19_1 : C 25 19 1 := by decide +kernel
theorem cell_25_19_2 : C 25 19 2 := by decide +kernel
theorem cell_25_19_3 : C 25 19 3 := by decide +kernel
theorem cell_25_19_4 : C 25 19 4 := by decide +kernel
theorem cell_25_19_5 : C 25 19 5 := by decide +kernel
theorem row_25_19 : ThresholdAt 25 19 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 19 0 cell_25_19_0
  | exact S 25 19 1 cell_25_19_1
  | exact S 25 19 2 cell_25_19_2
  | exact S 25 19 3 cell_25_19_3
  | exact S 25 19 4 cell_25_19_4
  | exact S 25 19 5 cell_25_19_5
theorem cell_25_20_0 : C 25 20 0 := by decide +kernel
theorem cell_25_20_1 : C 25 20 1 := by decide +kernel
theorem cell_25_20_2 : C 25 20 2 := by decide +kernel
theorem cell_25_20_3 : C 25 20 3 := by decide +kernel
theorem cell_25_20_4 : C 25 20 4 := by decide +kernel
theorem cell_25_20_5 : C 25 20 5 := by decide +kernel
theorem row_25_20 : ThresholdAt 25 20 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 20 0 cell_25_20_0
  | exact S 25 20 1 cell_25_20_1
  | exact S 25 20 2 cell_25_20_2
  | exact S 25 20 3 cell_25_20_3
  | exact S 25 20 4 cell_25_20_4
  | exact S 25 20 5 cell_25_20_5
theorem cell_25_21_0 : C 25 21 0 := by decide +kernel
theorem cell_25_21_1 : C 25 21 1 := by decide +kernel
theorem cell_25_21_2 : C 25 21 2 := by decide +kernel
theorem cell_25_21_3 : C 25 21 3 := by decide +kernel
theorem cell_25_21_4 : C 25 21 4 := by decide +kernel
theorem cell_25_21_5 : C 25 21 5 := by decide +kernel
theorem row_25_21 : ThresholdAt 25 21 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 21 0 cell_25_21_0
  | exact S 25 21 1 cell_25_21_1
  | exact S 25 21 2 cell_25_21_2
  | exact S 25 21 3 cell_25_21_3
  | exact S 25 21 4 cell_25_21_4
  | exact S 25 21 5 cell_25_21_5
theorem cell_25_22_0 : C 25 22 0 := by decide +kernel
theorem cell_25_22_1 : C 25 22 1 := by decide +kernel
theorem cell_25_22_2 : C 25 22 2 := by decide +kernel
theorem cell_25_22_3 : C 25 22 3 := by decide +kernel
theorem cell_25_22_4 : C 25 22 4 := by decide +kernel
theorem cell_25_22_5 : C 25 22 5 := by decide +kernel
theorem row_25_22 : ThresholdAt 25 22 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 22 0 cell_25_22_0
  | exact S 25 22 1 cell_25_22_1
  | exact S 25 22 2 cell_25_22_2
  | exact S 25 22 3 cell_25_22_3
  | exact S 25 22 4 cell_25_22_4
  | exact S 25 22 5 cell_25_22_5
theorem cell_25_23_0 : C 25 23 0 := by decide +kernel
theorem cell_25_23_1 : C 25 23 1 := by decide +kernel
theorem cell_25_23_2 : C 25 23 2 := by decide +kernel
theorem cell_25_23_3 : C 25 23 3 := by decide +kernel
theorem cell_25_23_4 : C 25 23 4 := by decide +kernel
theorem cell_25_23_5 : C 25 23 5 := by decide +kernel
theorem row_25_23 : ThresholdAt 25 23 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 23 0 cell_25_23_0
  | exact S 25 23 1 cell_25_23_1
  | exact S 25 23 2 cell_25_23_2
  | exact S 25 23 3 cell_25_23_3
  | exact S 25 23 4 cell_25_23_4
  | exact S 25 23 5 cell_25_23_5
theorem cell_25_24_0 : C 25 24 0 := by decide +kernel
theorem cell_25_24_1 : C 25 24 1 := by decide +kernel
theorem cell_25_24_2 : C 25 24 2 := by decide +kernel
theorem cell_25_24_3 : C 25 24 3 := by decide +kernel
theorem cell_25_24_4 : C 25 24 4 := by decide +kernel
theorem cell_25_24_5 : C 25 24 5 := by decide +kernel
theorem row_25_24 : ThresholdAt 25 24 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 24 0 cell_25_24_0
  | exact S 25 24 1 cell_25_24_1
  | exact S 25 24 2 cell_25_24_2
  | exact S 25 24 3 cell_25_24_3
  | exact S 25 24 4 cell_25_24_4
  | exact S 25 24 5 cell_25_24_5
theorem cell_25_25_0 : C 25 25 0 := by decide +kernel
theorem cell_25_25_1 : C 25 25 1 := by decide +kernel
theorem cell_25_25_2 : C 25 25 2 := by decide +kernel
theorem cell_25_25_3 : C 25 25 3 := by decide +kernel
theorem cell_25_25_4 : C 25 25 4 := by decide +kernel
theorem cell_25_25_5 : C 25 25 5 := by decide +kernel
theorem row_25_25 : ThresholdAt 25 25 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 25 0 cell_25_25_0
  | exact S 25 25 1 cell_25_25_1
  | exact S 25 25 2 cell_25_25_2
  | exact S 25 25 3 cell_25_25_3
  | exact S 25 25 4 cell_25_25_4
  | exact S 25 25 5 cell_25_25_5
theorem cell_25_26_0 : C 25 26 0 := by decide +kernel
theorem cell_25_26_1 : C 25 26 1 := by decide +kernel
theorem cell_25_26_2 : C 25 26 2 := by decide +kernel
theorem cell_25_26_3 : C 25 26 3 := by decide +kernel
theorem cell_25_26_4 : C 25 26 4 := by decide +kernel
theorem cell_25_26_5 : C 25 26 5 := by decide +kernel
theorem row_25_26 : ThresholdAt 25 26 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 26 0 cell_25_26_0
  | exact S 25 26 1 cell_25_26_1
  | exact S 25 26 2 cell_25_26_2
  | exact S 25 26 3 cell_25_26_3
  | exact S 25 26 4 cell_25_26_4
  | exact S 25 26 5 cell_25_26_5
theorem cell_25_27_0 : C 25 27 0 := by decide +kernel
theorem cell_25_27_1 : C 25 27 1 := by decide +kernel
theorem cell_25_27_2 : C 25 27 2 := by decide +kernel
theorem cell_25_27_3 : C 25 27 3 := by decide +kernel
theorem cell_25_27_4 : C 25 27 4 := by decide +kernel
theorem cell_25_27_5 : C 25 27 5 := by decide +kernel
theorem row_25_27 : ThresholdAt 25 27 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 27 0 cell_25_27_0
  | exact S 25 27 1 cell_25_27_1
  | exact S 25 27 2 cell_25_27_2
  | exact S 25 27 3 cell_25_27_3
  | exact S 25 27 4 cell_25_27_4
  | exact S 25 27 5 cell_25_27_5
theorem cell_25_28_0 : C 25 28 0 := by decide +kernel
theorem cell_25_28_1 : C 25 28 1 := by decide +kernel
theorem cell_25_28_2 : C 25 28 2 := by decide +kernel
theorem cell_25_28_3 : C 25 28 3 := by decide +kernel
theorem cell_25_28_4 : C 25 28 4 := by decide +kernel
theorem cell_25_28_5 : C 25 28 5 := by decide +kernel
theorem row_25_28 : ThresholdAt 25 28 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 28 0 cell_25_28_0
  | exact S 25 28 1 cell_25_28_1
  | exact S 25 28 2 cell_25_28_2
  | exact S 25 28 3 cell_25_28_3
  | exact S 25 28 4 cell_25_28_4
  | exact S 25 28 5 cell_25_28_5
theorem cell_25_29_0 : C 25 29 0 := by decide +kernel
theorem cell_25_29_1 : C 25 29 1 := by decide +kernel
theorem cell_25_29_2 : C 25 29 2 := by decide +kernel
theorem cell_25_29_3 : C 25 29 3 := by decide +kernel
theorem cell_25_29_4 : C 25 29 4 := by decide +kernel
theorem cell_25_29_5 : C 25 29 5 := by decide +kernel
theorem row_25_29 : ThresholdAt 25 29 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 29 0 cell_25_29_0
  | exact S 25 29 1 cell_25_29_1
  | exact S 25 29 2 cell_25_29_2
  | exact S 25 29 3 cell_25_29_3
  | exact S 25 29 4 cell_25_29_4
  | exact S 25 29 5 cell_25_29_5
theorem cell_25_30_0 : C 25 30 0 := by decide +kernel
theorem cell_25_30_1 : C 25 30 1 := by decide +kernel
theorem cell_25_30_2 : C 25 30 2 := by decide +kernel
theorem cell_25_30_3 : C 25 30 3 := by decide +kernel
theorem cell_25_30_4 : C 25 30 4 := by decide +kernel
theorem cell_25_30_5 : C 25 30 5 := by decide +kernel
theorem row_25_30 : ThresholdAt 25 30 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 30 0 cell_25_30_0
  | exact S 25 30 1 cell_25_30_1
  | exact S 25 30 2 cell_25_30_2
  | exact S 25 30 3 cell_25_30_3
  | exact S 25 30 4 cell_25_30_4
  | exact S 25 30 5 cell_25_30_5
theorem cell_25_31_0 : C 25 31 0 := by decide +kernel
theorem cell_25_31_1 : C 25 31 1 := by decide +kernel
theorem cell_25_31_2 : C 25 31 2 := by decide +kernel
theorem cell_25_31_3 : C 25 31 3 := by decide +kernel
theorem cell_25_31_4 : C 25 31 4 := by decide +kernel
theorem cell_25_31_5 : C 25 31 5 := by decide +kernel
theorem row_25_31 : ThresholdAt 25 31 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 31 0 cell_25_31_0
  | exact S 25 31 1 cell_25_31_1
  | exact S 25 31 2 cell_25_31_2
  | exact S 25 31 3 cell_25_31_3
  | exact S 25 31 4 cell_25_31_4
  | exact S 25 31 5 cell_25_31_5
theorem cell_25_32_0 : C 25 32 0 := by decide +kernel
theorem cell_25_32_1 : C 25 32 1 := by decide +kernel
theorem cell_25_32_2 : C 25 32 2 := by decide +kernel
theorem cell_25_32_3 : C 25 32 3 := by decide +kernel
theorem cell_25_32_4 : C 25 32 4 := by decide +kernel
theorem cell_25_32_5 : C 25 32 5 := by decide +kernel
theorem row_25_32 : ThresholdAt 25 32 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 32 0 cell_25_32_0
  | exact S 25 32 1 cell_25_32_1
  | exact S 25 32 2 cell_25_32_2
  | exact S 25 32 3 cell_25_32_3
  | exact S 25 32 4 cell_25_32_4
  | exact S 25 32 5 cell_25_32_5
theorem cell_25_33_0 : C 25 33 0 := by decide +kernel
theorem cell_25_33_1 : C 25 33 1 := by decide +kernel
theorem cell_25_33_2 : C 25 33 2 := by decide +kernel
theorem cell_25_33_3 : C 25 33 3 := by decide +kernel
theorem cell_25_33_4 : C 25 33 4 := by decide +kernel
theorem cell_25_33_5 : C 25 33 5 := by decide +kernel
theorem row_25_33 : ThresholdAt 25 33 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 33 0 cell_25_33_0
  | exact S 25 33 1 cell_25_33_1
  | exact S 25 33 2 cell_25_33_2
  | exact S 25 33 3 cell_25_33_3
  | exact S 25 33 4 cell_25_33_4
  | exact S 25 33 5 cell_25_33_5
theorem cell_25_34_0 : C 25 34 0 := by decide +kernel
theorem cell_25_34_1 : C 25 34 1 := by decide +kernel
theorem cell_25_34_2 : C 25 34 2 := by decide +kernel
theorem cell_25_34_3 : C 25 34 3 := by decide +kernel
theorem cell_25_34_4 : C 25 34 4 := by decide +kernel
theorem cell_25_34_5 : C 25 34 5 := by decide +kernel
theorem row_25_34 : ThresholdAt 25 34 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 34 0 cell_25_34_0
  | exact S 25 34 1 cell_25_34_1
  | exact S 25 34 2 cell_25_34_2
  | exact S 25 34 3 cell_25_34_3
  | exact S 25 34 4 cell_25_34_4
  | exact S 25 34 5 cell_25_34_5
theorem cell_25_35_0 : C 25 35 0 := by decide +kernel
theorem cell_25_35_1 : C 25 35 1 := by decide +kernel
theorem cell_25_35_2 : C 25 35 2 := by decide +kernel
theorem cell_25_35_3 : C 25 35 3 := by decide +kernel
theorem cell_25_35_4 : C 25 35 4 := by decide +kernel
theorem cell_25_35_5 : C 25 35 5 := by decide +kernel
theorem row_25_35 : ThresholdAt 25 35 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 35 0 cell_25_35_0
  | exact S 25 35 1 cell_25_35_1
  | exact S 25 35 2 cell_25_35_2
  | exact S 25 35 3 cell_25_35_3
  | exact S 25 35 4 cell_25_35_4
  | exact S 25 35 5 cell_25_35_5
theorem cell_25_36_0 : C 25 36 0 := by decide +kernel
theorem cell_25_36_1 : C 25 36 1 := by decide +kernel
theorem cell_25_36_2 : C 25 36 2 := by decide +kernel
theorem cell_25_36_3 : C 25 36 3 := by decide +kernel
theorem cell_25_36_4 : C 25 36 4 := by decide +kernel
theorem cell_25_36_5 : C 25 36 5 := by decide +kernel
theorem row_25_36 : ThresholdAt 25 36 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 36 0 cell_25_36_0
  | exact S 25 36 1 cell_25_36_1
  | exact S 25 36 2 cell_25_36_2
  | exact S 25 36 3 cell_25_36_3
  | exact S 25 36 4 cell_25_36_4
  | exact S 25 36 5 cell_25_36_5
theorem cell_25_37_0 : C 25 37 0 := by decide +kernel
theorem cell_25_37_1 : C 25 37 1 := by decide +kernel
theorem cell_25_37_2 : C 25 37 2 := by decide +kernel
theorem cell_25_37_3 : C 25 37 3 := by decide +kernel
theorem cell_25_37_4 : C 25 37 4 := by decide +kernel
theorem cell_25_37_5 : C 25 37 5 := by decide +kernel
theorem row_25_37 : ThresholdAt 25 37 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 37 0 cell_25_37_0
  | exact S 25 37 1 cell_25_37_1
  | exact S 25 37 2 cell_25_37_2
  | exact S 25 37 3 cell_25_37_3
  | exact S 25 37 4 cell_25_37_4
  | exact S 25 37 5 cell_25_37_5
theorem cell_25_38_0 : C 25 38 0 := by decide +kernel
theorem cell_25_38_1 : C 25 38 1 := by decide +kernel
theorem cell_25_38_2 : C 25 38 2 := by decide +kernel
theorem cell_25_38_3 : C 25 38 3 := by decide +kernel
theorem cell_25_38_4 : C 25 38 4 := by decide +kernel
theorem cell_25_38_5 : C 25 38 5 := by decide +kernel
theorem row_25_38 : ThresholdAt 25 38 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 38 0 cell_25_38_0
  | exact S 25 38 1 cell_25_38_1
  | exact S 25 38 2 cell_25_38_2
  | exact S 25 38 3 cell_25_38_3
  | exact S 25 38 4 cell_25_38_4
  | exact S 25 38 5 cell_25_38_5
theorem cell_25_39_0 : C 25 39 0 := by decide +kernel
theorem cell_25_39_1 : C 25 39 1 := by decide +kernel
theorem cell_25_39_2 : C 25 39 2 := by decide +kernel
theorem cell_25_39_3 : C 25 39 3 := by decide +kernel
theorem cell_25_39_4 : C 25 39 4 := by decide +kernel
theorem cell_25_39_5 : C 25 39 5 := by decide +kernel
theorem row_25_39 : ThresholdAt 25 39 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 39 0 cell_25_39_0
  | exact S 25 39 1 cell_25_39_1
  | exact S 25 39 2 cell_25_39_2
  | exact S 25 39 3 cell_25_39_3
  | exact S 25 39 4 cell_25_39_4
  | exact S 25 39 5 cell_25_39_5
theorem cell_25_40_0 : C 25 40 0 := by decide +kernel
theorem cell_25_40_1 : C 25 40 1 := by decide +kernel
theorem cell_25_40_2 : C 25 40 2 := by decide +kernel
theorem cell_25_40_3 : C 25 40 3 := by decide +kernel
theorem cell_25_40_4 : C 25 40 4 := by decide +kernel
theorem cell_25_40_5 : C 25 40 5 := by decide +kernel
theorem row_25_40 : ThresholdAt 25 40 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 40 0 cell_25_40_0
  | exact S 25 40 1 cell_25_40_1
  | exact S 25 40 2 cell_25_40_2
  | exact S 25 40 3 cell_25_40_3
  | exact S 25 40 4 cell_25_40_4
  | exact S 25 40 5 cell_25_40_5
theorem cell_25_41_0 : C 25 41 0 := by decide +kernel
theorem cell_25_41_1 : C 25 41 1 := by decide +kernel
theorem cell_25_41_2 : C 25 41 2 := by decide +kernel
theorem cell_25_41_3 : C 25 41 3 := by decide +kernel
theorem cell_25_41_4 : C 25 41 4 := by decide +kernel
theorem cell_25_41_5 : C 25 41 5 := by decide +kernel
theorem row_25_41 : ThresholdAt 25 41 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 41 0 cell_25_41_0
  | exact S 25 41 1 cell_25_41_1
  | exact S 25 41 2 cell_25_41_2
  | exact S 25 41 3 cell_25_41_3
  | exact S 25 41 4 cell_25_41_4
  | exact S 25 41 5 cell_25_41_5
theorem cell_25_42_0 : C 25 42 0 := by decide +kernel
theorem cell_25_42_1 : C 25 42 1 := by decide +kernel
theorem cell_25_42_2 : C 25 42 2 := by decide +kernel
theorem cell_25_42_3 : C 25 42 3 := by decide +kernel
theorem cell_25_42_4 : C 25 42 4 := by decide +kernel
theorem cell_25_42_5 : C 25 42 5 := by decide +kernel
theorem row_25_42 : ThresholdAt 25 42 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 42 0 cell_25_42_0
  | exact S 25 42 1 cell_25_42_1
  | exact S 25 42 2 cell_25_42_2
  | exact S 25 42 3 cell_25_42_3
  | exact S 25 42 4 cell_25_42_4
  | exact S 25 42 5 cell_25_42_5
theorem cell_25_43_0 : C 25 43 0 := by decide +kernel
theorem cell_25_43_1 : C 25 43 1 := by decide +kernel
theorem cell_25_43_2 : C 25 43 2 := by decide +kernel
theorem cell_25_43_3 : C 25 43 3 := by decide +kernel
theorem cell_25_43_4 : C 25 43 4 := by decide +kernel
theorem cell_25_43_5 : C 25 43 5 := by decide +kernel
theorem row_25_43 : ThresholdAt 25 43 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 43 0 cell_25_43_0
  | exact S 25 43 1 cell_25_43_1
  | exact S 25 43 2 cell_25_43_2
  | exact S 25 43 3 cell_25_43_3
  | exact S 25 43 4 cell_25_43_4
  | exact S 25 43 5 cell_25_43_5
theorem cell_25_44_0 : C 25 44 0 := by decide +kernel
theorem cell_25_44_1 : C 25 44 1 := by decide +kernel
theorem cell_25_44_2 : C 25 44 2 := by decide +kernel
theorem cell_25_44_3 : C 25 44 3 := by decide +kernel
theorem cell_25_44_4 : C 25 44 4 := by decide +kernel
theorem cell_25_44_5 : C 25 44 5 := by decide +kernel
theorem row_25_44 : ThresholdAt 25 44 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 44 0 cell_25_44_0
  | exact S 25 44 1 cell_25_44_1
  | exact S 25 44 2 cell_25_44_2
  | exact S 25 44 3 cell_25_44_3
  | exact S 25 44 4 cell_25_44_4
  | exact S 25 44 5 cell_25_44_5
theorem cell_25_45_0 : C 25 45 0 := by decide +kernel
theorem cell_25_45_1 : C 25 45 1 := by decide +kernel
theorem cell_25_45_2 : C 25 45 2 := by decide +kernel
theorem cell_25_45_3 : C 25 45 3 := by decide +kernel
theorem cell_25_45_4 : C 25 45 4 := by decide +kernel
theorem cell_25_45_5 : C 25 45 5 := by decide +kernel
theorem row_25_45 : ThresholdAt 25 45 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 45 0 cell_25_45_0
  | exact S 25 45 1 cell_25_45_1
  | exact S 25 45 2 cell_25_45_2
  | exact S 25 45 3 cell_25_45_3
  | exact S 25 45 4 cell_25_45_4
  | exact S 25 45 5 cell_25_45_5
theorem cell_25_46_0 : C 25 46 0 := by decide +kernel
theorem cell_25_46_1 : C 25 46 1 := by decide +kernel
theorem cell_25_46_2 : C 25 46 2 := by decide +kernel
theorem cell_25_46_3 : C 25 46 3 := by decide +kernel
theorem cell_25_46_4 : C 25 46 4 := by decide +kernel
theorem cell_25_46_5 : C 25 46 5 := by decide +kernel
theorem row_25_46 : ThresholdAt 25 46 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 46 0 cell_25_46_0
  | exact S 25 46 1 cell_25_46_1
  | exact S 25 46 2 cell_25_46_2
  | exact S 25 46 3 cell_25_46_3
  | exact S 25 46 4 cell_25_46_4
  | exact S 25 46 5 cell_25_46_5
theorem cell_25_47_0 : C 25 47 0 := by decide +kernel
theorem cell_25_47_1 : C 25 47 1 := by decide +kernel
theorem cell_25_47_2 : C 25 47 2 := by decide +kernel
theorem cell_25_47_3 : C 25 47 3 := by decide +kernel
theorem cell_25_47_4 : C 25 47 4 := by decide +kernel
theorem cell_25_47_5 : C 25 47 5 := by decide +kernel
theorem row_25_47 : ThresholdAt 25 47 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 47 0 cell_25_47_0
  | exact S 25 47 1 cell_25_47_1
  | exact S 25 47 2 cell_25_47_2
  | exact S 25 47 3 cell_25_47_3
  | exact S 25 47 4 cell_25_47_4
  | exact S 25 47 5 cell_25_47_5
theorem cell_25_48_0 : C 25 48 0 := by decide +kernel
theorem cell_25_48_1 : C 25 48 1 := by decide +kernel
theorem cell_25_48_2 : C 25 48 2 := by decide +kernel
theorem cell_25_48_3 : C 25 48 3 := by decide +kernel
theorem cell_25_48_4 : C 25 48 4 := by decide +kernel
theorem cell_25_48_5 : C 25 48 5 := by decide +kernel
theorem row_25_48 : ThresholdAt 25 48 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 48 0 cell_25_48_0
  | exact S 25 48 1 cell_25_48_1
  | exact S 25 48 2 cell_25_48_2
  | exact S 25 48 3 cell_25_48_3
  | exact S 25 48 4 cell_25_48_4
  | exact S 25 48 5 cell_25_48_5
theorem cell_25_49_0 : C 25 49 0 := by decide +kernel
theorem cell_25_49_1 : C 25 49 1 := by decide +kernel
theorem cell_25_49_2 : C 25 49 2 := by decide +kernel
theorem cell_25_49_3 : C 25 49 3 := by decide +kernel
theorem cell_25_49_4 : C 25 49 4 := by decide +kernel
theorem cell_25_49_5 : C 25 49 5 := by decide +kernel
theorem row_25_49 : ThresholdAt 25 49 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 49 0 cell_25_49_0
  | exact S 25 49 1 cell_25_49_1
  | exact S 25 49 2 cell_25_49_2
  | exact S 25 49 3 cell_25_49_3
  | exact S 25 49 4 cell_25_49_4
  | exact S 25 49 5 cell_25_49_5
theorem cell_25_50_0 : C 25 50 0 := by decide +kernel
theorem cell_25_50_1 : C 25 50 1 := by decide +kernel
theorem cell_25_50_2 : C 25 50 2 := by decide +kernel
theorem cell_25_50_3 : C 25 50 3 := by decide +kernel
theorem cell_25_50_4 : C 25 50 4 := by decide +kernel
theorem cell_25_50_5 : C 25 50 5 := by decide +kernel
theorem row_25_50 : ThresholdAt 25 50 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 50 0 cell_25_50_0
  | exact S 25 50 1 cell_25_50_1
  | exact S 25 50 2 cell_25_50_2
  | exact S 25 50 3 cell_25_50_3
  | exact S 25 50 4 cell_25_50_4
  | exact S 25 50 5 cell_25_50_5
theorem cell_25_51_0 : C 25 51 0 := by decide +kernel
theorem cell_25_51_1 : C 25 51 1 := by decide +kernel
theorem cell_25_51_2 : C 25 51 2 := by decide +kernel
theorem cell_25_51_3 : C 25 51 3 := by decide +kernel
theorem cell_25_51_4 : C 25 51 4 := by decide +kernel
theorem cell_25_51_5 : C 25 51 5 := by decide +kernel
theorem row_25_51 : ThresholdAt 25 51 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 51 0 cell_25_51_0
  | exact S 25 51 1 cell_25_51_1
  | exact S 25 51 2 cell_25_51_2
  | exact S 25 51 3 cell_25_51_3
  | exact S 25 51 4 cell_25_51_4
  | exact S 25 51 5 cell_25_51_5
theorem cell_25_52_0 : C 25 52 0 := by decide +kernel
theorem cell_25_52_1 : C 25 52 1 := by decide +kernel
theorem cell_25_52_2 : C 25 52 2 := by decide +kernel
theorem cell_25_52_3 : C 25 52 3 := by decide +kernel
theorem cell_25_52_4 : C 25 52 4 := by decide +kernel
theorem cell_25_52_5 : C 25 52 5 := by decide +kernel
theorem row_25_52 : ThresholdAt 25 52 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 52 0 cell_25_52_0
  | exact S 25 52 1 cell_25_52_1
  | exact S 25 52 2 cell_25_52_2
  | exact S 25 52 3 cell_25_52_3
  | exact S 25 52 4 cell_25_52_4
  | exact S 25 52 5 cell_25_52_5
theorem cell_25_53_0 : C 25 53 0 := by decide +kernel
theorem cell_25_53_1 : C 25 53 1 := by decide +kernel
theorem cell_25_53_2 : C 25 53 2 := by decide +kernel
theorem cell_25_53_3 : C 25 53 3 := by decide +kernel
theorem cell_25_53_4 : C 25 53 4 := by decide +kernel
theorem cell_25_53_5 : C 25 53 5 := by decide +kernel
theorem row_25_53 : ThresholdAt 25 53 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 53 0 cell_25_53_0
  | exact S 25 53 1 cell_25_53_1
  | exact S 25 53 2 cell_25_53_2
  | exact S 25 53 3 cell_25_53_3
  | exact S 25 53 4 cell_25_53_4
  | exact S 25 53 5 cell_25_53_5
theorem cell_25_54_0 : C 25 54 0 := by decide +kernel
theorem cell_25_54_1 : C 25 54 1 := by decide +kernel
theorem cell_25_54_2 : C 25 54 2 := by decide +kernel
theorem cell_25_54_3 : C 25 54 3 := by decide +kernel
theorem cell_25_54_4 : C 25 54 4 := by decide +kernel
theorem cell_25_54_5 : C 25 54 5 := by decide +kernel
theorem row_25_54 : ThresholdAt 25 54 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 54 0 cell_25_54_0
  | exact S 25 54 1 cell_25_54_1
  | exact S 25 54 2 cell_25_54_2
  | exact S 25 54 3 cell_25_54_3
  | exact S 25 54 4 cell_25_54_4
  | exact S 25 54 5 cell_25_54_5
theorem cell_25_55_0 : C 25 55 0 := by decide +kernel
theorem cell_25_55_1 : C 25 55 1 := by decide +kernel
theorem cell_25_55_2 : C 25 55 2 := by decide +kernel
theorem cell_25_55_3 : C 25 55 3 := by decide +kernel
theorem cell_25_55_4 : C 25 55 4 := by decide +kernel
theorem cell_25_55_5 : C 25 55 5 := by decide +kernel
theorem row_25_55 : ThresholdAt 25 55 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 55 0 cell_25_55_0
  | exact S 25 55 1 cell_25_55_1
  | exact S 25 55 2 cell_25_55_2
  | exact S 25 55 3 cell_25_55_3
  | exact S 25 55 4 cell_25_55_4
  | exact S 25 55 5 cell_25_55_5
theorem cell_25_56_0 : C 25 56 0 := by decide +kernel
theorem cell_25_56_1 : C 25 56 1 := by decide +kernel
theorem cell_25_56_2 : C 25 56 2 := by decide +kernel
theorem cell_25_56_3 : C 25 56 3 := by decide +kernel
theorem cell_25_56_4 : C 25 56 4 := by decide +kernel
theorem cell_25_56_5 : C 25 56 5 := by decide +kernel
theorem row_25_56 : ThresholdAt 25 56 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 56 0 cell_25_56_0
  | exact S 25 56 1 cell_25_56_1
  | exact S 25 56 2 cell_25_56_2
  | exact S 25 56 3 cell_25_56_3
  | exact S 25 56 4 cell_25_56_4
  | exact S 25 56 5 cell_25_56_5
theorem cell_25_57_0 : C 25 57 0 := by decide +kernel
theorem cell_25_57_1 : C 25 57 1 := by decide +kernel
theorem cell_25_57_2 : C 25 57 2 := by decide +kernel
theorem cell_25_57_3 : C 25 57 3 := by decide +kernel
theorem cell_25_57_4 : C 25 57 4 := by decide +kernel
theorem cell_25_57_5 : C 25 57 5 := by decide +kernel
theorem row_25_57 : ThresholdAt 25 57 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 57 0 cell_25_57_0
  | exact S 25 57 1 cell_25_57_1
  | exact S 25 57 2 cell_25_57_2
  | exact S 25 57 3 cell_25_57_3
  | exact S 25 57 4 cell_25_57_4
  | exact S 25 57 5 cell_25_57_5
theorem cell_25_58_0 : C 25 58 0 := by decide +kernel
theorem cell_25_58_1 : C 25 58 1 := by decide +kernel
theorem cell_25_58_2 : C 25 58 2 := by decide +kernel
theorem cell_25_58_3 : C 25 58 3 := by decide +kernel
theorem cell_25_58_4 : C 25 58 4 := by decide +kernel
theorem cell_25_58_5 : C 25 58 5 := by decide +kernel
theorem row_25_58 : ThresholdAt 25 58 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 58 0 cell_25_58_0
  | exact S 25 58 1 cell_25_58_1
  | exact S 25 58 2 cell_25_58_2
  | exact S 25 58 3 cell_25_58_3
  | exact S 25 58 4 cell_25_58_4
  | exact S 25 58 5 cell_25_58_5
theorem cell_25_59_0 : C 25 59 0 := by decide +kernel
theorem cell_25_59_1 : C 25 59 1 := by decide +kernel
theorem cell_25_59_2 : C 25 59 2 := by decide +kernel
theorem cell_25_59_3 : C 25 59 3 := by decide +kernel
theorem cell_25_59_4 : C 25 59 4 := by decide +kernel
theorem cell_25_59_5 : C 25 59 5 := by decide +kernel
theorem row_25_59 : ThresholdAt 25 59 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 59 0 cell_25_59_0
  | exact S 25 59 1 cell_25_59_1
  | exact S 25 59 2 cell_25_59_2
  | exact S 25 59 3 cell_25_59_3
  | exact S 25 59 4 cell_25_59_4
  | exact S 25 59 5 cell_25_59_5
theorem cell_25_60_0 : C 25 60 0 := by decide +kernel
theorem cell_25_60_1 : C 25 60 1 := by decide +kernel
theorem cell_25_60_2 : C 25 60 2 := by decide +kernel
theorem cell_25_60_3 : C 25 60 3 := by decide +kernel
theorem cell_25_60_4 : C 25 60 4 := by decide +kernel
theorem cell_25_60_5 : C 25 60 5 := by decide +kernel
theorem row_25_60 : ThresholdAt 25 60 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 60 0 cell_25_60_0
  | exact S 25 60 1 cell_25_60_1
  | exact S 25 60 2 cell_25_60_2
  | exact S 25 60 3 cell_25_60_3
  | exact S 25 60 4 cell_25_60_4
  | exact S 25 60 5 cell_25_60_5
theorem cell_25_61_0 : C 25 61 0 := by decide +kernel
theorem cell_25_61_1 : C 25 61 1 := by decide +kernel
theorem cell_25_61_2 : C 25 61 2 := by decide +kernel
theorem cell_25_61_3 : C 25 61 3 := by decide +kernel
theorem cell_25_61_4 : C 25 61 4 := by decide +kernel
theorem cell_25_61_5 : C 25 61 5 := by decide +kernel
theorem row_25_61 : ThresholdAt 25 61 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 61 0 cell_25_61_0
  | exact S 25 61 1 cell_25_61_1
  | exact S 25 61 2 cell_25_61_2
  | exact S 25 61 3 cell_25_61_3
  | exact S 25 61 4 cell_25_61_4
  | exact S 25 61 5 cell_25_61_5
theorem cell_25_62_0 : C 25 62 0 := by decide +kernel
theorem cell_25_62_1 : C 25 62 1 := by decide +kernel
theorem cell_25_62_2 : C 25 62 2 := by decide +kernel
theorem cell_25_62_3 : C 25 62 3 := by decide +kernel
theorem cell_25_62_4 : C 25 62 4 := by decide +kernel
theorem cell_25_62_5 : C 25 62 5 := by decide +kernel
theorem row_25_62 : ThresholdAt 25 62 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 62 0 cell_25_62_0
  | exact S 25 62 1 cell_25_62_1
  | exact S 25 62 2 cell_25_62_2
  | exact S 25 62 3 cell_25_62_3
  | exact S 25 62 4 cell_25_62_4
  | exact S 25 62 5 cell_25_62_5
theorem cell_25_63_0 : C 25 63 0 := by decide +kernel
theorem cell_25_63_1 : C 25 63 1 := by decide +kernel
theorem cell_25_63_2 : C 25 63 2 := by decide +kernel
theorem cell_25_63_3 : C 25 63 3 := by decide +kernel
theorem cell_25_63_4 : C 25 63 4 := by decide +kernel
theorem cell_25_63_5 : C 25 63 5 := by decide +kernel
theorem row_25_63 : ThresholdAt 25 63 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 63 0 cell_25_63_0
  | exact S 25 63 1 cell_25_63_1
  | exact S 25 63 2 cell_25_63_2
  | exact S 25 63 3 cell_25_63_3
  | exact S 25 63 4 cell_25_63_4
  | exact S 25 63 5 cell_25_63_5
theorem cell_25_64_0 : C 25 64 0 := by decide +kernel
theorem cell_25_64_1 : C 25 64 1 := by decide +kernel
theorem cell_25_64_2 : C 25 64 2 := by decide +kernel
theorem cell_25_64_3 : C 25 64 3 := by decide +kernel
theorem cell_25_64_4 : C 25 64 4 := by decide +kernel
theorem cell_25_64_5 : C 25 64 5 := by decide +kernel
theorem row_25_64 : ThresholdAt 25 64 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 64 0 cell_25_64_0
  | exact S 25 64 1 cell_25_64_1
  | exact S 25 64 2 cell_25_64_2
  | exact S 25 64 3 cell_25_64_3
  | exact S 25 64 4 cell_25_64_4
  | exact S 25 64 5 cell_25_64_5
theorem cell_25_65_0 : C 25 65 0 := by decide +kernel
theorem cell_25_65_1 : C 25 65 1 := by decide +kernel
theorem cell_25_65_2 : C 25 65 2 := by decide +kernel
theorem cell_25_65_3 : C 25 65 3 := by decide +kernel
theorem cell_25_65_4 : C 25 65 4 := by decide +kernel
theorem cell_25_65_5 : C 25 65 5 := by decide +kernel
theorem row_25_65 : ThresholdAt 25 65 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 65 0 cell_25_65_0
  | exact S 25 65 1 cell_25_65_1
  | exact S 25 65 2 cell_25_65_2
  | exact S 25 65 3 cell_25_65_3
  | exact S 25 65 4 cell_25_65_4
  | exact S 25 65 5 cell_25_65_5
theorem cell_25_66_0 : C 25 66 0 := by decide +kernel
theorem cell_25_66_1 : C 25 66 1 := by decide +kernel
theorem cell_25_66_2 : C 25 66 2 := by decide +kernel
theorem cell_25_66_3 : C 25 66 3 := by decide +kernel
theorem cell_25_66_4 : C 25 66 4 := by decide +kernel
theorem cell_25_66_5 : C 25 66 5 := by decide +kernel
theorem row_25_66 : ThresholdAt 25 66 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 66 0 cell_25_66_0
  | exact S 25 66 1 cell_25_66_1
  | exact S 25 66 2 cell_25_66_2
  | exact S 25 66 3 cell_25_66_3
  | exact S 25 66 4 cell_25_66_4
  | exact S 25 66 5 cell_25_66_5
theorem cell_25_67_0 : C 25 67 0 := by decide +kernel
theorem cell_25_67_1 : C 25 67 1 := by decide +kernel
theorem cell_25_67_2 : C 25 67 2 := by decide +kernel
theorem cell_25_67_3 : C 25 67 3 := by decide +kernel
theorem cell_25_67_4 : C 25 67 4 := by decide +kernel
theorem cell_25_67_5 : C 25 67 5 := by decide +kernel
theorem row_25_67 : ThresholdAt 25 67 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 67 0 cell_25_67_0
  | exact S 25 67 1 cell_25_67_1
  | exact S 25 67 2 cell_25_67_2
  | exact S 25 67 3 cell_25_67_3
  | exact S 25 67 4 cell_25_67_4
  | exact S 25 67 5 cell_25_67_5
theorem cell_25_68_0 : C 25 68 0 := by decide +kernel
theorem cell_25_68_1 : C 25 68 1 := by decide +kernel
theorem cell_25_68_2 : C 25 68 2 := by decide +kernel
theorem cell_25_68_3 : C 25 68 3 := by decide +kernel
theorem cell_25_68_4 : C 25 68 4 := by decide +kernel
theorem cell_25_68_5 : C 25 68 5 := by decide +kernel
theorem row_25_68 : ThresholdAt 25 68 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 68 0 cell_25_68_0
  | exact S 25 68 1 cell_25_68_1
  | exact S 25 68 2 cell_25_68_2
  | exact S 25 68 3 cell_25_68_3
  | exact S 25 68 4 cell_25_68_4
  | exact S 25 68 5 cell_25_68_5
theorem cell_25_69_0 : C 25 69 0 := by decide +kernel
theorem cell_25_69_1 : C 25 69 1 := by decide +kernel
theorem cell_25_69_2 : C 25 69 2 := by decide +kernel
theorem cell_25_69_3 : C 25 69 3 := by decide +kernel
theorem cell_25_69_4 : C 25 69 4 := by decide +kernel
theorem cell_25_69_5 : C 25 69 5 := by decide +kernel
theorem row_25_69 : ThresholdAt 25 69 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 69 0 cell_25_69_0
  | exact S 25 69 1 cell_25_69_1
  | exact S 25 69 2 cell_25_69_2
  | exact S 25 69 3 cell_25_69_3
  | exact S 25 69 4 cell_25_69_4
  | exact S 25 69 5 cell_25_69_5
theorem cell_25_70_0 : C 25 70 0 := by decide +kernel
theorem cell_25_70_1 : C 25 70 1 := by decide +kernel
theorem cell_25_70_2 : C 25 70 2 := by decide +kernel
theorem cell_25_70_3 : C 25 70 3 := by decide +kernel
theorem cell_25_70_4 : C 25 70 4 := by decide +kernel
theorem cell_25_70_5 : C 25 70 5 := by decide +kernel
theorem row_25_70 : ThresholdAt 25 70 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 70 0 cell_25_70_0
  | exact S 25 70 1 cell_25_70_1
  | exact S 25 70 2 cell_25_70_2
  | exact S 25 70 3 cell_25_70_3
  | exact S 25 70 4 cell_25_70_4
  | exact S 25 70 5 cell_25_70_5
theorem cell_25_71_0 : C 25 71 0 := by decide +kernel
theorem cell_25_71_1 : C 25 71 1 := by decide +kernel
theorem cell_25_71_2 : C 25 71 2 := by decide +kernel
theorem cell_25_71_3 : C 25 71 3 := by decide +kernel
theorem cell_25_71_4 : C 25 71 4 := by decide +kernel
theorem cell_25_71_5 : C 25 71 5 := by decide +kernel
theorem row_25_71 : ThresholdAt 25 71 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 71 0 cell_25_71_0
  | exact S 25 71 1 cell_25_71_1
  | exact S 25 71 2 cell_25_71_2
  | exact S 25 71 3 cell_25_71_3
  | exact S 25 71 4 cell_25_71_4
  | exact S 25 71 5 cell_25_71_5
theorem cell_25_72_0 : C 25 72 0 := by decide +kernel
theorem cell_25_72_1 : C 25 72 1 := by decide +kernel
theorem cell_25_72_2 : C 25 72 2 := by decide +kernel
theorem cell_25_72_3 : C 25 72 3 := by decide +kernel
theorem cell_25_72_4 : C 25 72 4 := by decide +kernel
theorem cell_25_72_5 : C 25 72 5 := by decide +kernel
theorem row_25_72 : ThresholdAt 25 72 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 72 0 cell_25_72_0
  | exact S 25 72 1 cell_25_72_1
  | exact S 25 72 2 cell_25_72_2
  | exact S 25 72 3 cell_25_72_3
  | exact S 25 72 4 cell_25_72_4
  | exact S 25 72 5 cell_25_72_5
theorem cell_25_73_0 : C 25 73 0 := by decide +kernel
theorem cell_25_73_1 : C 25 73 1 := by decide +kernel
theorem cell_25_73_2 : C 25 73 2 := by decide +kernel
theorem cell_25_73_3 : C 25 73 3 := by decide +kernel
theorem cell_25_73_4 : C 25 73 4 := by decide +kernel
theorem cell_25_73_5 : C 25 73 5 := by decide +kernel
theorem row_25_73 : ThresholdAt 25 73 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 73 0 cell_25_73_0
  | exact S 25 73 1 cell_25_73_1
  | exact S 25 73 2 cell_25_73_2
  | exact S 25 73 3 cell_25_73_3
  | exact S 25 73 4 cell_25_73_4
  | exact S 25 73 5 cell_25_73_5
theorem cell_25_74_0 : C 25 74 0 := by decide +kernel
theorem cell_25_74_1 : C 25 74 1 := by decide +kernel
theorem cell_25_74_2 : C 25 74 2 := by decide +kernel
theorem cell_25_74_3 : C 25 74 3 := by decide +kernel
theorem cell_25_74_4 : C 25 74 4 := by decide +kernel
theorem cell_25_74_5 : C 25 74 5 := by decide +kernel
theorem row_25_74 : ThresholdAt 25 74 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 74 0 cell_25_74_0
  | exact S 25 74 1 cell_25_74_1
  | exact S 25 74 2 cell_25_74_2
  | exact S 25 74 3 cell_25_74_3
  | exact S 25 74 4 cell_25_74_4
  | exact S 25 74 5 cell_25_74_5
theorem cell_25_75_0 : C 25 75 0 := by decide +kernel
theorem cell_25_75_1 : C 25 75 1 := by decide +kernel
theorem cell_25_75_2 : C 25 75 2 := by decide +kernel
theorem cell_25_75_3 : C 25 75 3 := by decide +kernel
theorem cell_25_75_4 : C 25 75 4 := by decide +kernel
theorem cell_25_75_5 : C 25 75 5 := by decide +kernel
theorem row_25_75 : ThresholdAt 25 75 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 75 0 cell_25_75_0
  | exact S 25 75 1 cell_25_75_1
  | exact S 25 75 2 cell_25_75_2
  | exact S 25 75 3 cell_25_75_3
  | exact S 25 75 4 cell_25_75_4
  | exact S 25 75 5 cell_25_75_5
theorem cell_25_76_0 : C 25 76 0 := by decide +kernel
theorem cell_25_76_1 : C 25 76 1 := by decide +kernel
theorem cell_25_76_2 : C 25 76 2 := by decide +kernel
theorem cell_25_76_3 : C 25 76 3 := by decide +kernel
theorem cell_25_76_4 : C 25 76 4 := by decide +kernel
theorem cell_25_76_5 : C 25 76 5 := by decide +kernel
theorem row_25_76 : ThresholdAt 25 76 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 76 0 cell_25_76_0
  | exact S 25 76 1 cell_25_76_1
  | exact S 25 76 2 cell_25_76_2
  | exact S 25 76 3 cell_25_76_3
  | exact S 25 76 4 cell_25_76_4
  | exact S 25 76 5 cell_25_76_5
theorem cell_25_77_0 : C 25 77 0 := by decide +kernel
theorem cell_25_77_1 : C 25 77 1 := by decide +kernel
theorem cell_25_77_2 : C 25 77 2 := by decide +kernel
theorem cell_25_77_3 : C 25 77 3 := by decide +kernel
theorem cell_25_77_4 : C 25 77 4 := by decide +kernel
theorem cell_25_77_5 : C 25 77 5 := by decide +kernel
theorem row_25_77 : ThresholdAt 25 77 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 77 0 cell_25_77_0
  | exact S 25 77 1 cell_25_77_1
  | exact S 25 77 2 cell_25_77_2
  | exact S 25 77 3 cell_25_77_3
  | exact S 25 77 4 cell_25_77_4
  | exact S 25 77 5 cell_25_77_5
theorem cell_25_78_0 : C 25 78 0 := by decide +kernel
theorem cell_25_78_1 : C 25 78 1 := by decide +kernel
theorem cell_25_78_2 : C 25 78 2 := by decide +kernel
theorem cell_25_78_3 : C 25 78 3 := by decide +kernel
theorem cell_25_78_4 : C 25 78 4 := by decide +kernel
theorem cell_25_78_5 : C 25 78 5 := by decide +kernel
theorem row_25_78 : ThresholdAt 25 78 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 78 0 cell_25_78_0
  | exact S 25 78 1 cell_25_78_1
  | exact S 25 78 2 cell_25_78_2
  | exact S 25 78 3 cell_25_78_3
  | exact S 25 78 4 cell_25_78_4
  | exact S 25 78 5 cell_25_78_5
theorem cell_25_79_0 : C 25 79 0 := by decide +kernel
theorem cell_25_79_1 : C 25 79 1 := by decide +kernel
theorem cell_25_79_2 : C 25 79 2 := by decide +kernel
theorem cell_25_79_3 : C 25 79 3 := by decide +kernel
theorem cell_25_79_4 : C 25 79 4 := by decide +kernel
theorem cell_25_79_5 : C 25 79 5 := by decide +kernel
theorem row_25_79 : ThresholdAt 25 79 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 79 0 cell_25_79_0
  | exact S 25 79 1 cell_25_79_1
  | exact S 25 79 2 cell_25_79_2
  | exact S 25 79 3 cell_25_79_3
  | exact S 25 79 4 cell_25_79_4
  | exact S 25 79 5 cell_25_79_5
theorem cell_25_80_0 : C 25 80 0 := by decide +kernel
theorem cell_25_80_1 : C 25 80 1 := by decide +kernel
theorem cell_25_80_2 : C 25 80 2 := by decide +kernel
theorem cell_25_80_3 : C 25 80 3 := by decide +kernel
theorem cell_25_80_4 : C 25 80 4 := by decide +kernel
theorem cell_25_80_5 : C 25 80 5 := by decide +kernel
theorem row_25_80 : ThresholdAt 25 80 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 80 0 cell_25_80_0
  | exact S 25 80 1 cell_25_80_1
  | exact S 25 80 2 cell_25_80_2
  | exact S 25 80 3 cell_25_80_3
  | exact S 25 80 4 cell_25_80_4
  | exact S 25 80 5 cell_25_80_5
theorem cell_25_81_0 : C 25 81 0 := by decide +kernel
theorem cell_25_81_1 : C 25 81 1 := by decide +kernel
theorem cell_25_81_2 : C 25 81 2 := by decide +kernel
theorem cell_25_81_3 : C 25 81 3 := by decide +kernel
theorem cell_25_81_4 : C 25 81 4 := by decide +kernel
theorem cell_25_81_5 : C 25 81 5 := by decide +kernel
theorem row_25_81 : ThresholdAt 25 81 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 81 0 cell_25_81_0
  | exact S 25 81 1 cell_25_81_1
  | exact S 25 81 2 cell_25_81_2
  | exact S 25 81 3 cell_25_81_3
  | exact S 25 81 4 cell_25_81_4
  | exact S 25 81 5 cell_25_81_5
theorem cell_25_82_0 : C 25 82 0 := by decide +kernel
theorem cell_25_82_1 : C 25 82 1 := by decide +kernel
theorem cell_25_82_2 : C 25 82 2 := by decide +kernel
theorem cell_25_82_3 : C 25 82 3 := by decide +kernel
theorem cell_25_82_4 : C 25 82 4 := by decide +kernel
theorem cell_25_82_5 : C 25 82 5 := by decide +kernel
theorem row_25_82 : ThresholdAt 25 82 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 82 0 cell_25_82_0
  | exact S 25 82 1 cell_25_82_1
  | exact S 25 82 2 cell_25_82_2
  | exact S 25 82 3 cell_25_82_3
  | exact S 25 82 4 cell_25_82_4
  | exact S 25 82 5 cell_25_82_5
theorem cell_25_83_0 : C 25 83 0 := by decide +kernel
theorem cell_25_83_1 : C 25 83 1 := by decide +kernel
theorem cell_25_83_2 : C 25 83 2 := by decide +kernel
theorem cell_25_83_3 : C 25 83 3 := by decide +kernel
theorem cell_25_83_4 : C 25 83 4 := by decide +kernel
theorem cell_25_83_5 : C 25 83 5 := by decide +kernel
theorem row_25_83 : ThresholdAt 25 83 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 83 0 cell_25_83_0
  | exact S 25 83 1 cell_25_83_1
  | exact S 25 83 2 cell_25_83_2
  | exact S 25 83 3 cell_25_83_3
  | exact S 25 83 4 cell_25_83_4
  | exact S 25 83 5 cell_25_83_5
theorem cell_25_84_0 : C 25 84 0 := by decide +kernel
theorem cell_25_84_1 : C 25 84 1 := by decide +kernel
theorem cell_25_84_2 : C 25 84 2 := by decide +kernel
theorem cell_25_84_3 : C 25 84 3 := by decide +kernel
theorem cell_25_84_4 : C 25 84 4 := by decide +kernel
theorem cell_25_84_5 : C 25 84 5 := by decide +kernel
theorem row_25_84 : ThresholdAt 25 84 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 84 0 cell_25_84_0
  | exact S 25 84 1 cell_25_84_1
  | exact S 25 84 2 cell_25_84_2
  | exact S 25 84 3 cell_25_84_3
  | exact S 25 84 4 cell_25_84_4
  | exact S 25 84 5 cell_25_84_5
theorem cell_25_85_0 : C 25 85 0 := by decide +kernel
theorem cell_25_85_1 : C 25 85 1 := by decide +kernel
theorem cell_25_85_2 : C 25 85 2 := by decide +kernel
theorem cell_25_85_3 : C 25 85 3 := by decide +kernel
theorem cell_25_85_4 : C 25 85 4 := by decide +kernel
theorem cell_25_85_5 : C 25 85 5 := by decide +kernel
theorem row_25_85 : ThresholdAt 25 85 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 85 0 cell_25_85_0
  | exact S 25 85 1 cell_25_85_1
  | exact S 25 85 2 cell_25_85_2
  | exact S 25 85 3 cell_25_85_3
  | exact S 25 85 4 cell_25_85_4
  | exact S 25 85 5 cell_25_85_5
theorem cell_25_86_0 : C 25 86 0 := by decide +kernel
theorem cell_25_86_1 : C 25 86 1 := by decide +kernel
theorem cell_25_86_2 : C 25 86 2 := by decide +kernel
theorem cell_25_86_3 : C 25 86 3 := by decide +kernel
theorem cell_25_86_4 : C 25 86 4 := by decide +kernel
theorem cell_25_86_5 : C 25 86 5 := by decide +kernel
theorem row_25_86 : ThresholdAt 25 86 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 86 0 cell_25_86_0
  | exact S 25 86 1 cell_25_86_1
  | exact S 25 86 2 cell_25_86_2
  | exact S 25 86 3 cell_25_86_3
  | exact S 25 86 4 cell_25_86_4
  | exact S 25 86 5 cell_25_86_5
theorem cell_25_87_0 : C 25 87 0 := by decide +kernel
theorem cell_25_87_1 : C 25 87 1 := by decide +kernel
theorem cell_25_87_2 : C 25 87 2 := by decide +kernel
theorem cell_25_87_3 : C 25 87 3 := by decide +kernel
theorem cell_25_87_4 : C 25 87 4 := by decide +kernel
theorem cell_25_87_5 : C 25 87 5 := by decide +kernel
theorem row_25_87 : ThresholdAt 25 87 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 87 0 cell_25_87_0
  | exact S 25 87 1 cell_25_87_1
  | exact S 25 87 2 cell_25_87_2
  | exact S 25 87 3 cell_25_87_3
  | exact S 25 87 4 cell_25_87_4
  | exact S 25 87 5 cell_25_87_5
theorem cell_25_88_0 : C 25 88 0 := by decide +kernel
theorem cell_25_88_1 : C 25 88 1 := by decide +kernel
theorem cell_25_88_2 : C 25 88 2 := by decide +kernel
theorem cell_25_88_3 : C 25 88 3 := by decide +kernel
theorem cell_25_88_4 : C 25 88 4 := by decide +kernel
theorem cell_25_88_5 : C 25 88 5 := by decide +kernel
theorem row_25_88 : ThresholdAt 25 88 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 88 0 cell_25_88_0
  | exact S 25 88 1 cell_25_88_1
  | exact S 25 88 2 cell_25_88_2
  | exact S 25 88 3 cell_25_88_3
  | exact S 25 88 4 cell_25_88_4
  | exact S 25 88 5 cell_25_88_5
theorem cell_25_89_0 : C 25 89 0 := by decide +kernel
theorem cell_25_89_1 : C 25 89 1 := by decide +kernel
theorem cell_25_89_2 : C 25 89 2 := by decide +kernel
theorem cell_25_89_3 : C 25 89 3 := by decide +kernel
theorem cell_25_89_4 : C 25 89 4 := by decide +kernel
theorem cell_25_89_5 : C 25 89 5 := by decide +kernel
theorem row_25_89 : ThresholdAt 25 89 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 89 0 cell_25_89_0
  | exact S 25 89 1 cell_25_89_1
  | exact S 25 89 2 cell_25_89_2
  | exact S 25 89 3 cell_25_89_3
  | exact S 25 89 4 cell_25_89_4
  | exact S 25 89 5 cell_25_89_5
theorem cell_25_90_0 : C 25 90 0 := by decide +kernel
theorem cell_25_90_1 : C 25 90 1 := by decide +kernel
theorem cell_25_90_2 : C 25 90 2 := by decide +kernel
theorem cell_25_90_3 : C 25 90 3 := by decide +kernel
theorem cell_25_90_4 : C 25 90 4 := by decide +kernel
theorem cell_25_90_5 : C 25 90 5 := by decide +kernel
theorem row_25_90 : ThresholdAt 25 90 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 90 0 cell_25_90_0
  | exact S 25 90 1 cell_25_90_1
  | exact S 25 90 2 cell_25_90_2
  | exact S 25 90 3 cell_25_90_3
  | exact S 25 90 4 cell_25_90_4
  | exact S 25 90 5 cell_25_90_5
theorem cell_25_91_0 : C 25 91 0 := by decide +kernel
theorem cell_25_91_1 : C 25 91 1 := by decide +kernel
theorem cell_25_91_2 : C 25 91 2 := by decide +kernel
theorem cell_25_91_3 : C 25 91 3 := by decide +kernel
theorem cell_25_91_4 : C 25 91 4 := by decide +kernel
theorem cell_25_91_5 : C 25 91 5 := by decide +kernel
theorem row_25_91 : ThresholdAt 25 91 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 91 0 cell_25_91_0
  | exact S 25 91 1 cell_25_91_1
  | exact S 25 91 2 cell_25_91_2
  | exact S 25 91 3 cell_25_91_3
  | exact S 25 91 4 cell_25_91_4
  | exact S 25 91 5 cell_25_91_5
theorem cell_25_92_0 : C 25 92 0 := by decide +kernel
theorem cell_25_92_1 : C 25 92 1 := by decide +kernel
theorem cell_25_92_2 : C 25 92 2 := by decide +kernel
theorem cell_25_92_3 : C 25 92 3 := by decide +kernel
theorem cell_25_92_4 : C 25 92 4 := by decide +kernel
theorem cell_25_92_5 : C 25 92 5 := by decide +kernel
theorem row_25_92 : ThresholdAt 25 92 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 92 0 cell_25_92_0
  | exact S 25 92 1 cell_25_92_1
  | exact S 25 92 2 cell_25_92_2
  | exact S 25 92 3 cell_25_92_3
  | exact S 25 92 4 cell_25_92_4
  | exact S 25 92 5 cell_25_92_5
theorem cell_25_93_0 : C 25 93 0 := by decide +kernel
theorem cell_25_93_1 : C 25 93 1 := by decide +kernel
theorem cell_25_93_2 : C 25 93 2 := by decide +kernel
theorem cell_25_93_3 : C 25 93 3 := by decide +kernel
theorem cell_25_93_4 : C 25 93 4 := by decide +kernel
theorem cell_25_93_5 : C 25 93 5 := by decide +kernel
theorem row_25_93 : ThresholdAt 25 93 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 93 0 cell_25_93_0
  | exact S 25 93 1 cell_25_93_1
  | exact S 25 93 2 cell_25_93_2
  | exact S 25 93 3 cell_25_93_3
  | exact S 25 93 4 cell_25_93_4
  | exact S 25 93 5 cell_25_93_5
theorem cell_25_94_0 : C 25 94 0 := by decide +kernel
theorem cell_25_94_1 : C 25 94 1 := by decide +kernel
theorem cell_25_94_2 : C 25 94 2 := by decide +kernel
theorem cell_25_94_3 : C 25 94 3 := by decide +kernel
theorem cell_25_94_4 : C 25 94 4 := by decide +kernel
theorem cell_25_94_5 : C 25 94 5 := by decide +kernel
theorem row_25_94 : ThresholdAt 25 94 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 94 0 cell_25_94_0
  | exact S 25 94 1 cell_25_94_1
  | exact S 25 94 2 cell_25_94_2
  | exact S 25 94 3 cell_25_94_3
  | exact S 25 94 4 cell_25_94_4
  | exact S 25 94 5 cell_25_94_5
theorem cell_25_95_0 : C 25 95 0 := by decide +kernel
theorem cell_25_95_1 : C 25 95 1 := by decide +kernel
theorem cell_25_95_2 : C 25 95 2 := by decide +kernel
theorem cell_25_95_3 : C 25 95 3 := by decide +kernel
theorem cell_25_95_4 : C 25 95 4 := by decide +kernel
theorem cell_25_95_5 : C 25 95 5 := by decide +kernel
theorem row_25_95 : ThresholdAt 25 95 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 95 0 cell_25_95_0
  | exact S 25 95 1 cell_25_95_1
  | exact S 25 95 2 cell_25_95_2
  | exact S 25 95 3 cell_25_95_3
  | exact S 25 95 4 cell_25_95_4
  | exact S 25 95 5 cell_25_95_5
theorem cell_25_96_0 : C 25 96 0 := by decide +kernel
theorem cell_25_96_1 : C 25 96 1 := by decide +kernel
theorem cell_25_96_2 : C 25 96 2 := by decide +kernel
theorem cell_25_96_3 : C 25 96 3 := by decide +kernel
theorem cell_25_96_4 : C 25 96 4 := by decide +kernel
theorem cell_25_96_5 : C 25 96 5 := by decide +kernel
theorem row_25_96 : ThresholdAt 25 96 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 96 0 cell_25_96_0
  | exact S 25 96 1 cell_25_96_1
  | exact S 25 96 2 cell_25_96_2
  | exact S 25 96 3 cell_25_96_3
  | exact S 25 96 4 cell_25_96_4
  | exact S 25 96 5 cell_25_96_5
theorem cell_25_97_0 : C 25 97 0 := by decide +kernel
theorem cell_25_97_1 : C 25 97 1 := by decide +kernel
theorem cell_25_97_2 : C 25 97 2 := by decide +kernel
theorem cell_25_97_3 : C 25 97 3 := by decide +kernel
theorem cell_25_97_4 : C 25 97 4 := by decide +kernel
theorem cell_25_97_5 : C 25 97 5 := by decide +kernel
theorem row_25_97 : ThresholdAt 25 97 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 97 0 cell_25_97_0
  | exact S 25 97 1 cell_25_97_1
  | exact S 25 97 2 cell_25_97_2
  | exact S 25 97 3 cell_25_97_3
  | exact S 25 97 4 cell_25_97_4
  | exact S 25 97 5 cell_25_97_5
theorem cell_25_98_0 : C 25 98 0 := by decide +kernel
theorem cell_25_98_1 : C 25 98 1 := by decide +kernel
theorem cell_25_98_2 : C 25 98 2 := by decide +kernel
theorem cell_25_98_3 : C 25 98 3 := by decide +kernel
theorem cell_25_98_4 : C 25 98 4 := by decide +kernel
theorem cell_25_98_5 : C 25 98 5 := by decide +kernel
theorem row_25_98 : ThresholdAt 25 98 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 98 0 cell_25_98_0
  | exact S 25 98 1 cell_25_98_1
  | exact S 25 98 2 cell_25_98_2
  | exact S 25 98 3 cell_25_98_3
  | exact S 25 98 4 cell_25_98_4
  | exact S 25 98 5 cell_25_98_5
theorem cell_25_99_0 : C 25 99 0 := by decide +kernel
theorem cell_25_99_1 : C 25 99 1 := by decide +kernel
theorem cell_25_99_2 : C 25 99 2 := by decide +kernel
theorem cell_25_99_3 : C 25 99 3 := by decide +kernel
theorem cell_25_99_4 : C 25 99 4 := by decide +kernel
theorem cell_25_99_5 : C 25 99 5 := by decide +kernel
theorem row_25_99 : ThresholdAt 25 99 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 99 0 cell_25_99_0
  | exact S 25 99 1 cell_25_99_1
  | exact S 25 99 2 cell_25_99_2
  | exact S 25 99 3 cell_25_99_3
  | exact S 25 99 4 cell_25_99_4
  | exact S 25 99 5 cell_25_99_5
theorem cell_25_100_0 : C 25 100 0 := by decide +kernel
theorem cell_25_100_1 : C 25 100 1 := by decide +kernel
theorem cell_25_100_2 : C 25 100 2 := by decide +kernel
theorem cell_25_100_3 : C 25 100 3 := by decide +kernel
theorem cell_25_100_4 : C 25 100 4 := by decide +kernel
theorem cell_25_100_5 : C 25 100 5 := by decide +kernel
theorem row_25_100 : ThresholdAt 25 100 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 100 0 cell_25_100_0
  | exact S 25 100 1 cell_25_100_1
  | exact S 25 100 2 cell_25_100_2
  | exact S 25 100 3 cell_25_100_3
  | exact S 25 100 4 cell_25_100_4
  | exact S 25 100 5 cell_25_100_5
theorem cell_25_101_0 : C 25 101 0 := by decide +kernel
theorem cell_25_101_1 : C 25 101 1 := by decide +kernel
theorem cell_25_101_2 : C 25 101 2 := by decide +kernel
theorem cell_25_101_3 : C 25 101 3 := by decide +kernel
theorem cell_25_101_4 : C 25 101 4 := by decide +kernel
theorem cell_25_101_5 : C 25 101 5 := by decide +kernel
theorem row_25_101 : ThresholdAt 25 101 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 101 0 cell_25_101_0
  | exact S 25 101 1 cell_25_101_1
  | exact S 25 101 2 cell_25_101_2
  | exact S 25 101 3 cell_25_101_3
  | exact S 25 101 4 cell_25_101_4
  | exact S 25 101 5 cell_25_101_5
theorem cell_25_102_0 : C 25 102 0 := by decide +kernel
theorem cell_25_102_1 : C 25 102 1 := by decide +kernel
theorem cell_25_102_2 : C 25 102 2 := by decide +kernel
theorem cell_25_102_3 : C 25 102 3 := by decide +kernel
theorem cell_25_102_4 : C 25 102 4 := by decide +kernel
theorem cell_25_102_5 : C 25 102 5 := by decide +kernel
theorem row_25_102 : ThresholdAt 25 102 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 102 0 cell_25_102_0
  | exact S 25 102 1 cell_25_102_1
  | exact S 25 102 2 cell_25_102_2
  | exact S 25 102 3 cell_25_102_3
  | exact S 25 102 4 cell_25_102_4
  | exact S 25 102 5 cell_25_102_5
theorem cell_25_103_0 : C 25 103 0 := by decide +kernel
theorem cell_25_103_1 : C 25 103 1 := by decide +kernel
theorem cell_25_103_2 : C 25 103 2 := by decide +kernel
theorem cell_25_103_3 : C 25 103 3 := by decide +kernel
theorem cell_25_103_4 : C 25 103 4 := by decide +kernel
theorem cell_25_103_5 : C 25 103 5 := by decide +kernel
theorem row_25_103 : ThresholdAt 25 103 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 103 0 cell_25_103_0
  | exact S 25 103 1 cell_25_103_1
  | exact S 25 103 2 cell_25_103_2
  | exact S 25 103 3 cell_25_103_3
  | exact S 25 103 4 cell_25_103_4
  | exact S 25 103 5 cell_25_103_5
theorem cell_25_104_0 : C 25 104 0 := by decide +kernel
theorem cell_25_104_1 : C 25 104 1 := by decide +kernel
theorem cell_25_104_2 : C 25 104 2 := by decide +kernel
theorem cell_25_104_3 : C 25 104 3 := by decide +kernel
theorem cell_25_104_4 : C 25 104 4 := by decide +kernel
theorem cell_25_104_5 : C 25 104 5 := by decide +kernel
theorem row_25_104 : ThresholdAt 25 104 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 104 0 cell_25_104_0
  | exact S 25 104 1 cell_25_104_1
  | exact S 25 104 2 cell_25_104_2
  | exact S 25 104 3 cell_25_104_3
  | exact S 25 104 4 cell_25_104_4
  | exact S 25 104 5 cell_25_104_5
theorem cell_25_105_0 : C 25 105 0 := by decide +kernel
theorem cell_25_105_1 : C 25 105 1 := by decide +kernel
theorem cell_25_105_2 : C 25 105 2 := by decide +kernel
theorem cell_25_105_3 : C 25 105 3 := by decide +kernel
theorem cell_25_105_4 : C 25 105 4 := by decide +kernel
theorem cell_25_105_5 : C 25 105 5 := by decide +kernel
theorem row_25_105 : ThresholdAt 25 105 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 105 0 cell_25_105_0
  | exact S 25 105 1 cell_25_105_1
  | exact S 25 105 2 cell_25_105_2
  | exact S 25 105 3 cell_25_105_3
  | exact S 25 105 4 cell_25_105_4
  | exact S 25 105 5 cell_25_105_5
theorem cell_25_106_0 : C 25 106 0 := by decide +kernel
theorem cell_25_106_1 : C 25 106 1 := by decide +kernel
theorem cell_25_106_2 : C 25 106 2 := by decide +kernel
theorem cell_25_106_3 : C 25 106 3 := by decide +kernel
theorem cell_25_106_4 : C 25 106 4 := by decide +kernel
theorem cell_25_106_5 : C 25 106 5 := by decide +kernel
theorem row_25_106 : ThresholdAt 25 106 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 106 0 cell_25_106_0
  | exact S 25 106 1 cell_25_106_1
  | exact S 25 106 2 cell_25_106_2
  | exact S 25 106 3 cell_25_106_3
  | exact S 25 106 4 cell_25_106_4
  | exact S 25 106 5 cell_25_106_5
theorem cell_25_107_0 : C 25 107 0 := by decide +kernel
theorem cell_25_107_1 : C 25 107 1 := by decide +kernel
theorem cell_25_107_2 : C 25 107 2 := by decide +kernel
theorem cell_25_107_3 : C 25 107 3 := by decide +kernel
theorem cell_25_107_4 : C 25 107 4 := by decide +kernel
theorem cell_25_107_5 : C 25 107 5 := by decide +kernel
theorem row_25_107 : ThresholdAt 25 107 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 107 0 cell_25_107_0
  | exact S 25 107 1 cell_25_107_1
  | exact S 25 107 2 cell_25_107_2
  | exact S 25 107 3 cell_25_107_3
  | exact S 25 107 4 cell_25_107_4
  | exact S 25 107 5 cell_25_107_5
theorem cell_25_108_0 : C 25 108 0 := by decide +kernel
theorem cell_25_108_1 : C 25 108 1 := by decide +kernel
theorem cell_25_108_2 : C 25 108 2 := by decide +kernel
theorem cell_25_108_3 : C 25 108 3 := by decide +kernel
theorem cell_25_108_4 : C 25 108 4 := by decide +kernel
theorem cell_25_108_5 : C 25 108 5 := by decide +kernel
theorem row_25_108 : ThresholdAt 25 108 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 108 0 cell_25_108_0
  | exact S 25 108 1 cell_25_108_1
  | exact S 25 108 2 cell_25_108_2
  | exact S 25 108 3 cell_25_108_3
  | exact S 25 108 4 cell_25_108_4
  | exact S 25 108 5 cell_25_108_5
theorem cell_25_109_0 : C 25 109 0 := by decide +kernel
theorem cell_25_109_1 : C 25 109 1 := by decide +kernel
theorem cell_25_109_2 : C 25 109 2 := by decide +kernel
theorem cell_25_109_3 : C 25 109 3 := by decide +kernel
theorem cell_25_109_4 : C 25 109 4 := by decide +kernel
theorem cell_25_109_5 : C 25 109 5 := by decide +kernel
theorem row_25_109 : ThresholdAt 25 109 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 109 0 cell_25_109_0
  | exact S 25 109 1 cell_25_109_1
  | exact S 25 109 2 cell_25_109_2
  | exact S 25 109 3 cell_25_109_3
  | exact S 25 109 4 cell_25_109_4
  | exact S 25 109 5 cell_25_109_5
theorem cell_25_110_0 : C 25 110 0 := by decide +kernel
theorem cell_25_110_1 : C 25 110 1 := by decide +kernel
theorem cell_25_110_2 : C 25 110 2 := by decide +kernel
theorem cell_25_110_3 : C 25 110 3 := by decide +kernel
theorem cell_25_110_4 : C 25 110 4 := by decide +kernel
theorem cell_25_110_5 : C 25 110 5 := by decide +kernel
theorem row_25_110 : ThresholdAt 25 110 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 110 0 cell_25_110_0
  | exact S 25 110 1 cell_25_110_1
  | exact S 25 110 2 cell_25_110_2
  | exact S 25 110 3 cell_25_110_3
  | exact S 25 110 4 cell_25_110_4
  | exact S 25 110 5 cell_25_110_5
theorem cell_25_111_0 : C 25 111 0 := by decide +kernel
theorem cell_25_111_1 : C 25 111 1 := by decide +kernel
theorem cell_25_111_2 : C 25 111 2 := by decide +kernel
theorem cell_25_111_3 : C 25 111 3 := by decide +kernel
theorem cell_25_111_4 : C 25 111 4 := by decide +kernel
theorem cell_25_111_5 : C 25 111 5 := by decide +kernel
theorem row_25_111 : ThresholdAt 25 111 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 111 0 cell_25_111_0
  | exact S 25 111 1 cell_25_111_1
  | exact S 25 111 2 cell_25_111_2
  | exact S 25 111 3 cell_25_111_3
  | exact S 25 111 4 cell_25_111_4
  | exact S 25 111 5 cell_25_111_5
theorem cell_25_112_0 : C 25 112 0 := by decide +kernel
theorem cell_25_112_1 : C 25 112 1 := by decide +kernel
theorem cell_25_112_2 : C 25 112 2 := by decide +kernel
theorem cell_25_112_3 : C 25 112 3 := by decide +kernel
theorem cell_25_112_4 : C 25 112 4 := by decide +kernel
theorem cell_25_112_5 : C 25 112 5 := by decide +kernel
theorem row_25_112 : ThresholdAt 25 112 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 112 0 cell_25_112_0
  | exact S 25 112 1 cell_25_112_1
  | exact S 25 112 2 cell_25_112_2
  | exact S 25 112 3 cell_25_112_3
  | exact S 25 112 4 cell_25_112_4
  | exact S 25 112 5 cell_25_112_5
theorem cell_25_113_0 : C 25 113 0 := by decide +kernel
theorem cell_25_113_1 : C 25 113 1 := by decide +kernel
theorem cell_25_113_2 : C 25 113 2 := by decide +kernel
theorem cell_25_113_3 : C 25 113 3 := by decide +kernel
theorem cell_25_113_4 : C 25 113 4 := by decide +kernel
theorem cell_25_113_5 : C 25 113 5 := by decide +kernel
theorem row_25_113 : ThresholdAt 25 113 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 113 0 cell_25_113_0
  | exact S 25 113 1 cell_25_113_1
  | exact S 25 113 2 cell_25_113_2
  | exact S 25 113 3 cell_25_113_3
  | exact S 25 113 4 cell_25_113_4
  | exact S 25 113 5 cell_25_113_5
theorem cell_25_114_0 : C 25 114 0 := by decide +kernel
theorem cell_25_114_1 : C 25 114 1 := by decide +kernel
theorem cell_25_114_2 : C 25 114 2 := by decide +kernel
theorem cell_25_114_3 : C 25 114 3 := by decide +kernel
theorem cell_25_114_4 : C 25 114 4 := by decide +kernel
theorem cell_25_114_5 : C 25 114 5 := by decide +kernel
theorem row_25_114 : ThresholdAt 25 114 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 25 114 0 cell_25_114_0
  | exact S 25 114 1 cell_25_114_1
  | exact S 25 114 2 cell_25_114_2
  | exact S 25 114 3 cell_25_114_3
  | exact S 25 114 4 cell_25_114_4
  | exact S 25 114 5 cell_25_114_5
theorem checkedR25 : ∀ V ∈ List.range 115, ThresholdAt 25 V := by
  intro V hV
  have hv : V < 115 := List.mem_range.mp hV
  by_cases h0_115 : V < 57
  · by_cases h0_57 : V < 28
    · by_cases h0_28 : V < 14
      · by_cases h0_14 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have he : V = 0 := by omega
              subst V
              exact row_25_0
            · by_cases h1_3 : V < 2
              · have he : V = 1 := by omega
                subst V
                exact row_25_1
              · have he : V = 2 := by omega
                subst V
                exact row_25_2
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have he : V = 3 := by omega
                subst V
                exact row_25_3
              · have he : V = 4 := by omega
                subst V
                exact row_25_4
            · by_cases h5_7 : V < 6
              · have he : V = 5 := by omega
                subst V
                exact row_25_5
              · have he : V = 6 := by omega
                subst V
                exact row_25_6
        · by_cases h7_14 : V < 10
          · by_cases h7_10 : V < 8
            · have he : V = 7 := by omega
              subst V
              exact row_25_7
            · by_cases h8_10 : V < 9
              · have he : V = 8 := by omega
                subst V
                exact row_25_8
              · have he : V = 9 := by omega
                subst V
                exact row_25_9
          · by_cases h10_14 : V < 12
            · by_cases h10_12 : V < 11
              · have he : V = 10 := by omega
                subst V
                exact row_25_10
              · have he : V = 11 := by omega
                subst V
                exact row_25_11
            · by_cases h12_14 : V < 13
              · have he : V = 12 := by omega
                subst V
                exact row_25_12
              · have he : V = 13 := by omega
                subst V
                exact row_25_13
      · by_cases h14_28 : V < 21
        · by_cases h14_21 : V < 17
          · by_cases h14_17 : V < 15
            · have he : V = 14 := by omega
              subst V
              exact row_25_14
            · by_cases h15_17 : V < 16
              · have he : V = 15 := by omega
                subst V
                exact row_25_15
              · have he : V = 16 := by omega
                subst V
                exact row_25_16
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have he : V = 17 := by omega
                subst V
                exact row_25_17
              · have he : V = 18 := by omega
                subst V
                exact row_25_18
            · by_cases h19_21 : V < 20
              · have he : V = 19 := by omega
                subst V
                exact row_25_19
              · have he : V = 20 := by omega
                subst V
                exact row_25_20
        · by_cases h21_28 : V < 24
          · by_cases h21_24 : V < 22
            · have he : V = 21 := by omega
              subst V
              exact row_25_21
            · by_cases h22_24 : V < 23
              · have he : V = 22 := by omega
                subst V
                exact row_25_22
              · have he : V = 23 := by omega
                subst V
                exact row_25_23
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have he : V = 24 := by omega
                subst V
                exact row_25_24
              · have he : V = 25 := by omega
                subst V
                exact row_25_25
            · by_cases h26_28 : V < 27
              · have he : V = 26 := by omega
                subst V
                exact row_25_26
              · have he : V = 27 := by omega
                subst V
                exact row_25_27
    · by_cases h28_57 : V < 42
      · by_cases h28_42 : V < 35
        · by_cases h28_35 : V < 31
          · by_cases h28_31 : V < 29
            · have he : V = 28 := by omega
              subst V
              exact row_25_28
            · by_cases h29_31 : V < 30
              · have he : V = 29 := by omega
                subst V
                exact row_25_29
              · have he : V = 30 := by omega
                subst V
                exact row_25_30
          · by_cases h31_35 : V < 33
            · by_cases h31_33 : V < 32
              · have he : V = 31 := by omega
                subst V
                exact row_25_31
              · have he : V = 32 := by omega
                subst V
                exact row_25_32
            · by_cases h33_35 : V < 34
              · have he : V = 33 := by omega
                subst V
                exact row_25_33
              · have he : V = 34 := by omega
                subst V
                exact row_25_34
        · by_cases h35_42 : V < 38
          · by_cases h35_38 : V < 36
            · have he : V = 35 := by omega
              subst V
              exact row_25_35
            · by_cases h36_38 : V < 37
              · have he : V = 36 := by omega
                subst V
                exact row_25_36
              · have he : V = 37 := by omega
                subst V
                exact row_25_37
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have he : V = 38 := by omega
                subst V
                exact row_25_38
              · have he : V = 39 := by omega
                subst V
                exact row_25_39
            · by_cases h40_42 : V < 41
              · have he : V = 40 := by omega
                subst V
                exact row_25_40
              · have he : V = 41 := by omega
                subst V
                exact row_25_41
      · by_cases h42_57 : V < 49
        · by_cases h42_49 : V < 45
          · by_cases h42_45 : V < 43
            · have he : V = 42 := by omega
              subst V
              exact row_25_42
            · by_cases h43_45 : V < 44
              · have he : V = 43 := by omega
                subst V
                exact row_25_43
              · have he : V = 44 := by omega
                subst V
                exact row_25_44
          · by_cases h45_49 : V < 47
            · by_cases h45_47 : V < 46
              · have he : V = 45 := by omega
                subst V
                exact row_25_45
              · have he : V = 46 := by omega
                subst V
                exact row_25_46
            · by_cases h47_49 : V < 48
              · have he : V = 47 := by omega
                subst V
                exact row_25_47
              · have he : V = 48 := by omega
                subst V
                exact row_25_48
        · by_cases h49_57 : V < 53
          · by_cases h49_53 : V < 51
            · by_cases h49_51 : V < 50
              · have he : V = 49 := by omega
                subst V
                exact row_25_49
              · have he : V = 50 := by omega
                subst V
                exact row_25_50
            · by_cases h51_53 : V < 52
              · have he : V = 51 := by omega
                subst V
                exact row_25_51
              · have he : V = 52 := by omega
                subst V
                exact row_25_52
          · by_cases h53_57 : V < 55
            · by_cases h53_55 : V < 54
              · have he : V = 53 := by omega
                subst V
                exact row_25_53
              · have he : V = 54 := by omega
                subst V
                exact row_25_54
            · by_cases h55_57 : V < 56
              · have he : V = 55 := by omega
                subst V
                exact row_25_55
              · have he : V = 56 := by omega
                subst V
                exact row_25_56
  · by_cases h57_115 : V < 86
    · by_cases h57_86 : V < 71
      · by_cases h57_71 : V < 64
        · by_cases h57_64 : V < 60
          · by_cases h57_60 : V < 58
            · have he : V = 57 := by omega
              subst V
              exact row_25_57
            · by_cases h58_60 : V < 59
              · have he : V = 58 := by omega
                subst V
                exact row_25_58
              · have he : V = 59 := by omega
                subst V
                exact row_25_59
          · by_cases h60_64 : V < 62
            · by_cases h60_62 : V < 61
              · have he : V = 60 := by omega
                subst V
                exact row_25_60
              · have he : V = 61 := by omega
                subst V
                exact row_25_61
            · by_cases h62_64 : V < 63
              · have he : V = 62 := by omega
                subst V
                exact row_25_62
              · have he : V = 63 := by omega
                subst V
                exact row_25_63
        · by_cases h64_71 : V < 67
          · by_cases h64_67 : V < 65
            · have he : V = 64 := by omega
              subst V
              exact row_25_64
            · by_cases h65_67 : V < 66
              · have he : V = 65 := by omega
                subst V
                exact row_25_65
              · have he : V = 66 := by omega
                subst V
                exact row_25_66
          · by_cases h67_71 : V < 69
            · by_cases h67_69 : V < 68
              · have he : V = 67 := by omega
                subst V
                exact row_25_67
              · have he : V = 68 := by omega
                subst V
                exact row_25_68
            · by_cases h69_71 : V < 70
              · have he : V = 69 := by omega
                subst V
                exact row_25_69
              · have he : V = 70 := by omega
                subst V
                exact row_25_70
      · by_cases h71_86 : V < 78
        · by_cases h71_78 : V < 74
          · by_cases h71_74 : V < 72
            · have he : V = 71 := by omega
              subst V
              exact row_25_71
            · by_cases h72_74 : V < 73
              · have he : V = 72 := by omega
                subst V
                exact row_25_72
              · have he : V = 73 := by omega
                subst V
                exact row_25_73
          · by_cases h74_78 : V < 76
            · by_cases h74_76 : V < 75
              · have he : V = 74 := by omega
                subst V
                exact row_25_74
              · have he : V = 75 := by omega
                subst V
                exact row_25_75
            · by_cases h76_78 : V < 77
              · have he : V = 76 := by omega
                subst V
                exact row_25_76
              · have he : V = 77 := by omega
                subst V
                exact row_25_77
        · by_cases h78_86 : V < 82
          · by_cases h78_82 : V < 80
            · by_cases h78_80 : V < 79
              · have he : V = 78 := by omega
                subst V
                exact row_25_78
              · have he : V = 79 := by omega
                subst V
                exact row_25_79
            · by_cases h80_82 : V < 81
              · have he : V = 80 := by omega
                subst V
                exact row_25_80
              · have he : V = 81 := by omega
                subst V
                exact row_25_81
          · by_cases h82_86 : V < 84
            · by_cases h82_84 : V < 83
              · have he : V = 82 := by omega
                subst V
                exact row_25_82
              · have he : V = 83 := by omega
                subst V
                exact row_25_83
            · by_cases h84_86 : V < 85
              · have he : V = 84 := by omega
                subst V
                exact row_25_84
              · have he : V = 85 := by omega
                subst V
                exact row_25_85
    · by_cases h86_115 : V < 100
      · by_cases h86_100 : V < 93
        · by_cases h86_93 : V < 89
          · by_cases h86_89 : V < 87
            · have he : V = 86 := by omega
              subst V
              exact row_25_86
            · by_cases h87_89 : V < 88
              · have he : V = 87 := by omega
                subst V
                exact row_25_87
              · have he : V = 88 := by omega
                subst V
                exact row_25_88
          · by_cases h89_93 : V < 91
            · by_cases h89_91 : V < 90
              · have he : V = 89 := by omega
                subst V
                exact row_25_89
              · have he : V = 90 := by omega
                subst V
                exact row_25_90
            · by_cases h91_93 : V < 92
              · have he : V = 91 := by omega
                subst V
                exact row_25_91
              · have he : V = 92 := by omega
                subst V
                exact row_25_92
        · by_cases h93_100 : V < 96
          · by_cases h93_96 : V < 94
            · have he : V = 93 := by omega
              subst V
              exact row_25_93
            · by_cases h94_96 : V < 95
              · have he : V = 94 := by omega
                subst V
                exact row_25_94
              · have he : V = 95 := by omega
                subst V
                exact row_25_95
          · by_cases h96_100 : V < 98
            · by_cases h96_98 : V < 97
              · have he : V = 96 := by omega
                subst V
                exact row_25_96
              · have he : V = 97 := by omega
                subst V
                exact row_25_97
            · by_cases h98_100 : V < 99
              · have he : V = 98 := by omega
                subst V
                exact row_25_98
              · have he : V = 99 := by omega
                subst V
                exact row_25_99
      · by_cases h100_115 : V < 107
        · by_cases h100_107 : V < 103
          · by_cases h100_103 : V < 101
            · have he : V = 100 := by omega
              subst V
              exact row_25_100
            · by_cases h101_103 : V < 102
              · have he : V = 101 := by omega
                subst V
                exact row_25_101
              · have he : V = 102 := by omega
                subst V
                exact row_25_102
          · by_cases h103_107 : V < 105
            · by_cases h103_105 : V < 104
              · have he : V = 103 := by omega
                subst V
                exact row_25_103
              · have he : V = 104 := by omega
                subst V
                exact row_25_104
            · by_cases h105_107 : V < 106
              · have he : V = 105 := by omega
                subst V
                exact row_25_105
              · have he : V = 106 := by omega
                subst V
                exact row_25_106
        · by_cases h107_115 : V < 111
          · by_cases h107_111 : V < 109
            · by_cases h107_109 : V < 108
              · have he : V = 107 := by omega
                subst V
                exact row_25_107
              · have he : V = 108 := by omega
                subst V
                exact row_25_108
            · by_cases h109_111 : V < 110
              · have he : V = 109 := by omega
                subst V
                exact row_25_109
              · have he : V = 110 := by omega
                subst V
                exact row_25_110
          · by_cases h111_115 : V < 113
            · by_cases h111_113 : V < 112
              · have he : V = 111 := by omega
                subst V
                exact row_25_111
              · have he : V = 112 := by omega
                subst V
                exact row_25_112
            · by_cases h113_115 : V < 114
              · have he : V = 113 := by omega
                subst V
                exact row_25_113
              · have he : V = 114 := by omega
                subst V
                exact row_25_114
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
