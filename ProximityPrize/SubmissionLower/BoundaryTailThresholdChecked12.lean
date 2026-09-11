import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked11

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem cell_12_0_0 : C 12 0 0 := by decide +kernel
theorem cell_12_0_1 : C 12 0 1 := by decide +kernel
theorem cell_12_0_2 : C 12 0 2 := by decide +kernel
theorem cell_12_0_3 : C 12 0 3 := by decide +kernel
theorem cell_12_0_4 : C 12 0 4 := by decide +kernel
theorem cell_12_0_5 : C 12 0 5 := by decide +kernel
theorem row_12_0 : ThresholdAt 12 0 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 0 0 cell_12_0_0
  | exact S 12 0 1 cell_12_0_1
  | exact S 12 0 2 cell_12_0_2
  | exact S 12 0 3 cell_12_0_3
  | exact S 12 0 4 cell_12_0_4
  | exact S 12 0 5 cell_12_0_5
theorem cell_12_1_0 : C 12 1 0 := by decide +kernel
theorem cell_12_1_1 : C 12 1 1 := by decide +kernel
theorem cell_12_1_2 : C 12 1 2 := by decide +kernel
theorem cell_12_1_3 : C 12 1 3 := by decide +kernel
theorem cell_12_1_4 : C 12 1 4 := by decide +kernel
theorem cell_12_1_5 : C 12 1 5 := by decide +kernel
theorem row_12_1 : ThresholdAt 12 1 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 1 0 cell_12_1_0
  | exact S 12 1 1 cell_12_1_1
  | exact S 12 1 2 cell_12_1_2
  | exact S 12 1 3 cell_12_1_3
  | exact S 12 1 4 cell_12_1_4
  | exact S 12 1 5 cell_12_1_5
theorem cell_12_2_0 : C 12 2 0 := by decide +kernel
theorem cell_12_2_1 : C 12 2 1 := by decide +kernel
theorem cell_12_2_2 : C 12 2 2 := by decide +kernel
theorem cell_12_2_3 : C 12 2 3 := by decide +kernel
theorem cell_12_2_4 : C 12 2 4 := by decide +kernel
theorem cell_12_2_5 : C 12 2 5 := by decide +kernel
theorem row_12_2 : ThresholdAt 12 2 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 2 0 cell_12_2_0
  | exact S 12 2 1 cell_12_2_1
  | exact S 12 2 2 cell_12_2_2
  | exact S 12 2 3 cell_12_2_3
  | exact S 12 2 4 cell_12_2_4
  | exact S 12 2 5 cell_12_2_5
theorem cell_12_3_0 : C 12 3 0 := by decide +kernel
theorem cell_12_3_1 : C 12 3 1 := by decide +kernel
theorem cell_12_3_2 : C 12 3 2 := by decide +kernel
theorem cell_12_3_3 : C 12 3 3 := by decide +kernel
theorem cell_12_3_4 : C 12 3 4 := by decide +kernel
theorem cell_12_3_5 : C 12 3 5 := by decide +kernel
theorem row_12_3 : ThresholdAt 12 3 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 3 0 cell_12_3_0
  | exact S 12 3 1 cell_12_3_1
  | exact S 12 3 2 cell_12_3_2
  | exact S 12 3 3 cell_12_3_3
  | exact S 12 3 4 cell_12_3_4
  | exact S 12 3 5 cell_12_3_5
theorem cell_12_4_0 : C 12 4 0 := by decide +kernel
theorem cell_12_4_1 : C 12 4 1 := by decide +kernel
theorem cell_12_4_2 : C 12 4 2 := by decide +kernel
theorem cell_12_4_3 : C 12 4 3 := by decide +kernel
theorem cell_12_4_4 : C 12 4 4 := by decide +kernel
theorem cell_12_4_5 : C 12 4 5 := by decide +kernel
theorem row_12_4 : ThresholdAt 12 4 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 4 0 cell_12_4_0
  | exact S 12 4 1 cell_12_4_1
  | exact S 12 4 2 cell_12_4_2
  | exact S 12 4 3 cell_12_4_3
  | exact S 12 4 4 cell_12_4_4
  | exact S 12 4 5 cell_12_4_5
theorem cell_12_5_0 : C 12 5 0 := by decide +kernel
theorem cell_12_5_1 : C 12 5 1 := by decide +kernel
theorem cell_12_5_2 : C 12 5 2 := by decide +kernel
theorem cell_12_5_3 : C 12 5 3 := by decide +kernel
theorem cell_12_5_4 : C 12 5 4 := by decide +kernel
theorem cell_12_5_5 : C 12 5 5 := by decide +kernel
theorem row_12_5 : ThresholdAt 12 5 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 5 0 cell_12_5_0
  | exact S 12 5 1 cell_12_5_1
  | exact S 12 5 2 cell_12_5_2
  | exact S 12 5 3 cell_12_5_3
  | exact S 12 5 4 cell_12_5_4
  | exact S 12 5 5 cell_12_5_5
theorem cell_12_6_0 : C 12 6 0 := by decide +kernel
theorem cell_12_6_1 : C 12 6 1 := by decide +kernel
theorem cell_12_6_2 : C 12 6 2 := by decide +kernel
theorem cell_12_6_3 : C 12 6 3 := by decide +kernel
theorem cell_12_6_4 : C 12 6 4 := by decide +kernel
theorem cell_12_6_5 : C 12 6 5 := by decide +kernel
theorem row_12_6 : ThresholdAt 12 6 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 6 0 cell_12_6_0
  | exact S 12 6 1 cell_12_6_1
  | exact S 12 6 2 cell_12_6_2
  | exact S 12 6 3 cell_12_6_3
  | exact S 12 6 4 cell_12_6_4
  | exact S 12 6 5 cell_12_6_5
theorem cell_12_7_0 : C 12 7 0 := by decide +kernel
theorem cell_12_7_1 : C 12 7 1 := by decide +kernel
theorem cell_12_7_2 : C 12 7 2 := by decide +kernel
theorem cell_12_7_3 : C 12 7 3 := by decide +kernel
theorem cell_12_7_4 : C 12 7 4 := by decide +kernel
theorem cell_12_7_5 : C 12 7 5 := by decide +kernel
theorem row_12_7 : ThresholdAt 12 7 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 7 0 cell_12_7_0
  | exact S 12 7 1 cell_12_7_1
  | exact S 12 7 2 cell_12_7_2
  | exact S 12 7 3 cell_12_7_3
  | exact S 12 7 4 cell_12_7_4
  | exact S 12 7 5 cell_12_7_5
theorem cell_12_8_0 : C 12 8 0 := by decide +kernel
theorem cell_12_8_1 : C 12 8 1 := by decide +kernel
theorem cell_12_8_2 : C 12 8 2 := by decide +kernel
theorem cell_12_8_3 : C 12 8 3 := by decide +kernel
theorem cell_12_8_4 : C 12 8 4 := by decide +kernel
theorem cell_12_8_5 : C 12 8 5 := by decide +kernel
theorem row_12_8 : ThresholdAt 12 8 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 8 0 cell_12_8_0
  | exact S 12 8 1 cell_12_8_1
  | exact S 12 8 2 cell_12_8_2
  | exact S 12 8 3 cell_12_8_3
  | exact S 12 8 4 cell_12_8_4
  | exact S 12 8 5 cell_12_8_5
theorem cell_12_9_0 : C 12 9 0 := by decide +kernel
theorem cell_12_9_1 : C 12 9 1 := by decide +kernel
theorem cell_12_9_2 : C 12 9 2 := by decide +kernel
theorem cell_12_9_3 : C 12 9 3 := by decide +kernel
theorem cell_12_9_4 : C 12 9 4 := by decide +kernel
theorem cell_12_9_5 : C 12 9 5 := by decide +kernel
theorem row_12_9 : ThresholdAt 12 9 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 9 0 cell_12_9_0
  | exact S 12 9 1 cell_12_9_1
  | exact S 12 9 2 cell_12_9_2
  | exact S 12 9 3 cell_12_9_3
  | exact S 12 9 4 cell_12_9_4
  | exact S 12 9 5 cell_12_9_5
theorem cell_12_10_0 : C 12 10 0 := by decide +kernel
theorem cell_12_10_1 : C 12 10 1 := by decide +kernel
theorem cell_12_10_2 : C 12 10 2 := by decide +kernel
theorem cell_12_10_3 : C 12 10 3 := by decide +kernel
theorem cell_12_10_4 : C 12 10 4 := by decide +kernel
theorem cell_12_10_5 : C 12 10 5 := by decide +kernel
theorem row_12_10 : ThresholdAt 12 10 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 10 0 cell_12_10_0
  | exact S 12 10 1 cell_12_10_1
  | exact S 12 10 2 cell_12_10_2
  | exact S 12 10 3 cell_12_10_3
  | exact S 12 10 4 cell_12_10_4
  | exact S 12 10 5 cell_12_10_5
theorem cell_12_11_0 : C 12 11 0 := by decide +kernel
theorem cell_12_11_1 : C 12 11 1 := by decide +kernel
theorem cell_12_11_2 : C 12 11 2 := by decide +kernel
theorem cell_12_11_3 : C 12 11 3 := by decide +kernel
theorem cell_12_11_4 : C 12 11 4 := by decide +kernel
theorem cell_12_11_5 : C 12 11 5 := by decide +kernel
theorem row_12_11 : ThresholdAt 12 11 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 11 0 cell_12_11_0
  | exact S 12 11 1 cell_12_11_1
  | exact S 12 11 2 cell_12_11_2
  | exact S 12 11 3 cell_12_11_3
  | exact S 12 11 4 cell_12_11_4
  | exact S 12 11 5 cell_12_11_5
theorem cell_12_12_0 : C 12 12 0 := by decide +kernel
theorem cell_12_12_1 : C 12 12 1 := by decide +kernel
theorem cell_12_12_2 : C 12 12 2 := by decide +kernel
theorem cell_12_12_3 : C 12 12 3 := by decide +kernel
theorem cell_12_12_4 : C 12 12 4 := by decide +kernel
theorem cell_12_12_5 : C 12 12 5 := by decide +kernel
theorem row_12_12 : ThresholdAt 12 12 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 12 0 cell_12_12_0
  | exact S 12 12 1 cell_12_12_1
  | exact S 12 12 2 cell_12_12_2
  | exact S 12 12 3 cell_12_12_3
  | exact S 12 12 4 cell_12_12_4
  | exact S 12 12 5 cell_12_12_5
theorem cell_12_13_0 : C 12 13 0 := by decide +kernel
theorem cell_12_13_1 : C 12 13 1 := by decide +kernel
theorem cell_12_13_2 : C 12 13 2 := by decide +kernel
theorem cell_12_13_3 : C 12 13 3 := by decide +kernel
theorem cell_12_13_4 : C 12 13 4 := by decide +kernel
theorem cell_12_13_5 : C 12 13 5 := by decide +kernel
theorem row_12_13 : ThresholdAt 12 13 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 13 0 cell_12_13_0
  | exact S 12 13 1 cell_12_13_1
  | exact S 12 13 2 cell_12_13_2
  | exact S 12 13 3 cell_12_13_3
  | exact S 12 13 4 cell_12_13_4
  | exact S 12 13 5 cell_12_13_5
theorem cell_12_14_0 : C 12 14 0 := by decide +kernel
theorem cell_12_14_1 : C 12 14 1 := by decide +kernel
theorem cell_12_14_2 : C 12 14 2 := by decide +kernel
theorem cell_12_14_3 : C 12 14 3 := by decide +kernel
theorem cell_12_14_4 : C 12 14 4 := by decide +kernel
theorem cell_12_14_5 : C 12 14 5 := by decide +kernel
theorem row_12_14 : ThresholdAt 12 14 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 14 0 cell_12_14_0
  | exact S 12 14 1 cell_12_14_1
  | exact S 12 14 2 cell_12_14_2
  | exact S 12 14 3 cell_12_14_3
  | exact S 12 14 4 cell_12_14_4
  | exact S 12 14 5 cell_12_14_5
theorem cell_12_15_0 : C 12 15 0 := by decide +kernel
theorem cell_12_15_1 : C 12 15 1 := by decide +kernel
theorem cell_12_15_2 : C 12 15 2 := by decide +kernel
theorem cell_12_15_3 : C 12 15 3 := by decide +kernel
theorem cell_12_15_4 : C 12 15 4 := by decide +kernel
theorem cell_12_15_5 : C 12 15 5 := by decide +kernel
theorem row_12_15 : ThresholdAt 12 15 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 15 0 cell_12_15_0
  | exact S 12 15 1 cell_12_15_1
  | exact S 12 15 2 cell_12_15_2
  | exact S 12 15 3 cell_12_15_3
  | exact S 12 15 4 cell_12_15_4
  | exact S 12 15 5 cell_12_15_5
theorem cell_12_16_0 : C 12 16 0 := by decide +kernel
theorem cell_12_16_1 : C 12 16 1 := by decide +kernel
theorem cell_12_16_2 : C 12 16 2 := by decide +kernel
theorem cell_12_16_3 : C 12 16 3 := by decide +kernel
theorem cell_12_16_4 : C 12 16 4 := by decide +kernel
theorem cell_12_16_5 : C 12 16 5 := by decide +kernel
theorem row_12_16 : ThresholdAt 12 16 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 16 0 cell_12_16_0
  | exact S 12 16 1 cell_12_16_1
  | exact S 12 16 2 cell_12_16_2
  | exact S 12 16 3 cell_12_16_3
  | exact S 12 16 4 cell_12_16_4
  | exact S 12 16 5 cell_12_16_5
theorem cell_12_17_0 : C 12 17 0 := by decide +kernel
theorem cell_12_17_1 : C 12 17 1 := by decide +kernel
theorem cell_12_17_2 : C 12 17 2 := by decide +kernel
theorem cell_12_17_3 : C 12 17 3 := by decide +kernel
theorem cell_12_17_4 : C 12 17 4 := by decide +kernel
theorem cell_12_17_5 : C 12 17 5 := by decide +kernel
theorem row_12_17 : ThresholdAt 12 17 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 17 0 cell_12_17_0
  | exact S 12 17 1 cell_12_17_1
  | exact S 12 17 2 cell_12_17_2
  | exact S 12 17 3 cell_12_17_3
  | exact S 12 17 4 cell_12_17_4
  | exact S 12 17 5 cell_12_17_5
theorem cell_12_18_0 : C 12 18 0 := by decide +kernel
theorem cell_12_18_1 : C 12 18 1 := by decide +kernel
theorem cell_12_18_2 : C 12 18 2 := by decide +kernel
theorem cell_12_18_3 : C 12 18 3 := by decide +kernel
theorem cell_12_18_4 : C 12 18 4 := by decide +kernel
theorem cell_12_18_5 : C 12 18 5 := by decide +kernel
theorem row_12_18 : ThresholdAt 12 18 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 18 0 cell_12_18_0
  | exact S 12 18 1 cell_12_18_1
  | exact S 12 18 2 cell_12_18_2
  | exact S 12 18 3 cell_12_18_3
  | exact S 12 18 4 cell_12_18_4
  | exact S 12 18 5 cell_12_18_5
theorem cell_12_19_0 : C 12 19 0 := by decide +kernel
theorem cell_12_19_1 : C 12 19 1 := by decide +kernel
theorem cell_12_19_2 : C 12 19 2 := by decide +kernel
theorem cell_12_19_3 : C 12 19 3 := by decide +kernel
theorem cell_12_19_4 : C 12 19 4 := by decide +kernel
theorem cell_12_19_5 : C 12 19 5 := by decide +kernel
theorem row_12_19 : ThresholdAt 12 19 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 19 0 cell_12_19_0
  | exact S 12 19 1 cell_12_19_1
  | exact S 12 19 2 cell_12_19_2
  | exact S 12 19 3 cell_12_19_3
  | exact S 12 19 4 cell_12_19_4
  | exact S 12 19 5 cell_12_19_5
theorem cell_12_20_0 : C 12 20 0 := by decide +kernel
theorem cell_12_20_1 : C 12 20 1 := by decide +kernel
theorem cell_12_20_2 : C 12 20 2 := by decide +kernel
theorem cell_12_20_3 : C 12 20 3 := by decide +kernel
theorem cell_12_20_4 : C 12 20 4 := by decide +kernel
theorem cell_12_20_5 : C 12 20 5 := by decide +kernel
theorem row_12_20 : ThresholdAt 12 20 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 20 0 cell_12_20_0
  | exact S 12 20 1 cell_12_20_1
  | exact S 12 20 2 cell_12_20_2
  | exact S 12 20 3 cell_12_20_3
  | exact S 12 20 4 cell_12_20_4
  | exact S 12 20 5 cell_12_20_5
theorem cell_12_21_0 : C 12 21 0 := by decide +kernel
theorem cell_12_21_1 : C 12 21 1 := by decide +kernel
theorem cell_12_21_2 : C 12 21 2 := by decide +kernel
theorem cell_12_21_3 : C 12 21 3 := by decide +kernel
theorem cell_12_21_4 : C 12 21 4 := by decide +kernel
theorem cell_12_21_5 : C 12 21 5 := by decide +kernel
theorem row_12_21 : ThresholdAt 12 21 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 21 0 cell_12_21_0
  | exact S 12 21 1 cell_12_21_1
  | exact S 12 21 2 cell_12_21_2
  | exact S 12 21 3 cell_12_21_3
  | exact S 12 21 4 cell_12_21_4
  | exact S 12 21 5 cell_12_21_5
theorem cell_12_22_0 : C 12 22 0 := by decide +kernel
theorem cell_12_22_1 : C 12 22 1 := by decide +kernel
theorem cell_12_22_2 : C 12 22 2 := by decide +kernel
theorem cell_12_22_3 : C 12 22 3 := by decide +kernel
theorem cell_12_22_4 : C 12 22 4 := by decide +kernel
theorem cell_12_22_5 : C 12 22 5 := by decide +kernel
theorem row_12_22 : ThresholdAt 12 22 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 22 0 cell_12_22_0
  | exact S 12 22 1 cell_12_22_1
  | exact S 12 22 2 cell_12_22_2
  | exact S 12 22 3 cell_12_22_3
  | exact S 12 22 4 cell_12_22_4
  | exact S 12 22 5 cell_12_22_5
theorem cell_12_23_0 : C 12 23 0 := by decide +kernel
theorem cell_12_23_1 : C 12 23 1 := by decide +kernel
theorem cell_12_23_2 : C 12 23 2 := by decide +kernel
theorem cell_12_23_3 : C 12 23 3 := by decide +kernel
theorem cell_12_23_4 : C 12 23 4 := by decide +kernel
theorem cell_12_23_5 : C 12 23 5 := by decide +kernel
theorem row_12_23 : ThresholdAt 12 23 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 23 0 cell_12_23_0
  | exact S 12 23 1 cell_12_23_1
  | exact S 12 23 2 cell_12_23_2
  | exact S 12 23 3 cell_12_23_3
  | exact S 12 23 4 cell_12_23_4
  | exact S 12 23 5 cell_12_23_5
theorem cell_12_24_0 : C 12 24 0 := by decide +kernel
theorem cell_12_24_1 : C 12 24 1 := by decide +kernel
theorem cell_12_24_2 : C 12 24 2 := by decide +kernel
theorem cell_12_24_3 : C 12 24 3 := by decide +kernel
theorem cell_12_24_4 : C 12 24 4 := by decide +kernel
theorem cell_12_24_5 : C 12 24 5 := by decide +kernel
theorem row_12_24 : ThresholdAt 12 24 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 24 0 cell_12_24_0
  | exact S 12 24 1 cell_12_24_1
  | exact S 12 24 2 cell_12_24_2
  | exact S 12 24 3 cell_12_24_3
  | exact S 12 24 4 cell_12_24_4
  | exact S 12 24 5 cell_12_24_5
theorem cell_12_25_0 : C 12 25 0 := by decide +kernel
theorem cell_12_25_1 : C 12 25 1 := by decide +kernel
theorem cell_12_25_2 : C 12 25 2 := by decide +kernel
theorem cell_12_25_3 : C 12 25 3 := by decide +kernel
theorem cell_12_25_4 : C 12 25 4 := by decide +kernel
theorem cell_12_25_5 : C 12 25 5 := by decide +kernel
theorem row_12_25 : ThresholdAt 12 25 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 25 0 cell_12_25_0
  | exact S 12 25 1 cell_12_25_1
  | exact S 12 25 2 cell_12_25_2
  | exact S 12 25 3 cell_12_25_3
  | exact S 12 25 4 cell_12_25_4
  | exact S 12 25 5 cell_12_25_5
theorem cell_12_26_0 : C 12 26 0 := by decide +kernel
theorem cell_12_26_1 : C 12 26 1 := by decide +kernel
theorem cell_12_26_2 : C 12 26 2 := by decide +kernel
theorem cell_12_26_3 : C 12 26 3 := by decide +kernel
theorem cell_12_26_4 : C 12 26 4 := by decide +kernel
theorem cell_12_26_5 : C 12 26 5 := by decide +kernel
theorem row_12_26 : ThresholdAt 12 26 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 26 0 cell_12_26_0
  | exact S 12 26 1 cell_12_26_1
  | exact S 12 26 2 cell_12_26_2
  | exact S 12 26 3 cell_12_26_3
  | exact S 12 26 4 cell_12_26_4
  | exact S 12 26 5 cell_12_26_5
theorem cell_12_27_0 : C 12 27 0 := by decide +kernel
theorem cell_12_27_1 : C 12 27 1 := by decide +kernel
theorem cell_12_27_2 : C 12 27 2 := by decide +kernel
theorem cell_12_27_3 : C 12 27 3 := by decide +kernel
theorem cell_12_27_4 : C 12 27 4 := by decide +kernel
theorem cell_12_27_5 : C 12 27 5 := by decide +kernel
theorem row_12_27 : ThresholdAt 12 27 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 27 0 cell_12_27_0
  | exact S 12 27 1 cell_12_27_1
  | exact S 12 27 2 cell_12_27_2
  | exact S 12 27 3 cell_12_27_3
  | exact S 12 27 4 cell_12_27_4
  | exact S 12 27 5 cell_12_27_5
theorem cell_12_28_0 : C 12 28 0 := by decide +kernel
theorem cell_12_28_1 : C 12 28 1 := by decide +kernel
theorem cell_12_28_2 : C 12 28 2 := by decide +kernel
theorem cell_12_28_3 : C 12 28 3 := by decide +kernel
theorem cell_12_28_4 : C 12 28 4 := by decide +kernel
theorem cell_12_28_5 : C 12 28 5 := by decide +kernel
theorem row_12_28 : ThresholdAt 12 28 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 28 0 cell_12_28_0
  | exact S 12 28 1 cell_12_28_1
  | exact S 12 28 2 cell_12_28_2
  | exact S 12 28 3 cell_12_28_3
  | exact S 12 28 4 cell_12_28_4
  | exact S 12 28 5 cell_12_28_5
theorem cell_12_29_0 : C 12 29 0 := by decide +kernel
theorem cell_12_29_1 : C 12 29 1 := by decide +kernel
theorem cell_12_29_2 : C 12 29 2 := by decide +kernel
theorem cell_12_29_3 : C 12 29 3 := by decide +kernel
theorem cell_12_29_4 : C 12 29 4 := by decide +kernel
theorem cell_12_29_5 : C 12 29 5 := by decide +kernel
theorem row_12_29 : ThresholdAt 12 29 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 29 0 cell_12_29_0
  | exact S 12 29 1 cell_12_29_1
  | exact S 12 29 2 cell_12_29_2
  | exact S 12 29 3 cell_12_29_3
  | exact S 12 29 4 cell_12_29_4
  | exact S 12 29 5 cell_12_29_5
theorem cell_12_30_0 : C 12 30 0 := by decide +kernel
theorem cell_12_30_1 : C 12 30 1 := by decide +kernel
theorem cell_12_30_2 : C 12 30 2 := by decide +kernel
theorem cell_12_30_3 : C 12 30 3 := by decide +kernel
theorem cell_12_30_4 : C 12 30 4 := by decide +kernel
theorem cell_12_30_5 : C 12 30 5 := by decide +kernel
theorem row_12_30 : ThresholdAt 12 30 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 30 0 cell_12_30_0
  | exact S 12 30 1 cell_12_30_1
  | exact S 12 30 2 cell_12_30_2
  | exact S 12 30 3 cell_12_30_3
  | exact S 12 30 4 cell_12_30_4
  | exact S 12 30 5 cell_12_30_5
theorem cell_12_31_0 : C 12 31 0 := by decide +kernel
theorem cell_12_31_1 : C 12 31 1 := by decide +kernel
theorem cell_12_31_2 : C 12 31 2 := by decide +kernel
theorem cell_12_31_3 : C 12 31 3 := by decide +kernel
theorem cell_12_31_4 : C 12 31 4 := by decide +kernel
theorem cell_12_31_5 : C 12 31 5 := by decide +kernel
theorem row_12_31 : ThresholdAt 12 31 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 31 0 cell_12_31_0
  | exact S 12 31 1 cell_12_31_1
  | exact S 12 31 2 cell_12_31_2
  | exact S 12 31 3 cell_12_31_3
  | exact S 12 31 4 cell_12_31_4
  | exact S 12 31 5 cell_12_31_5
theorem cell_12_32_0 : C 12 32 0 := by decide +kernel
theorem cell_12_32_1 : C 12 32 1 := by decide +kernel
theorem cell_12_32_2 : C 12 32 2 := by decide +kernel
theorem cell_12_32_3 : C 12 32 3 := by decide +kernel
theorem cell_12_32_4 : C 12 32 4 := by decide +kernel
theorem cell_12_32_5 : C 12 32 5 := by decide +kernel
theorem row_12_32 : ThresholdAt 12 32 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 32 0 cell_12_32_0
  | exact S 12 32 1 cell_12_32_1
  | exact S 12 32 2 cell_12_32_2
  | exact S 12 32 3 cell_12_32_3
  | exact S 12 32 4 cell_12_32_4
  | exact S 12 32 5 cell_12_32_5
theorem cell_12_33_0 : C 12 33 0 := by decide +kernel
theorem cell_12_33_1 : C 12 33 1 := by decide +kernel
theorem cell_12_33_2 : C 12 33 2 := by decide +kernel
theorem cell_12_33_3 : C 12 33 3 := by decide +kernel
theorem cell_12_33_4 : C 12 33 4 := by decide +kernel
theorem cell_12_33_5 : C 12 33 5 := by decide +kernel
theorem row_12_33 : ThresholdAt 12 33 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 33 0 cell_12_33_0
  | exact S 12 33 1 cell_12_33_1
  | exact S 12 33 2 cell_12_33_2
  | exact S 12 33 3 cell_12_33_3
  | exact S 12 33 4 cell_12_33_4
  | exact S 12 33 5 cell_12_33_5
theorem cell_12_34_0 : C 12 34 0 := by decide +kernel
theorem cell_12_34_1 : C 12 34 1 := by decide +kernel
theorem cell_12_34_2 : C 12 34 2 := by decide +kernel
theorem cell_12_34_3 : C 12 34 3 := by decide +kernel
theorem cell_12_34_4 : C 12 34 4 := by decide +kernel
theorem cell_12_34_5 : C 12 34 5 := by decide +kernel
theorem row_12_34 : ThresholdAt 12 34 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 34 0 cell_12_34_0
  | exact S 12 34 1 cell_12_34_1
  | exact S 12 34 2 cell_12_34_2
  | exact S 12 34 3 cell_12_34_3
  | exact S 12 34 4 cell_12_34_4
  | exact S 12 34 5 cell_12_34_5
theorem cell_12_35_0 : C 12 35 0 := by decide +kernel
theorem cell_12_35_1 : C 12 35 1 := by decide +kernel
theorem cell_12_35_2 : C 12 35 2 := by decide +kernel
theorem cell_12_35_3 : C 12 35 3 := by decide +kernel
theorem cell_12_35_4 : C 12 35 4 := by decide +kernel
theorem cell_12_35_5 : C 12 35 5 := by decide +kernel
theorem row_12_35 : ThresholdAt 12 35 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 35 0 cell_12_35_0
  | exact S 12 35 1 cell_12_35_1
  | exact S 12 35 2 cell_12_35_2
  | exact S 12 35 3 cell_12_35_3
  | exact S 12 35 4 cell_12_35_4
  | exact S 12 35 5 cell_12_35_5
theorem cell_12_36_0 : C 12 36 0 := by decide +kernel
theorem cell_12_36_1 : C 12 36 1 := by decide +kernel
theorem cell_12_36_2 : C 12 36 2 := by decide +kernel
theorem cell_12_36_3 : C 12 36 3 := by decide +kernel
theorem cell_12_36_4 : C 12 36 4 := by decide +kernel
theorem cell_12_36_5 : C 12 36 5 := by decide +kernel
theorem row_12_36 : ThresholdAt 12 36 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 36 0 cell_12_36_0
  | exact S 12 36 1 cell_12_36_1
  | exact S 12 36 2 cell_12_36_2
  | exact S 12 36 3 cell_12_36_3
  | exact S 12 36 4 cell_12_36_4
  | exact S 12 36 5 cell_12_36_5
theorem cell_12_37_0 : C 12 37 0 := by decide +kernel
theorem cell_12_37_1 : C 12 37 1 := by decide +kernel
theorem cell_12_37_2 : C 12 37 2 := by decide +kernel
theorem cell_12_37_3 : C 12 37 3 := by decide +kernel
theorem cell_12_37_4 : C 12 37 4 := by decide +kernel
theorem cell_12_37_5 : C 12 37 5 := by decide +kernel
theorem row_12_37 : ThresholdAt 12 37 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 37 0 cell_12_37_0
  | exact S 12 37 1 cell_12_37_1
  | exact S 12 37 2 cell_12_37_2
  | exact S 12 37 3 cell_12_37_3
  | exact S 12 37 4 cell_12_37_4
  | exact S 12 37 5 cell_12_37_5
theorem cell_12_38_0 : C 12 38 0 := by decide +kernel
theorem cell_12_38_1 : C 12 38 1 := by decide +kernel
theorem cell_12_38_2 : C 12 38 2 := by decide +kernel
theorem cell_12_38_3 : C 12 38 3 := by decide +kernel
theorem cell_12_38_4 : C 12 38 4 := by decide +kernel
theorem cell_12_38_5 : C 12 38 5 := by decide +kernel
theorem row_12_38 : ThresholdAt 12 38 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 38 0 cell_12_38_0
  | exact S 12 38 1 cell_12_38_1
  | exact S 12 38 2 cell_12_38_2
  | exact S 12 38 3 cell_12_38_3
  | exact S 12 38 4 cell_12_38_4
  | exact S 12 38 5 cell_12_38_5
theorem cell_12_39_0 : C 12 39 0 := by decide +kernel
theorem cell_12_39_1 : C 12 39 1 := by decide +kernel
theorem cell_12_39_2 : C 12 39 2 := by decide +kernel
theorem cell_12_39_3 : C 12 39 3 := by decide +kernel
theorem cell_12_39_4 : C 12 39 4 := by decide +kernel
theorem cell_12_39_5 : C 12 39 5 := by decide +kernel
theorem row_12_39 : ThresholdAt 12 39 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 39 0 cell_12_39_0
  | exact S 12 39 1 cell_12_39_1
  | exact S 12 39 2 cell_12_39_2
  | exact S 12 39 3 cell_12_39_3
  | exact S 12 39 4 cell_12_39_4
  | exact S 12 39 5 cell_12_39_5
theorem cell_12_40_0 : C 12 40 0 := by decide +kernel
theorem cell_12_40_1 : C 12 40 1 := by decide +kernel
theorem cell_12_40_2 : C 12 40 2 := by decide +kernel
theorem cell_12_40_3 : C 12 40 3 := by decide +kernel
theorem cell_12_40_4 : C 12 40 4 := by decide +kernel
theorem cell_12_40_5 : C 12 40 5 := by decide +kernel
theorem row_12_40 : ThresholdAt 12 40 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 40 0 cell_12_40_0
  | exact S 12 40 1 cell_12_40_1
  | exact S 12 40 2 cell_12_40_2
  | exact S 12 40 3 cell_12_40_3
  | exact S 12 40 4 cell_12_40_4
  | exact S 12 40 5 cell_12_40_5
theorem cell_12_41_0 : C 12 41 0 := by decide +kernel
theorem cell_12_41_1 : C 12 41 1 := by decide +kernel
theorem cell_12_41_2 : C 12 41 2 := by decide +kernel
theorem cell_12_41_3 : C 12 41 3 := by decide +kernel
theorem cell_12_41_4 : C 12 41 4 := by decide +kernel
theorem cell_12_41_5 : C 12 41 5 := by decide +kernel
theorem row_12_41 : ThresholdAt 12 41 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 41 0 cell_12_41_0
  | exact S 12 41 1 cell_12_41_1
  | exact S 12 41 2 cell_12_41_2
  | exact S 12 41 3 cell_12_41_3
  | exact S 12 41 4 cell_12_41_4
  | exact S 12 41 5 cell_12_41_5
theorem cell_12_42_0 : C 12 42 0 := by decide +kernel
theorem cell_12_42_1 : C 12 42 1 := by decide +kernel
theorem cell_12_42_2 : C 12 42 2 := by decide +kernel
theorem cell_12_42_3 : C 12 42 3 := by decide +kernel
theorem cell_12_42_4 : C 12 42 4 := by decide +kernel
theorem cell_12_42_5 : C 12 42 5 := by decide +kernel
theorem row_12_42 : ThresholdAt 12 42 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 42 0 cell_12_42_0
  | exact S 12 42 1 cell_12_42_1
  | exact S 12 42 2 cell_12_42_2
  | exact S 12 42 3 cell_12_42_3
  | exact S 12 42 4 cell_12_42_4
  | exact S 12 42 5 cell_12_42_5
theorem cell_12_43_0 : C 12 43 0 := by decide +kernel
theorem cell_12_43_1 : C 12 43 1 := by decide +kernel
theorem cell_12_43_2 : C 12 43 2 := by decide +kernel
theorem cell_12_43_3 : C 12 43 3 := by decide +kernel
theorem cell_12_43_4 : C 12 43 4 := by decide +kernel
theorem cell_12_43_5 : C 12 43 5 := by decide +kernel
theorem row_12_43 : ThresholdAt 12 43 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 43 0 cell_12_43_0
  | exact S 12 43 1 cell_12_43_1
  | exact S 12 43 2 cell_12_43_2
  | exact S 12 43 3 cell_12_43_3
  | exact S 12 43 4 cell_12_43_4
  | exact S 12 43 5 cell_12_43_5
theorem cell_12_44_0 : C 12 44 0 := by decide +kernel
theorem cell_12_44_1 : C 12 44 1 := by decide +kernel
theorem cell_12_44_2 : C 12 44 2 := by decide +kernel
theorem cell_12_44_3 : C 12 44 3 := by decide +kernel
theorem cell_12_44_4 : C 12 44 4 := by decide +kernel
theorem cell_12_44_5 : C 12 44 5 := by decide +kernel
theorem row_12_44 : ThresholdAt 12 44 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 44 0 cell_12_44_0
  | exact S 12 44 1 cell_12_44_1
  | exact S 12 44 2 cell_12_44_2
  | exact S 12 44 3 cell_12_44_3
  | exact S 12 44 4 cell_12_44_4
  | exact S 12 44 5 cell_12_44_5
theorem cell_12_45_0 : C 12 45 0 := by decide +kernel
theorem cell_12_45_1 : C 12 45 1 := by decide +kernel
theorem cell_12_45_2 : C 12 45 2 := by decide +kernel
theorem cell_12_45_3 : C 12 45 3 := by decide +kernel
theorem cell_12_45_4 : C 12 45 4 := by decide +kernel
theorem cell_12_45_5 : C 12 45 5 := by decide +kernel
theorem row_12_45 : ThresholdAt 12 45 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 45 0 cell_12_45_0
  | exact S 12 45 1 cell_12_45_1
  | exact S 12 45 2 cell_12_45_2
  | exact S 12 45 3 cell_12_45_3
  | exact S 12 45 4 cell_12_45_4
  | exact S 12 45 5 cell_12_45_5
theorem cell_12_46_0 : C 12 46 0 := by decide +kernel
theorem cell_12_46_1 : C 12 46 1 := by decide +kernel
theorem cell_12_46_2 : C 12 46 2 := by decide +kernel
theorem cell_12_46_3 : C 12 46 3 := by decide +kernel
theorem cell_12_46_4 : C 12 46 4 := by decide +kernel
theorem cell_12_46_5 : C 12 46 5 := by decide +kernel
theorem row_12_46 : ThresholdAt 12 46 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 46 0 cell_12_46_0
  | exact S 12 46 1 cell_12_46_1
  | exact S 12 46 2 cell_12_46_2
  | exact S 12 46 3 cell_12_46_3
  | exact S 12 46 4 cell_12_46_4
  | exact S 12 46 5 cell_12_46_5
theorem cell_12_47_0 : C 12 47 0 := by decide +kernel
theorem cell_12_47_1 : C 12 47 1 := by decide +kernel
theorem cell_12_47_2 : C 12 47 2 := by decide +kernel
theorem cell_12_47_3 : C 12 47 3 := by decide +kernel
theorem cell_12_47_4 : C 12 47 4 := by decide +kernel
theorem cell_12_47_5 : C 12 47 5 := by decide +kernel
theorem row_12_47 : ThresholdAt 12 47 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 47 0 cell_12_47_0
  | exact S 12 47 1 cell_12_47_1
  | exact S 12 47 2 cell_12_47_2
  | exact S 12 47 3 cell_12_47_3
  | exact S 12 47 4 cell_12_47_4
  | exact S 12 47 5 cell_12_47_5
theorem cell_12_48_0 : C 12 48 0 := by decide +kernel
theorem cell_12_48_1 : C 12 48 1 := by decide +kernel
theorem cell_12_48_2 : C 12 48 2 := by decide +kernel
theorem cell_12_48_3 : C 12 48 3 := by decide +kernel
theorem cell_12_48_4 : C 12 48 4 := by decide +kernel
theorem cell_12_48_5 : C 12 48 5 := by decide +kernel
theorem row_12_48 : ThresholdAt 12 48 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 48 0 cell_12_48_0
  | exact S 12 48 1 cell_12_48_1
  | exact S 12 48 2 cell_12_48_2
  | exact S 12 48 3 cell_12_48_3
  | exact S 12 48 4 cell_12_48_4
  | exact S 12 48 5 cell_12_48_5
theorem cell_12_49_0 : C 12 49 0 := by decide +kernel
theorem cell_12_49_1 : C 12 49 1 := by decide +kernel
theorem cell_12_49_2 : C 12 49 2 := by decide +kernel
theorem cell_12_49_3 : C 12 49 3 := by decide +kernel
theorem cell_12_49_4 : C 12 49 4 := by decide +kernel
theorem cell_12_49_5 : C 12 49 5 := by decide +kernel
theorem row_12_49 : ThresholdAt 12 49 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 49 0 cell_12_49_0
  | exact S 12 49 1 cell_12_49_1
  | exact S 12 49 2 cell_12_49_2
  | exact S 12 49 3 cell_12_49_3
  | exact S 12 49 4 cell_12_49_4
  | exact S 12 49 5 cell_12_49_5
theorem cell_12_50_0 : C 12 50 0 := by decide +kernel
theorem cell_12_50_1 : C 12 50 1 := by decide +kernel
theorem cell_12_50_2 : C 12 50 2 := by decide +kernel
theorem cell_12_50_3 : C 12 50 3 := by decide +kernel
theorem cell_12_50_4 : C 12 50 4 := by decide +kernel
theorem cell_12_50_5 : C 12 50 5 := by decide +kernel
theorem row_12_50 : ThresholdAt 12 50 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 50 0 cell_12_50_0
  | exact S 12 50 1 cell_12_50_1
  | exact S 12 50 2 cell_12_50_2
  | exact S 12 50 3 cell_12_50_3
  | exact S 12 50 4 cell_12_50_4
  | exact S 12 50 5 cell_12_50_5
theorem cell_12_51_0 : C 12 51 0 := by decide +kernel
theorem cell_12_51_1 : C 12 51 1 := by decide +kernel
theorem cell_12_51_2 : C 12 51 2 := by decide +kernel
theorem cell_12_51_3 : C 12 51 3 := by decide +kernel
theorem cell_12_51_4 : C 12 51 4 := by decide +kernel
theorem cell_12_51_5 : C 12 51 5 := by decide +kernel
theorem row_12_51 : ThresholdAt 12 51 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 51 0 cell_12_51_0
  | exact S 12 51 1 cell_12_51_1
  | exact S 12 51 2 cell_12_51_2
  | exact S 12 51 3 cell_12_51_3
  | exact S 12 51 4 cell_12_51_4
  | exact S 12 51 5 cell_12_51_5
theorem cell_12_52_0 : C 12 52 0 := by decide +kernel
theorem cell_12_52_1 : C 12 52 1 := by decide +kernel
theorem cell_12_52_2 : C 12 52 2 := by decide +kernel
theorem cell_12_52_3 : C 12 52 3 := by decide +kernel
theorem cell_12_52_4 : C 12 52 4 := by decide +kernel
theorem cell_12_52_5 : C 12 52 5 := by decide +kernel
theorem row_12_52 : ThresholdAt 12 52 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 52 0 cell_12_52_0
  | exact S 12 52 1 cell_12_52_1
  | exact S 12 52 2 cell_12_52_2
  | exact S 12 52 3 cell_12_52_3
  | exact S 12 52 4 cell_12_52_4
  | exact S 12 52 5 cell_12_52_5
theorem cell_12_53_0 : C 12 53 0 := by decide +kernel
theorem cell_12_53_1 : C 12 53 1 := by decide +kernel
theorem cell_12_53_2 : C 12 53 2 := by decide +kernel
theorem cell_12_53_3 : C 12 53 3 := by decide +kernel
theorem cell_12_53_4 : C 12 53 4 := by decide +kernel
theorem cell_12_53_5 : C 12 53 5 := by decide +kernel
theorem row_12_53 : ThresholdAt 12 53 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 53 0 cell_12_53_0
  | exact S 12 53 1 cell_12_53_1
  | exact S 12 53 2 cell_12_53_2
  | exact S 12 53 3 cell_12_53_3
  | exact S 12 53 4 cell_12_53_4
  | exact S 12 53 5 cell_12_53_5
theorem cell_12_54_0 : C 12 54 0 := by decide +kernel
theorem cell_12_54_1 : C 12 54 1 := by decide +kernel
theorem cell_12_54_2 : C 12 54 2 := by decide +kernel
theorem cell_12_54_3 : C 12 54 3 := by decide +kernel
theorem cell_12_54_4 : C 12 54 4 := by decide +kernel
theorem cell_12_54_5 : C 12 54 5 := by decide +kernel
theorem row_12_54 : ThresholdAt 12 54 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 54 0 cell_12_54_0
  | exact S 12 54 1 cell_12_54_1
  | exact S 12 54 2 cell_12_54_2
  | exact S 12 54 3 cell_12_54_3
  | exact S 12 54 4 cell_12_54_4
  | exact S 12 54 5 cell_12_54_5
theorem cell_12_55_0 : C 12 55 0 := by decide +kernel
theorem cell_12_55_1 : C 12 55 1 := by decide +kernel
theorem cell_12_55_2 : C 12 55 2 := by decide +kernel
theorem cell_12_55_3 : C 12 55 3 := by decide +kernel
theorem cell_12_55_4 : C 12 55 4 := by decide +kernel
theorem cell_12_55_5 : C 12 55 5 := by decide +kernel
theorem row_12_55 : ThresholdAt 12 55 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 55 0 cell_12_55_0
  | exact S 12 55 1 cell_12_55_1
  | exact S 12 55 2 cell_12_55_2
  | exact S 12 55 3 cell_12_55_3
  | exact S 12 55 4 cell_12_55_4
  | exact S 12 55 5 cell_12_55_5
theorem cell_12_56_0 : C 12 56 0 := by decide +kernel
theorem cell_12_56_1 : C 12 56 1 := by decide +kernel
theorem cell_12_56_2 : C 12 56 2 := by decide +kernel
theorem cell_12_56_3 : C 12 56 3 := by decide +kernel
theorem cell_12_56_4 : C 12 56 4 := by decide +kernel
theorem cell_12_56_5 : C 12 56 5 := by decide +kernel
theorem row_12_56 : ThresholdAt 12 56 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 56 0 cell_12_56_0
  | exact S 12 56 1 cell_12_56_1
  | exact S 12 56 2 cell_12_56_2
  | exact S 12 56 3 cell_12_56_3
  | exact S 12 56 4 cell_12_56_4
  | exact S 12 56 5 cell_12_56_5
theorem cell_12_57_0 : C 12 57 0 := by decide +kernel
theorem cell_12_57_1 : C 12 57 1 := by decide +kernel
theorem cell_12_57_2 : C 12 57 2 := by decide +kernel
theorem cell_12_57_3 : C 12 57 3 := by decide +kernel
theorem cell_12_57_4 : C 12 57 4 := by decide +kernel
theorem cell_12_57_5 : C 12 57 5 := by decide +kernel
theorem row_12_57 : ThresholdAt 12 57 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 57 0 cell_12_57_0
  | exact S 12 57 1 cell_12_57_1
  | exact S 12 57 2 cell_12_57_2
  | exact S 12 57 3 cell_12_57_3
  | exact S 12 57 4 cell_12_57_4
  | exact S 12 57 5 cell_12_57_5
theorem cell_12_58_0 : C 12 58 0 := by decide +kernel
theorem cell_12_58_1 : C 12 58 1 := by decide +kernel
theorem cell_12_58_2 : C 12 58 2 := by decide +kernel
theorem cell_12_58_3 : C 12 58 3 := by decide +kernel
theorem cell_12_58_4 : C 12 58 4 := by decide +kernel
theorem cell_12_58_5 : C 12 58 5 := by decide +kernel
theorem row_12_58 : ThresholdAt 12 58 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 58 0 cell_12_58_0
  | exact S 12 58 1 cell_12_58_1
  | exact S 12 58 2 cell_12_58_2
  | exact S 12 58 3 cell_12_58_3
  | exact S 12 58 4 cell_12_58_4
  | exact S 12 58 5 cell_12_58_5
theorem cell_12_59_0 : C 12 59 0 := by decide +kernel
theorem cell_12_59_1 : C 12 59 1 := by decide +kernel
theorem cell_12_59_2 : C 12 59 2 := by decide +kernel
theorem cell_12_59_3 : C 12 59 3 := by decide +kernel
theorem cell_12_59_4 : C 12 59 4 := by decide +kernel
theorem cell_12_59_5 : C 12 59 5 := by decide +kernel
theorem row_12_59 : ThresholdAt 12 59 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 59 0 cell_12_59_0
  | exact S 12 59 1 cell_12_59_1
  | exact S 12 59 2 cell_12_59_2
  | exact S 12 59 3 cell_12_59_3
  | exact S 12 59 4 cell_12_59_4
  | exact S 12 59 5 cell_12_59_5
theorem cell_12_60_0 : C 12 60 0 := by decide +kernel
theorem cell_12_60_1 : C 12 60 1 := by decide +kernel
theorem cell_12_60_2 : C 12 60 2 := by decide +kernel
theorem cell_12_60_3 : C 12 60 3 := by decide +kernel
theorem cell_12_60_4 : C 12 60 4 := by decide +kernel
theorem cell_12_60_5 : C 12 60 5 := by decide +kernel
theorem row_12_60 : ThresholdAt 12 60 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 60 0 cell_12_60_0
  | exact S 12 60 1 cell_12_60_1
  | exact S 12 60 2 cell_12_60_2
  | exact S 12 60 3 cell_12_60_3
  | exact S 12 60 4 cell_12_60_4
  | exact S 12 60 5 cell_12_60_5
theorem cell_12_61_0 : C 12 61 0 := by decide +kernel
theorem cell_12_61_1 : C 12 61 1 := by decide +kernel
theorem cell_12_61_2 : C 12 61 2 := by decide +kernel
theorem cell_12_61_3 : C 12 61 3 := by decide +kernel
theorem cell_12_61_4 : C 12 61 4 := by decide +kernel
theorem cell_12_61_5 : C 12 61 5 := by decide +kernel
theorem row_12_61 : ThresholdAt 12 61 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 61 0 cell_12_61_0
  | exact S 12 61 1 cell_12_61_1
  | exact S 12 61 2 cell_12_61_2
  | exact S 12 61 3 cell_12_61_3
  | exact S 12 61 4 cell_12_61_4
  | exact S 12 61 5 cell_12_61_5
theorem cell_12_62_0 : C 12 62 0 := by decide +kernel
theorem cell_12_62_1 : C 12 62 1 := by decide +kernel
theorem cell_12_62_2 : C 12 62 2 := by decide +kernel
theorem cell_12_62_3 : C 12 62 3 := by decide +kernel
theorem cell_12_62_4 : C 12 62 4 := by decide +kernel
theorem cell_12_62_5 : C 12 62 5 := by decide +kernel
theorem row_12_62 : ThresholdAt 12 62 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 62 0 cell_12_62_0
  | exact S 12 62 1 cell_12_62_1
  | exact S 12 62 2 cell_12_62_2
  | exact S 12 62 3 cell_12_62_3
  | exact S 12 62 4 cell_12_62_4
  | exact S 12 62 5 cell_12_62_5
theorem cell_12_63_0 : C 12 63 0 := by decide +kernel
theorem cell_12_63_1 : C 12 63 1 := by decide +kernel
theorem cell_12_63_2 : C 12 63 2 := by decide +kernel
theorem cell_12_63_3 : C 12 63 3 := by decide +kernel
theorem cell_12_63_4 : C 12 63 4 := by decide +kernel
theorem cell_12_63_5 : C 12 63 5 := by decide +kernel
theorem row_12_63 : ThresholdAt 12 63 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 63 0 cell_12_63_0
  | exact S 12 63 1 cell_12_63_1
  | exact S 12 63 2 cell_12_63_2
  | exact S 12 63 3 cell_12_63_3
  | exact S 12 63 4 cell_12_63_4
  | exact S 12 63 5 cell_12_63_5
theorem cell_12_64_0 : C 12 64 0 := by decide +kernel
theorem cell_12_64_1 : C 12 64 1 := by decide +kernel
theorem cell_12_64_2 : C 12 64 2 := by decide +kernel
theorem cell_12_64_3 : C 12 64 3 := by decide +kernel
theorem cell_12_64_4 : C 12 64 4 := by decide +kernel
theorem cell_12_64_5 : C 12 64 5 := by decide +kernel
theorem row_12_64 : ThresholdAt 12 64 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 64 0 cell_12_64_0
  | exact S 12 64 1 cell_12_64_1
  | exact S 12 64 2 cell_12_64_2
  | exact S 12 64 3 cell_12_64_3
  | exact S 12 64 4 cell_12_64_4
  | exact S 12 64 5 cell_12_64_5
theorem cell_12_65_0 : C 12 65 0 := by decide +kernel
theorem cell_12_65_1 : C 12 65 1 := by decide +kernel
theorem cell_12_65_2 : C 12 65 2 := by decide +kernel
theorem cell_12_65_3 : C 12 65 3 := by decide +kernel
theorem cell_12_65_4 : C 12 65 4 := by decide +kernel
theorem cell_12_65_5 : C 12 65 5 := by decide +kernel
theorem row_12_65 : ThresholdAt 12 65 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 65 0 cell_12_65_0
  | exact S 12 65 1 cell_12_65_1
  | exact S 12 65 2 cell_12_65_2
  | exact S 12 65 3 cell_12_65_3
  | exact S 12 65 4 cell_12_65_4
  | exact S 12 65 5 cell_12_65_5
theorem cell_12_66_0 : C 12 66 0 := by decide +kernel
theorem cell_12_66_1 : C 12 66 1 := by decide +kernel
theorem cell_12_66_2 : C 12 66 2 := by decide +kernel
theorem cell_12_66_3 : C 12 66 3 := by decide +kernel
theorem cell_12_66_4 : C 12 66 4 := by decide +kernel
theorem cell_12_66_5 : C 12 66 5 := by decide +kernel
theorem row_12_66 : ThresholdAt 12 66 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 66 0 cell_12_66_0
  | exact S 12 66 1 cell_12_66_1
  | exact S 12 66 2 cell_12_66_2
  | exact S 12 66 3 cell_12_66_3
  | exact S 12 66 4 cell_12_66_4
  | exact S 12 66 5 cell_12_66_5
theorem cell_12_67_0 : C 12 67 0 := by decide +kernel
theorem cell_12_67_1 : C 12 67 1 := by decide +kernel
theorem cell_12_67_2 : C 12 67 2 := by decide +kernel
theorem cell_12_67_3 : C 12 67 3 := by decide +kernel
theorem cell_12_67_4 : C 12 67 4 := by decide +kernel
theorem cell_12_67_5 : C 12 67 5 := by decide +kernel
theorem row_12_67 : ThresholdAt 12 67 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 67 0 cell_12_67_0
  | exact S 12 67 1 cell_12_67_1
  | exact S 12 67 2 cell_12_67_2
  | exact S 12 67 3 cell_12_67_3
  | exact S 12 67 4 cell_12_67_4
  | exact S 12 67 5 cell_12_67_5
theorem cell_12_68_0 : C 12 68 0 := by decide +kernel
theorem cell_12_68_1 : C 12 68 1 := by decide +kernel
theorem cell_12_68_2 : C 12 68 2 := by decide +kernel
theorem cell_12_68_3 : C 12 68 3 := by decide +kernel
theorem cell_12_68_4 : C 12 68 4 := by decide +kernel
theorem cell_12_68_5 : C 12 68 5 := by decide +kernel
theorem row_12_68 : ThresholdAt 12 68 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 68 0 cell_12_68_0
  | exact S 12 68 1 cell_12_68_1
  | exact S 12 68 2 cell_12_68_2
  | exact S 12 68 3 cell_12_68_3
  | exact S 12 68 4 cell_12_68_4
  | exact S 12 68 5 cell_12_68_5
theorem cell_12_69_0 : C 12 69 0 := by decide +kernel
theorem cell_12_69_1 : C 12 69 1 := by decide +kernel
theorem cell_12_69_2 : C 12 69 2 := by decide +kernel
theorem cell_12_69_3 : C 12 69 3 := by decide +kernel
theorem cell_12_69_4 : C 12 69 4 := by decide +kernel
theorem cell_12_69_5 : C 12 69 5 := by decide +kernel
theorem row_12_69 : ThresholdAt 12 69 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 69 0 cell_12_69_0
  | exact S 12 69 1 cell_12_69_1
  | exact S 12 69 2 cell_12_69_2
  | exact S 12 69 3 cell_12_69_3
  | exact S 12 69 4 cell_12_69_4
  | exact S 12 69 5 cell_12_69_5
theorem cell_12_70_0 : C 12 70 0 := by decide +kernel
theorem cell_12_70_1 : C 12 70 1 := by decide +kernel
theorem cell_12_70_2 : C 12 70 2 := by decide +kernel
theorem cell_12_70_3 : C 12 70 3 := by decide +kernel
theorem cell_12_70_4 : C 12 70 4 := by decide +kernel
theorem cell_12_70_5 : C 12 70 5 := by decide +kernel
theorem row_12_70 : ThresholdAt 12 70 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 70 0 cell_12_70_0
  | exact S 12 70 1 cell_12_70_1
  | exact S 12 70 2 cell_12_70_2
  | exact S 12 70 3 cell_12_70_3
  | exact S 12 70 4 cell_12_70_4
  | exact S 12 70 5 cell_12_70_5
theorem cell_12_71_0 : C 12 71 0 := by decide +kernel
theorem cell_12_71_1 : C 12 71 1 := by decide +kernel
theorem cell_12_71_2 : C 12 71 2 := by decide +kernel
theorem cell_12_71_3 : C 12 71 3 := by decide +kernel
theorem cell_12_71_4 : C 12 71 4 := by decide +kernel
theorem cell_12_71_5 : C 12 71 5 := by decide +kernel
theorem row_12_71 : ThresholdAt 12 71 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 71 0 cell_12_71_0
  | exact S 12 71 1 cell_12_71_1
  | exact S 12 71 2 cell_12_71_2
  | exact S 12 71 3 cell_12_71_3
  | exact S 12 71 4 cell_12_71_4
  | exact S 12 71 5 cell_12_71_5
theorem cell_12_72_0 : C 12 72 0 := by decide +kernel
theorem cell_12_72_1 : C 12 72 1 := by decide +kernel
theorem cell_12_72_2 : C 12 72 2 := by decide +kernel
theorem cell_12_72_3 : C 12 72 3 := by decide +kernel
theorem cell_12_72_4 : C 12 72 4 := by decide +kernel
theorem cell_12_72_5 : C 12 72 5 := by decide +kernel
theorem row_12_72 : ThresholdAt 12 72 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 72 0 cell_12_72_0
  | exact S 12 72 1 cell_12_72_1
  | exact S 12 72 2 cell_12_72_2
  | exact S 12 72 3 cell_12_72_3
  | exact S 12 72 4 cell_12_72_4
  | exact S 12 72 5 cell_12_72_5
theorem cell_12_73_0 : C 12 73 0 := by decide +kernel
theorem cell_12_73_1 : C 12 73 1 := by decide +kernel
theorem cell_12_73_2 : C 12 73 2 := by decide +kernel
theorem cell_12_73_3 : C 12 73 3 := by decide +kernel
theorem cell_12_73_4 : C 12 73 4 := by decide +kernel
theorem cell_12_73_5 : C 12 73 5 := by decide +kernel
theorem row_12_73 : ThresholdAt 12 73 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 73 0 cell_12_73_0
  | exact S 12 73 1 cell_12_73_1
  | exact S 12 73 2 cell_12_73_2
  | exact S 12 73 3 cell_12_73_3
  | exact S 12 73 4 cell_12_73_4
  | exact S 12 73 5 cell_12_73_5
theorem cell_12_74_0 : C 12 74 0 := by decide +kernel
theorem cell_12_74_1 : C 12 74 1 := by decide +kernel
theorem cell_12_74_2 : C 12 74 2 := by decide +kernel
theorem cell_12_74_3 : C 12 74 3 := by decide +kernel
theorem cell_12_74_4 : C 12 74 4 := by decide +kernel
theorem cell_12_74_5 : C 12 74 5 := by decide +kernel
theorem row_12_74 : ThresholdAt 12 74 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 74 0 cell_12_74_0
  | exact S 12 74 1 cell_12_74_1
  | exact S 12 74 2 cell_12_74_2
  | exact S 12 74 3 cell_12_74_3
  | exact S 12 74 4 cell_12_74_4
  | exact S 12 74 5 cell_12_74_5
theorem cell_12_75_0 : C 12 75 0 := by decide +kernel
theorem cell_12_75_1 : C 12 75 1 := by decide +kernel
theorem cell_12_75_2 : C 12 75 2 := by decide +kernel
theorem cell_12_75_3 : C 12 75 3 := by decide +kernel
theorem cell_12_75_4 : C 12 75 4 := by decide +kernel
theorem cell_12_75_5 : C 12 75 5 := by decide +kernel
theorem row_12_75 : ThresholdAt 12 75 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 75 0 cell_12_75_0
  | exact S 12 75 1 cell_12_75_1
  | exact S 12 75 2 cell_12_75_2
  | exact S 12 75 3 cell_12_75_3
  | exact S 12 75 4 cell_12_75_4
  | exact S 12 75 5 cell_12_75_5
theorem cell_12_76_0 : C 12 76 0 := by decide +kernel
theorem cell_12_76_1 : C 12 76 1 := by decide +kernel
theorem cell_12_76_2 : C 12 76 2 := by decide +kernel
theorem cell_12_76_3 : C 12 76 3 := by decide +kernel
theorem cell_12_76_4 : C 12 76 4 := by decide +kernel
theorem cell_12_76_5 : C 12 76 5 := by decide +kernel
theorem row_12_76 : ThresholdAt 12 76 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 76 0 cell_12_76_0
  | exact S 12 76 1 cell_12_76_1
  | exact S 12 76 2 cell_12_76_2
  | exact S 12 76 3 cell_12_76_3
  | exact S 12 76 4 cell_12_76_4
  | exact S 12 76 5 cell_12_76_5
theorem cell_12_77_0 : C 12 77 0 := by decide +kernel
theorem cell_12_77_1 : C 12 77 1 := by decide +kernel
theorem cell_12_77_2 : C 12 77 2 := by decide +kernel
theorem cell_12_77_3 : C 12 77 3 := by decide +kernel
theorem cell_12_77_4 : C 12 77 4 := by decide +kernel
theorem cell_12_77_5 : C 12 77 5 := by decide +kernel
theorem row_12_77 : ThresholdAt 12 77 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 77 0 cell_12_77_0
  | exact S 12 77 1 cell_12_77_1
  | exact S 12 77 2 cell_12_77_2
  | exact S 12 77 3 cell_12_77_3
  | exact S 12 77 4 cell_12_77_4
  | exact S 12 77 5 cell_12_77_5
theorem cell_12_78_0 : C 12 78 0 := by decide +kernel
theorem cell_12_78_1 : C 12 78 1 := by decide +kernel
theorem cell_12_78_2 : C 12 78 2 := by decide +kernel
theorem cell_12_78_3 : C 12 78 3 := by decide +kernel
theorem cell_12_78_4 : C 12 78 4 := by decide +kernel
theorem cell_12_78_5 : C 12 78 5 := by decide +kernel
theorem row_12_78 : ThresholdAt 12 78 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 78 0 cell_12_78_0
  | exact S 12 78 1 cell_12_78_1
  | exact S 12 78 2 cell_12_78_2
  | exact S 12 78 3 cell_12_78_3
  | exact S 12 78 4 cell_12_78_4
  | exact S 12 78 5 cell_12_78_5
theorem cell_12_79_0 : C 12 79 0 := by decide +kernel
theorem cell_12_79_1 : C 12 79 1 := by decide +kernel
theorem cell_12_79_2 : C 12 79 2 := by decide +kernel
theorem cell_12_79_3 : C 12 79 3 := by decide +kernel
theorem cell_12_79_4 : C 12 79 4 := by decide +kernel
theorem cell_12_79_5 : C 12 79 5 := by decide +kernel
theorem row_12_79 : ThresholdAt 12 79 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 79 0 cell_12_79_0
  | exact S 12 79 1 cell_12_79_1
  | exact S 12 79 2 cell_12_79_2
  | exact S 12 79 3 cell_12_79_3
  | exact S 12 79 4 cell_12_79_4
  | exact S 12 79 5 cell_12_79_5
theorem cell_12_80_0 : C 12 80 0 := by decide +kernel
theorem cell_12_80_1 : C 12 80 1 := by decide +kernel
theorem cell_12_80_2 : C 12 80 2 := by decide +kernel
theorem cell_12_80_3 : C 12 80 3 := by decide +kernel
theorem cell_12_80_4 : C 12 80 4 := by decide +kernel
theorem cell_12_80_5 : C 12 80 5 := by decide +kernel
theorem row_12_80 : ThresholdAt 12 80 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 80 0 cell_12_80_0
  | exact S 12 80 1 cell_12_80_1
  | exact S 12 80 2 cell_12_80_2
  | exact S 12 80 3 cell_12_80_3
  | exact S 12 80 4 cell_12_80_4
  | exact S 12 80 5 cell_12_80_5
theorem cell_12_81_0 : C 12 81 0 := by decide +kernel
theorem cell_12_81_1 : C 12 81 1 := by decide +kernel
theorem cell_12_81_2 : C 12 81 2 := by decide +kernel
theorem cell_12_81_3 : C 12 81 3 := by decide +kernel
theorem cell_12_81_4 : C 12 81 4 := by decide +kernel
theorem cell_12_81_5 : C 12 81 5 := by decide +kernel
theorem row_12_81 : ThresholdAt 12 81 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 81 0 cell_12_81_0
  | exact S 12 81 1 cell_12_81_1
  | exact S 12 81 2 cell_12_81_2
  | exact S 12 81 3 cell_12_81_3
  | exact S 12 81 4 cell_12_81_4
  | exact S 12 81 5 cell_12_81_5
theorem cell_12_82_0 : C 12 82 0 := by decide +kernel
theorem cell_12_82_1 : C 12 82 1 := by decide +kernel
theorem cell_12_82_2 : C 12 82 2 := by decide +kernel
theorem cell_12_82_3 : C 12 82 3 := by decide +kernel
theorem cell_12_82_4 : C 12 82 4 := by decide +kernel
theorem cell_12_82_5 : C 12 82 5 := by decide +kernel
theorem row_12_82 : ThresholdAt 12 82 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 82 0 cell_12_82_0
  | exact S 12 82 1 cell_12_82_1
  | exact S 12 82 2 cell_12_82_2
  | exact S 12 82 3 cell_12_82_3
  | exact S 12 82 4 cell_12_82_4
  | exact S 12 82 5 cell_12_82_5
theorem cell_12_83_0 : C 12 83 0 := by decide +kernel
theorem cell_12_83_1 : C 12 83 1 := by decide +kernel
theorem cell_12_83_2 : C 12 83 2 := by decide +kernel
theorem cell_12_83_3 : C 12 83 3 := by decide +kernel
theorem cell_12_83_4 : C 12 83 4 := by decide +kernel
theorem cell_12_83_5 : C 12 83 5 := by decide +kernel
theorem row_12_83 : ThresholdAt 12 83 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 83 0 cell_12_83_0
  | exact S 12 83 1 cell_12_83_1
  | exact S 12 83 2 cell_12_83_2
  | exact S 12 83 3 cell_12_83_3
  | exact S 12 83 4 cell_12_83_4
  | exact S 12 83 5 cell_12_83_5
theorem cell_12_84_0 : C 12 84 0 := by decide +kernel
theorem cell_12_84_1 : C 12 84 1 := by decide +kernel
theorem cell_12_84_2 : C 12 84 2 := by decide +kernel
theorem cell_12_84_3 : C 12 84 3 := by decide +kernel
theorem cell_12_84_4 : C 12 84 4 := by decide +kernel
theorem cell_12_84_5 : C 12 84 5 := by decide +kernel
theorem row_12_84 : ThresholdAt 12 84 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 84 0 cell_12_84_0
  | exact S 12 84 1 cell_12_84_1
  | exact S 12 84 2 cell_12_84_2
  | exact S 12 84 3 cell_12_84_3
  | exact S 12 84 4 cell_12_84_4
  | exact S 12 84 5 cell_12_84_5
theorem cell_12_85_0 : C 12 85 0 := by decide +kernel
theorem cell_12_85_1 : C 12 85 1 := by decide +kernel
theorem cell_12_85_2 : C 12 85 2 := by decide +kernel
theorem cell_12_85_3 : C 12 85 3 := by decide +kernel
theorem cell_12_85_4 : C 12 85 4 := by decide +kernel
theorem cell_12_85_5 : C 12 85 5 := by decide +kernel
theorem row_12_85 : ThresholdAt 12 85 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 85 0 cell_12_85_0
  | exact S 12 85 1 cell_12_85_1
  | exact S 12 85 2 cell_12_85_2
  | exact S 12 85 3 cell_12_85_3
  | exact S 12 85 4 cell_12_85_4
  | exact S 12 85 5 cell_12_85_5
theorem cell_12_86_0 : C 12 86 0 := by decide +kernel
theorem cell_12_86_1 : C 12 86 1 := by decide +kernel
theorem cell_12_86_2 : C 12 86 2 := by decide +kernel
theorem cell_12_86_3 : C 12 86 3 := by decide +kernel
theorem cell_12_86_4 : C 12 86 4 := by decide +kernel
theorem cell_12_86_5 : C 12 86 5 := by decide +kernel
theorem row_12_86 : ThresholdAt 12 86 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 86 0 cell_12_86_0
  | exact S 12 86 1 cell_12_86_1
  | exact S 12 86 2 cell_12_86_2
  | exact S 12 86 3 cell_12_86_3
  | exact S 12 86 4 cell_12_86_4
  | exact S 12 86 5 cell_12_86_5
theorem cell_12_87_0 : C 12 87 0 := by decide +kernel
theorem cell_12_87_1 : C 12 87 1 := by decide +kernel
theorem cell_12_87_2 : C 12 87 2 := by decide +kernel
theorem cell_12_87_3 : C 12 87 3 := by decide +kernel
theorem cell_12_87_4 : C 12 87 4 := by decide +kernel
theorem cell_12_87_5 : C 12 87 5 := by decide +kernel
theorem row_12_87 : ThresholdAt 12 87 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 87 0 cell_12_87_0
  | exact S 12 87 1 cell_12_87_1
  | exact S 12 87 2 cell_12_87_2
  | exact S 12 87 3 cell_12_87_3
  | exact S 12 87 4 cell_12_87_4
  | exact S 12 87 5 cell_12_87_5
theorem cell_12_88_0 : C 12 88 0 := by decide +kernel
theorem cell_12_88_1 : C 12 88 1 := by decide +kernel
theorem cell_12_88_2 : C 12 88 2 := by decide +kernel
theorem cell_12_88_3 : C 12 88 3 := by decide +kernel
theorem cell_12_88_4 : C 12 88 4 := by decide +kernel
theorem cell_12_88_5 : C 12 88 5 := by decide +kernel
theorem row_12_88 : ThresholdAt 12 88 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 88 0 cell_12_88_0
  | exact S 12 88 1 cell_12_88_1
  | exact S 12 88 2 cell_12_88_2
  | exact S 12 88 3 cell_12_88_3
  | exact S 12 88 4 cell_12_88_4
  | exact S 12 88 5 cell_12_88_5
theorem cell_12_89_0 : C 12 89 0 := by decide +kernel
theorem cell_12_89_1 : C 12 89 1 := by decide +kernel
theorem cell_12_89_2 : C 12 89 2 := by decide +kernel
theorem cell_12_89_3 : C 12 89 3 := by decide +kernel
theorem cell_12_89_4 : C 12 89 4 := by decide +kernel
theorem cell_12_89_5 : C 12 89 5 := by decide +kernel
theorem row_12_89 : ThresholdAt 12 89 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 89 0 cell_12_89_0
  | exact S 12 89 1 cell_12_89_1
  | exact S 12 89 2 cell_12_89_2
  | exact S 12 89 3 cell_12_89_3
  | exact S 12 89 4 cell_12_89_4
  | exact S 12 89 5 cell_12_89_5
theorem cell_12_90_0 : C 12 90 0 := by decide +kernel
theorem cell_12_90_1 : C 12 90 1 := by decide +kernel
theorem cell_12_90_2 : C 12 90 2 := by decide +kernel
theorem cell_12_90_3 : C 12 90 3 := by decide +kernel
theorem cell_12_90_4 : C 12 90 4 := by decide +kernel
theorem cell_12_90_5 : C 12 90 5 := by decide +kernel
theorem row_12_90 : ThresholdAt 12 90 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 90 0 cell_12_90_0
  | exact S 12 90 1 cell_12_90_1
  | exact S 12 90 2 cell_12_90_2
  | exact S 12 90 3 cell_12_90_3
  | exact S 12 90 4 cell_12_90_4
  | exact S 12 90 5 cell_12_90_5
theorem cell_12_91_0 : C 12 91 0 := by decide +kernel
theorem cell_12_91_1 : C 12 91 1 := by decide +kernel
theorem cell_12_91_2 : C 12 91 2 := by decide +kernel
theorem cell_12_91_3 : C 12 91 3 := by decide +kernel
theorem cell_12_91_4 : C 12 91 4 := by decide +kernel
theorem cell_12_91_5 : C 12 91 5 := by decide +kernel
theorem row_12_91 : ThresholdAt 12 91 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 91 0 cell_12_91_0
  | exact S 12 91 1 cell_12_91_1
  | exact S 12 91 2 cell_12_91_2
  | exact S 12 91 3 cell_12_91_3
  | exact S 12 91 4 cell_12_91_4
  | exact S 12 91 5 cell_12_91_5
theorem cell_12_92_0 : C 12 92 0 := by decide +kernel
theorem cell_12_92_1 : C 12 92 1 := by decide +kernel
theorem cell_12_92_2 : C 12 92 2 := by decide +kernel
theorem cell_12_92_3 : C 12 92 3 := by decide +kernel
theorem cell_12_92_4 : C 12 92 4 := by decide +kernel
theorem cell_12_92_5 : C 12 92 5 := by decide +kernel
theorem row_12_92 : ThresholdAt 12 92 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 92 0 cell_12_92_0
  | exact S 12 92 1 cell_12_92_1
  | exact S 12 92 2 cell_12_92_2
  | exact S 12 92 3 cell_12_92_3
  | exact S 12 92 4 cell_12_92_4
  | exact S 12 92 5 cell_12_92_5
theorem cell_12_93_0 : C 12 93 0 := by decide +kernel
theorem cell_12_93_1 : C 12 93 1 := by decide +kernel
theorem cell_12_93_2 : C 12 93 2 := by decide +kernel
theorem cell_12_93_3 : C 12 93 3 := by decide +kernel
theorem cell_12_93_4 : C 12 93 4 := by decide +kernel
theorem cell_12_93_5 : C 12 93 5 := by decide +kernel
theorem row_12_93 : ThresholdAt 12 93 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 93 0 cell_12_93_0
  | exact S 12 93 1 cell_12_93_1
  | exact S 12 93 2 cell_12_93_2
  | exact S 12 93 3 cell_12_93_3
  | exact S 12 93 4 cell_12_93_4
  | exact S 12 93 5 cell_12_93_5
theorem cell_12_94_0 : C 12 94 0 := by decide +kernel
theorem cell_12_94_1 : C 12 94 1 := by decide +kernel
theorem cell_12_94_2 : C 12 94 2 := by decide +kernel
theorem cell_12_94_3 : C 12 94 3 := by decide +kernel
theorem cell_12_94_4 : C 12 94 4 := by decide +kernel
theorem cell_12_94_5 : C 12 94 5 := by decide +kernel
theorem row_12_94 : ThresholdAt 12 94 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 94 0 cell_12_94_0
  | exact S 12 94 1 cell_12_94_1
  | exact S 12 94 2 cell_12_94_2
  | exact S 12 94 3 cell_12_94_3
  | exact S 12 94 4 cell_12_94_4
  | exact S 12 94 5 cell_12_94_5
theorem cell_12_95_0 : C 12 95 0 := by decide +kernel
theorem cell_12_95_1 : C 12 95 1 := by decide +kernel
theorem cell_12_95_2 : C 12 95 2 := by decide +kernel
theorem cell_12_95_3 : C 12 95 3 := by decide +kernel
theorem cell_12_95_4 : C 12 95 4 := by decide +kernel
theorem cell_12_95_5 : C 12 95 5 := by decide +kernel
theorem row_12_95 : ThresholdAt 12 95 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 95 0 cell_12_95_0
  | exact S 12 95 1 cell_12_95_1
  | exact S 12 95 2 cell_12_95_2
  | exact S 12 95 3 cell_12_95_3
  | exact S 12 95 4 cell_12_95_4
  | exact S 12 95 5 cell_12_95_5
theorem cell_12_96_0 : C 12 96 0 := by decide +kernel
theorem cell_12_96_1 : C 12 96 1 := by decide +kernel
theorem cell_12_96_2 : C 12 96 2 := by decide +kernel
theorem cell_12_96_3 : C 12 96 3 := by decide +kernel
theorem cell_12_96_4 : C 12 96 4 := by decide +kernel
theorem cell_12_96_5 : C 12 96 5 := by decide +kernel
theorem row_12_96 : ThresholdAt 12 96 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 96 0 cell_12_96_0
  | exact S 12 96 1 cell_12_96_1
  | exact S 12 96 2 cell_12_96_2
  | exact S 12 96 3 cell_12_96_3
  | exact S 12 96 4 cell_12_96_4
  | exact S 12 96 5 cell_12_96_5
theorem cell_12_97_0 : C 12 97 0 := by decide +kernel
theorem cell_12_97_1 : C 12 97 1 := by decide +kernel
theorem cell_12_97_2 : C 12 97 2 := by decide +kernel
theorem cell_12_97_3 : C 12 97 3 := by decide +kernel
theorem cell_12_97_4 : C 12 97 4 := by decide +kernel
theorem cell_12_97_5 : C 12 97 5 := by decide +kernel
theorem row_12_97 : ThresholdAt 12 97 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 97 0 cell_12_97_0
  | exact S 12 97 1 cell_12_97_1
  | exact S 12 97 2 cell_12_97_2
  | exact S 12 97 3 cell_12_97_3
  | exact S 12 97 4 cell_12_97_4
  | exact S 12 97 5 cell_12_97_5
theorem cell_12_98_0 : C 12 98 0 := by decide +kernel
theorem cell_12_98_1 : C 12 98 1 := by decide +kernel
theorem cell_12_98_2 : C 12 98 2 := by decide +kernel
theorem cell_12_98_3 : C 12 98 3 := by decide +kernel
theorem cell_12_98_4 : C 12 98 4 := by decide +kernel
theorem cell_12_98_5 : C 12 98 5 := by decide +kernel
theorem row_12_98 : ThresholdAt 12 98 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 98 0 cell_12_98_0
  | exact S 12 98 1 cell_12_98_1
  | exact S 12 98 2 cell_12_98_2
  | exact S 12 98 3 cell_12_98_3
  | exact S 12 98 4 cell_12_98_4
  | exact S 12 98 5 cell_12_98_5
theorem cell_12_99_0 : C 12 99 0 := by decide +kernel
theorem cell_12_99_1 : C 12 99 1 := by decide +kernel
theorem cell_12_99_2 : C 12 99 2 := by decide +kernel
theorem cell_12_99_3 : C 12 99 3 := by decide +kernel
theorem cell_12_99_4 : C 12 99 4 := by decide +kernel
theorem cell_12_99_5 : C 12 99 5 := by decide +kernel
theorem row_12_99 : ThresholdAt 12 99 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 99 0 cell_12_99_0
  | exact S 12 99 1 cell_12_99_1
  | exact S 12 99 2 cell_12_99_2
  | exact S 12 99 3 cell_12_99_3
  | exact S 12 99 4 cell_12_99_4
  | exact S 12 99 5 cell_12_99_5
theorem cell_12_100_0 : C 12 100 0 := by decide +kernel
theorem cell_12_100_1 : C 12 100 1 := by decide +kernel
theorem cell_12_100_2 : C 12 100 2 := by decide +kernel
theorem cell_12_100_3 : C 12 100 3 := by decide +kernel
theorem cell_12_100_4 : C 12 100 4 := by decide +kernel
theorem cell_12_100_5 : C 12 100 5 := by decide +kernel
theorem row_12_100 : ThresholdAt 12 100 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 100 0 cell_12_100_0
  | exact S 12 100 1 cell_12_100_1
  | exact S 12 100 2 cell_12_100_2
  | exact S 12 100 3 cell_12_100_3
  | exact S 12 100 4 cell_12_100_4
  | exact S 12 100 5 cell_12_100_5
theorem cell_12_101_0 : C 12 101 0 := by decide +kernel
theorem cell_12_101_1 : C 12 101 1 := by decide +kernel
theorem cell_12_101_2 : C 12 101 2 := by decide +kernel
theorem cell_12_101_3 : C 12 101 3 := by decide +kernel
theorem cell_12_101_4 : C 12 101 4 := by decide +kernel
theorem cell_12_101_5 : C 12 101 5 := by decide +kernel
theorem row_12_101 : ThresholdAt 12 101 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 101 0 cell_12_101_0
  | exact S 12 101 1 cell_12_101_1
  | exact S 12 101 2 cell_12_101_2
  | exact S 12 101 3 cell_12_101_3
  | exact S 12 101 4 cell_12_101_4
  | exact S 12 101 5 cell_12_101_5
theorem cell_12_102_0 : C 12 102 0 := by decide +kernel
theorem cell_12_102_1 : C 12 102 1 := by decide +kernel
theorem cell_12_102_2 : C 12 102 2 := by decide +kernel
theorem cell_12_102_3 : C 12 102 3 := by decide +kernel
theorem cell_12_102_4 : C 12 102 4 := by decide +kernel
theorem cell_12_102_5 : C 12 102 5 := by decide +kernel
theorem row_12_102 : ThresholdAt 12 102 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 102 0 cell_12_102_0
  | exact S 12 102 1 cell_12_102_1
  | exact S 12 102 2 cell_12_102_2
  | exact S 12 102 3 cell_12_102_3
  | exact S 12 102 4 cell_12_102_4
  | exact S 12 102 5 cell_12_102_5
theorem cell_12_103_0 : C 12 103 0 := by decide +kernel
theorem cell_12_103_1 : C 12 103 1 := by decide +kernel
theorem cell_12_103_2 : C 12 103 2 := by decide +kernel
theorem cell_12_103_3 : C 12 103 3 := by decide +kernel
theorem cell_12_103_4 : C 12 103 4 := by decide +kernel
theorem cell_12_103_5 : C 12 103 5 := by decide +kernel
theorem row_12_103 : ThresholdAt 12 103 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 103 0 cell_12_103_0
  | exact S 12 103 1 cell_12_103_1
  | exact S 12 103 2 cell_12_103_2
  | exact S 12 103 3 cell_12_103_3
  | exact S 12 103 4 cell_12_103_4
  | exact S 12 103 5 cell_12_103_5
theorem cell_12_104_0 : C 12 104 0 := by decide +kernel
theorem cell_12_104_1 : C 12 104 1 := by decide +kernel
theorem cell_12_104_2 : C 12 104 2 := by decide +kernel
theorem cell_12_104_3 : C 12 104 3 := by decide +kernel
theorem cell_12_104_4 : C 12 104 4 := by decide +kernel
theorem cell_12_104_5 : C 12 104 5 := by decide +kernel
theorem row_12_104 : ThresholdAt 12 104 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 104 0 cell_12_104_0
  | exact S 12 104 1 cell_12_104_1
  | exact S 12 104 2 cell_12_104_2
  | exact S 12 104 3 cell_12_104_3
  | exact S 12 104 4 cell_12_104_4
  | exact S 12 104 5 cell_12_104_5
theorem cell_12_105_0 : C 12 105 0 := by decide +kernel
theorem cell_12_105_1 : C 12 105 1 := by decide +kernel
theorem cell_12_105_2 : C 12 105 2 := by decide +kernel
theorem cell_12_105_3 : C 12 105 3 := by decide +kernel
theorem cell_12_105_4 : C 12 105 4 := by decide +kernel
theorem cell_12_105_5 : C 12 105 5 := by decide +kernel
theorem row_12_105 : ThresholdAt 12 105 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 105 0 cell_12_105_0
  | exact S 12 105 1 cell_12_105_1
  | exact S 12 105 2 cell_12_105_2
  | exact S 12 105 3 cell_12_105_3
  | exact S 12 105 4 cell_12_105_4
  | exact S 12 105 5 cell_12_105_5
theorem cell_12_106_0 : C 12 106 0 := by decide +kernel
theorem cell_12_106_1 : C 12 106 1 := by decide +kernel
theorem cell_12_106_2 : C 12 106 2 := by decide +kernel
theorem cell_12_106_3 : C 12 106 3 := by decide +kernel
theorem cell_12_106_4 : C 12 106 4 := by decide +kernel
theorem cell_12_106_5 : C 12 106 5 := by decide +kernel
theorem row_12_106 : ThresholdAt 12 106 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 106 0 cell_12_106_0
  | exact S 12 106 1 cell_12_106_1
  | exact S 12 106 2 cell_12_106_2
  | exact S 12 106 3 cell_12_106_3
  | exact S 12 106 4 cell_12_106_4
  | exact S 12 106 5 cell_12_106_5
theorem cell_12_107_0 : C 12 107 0 := by decide +kernel
theorem cell_12_107_1 : C 12 107 1 := by decide +kernel
theorem cell_12_107_2 : C 12 107 2 := by decide +kernel
theorem cell_12_107_3 : C 12 107 3 := by decide +kernel
theorem cell_12_107_4 : C 12 107 4 := by decide +kernel
theorem cell_12_107_5 : C 12 107 5 := by decide +kernel
theorem row_12_107 : ThresholdAt 12 107 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 107 0 cell_12_107_0
  | exact S 12 107 1 cell_12_107_1
  | exact S 12 107 2 cell_12_107_2
  | exact S 12 107 3 cell_12_107_3
  | exact S 12 107 4 cell_12_107_4
  | exact S 12 107 5 cell_12_107_5
theorem cell_12_108_0 : C 12 108 0 := by decide +kernel
theorem cell_12_108_1 : C 12 108 1 := by decide +kernel
theorem cell_12_108_2 : C 12 108 2 := by decide +kernel
theorem cell_12_108_3 : C 12 108 3 := by decide +kernel
theorem cell_12_108_4 : C 12 108 4 := by decide +kernel
theorem cell_12_108_5 : C 12 108 5 := by decide +kernel
theorem row_12_108 : ThresholdAt 12 108 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 108 0 cell_12_108_0
  | exact S 12 108 1 cell_12_108_1
  | exact S 12 108 2 cell_12_108_2
  | exact S 12 108 3 cell_12_108_3
  | exact S 12 108 4 cell_12_108_4
  | exact S 12 108 5 cell_12_108_5
theorem cell_12_109_0 : C 12 109 0 := by decide +kernel
theorem cell_12_109_1 : C 12 109 1 := by decide +kernel
theorem cell_12_109_2 : C 12 109 2 := by decide +kernel
theorem cell_12_109_3 : C 12 109 3 := by decide +kernel
theorem cell_12_109_4 : C 12 109 4 := by decide +kernel
theorem cell_12_109_5 : C 12 109 5 := by decide +kernel
theorem row_12_109 : ThresholdAt 12 109 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 109 0 cell_12_109_0
  | exact S 12 109 1 cell_12_109_1
  | exact S 12 109 2 cell_12_109_2
  | exact S 12 109 3 cell_12_109_3
  | exact S 12 109 4 cell_12_109_4
  | exact S 12 109 5 cell_12_109_5
theorem cell_12_110_0 : C 12 110 0 := by decide +kernel
theorem cell_12_110_1 : C 12 110 1 := by decide +kernel
theorem cell_12_110_2 : C 12 110 2 := by decide +kernel
theorem cell_12_110_3 : C 12 110 3 := by decide +kernel
theorem cell_12_110_4 : C 12 110 4 := by decide +kernel
theorem cell_12_110_5 : C 12 110 5 := by decide +kernel
theorem row_12_110 : ThresholdAt 12 110 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 110 0 cell_12_110_0
  | exact S 12 110 1 cell_12_110_1
  | exact S 12 110 2 cell_12_110_2
  | exact S 12 110 3 cell_12_110_3
  | exact S 12 110 4 cell_12_110_4
  | exact S 12 110 5 cell_12_110_5
theorem cell_12_111_0 : C 12 111 0 := by decide +kernel
theorem cell_12_111_1 : C 12 111 1 := by decide +kernel
theorem cell_12_111_2 : C 12 111 2 := by decide +kernel
theorem cell_12_111_3 : C 12 111 3 := by decide +kernel
theorem cell_12_111_4 : C 12 111 4 := by decide +kernel
theorem cell_12_111_5 : C 12 111 5 := by decide +kernel
theorem row_12_111 : ThresholdAt 12 111 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 111 0 cell_12_111_0
  | exact S 12 111 1 cell_12_111_1
  | exact S 12 111 2 cell_12_111_2
  | exact S 12 111 3 cell_12_111_3
  | exact S 12 111 4 cell_12_111_4
  | exact S 12 111 5 cell_12_111_5
theorem cell_12_112_0 : C 12 112 0 := by decide +kernel
theorem cell_12_112_1 : C 12 112 1 := by decide +kernel
theorem cell_12_112_2 : C 12 112 2 := by decide +kernel
theorem cell_12_112_3 : C 12 112 3 := by decide +kernel
theorem cell_12_112_4 : C 12 112 4 := by decide +kernel
theorem cell_12_112_5 : C 12 112 5 := by decide +kernel
theorem row_12_112 : ThresholdAt 12 112 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 112 0 cell_12_112_0
  | exact S 12 112 1 cell_12_112_1
  | exact S 12 112 2 cell_12_112_2
  | exact S 12 112 3 cell_12_112_3
  | exact S 12 112 4 cell_12_112_4
  | exact S 12 112 5 cell_12_112_5
theorem cell_12_113_0 : C 12 113 0 := by decide +kernel
theorem cell_12_113_1 : C 12 113 1 := by decide +kernel
theorem cell_12_113_2 : C 12 113 2 := by decide +kernel
theorem cell_12_113_3 : C 12 113 3 := by decide +kernel
theorem cell_12_113_4 : C 12 113 4 := by decide +kernel
theorem cell_12_113_5 : C 12 113 5 := by decide +kernel
theorem row_12_113 : ThresholdAt 12 113 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 113 0 cell_12_113_0
  | exact S 12 113 1 cell_12_113_1
  | exact S 12 113 2 cell_12_113_2
  | exact S 12 113 3 cell_12_113_3
  | exact S 12 113 4 cell_12_113_4
  | exact S 12 113 5 cell_12_113_5
theorem cell_12_114_0 : C 12 114 0 := by decide +kernel
theorem cell_12_114_1 : C 12 114 1 := by decide +kernel
theorem cell_12_114_2 : C 12 114 2 := by decide +kernel
theorem cell_12_114_3 : C 12 114 3 := by decide +kernel
theorem cell_12_114_4 : C 12 114 4 := by decide +kernel
theorem cell_12_114_5 : C 12 114 5 := by decide +kernel
theorem row_12_114 : ThresholdAt 12 114 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 114 0 cell_12_114_0
  | exact S 12 114 1 cell_12_114_1
  | exact S 12 114 2 cell_12_114_2
  | exact S 12 114 3 cell_12_114_3
  | exact S 12 114 4 cell_12_114_4
  | exact S 12 114 5 cell_12_114_5
theorem cell_12_115_0 : C 12 115 0 := by decide +kernel
theorem cell_12_115_1 : C 12 115 1 := by decide +kernel
theorem cell_12_115_2 : C 12 115 2 := by decide +kernel
theorem cell_12_115_3 : C 12 115 3 := by decide +kernel
theorem cell_12_115_4 : C 12 115 4 := by decide +kernel
theorem cell_12_115_5 : C 12 115 5 := by decide +kernel
theorem row_12_115 : ThresholdAt 12 115 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 115 0 cell_12_115_0
  | exact S 12 115 1 cell_12_115_1
  | exact S 12 115 2 cell_12_115_2
  | exact S 12 115 3 cell_12_115_3
  | exact S 12 115 4 cell_12_115_4
  | exact S 12 115 5 cell_12_115_5
theorem cell_12_116_0 : C 12 116 0 := by decide +kernel
theorem cell_12_116_1 : C 12 116 1 := by decide +kernel
theorem cell_12_116_2 : C 12 116 2 := by decide +kernel
theorem cell_12_116_3 : C 12 116 3 := by decide +kernel
theorem cell_12_116_4 : C 12 116 4 := by decide +kernel
theorem cell_12_116_5 : C 12 116 5 := by decide +kernel
theorem row_12_116 : ThresholdAt 12 116 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 116 0 cell_12_116_0
  | exact S 12 116 1 cell_12_116_1
  | exact S 12 116 2 cell_12_116_2
  | exact S 12 116 3 cell_12_116_3
  | exact S 12 116 4 cell_12_116_4
  | exact S 12 116 5 cell_12_116_5
theorem cell_12_117_0 : C 12 117 0 := by decide +kernel
theorem cell_12_117_1 : C 12 117 1 := by decide +kernel
theorem cell_12_117_2 : C 12 117 2 := by decide +kernel
theorem cell_12_117_3 : C 12 117 3 := by decide +kernel
theorem cell_12_117_4 : C 12 117 4 := by decide +kernel
theorem cell_12_117_5 : C 12 117 5 := by decide +kernel
theorem row_12_117 : ThresholdAt 12 117 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 117 0 cell_12_117_0
  | exact S 12 117 1 cell_12_117_1
  | exact S 12 117 2 cell_12_117_2
  | exact S 12 117 3 cell_12_117_3
  | exact S 12 117 4 cell_12_117_4
  | exact S 12 117 5 cell_12_117_5
theorem cell_12_118_0 : C 12 118 0 := by decide +kernel
theorem cell_12_118_1 : C 12 118 1 := by decide +kernel
theorem cell_12_118_2 : C 12 118 2 := by decide +kernel
theorem cell_12_118_3 : C 12 118 3 := by decide +kernel
theorem cell_12_118_4 : C 12 118 4 := by decide +kernel
theorem cell_12_118_5 : C 12 118 5 := by decide +kernel
theorem row_12_118 : ThresholdAt 12 118 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 118 0 cell_12_118_0
  | exact S 12 118 1 cell_12_118_1
  | exact S 12 118 2 cell_12_118_2
  | exact S 12 118 3 cell_12_118_3
  | exact S 12 118 4 cell_12_118_4
  | exact S 12 118 5 cell_12_118_5
theorem cell_12_119_0 : C 12 119 0 := by decide +kernel
theorem cell_12_119_1 : C 12 119 1 := by decide +kernel
theorem cell_12_119_2 : C 12 119 2 := by decide +kernel
theorem cell_12_119_3 : C 12 119 3 := by decide +kernel
theorem cell_12_119_4 : C 12 119 4 := by decide +kernel
theorem cell_12_119_5 : C 12 119 5 := by decide +kernel
theorem row_12_119 : ThresholdAt 12 119 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 119 0 cell_12_119_0
  | exact S 12 119 1 cell_12_119_1
  | exact S 12 119 2 cell_12_119_2
  | exact S 12 119 3 cell_12_119_3
  | exact S 12 119 4 cell_12_119_4
  | exact S 12 119 5 cell_12_119_5
theorem cell_12_120_0 : C 12 120 0 := by decide +kernel
theorem cell_12_120_1 : C 12 120 1 := by decide +kernel
theorem cell_12_120_2 : C 12 120 2 := by decide +kernel
theorem cell_12_120_3 : C 12 120 3 := by decide +kernel
theorem cell_12_120_4 : C 12 120 4 := by decide +kernel
theorem cell_12_120_5 : C 12 120 5 := by decide +kernel
theorem row_12_120 : ThresholdAt 12 120 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 120 0 cell_12_120_0
  | exact S 12 120 1 cell_12_120_1
  | exact S 12 120 2 cell_12_120_2
  | exact S 12 120 3 cell_12_120_3
  | exact S 12 120 4 cell_12_120_4
  | exact S 12 120 5 cell_12_120_5
theorem cell_12_121_0 : C 12 121 0 := by decide +kernel
theorem cell_12_121_1 : C 12 121 1 := by decide +kernel
theorem cell_12_121_2 : C 12 121 2 := by decide +kernel
theorem cell_12_121_3 : C 12 121 3 := by decide +kernel
theorem cell_12_121_4 : C 12 121 4 := by decide +kernel
theorem cell_12_121_5 : C 12 121 5 := by decide +kernel
theorem row_12_121 : ThresholdAt 12 121 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 121 0 cell_12_121_0
  | exact S 12 121 1 cell_12_121_1
  | exact S 12 121 2 cell_12_121_2
  | exact S 12 121 3 cell_12_121_3
  | exact S 12 121 4 cell_12_121_4
  | exact S 12 121 5 cell_12_121_5
theorem cell_12_122_0 : C 12 122 0 := by decide +kernel
theorem cell_12_122_1 : C 12 122 1 := by decide +kernel
theorem cell_12_122_2 : C 12 122 2 := by decide +kernel
theorem cell_12_122_3 : C 12 122 3 := by decide +kernel
theorem cell_12_122_4 : C 12 122 4 := by decide +kernel
theorem cell_12_122_5 : C 12 122 5 := by decide +kernel
theorem row_12_122 : ThresholdAt 12 122 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 122 0 cell_12_122_0
  | exact S 12 122 1 cell_12_122_1
  | exact S 12 122 2 cell_12_122_2
  | exact S 12 122 3 cell_12_122_3
  | exact S 12 122 4 cell_12_122_4
  | exact S 12 122 5 cell_12_122_5
theorem cell_12_123_0 : C 12 123 0 := by decide +kernel
theorem cell_12_123_1 : C 12 123 1 := by decide +kernel
theorem cell_12_123_2 : C 12 123 2 := by decide +kernel
theorem cell_12_123_3 : C 12 123 3 := by decide +kernel
theorem cell_12_123_4 : C 12 123 4 := by decide +kernel
theorem cell_12_123_5 : C 12 123 5 := by decide +kernel
theorem row_12_123 : ThresholdAt 12 123 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 123 0 cell_12_123_0
  | exact S 12 123 1 cell_12_123_1
  | exact S 12 123 2 cell_12_123_2
  | exact S 12 123 3 cell_12_123_3
  | exact S 12 123 4 cell_12_123_4
  | exact S 12 123 5 cell_12_123_5
theorem cell_12_124_0 : C 12 124 0 := by decide +kernel
theorem cell_12_124_1 : C 12 124 1 := by decide +kernel
theorem cell_12_124_2 : C 12 124 2 := by decide +kernel
theorem cell_12_124_3 : C 12 124 3 := by decide +kernel
theorem cell_12_124_4 : C 12 124 4 := by decide +kernel
theorem cell_12_124_5 : C 12 124 5 := by decide +kernel
theorem row_12_124 : ThresholdAt 12 124 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 124 0 cell_12_124_0
  | exact S 12 124 1 cell_12_124_1
  | exact S 12 124 2 cell_12_124_2
  | exact S 12 124 3 cell_12_124_3
  | exact S 12 124 4 cell_12_124_4
  | exact S 12 124 5 cell_12_124_5
theorem cell_12_125_0 : C 12 125 0 := by decide +kernel
theorem cell_12_125_1 : C 12 125 1 := by decide +kernel
theorem cell_12_125_2 : C 12 125 2 := by decide +kernel
theorem cell_12_125_3 : C 12 125 3 := by decide +kernel
theorem cell_12_125_4 : C 12 125 4 := by decide +kernel
theorem cell_12_125_5 : C 12 125 5 := by decide +kernel
theorem row_12_125 : ThresholdAt 12 125 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 125 0 cell_12_125_0
  | exact S 12 125 1 cell_12_125_1
  | exact S 12 125 2 cell_12_125_2
  | exact S 12 125 3 cell_12_125_3
  | exact S 12 125 4 cell_12_125_4
  | exact S 12 125 5 cell_12_125_5
theorem cell_12_126_0 : C 12 126 0 := by decide +kernel
theorem cell_12_126_1 : C 12 126 1 := by decide +kernel
theorem cell_12_126_2 : C 12 126 2 := by decide +kernel
theorem cell_12_126_3 : C 12 126 3 := by decide +kernel
theorem cell_12_126_4 : C 12 126 4 := by decide +kernel
theorem cell_12_126_5 : C 12 126 5 := by decide +kernel
theorem row_12_126 : ThresholdAt 12 126 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 126 0 cell_12_126_0
  | exact S 12 126 1 cell_12_126_1
  | exact S 12 126 2 cell_12_126_2
  | exact S 12 126 3 cell_12_126_3
  | exact S 12 126 4 cell_12_126_4
  | exact S 12 126 5 cell_12_126_5
theorem cell_12_127_0 : C 12 127 0 := by decide +kernel
theorem cell_12_127_1 : C 12 127 1 := by decide +kernel
theorem cell_12_127_2 : C 12 127 2 := by decide +kernel
theorem cell_12_127_3 : C 12 127 3 := by decide +kernel
theorem cell_12_127_4 : C 12 127 4 := by decide +kernel
theorem cell_12_127_5 : C 12 127 5 := by decide +kernel
theorem row_12_127 : ThresholdAt 12 127 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 12 127 0 cell_12_127_0
  | exact S 12 127 1 cell_12_127_1
  | exact S 12 127 2 cell_12_127_2
  | exact S 12 127 3 cell_12_127_3
  | exact S 12 127 4 cell_12_127_4
  | exact S 12 127 5 cell_12_127_5
theorem checkedR12 : ∀ V ∈ List.range 128, ThresholdAt 12 V := by
  intro V hV
  have hv : V < 128 := List.mem_range.mp hV
  by_cases h0_128 : V < 64
  · by_cases h0_64 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have he : V = 0 := by omega
                subst V
                exact row_12_0
              · have he : V = 1 := by omega
                subst V
                exact row_12_1
            · by_cases h2_4 : V < 3
              · have he : V = 2 := by omega
                subst V
                exact row_12_2
              · have he : V = 3 := by omega
                subst V
                exact row_12_3
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have he : V = 4 := by omega
                subst V
                exact row_12_4
              · have he : V = 5 := by omega
                subst V
                exact row_12_5
            · by_cases h6_8 : V < 7
              · have he : V = 6 := by omega
                subst V
                exact row_12_6
              · have he : V = 7 := by omega
                subst V
                exact row_12_7
        · by_cases h8_16 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have he : V = 8 := by omega
                subst V
                exact row_12_8
              · have he : V = 9 := by omega
                subst V
                exact row_12_9
            · by_cases h10_12 : V < 11
              · have he : V = 10 := by omega
                subst V
                exact row_12_10
              · have he : V = 11 := by omega
                subst V
                exact row_12_11
          · by_cases h12_16 : V < 14
            · by_cases h12_14 : V < 13
              · have he : V = 12 := by omega
                subst V
                exact row_12_12
              · have he : V = 13 := by omega
                subst V
                exact row_12_13
            · by_cases h14_16 : V < 15
              · have he : V = 14 := by omega
                subst V
                exact row_12_14
              · have he : V = 15 := by omega
                subst V
                exact row_12_15
      · by_cases h16_32 : V < 24
        · by_cases h16_24 : V < 20
          · by_cases h16_20 : V < 18
            · by_cases h16_18 : V < 17
              · have he : V = 16 := by omega
                subst V
                exact row_12_16
              · have he : V = 17 := by omega
                subst V
                exact row_12_17
            · by_cases h18_20 : V < 19
              · have he : V = 18 := by omega
                subst V
                exact row_12_18
              · have he : V = 19 := by omega
                subst V
                exact row_12_19
          · by_cases h20_24 : V < 22
            · by_cases h20_22 : V < 21
              · have he : V = 20 := by omega
                subst V
                exact row_12_20
              · have he : V = 21 := by omega
                subst V
                exact row_12_21
            · by_cases h22_24 : V < 23
              · have he : V = 22 := by omega
                subst V
                exact row_12_22
              · have he : V = 23 := by omega
                subst V
                exact row_12_23
        · by_cases h24_32 : V < 28
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have he : V = 24 := by omega
                subst V
                exact row_12_24
              · have he : V = 25 := by omega
                subst V
                exact row_12_25
            · by_cases h26_28 : V < 27
              · have he : V = 26 := by omega
                subst V
                exact row_12_26
              · have he : V = 27 := by omega
                subst V
                exact row_12_27
          · by_cases h28_32 : V < 30
            · by_cases h28_30 : V < 29
              · have he : V = 28 := by omega
                subst V
                exact row_12_28
              · have he : V = 29 := by omega
                subst V
                exact row_12_29
            · by_cases h30_32 : V < 31
              · have he : V = 30 := by omega
                subst V
                exact row_12_30
              · have he : V = 31 := by omega
                subst V
                exact row_12_31
    · by_cases h32_64 : V < 48
      · by_cases h32_48 : V < 40
        · by_cases h32_40 : V < 36
          · by_cases h32_36 : V < 34
            · by_cases h32_34 : V < 33
              · have he : V = 32 := by omega
                subst V
                exact row_12_32
              · have he : V = 33 := by omega
                subst V
                exact row_12_33
            · by_cases h34_36 : V < 35
              · have he : V = 34 := by omega
                subst V
                exact row_12_34
              · have he : V = 35 := by omega
                subst V
                exact row_12_35
          · by_cases h36_40 : V < 38
            · by_cases h36_38 : V < 37
              · have he : V = 36 := by omega
                subst V
                exact row_12_36
              · have he : V = 37 := by omega
                subst V
                exact row_12_37
            · by_cases h38_40 : V < 39
              · have he : V = 38 := by omega
                subst V
                exact row_12_38
              · have he : V = 39 := by omega
                subst V
                exact row_12_39
        · by_cases h40_48 : V < 44
          · by_cases h40_44 : V < 42
            · by_cases h40_42 : V < 41
              · have he : V = 40 := by omega
                subst V
                exact row_12_40
              · have he : V = 41 := by omega
                subst V
                exact row_12_41
            · by_cases h42_44 : V < 43
              · have he : V = 42 := by omega
                subst V
                exact row_12_42
              · have he : V = 43 := by omega
                subst V
                exact row_12_43
          · by_cases h44_48 : V < 46
            · by_cases h44_46 : V < 45
              · have he : V = 44 := by omega
                subst V
                exact row_12_44
              · have he : V = 45 := by omega
                subst V
                exact row_12_45
            · by_cases h46_48 : V < 47
              · have he : V = 46 := by omega
                subst V
                exact row_12_46
              · have he : V = 47 := by omega
                subst V
                exact row_12_47
      · by_cases h48_64 : V < 56
        · by_cases h48_56 : V < 52
          · by_cases h48_52 : V < 50
            · by_cases h48_50 : V < 49
              · have he : V = 48 := by omega
                subst V
                exact row_12_48
              · have he : V = 49 := by omega
                subst V
                exact row_12_49
            · by_cases h50_52 : V < 51
              · have he : V = 50 := by omega
                subst V
                exact row_12_50
              · have he : V = 51 := by omega
                subst V
                exact row_12_51
          · by_cases h52_56 : V < 54
            · by_cases h52_54 : V < 53
              · have he : V = 52 := by omega
                subst V
                exact row_12_52
              · have he : V = 53 := by omega
                subst V
                exact row_12_53
            · by_cases h54_56 : V < 55
              · have he : V = 54 := by omega
                subst V
                exact row_12_54
              · have he : V = 55 := by omega
                subst V
                exact row_12_55
        · by_cases h56_64 : V < 60
          · by_cases h56_60 : V < 58
            · by_cases h56_58 : V < 57
              · have he : V = 56 := by omega
                subst V
                exact row_12_56
              · have he : V = 57 := by omega
                subst V
                exact row_12_57
            · by_cases h58_60 : V < 59
              · have he : V = 58 := by omega
                subst V
                exact row_12_58
              · have he : V = 59 := by omega
                subst V
                exact row_12_59
          · by_cases h60_64 : V < 62
            · by_cases h60_62 : V < 61
              · have he : V = 60 := by omega
                subst V
                exact row_12_60
              · have he : V = 61 := by omega
                subst V
                exact row_12_61
            · by_cases h62_64 : V < 63
              · have he : V = 62 := by omega
                subst V
                exact row_12_62
              · have he : V = 63 := by omega
                subst V
                exact row_12_63
  · by_cases h64_128 : V < 96
    · by_cases h64_96 : V < 80
      · by_cases h64_80 : V < 72
        · by_cases h64_72 : V < 68
          · by_cases h64_68 : V < 66
            · by_cases h64_66 : V < 65
              · have he : V = 64 := by omega
                subst V
                exact row_12_64
              · have he : V = 65 := by omega
                subst V
                exact row_12_65
            · by_cases h66_68 : V < 67
              · have he : V = 66 := by omega
                subst V
                exact row_12_66
              · have he : V = 67 := by omega
                subst V
                exact row_12_67
          · by_cases h68_72 : V < 70
            · by_cases h68_70 : V < 69
              · have he : V = 68 := by omega
                subst V
                exact row_12_68
              · have he : V = 69 := by omega
                subst V
                exact row_12_69
            · by_cases h70_72 : V < 71
              · have he : V = 70 := by omega
                subst V
                exact row_12_70
              · have he : V = 71 := by omega
                subst V
                exact row_12_71
        · by_cases h72_80 : V < 76
          · by_cases h72_76 : V < 74
            · by_cases h72_74 : V < 73
              · have he : V = 72 := by omega
                subst V
                exact row_12_72
              · have he : V = 73 := by omega
                subst V
                exact row_12_73
            · by_cases h74_76 : V < 75
              · have he : V = 74 := by omega
                subst V
                exact row_12_74
              · have he : V = 75 := by omega
                subst V
                exact row_12_75
          · by_cases h76_80 : V < 78
            · by_cases h76_78 : V < 77
              · have he : V = 76 := by omega
                subst V
                exact row_12_76
              · have he : V = 77 := by omega
                subst V
                exact row_12_77
            · by_cases h78_80 : V < 79
              · have he : V = 78 := by omega
                subst V
                exact row_12_78
              · have he : V = 79 := by omega
                subst V
                exact row_12_79
      · by_cases h80_96 : V < 88
        · by_cases h80_88 : V < 84
          · by_cases h80_84 : V < 82
            · by_cases h80_82 : V < 81
              · have he : V = 80 := by omega
                subst V
                exact row_12_80
              · have he : V = 81 := by omega
                subst V
                exact row_12_81
            · by_cases h82_84 : V < 83
              · have he : V = 82 := by omega
                subst V
                exact row_12_82
              · have he : V = 83 := by omega
                subst V
                exact row_12_83
          · by_cases h84_88 : V < 86
            · by_cases h84_86 : V < 85
              · have he : V = 84 := by omega
                subst V
                exact row_12_84
              · have he : V = 85 := by omega
                subst V
                exact row_12_85
            · by_cases h86_88 : V < 87
              · have he : V = 86 := by omega
                subst V
                exact row_12_86
              · have he : V = 87 := by omega
                subst V
                exact row_12_87
        · by_cases h88_96 : V < 92
          · by_cases h88_92 : V < 90
            · by_cases h88_90 : V < 89
              · have he : V = 88 := by omega
                subst V
                exact row_12_88
              · have he : V = 89 := by omega
                subst V
                exact row_12_89
            · by_cases h90_92 : V < 91
              · have he : V = 90 := by omega
                subst V
                exact row_12_90
              · have he : V = 91 := by omega
                subst V
                exact row_12_91
          · by_cases h92_96 : V < 94
            · by_cases h92_94 : V < 93
              · have he : V = 92 := by omega
                subst V
                exact row_12_92
              · have he : V = 93 := by omega
                subst V
                exact row_12_93
            · by_cases h94_96 : V < 95
              · have he : V = 94 := by omega
                subst V
                exact row_12_94
              · have he : V = 95 := by omega
                subst V
                exact row_12_95
    · by_cases h96_128 : V < 112
      · by_cases h96_112 : V < 104
        · by_cases h96_104 : V < 100
          · by_cases h96_100 : V < 98
            · by_cases h96_98 : V < 97
              · have he : V = 96 := by omega
                subst V
                exact row_12_96
              · have he : V = 97 := by omega
                subst V
                exact row_12_97
            · by_cases h98_100 : V < 99
              · have he : V = 98 := by omega
                subst V
                exact row_12_98
              · have he : V = 99 := by omega
                subst V
                exact row_12_99
          · by_cases h100_104 : V < 102
            · by_cases h100_102 : V < 101
              · have he : V = 100 := by omega
                subst V
                exact row_12_100
              · have he : V = 101 := by omega
                subst V
                exact row_12_101
            · by_cases h102_104 : V < 103
              · have he : V = 102 := by omega
                subst V
                exact row_12_102
              · have he : V = 103 := by omega
                subst V
                exact row_12_103
        · by_cases h104_112 : V < 108
          · by_cases h104_108 : V < 106
            · by_cases h104_106 : V < 105
              · have he : V = 104 := by omega
                subst V
                exact row_12_104
              · have he : V = 105 := by omega
                subst V
                exact row_12_105
            · by_cases h106_108 : V < 107
              · have he : V = 106 := by omega
                subst V
                exact row_12_106
              · have he : V = 107 := by omega
                subst V
                exact row_12_107
          · by_cases h108_112 : V < 110
            · by_cases h108_110 : V < 109
              · have he : V = 108 := by omega
                subst V
                exact row_12_108
              · have he : V = 109 := by omega
                subst V
                exact row_12_109
            · by_cases h110_112 : V < 111
              · have he : V = 110 := by omega
                subst V
                exact row_12_110
              · have he : V = 111 := by omega
                subst V
                exact row_12_111
      · by_cases h112_128 : V < 120
        · by_cases h112_120 : V < 116
          · by_cases h112_116 : V < 114
            · by_cases h112_114 : V < 113
              · have he : V = 112 := by omega
                subst V
                exact row_12_112
              · have he : V = 113 := by omega
                subst V
                exact row_12_113
            · by_cases h114_116 : V < 115
              · have he : V = 114 := by omega
                subst V
                exact row_12_114
              · have he : V = 115 := by omega
                subst V
                exact row_12_115
          · by_cases h116_120 : V < 118
            · by_cases h116_118 : V < 117
              · have he : V = 116 := by omega
                subst V
                exact row_12_116
              · have he : V = 117 := by omega
                subst V
                exact row_12_117
            · by_cases h118_120 : V < 119
              · have he : V = 118 := by omega
                subst V
                exact row_12_118
              · have he : V = 119 := by omega
                subst V
                exact row_12_119
        · by_cases h120_128 : V < 124
          · by_cases h120_124 : V < 122
            · by_cases h120_122 : V < 121
              · have he : V = 120 := by omega
                subst V
                exact row_12_120
              · have he : V = 121 := by omega
                subst V
                exact row_12_121
            · by_cases h122_124 : V < 123
              · have he : V = 122 := by omega
                subst V
                exact row_12_122
              · have he : V = 123 := by omega
                subst V
                exact row_12_123
          · by_cases h124_128 : V < 126
            · by_cases h124_126 : V < 125
              · have he : V = 124 := by omega
                subst V
                exact row_12_124
              · have he : V = 125 := by omega
                subst V
                exact row_12_125
            · by_cases h126_128 : V < 127
              · have he : V = 126 := by omega
                subst V
                exact row_12_126
              · have he : V = 127 := by omega
                subst V
                exact row_12_127
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
