import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked19

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_20_0_0 : C 20 0 0 := by decide +kernel
theorem cell_20_0_1 : C 20 0 1 := by decide +kernel
theorem cell_20_0_2 : C 20 0 2 := by decide +kernel
theorem cell_20_0_3 : C 20 0 3 := by decide +kernel
theorem cell_20_0_4 : C 20 0 4 := by decide +kernel
theorem cell_20_0_5 : C 20 0 5 := by decide +kernel
theorem row_20_0 : ThresholdAt 20 0 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 0 0 cell_20_0_0
  | exact S 20 0 1 cell_20_0_1
  | exact S 20 0 2 cell_20_0_2
  | exact S 20 0 3 cell_20_0_3
  | exact S 20 0 4 cell_20_0_4
  | exact S 20 0 5 cell_20_0_5
theorem cell_20_1_0 : C 20 1 0 := by decide +kernel
theorem cell_20_1_1 : C 20 1 1 := by decide +kernel
theorem cell_20_1_2 : C 20 1 2 := by decide +kernel
theorem cell_20_1_3 : C 20 1 3 := by decide +kernel
theorem cell_20_1_4 : C 20 1 4 := by decide +kernel
theorem cell_20_1_5 : C 20 1 5 := by decide +kernel
theorem row_20_1 : ThresholdAt 20 1 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 1 0 cell_20_1_0
  | exact S 20 1 1 cell_20_1_1
  | exact S 20 1 2 cell_20_1_2
  | exact S 20 1 3 cell_20_1_3
  | exact S 20 1 4 cell_20_1_4
  | exact S 20 1 5 cell_20_1_5
theorem cell_20_2_0 : C 20 2 0 := by decide +kernel
theorem cell_20_2_1 : C 20 2 1 := by decide +kernel
theorem cell_20_2_2 : C 20 2 2 := by decide +kernel
theorem cell_20_2_3 : C 20 2 3 := by decide +kernel
theorem cell_20_2_4 : C 20 2 4 := by decide +kernel
theorem cell_20_2_5 : C 20 2 5 := by decide +kernel
theorem row_20_2 : ThresholdAt 20 2 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 2 0 cell_20_2_0
  | exact S 20 2 1 cell_20_2_1
  | exact S 20 2 2 cell_20_2_2
  | exact S 20 2 3 cell_20_2_3
  | exact S 20 2 4 cell_20_2_4
  | exact S 20 2 5 cell_20_2_5
theorem cell_20_3_0 : C 20 3 0 := by decide +kernel
theorem cell_20_3_1 : C 20 3 1 := by decide +kernel
theorem cell_20_3_2 : C 20 3 2 := by decide +kernel
theorem cell_20_3_3 : C 20 3 3 := by decide +kernel
theorem cell_20_3_4 : C 20 3 4 := by decide +kernel
theorem cell_20_3_5 : C 20 3 5 := by decide +kernel
theorem row_20_3 : ThresholdAt 20 3 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 3 0 cell_20_3_0
  | exact S 20 3 1 cell_20_3_1
  | exact S 20 3 2 cell_20_3_2
  | exact S 20 3 3 cell_20_3_3
  | exact S 20 3 4 cell_20_3_4
  | exact S 20 3 5 cell_20_3_5
theorem cell_20_4_0 : C 20 4 0 := by decide +kernel
theorem cell_20_4_1 : C 20 4 1 := by decide +kernel
theorem cell_20_4_2 : C 20 4 2 := by decide +kernel
theorem cell_20_4_3 : C 20 4 3 := by decide +kernel
theorem cell_20_4_4 : C 20 4 4 := by decide +kernel
theorem cell_20_4_5 : C 20 4 5 := by decide +kernel
theorem row_20_4 : ThresholdAt 20 4 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 4 0 cell_20_4_0
  | exact S 20 4 1 cell_20_4_1
  | exact S 20 4 2 cell_20_4_2
  | exact S 20 4 3 cell_20_4_3
  | exact S 20 4 4 cell_20_4_4
  | exact S 20 4 5 cell_20_4_5
theorem cell_20_5_0 : C 20 5 0 := by decide +kernel
theorem cell_20_5_1 : C 20 5 1 := by decide +kernel
theorem cell_20_5_2 : C 20 5 2 := by decide +kernel
theorem cell_20_5_3 : C 20 5 3 := by decide +kernel
theorem cell_20_5_4 : C 20 5 4 := by decide +kernel
theorem cell_20_5_5 : C 20 5 5 := by decide +kernel
theorem row_20_5 : ThresholdAt 20 5 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 5 0 cell_20_5_0
  | exact S 20 5 1 cell_20_5_1
  | exact S 20 5 2 cell_20_5_2
  | exact S 20 5 3 cell_20_5_3
  | exact S 20 5 4 cell_20_5_4
  | exact S 20 5 5 cell_20_5_5
theorem cell_20_6_0 : C 20 6 0 := by decide +kernel
theorem cell_20_6_1 : C 20 6 1 := by decide +kernel
theorem cell_20_6_2 : C 20 6 2 := by decide +kernel
theorem cell_20_6_3 : C 20 6 3 := by decide +kernel
theorem cell_20_6_4 : C 20 6 4 := by decide +kernel
theorem cell_20_6_5 : C 20 6 5 := by decide +kernel
theorem row_20_6 : ThresholdAt 20 6 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 6 0 cell_20_6_0
  | exact S 20 6 1 cell_20_6_1
  | exact S 20 6 2 cell_20_6_2
  | exact S 20 6 3 cell_20_6_3
  | exact S 20 6 4 cell_20_6_4
  | exact S 20 6 5 cell_20_6_5
theorem cell_20_7_0 : C 20 7 0 := by decide +kernel
theorem cell_20_7_1 : C 20 7 1 := by decide +kernel
theorem cell_20_7_2 : C 20 7 2 := by decide +kernel
theorem cell_20_7_3 : C 20 7 3 := by decide +kernel
theorem cell_20_7_4 : C 20 7 4 := by decide +kernel
theorem cell_20_7_5 : C 20 7 5 := by decide +kernel
theorem row_20_7 : ThresholdAt 20 7 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 7 0 cell_20_7_0
  | exact S 20 7 1 cell_20_7_1
  | exact S 20 7 2 cell_20_7_2
  | exact S 20 7 3 cell_20_7_3
  | exact S 20 7 4 cell_20_7_4
  | exact S 20 7 5 cell_20_7_5
theorem cell_20_8_0 : C 20 8 0 := by decide +kernel
theorem cell_20_8_1 : C 20 8 1 := by decide +kernel
theorem cell_20_8_2 : C 20 8 2 := by decide +kernel
theorem cell_20_8_3 : C 20 8 3 := by decide +kernel
theorem cell_20_8_4 : C 20 8 4 := by decide +kernel
theorem cell_20_8_5 : C 20 8 5 := by decide +kernel
theorem row_20_8 : ThresholdAt 20 8 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 8 0 cell_20_8_0
  | exact S 20 8 1 cell_20_8_1
  | exact S 20 8 2 cell_20_8_2
  | exact S 20 8 3 cell_20_8_3
  | exact S 20 8 4 cell_20_8_4
  | exact S 20 8 5 cell_20_8_5
theorem cell_20_9_0 : C 20 9 0 := by decide +kernel
theorem cell_20_9_1 : C 20 9 1 := by decide +kernel
theorem cell_20_9_2 : C 20 9 2 := by decide +kernel
theorem cell_20_9_3 : C 20 9 3 := by decide +kernel
theorem cell_20_9_4 : C 20 9 4 := by decide +kernel
theorem cell_20_9_5 : C 20 9 5 := by decide +kernel
theorem row_20_9 : ThresholdAt 20 9 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 9 0 cell_20_9_0
  | exact S 20 9 1 cell_20_9_1
  | exact S 20 9 2 cell_20_9_2
  | exact S 20 9 3 cell_20_9_3
  | exact S 20 9 4 cell_20_9_4
  | exact S 20 9 5 cell_20_9_5
theorem cell_20_10_0 : C 20 10 0 := by decide +kernel
theorem cell_20_10_1 : C 20 10 1 := by decide +kernel
theorem cell_20_10_2 : C 20 10 2 := by decide +kernel
theorem cell_20_10_3 : C 20 10 3 := by decide +kernel
theorem cell_20_10_4 : C 20 10 4 := by decide +kernel
theorem cell_20_10_5 : C 20 10 5 := by decide +kernel
theorem row_20_10 : ThresholdAt 20 10 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 10 0 cell_20_10_0
  | exact S 20 10 1 cell_20_10_1
  | exact S 20 10 2 cell_20_10_2
  | exact S 20 10 3 cell_20_10_3
  | exact S 20 10 4 cell_20_10_4
  | exact S 20 10 5 cell_20_10_5
theorem cell_20_11_0 : C 20 11 0 := by decide +kernel
theorem cell_20_11_1 : C 20 11 1 := by decide +kernel
theorem cell_20_11_2 : C 20 11 2 := by decide +kernel
theorem cell_20_11_3 : C 20 11 3 := by decide +kernel
theorem cell_20_11_4 : C 20 11 4 := by decide +kernel
theorem cell_20_11_5 : C 20 11 5 := by decide +kernel
theorem row_20_11 : ThresholdAt 20 11 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 11 0 cell_20_11_0
  | exact S 20 11 1 cell_20_11_1
  | exact S 20 11 2 cell_20_11_2
  | exact S 20 11 3 cell_20_11_3
  | exact S 20 11 4 cell_20_11_4
  | exact S 20 11 5 cell_20_11_5
theorem cell_20_12_0 : C 20 12 0 := by decide +kernel
theorem cell_20_12_1 : C 20 12 1 := by decide +kernel
theorem cell_20_12_2 : C 20 12 2 := by decide +kernel
theorem cell_20_12_3 : C 20 12 3 := by decide +kernel
theorem cell_20_12_4 : C 20 12 4 := by decide +kernel
theorem cell_20_12_5 : C 20 12 5 := by decide +kernel
theorem row_20_12 : ThresholdAt 20 12 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 12 0 cell_20_12_0
  | exact S 20 12 1 cell_20_12_1
  | exact S 20 12 2 cell_20_12_2
  | exact S 20 12 3 cell_20_12_3
  | exact S 20 12 4 cell_20_12_4
  | exact S 20 12 5 cell_20_12_5
theorem cell_20_13_0 : C 20 13 0 := by decide +kernel
theorem cell_20_13_1 : C 20 13 1 := by decide +kernel
theorem cell_20_13_2 : C 20 13 2 := by decide +kernel
theorem cell_20_13_3 : C 20 13 3 := by decide +kernel
theorem cell_20_13_4 : C 20 13 4 := by decide +kernel
theorem cell_20_13_5 : C 20 13 5 := by decide +kernel
theorem row_20_13 : ThresholdAt 20 13 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 13 0 cell_20_13_0
  | exact S 20 13 1 cell_20_13_1
  | exact S 20 13 2 cell_20_13_2
  | exact S 20 13 3 cell_20_13_3
  | exact S 20 13 4 cell_20_13_4
  | exact S 20 13 5 cell_20_13_5
theorem cell_20_14_0 : C 20 14 0 := by decide +kernel
theorem cell_20_14_1 : C 20 14 1 := by decide +kernel
theorem cell_20_14_2 : C 20 14 2 := by decide +kernel
theorem cell_20_14_3 : C 20 14 3 := by decide +kernel
theorem cell_20_14_4 : C 20 14 4 := by decide +kernel
theorem cell_20_14_5 : C 20 14 5 := by decide +kernel
theorem row_20_14 : ThresholdAt 20 14 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 14 0 cell_20_14_0
  | exact S 20 14 1 cell_20_14_1
  | exact S 20 14 2 cell_20_14_2
  | exact S 20 14 3 cell_20_14_3
  | exact S 20 14 4 cell_20_14_4
  | exact S 20 14 5 cell_20_14_5
theorem cell_20_15_0 : C 20 15 0 := by decide +kernel
theorem cell_20_15_1 : C 20 15 1 := by decide +kernel
theorem cell_20_15_2 : C 20 15 2 := by decide +kernel
theorem cell_20_15_3 : C 20 15 3 := by decide +kernel
theorem cell_20_15_4 : C 20 15 4 := by decide +kernel
theorem cell_20_15_5 : C 20 15 5 := by decide +kernel
theorem row_20_15 : ThresholdAt 20 15 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 15 0 cell_20_15_0
  | exact S 20 15 1 cell_20_15_1
  | exact S 20 15 2 cell_20_15_2
  | exact S 20 15 3 cell_20_15_3
  | exact S 20 15 4 cell_20_15_4
  | exact S 20 15 5 cell_20_15_5
theorem cell_20_16_0 : C 20 16 0 := by decide +kernel
theorem cell_20_16_1 : C 20 16 1 := by decide +kernel
theorem cell_20_16_2 : C 20 16 2 := by decide +kernel
theorem cell_20_16_3 : C 20 16 3 := by decide +kernel
theorem cell_20_16_4 : C 20 16 4 := by decide +kernel
theorem cell_20_16_5 : C 20 16 5 := by decide +kernel
theorem row_20_16 : ThresholdAt 20 16 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 16 0 cell_20_16_0
  | exact S 20 16 1 cell_20_16_1
  | exact S 20 16 2 cell_20_16_2
  | exact S 20 16 3 cell_20_16_3
  | exact S 20 16 4 cell_20_16_4
  | exact S 20 16 5 cell_20_16_5
theorem cell_20_17_0 : C 20 17 0 := by decide +kernel
theorem cell_20_17_1 : C 20 17 1 := by decide +kernel
theorem cell_20_17_2 : C 20 17 2 := by decide +kernel
theorem cell_20_17_3 : C 20 17 3 := by decide +kernel
theorem cell_20_17_4 : C 20 17 4 := by decide +kernel
theorem cell_20_17_5 : C 20 17 5 := by decide +kernel
theorem row_20_17 : ThresholdAt 20 17 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 17 0 cell_20_17_0
  | exact S 20 17 1 cell_20_17_1
  | exact S 20 17 2 cell_20_17_2
  | exact S 20 17 3 cell_20_17_3
  | exact S 20 17 4 cell_20_17_4
  | exact S 20 17 5 cell_20_17_5
theorem cell_20_18_0 : C 20 18 0 := by decide +kernel
theorem cell_20_18_1 : C 20 18 1 := by decide +kernel
theorem cell_20_18_2 : C 20 18 2 := by decide +kernel
theorem cell_20_18_3 : C 20 18 3 := by decide +kernel
theorem cell_20_18_4 : C 20 18 4 := by decide +kernel
theorem cell_20_18_5 : C 20 18 5 := by decide +kernel
theorem row_20_18 : ThresholdAt 20 18 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 18 0 cell_20_18_0
  | exact S 20 18 1 cell_20_18_1
  | exact S 20 18 2 cell_20_18_2
  | exact S 20 18 3 cell_20_18_3
  | exact S 20 18 4 cell_20_18_4
  | exact S 20 18 5 cell_20_18_5
theorem cell_20_19_0 : C 20 19 0 := by decide +kernel
theorem cell_20_19_1 : C 20 19 1 := by decide +kernel
theorem cell_20_19_2 : C 20 19 2 := by decide +kernel
theorem cell_20_19_3 : C 20 19 3 := by decide +kernel
theorem cell_20_19_4 : C 20 19 4 := by decide +kernel
theorem cell_20_19_5 : C 20 19 5 := by decide +kernel
theorem row_20_19 : ThresholdAt 20 19 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 19 0 cell_20_19_0
  | exact S 20 19 1 cell_20_19_1
  | exact S 20 19 2 cell_20_19_2
  | exact S 20 19 3 cell_20_19_3
  | exact S 20 19 4 cell_20_19_4
  | exact S 20 19 5 cell_20_19_5
theorem cell_20_20_0 : C 20 20 0 := by decide +kernel
theorem cell_20_20_1 : C 20 20 1 := by decide +kernel
theorem cell_20_20_2 : C 20 20 2 := by decide +kernel
theorem cell_20_20_3 : C 20 20 3 := by decide +kernel
theorem cell_20_20_4 : C 20 20 4 := by decide +kernel
theorem cell_20_20_5 : C 20 20 5 := by decide +kernel
theorem row_20_20 : ThresholdAt 20 20 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 20 0 cell_20_20_0
  | exact S 20 20 1 cell_20_20_1
  | exact S 20 20 2 cell_20_20_2
  | exact S 20 20 3 cell_20_20_3
  | exact S 20 20 4 cell_20_20_4
  | exact S 20 20 5 cell_20_20_5
theorem cell_20_21_0 : C 20 21 0 := by decide +kernel
theorem cell_20_21_1 : C 20 21 1 := by decide +kernel
theorem cell_20_21_2 : C 20 21 2 := by decide +kernel
theorem cell_20_21_3 : C 20 21 3 := by decide +kernel
theorem cell_20_21_4 : C 20 21 4 := by decide +kernel
theorem cell_20_21_5 : C 20 21 5 := by decide +kernel
theorem row_20_21 : ThresholdAt 20 21 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 21 0 cell_20_21_0
  | exact S 20 21 1 cell_20_21_1
  | exact S 20 21 2 cell_20_21_2
  | exact S 20 21 3 cell_20_21_3
  | exact S 20 21 4 cell_20_21_4
  | exact S 20 21 5 cell_20_21_5
theorem cell_20_22_0 : C 20 22 0 := by decide +kernel
theorem cell_20_22_1 : C 20 22 1 := by decide +kernel
theorem cell_20_22_2 : C 20 22 2 := by decide +kernel
theorem cell_20_22_3 : C 20 22 3 := by decide +kernel
theorem cell_20_22_4 : C 20 22 4 := by decide +kernel
theorem cell_20_22_5 : C 20 22 5 := by decide +kernel
theorem row_20_22 : ThresholdAt 20 22 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 22 0 cell_20_22_0
  | exact S 20 22 1 cell_20_22_1
  | exact S 20 22 2 cell_20_22_2
  | exact S 20 22 3 cell_20_22_3
  | exact S 20 22 4 cell_20_22_4
  | exact S 20 22 5 cell_20_22_5
theorem cell_20_23_0 : C 20 23 0 := by decide +kernel
theorem cell_20_23_1 : C 20 23 1 := by decide +kernel
theorem cell_20_23_2 : C 20 23 2 := by decide +kernel
theorem cell_20_23_3 : C 20 23 3 := by decide +kernel
theorem cell_20_23_4 : C 20 23 4 := by decide +kernel
theorem cell_20_23_5 : C 20 23 5 := by decide +kernel
theorem row_20_23 : ThresholdAt 20 23 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 23 0 cell_20_23_0
  | exact S 20 23 1 cell_20_23_1
  | exact S 20 23 2 cell_20_23_2
  | exact S 20 23 3 cell_20_23_3
  | exact S 20 23 4 cell_20_23_4
  | exact S 20 23 5 cell_20_23_5
theorem cell_20_24_0 : C 20 24 0 := by decide +kernel
theorem cell_20_24_1 : C 20 24 1 := by decide +kernel
theorem cell_20_24_2 : C 20 24 2 := by decide +kernel
theorem cell_20_24_3 : C 20 24 3 := by decide +kernel
theorem cell_20_24_4 : C 20 24 4 := by decide +kernel
theorem cell_20_24_5 : C 20 24 5 := by decide +kernel
theorem row_20_24 : ThresholdAt 20 24 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 24 0 cell_20_24_0
  | exact S 20 24 1 cell_20_24_1
  | exact S 20 24 2 cell_20_24_2
  | exact S 20 24 3 cell_20_24_3
  | exact S 20 24 4 cell_20_24_4
  | exact S 20 24 5 cell_20_24_5
theorem cell_20_25_0 : C 20 25 0 := by decide +kernel
theorem cell_20_25_1 : C 20 25 1 := by decide +kernel
theorem cell_20_25_2 : C 20 25 2 := by decide +kernel
theorem cell_20_25_3 : C 20 25 3 := by decide +kernel
theorem cell_20_25_4 : C 20 25 4 := by decide +kernel
theorem cell_20_25_5 : C 20 25 5 := by decide +kernel
theorem row_20_25 : ThresholdAt 20 25 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 25 0 cell_20_25_0
  | exact S 20 25 1 cell_20_25_1
  | exact S 20 25 2 cell_20_25_2
  | exact S 20 25 3 cell_20_25_3
  | exact S 20 25 4 cell_20_25_4
  | exact S 20 25 5 cell_20_25_5
theorem cell_20_26_0 : C 20 26 0 := by decide +kernel
theorem cell_20_26_1 : C 20 26 1 := by decide +kernel
theorem cell_20_26_2 : C 20 26 2 := by decide +kernel
theorem cell_20_26_3 : C 20 26 3 := by decide +kernel
theorem cell_20_26_4 : C 20 26 4 := by decide +kernel
theorem cell_20_26_5 : C 20 26 5 := by decide +kernel
theorem row_20_26 : ThresholdAt 20 26 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 26 0 cell_20_26_0
  | exact S 20 26 1 cell_20_26_1
  | exact S 20 26 2 cell_20_26_2
  | exact S 20 26 3 cell_20_26_3
  | exact S 20 26 4 cell_20_26_4
  | exact S 20 26 5 cell_20_26_5
theorem cell_20_27_0 : C 20 27 0 := by decide +kernel
theorem cell_20_27_1 : C 20 27 1 := by decide +kernel
theorem cell_20_27_2 : C 20 27 2 := by decide +kernel
theorem cell_20_27_3 : C 20 27 3 := by decide +kernel
theorem cell_20_27_4 : C 20 27 4 := by decide +kernel
theorem cell_20_27_5 : C 20 27 5 := by decide +kernel
theorem row_20_27 : ThresholdAt 20 27 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 27 0 cell_20_27_0
  | exact S 20 27 1 cell_20_27_1
  | exact S 20 27 2 cell_20_27_2
  | exact S 20 27 3 cell_20_27_3
  | exact S 20 27 4 cell_20_27_4
  | exact S 20 27 5 cell_20_27_5
theorem cell_20_28_0 : C 20 28 0 := by decide +kernel
theorem cell_20_28_1 : C 20 28 1 := by decide +kernel
theorem cell_20_28_2 : C 20 28 2 := by decide +kernel
theorem cell_20_28_3 : C 20 28 3 := by decide +kernel
theorem cell_20_28_4 : C 20 28 4 := by decide +kernel
theorem cell_20_28_5 : C 20 28 5 := by decide +kernel
theorem row_20_28 : ThresholdAt 20 28 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 28 0 cell_20_28_0
  | exact S 20 28 1 cell_20_28_1
  | exact S 20 28 2 cell_20_28_2
  | exact S 20 28 3 cell_20_28_3
  | exact S 20 28 4 cell_20_28_4
  | exact S 20 28 5 cell_20_28_5
theorem cell_20_29_0 : C 20 29 0 := by decide +kernel
theorem cell_20_29_1 : C 20 29 1 := by decide +kernel
theorem cell_20_29_2 : C 20 29 2 := by decide +kernel
theorem cell_20_29_3 : C 20 29 3 := by decide +kernel
theorem cell_20_29_4 : C 20 29 4 := by decide +kernel
theorem cell_20_29_5 : C 20 29 5 := by decide +kernel
theorem row_20_29 : ThresholdAt 20 29 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 29 0 cell_20_29_0
  | exact S 20 29 1 cell_20_29_1
  | exact S 20 29 2 cell_20_29_2
  | exact S 20 29 3 cell_20_29_3
  | exact S 20 29 4 cell_20_29_4
  | exact S 20 29 5 cell_20_29_5
theorem cell_20_30_0 : C 20 30 0 := by decide +kernel
theorem cell_20_30_1 : C 20 30 1 := by decide +kernel
theorem cell_20_30_2 : C 20 30 2 := by decide +kernel
theorem cell_20_30_3 : C 20 30 3 := by decide +kernel
theorem cell_20_30_4 : C 20 30 4 := by decide +kernel
theorem cell_20_30_5 : C 20 30 5 := by decide +kernel
theorem row_20_30 : ThresholdAt 20 30 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 30 0 cell_20_30_0
  | exact S 20 30 1 cell_20_30_1
  | exact S 20 30 2 cell_20_30_2
  | exact S 20 30 3 cell_20_30_3
  | exact S 20 30 4 cell_20_30_4
  | exact S 20 30 5 cell_20_30_5
theorem cell_20_31_0 : C 20 31 0 := by decide +kernel
theorem cell_20_31_1 : C 20 31 1 := by decide +kernel
theorem cell_20_31_2 : C 20 31 2 := by decide +kernel
theorem cell_20_31_3 : C 20 31 3 := by decide +kernel
theorem cell_20_31_4 : C 20 31 4 := by decide +kernel
theorem cell_20_31_5 : C 20 31 5 := by decide +kernel
theorem row_20_31 : ThresholdAt 20 31 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 31 0 cell_20_31_0
  | exact S 20 31 1 cell_20_31_1
  | exact S 20 31 2 cell_20_31_2
  | exact S 20 31 3 cell_20_31_3
  | exact S 20 31 4 cell_20_31_4
  | exact S 20 31 5 cell_20_31_5
theorem cell_20_32_0 : C 20 32 0 := by decide +kernel
theorem cell_20_32_1 : C 20 32 1 := by decide +kernel
theorem cell_20_32_2 : C 20 32 2 := by decide +kernel
theorem cell_20_32_3 : C 20 32 3 := by decide +kernel
theorem cell_20_32_4 : C 20 32 4 := by decide +kernel
theorem cell_20_32_5 : C 20 32 5 := by decide +kernel
theorem row_20_32 : ThresholdAt 20 32 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 32 0 cell_20_32_0
  | exact S 20 32 1 cell_20_32_1
  | exact S 20 32 2 cell_20_32_2
  | exact S 20 32 3 cell_20_32_3
  | exact S 20 32 4 cell_20_32_4
  | exact S 20 32 5 cell_20_32_5
theorem cell_20_33_0 : C 20 33 0 := by decide +kernel
theorem cell_20_33_1 : C 20 33 1 := by decide +kernel
theorem cell_20_33_2 : C 20 33 2 := by decide +kernel
theorem cell_20_33_3 : C 20 33 3 := by decide +kernel
theorem cell_20_33_4 : C 20 33 4 := by decide +kernel
theorem cell_20_33_5 : C 20 33 5 := by decide +kernel
theorem row_20_33 : ThresholdAt 20 33 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 33 0 cell_20_33_0
  | exact S 20 33 1 cell_20_33_1
  | exact S 20 33 2 cell_20_33_2
  | exact S 20 33 3 cell_20_33_3
  | exact S 20 33 4 cell_20_33_4
  | exact S 20 33 5 cell_20_33_5
theorem cell_20_34_0 : C 20 34 0 := by decide +kernel
theorem cell_20_34_1 : C 20 34 1 := by decide +kernel
theorem cell_20_34_2 : C 20 34 2 := by decide +kernel
theorem cell_20_34_3 : C 20 34 3 := by decide +kernel
theorem cell_20_34_4 : C 20 34 4 := by decide +kernel
theorem cell_20_34_5 : C 20 34 5 := by decide +kernel
theorem row_20_34 : ThresholdAt 20 34 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 34 0 cell_20_34_0
  | exact S 20 34 1 cell_20_34_1
  | exact S 20 34 2 cell_20_34_2
  | exact S 20 34 3 cell_20_34_3
  | exact S 20 34 4 cell_20_34_4
  | exact S 20 34 5 cell_20_34_5
theorem cell_20_35_0 : C 20 35 0 := by decide +kernel
theorem cell_20_35_1 : C 20 35 1 := by decide +kernel
theorem cell_20_35_2 : C 20 35 2 := by decide +kernel
theorem cell_20_35_3 : C 20 35 3 := by decide +kernel
theorem cell_20_35_4 : C 20 35 4 := by decide +kernel
theorem cell_20_35_5 : C 20 35 5 := by decide +kernel
theorem row_20_35 : ThresholdAt 20 35 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 35 0 cell_20_35_0
  | exact S 20 35 1 cell_20_35_1
  | exact S 20 35 2 cell_20_35_2
  | exact S 20 35 3 cell_20_35_3
  | exact S 20 35 4 cell_20_35_4
  | exact S 20 35 5 cell_20_35_5
theorem cell_20_36_0 : C 20 36 0 := by decide +kernel
theorem cell_20_36_1 : C 20 36 1 := by decide +kernel
theorem cell_20_36_2 : C 20 36 2 := by decide +kernel
theorem cell_20_36_3 : C 20 36 3 := by decide +kernel
theorem cell_20_36_4 : C 20 36 4 := by decide +kernel
theorem cell_20_36_5 : C 20 36 5 := by decide +kernel
theorem row_20_36 : ThresholdAt 20 36 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 36 0 cell_20_36_0
  | exact S 20 36 1 cell_20_36_1
  | exact S 20 36 2 cell_20_36_2
  | exact S 20 36 3 cell_20_36_3
  | exact S 20 36 4 cell_20_36_4
  | exact S 20 36 5 cell_20_36_5
theorem cell_20_37_0 : C 20 37 0 := by decide +kernel
theorem cell_20_37_1 : C 20 37 1 := by decide +kernel
theorem cell_20_37_2 : C 20 37 2 := by decide +kernel
theorem cell_20_37_3 : C 20 37 3 := by decide +kernel
theorem cell_20_37_4 : C 20 37 4 := by decide +kernel
theorem cell_20_37_5 : C 20 37 5 := by decide +kernel
theorem row_20_37 : ThresholdAt 20 37 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 37 0 cell_20_37_0
  | exact S 20 37 1 cell_20_37_1
  | exact S 20 37 2 cell_20_37_2
  | exact S 20 37 3 cell_20_37_3
  | exact S 20 37 4 cell_20_37_4
  | exact S 20 37 5 cell_20_37_5
theorem cell_20_38_0 : C 20 38 0 := by decide +kernel
theorem cell_20_38_1 : C 20 38 1 := by decide +kernel
theorem cell_20_38_2 : C 20 38 2 := by decide +kernel
theorem cell_20_38_3 : C 20 38 3 := by decide +kernel
theorem cell_20_38_4 : C 20 38 4 := by decide +kernel
theorem cell_20_38_5 : C 20 38 5 := by decide +kernel
theorem row_20_38 : ThresholdAt 20 38 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 38 0 cell_20_38_0
  | exact S 20 38 1 cell_20_38_1
  | exact S 20 38 2 cell_20_38_2
  | exact S 20 38 3 cell_20_38_3
  | exact S 20 38 4 cell_20_38_4
  | exact S 20 38 5 cell_20_38_5
theorem cell_20_39_0 : C 20 39 0 := by decide +kernel
theorem cell_20_39_1 : C 20 39 1 := by decide +kernel
theorem cell_20_39_2 : C 20 39 2 := by decide +kernel
theorem cell_20_39_3 : C 20 39 3 := by decide +kernel
theorem cell_20_39_4 : C 20 39 4 := by decide +kernel
theorem cell_20_39_5 : C 20 39 5 := by decide +kernel
theorem row_20_39 : ThresholdAt 20 39 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 39 0 cell_20_39_0
  | exact S 20 39 1 cell_20_39_1
  | exact S 20 39 2 cell_20_39_2
  | exact S 20 39 3 cell_20_39_3
  | exact S 20 39 4 cell_20_39_4
  | exact S 20 39 5 cell_20_39_5
theorem cell_20_40_0 : C 20 40 0 := by decide +kernel
theorem cell_20_40_1 : C 20 40 1 := by decide +kernel
theorem cell_20_40_2 : C 20 40 2 := by decide +kernel
theorem cell_20_40_3 : C 20 40 3 := by decide +kernel
theorem cell_20_40_4 : C 20 40 4 := by decide +kernel
theorem cell_20_40_5 : C 20 40 5 := by decide +kernel
theorem row_20_40 : ThresholdAt 20 40 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 40 0 cell_20_40_0
  | exact S 20 40 1 cell_20_40_1
  | exact S 20 40 2 cell_20_40_2
  | exact S 20 40 3 cell_20_40_3
  | exact S 20 40 4 cell_20_40_4
  | exact S 20 40 5 cell_20_40_5
theorem cell_20_41_0 : C 20 41 0 := by decide +kernel
theorem cell_20_41_1 : C 20 41 1 := by decide +kernel
theorem cell_20_41_2 : C 20 41 2 := by decide +kernel
theorem cell_20_41_3 : C 20 41 3 := by decide +kernel
theorem cell_20_41_4 : C 20 41 4 := by decide +kernel
theorem cell_20_41_5 : C 20 41 5 := by decide +kernel
theorem row_20_41 : ThresholdAt 20 41 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 41 0 cell_20_41_0
  | exact S 20 41 1 cell_20_41_1
  | exact S 20 41 2 cell_20_41_2
  | exact S 20 41 3 cell_20_41_3
  | exact S 20 41 4 cell_20_41_4
  | exact S 20 41 5 cell_20_41_5
theorem cell_20_42_0 : C 20 42 0 := by decide +kernel
theorem cell_20_42_1 : C 20 42 1 := by decide +kernel
theorem cell_20_42_2 : C 20 42 2 := by decide +kernel
theorem cell_20_42_3 : C 20 42 3 := by decide +kernel
theorem cell_20_42_4 : C 20 42 4 := by decide +kernel
theorem cell_20_42_5 : C 20 42 5 := by decide +kernel
theorem row_20_42 : ThresholdAt 20 42 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 42 0 cell_20_42_0
  | exact S 20 42 1 cell_20_42_1
  | exact S 20 42 2 cell_20_42_2
  | exact S 20 42 3 cell_20_42_3
  | exact S 20 42 4 cell_20_42_4
  | exact S 20 42 5 cell_20_42_5
theorem cell_20_43_0 : C 20 43 0 := by decide +kernel
theorem cell_20_43_1 : C 20 43 1 := by decide +kernel
theorem cell_20_43_2 : C 20 43 2 := by decide +kernel
theorem cell_20_43_3 : C 20 43 3 := by decide +kernel
theorem cell_20_43_4 : C 20 43 4 := by decide +kernel
theorem cell_20_43_5 : C 20 43 5 := by decide +kernel
theorem row_20_43 : ThresholdAt 20 43 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 43 0 cell_20_43_0
  | exact S 20 43 1 cell_20_43_1
  | exact S 20 43 2 cell_20_43_2
  | exact S 20 43 3 cell_20_43_3
  | exact S 20 43 4 cell_20_43_4
  | exact S 20 43 5 cell_20_43_5
theorem cell_20_44_0 : C 20 44 0 := by decide +kernel
theorem cell_20_44_1 : C 20 44 1 := by decide +kernel
theorem cell_20_44_2 : C 20 44 2 := by decide +kernel
theorem cell_20_44_3 : C 20 44 3 := by decide +kernel
theorem cell_20_44_4 : C 20 44 4 := by decide +kernel
theorem cell_20_44_5 : C 20 44 5 := by decide +kernel
theorem row_20_44 : ThresholdAt 20 44 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 44 0 cell_20_44_0
  | exact S 20 44 1 cell_20_44_1
  | exact S 20 44 2 cell_20_44_2
  | exact S 20 44 3 cell_20_44_3
  | exact S 20 44 4 cell_20_44_4
  | exact S 20 44 5 cell_20_44_5
theorem cell_20_45_0 : C 20 45 0 := by decide +kernel
theorem cell_20_45_1 : C 20 45 1 := by decide +kernel
theorem cell_20_45_2 : C 20 45 2 := by decide +kernel
theorem cell_20_45_3 : C 20 45 3 := by decide +kernel
theorem cell_20_45_4 : C 20 45 4 := by decide +kernel
theorem cell_20_45_5 : C 20 45 5 := by decide +kernel
theorem row_20_45 : ThresholdAt 20 45 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 45 0 cell_20_45_0
  | exact S 20 45 1 cell_20_45_1
  | exact S 20 45 2 cell_20_45_2
  | exact S 20 45 3 cell_20_45_3
  | exact S 20 45 4 cell_20_45_4
  | exact S 20 45 5 cell_20_45_5
theorem cell_20_46_0 : C 20 46 0 := by decide +kernel
theorem cell_20_46_1 : C 20 46 1 := by decide +kernel
theorem cell_20_46_2 : C 20 46 2 := by decide +kernel
theorem cell_20_46_3 : C 20 46 3 := by decide +kernel
theorem cell_20_46_4 : C 20 46 4 := by decide +kernel
theorem cell_20_46_5 : C 20 46 5 := by decide +kernel
theorem row_20_46 : ThresholdAt 20 46 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 46 0 cell_20_46_0
  | exact S 20 46 1 cell_20_46_1
  | exact S 20 46 2 cell_20_46_2
  | exact S 20 46 3 cell_20_46_3
  | exact S 20 46 4 cell_20_46_4
  | exact S 20 46 5 cell_20_46_5
theorem cell_20_47_0 : C 20 47 0 := by decide +kernel
theorem cell_20_47_1 : C 20 47 1 := by decide +kernel
theorem cell_20_47_2 : C 20 47 2 := by decide +kernel
theorem cell_20_47_3 : C 20 47 3 := by decide +kernel
theorem cell_20_47_4 : C 20 47 4 := by decide +kernel
theorem cell_20_47_5 : C 20 47 5 := by decide +kernel
theorem row_20_47 : ThresholdAt 20 47 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 47 0 cell_20_47_0
  | exact S 20 47 1 cell_20_47_1
  | exact S 20 47 2 cell_20_47_2
  | exact S 20 47 3 cell_20_47_3
  | exact S 20 47 4 cell_20_47_4
  | exact S 20 47 5 cell_20_47_5
theorem cell_20_48_0 : C 20 48 0 := by decide +kernel
theorem cell_20_48_1 : C 20 48 1 := by decide +kernel
theorem cell_20_48_2 : C 20 48 2 := by decide +kernel
theorem cell_20_48_3 : C 20 48 3 := by decide +kernel
theorem cell_20_48_4 : C 20 48 4 := by decide +kernel
theorem cell_20_48_5 : C 20 48 5 := by decide +kernel
theorem row_20_48 : ThresholdAt 20 48 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 48 0 cell_20_48_0
  | exact S 20 48 1 cell_20_48_1
  | exact S 20 48 2 cell_20_48_2
  | exact S 20 48 3 cell_20_48_3
  | exact S 20 48 4 cell_20_48_4
  | exact S 20 48 5 cell_20_48_5
theorem cell_20_49_0 : C 20 49 0 := by decide +kernel
theorem cell_20_49_1 : C 20 49 1 := by decide +kernel
theorem cell_20_49_2 : C 20 49 2 := by decide +kernel
theorem cell_20_49_3 : C 20 49 3 := by decide +kernel
theorem cell_20_49_4 : C 20 49 4 := by decide +kernel
theorem cell_20_49_5 : C 20 49 5 := by decide +kernel
theorem row_20_49 : ThresholdAt 20 49 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 49 0 cell_20_49_0
  | exact S 20 49 1 cell_20_49_1
  | exact S 20 49 2 cell_20_49_2
  | exact S 20 49 3 cell_20_49_3
  | exact S 20 49 4 cell_20_49_4
  | exact S 20 49 5 cell_20_49_5
theorem cell_20_50_0 : C 20 50 0 := by decide +kernel
theorem cell_20_50_1 : C 20 50 1 := by decide +kernel
theorem cell_20_50_2 : C 20 50 2 := by decide +kernel
theorem cell_20_50_3 : C 20 50 3 := by decide +kernel
theorem cell_20_50_4 : C 20 50 4 := by decide +kernel
theorem cell_20_50_5 : C 20 50 5 := by decide +kernel
theorem row_20_50 : ThresholdAt 20 50 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 50 0 cell_20_50_0
  | exact S 20 50 1 cell_20_50_1
  | exact S 20 50 2 cell_20_50_2
  | exact S 20 50 3 cell_20_50_3
  | exact S 20 50 4 cell_20_50_4
  | exact S 20 50 5 cell_20_50_5
theorem cell_20_51_0 : C 20 51 0 := by decide +kernel
theorem cell_20_51_1 : C 20 51 1 := by decide +kernel
theorem cell_20_51_2 : C 20 51 2 := by decide +kernel
theorem cell_20_51_3 : C 20 51 3 := by decide +kernel
theorem cell_20_51_4 : C 20 51 4 := by decide +kernel
theorem cell_20_51_5 : C 20 51 5 := by decide +kernel
theorem row_20_51 : ThresholdAt 20 51 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 51 0 cell_20_51_0
  | exact S 20 51 1 cell_20_51_1
  | exact S 20 51 2 cell_20_51_2
  | exact S 20 51 3 cell_20_51_3
  | exact S 20 51 4 cell_20_51_4
  | exact S 20 51 5 cell_20_51_5
theorem cell_20_52_0 : C 20 52 0 := by decide +kernel
theorem cell_20_52_1 : C 20 52 1 := by decide +kernel
theorem cell_20_52_2 : C 20 52 2 := by decide +kernel
theorem cell_20_52_3 : C 20 52 3 := by decide +kernel
theorem cell_20_52_4 : C 20 52 4 := by decide +kernel
theorem cell_20_52_5 : C 20 52 5 := by decide +kernel
theorem row_20_52 : ThresholdAt 20 52 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 52 0 cell_20_52_0
  | exact S 20 52 1 cell_20_52_1
  | exact S 20 52 2 cell_20_52_2
  | exact S 20 52 3 cell_20_52_3
  | exact S 20 52 4 cell_20_52_4
  | exact S 20 52 5 cell_20_52_5
theorem cell_20_53_0 : C 20 53 0 := by decide +kernel
theorem cell_20_53_1 : C 20 53 1 := by decide +kernel
theorem cell_20_53_2 : C 20 53 2 := by decide +kernel
theorem cell_20_53_3 : C 20 53 3 := by decide +kernel
theorem cell_20_53_4 : C 20 53 4 := by decide +kernel
theorem cell_20_53_5 : C 20 53 5 := by decide +kernel
theorem row_20_53 : ThresholdAt 20 53 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 53 0 cell_20_53_0
  | exact S 20 53 1 cell_20_53_1
  | exact S 20 53 2 cell_20_53_2
  | exact S 20 53 3 cell_20_53_3
  | exact S 20 53 4 cell_20_53_4
  | exact S 20 53 5 cell_20_53_5
theorem cell_20_54_0 : C 20 54 0 := by decide +kernel
theorem cell_20_54_1 : C 20 54 1 := by decide +kernel
theorem cell_20_54_2 : C 20 54 2 := by decide +kernel
theorem cell_20_54_3 : C 20 54 3 := by decide +kernel
theorem cell_20_54_4 : C 20 54 4 := by decide +kernel
theorem cell_20_54_5 : C 20 54 5 := by decide +kernel
theorem row_20_54 : ThresholdAt 20 54 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 54 0 cell_20_54_0
  | exact S 20 54 1 cell_20_54_1
  | exact S 20 54 2 cell_20_54_2
  | exact S 20 54 3 cell_20_54_3
  | exact S 20 54 4 cell_20_54_4
  | exact S 20 54 5 cell_20_54_5
theorem cell_20_55_0 : C 20 55 0 := by decide +kernel
theorem cell_20_55_1 : C 20 55 1 := by decide +kernel
theorem cell_20_55_2 : C 20 55 2 := by decide +kernel
theorem cell_20_55_3 : C 20 55 3 := by decide +kernel
theorem cell_20_55_4 : C 20 55 4 := by decide +kernel
theorem cell_20_55_5 : C 20 55 5 := by decide +kernel
theorem row_20_55 : ThresholdAt 20 55 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 55 0 cell_20_55_0
  | exact S 20 55 1 cell_20_55_1
  | exact S 20 55 2 cell_20_55_2
  | exact S 20 55 3 cell_20_55_3
  | exact S 20 55 4 cell_20_55_4
  | exact S 20 55 5 cell_20_55_5
theorem cell_20_56_0 : C 20 56 0 := by decide +kernel
theorem cell_20_56_1 : C 20 56 1 := by decide +kernel
theorem cell_20_56_2 : C 20 56 2 := by decide +kernel
theorem cell_20_56_3 : C 20 56 3 := by decide +kernel
theorem cell_20_56_4 : C 20 56 4 := by decide +kernel
theorem cell_20_56_5 : C 20 56 5 := by decide +kernel
theorem row_20_56 : ThresholdAt 20 56 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 56 0 cell_20_56_0
  | exact S 20 56 1 cell_20_56_1
  | exact S 20 56 2 cell_20_56_2
  | exact S 20 56 3 cell_20_56_3
  | exact S 20 56 4 cell_20_56_4
  | exact S 20 56 5 cell_20_56_5
theorem cell_20_57_0 : C 20 57 0 := by decide +kernel
theorem cell_20_57_1 : C 20 57 1 := by decide +kernel
theorem cell_20_57_2 : C 20 57 2 := by decide +kernel
theorem cell_20_57_3 : C 20 57 3 := by decide +kernel
theorem cell_20_57_4 : C 20 57 4 := by decide +kernel
theorem cell_20_57_5 : C 20 57 5 := by decide +kernel
theorem row_20_57 : ThresholdAt 20 57 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 57 0 cell_20_57_0
  | exact S 20 57 1 cell_20_57_1
  | exact S 20 57 2 cell_20_57_2
  | exact S 20 57 3 cell_20_57_3
  | exact S 20 57 4 cell_20_57_4
  | exact S 20 57 5 cell_20_57_5
theorem cell_20_58_0 : C 20 58 0 := by decide +kernel
theorem cell_20_58_1 : C 20 58 1 := by decide +kernel
theorem cell_20_58_2 : C 20 58 2 := by decide +kernel
theorem cell_20_58_3 : C 20 58 3 := by decide +kernel
theorem cell_20_58_4 : C 20 58 4 := by decide +kernel
theorem cell_20_58_5 : C 20 58 5 := by decide +kernel
theorem row_20_58 : ThresholdAt 20 58 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 58 0 cell_20_58_0
  | exact S 20 58 1 cell_20_58_1
  | exact S 20 58 2 cell_20_58_2
  | exact S 20 58 3 cell_20_58_3
  | exact S 20 58 4 cell_20_58_4
  | exact S 20 58 5 cell_20_58_5
theorem cell_20_59_0 : C 20 59 0 := by decide +kernel
theorem cell_20_59_1 : C 20 59 1 := by decide +kernel
theorem cell_20_59_2 : C 20 59 2 := by decide +kernel
theorem cell_20_59_3 : C 20 59 3 := by decide +kernel
theorem cell_20_59_4 : C 20 59 4 := by decide +kernel
theorem cell_20_59_5 : C 20 59 5 := by decide +kernel
theorem row_20_59 : ThresholdAt 20 59 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 59 0 cell_20_59_0
  | exact S 20 59 1 cell_20_59_1
  | exact S 20 59 2 cell_20_59_2
  | exact S 20 59 3 cell_20_59_3
  | exact S 20 59 4 cell_20_59_4
  | exact S 20 59 5 cell_20_59_5
theorem cell_20_60_0 : C 20 60 0 := by decide +kernel
theorem cell_20_60_1 : C 20 60 1 := by decide +kernel
theorem cell_20_60_2 : C 20 60 2 := by decide +kernel
theorem cell_20_60_3 : C 20 60 3 := by decide +kernel
theorem cell_20_60_4 : C 20 60 4 := by decide +kernel
theorem cell_20_60_5 : C 20 60 5 := by decide +kernel
theorem row_20_60 : ThresholdAt 20 60 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 60 0 cell_20_60_0
  | exact S 20 60 1 cell_20_60_1
  | exact S 20 60 2 cell_20_60_2
  | exact S 20 60 3 cell_20_60_3
  | exact S 20 60 4 cell_20_60_4
  | exact S 20 60 5 cell_20_60_5
theorem cell_20_61_0 : C 20 61 0 := by decide +kernel
theorem cell_20_61_1 : C 20 61 1 := by decide +kernel
theorem cell_20_61_2 : C 20 61 2 := by decide +kernel
theorem cell_20_61_3 : C 20 61 3 := by decide +kernel
theorem cell_20_61_4 : C 20 61 4 := by decide +kernel
theorem cell_20_61_5 : C 20 61 5 := by decide +kernel
theorem row_20_61 : ThresholdAt 20 61 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 61 0 cell_20_61_0
  | exact S 20 61 1 cell_20_61_1
  | exact S 20 61 2 cell_20_61_2
  | exact S 20 61 3 cell_20_61_3
  | exact S 20 61 4 cell_20_61_4
  | exact S 20 61 5 cell_20_61_5
theorem cell_20_62_0 : C 20 62 0 := by decide +kernel
theorem cell_20_62_1 : C 20 62 1 := by decide +kernel
theorem cell_20_62_2 : C 20 62 2 := by decide +kernel
theorem cell_20_62_3 : C 20 62 3 := by decide +kernel
theorem cell_20_62_4 : C 20 62 4 := by decide +kernel
theorem cell_20_62_5 : C 20 62 5 := by decide +kernel
theorem row_20_62 : ThresholdAt 20 62 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 62 0 cell_20_62_0
  | exact S 20 62 1 cell_20_62_1
  | exact S 20 62 2 cell_20_62_2
  | exact S 20 62 3 cell_20_62_3
  | exact S 20 62 4 cell_20_62_4
  | exact S 20 62 5 cell_20_62_5
theorem cell_20_63_0 : C 20 63 0 := by decide +kernel
theorem cell_20_63_1 : C 20 63 1 := by decide +kernel
theorem cell_20_63_2 : C 20 63 2 := by decide +kernel
theorem cell_20_63_3 : C 20 63 3 := by decide +kernel
theorem cell_20_63_4 : C 20 63 4 := by decide +kernel
theorem cell_20_63_5 : C 20 63 5 := by decide +kernel
theorem row_20_63 : ThresholdAt 20 63 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 63 0 cell_20_63_0
  | exact S 20 63 1 cell_20_63_1
  | exact S 20 63 2 cell_20_63_2
  | exact S 20 63 3 cell_20_63_3
  | exact S 20 63 4 cell_20_63_4
  | exact S 20 63 5 cell_20_63_5
theorem cell_20_64_0 : C 20 64 0 := by decide +kernel
theorem cell_20_64_1 : C 20 64 1 := by decide +kernel
theorem cell_20_64_2 : C 20 64 2 := by decide +kernel
theorem cell_20_64_3 : C 20 64 3 := by decide +kernel
theorem cell_20_64_4 : C 20 64 4 := by decide +kernel
theorem cell_20_64_5 : C 20 64 5 := by decide +kernel
theorem row_20_64 : ThresholdAt 20 64 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 64 0 cell_20_64_0
  | exact S 20 64 1 cell_20_64_1
  | exact S 20 64 2 cell_20_64_2
  | exact S 20 64 3 cell_20_64_3
  | exact S 20 64 4 cell_20_64_4
  | exact S 20 64 5 cell_20_64_5
theorem cell_20_65_0 : C 20 65 0 := by decide +kernel
theorem cell_20_65_1 : C 20 65 1 := by decide +kernel
theorem cell_20_65_2 : C 20 65 2 := by decide +kernel
theorem cell_20_65_3 : C 20 65 3 := by decide +kernel
theorem cell_20_65_4 : C 20 65 4 := by decide +kernel
theorem cell_20_65_5 : C 20 65 5 := by decide +kernel
theorem row_20_65 : ThresholdAt 20 65 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 65 0 cell_20_65_0
  | exact S 20 65 1 cell_20_65_1
  | exact S 20 65 2 cell_20_65_2
  | exact S 20 65 3 cell_20_65_3
  | exact S 20 65 4 cell_20_65_4
  | exact S 20 65 5 cell_20_65_5
theorem cell_20_66_0 : C 20 66 0 := by decide +kernel
theorem cell_20_66_1 : C 20 66 1 := by decide +kernel
theorem cell_20_66_2 : C 20 66 2 := by decide +kernel
theorem cell_20_66_3 : C 20 66 3 := by decide +kernel
theorem cell_20_66_4 : C 20 66 4 := by decide +kernel
theorem cell_20_66_5 : C 20 66 5 := by decide +kernel
theorem row_20_66 : ThresholdAt 20 66 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 66 0 cell_20_66_0
  | exact S 20 66 1 cell_20_66_1
  | exact S 20 66 2 cell_20_66_2
  | exact S 20 66 3 cell_20_66_3
  | exact S 20 66 4 cell_20_66_4
  | exact S 20 66 5 cell_20_66_5
theorem cell_20_67_0 : C 20 67 0 := by decide +kernel
theorem cell_20_67_1 : C 20 67 1 := by decide +kernel
theorem cell_20_67_2 : C 20 67 2 := by decide +kernel
theorem cell_20_67_3 : C 20 67 3 := by decide +kernel
theorem cell_20_67_4 : C 20 67 4 := by decide +kernel
theorem cell_20_67_5 : C 20 67 5 := by decide +kernel
theorem row_20_67 : ThresholdAt 20 67 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 67 0 cell_20_67_0
  | exact S 20 67 1 cell_20_67_1
  | exact S 20 67 2 cell_20_67_2
  | exact S 20 67 3 cell_20_67_3
  | exact S 20 67 4 cell_20_67_4
  | exact S 20 67 5 cell_20_67_5
theorem cell_20_68_0 : C 20 68 0 := by decide +kernel
theorem cell_20_68_1 : C 20 68 1 := by decide +kernel
theorem cell_20_68_2 : C 20 68 2 := by decide +kernel
theorem cell_20_68_3 : C 20 68 3 := by decide +kernel
theorem cell_20_68_4 : C 20 68 4 := by decide +kernel
theorem cell_20_68_5 : C 20 68 5 := by decide +kernel
theorem row_20_68 : ThresholdAt 20 68 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 68 0 cell_20_68_0
  | exact S 20 68 1 cell_20_68_1
  | exact S 20 68 2 cell_20_68_2
  | exact S 20 68 3 cell_20_68_3
  | exact S 20 68 4 cell_20_68_4
  | exact S 20 68 5 cell_20_68_5
theorem cell_20_69_0 : C 20 69 0 := by decide +kernel
theorem cell_20_69_1 : C 20 69 1 := by decide +kernel
theorem cell_20_69_2 : C 20 69 2 := by decide +kernel
theorem cell_20_69_3 : C 20 69 3 := by decide +kernel
theorem cell_20_69_4 : C 20 69 4 := by decide +kernel
theorem cell_20_69_5 : C 20 69 5 := by decide +kernel
theorem row_20_69 : ThresholdAt 20 69 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 69 0 cell_20_69_0
  | exact S 20 69 1 cell_20_69_1
  | exact S 20 69 2 cell_20_69_2
  | exact S 20 69 3 cell_20_69_3
  | exact S 20 69 4 cell_20_69_4
  | exact S 20 69 5 cell_20_69_5
theorem cell_20_70_0 : C 20 70 0 := by decide +kernel
theorem cell_20_70_1 : C 20 70 1 := by decide +kernel
theorem cell_20_70_2 : C 20 70 2 := by decide +kernel
theorem cell_20_70_3 : C 20 70 3 := by decide +kernel
theorem cell_20_70_4 : C 20 70 4 := by decide +kernel
theorem cell_20_70_5 : C 20 70 5 := by decide +kernel
theorem row_20_70 : ThresholdAt 20 70 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 70 0 cell_20_70_0
  | exact S 20 70 1 cell_20_70_1
  | exact S 20 70 2 cell_20_70_2
  | exact S 20 70 3 cell_20_70_3
  | exact S 20 70 4 cell_20_70_4
  | exact S 20 70 5 cell_20_70_5
theorem cell_20_71_0 : C 20 71 0 := by decide +kernel
theorem cell_20_71_1 : C 20 71 1 := by decide +kernel
theorem cell_20_71_2 : C 20 71 2 := by decide +kernel
theorem cell_20_71_3 : C 20 71 3 := by decide +kernel
theorem cell_20_71_4 : C 20 71 4 := by decide +kernel
theorem cell_20_71_5 : C 20 71 5 := by decide +kernel
theorem row_20_71 : ThresholdAt 20 71 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 71 0 cell_20_71_0
  | exact S 20 71 1 cell_20_71_1
  | exact S 20 71 2 cell_20_71_2
  | exact S 20 71 3 cell_20_71_3
  | exact S 20 71 4 cell_20_71_4
  | exact S 20 71 5 cell_20_71_5
theorem cell_20_72_0 : C 20 72 0 := by decide +kernel
theorem cell_20_72_1 : C 20 72 1 := by decide +kernel
theorem cell_20_72_2 : C 20 72 2 := by decide +kernel
theorem cell_20_72_3 : C 20 72 3 := by decide +kernel
theorem cell_20_72_4 : C 20 72 4 := by decide +kernel
theorem cell_20_72_5 : C 20 72 5 := by decide +kernel
theorem row_20_72 : ThresholdAt 20 72 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 72 0 cell_20_72_0
  | exact S 20 72 1 cell_20_72_1
  | exact S 20 72 2 cell_20_72_2
  | exact S 20 72 3 cell_20_72_3
  | exact S 20 72 4 cell_20_72_4
  | exact S 20 72 5 cell_20_72_5
theorem cell_20_73_0 : C 20 73 0 := by decide +kernel
theorem cell_20_73_1 : C 20 73 1 := by decide +kernel
theorem cell_20_73_2 : C 20 73 2 := by decide +kernel
theorem cell_20_73_3 : C 20 73 3 := by decide +kernel
theorem cell_20_73_4 : C 20 73 4 := by decide +kernel
theorem cell_20_73_5 : C 20 73 5 := by decide +kernel
theorem row_20_73 : ThresholdAt 20 73 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 73 0 cell_20_73_0
  | exact S 20 73 1 cell_20_73_1
  | exact S 20 73 2 cell_20_73_2
  | exact S 20 73 3 cell_20_73_3
  | exact S 20 73 4 cell_20_73_4
  | exact S 20 73 5 cell_20_73_5
theorem cell_20_74_0 : C 20 74 0 := by decide +kernel
theorem cell_20_74_1 : C 20 74 1 := by decide +kernel
theorem cell_20_74_2 : C 20 74 2 := by decide +kernel
theorem cell_20_74_3 : C 20 74 3 := by decide +kernel
theorem cell_20_74_4 : C 20 74 4 := by decide +kernel
theorem cell_20_74_5 : C 20 74 5 := by decide +kernel
theorem row_20_74 : ThresholdAt 20 74 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 74 0 cell_20_74_0
  | exact S 20 74 1 cell_20_74_1
  | exact S 20 74 2 cell_20_74_2
  | exact S 20 74 3 cell_20_74_3
  | exact S 20 74 4 cell_20_74_4
  | exact S 20 74 5 cell_20_74_5
theorem cell_20_75_0 : C 20 75 0 := by decide +kernel
theorem cell_20_75_1 : C 20 75 1 := by decide +kernel
theorem cell_20_75_2 : C 20 75 2 := by decide +kernel
theorem cell_20_75_3 : C 20 75 3 := by decide +kernel
theorem cell_20_75_4 : C 20 75 4 := by decide +kernel
theorem cell_20_75_5 : C 20 75 5 := by decide +kernel
theorem row_20_75 : ThresholdAt 20 75 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 75 0 cell_20_75_0
  | exact S 20 75 1 cell_20_75_1
  | exact S 20 75 2 cell_20_75_2
  | exact S 20 75 3 cell_20_75_3
  | exact S 20 75 4 cell_20_75_4
  | exact S 20 75 5 cell_20_75_5
theorem cell_20_76_0 : C 20 76 0 := by decide +kernel
theorem cell_20_76_1 : C 20 76 1 := by decide +kernel
theorem cell_20_76_2 : C 20 76 2 := by decide +kernel
theorem cell_20_76_3 : C 20 76 3 := by decide +kernel
theorem cell_20_76_4 : C 20 76 4 := by decide +kernel
theorem cell_20_76_5 : C 20 76 5 := by decide +kernel
theorem row_20_76 : ThresholdAt 20 76 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 76 0 cell_20_76_0
  | exact S 20 76 1 cell_20_76_1
  | exact S 20 76 2 cell_20_76_2
  | exact S 20 76 3 cell_20_76_3
  | exact S 20 76 4 cell_20_76_4
  | exact S 20 76 5 cell_20_76_5
theorem cell_20_77_0 : C 20 77 0 := by decide +kernel
theorem cell_20_77_1 : C 20 77 1 := by decide +kernel
theorem cell_20_77_2 : C 20 77 2 := by decide +kernel
theorem cell_20_77_3 : C 20 77 3 := by decide +kernel
theorem cell_20_77_4 : C 20 77 4 := by decide +kernel
theorem cell_20_77_5 : C 20 77 5 := by decide +kernel
theorem row_20_77 : ThresholdAt 20 77 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 77 0 cell_20_77_0
  | exact S 20 77 1 cell_20_77_1
  | exact S 20 77 2 cell_20_77_2
  | exact S 20 77 3 cell_20_77_3
  | exact S 20 77 4 cell_20_77_4
  | exact S 20 77 5 cell_20_77_5
theorem cell_20_78_0 : C 20 78 0 := by decide +kernel
theorem cell_20_78_1 : C 20 78 1 := by decide +kernel
theorem cell_20_78_2 : C 20 78 2 := by decide +kernel
theorem cell_20_78_3 : C 20 78 3 := by decide +kernel
theorem cell_20_78_4 : C 20 78 4 := by decide +kernel
theorem cell_20_78_5 : C 20 78 5 := by decide +kernel
theorem row_20_78 : ThresholdAt 20 78 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 78 0 cell_20_78_0
  | exact S 20 78 1 cell_20_78_1
  | exact S 20 78 2 cell_20_78_2
  | exact S 20 78 3 cell_20_78_3
  | exact S 20 78 4 cell_20_78_4
  | exact S 20 78 5 cell_20_78_5
theorem cell_20_79_0 : C 20 79 0 := by decide +kernel
theorem cell_20_79_1 : C 20 79 1 := by decide +kernel
theorem cell_20_79_2 : C 20 79 2 := by decide +kernel
theorem cell_20_79_3 : C 20 79 3 := by decide +kernel
theorem cell_20_79_4 : C 20 79 4 := by decide +kernel
theorem cell_20_79_5 : C 20 79 5 := by decide +kernel
theorem row_20_79 : ThresholdAt 20 79 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 79 0 cell_20_79_0
  | exact S 20 79 1 cell_20_79_1
  | exact S 20 79 2 cell_20_79_2
  | exact S 20 79 3 cell_20_79_3
  | exact S 20 79 4 cell_20_79_4
  | exact S 20 79 5 cell_20_79_5
theorem cell_20_80_0 : C 20 80 0 := by decide +kernel
theorem cell_20_80_1 : C 20 80 1 := by decide +kernel
theorem cell_20_80_2 : C 20 80 2 := by decide +kernel
theorem cell_20_80_3 : C 20 80 3 := by decide +kernel
theorem cell_20_80_4 : C 20 80 4 := by decide +kernel
theorem cell_20_80_5 : C 20 80 5 := by decide +kernel
theorem row_20_80 : ThresholdAt 20 80 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 80 0 cell_20_80_0
  | exact S 20 80 1 cell_20_80_1
  | exact S 20 80 2 cell_20_80_2
  | exact S 20 80 3 cell_20_80_3
  | exact S 20 80 4 cell_20_80_4
  | exact S 20 80 5 cell_20_80_5
theorem cell_20_81_0 : C 20 81 0 := by decide +kernel
theorem cell_20_81_1 : C 20 81 1 := by decide +kernel
theorem cell_20_81_2 : C 20 81 2 := by decide +kernel
theorem cell_20_81_3 : C 20 81 3 := by decide +kernel
theorem cell_20_81_4 : C 20 81 4 := by decide +kernel
theorem cell_20_81_5 : C 20 81 5 := by decide +kernel
theorem row_20_81 : ThresholdAt 20 81 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 81 0 cell_20_81_0
  | exact S 20 81 1 cell_20_81_1
  | exact S 20 81 2 cell_20_81_2
  | exact S 20 81 3 cell_20_81_3
  | exact S 20 81 4 cell_20_81_4
  | exact S 20 81 5 cell_20_81_5
theorem cell_20_82_0 : C 20 82 0 := by decide +kernel
theorem cell_20_82_1 : C 20 82 1 := by decide +kernel
theorem cell_20_82_2 : C 20 82 2 := by decide +kernel
theorem cell_20_82_3 : C 20 82 3 := by decide +kernel
theorem cell_20_82_4 : C 20 82 4 := by decide +kernel
theorem cell_20_82_5 : C 20 82 5 := by decide +kernel
theorem row_20_82 : ThresholdAt 20 82 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 82 0 cell_20_82_0
  | exact S 20 82 1 cell_20_82_1
  | exact S 20 82 2 cell_20_82_2
  | exact S 20 82 3 cell_20_82_3
  | exact S 20 82 4 cell_20_82_4
  | exact S 20 82 5 cell_20_82_5
theorem cell_20_83_0 : C 20 83 0 := by decide +kernel
theorem cell_20_83_1 : C 20 83 1 := by decide +kernel
theorem cell_20_83_2 : C 20 83 2 := by decide +kernel
theorem cell_20_83_3 : C 20 83 3 := by decide +kernel
theorem cell_20_83_4 : C 20 83 4 := by decide +kernel
theorem cell_20_83_5 : C 20 83 5 := by decide +kernel
theorem row_20_83 : ThresholdAt 20 83 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 83 0 cell_20_83_0
  | exact S 20 83 1 cell_20_83_1
  | exact S 20 83 2 cell_20_83_2
  | exact S 20 83 3 cell_20_83_3
  | exact S 20 83 4 cell_20_83_4
  | exact S 20 83 5 cell_20_83_5
theorem cell_20_84_0 : C 20 84 0 := by decide +kernel
theorem cell_20_84_1 : C 20 84 1 := by decide +kernel
theorem cell_20_84_2 : C 20 84 2 := by decide +kernel
theorem cell_20_84_3 : C 20 84 3 := by decide +kernel
theorem cell_20_84_4 : C 20 84 4 := by decide +kernel
theorem cell_20_84_5 : C 20 84 5 := by decide +kernel
theorem row_20_84 : ThresholdAt 20 84 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 84 0 cell_20_84_0
  | exact S 20 84 1 cell_20_84_1
  | exact S 20 84 2 cell_20_84_2
  | exact S 20 84 3 cell_20_84_3
  | exact S 20 84 4 cell_20_84_4
  | exact S 20 84 5 cell_20_84_5
theorem cell_20_85_0 : C 20 85 0 := by decide +kernel
theorem cell_20_85_1 : C 20 85 1 := by decide +kernel
theorem cell_20_85_2 : C 20 85 2 := by decide +kernel
theorem cell_20_85_3 : C 20 85 3 := by decide +kernel
theorem cell_20_85_4 : C 20 85 4 := by decide +kernel
theorem cell_20_85_5 : C 20 85 5 := by decide +kernel
theorem row_20_85 : ThresholdAt 20 85 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 85 0 cell_20_85_0
  | exact S 20 85 1 cell_20_85_1
  | exact S 20 85 2 cell_20_85_2
  | exact S 20 85 3 cell_20_85_3
  | exact S 20 85 4 cell_20_85_4
  | exact S 20 85 5 cell_20_85_5
theorem cell_20_86_0 : C 20 86 0 := by decide +kernel
theorem cell_20_86_1 : C 20 86 1 := by decide +kernel
theorem cell_20_86_2 : C 20 86 2 := by decide +kernel
theorem cell_20_86_3 : C 20 86 3 := by decide +kernel
theorem cell_20_86_4 : C 20 86 4 := by decide +kernel
theorem cell_20_86_5 : C 20 86 5 := by decide +kernel
theorem row_20_86 : ThresholdAt 20 86 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 86 0 cell_20_86_0
  | exact S 20 86 1 cell_20_86_1
  | exact S 20 86 2 cell_20_86_2
  | exact S 20 86 3 cell_20_86_3
  | exact S 20 86 4 cell_20_86_4
  | exact S 20 86 5 cell_20_86_5
theorem cell_20_87_0 : C 20 87 0 := by decide +kernel
theorem cell_20_87_1 : C 20 87 1 := by decide +kernel
theorem cell_20_87_2 : C 20 87 2 := by decide +kernel
theorem cell_20_87_3 : C 20 87 3 := by decide +kernel
theorem cell_20_87_4 : C 20 87 4 := by decide +kernel
theorem cell_20_87_5 : C 20 87 5 := by decide +kernel
theorem row_20_87 : ThresholdAt 20 87 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 87 0 cell_20_87_0
  | exact S 20 87 1 cell_20_87_1
  | exact S 20 87 2 cell_20_87_2
  | exact S 20 87 3 cell_20_87_3
  | exact S 20 87 4 cell_20_87_4
  | exact S 20 87 5 cell_20_87_5
theorem cell_20_88_0 : C 20 88 0 := by decide +kernel
theorem cell_20_88_1 : C 20 88 1 := by decide +kernel
theorem cell_20_88_2 : C 20 88 2 := by decide +kernel
theorem cell_20_88_3 : C 20 88 3 := by decide +kernel
theorem cell_20_88_4 : C 20 88 4 := by decide +kernel
theorem cell_20_88_5 : C 20 88 5 := by decide +kernel
theorem row_20_88 : ThresholdAt 20 88 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 88 0 cell_20_88_0
  | exact S 20 88 1 cell_20_88_1
  | exact S 20 88 2 cell_20_88_2
  | exact S 20 88 3 cell_20_88_3
  | exact S 20 88 4 cell_20_88_4
  | exact S 20 88 5 cell_20_88_5
theorem cell_20_89_0 : C 20 89 0 := by decide +kernel
theorem cell_20_89_1 : C 20 89 1 := by decide +kernel
theorem cell_20_89_2 : C 20 89 2 := by decide +kernel
theorem cell_20_89_3 : C 20 89 3 := by decide +kernel
theorem cell_20_89_4 : C 20 89 4 := by decide +kernel
theorem cell_20_89_5 : C 20 89 5 := by decide +kernel
theorem row_20_89 : ThresholdAt 20 89 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 89 0 cell_20_89_0
  | exact S 20 89 1 cell_20_89_1
  | exact S 20 89 2 cell_20_89_2
  | exact S 20 89 3 cell_20_89_3
  | exact S 20 89 4 cell_20_89_4
  | exact S 20 89 5 cell_20_89_5
theorem cell_20_90_0 : C 20 90 0 := by decide +kernel
theorem cell_20_90_1 : C 20 90 1 := by decide +kernel
theorem cell_20_90_2 : C 20 90 2 := by decide +kernel
theorem cell_20_90_3 : C 20 90 3 := by decide +kernel
theorem cell_20_90_4 : C 20 90 4 := by decide +kernel
theorem cell_20_90_5 : C 20 90 5 := by decide +kernel
theorem row_20_90 : ThresholdAt 20 90 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 90 0 cell_20_90_0
  | exact S 20 90 1 cell_20_90_1
  | exact S 20 90 2 cell_20_90_2
  | exact S 20 90 3 cell_20_90_3
  | exact S 20 90 4 cell_20_90_4
  | exact S 20 90 5 cell_20_90_5
theorem cell_20_91_0 : C 20 91 0 := by decide +kernel
theorem cell_20_91_1 : C 20 91 1 := by decide +kernel
theorem cell_20_91_2 : C 20 91 2 := by decide +kernel
theorem cell_20_91_3 : C 20 91 3 := by decide +kernel
theorem cell_20_91_4 : C 20 91 4 := by decide +kernel
theorem cell_20_91_5 : C 20 91 5 := by decide +kernel
theorem row_20_91 : ThresholdAt 20 91 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 91 0 cell_20_91_0
  | exact S 20 91 1 cell_20_91_1
  | exact S 20 91 2 cell_20_91_2
  | exact S 20 91 3 cell_20_91_3
  | exact S 20 91 4 cell_20_91_4
  | exact S 20 91 5 cell_20_91_5
theorem cell_20_92_0 : C 20 92 0 := by decide +kernel
theorem cell_20_92_1 : C 20 92 1 := by decide +kernel
theorem cell_20_92_2 : C 20 92 2 := by decide +kernel
theorem cell_20_92_3 : C 20 92 3 := by decide +kernel
theorem cell_20_92_4 : C 20 92 4 := by decide +kernel
theorem cell_20_92_5 : C 20 92 5 := by decide +kernel
theorem row_20_92 : ThresholdAt 20 92 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 92 0 cell_20_92_0
  | exact S 20 92 1 cell_20_92_1
  | exact S 20 92 2 cell_20_92_2
  | exact S 20 92 3 cell_20_92_3
  | exact S 20 92 4 cell_20_92_4
  | exact S 20 92 5 cell_20_92_5
theorem cell_20_93_0 : C 20 93 0 := by decide +kernel
theorem cell_20_93_1 : C 20 93 1 := by decide +kernel
theorem cell_20_93_2 : C 20 93 2 := by decide +kernel
theorem cell_20_93_3 : C 20 93 3 := by decide +kernel
theorem cell_20_93_4 : C 20 93 4 := by decide +kernel
theorem cell_20_93_5 : C 20 93 5 := by decide +kernel
theorem row_20_93 : ThresholdAt 20 93 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 93 0 cell_20_93_0
  | exact S 20 93 1 cell_20_93_1
  | exact S 20 93 2 cell_20_93_2
  | exact S 20 93 3 cell_20_93_3
  | exact S 20 93 4 cell_20_93_4
  | exact S 20 93 5 cell_20_93_5
theorem cell_20_94_0 : C 20 94 0 := by decide +kernel
theorem cell_20_94_1 : C 20 94 1 := by decide +kernel
theorem cell_20_94_2 : C 20 94 2 := by decide +kernel
theorem cell_20_94_3 : C 20 94 3 := by decide +kernel
theorem cell_20_94_4 : C 20 94 4 := by decide +kernel
theorem cell_20_94_5 : C 20 94 5 := by decide +kernel
theorem row_20_94 : ThresholdAt 20 94 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 94 0 cell_20_94_0
  | exact S 20 94 1 cell_20_94_1
  | exact S 20 94 2 cell_20_94_2
  | exact S 20 94 3 cell_20_94_3
  | exact S 20 94 4 cell_20_94_4
  | exact S 20 94 5 cell_20_94_5
theorem cell_20_95_0 : C 20 95 0 := by decide +kernel
theorem cell_20_95_1 : C 20 95 1 := by decide +kernel
theorem cell_20_95_2 : C 20 95 2 := by decide +kernel
theorem cell_20_95_3 : C 20 95 3 := by decide +kernel
theorem cell_20_95_4 : C 20 95 4 := by decide +kernel
theorem cell_20_95_5 : C 20 95 5 := by decide +kernel
theorem row_20_95 : ThresholdAt 20 95 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 95 0 cell_20_95_0
  | exact S 20 95 1 cell_20_95_1
  | exact S 20 95 2 cell_20_95_2
  | exact S 20 95 3 cell_20_95_3
  | exact S 20 95 4 cell_20_95_4
  | exact S 20 95 5 cell_20_95_5
theorem cell_20_96_0 : C 20 96 0 := by decide +kernel
theorem cell_20_96_1 : C 20 96 1 := by decide +kernel
theorem cell_20_96_2 : C 20 96 2 := by decide +kernel
theorem cell_20_96_3 : C 20 96 3 := by decide +kernel
theorem cell_20_96_4 : C 20 96 4 := by decide +kernel
theorem cell_20_96_5 : C 20 96 5 := by decide +kernel
theorem row_20_96 : ThresholdAt 20 96 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 96 0 cell_20_96_0
  | exact S 20 96 1 cell_20_96_1
  | exact S 20 96 2 cell_20_96_2
  | exact S 20 96 3 cell_20_96_3
  | exact S 20 96 4 cell_20_96_4
  | exact S 20 96 5 cell_20_96_5
theorem cell_20_97_0 : C 20 97 0 := by decide +kernel
theorem cell_20_97_1 : C 20 97 1 := by decide +kernel
theorem cell_20_97_2 : C 20 97 2 := by decide +kernel
theorem cell_20_97_3 : C 20 97 3 := by decide +kernel
theorem cell_20_97_4 : C 20 97 4 := by decide +kernel
theorem cell_20_97_5 : C 20 97 5 := by decide +kernel
theorem row_20_97 : ThresholdAt 20 97 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 97 0 cell_20_97_0
  | exact S 20 97 1 cell_20_97_1
  | exact S 20 97 2 cell_20_97_2
  | exact S 20 97 3 cell_20_97_3
  | exact S 20 97 4 cell_20_97_4
  | exact S 20 97 5 cell_20_97_5
theorem cell_20_98_0 : C 20 98 0 := by decide +kernel
theorem cell_20_98_1 : C 20 98 1 := by decide +kernel
theorem cell_20_98_2 : C 20 98 2 := by decide +kernel
theorem cell_20_98_3 : C 20 98 3 := by decide +kernel
theorem cell_20_98_4 : C 20 98 4 := by decide +kernel
theorem cell_20_98_5 : C 20 98 5 := by decide +kernel
theorem row_20_98 : ThresholdAt 20 98 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 98 0 cell_20_98_0
  | exact S 20 98 1 cell_20_98_1
  | exact S 20 98 2 cell_20_98_2
  | exact S 20 98 3 cell_20_98_3
  | exact S 20 98 4 cell_20_98_4
  | exact S 20 98 5 cell_20_98_5
theorem cell_20_99_0 : C 20 99 0 := by decide +kernel
theorem cell_20_99_1 : C 20 99 1 := by decide +kernel
theorem cell_20_99_2 : C 20 99 2 := by decide +kernel
theorem cell_20_99_3 : C 20 99 3 := by decide +kernel
theorem cell_20_99_4 : C 20 99 4 := by decide +kernel
theorem cell_20_99_5 : C 20 99 5 := by decide +kernel
theorem row_20_99 : ThresholdAt 20 99 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 99 0 cell_20_99_0
  | exact S 20 99 1 cell_20_99_1
  | exact S 20 99 2 cell_20_99_2
  | exact S 20 99 3 cell_20_99_3
  | exact S 20 99 4 cell_20_99_4
  | exact S 20 99 5 cell_20_99_5
theorem cell_20_100_0 : C 20 100 0 := by decide +kernel
theorem cell_20_100_1 : C 20 100 1 := by decide +kernel
theorem cell_20_100_2 : C 20 100 2 := by decide +kernel
theorem cell_20_100_3 : C 20 100 3 := by decide +kernel
theorem cell_20_100_4 : C 20 100 4 := by decide +kernel
theorem cell_20_100_5 : C 20 100 5 := by decide +kernel
theorem row_20_100 : ThresholdAt 20 100 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 100 0 cell_20_100_0
  | exact S 20 100 1 cell_20_100_1
  | exact S 20 100 2 cell_20_100_2
  | exact S 20 100 3 cell_20_100_3
  | exact S 20 100 4 cell_20_100_4
  | exact S 20 100 5 cell_20_100_5
theorem cell_20_101_0 : C 20 101 0 := by decide +kernel
theorem cell_20_101_1 : C 20 101 1 := by decide +kernel
theorem cell_20_101_2 : C 20 101 2 := by decide +kernel
theorem cell_20_101_3 : C 20 101 3 := by decide +kernel
theorem cell_20_101_4 : C 20 101 4 := by decide +kernel
theorem cell_20_101_5 : C 20 101 5 := by decide +kernel
theorem row_20_101 : ThresholdAt 20 101 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 101 0 cell_20_101_0
  | exact S 20 101 1 cell_20_101_1
  | exact S 20 101 2 cell_20_101_2
  | exact S 20 101 3 cell_20_101_3
  | exact S 20 101 4 cell_20_101_4
  | exact S 20 101 5 cell_20_101_5
theorem cell_20_102_0 : C 20 102 0 := by decide +kernel
theorem cell_20_102_1 : C 20 102 1 := by decide +kernel
theorem cell_20_102_2 : C 20 102 2 := by decide +kernel
theorem cell_20_102_3 : C 20 102 3 := by decide +kernel
theorem cell_20_102_4 : C 20 102 4 := by decide +kernel
theorem cell_20_102_5 : C 20 102 5 := by decide +kernel
theorem row_20_102 : ThresholdAt 20 102 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 102 0 cell_20_102_0
  | exact S 20 102 1 cell_20_102_1
  | exact S 20 102 2 cell_20_102_2
  | exact S 20 102 3 cell_20_102_3
  | exact S 20 102 4 cell_20_102_4
  | exact S 20 102 5 cell_20_102_5
theorem cell_20_103_0 : C 20 103 0 := by decide +kernel
theorem cell_20_103_1 : C 20 103 1 := by decide +kernel
theorem cell_20_103_2 : C 20 103 2 := by decide +kernel
theorem cell_20_103_3 : C 20 103 3 := by decide +kernel
theorem cell_20_103_4 : C 20 103 4 := by decide +kernel
theorem cell_20_103_5 : C 20 103 5 := by decide +kernel
theorem row_20_103 : ThresholdAt 20 103 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 103 0 cell_20_103_0
  | exact S 20 103 1 cell_20_103_1
  | exact S 20 103 2 cell_20_103_2
  | exact S 20 103 3 cell_20_103_3
  | exact S 20 103 4 cell_20_103_4
  | exact S 20 103 5 cell_20_103_5
theorem cell_20_104_0 : C 20 104 0 := by decide +kernel
theorem cell_20_104_1 : C 20 104 1 := by decide +kernel
theorem cell_20_104_2 : C 20 104 2 := by decide +kernel
theorem cell_20_104_3 : C 20 104 3 := by decide +kernel
theorem cell_20_104_4 : C 20 104 4 := by decide +kernel
theorem cell_20_104_5 : C 20 104 5 := by decide +kernel
theorem row_20_104 : ThresholdAt 20 104 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 104 0 cell_20_104_0
  | exact S 20 104 1 cell_20_104_1
  | exact S 20 104 2 cell_20_104_2
  | exact S 20 104 3 cell_20_104_3
  | exact S 20 104 4 cell_20_104_4
  | exact S 20 104 5 cell_20_104_5
theorem cell_20_105_0 : C 20 105 0 := by decide +kernel
theorem cell_20_105_1 : C 20 105 1 := by decide +kernel
theorem cell_20_105_2 : C 20 105 2 := by decide +kernel
theorem cell_20_105_3 : C 20 105 3 := by decide +kernel
theorem cell_20_105_4 : C 20 105 4 := by decide +kernel
theorem cell_20_105_5 : C 20 105 5 := by decide +kernel
theorem row_20_105 : ThresholdAt 20 105 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 105 0 cell_20_105_0
  | exact S 20 105 1 cell_20_105_1
  | exact S 20 105 2 cell_20_105_2
  | exact S 20 105 3 cell_20_105_3
  | exact S 20 105 4 cell_20_105_4
  | exact S 20 105 5 cell_20_105_5
theorem cell_20_106_0 : C 20 106 0 := by decide +kernel
theorem cell_20_106_1 : C 20 106 1 := by decide +kernel
theorem cell_20_106_2 : C 20 106 2 := by decide +kernel
theorem cell_20_106_3 : C 20 106 3 := by decide +kernel
theorem cell_20_106_4 : C 20 106 4 := by decide +kernel
theorem cell_20_106_5 : C 20 106 5 := by decide +kernel
theorem row_20_106 : ThresholdAt 20 106 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 106 0 cell_20_106_0
  | exact S 20 106 1 cell_20_106_1
  | exact S 20 106 2 cell_20_106_2
  | exact S 20 106 3 cell_20_106_3
  | exact S 20 106 4 cell_20_106_4
  | exact S 20 106 5 cell_20_106_5
theorem cell_20_107_0 : C 20 107 0 := by decide +kernel
theorem cell_20_107_1 : C 20 107 1 := by decide +kernel
theorem cell_20_107_2 : C 20 107 2 := by decide +kernel
theorem cell_20_107_3 : C 20 107 3 := by decide +kernel
theorem cell_20_107_4 : C 20 107 4 := by decide +kernel
theorem cell_20_107_5 : C 20 107 5 := by decide +kernel
theorem row_20_107 : ThresholdAt 20 107 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 107 0 cell_20_107_0
  | exact S 20 107 1 cell_20_107_1
  | exact S 20 107 2 cell_20_107_2
  | exact S 20 107 3 cell_20_107_3
  | exact S 20 107 4 cell_20_107_4
  | exact S 20 107 5 cell_20_107_5
theorem cell_20_108_0 : C 20 108 0 := by decide +kernel
theorem cell_20_108_1 : C 20 108 1 := by decide +kernel
theorem cell_20_108_2 : C 20 108 2 := by decide +kernel
theorem cell_20_108_3 : C 20 108 3 := by decide +kernel
theorem cell_20_108_4 : C 20 108 4 := by decide +kernel
theorem cell_20_108_5 : C 20 108 5 := by decide +kernel
theorem row_20_108 : ThresholdAt 20 108 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 108 0 cell_20_108_0
  | exact S 20 108 1 cell_20_108_1
  | exact S 20 108 2 cell_20_108_2
  | exact S 20 108 3 cell_20_108_3
  | exact S 20 108 4 cell_20_108_4
  | exact S 20 108 5 cell_20_108_5
theorem cell_20_109_0 : C 20 109 0 := by decide +kernel
theorem cell_20_109_1 : C 20 109 1 := by decide +kernel
theorem cell_20_109_2 : C 20 109 2 := by decide +kernel
theorem cell_20_109_3 : C 20 109 3 := by decide +kernel
theorem cell_20_109_4 : C 20 109 4 := by decide +kernel
theorem cell_20_109_5 : C 20 109 5 := by decide +kernel
theorem row_20_109 : ThresholdAt 20 109 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 109 0 cell_20_109_0
  | exact S 20 109 1 cell_20_109_1
  | exact S 20 109 2 cell_20_109_2
  | exact S 20 109 3 cell_20_109_3
  | exact S 20 109 4 cell_20_109_4
  | exact S 20 109 5 cell_20_109_5
theorem cell_20_110_0 : C 20 110 0 := by decide +kernel
theorem cell_20_110_1 : C 20 110 1 := by decide +kernel
theorem cell_20_110_2 : C 20 110 2 := by decide +kernel
theorem cell_20_110_3 : C 20 110 3 := by decide +kernel
theorem cell_20_110_4 : C 20 110 4 := by decide +kernel
theorem cell_20_110_5 : C 20 110 5 := by decide +kernel
theorem row_20_110 : ThresholdAt 20 110 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 110 0 cell_20_110_0
  | exact S 20 110 1 cell_20_110_1
  | exact S 20 110 2 cell_20_110_2
  | exact S 20 110 3 cell_20_110_3
  | exact S 20 110 4 cell_20_110_4
  | exact S 20 110 5 cell_20_110_5
theorem cell_20_111_0 : C 20 111 0 := by decide +kernel
theorem cell_20_111_1 : C 20 111 1 := by decide +kernel
theorem cell_20_111_2 : C 20 111 2 := by decide +kernel
theorem cell_20_111_3 : C 20 111 3 := by decide +kernel
theorem cell_20_111_4 : C 20 111 4 := by decide +kernel
theorem cell_20_111_5 : C 20 111 5 := by decide +kernel
theorem row_20_111 : ThresholdAt 20 111 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 111 0 cell_20_111_0
  | exact S 20 111 1 cell_20_111_1
  | exact S 20 111 2 cell_20_111_2
  | exact S 20 111 3 cell_20_111_3
  | exact S 20 111 4 cell_20_111_4
  | exact S 20 111 5 cell_20_111_5
theorem cell_20_112_0 : C 20 112 0 := by decide +kernel
theorem cell_20_112_1 : C 20 112 1 := by decide +kernel
theorem cell_20_112_2 : C 20 112 2 := by decide +kernel
theorem cell_20_112_3 : C 20 112 3 := by decide +kernel
theorem cell_20_112_4 : C 20 112 4 := by decide +kernel
theorem cell_20_112_5 : C 20 112 5 := by decide +kernel
theorem row_20_112 : ThresholdAt 20 112 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 112 0 cell_20_112_0
  | exact S 20 112 1 cell_20_112_1
  | exact S 20 112 2 cell_20_112_2
  | exact S 20 112 3 cell_20_112_3
  | exact S 20 112 4 cell_20_112_4
  | exact S 20 112 5 cell_20_112_5
theorem cell_20_113_0 : C 20 113 0 := by decide +kernel
theorem cell_20_113_1 : C 20 113 1 := by decide +kernel
theorem cell_20_113_2 : C 20 113 2 := by decide +kernel
theorem cell_20_113_3 : C 20 113 3 := by decide +kernel
theorem cell_20_113_4 : C 20 113 4 := by decide +kernel
theorem cell_20_113_5 : C 20 113 5 := by decide +kernel
theorem row_20_113 : ThresholdAt 20 113 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 113 0 cell_20_113_0
  | exact S 20 113 1 cell_20_113_1
  | exact S 20 113 2 cell_20_113_2
  | exact S 20 113 3 cell_20_113_3
  | exact S 20 113 4 cell_20_113_4
  | exact S 20 113 5 cell_20_113_5
theorem cell_20_114_0 : C 20 114 0 := by decide +kernel
theorem cell_20_114_1 : C 20 114 1 := by decide +kernel
theorem cell_20_114_2 : C 20 114 2 := by decide +kernel
theorem cell_20_114_3 : C 20 114 3 := by decide +kernel
theorem cell_20_114_4 : C 20 114 4 := by decide +kernel
theorem cell_20_114_5 : C 20 114 5 := by decide +kernel
theorem row_20_114 : ThresholdAt 20 114 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 114 0 cell_20_114_0
  | exact S 20 114 1 cell_20_114_1
  | exact S 20 114 2 cell_20_114_2
  | exact S 20 114 3 cell_20_114_3
  | exact S 20 114 4 cell_20_114_4
  | exact S 20 114 5 cell_20_114_5
theorem cell_20_115_0 : C 20 115 0 := by decide +kernel
theorem cell_20_115_1 : C 20 115 1 := by decide +kernel
theorem cell_20_115_2 : C 20 115 2 := by decide +kernel
theorem cell_20_115_3 : C 20 115 3 := by decide +kernel
theorem cell_20_115_4 : C 20 115 4 := by decide +kernel
theorem cell_20_115_5 : C 20 115 5 := by decide +kernel
theorem row_20_115 : ThresholdAt 20 115 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 115 0 cell_20_115_0
  | exact S 20 115 1 cell_20_115_1
  | exact S 20 115 2 cell_20_115_2
  | exact S 20 115 3 cell_20_115_3
  | exact S 20 115 4 cell_20_115_4
  | exact S 20 115 5 cell_20_115_5
theorem cell_20_116_0 : C 20 116 0 := by decide +kernel
theorem cell_20_116_1 : C 20 116 1 := by decide +kernel
theorem cell_20_116_2 : C 20 116 2 := by decide +kernel
theorem cell_20_116_3 : C 20 116 3 := by decide +kernel
theorem cell_20_116_4 : C 20 116 4 := by decide +kernel
theorem cell_20_116_5 : C 20 116 5 := by decide +kernel
theorem row_20_116 : ThresholdAt 20 116 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 116 0 cell_20_116_0
  | exact S 20 116 1 cell_20_116_1
  | exact S 20 116 2 cell_20_116_2
  | exact S 20 116 3 cell_20_116_3
  | exact S 20 116 4 cell_20_116_4
  | exact S 20 116 5 cell_20_116_5
theorem cell_20_117_0 : C 20 117 0 := by decide +kernel
theorem cell_20_117_1 : C 20 117 1 := by decide +kernel
theorem cell_20_117_2 : C 20 117 2 := by decide +kernel
theorem cell_20_117_3 : C 20 117 3 := by decide +kernel
theorem cell_20_117_4 : C 20 117 4 := by decide +kernel
theorem cell_20_117_5 : C 20 117 5 := by decide +kernel
theorem row_20_117 : ThresholdAt 20 117 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 117 0 cell_20_117_0
  | exact S 20 117 1 cell_20_117_1
  | exact S 20 117 2 cell_20_117_2
  | exact S 20 117 3 cell_20_117_3
  | exact S 20 117 4 cell_20_117_4
  | exact S 20 117 5 cell_20_117_5
theorem cell_20_118_0 : C 20 118 0 := by decide +kernel
theorem cell_20_118_1 : C 20 118 1 := by decide +kernel
theorem cell_20_118_2 : C 20 118 2 := by decide +kernel
theorem cell_20_118_3 : C 20 118 3 := by decide +kernel
theorem cell_20_118_4 : C 20 118 4 := by decide +kernel
theorem cell_20_118_5 : C 20 118 5 := by decide +kernel
theorem row_20_118 : ThresholdAt 20 118 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 118 0 cell_20_118_0
  | exact S 20 118 1 cell_20_118_1
  | exact S 20 118 2 cell_20_118_2
  | exact S 20 118 3 cell_20_118_3
  | exact S 20 118 4 cell_20_118_4
  | exact S 20 118 5 cell_20_118_5
theorem cell_20_119_0 : C 20 119 0 := by decide +kernel
theorem cell_20_119_1 : C 20 119 1 := by decide +kernel
theorem cell_20_119_2 : C 20 119 2 := by decide +kernel
theorem cell_20_119_3 : C 20 119 3 := by decide +kernel
theorem cell_20_119_4 : C 20 119 4 := by decide +kernel
theorem cell_20_119_5 : C 20 119 5 := by decide +kernel
theorem row_20_119 : ThresholdAt 20 119 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 20 119 0 cell_20_119_0
  | exact S 20 119 1 cell_20_119_1
  | exact S 20 119 2 cell_20_119_2
  | exact S 20 119 3 cell_20_119_3
  | exact S 20 119 4 cell_20_119_4
  | exact S 20 119 5 cell_20_119_5
theorem checkedR20 : ∀ V ∈ List.range 120, ThresholdAt 20 V := by
  intro V hV
  have hv : V < 120 := List.mem_range.mp hV
  by_cases h0_120 : V < 60
  · by_cases h0_60 : V < 30
    · by_cases h0_30 : V < 15
      · by_cases h0_15 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have he : V = 0 := by omega
              subst V
              exact row_20_0
            · by_cases h1_3 : V < 2
              · have he : V = 1 := by omega
                subst V
                exact row_20_1
              · have he : V = 2 := by omega
                subst V
                exact row_20_2
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have he : V = 3 := by omega
                subst V
                exact row_20_3
              · have he : V = 4 := by omega
                subst V
                exact row_20_4
            · by_cases h5_7 : V < 6
              · have he : V = 5 := by omega
                subst V
                exact row_20_5
              · have he : V = 6 := by omega
                subst V
                exact row_20_6
        · by_cases h7_15 : V < 11
          · by_cases h7_11 : V < 9
            · by_cases h7_9 : V < 8
              · have he : V = 7 := by omega
                subst V
                exact row_20_7
              · have he : V = 8 := by omega
                subst V
                exact row_20_8
            · by_cases h9_11 : V < 10
              · have he : V = 9 := by omega
                subst V
                exact row_20_9
              · have he : V = 10 := by omega
                subst V
                exact row_20_10
          · by_cases h11_15 : V < 13
            · by_cases h11_13 : V < 12
              · have he : V = 11 := by omega
                subst V
                exact row_20_11
              · have he : V = 12 := by omega
                subst V
                exact row_20_12
            · by_cases h13_15 : V < 14
              · have he : V = 13 := by omega
                subst V
                exact row_20_13
              · have he : V = 14 := by omega
                subst V
                exact row_20_14
      · by_cases h15_30 : V < 22
        · by_cases h15_22 : V < 18
          · by_cases h15_18 : V < 16
            · have he : V = 15 := by omega
              subst V
              exact row_20_15
            · by_cases h16_18 : V < 17
              · have he : V = 16 := by omega
                subst V
                exact row_20_16
              · have he : V = 17 := by omega
                subst V
                exact row_20_17
          · by_cases h18_22 : V < 20
            · by_cases h18_20 : V < 19
              · have he : V = 18 := by omega
                subst V
                exact row_20_18
              · have he : V = 19 := by omega
                subst V
                exact row_20_19
            · by_cases h20_22 : V < 21
              · have he : V = 20 := by omega
                subst V
                exact row_20_20
              · have he : V = 21 := by omega
                subst V
                exact row_20_21
        · by_cases h22_30 : V < 26
          · by_cases h22_26 : V < 24
            · by_cases h22_24 : V < 23
              · have he : V = 22 := by omega
                subst V
                exact row_20_22
              · have he : V = 23 := by omega
                subst V
                exact row_20_23
            · by_cases h24_26 : V < 25
              · have he : V = 24 := by omega
                subst V
                exact row_20_24
              · have he : V = 25 := by omega
                subst V
                exact row_20_25
          · by_cases h26_30 : V < 28
            · by_cases h26_28 : V < 27
              · have he : V = 26 := by omega
                subst V
                exact row_20_26
              · have he : V = 27 := by omega
                subst V
                exact row_20_27
            · by_cases h28_30 : V < 29
              · have he : V = 28 := by omega
                subst V
                exact row_20_28
              · have he : V = 29 := by omega
                subst V
                exact row_20_29
    · by_cases h30_60 : V < 45
      · by_cases h30_45 : V < 37
        · by_cases h30_37 : V < 33
          · by_cases h30_33 : V < 31
            · have he : V = 30 := by omega
              subst V
              exact row_20_30
            · by_cases h31_33 : V < 32
              · have he : V = 31 := by omega
                subst V
                exact row_20_31
              · have he : V = 32 := by omega
                subst V
                exact row_20_32
          · by_cases h33_37 : V < 35
            · by_cases h33_35 : V < 34
              · have he : V = 33 := by omega
                subst V
                exact row_20_33
              · have he : V = 34 := by omega
                subst V
                exact row_20_34
            · by_cases h35_37 : V < 36
              · have he : V = 35 := by omega
                subst V
                exact row_20_35
              · have he : V = 36 := by omega
                subst V
                exact row_20_36
        · by_cases h37_45 : V < 41
          · by_cases h37_41 : V < 39
            · by_cases h37_39 : V < 38
              · have he : V = 37 := by omega
                subst V
                exact row_20_37
              · have he : V = 38 := by omega
                subst V
                exact row_20_38
            · by_cases h39_41 : V < 40
              · have he : V = 39 := by omega
                subst V
                exact row_20_39
              · have he : V = 40 := by omega
                subst V
                exact row_20_40
          · by_cases h41_45 : V < 43
            · by_cases h41_43 : V < 42
              · have he : V = 41 := by omega
                subst V
                exact row_20_41
              · have he : V = 42 := by omega
                subst V
                exact row_20_42
            · by_cases h43_45 : V < 44
              · have he : V = 43 := by omega
                subst V
                exact row_20_43
              · have he : V = 44 := by omega
                subst V
                exact row_20_44
      · by_cases h45_60 : V < 52
        · by_cases h45_52 : V < 48
          · by_cases h45_48 : V < 46
            · have he : V = 45 := by omega
              subst V
              exact row_20_45
            · by_cases h46_48 : V < 47
              · have he : V = 46 := by omega
                subst V
                exact row_20_46
              · have he : V = 47 := by omega
                subst V
                exact row_20_47
          · by_cases h48_52 : V < 50
            · by_cases h48_50 : V < 49
              · have he : V = 48 := by omega
                subst V
                exact row_20_48
              · have he : V = 49 := by omega
                subst V
                exact row_20_49
            · by_cases h50_52 : V < 51
              · have he : V = 50 := by omega
                subst V
                exact row_20_50
              · have he : V = 51 := by omega
                subst V
                exact row_20_51
        · by_cases h52_60 : V < 56
          · by_cases h52_56 : V < 54
            · by_cases h52_54 : V < 53
              · have he : V = 52 := by omega
                subst V
                exact row_20_52
              · have he : V = 53 := by omega
                subst V
                exact row_20_53
            · by_cases h54_56 : V < 55
              · have he : V = 54 := by omega
                subst V
                exact row_20_54
              · have he : V = 55 := by omega
                subst V
                exact row_20_55
          · by_cases h56_60 : V < 58
            · by_cases h56_58 : V < 57
              · have he : V = 56 := by omega
                subst V
                exact row_20_56
              · have he : V = 57 := by omega
                subst V
                exact row_20_57
            · by_cases h58_60 : V < 59
              · have he : V = 58 := by omega
                subst V
                exact row_20_58
              · have he : V = 59 := by omega
                subst V
                exact row_20_59
  · by_cases h60_120 : V < 90
    · by_cases h60_90 : V < 75
      · by_cases h60_75 : V < 67
        · by_cases h60_67 : V < 63
          · by_cases h60_63 : V < 61
            · have he : V = 60 := by omega
              subst V
              exact row_20_60
            · by_cases h61_63 : V < 62
              · have he : V = 61 := by omega
                subst V
                exact row_20_61
              · have he : V = 62 := by omega
                subst V
                exact row_20_62
          · by_cases h63_67 : V < 65
            · by_cases h63_65 : V < 64
              · have he : V = 63 := by omega
                subst V
                exact row_20_63
              · have he : V = 64 := by omega
                subst V
                exact row_20_64
            · by_cases h65_67 : V < 66
              · have he : V = 65 := by omega
                subst V
                exact row_20_65
              · have he : V = 66 := by omega
                subst V
                exact row_20_66
        · by_cases h67_75 : V < 71
          · by_cases h67_71 : V < 69
            · by_cases h67_69 : V < 68
              · have he : V = 67 := by omega
                subst V
                exact row_20_67
              · have he : V = 68 := by omega
                subst V
                exact row_20_68
            · by_cases h69_71 : V < 70
              · have he : V = 69 := by omega
                subst V
                exact row_20_69
              · have he : V = 70 := by omega
                subst V
                exact row_20_70
          · by_cases h71_75 : V < 73
            · by_cases h71_73 : V < 72
              · have he : V = 71 := by omega
                subst V
                exact row_20_71
              · have he : V = 72 := by omega
                subst V
                exact row_20_72
            · by_cases h73_75 : V < 74
              · have he : V = 73 := by omega
                subst V
                exact row_20_73
              · have he : V = 74 := by omega
                subst V
                exact row_20_74
      · by_cases h75_90 : V < 82
        · by_cases h75_82 : V < 78
          · by_cases h75_78 : V < 76
            · have he : V = 75 := by omega
              subst V
              exact row_20_75
            · by_cases h76_78 : V < 77
              · have he : V = 76 := by omega
                subst V
                exact row_20_76
              · have he : V = 77 := by omega
                subst V
                exact row_20_77
          · by_cases h78_82 : V < 80
            · by_cases h78_80 : V < 79
              · have he : V = 78 := by omega
                subst V
                exact row_20_78
              · have he : V = 79 := by omega
                subst V
                exact row_20_79
            · by_cases h80_82 : V < 81
              · have he : V = 80 := by omega
                subst V
                exact row_20_80
              · have he : V = 81 := by omega
                subst V
                exact row_20_81
        · by_cases h82_90 : V < 86
          · by_cases h82_86 : V < 84
            · by_cases h82_84 : V < 83
              · have he : V = 82 := by omega
                subst V
                exact row_20_82
              · have he : V = 83 := by omega
                subst V
                exact row_20_83
            · by_cases h84_86 : V < 85
              · have he : V = 84 := by omega
                subst V
                exact row_20_84
              · have he : V = 85 := by omega
                subst V
                exact row_20_85
          · by_cases h86_90 : V < 88
            · by_cases h86_88 : V < 87
              · have he : V = 86 := by omega
                subst V
                exact row_20_86
              · have he : V = 87 := by omega
                subst V
                exact row_20_87
            · by_cases h88_90 : V < 89
              · have he : V = 88 := by omega
                subst V
                exact row_20_88
              · have he : V = 89 := by omega
                subst V
                exact row_20_89
    · by_cases h90_120 : V < 105
      · by_cases h90_105 : V < 97
        · by_cases h90_97 : V < 93
          · by_cases h90_93 : V < 91
            · have he : V = 90 := by omega
              subst V
              exact row_20_90
            · by_cases h91_93 : V < 92
              · have he : V = 91 := by omega
                subst V
                exact row_20_91
              · have he : V = 92 := by omega
                subst V
                exact row_20_92
          · by_cases h93_97 : V < 95
            · by_cases h93_95 : V < 94
              · have he : V = 93 := by omega
                subst V
                exact row_20_93
              · have he : V = 94 := by omega
                subst V
                exact row_20_94
            · by_cases h95_97 : V < 96
              · have he : V = 95 := by omega
                subst V
                exact row_20_95
              · have he : V = 96 := by omega
                subst V
                exact row_20_96
        · by_cases h97_105 : V < 101
          · by_cases h97_101 : V < 99
            · by_cases h97_99 : V < 98
              · have he : V = 97 := by omega
                subst V
                exact row_20_97
              · have he : V = 98 := by omega
                subst V
                exact row_20_98
            · by_cases h99_101 : V < 100
              · have he : V = 99 := by omega
                subst V
                exact row_20_99
              · have he : V = 100 := by omega
                subst V
                exact row_20_100
          · by_cases h101_105 : V < 103
            · by_cases h101_103 : V < 102
              · have he : V = 101 := by omega
                subst V
                exact row_20_101
              · have he : V = 102 := by omega
                subst V
                exact row_20_102
            · by_cases h103_105 : V < 104
              · have he : V = 103 := by omega
                subst V
                exact row_20_103
              · have he : V = 104 := by omega
                subst V
                exact row_20_104
      · by_cases h105_120 : V < 112
        · by_cases h105_112 : V < 108
          · by_cases h105_108 : V < 106
            · have he : V = 105 := by omega
              subst V
              exact row_20_105
            · by_cases h106_108 : V < 107
              · have he : V = 106 := by omega
                subst V
                exact row_20_106
              · have he : V = 107 := by omega
                subst V
                exact row_20_107
          · by_cases h108_112 : V < 110
            · by_cases h108_110 : V < 109
              · have he : V = 108 := by omega
                subst V
                exact row_20_108
              · have he : V = 109 := by omega
                subst V
                exact row_20_109
            · by_cases h110_112 : V < 111
              · have he : V = 110 := by omega
                subst V
                exact row_20_110
              · have he : V = 111 := by omega
                subst V
                exact row_20_111
        · by_cases h112_120 : V < 116
          · by_cases h112_116 : V < 114
            · by_cases h112_114 : V < 113
              · have he : V = 112 := by omega
                subst V
                exact row_20_112
              · have he : V = 113 := by omega
                subst V
                exact row_20_113
            · by_cases h114_116 : V < 115
              · have he : V = 114 := by omega
                subst V
                exact row_20_114
              · have he : V = 115 := by omega
                subst V
                exact row_20_115
          · by_cases h116_120 : V < 118
            · by_cases h116_118 : V < 117
              · have he : V = 116 := by omega
                subst V
                exact row_20_116
              · have he : V = 117 := by omega
                subst V
                exact row_20_117
            · by_cases h118_120 : V < 119
              · have he : V = 118 := by omega
                subst V
                exact row_20_118
              · have he : V = 119 := by omega
                subst V
                exact row_20_119
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
