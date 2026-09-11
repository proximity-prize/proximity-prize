import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked08

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem cell_9_0_0 : C 9 0 0 := by decide +kernel
theorem cell_9_0_1 : C 9 0 1 := by decide +kernel
theorem cell_9_0_2 : C 9 0 2 := by decide +kernel
theorem cell_9_0_3 : C 9 0 3 := by decide +kernel
theorem cell_9_0_4 : C 9 0 4 := by decide +kernel
theorem cell_9_0_5 : C 9 0 5 := by decide +kernel
theorem row_9_0 : ThresholdAt 9 0 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 0 0 cell_9_0_0
  | exact S 9 0 1 cell_9_0_1
  | exact S 9 0 2 cell_9_0_2
  | exact S 9 0 3 cell_9_0_3
  | exact S 9 0 4 cell_9_0_4
  | exact S 9 0 5 cell_9_0_5
theorem cell_9_1_0 : C 9 1 0 := by decide +kernel
theorem cell_9_1_1 : C 9 1 1 := by decide +kernel
theorem cell_9_1_2 : C 9 1 2 := by decide +kernel
theorem cell_9_1_3 : C 9 1 3 := by decide +kernel
theorem cell_9_1_4 : C 9 1 4 := by decide +kernel
theorem cell_9_1_5 : C 9 1 5 := by decide +kernel
theorem row_9_1 : ThresholdAt 9 1 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 1 0 cell_9_1_0
  | exact S 9 1 1 cell_9_1_1
  | exact S 9 1 2 cell_9_1_2
  | exact S 9 1 3 cell_9_1_3
  | exact S 9 1 4 cell_9_1_4
  | exact S 9 1 5 cell_9_1_5
theorem cell_9_2_0 : C 9 2 0 := by decide +kernel
theorem cell_9_2_1 : C 9 2 1 := by decide +kernel
theorem cell_9_2_2 : C 9 2 2 := by decide +kernel
theorem cell_9_2_3 : C 9 2 3 := by decide +kernel
theorem cell_9_2_4 : C 9 2 4 := by decide +kernel
theorem cell_9_2_5 : C 9 2 5 := by decide +kernel
theorem row_9_2 : ThresholdAt 9 2 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 2 0 cell_9_2_0
  | exact S 9 2 1 cell_9_2_1
  | exact S 9 2 2 cell_9_2_2
  | exact S 9 2 3 cell_9_2_3
  | exact S 9 2 4 cell_9_2_4
  | exact S 9 2 5 cell_9_2_5
theorem cell_9_3_0 : C 9 3 0 := by decide +kernel
theorem cell_9_3_1 : C 9 3 1 := by decide +kernel
theorem cell_9_3_2 : C 9 3 2 := by decide +kernel
theorem cell_9_3_3 : C 9 3 3 := by decide +kernel
theorem cell_9_3_4 : C 9 3 4 := by decide +kernel
theorem cell_9_3_5 : C 9 3 5 := by decide +kernel
theorem row_9_3 : ThresholdAt 9 3 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 3 0 cell_9_3_0
  | exact S 9 3 1 cell_9_3_1
  | exact S 9 3 2 cell_9_3_2
  | exact S 9 3 3 cell_9_3_3
  | exact S 9 3 4 cell_9_3_4
  | exact S 9 3 5 cell_9_3_5
theorem cell_9_4_0 : C 9 4 0 := by decide +kernel
theorem cell_9_4_1 : C 9 4 1 := by decide +kernel
theorem cell_9_4_2 : C 9 4 2 := by decide +kernel
theorem cell_9_4_3 : C 9 4 3 := by decide +kernel
theorem cell_9_4_4 : C 9 4 4 := by decide +kernel
theorem cell_9_4_5 : C 9 4 5 := by decide +kernel
theorem row_9_4 : ThresholdAt 9 4 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 4 0 cell_9_4_0
  | exact S 9 4 1 cell_9_4_1
  | exact S 9 4 2 cell_9_4_2
  | exact S 9 4 3 cell_9_4_3
  | exact S 9 4 4 cell_9_4_4
  | exact S 9 4 5 cell_9_4_5
theorem cell_9_5_0 : C 9 5 0 := by decide +kernel
theorem cell_9_5_1 : C 9 5 1 := by decide +kernel
theorem cell_9_5_2 : C 9 5 2 := by decide +kernel
theorem cell_9_5_3 : C 9 5 3 := by decide +kernel
theorem cell_9_5_4 : C 9 5 4 := by decide +kernel
theorem cell_9_5_5 : C 9 5 5 := by decide +kernel
theorem row_9_5 : ThresholdAt 9 5 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 5 0 cell_9_5_0
  | exact S 9 5 1 cell_9_5_1
  | exact S 9 5 2 cell_9_5_2
  | exact S 9 5 3 cell_9_5_3
  | exact S 9 5 4 cell_9_5_4
  | exact S 9 5 5 cell_9_5_5
theorem cell_9_6_0 : C 9 6 0 := by decide +kernel
theorem cell_9_6_1 : C 9 6 1 := by decide +kernel
theorem cell_9_6_2 : C 9 6 2 := by decide +kernel
theorem cell_9_6_3 : C 9 6 3 := by decide +kernel
theorem cell_9_6_4 : C 9 6 4 := by decide +kernel
theorem cell_9_6_5 : C 9 6 5 := by decide +kernel
theorem row_9_6 : ThresholdAt 9 6 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 6 0 cell_9_6_0
  | exact S 9 6 1 cell_9_6_1
  | exact S 9 6 2 cell_9_6_2
  | exact S 9 6 3 cell_9_6_3
  | exact S 9 6 4 cell_9_6_4
  | exact S 9 6 5 cell_9_6_5
theorem cell_9_7_0 : C 9 7 0 := by decide +kernel
theorem cell_9_7_1 : C 9 7 1 := by decide +kernel
theorem cell_9_7_2 : C 9 7 2 := by decide +kernel
theorem cell_9_7_3 : C 9 7 3 := by decide +kernel
theorem cell_9_7_4 : C 9 7 4 := by decide +kernel
theorem cell_9_7_5 : C 9 7 5 := by decide +kernel
theorem row_9_7 : ThresholdAt 9 7 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 7 0 cell_9_7_0
  | exact S 9 7 1 cell_9_7_1
  | exact S 9 7 2 cell_9_7_2
  | exact S 9 7 3 cell_9_7_3
  | exact S 9 7 4 cell_9_7_4
  | exact S 9 7 5 cell_9_7_5
theorem cell_9_8_0 : C 9 8 0 := by decide +kernel
theorem cell_9_8_1 : C 9 8 1 := by decide +kernel
theorem cell_9_8_2 : C 9 8 2 := by decide +kernel
theorem cell_9_8_3 : C 9 8 3 := by decide +kernel
theorem cell_9_8_4 : C 9 8 4 := by decide +kernel
theorem cell_9_8_5 : C 9 8 5 := by decide +kernel
theorem row_9_8 : ThresholdAt 9 8 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 8 0 cell_9_8_0
  | exact S 9 8 1 cell_9_8_1
  | exact S 9 8 2 cell_9_8_2
  | exact S 9 8 3 cell_9_8_3
  | exact S 9 8 4 cell_9_8_4
  | exact S 9 8 5 cell_9_8_5
theorem cell_9_9_0 : C 9 9 0 := by decide +kernel
theorem cell_9_9_1 : C 9 9 1 := by decide +kernel
theorem cell_9_9_2 : C 9 9 2 := by decide +kernel
theorem cell_9_9_3 : C 9 9 3 := by decide +kernel
theorem cell_9_9_4 : C 9 9 4 := by decide +kernel
theorem cell_9_9_5 : C 9 9 5 := by decide +kernel
theorem row_9_9 : ThresholdAt 9 9 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 9 0 cell_9_9_0
  | exact S 9 9 1 cell_9_9_1
  | exact S 9 9 2 cell_9_9_2
  | exact S 9 9 3 cell_9_9_3
  | exact S 9 9 4 cell_9_9_4
  | exact S 9 9 5 cell_9_9_5
theorem cell_9_10_0 : C 9 10 0 := by decide +kernel
theorem cell_9_10_1 : C 9 10 1 := by decide +kernel
theorem cell_9_10_2 : C 9 10 2 := by decide +kernel
theorem cell_9_10_3 : C 9 10 3 := by decide +kernel
theorem cell_9_10_4 : C 9 10 4 := by decide +kernel
theorem cell_9_10_5 : C 9 10 5 := by decide +kernel
theorem row_9_10 : ThresholdAt 9 10 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 10 0 cell_9_10_0
  | exact S 9 10 1 cell_9_10_1
  | exact S 9 10 2 cell_9_10_2
  | exact S 9 10 3 cell_9_10_3
  | exact S 9 10 4 cell_9_10_4
  | exact S 9 10 5 cell_9_10_5
theorem cell_9_11_0 : C 9 11 0 := by decide +kernel
theorem cell_9_11_1 : C 9 11 1 := by decide +kernel
theorem cell_9_11_2 : C 9 11 2 := by decide +kernel
theorem cell_9_11_3 : C 9 11 3 := by decide +kernel
theorem cell_9_11_4 : C 9 11 4 := by decide +kernel
theorem cell_9_11_5 : C 9 11 5 := by decide +kernel
theorem row_9_11 : ThresholdAt 9 11 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 11 0 cell_9_11_0
  | exact S 9 11 1 cell_9_11_1
  | exact S 9 11 2 cell_9_11_2
  | exact S 9 11 3 cell_9_11_3
  | exact S 9 11 4 cell_9_11_4
  | exact S 9 11 5 cell_9_11_5
theorem cell_9_12_0 : C 9 12 0 := by decide +kernel
theorem cell_9_12_1 : C 9 12 1 := by decide +kernel
theorem cell_9_12_2 : C 9 12 2 := by decide +kernel
theorem cell_9_12_3 : C 9 12 3 := by decide +kernel
theorem cell_9_12_4 : C 9 12 4 := by decide +kernel
theorem cell_9_12_5 : C 9 12 5 := by decide +kernel
theorem row_9_12 : ThresholdAt 9 12 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 12 0 cell_9_12_0
  | exact S 9 12 1 cell_9_12_1
  | exact S 9 12 2 cell_9_12_2
  | exact S 9 12 3 cell_9_12_3
  | exact S 9 12 4 cell_9_12_4
  | exact S 9 12 5 cell_9_12_5
theorem cell_9_13_0 : C 9 13 0 := by decide +kernel
theorem cell_9_13_1 : C 9 13 1 := by decide +kernel
theorem cell_9_13_2 : C 9 13 2 := by decide +kernel
theorem cell_9_13_3 : C 9 13 3 := by decide +kernel
theorem cell_9_13_4 : C 9 13 4 := by decide +kernel
theorem cell_9_13_5 : C 9 13 5 := by decide +kernel
theorem row_9_13 : ThresholdAt 9 13 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 13 0 cell_9_13_0
  | exact S 9 13 1 cell_9_13_1
  | exact S 9 13 2 cell_9_13_2
  | exact S 9 13 3 cell_9_13_3
  | exact S 9 13 4 cell_9_13_4
  | exact S 9 13 5 cell_9_13_5
theorem cell_9_14_0 : C 9 14 0 := by decide +kernel
theorem cell_9_14_1 : C 9 14 1 := by decide +kernel
theorem cell_9_14_2 : C 9 14 2 := by decide +kernel
theorem cell_9_14_3 : C 9 14 3 := by decide +kernel
theorem cell_9_14_4 : C 9 14 4 := by decide +kernel
theorem cell_9_14_5 : C 9 14 5 := by decide +kernel
theorem row_9_14 : ThresholdAt 9 14 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 14 0 cell_9_14_0
  | exact S 9 14 1 cell_9_14_1
  | exact S 9 14 2 cell_9_14_2
  | exact S 9 14 3 cell_9_14_3
  | exact S 9 14 4 cell_9_14_4
  | exact S 9 14 5 cell_9_14_5
theorem cell_9_15_0 : C 9 15 0 := by decide +kernel
theorem cell_9_15_1 : C 9 15 1 := by decide +kernel
theorem cell_9_15_2 : C 9 15 2 := by decide +kernel
theorem cell_9_15_3 : C 9 15 3 := by decide +kernel
theorem cell_9_15_4 : C 9 15 4 := by decide +kernel
theorem cell_9_15_5 : C 9 15 5 := by decide +kernel
theorem row_9_15 : ThresholdAt 9 15 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 15 0 cell_9_15_0
  | exact S 9 15 1 cell_9_15_1
  | exact S 9 15 2 cell_9_15_2
  | exact S 9 15 3 cell_9_15_3
  | exact S 9 15 4 cell_9_15_4
  | exact S 9 15 5 cell_9_15_5
theorem cell_9_16_0 : C 9 16 0 := by decide +kernel
theorem cell_9_16_1 : C 9 16 1 := by decide +kernel
theorem cell_9_16_2 : C 9 16 2 := by decide +kernel
theorem cell_9_16_3 : C 9 16 3 := by decide +kernel
theorem cell_9_16_4 : C 9 16 4 := by decide +kernel
theorem cell_9_16_5 : C 9 16 5 := by decide +kernel
theorem row_9_16 : ThresholdAt 9 16 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 16 0 cell_9_16_0
  | exact S 9 16 1 cell_9_16_1
  | exact S 9 16 2 cell_9_16_2
  | exact S 9 16 3 cell_9_16_3
  | exact S 9 16 4 cell_9_16_4
  | exact S 9 16 5 cell_9_16_5
theorem cell_9_17_0 : C 9 17 0 := by decide +kernel
theorem cell_9_17_1 : C 9 17 1 := by decide +kernel
theorem cell_9_17_2 : C 9 17 2 := by decide +kernel
theorem cell_9_17_3 : C 9 17 3 := by decide +kernel
theorem cell_9_17_4 : C 9 17 4 := by decide +kernel
theorem cell_9_17_5 : C 9 17 5 := by decide +kernel
theorem row_9_17 : ThresholdAt 9 17 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 17 0 cell_9_17_0
  | exact S 9 17 1 cell_9_17_1
  | exact S 9 17 2 cell_9_17_2
  | exact S 9 17 3 cell_9_17_3
  | exact S 9 17 4 cell_9_17_4
  | exact S 9 17 5 cell_9_17_5
theorem cell_9_18_0 : C 9 18 0 := by decide +kernel
theorem cell_9_18_1 : C 9 18 1 := by decide +kernel
theorem cell_9_18_2 : C 9 18 2 := by decide +kernel
theorem cell_9_18_3 : C 9 18 3 := by decide +kernel
theorem cell_9_18_4 : C 9 18 4 := by decide +kernel
theorem cell_9_18_5 : C 9 18 5 := by decide +kernel
theorem row_9_18 : ThresholdAt 9 18 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 18 0 cell_9_18_0
  | exact S 9 18 1 cell_9_18_1
  | exact S 9 18 2 cell_9_18_2
  | exact S 9 18 3 cell_9_18_3
  | exact S 9 18 4 cell_9_18_4
  | exact S 9 18 5 cell_9_18_5
theorem cell_9_19_0 : C 9 19 0 := by decide +kernel
theorem cell_9_19_1 : C 9 19 1 := by decide +kernel
theorem cell_9_19_2 : C 9 19 2 := by decide +kernel
theorem cell_9_19_3 : C 9 19 3 := by decide +kernel
theorem cell_9_19_4 : C 9 19 4 := by decide +kernel
theorem cell_9_19_5 : C 9 19 5 := by decide +kernel
theorem row_9_19 : ThresholdAt 9 19 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 19 0 cell_9_19_0
  | exact S 9 19 1 cell_9_19_1
  | exact S 9 19 2 cell_9_19_2
  | exact S 9 19 3 cell_9_19_3
  | exact S 9 19 4 cell_9_19_4
  | exact S 9 19 5 cell_9_19_5
theorem cell_9_20_0 : C 9 20 0 := by decide +kernel
theorem cell_9_20_1 : C 9 20 1 := by decide +kernel
theorem cell_9_20_2 : C 9 20 2 := by decide +kernel
theorem cell_9_20_3 : C 9 20 3 := by decide +kernel
theorem cell_9_20_4 : C 9 20 4 := by decide +kernel
theorem cell_9_20_5 : C 9 20 5 := by decide +kernel
theorem row_9_20 : ThresholdAt 9 20 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 20 0 cell_9_20_0
  | exact S 9 20 1 cell_9_20_1
  | exact S 9 20 2 cell_9_20_2
  | exact S 9 20 3 cell_9_20_3
  | exact S 9 20 4 cell_9_20_4
  | exact S 9 20 5 cell_9_20_5
theorem cell_9_21_0 : C 9 21 0 := by decide +kernel
theorem cell_9_21_1 : C 9 21 1 := by decide +kernel
theorem cell_9_21_2 : C 9 21 2 := by decide +kernel
theorem cell_9_21_3 : C 9 21 3 := by decide +kernel
theorem cell_9_21_4 : C 9 21 4 := by decide +kernel
theorem cell_9_21_5 : C 9 21 5 := by decide +kernel
theorem row_9_21 : ThresholdAt 9 21 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 21 0 cell_9_21_0
  | exact S 9 21 1 cell_9_21_1
  | exact S 9 21 2 cell_9_21_2
  | exact S 9 21 3 cell_9_21_3
  | exact S 9 21 4 cell_9_21_4
  | exact S 9 21 5 cell_9_21_5
theorem cell_9_22_0 : C 9 22 0 := by decide +kernel
theorem cell_9_22_1 : C 9 22 1 := by decide +kernel
theorem cell_9_22_2 : C 9 22 2 := by decide +kernel
theorem cell_9_22_3 : C 9 22 3 := by decide +kernel
theorem cell_9_22_4 : C 9 22 4 := by decide +kernel
theorem cell_9_22_5 : C 9 22 5 := by decide +kernel
theorem row_9_22 : ThresholdAt 9 22 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 22 0 cell_9_22_0
  | exact S 9 22 1 cell_9_22_1
  | exact S 9 22 2 cell_9_22_2
  | exact S 9 22 3 cell_9_22_3
  | exact S 9 22 4 cell_9_22_4
  | exact S 9 22 5 cell_9_22_5
theorem cell_9_23_0 : C 9 23 0 := by decide +kernel
theorem cell_9_23_1 : C 9 23 1 := by decide +kernel
theorem cell_9_23_2 : C 9 23 2 := by decide +kernel
theorem cell_9_23_3 : C 9 23 3 := by decide +kernel
theorem cell_9_23_4 : C 9 23 4 := by decide +kernel
theorem cell_9_23_5 : C 9 23 5 := by decide +kernel
theorem row_9_23 : ThresholdAt 9 23 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 23 0 cell_9_23_0
  | exact S 9 23 1 cell_9_23_1
  | exact S 9 23 2 cell_9_23_2
  | exact S 9 23 3 cell_9_23_3
  | exact S 9 23 4 cell_9_23_4
  | exact S 9 23 5 cell_9_23_5
theorem cell_9_24_0 : C 9 24 0 := by decide +kernel
theorem cell_9_24_1 : C 9 24 1 := by decide +kernel
theorem cell_9_24_2 : C 9 24 2 := by decide +kernel
theorem cell_9_24_3 : C 9 24 3 := by decide +kernel
theorem cell_9_24_4 : C 9 24 4 := by decide +kernel
theorem cell_9_24_5 : C 9 24 5 := by decide +kernel
theorem row_9_24 : ThresholdAt 9 24 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 24 0 cell_9_24_0
  | exact S 9 24 1 cell_9_24_1
  | exact S 9 24 2 cell_9_24_2
  | exact S 9 24 3 cell_9_24_3
  | exact S 9 24 4 cell_9_24_4
  | exact S 9 24 5 cell_9_24_5
theorem cell_9_25_0 : C 9 25 0 := by decide +kernel
theorem cell_9_25_1 : C 9 25 1 := by decide +kernel
theorem cell_9_25_2 : C 9 25 2 := by decide +kernel
theorem cell_9_25_3 : C 9 25 3 := by decide +kernel
theorem cell_9_25_4 : C 9 25 4 := by decide +kernel
theorem cell_9_25_5 : C 9 25 5 := by decide +kernel
theorem row_9_25 : ThresholdAt 9 25 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 25 0 cell_9_25_0
  | exact S 9 25 1 cell_9_25_1
  | exact S 9 25 2 cell_9_25_2
  | exact S 9 25 3 cell_9_25_3
  | exact S 9 25 4 cell_9_25_4
  | exact S 9 25 5 cell_9_25_5
theorem cell_9_26_0 : C 9 26 0 := by decide +kernel
theorem cell_9_26_1 : C 9 26 1 := by decide +kernel
theorem cell_9_26_2 : C 9 26 2 := by decide +kernel
theorem cell_9_26_3 : C 9 26 3 := by decide +kernel
theorem cell_9_26_4 : C 9 26 4 := by decide +kernel
theorem cell_9_26_5 : C 9 26 5 := by decide +kernel
theorem row_9_26 : ThresholdAt 9 26 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 26 0 cell_9_26_0
  | exact S 9 26 1 cell_9_26_1
  | exact S 9 26 2 cell_9_26_2
  | exact S 9 26 3 cell_9_26_3
  | exact S 9 26 4 cell_9_26_4
  | exact S 9 26 5 cell_9_26_5
theorem cell_9_27_0 : C 9 27 0 := by decide +kernel
theorem cell_9_27_1 : C 9 27 1 := by decide +kernel
theorem cell_9_27_2 : C 9 27 2 := by decide +kernel
theorem cell_9_27_3 : C 9 27 3 := by decide +kernel
theorem cell_9_27_4 : C 9 27 4 := by decide +kernel
theorem cell_9_27_5 : C 9 27 5 := by decide +kernel
theorem row_9_27 : ThresholdAt 9 27 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 27 0 cell_9_27_0
  | exact S 9 27 1 cell_9_27_1
  | exact S 9 27 2 cell_9_27_2
  | exact S 9 27 3 cell_9_27_3
  | exact S 9 27 4 cell_9_27_4
  | exact S 9 27 5 cell_9_27_5
theorem cell_9_28_0 : C 9 28 0 := by decide +kernel
theorem cell_9_28_1 : C 9 28 1 := by decide +kernel
theorem cell_9_28_2 : C 9 28 2 := by decide +kernel
theorem cell_9_28_3 : C 9 28 3 := by decide +kernel
theorem cell_9_28_4 : C 9 28 4 := by decide +kernel
theorem cell_9_28_5 : C 9 28 5 := by decide +kernel
theorem row_9_28 : ThresholdAt 9 28 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 28 0 cell_9_28_0
  | exact S 9 28 1 cell_9_28_1
  | exact S 9 28 2 cell_9_28_2
  | exact S 9 28 3 cell_9_28_3
  | exact S 9 28 4 cell_9_28_4
  | exact S 9 28 5 cell_9_28_5
theorem cell_9_29_0 : C 9 29 0 := by decide +kernel
theorem cell_9_29_1 : C 9 29 1 := by decide +kernel
theorem cell_9_29_2 : C 9 29 2 := by decide +kernel
theorem cell_9_29_3 : C 9 29 3 := by decide +kernel
theorem cell_9_29_4 : C 9 29 4 := by decide +kernel
theorem cell_9_29_5 : C 9 29 5 := by decide +kernel
theorem row_9_29 : ThresholdAt 9 29 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 29 0 cell_9_29_0
  | exact S 9 29 1 cell_9_29_1
  | exact S 9 29 2 cell_9_29_2
  | exact S 9 29 3 cell_9_29_3
  | exact S 9 29 4 cell_9_29_4
  | exact S 9 29 5 cell_9_29_5
theorem cell_9_30_0 : C 9 30 0 := by decide +kernel
theorem cell_9_30_1 : C 9 30 1 := by decide +kernel
theorem cell_9_30_2 : C 9 30 2 := by decide +kernel
theorem cell_9_30_3 : C 9 30 3 := by decide +kernel
theorem cell_9_30_4 : C 9 30 4 := by decide +kernel
theorem cell_9_30_5 : C 9 30 5 := by decide +kernel
theorem row_9_30 : ThresholdAt 9 30 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 30 0 cell_9_30_0
  | exact S 9 30 1 cell_9_30_1
  | exact S 9 30 2 cell_9_30_2
  | exact S 9 30 3 cell_9_30_3
  | exact S 9 30 4 cell_9_30_4
  | exact S 9 30 5 cell_9_30_5
theorem cell_9_31_0 : C 9 31 0 := by decide +kernel
theorem cell_9_31_1 : C 9 31 1 := by decide +kernel
theorem cell_9_31_2 : C 9 31 2 := by decide +kernel
theorem cell_9_31_3 : C 9 31 3 := by decide +kernel
theorem cell_9_31_4 : C 9 31 4 := by decide +kernel
theorem cell_9_31_5 : C 9 31 5 := by decide +kernel
theorem row_9_31 : ThresholdAt 9 31 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 31 0 cell_9_31_0
  | exact S 9 31 1 cell_9_31_1
  | exact S 9 31 2 cell_9_31_2
  | exact S 9 31 3 cell_9_31_3
  | exact S 9 31 4 cell_9_31_4
  | exact S 9 31 5 cell_9_31_5
theorem cell_9_32_0 : C 9 32 0 := by decide +kernel
theorem cell_9_32_1 : C 9 32 1 := by decide +kernel
theorem cell_9_32_2 : C 9 32 2 := by decide +kernel
theorem cell_9_32_3 : C 9 32 3 := by decide +kernel
theorem cell_9_32_4 : C 9 32 4 := by decide +kernel
theorem cell_9_32_5 : C 9 32 5 := by decide +kernel
theorem row_9_32 : ThresholdAt 9 32 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 32 0 cell_9_32_0
  | exact S 9 32 1 cell_9_32_1
  | exact S 9 32 2 cell_9_32_2
  | exact S 9 32 3 cell_9_32_3
  | exact S 9 32 4 cell_9_32_4
  | exact S 9 32 5 cell_9_32_5
theorem cell_9_33_0 : C 9 33 0 := by decide +kernel
theorem cell_9_33_1 : C 9 33 1 := by decide +kernel
theorem cell_9_33_2 : C 9 33 2 := by decide +kernel
theorem cell_9_33_3 : C 9 33 3 := by decide +kernel
theorem cell_9_33_4 : C 9 33 4 := by decide +kernel
theorem cell_9_33_5 : C 9 33 5 := by decide +kernel
theorem row_9_33 : ThresholdAt 9 33 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 33 0 cell_9_33_0
  | exact S 9 33 1 cell_9_33_1
  | exact S 9 33 2 cell_9_33_2
  | exact S 9 33 3 cell_9_33_3
  | exact S 9 33 4 cell_9_33_4
  | exact S 9 33 5 cell_9_33_5
theorem cell_9_34_0 : C 9 34 0 := by decide +kernel
theorem cell_9_34_1 : C 9 34 1 := by decide +kernel
theorem cell_9_34_2 : C 9 34 2 := by decide +kernel
theorem cell_9_34_3 : C 9 34 3 := by decide +kernel
theorem cell_9_34_4 : C 9 34 4 := by decide +kernel
theorem cell_9_34_5 : C 9 34 5 := by decide +kernel
theorem row_9_34 : ThresholdAt 9 34 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 34 0 cell_9_34_0
  | exact S 9 34 1 cell_9_34_1
  | exact S 9 34 2 cell_9_34_2
  | exact S 9 34 3 cell_9_34_3
  | exact S 9 34 4 cell_9_34_4
  | exact S 9 34 5 cell_9_34_5
theorem cell_9_35_0 : C 9 35 0 := by decide +kernel
theorem cell_9_35_1 : C 9 35 1 := by decide +kernel
theorem cell_9_35_2 : C 9 35 2 := by decide +kernel
theorem cell_9_35_3 : C 9 35 3 := by decide +kernel
theorem cell_9_35_4 : C 9 35 4 := by decide +kernel
theorem cell_9_35_5 : C 9 35 5 := by decide +kernel
theorem row_9_35 : ThresholdAt 9 35 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 35 0 cell_9_35_0
  | exact S 9 35 1 cell_9_35_1
  | exact S 9 35 2 cell_9_35_2
  | exact S 9 35 3 cell_9_35_3
  | exact S 9 35 4 cell_9_35_4
  | exact S 9 35 5 cell_9_35_5
theorem cell_9_36_0 : C 9 36 0 := by decide +kernel
theorem cell_9_36_1 : C 9 36 1 := by decide +kernel
theorem cell_9_36_2 : C 9 36 2 := by decide +kernel
theorem cell_9_36_3 : C 9 36 3 := by decide +kernel
theorem cell_9_36_4 : C 9 36 4 := by decide +kernel
theorem cell_9_36_5 : C 9 36 5 := by decide +kernel
theorem row_9_36 : ThresholdAt 9 36 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 36 0 cell_9_36_0
  | exact S 9 36 1 cell_9_36_1
  | exact S 9 36 2 cell_9_36_2
  | exact S 9 36 3 cell_9_36_3
  | exact S 9 36 4 cell_9_36_4
  | exact S 9 36 5 cell_9_36_5
theorem cell_9_37_0 : C 9 37 0 := by decide +kernel
theorem cell_9_37_1 : C 9 37 1 := by decide +kernel
theorem cell_9_37_2 : C 9 37 2 := by decide +kernel
theorem cell_9_37_3 : C 9 37 3 := by decide +kernel
theorem cell_9_37_4 : C 9 37 4 := by decide +kernel
theorem cell_9_37_5 : C 9 37 5 := by decide +kernel
theorem row_9_37 : ThresholdAt 9 37 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 37 0 cell_9_37_0
  | exact S 9 37 1 cell_9_37_1
  | exact S 9 37 2 cell_9_37_2
  | exact S 9 37 3 cell_9_37_3
  | exact S 9 37 4 cell_9_37_4
  | exact S 9 37 5 cell_9_37_5
theorem cell_9_38_0 : C 9 38 0 := by decide +kernel
theorem cell_9_38_1 : C 9 38 1 := by decide +kernel
theorem cell_9_38_2 : C 9 38 2 := by decide +kernel
theorem cell_9_38_3 : C 9 38 3 := by decide +kernel
theorem cell_9_38_4 : C 9 38 4 := by decide +kernel
theorem cell_9_38_5 : C 9 38 5 := by decide +kernel
theorem row_9_38 : ThresholdAt 9 38 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 38 0 cell_9_38_0
  | exact S 9 38 1 cell_9_38_1
  | exact S 9 38 2 cell_9_38_2
  | exact S 9 38 3 cell_9_38_3
  | exact S 9 38 4 cell_9_38_4
  | exact S 9 38 5 cell_9_38_5
theorem cell_9_39_0 : C 9 39 0 := by decide +kernel
theorem cell_9_39_1 : C 9 39 1 := by decide +kernel
theorem cell_9_39_2 : C 9 39 2 := by decide +kernel
theorem cell_9_39_3 : C 9 39 3 := by decide +kernel
theorem cell_9_39_4 : C 9 39 4 := by decide +kernel
theorem cell_9_39_5 : C 9 39 5 := by decide +kernel
theorem row_9_39 : ThresholdAt 9 39 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 39 0 cell_9_39_0
  | exact S 9 39 1 cell_9_39_1
  | exact S 9 39 2 cell_9_39_2
  | exact S 9 39 3 cell_9_39_3
  | exact S 9 39 4 cell_9_39_4
  | exact S 9 39 5 cell_9_39_5
theorem cell_9_40_0 : C 9 40 0 := by decide +kernel
theorem cell_9_40_1 : C 9 40 1 := by decide +kernel
theorem cell_9_40_2 : C 9 40 2 := by decide +kernel
theorem cell_9_40_3 : C 9 40 3 := by decide +kernel
theorem cell_9_40_4 : C 9 40 4 := by decide +kernel
theorem cell_9_40_5 : C 9 40 5 := by decide +kernel
theorem row_9_40 : ThresholdAt 9 40 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 40 0 cell_9_40_0
  | exact S 9 40 1 cell_9_40_1
  | exact S 9 40 2 cell_9_40_2
  | exact S 9 40 3 cell_9_40_3
  | exact S 9 40 4 cell_9_40_4
  | exact S 9 40 5 cell_9_40_5
theorem cell_9_41_0 : C 9 41 0 := by decide +kernel
theorem cell_9_41_1 : C 9 41 1 := by decide +kernel
theorem cell_9_41_2 : C 9 41 2 := by decide +kernel
theorem cell_9_41_3 : C 9 41 3 := by decide +kernel
theorem cell_9_41_4 : C 9 41 4 := by decide +kernel
theorem cell_9_41_5 : C 9 41 5 := by decide +kernel
theorem row_9_41 : ThresholdAt 9 41 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 41 0 cell_9_41_0
  | exact S 9 41 1 cell_9_41_1
  | exact S 9 41 2 cell_9_41_2
  | exact S 9 41 3 cell_9_41_3
  | exact S 9 41 4 cell_9_41_4
  | exact S 9 41 5 cell_9_41_5
theorem cell_9_42_0 : C 9 42 0 := by decide +kernel
theorem cell_9_42_1 : C 9 42 1 := by decide +kernel
theorem cell_9_42_2 : C 9 42 2 := by decide +kernel
theorem cell_9_42_3 : C 9 42 3 := by decide +kernel
theorem cell_9_42_4 : C 9 42 4 := by decide +kernel
theorem cell_9_42_5 : C 9 42 5 := by decide +kernel
theorem row_9_42 : ThresholdAt 9 42 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 42 0 cell_9_42_0
  | exact S 9 42 1 cell_9_42_1
  | exact S 9 42 2 cell_9_42_2
  | exact S 9 42 3 cell_9_42_3
  | exact S 9 42 4 cell_9_42_4
  | exact S 9 42 5 cell_9_42_5
theorem cell_9_43_0 : C 9 43 0 := by decide +kernel
theorem cell_9_43_1 : C 9 43 1 := by decide +kernel
theorem cell_9_43_2 : C 9 43 2 := by decide +kernel
theorem cell_9_43_3 : C 9 43 3 := by decide +kernel
theorem cell_9_43_4 : C 9 43 4 := by decide +kernel
theorem cell_9_43_5 : C 9 43 5 := by decide +kernel
theorem row_9_43 : ThresholdAt 9 43 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 43 0 cell_9_43_0
  | exact S 9 43 1 cell_9_43_1
  | exact S 9 43 2 cell_9_43_2
  | exact S 9 43 3 cell_9_43_3
  | exact S 9 43 4 cell_9_43_4
  | exact S 9 43 5 cell_9_43_5
theorem cell_9_44_0 : C 9 44 0 := by decide +kernel
theorem cell_9_44_1 : C 9 44 1 := by decide +kernel
theorem cell_9_44_2 : C 9 44 2 := by decide +kernel
theorem cell_9_44_3 : C 9 44 3 := by decide +kernel
theorem cell_9_44_4 : C 9 44 4 := by decide +kernel
theorem cell_9_44_5 : C 9 44 5 := by decide +kernel
theorem row_9_44 : ThresholdAt 9 44 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 44 0 cell_9_44_0
  | exact S 9 44 1 cell_9_44_1
  | exact S 9 44 2 cell_9_44_2
  | exact S 9 44 3 cell_9_44_3
  | exact S 9 44 4 cell_9_44_4
  | exact S 9 44 5 cell_9_44_5
theorem cell_9_45_0 : C 9 45 0 := by decide +kernel
theorem cell_9_45_1 : C 9 45 1 := by decide +kernel
theorem cell_9_45_2 : C 9 45 2 := by decide +kernel
theorem cell_9_45_3 : C 9 45 3 := by decide +kernel
theorem cell_9_45_4 : C 9 45 4 := by decide +kernel
theorem cell_9_45_5 : C 9 45 5 := by decide +kernel
theorem row_9_45 : ThresholdAt 9 45 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 45 0 cell_9_45_0
  | exact S 9 45 1 cell_9_45_1
  | exact S 9 45 2 cell_9_45_2
  | exact S 9 45 3 cell_9_45_3
  | exact S 9 45 4 cell_9_45_4
  | exact S 9 45 5 cell_9_45_5
theorem cell_9_46_0 : C 9 46 0 := by decide +kernel
theorem cell_9_46_1 : C 9 46 1 := by decide +kernel
theorem cell_9_46_2 : C 9 46 2 := by decide +kernel
theorem cell_9_46_3 : C 9 46 3 := by decide +kernel
theorem cell_9_46_4 : C 9 46 4 := by decide +kernel
theorem cell_9_46_5 : C 9 46 5 := by decide +kernel
theorem row_9_46 : ThresholdAt 9 46 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 46 0 cell_9_46_0
  | exact S 9 46 1 cell_9_46_1
  | exact S 9 46 2 cell_9_46_2
  | exact S 9 46 3 cell_9_46_3
  | exact S 9 46 4 cell_9_46_4
  | exact S 9 46 5 cell_9_46_5
theorem cell_9_47_0 : C 9 47 0 := by decide +kernel
theorem cell_9_47_1 : C 9 47 1 := by decide +kernel
theorem cell_9_47_2 : C 9 47 2 := by decide +kernel
theorem cell_9_47_3 : C 9 47 3 := by decide +kernel
theorem cell_9_47_4 : C 9 47 4 := by decide +kernel
theorem cell_9_47_5 : C 9 47 5 := by decide +kernel
theorem row_9_47 : ThresholdAt 9 47 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 47 0 cell_9_47_0
  | exact S 9 47 1 cell_9_47_1
  | exact S 9 47 2 cell_9_47_2
  | exact S 9 47 3 cell_9_47_3
  | exact S 9 47 4 cell_9_47_4
  | exact S 9 47 5 cell_9_47_5
theorem cell_9_48_0 : C 9 48 0 := by decide +kernel
theorem cell_9_48_1 : C 9 48 1 := by decide +kernel
theorem cell_9_48_2 : C 9 48 2 := by decide +kernel
theorem cell_9_48_3 : C 9 48 3 := by decide +kernel
theorem cell_9_48_4 : C 9 48 4 := by decide +kernel
theorem cell_9_48_5 : C 9 48 5 := by decide +kernel
theorem row_9_48 : ThresholdAt 9 48 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 48 0 cell_9_48_0
  | exact S 9 48 1 cell_9_48_1
  | exact S 9 48 2 cell_9_48_2
  | exact S 9 48 3 cell_9_48_3
  | exact S 9 48 4 cell_9_48_4
  | exact S 9 48 5 cell_9_48_5
theorem cell_9_49_0 : C 9 49 0 := by decide +kernel
theorem cell_9_49_1 : C 9 49 1 := by decide +kernel
theorem cell_9_49_2 : C 9 49 2 := by decide +kernel
theorem cell_9_49_3 : C 9 49 3 := by decide +kernel
theorem cell_9_49_4 : C 9 49 4 := by decide +kernel
theorem cell_9_49_5 : C 9 49 5 := by decide +kernel
theorem row_9_49 : ThresholdAt 9 49 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 49 0 cell_9_49_0
  | exact S 9 49 1 cell_9_49_1
  | exact S 9 49 2 cell_9_49_2
  | exact S 9 49 3 cell_9_49_3
  | exact S 9 49 4 cell_9_49_4
  | exact S 9 49 5 cell_9_49_5
theorem cell_9_50_0 : C 9 50 0 := by decide +kernel
theorem cell_9_50_1 : C 9 50 1 := by decide +kernel
theorem cell_9_50_2 : C 9 50 2 := by decide +kernel
theorem cell_9_50_3 : C 9 50 3 := by decide +kernel
theorem cell_9_50_4 : C 9 50 4 := by decide +kernel
theorem cell_9_50_5 : C 9 50 5 := by decide +kernel
theorem row_9_50 : ThresholdAt 9 50 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 50 0 cell_9_50_0
  | exact S 9 50 1 cell_9_50_1
  | exact S 9 50 2 cell_9_50_2
  | exact S 9 50 3 cell_9_50_3
  | exact S 9 50 4 cell_9_50_4
  | exact S 9 50 5 cell_9_50_5
theorem cell_9_51_0 : C 9 51 0 := by decide +kernel
theorem cell_9_51_1 : C 9 51 1 := by decide +kernel
theorem cell_9_51_2 : C 9 51 2 := by decide +kernel
theorem cell_9_51_3 : C 9 51 3 := by decide +kernel
theorem cell_9_51_4 : C 9 51 4 := by decide +kernel
theorem cell_9_51_5 : C 9 51 5 := by decide +kernel
theorem row_9_51 : ThresholdAt 9 51 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 51 0 cell_9_51_0
  | exact S 9 51 1 cell_9_51_1
  | exact S 9 51 2 cell_9_51_2
  | exact S 9 51 3 cell_9_51_3
  | exact S 9 51 4 cell_9_51_4
  | exact S 9 51 5 cell_9_51_5
theorem cell_9_52_0 : C 9 52 0 := by decide +kernel
theorem cell_9_52_1 : C 9 52 1 := by decide +kernel
theorem cell_9_52_2 : C 9 52 2 := by decide +kernel
theorem cell_9_52_3 : C 9 52 3 := by decide +kernel
theorem cell_9_52_4 : C 9 52 4 := by decide +kernel
theorem cell_9_52_5 : C 9 52 5 := by decide +kernel
theorem row_9_52 : ThresholdAt 9 52 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 52 0 cell_9_52_0
  | exact S 9 52 1 cell_9_52_1
  | exact S 9 52 2 cell_9_52_2
  | exact S 9 52 3 cell_9_52_3
  | exact S 9 52 4 cell_9_52_4
  | exact S 9 52 5 cell_9_52_5
theorem cell_9_53_0 : C 9 53 0 := by decide +kernel
theorem cell_9_53_1 : C 9 53 1 := by decide +kernel
theorem cell_9_53_2 : C 9 53 2 := by decide +kernel
theorem cell_9_53_3 : C 9 53 3 := by decide +kernel
theorem cell_9_53_4 : C 9 53 4 := by decide +kernel
theorem cell_9_53_5 : C 9 53 5 := by decide +kernel
theorem row_9_53 : ThresholdAt 9 53 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 53 0 cell_9_53_0
  | exact S 9 53 1 cell_9_53_1
  | exact S 9 53 2 cell_9_53_2
  | exact S 9 53 3 cell_9_53_3
  | exact S 9 53 4 cell_9_53_4
  | exact S 9 53 5 cell_9_53_5
theorem cell_9_54_0 : C 9 54 0 := by decide +kernel
theorem cell_9_54_1 : C 9 54 1 := by decide +kernel
theorem cell_9_54_2 : C 9 54 2 := by decide +kernel
theorem cell_9_54_3 : C 9 54 3 := by decide +kernel
theorem cell_9_54_4 : C 9 54 4 := by decide +kernel
theorem cell_9_54_5 : C 9 54 5 := by decide +kernel
theorem row_9_54 : ThresholdAt 9 54 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 54 0 cell_9_54_0
  | exact S 9 54 1 cell_9_54_1
  | exact S 9 54 2 cell_9_54_2
  | exact S 9 54 3 cell_9_54_3
  | exact S 9 54 4 cell_9_54_4
  | exact S 9 54 5 cell_9_54_5
theorem cell_9_55_0 : C 9 55 0 := by decide +kernel
theorem cell_9_55_1 : C 9 55 1 := by decide +kernel
theorem cell_9_55_2 : C 9 55 2 := by decide +kernel
theorem cell_9_55_3 : C 9 55 3 := by decide +kernel
theorem cell_9_55_4 : C 9 55 4 := by decide +kernel
theorem cell_9_55_5 : C 9 55 5 := by decide +kernel
theorem row_9_55 : ThresholdAt 9 55 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 55 0 cell_9_55_0
  | exact S 9 55 1 cell_9_55_1
  | exact S 9 55 2 cell_9_55_2
  | exact S 9 55 3 cell_9_55_3
  | exact S 9 55 4 cell_9_55_4
  | exact S 9 55 5 cell_9_55_5
theorem cell_9_56_0 : C 9 56 0 := by decide +kernel
theorem cell_9_56_1 : C 9 56 1 := by decide +kernel
theorem cell_9_56_2 : C 9 56 2 := by decide +kernel
theorem cell_9_56_3 : C 9 56 3 := by decide +kernel
theorem cell_9_56_4 : C 9 56 4 := by decide +kernel
theorem cell_9_56_5 : C 9 56 5 := by decide +kernel
theorem row_9_56 : ThresholdAt 9 56 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 56 0 cell_9_56_0
  | exact S 9 56 1 cell_9_56_1
  | exact S 9 56 2 cell_9_56_2
  | exact S 9 56 3 cell_9_56_3
  | exact S 9 56 4 cell_9_56_4
  | exact S 9 56 5 cell_9_56_5
theorem cell_9_57_0 : C 9 57 0 := by decide +kernel
theorem cell_9_57_1 : C 9 57 1 := by decide +kernel
theorem cell_9_57_2 : C 9 57 2 := by decide +kernel
theorem cell_9_57_3 : C 9 57 3 := by decide +kernel
theorem cell_9_57_4 : C 9 57 4 := by decide +kernel
theorem cell_9_57_5 : C 9 57 5 := by decide +kernel
theorem row_9_57 : ThresholdAt 9 57 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 57 0 cell_9_57_0
  | exact S 9 57 1 cell_9_57_1
  | exact S 9 57 2 cell_9_57_2
  | exact S 9 57 3 cell_9_57_3
  | exact S 9 57 4 cell_9_57_4
  | exact S 9 57 5 cell_9_57_5
theorem cell_9_58_0 : C 9 58 0 := by decide +kernel
theorem cell_9_58_1 : C 9 58 1 := by decide +kernel
theorem cell_9_58_2 : C 9 58 2 := by decide +kernel
theorem cell_9_58_3 : C 9 58 3 := by decide +kernel
theorem cell_9_58_4 : C 9 58 4 := by decide +kernel
theorem cell_9_58_5 : C 9 58 5 := by decide +kernel
theorem row_9_58 : ThresholdAt 9 58 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 58 0 cell_9_58_0
  | exact S 9 58 1 cell_9_58_1
  | exact S 9 58 2 cell_9_58_2
  | exact S 9 58 3 cell_9_58_3
  | exact S 9 58 4 cell_9_58_4
  | exact S 9 58 5 cell_9_58_5
theorem cell_9_59_0 : C 9 59 0 := by decide +kernel
theorem cell_9_59_1 : C 9 59 1 := by decide +kernel
theorem cell_9_59_2 : C 9 59 2 := by decide +kernel
theorem cell_9_59_3 : C 9 59 3 := by decide +kernel
theorem cell_9_59_4 : C 9 59 4 := by decide +kernel
theorem cell_9_59_5 : C 9 59 5 := by decide +kernel
theorem row_9_59 : ThresholdAt 9 59 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 59 0 cell_9_59_0
  | exact S 9 59 1 cell_9_59_1
  | exact S 9 59 2 cell_9_59_2
  | exact S 9 59 3 cell_9_59_3
  | exact S 9 59 4 cell_9_59_4
  | exact S 9 59 5 cell_9_59_5
theorem cell_9_60_0 : C 9 60 0 := by decide +kernel
theorem cell_9_60_1 : C 9 60 1 := by decide +kernel
theorem cell_9_60_2 : C 9 60 2 := by decide +kernel
theorem cell_9_60_3 : C 9 60 3 := by decide +kernel
theorem cell_9_60_4 : C 9 60 4 := by decide +kernel
theorem cell_9_60_5 : C 9 60 5 := by decide +kernel
theorem row_9_60 : ThresholdAt 9 60 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 60 0 cell_9_60_0
  | exact S 9 60 1 cell_9_60_1
  | exact S 9 60 2 cell_9_60_2
  | exact S 9 60 3 cell_9_60_3
  | exact S 9 60 4 cell_9_60_4
  | exact S 9 60 5 cell_9_60_5
theorem cell_9_61_0 : C 9 61 0 := by decide +kernel
theorem cell_9_61_1 : C 9 61 1 := by decide +kernel
theorem cell_9_61_2 : C 9 61 2 := by decide +kernel
theorem cell_9_61_3 : C 9 61 3 := by decide +kernel
theorem cell_9_61_4 : C 9 61 4 := by decide +kernel
theorem cell_9_61_5 : C 9 61 5 := by decide +kernel
theorem row_9_61 : ThresholdAt 9 61 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 61 0 cell_9_61_0
  | exact S 9 61 1 cell_9_61_1
  | exact S 9 61 2 cell_9_61_2
  | exact S 9 61 3 cell_9_61_3
  | exact S 9 61 4 cell_9_61_4
  | exact S 9 61 5 cell_9_61_5
theorem cell_9_62_0 : C 9 62 0 := by decide +kernel
theorem cell_9_62_1 : C 9 62 1 := by decide +kernel
theorem cell_9_62_2 : C 9 62 2 := by decide +kernel
theorem cell_9_62_3 : C 9 62 3 := by decide +kernel
theorem cell_9_62_4 : C 9 62 4 := by decide +kernel
theorem cell_9_62_5 : C 9 62 5 := by decide +kernel
theorem row_9_62 : ThresholdAt 9 62 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 62 0 cell_9_62_0
  | exact S 9 62 1 cell_9_62_1
  | exact S 9 62 2 cell_9_62_2
  | exact S 9 62 3 cell_9_62_3
  | exact S 9 62 4 cell_9_62_4
  | exact S 9 62 5 cell_9_62_5
theorem cell_9_63_0 : C 9 63 0 := by decide +kernel
theorem cell_9_63_1 : C 9 63 1 := by decide +kernel
theorem cell_9_63_2 : C 9 63 2 := by decide +kernel
theorem cell_9_63_3 : C 9 63 3 := by decide +kernel
theorem cell_9_63_4 : C 9 63 4 := by decide +kernel
theorem cell_9_63_5 : C 9 63 5 := by decide +kernel
theorem row_9_63 : ThresholdAt 9 63 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 63 0 cell_9_63_0
  | exact S 9 63 1 cell_9_63_1
  | exact S 9 63 2 cell_9_63_2
  | exact S 9 63 3 cell_9_63_3
  | exact S 9 63 4 cell_9_63_4
  | exact S 9 63 5 cell_9_63_5
theorem cell_9_64_0 : C 9 64 0 := by decide +kernel
theorem cell_9_64_1 : C 9 64 1 := by decide +kernel
theorem cell_9_64_2 : C 9 64 2 := by decide +kernel
theorem cell_9_64_3 : C 9 64 3 := by decide +kernel
theorem cell_9_64_4 : C 9 64 4 := by decide +kernel
theorem cell_9_64_5 : C 9 64 5 := by decide +kernel
theorem row_9_64 : ThresholdAt 9 64 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 64 0 cell_9_64_0
  | exact S 9 64 1 cell_9_64_1
  | exact S 9 64 2 cell_9_64_2
  | exact S 9 64 3 cell_9_64_3
  | exact S 9 64 4 cell_9_64_4
  | exact S 9 64 5 cell_9_64_5
theorem cell_9_65_0 : C 9 65 0 := by decide +kernel
theorem cell_9_65_1 : C 9 65 1 := by decide +kernel
theorem cell_9_65_2 : C 9 65 2 := by decide +kernel
theorem cell_9_65_3 : C 9 65 3 := by decide +kernel
theorem cell_9_65_4 : C 9 65 4 := by decide +kernel
theorem cell_9_65_5 : C 9 65 5 := by decide +kernel
theorem row_9_65 : ThresholdAt 9 65 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 65 0 cell_9_65_0
  | exact S 9 65 1 cell_9_65_1
  | exact S 9 65 2 cell_9_65_2
  | exact S 9 65 3 cell_9_65_3
  | exact S 9 65 4 cell_9_65_4
  | exact S 9 65 5 cell_9_65_5
theorem cell_9_66_0 : C 9 66 0 := by decide +kernel
theorem cell_9_66_1 : C 9 66 1 := by decide +kernel
theorem cell_9_66_2 : C 9 66 2 := by decide +kernel
theorem cell_9_66_3 : C 9 66 3 := by decide +kernel
theorem cell_9_66_4 : C 9 66 4 := by decide +kernel
theorem cell_9_66_5 : C 9 66 5 := by decide +kernel
theorem row_9_66 : ThresholdAt 9 66 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 66 0 cell_9_66_0
  | exact S 9 66 1 cell_9_66_1
  | exact S 9 66 2 cell_9_66_2
  | exact S 9 66 3 cell_9_66_3
  | exact S 9 66 4 cell_9_66_4
  | exact S 9 66 5 cell_9_66_5
theorem cell_9_67_0 : C 9 67 0 := by decide +kernel
theorem cell_9_67_1 : C 9 67 1 := by decide +kernel
theorem cell_9_67_2 : C 9 67 2 := by decide +kernel
theorem cell_9_67_3 : C 9 67 3 := by decide +kernel
theorem cell_9_67_4 : C 9 67 4 := by decide +kernel
theorem cell_9_67_5 : C 9 67 5 := by decide +kernel
theorem row_9_67 : ThresholdAt 9 67 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 67 0 cell_9_67_0
  | exact S 9 67 1 cell_9_67_1
  | exact S 9 67 2 cell_9_67_2
  | exact S 9 67 3 cell_9_67_3
  | exact S 9 67 4 cell_9_67_4
  | exact S 9 67 5 cell_9_67_5
theorem cell_9_68_0 : C 9 68 0 := by decide +kernel
theorem cell_9_68_1 : C 9 68 1 := by decide +kernel
theorem cell_9_68_2 : C 9 68 2 := by decide +kernel
theorem cell_9_68_3 : C 9 68 3 := by decide +kernel
theorem cell_9_68_4 : C 9 68 4 := by decide +kernel
theorem cell_9_68_5 : C 9 68 5 := by decide +kernel
theorem row_9_68 : ThresholdAt 9 68 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 68 0 cell_9_68_0
  | exact S 9 68 1 cell_9_68_1
  | exact S 9 68 2 cell_9_68_2
  | exact S 9 68 3 cell_9_68_3
  | exact S 9 68 4 cell_9_68_4
  | exact S 9 68 5 cell_9_68_5
theorem cell_9_69_0 : C 9 69 0 := by decide +kernel
theorem cell_9_69_1 : C 9 69 1 := by decide +kernel
theorem cell_9_69_2 : C 9 69 2 := by decide +kernel
theorem cell_9_69_3 : C 9 69 3 := by decide +kernel
theorem cell_9_69_4 : C 9 69 4 := by decide +kernel
theorem cell_9_69_5 : C 9 69 5 := by decide +kernel
theorem row_9_69 : ThresholdAt 9 69 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 69 0 cell_9_69_0
  | exact S 9 69 1 cell_9_69_1
  | exact S 9 69 2 cell_9_69_2
  | exact S 9 69 3 cell_9_69_3
  | exact S 9 69 4 cell_9_69_4
  | exact S 9 69 5 cell_9_69_5
theorem cell_9_70_0 : C 9 70 0 := by decide +kernel
theorem cell_9_70_1 : C 9 70 1 := by decide +kernel
theorem cell_9_70_2 : C 9 70 2 := by decide +kernel
theorem cell_9_70_3 : C 9 70 3 := by decide +kernel
theorem cell_9_70_4 : C 9 70 4 := by decide +kernel
theorem cell_9_70_5 : C 9 70 5 := by decide +kernel
theorem row_9_70 : ThresholdAt 9 70 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 70 0 cell_9_70_0
  | exact S 9 70 1 cell_9_70_1
  | exact S 9 70 2 cell_9_70_2
  | exact S 9 70 3 cell_9_70_3
  | exact S 9 70 4 cell_9_70_4
  | exact S 9 70 5 cell_9_70_5
theorem cell_9_71_0 : C 9 71 0 := by decide +kernel
theorem cell_9_71_1 : C 9 71 1 := by decide +kernel
theorem cell_9_71_2 : C 9 71 2 := by decide +kernel
theorem cell_9_71_3 : C 9 71 3 := by decide +kernel
theorem cell_9_71_4 : C 9 71 4 := by decide +kernel
theorem cell_9_71_5 : C 9 71 5 := by decide +kernel
theorem row_9_71 : ThresholdAt 9 71 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 71 0 cell_9_71_0
  | exact S 9 71 1 cell_9_71_1
  | exact S 9 71 2 cell_9_71_2
  | exact S 9 71 3 cell_9_71_3
  | exact S 9 71 4 cell_9_71_4
  | exact S 9 71 5 cell_9_71_5
theorem cell_9_72_0 : C 9 72 0 := by decide +kernel
theorem cell_9_72_1 : C 9 72 1 := by decide +kernel
theorem cell_9_72_2 : C 9 72 2 := by decide +kernel
theorem cell_9_72_3 : C 9 72 3 := by decide +kernel
theorem cell_9_72_4 : C 9 72 4 := by decide +kernel
theorem cell_9_72_5 : C 9 72 5 := by decide +kernel
theorem row_9_72 : ThresholdAt 9 72 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 72 0 cell_9_72_0
  | exact S 9 72 1 cell_9_72_1
  | exact S 9 72 2 cell_9_72_2
  | exact S 9 72 3 cell_9_72_3
  | exact S 9 72 4 cell_9_72_4
  | exact S 9 72 5 cell_9_72_5
theorem cell_9_73_0 : C 9 73 0 := by decide +kernel
theorem cell_9_73_1 : C 9 73 1 := by decide +kernel
theorem cell_9_73_2 : C 9 73 2 := by decide +kernel
theorem cell_9_73_3 : C 9 73 3 := by decide +kernel
theorem cell_9_73_4 : C 9 73 4 := by decide +kernel
theorem cell_9_73_5 : C 9 73 5 := by decide +kernel
theorem row_9_73 : ThresholdAt 9 73 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 73 0 cell_9_73_0
  | exact S 9 73 1 cell_9_73_1
  | exact S 9 73 2 cell_9_73_2
  | exact S 9 73 3 cell_9_73_3
  | exact S 9 73 4 cell_9_73_4
  | exact S 9 73 5 cell_9_73_5
theorem cell_9_74_0 : C 9 74 0 := by decide +kernel
theorem cell_9_74_1 : C 9 74 1 := by decide +kernel
theorem cell_9_74_2 : C 9 74 2 := by decide +kernel
theorem cell_9_74_3 : C 9 74 3 := by decide +kernel
theorem cell_9_74_4 : C 9 74 4 := by decide +kernel
theorem cell_9_74_5 : C 9 74 5 := by decide +kernel
theorem row_9_74 : ThresholdAt 9 74 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 74 0 cell_9_74_0
  | exact S 9 74 1 cell_9_74_1
  | exact S 9 74 2 cell_9_74_2
  | exact S 9 74 3 cell_9_74_3
  | exact S 9 74 4 cell_9_74_4
  | exact S 9 74 5 cell_9_74_5
theorem cell_9_75_0 : C 9 75 0 := by decide +kernel
theorem cell_9_75_1 : C 9 75 1 := by decide +kernel
theorem cell_9_75_2 : C 9 75 2 := by decide +kernel
theorem cell_9_75_3 : C 9 75 3 := by decide +kernel
theorem cell_9_75_4 : C 9 75 4 := by decide +kernel
theorem cell_9_75_5 : C 9 75 5 := by decide +kernel
theorem row_9_75 : ThresholdAt 9 75 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 75 0 cell_9_75_0
  | exact S 9 75 1 cell_9_75_1
  | exact S 9 75 2 cell_9_75_2
  | exact S 9 75 3 cell_9_75_3
  | exact S 9 75 4 cell_9_75_4
  | exact S 9 75 5 cell_9_75_5
theorem cell_9_76_0 : C 9 76 0 := by decide +kernel
theorem cell_9_76_1 : C 9 76 1 := by decide +kernel
theorem cell_9_76_2 : C 9 76 2 := by decide +kernel
theorem cell_9_76_3 : C 9 76 3 := by decide +kernel
theorem cell_9_76_4 : C 9 76 4 := by decide +kernel
theorem cell_9_76_5 : C 9 76 5 := by decide +kernel
theorem row_9_76 : ThresholdAt 9 76 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 76 0 cell_9_76_0
  | exact S 9 76 1 cell_9_76_1
  | exact S 9 76 2 cell_9_76_2
  | exact S 9 76 3 cell_9_76_3
  | exact S 9 76 4 cell_9_76_4
  | exact S 9 76 5 cell_9_76_5
theorem cell_9_77_0 : C 9 77 0 := by decide +kernel
theorem cell_9_77_1 : C 9 77 1 := by decide +kernel
theorem cell_9_77_2 : C 9 77 2 := by decide +kernel
theorem cell_9_77_3 : C 9 77 3 := by decide +kernel
theorem cell_9_77_4 : C 9 77 4 := by decide +kernel
theorem cell_9_77_5 : C 9 77 5 := by decide +kernel
theorem row_9_77 : ThresholdAt 9 77 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 77 0 cell_9_77_0
  | exact S 9 77 1 cell_9_77_1
  | exact S 9 77 2 cell_9_77_2
  | exact S 9 77 3 cell_9_77_3
  | exact S 9 77 4 cell_9_77_4
  | exact S 9 77 5 cell_9_77_5
theorem cell_9_78_0 : C 9 78 0 := by decide +kernel
theorem cell_9_78_1 : C 9 78 1 := by decide +kernel
theorem cell_9_78_2 : C 9 78 2 := by decide +kernel
theorem cell_9_78_3 : C 9 78 3 := by decide +kernel
theorem cell_9_78_4 : C 9 78 4 := by decide +kernel
theorem cell_9_78_5 : C 9 78 5 := by decide +kernel
theorem row_9_78 : ThresholdAt 9 78 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 78 0 cell_9_78_0
  | exact S 9 78 1 cell_9_78_1
  | exact S 9 78 2 cell_9_78_2
  | exact S 9 78 3 cell_9_78_3
  | exact S 9 78 4 cell_9_78_4
  | exact S 9 78 5 cell_9_78_5
theorem cell_9_79_0 : C 9 79 0 := by decide +kernel
theorem cell_9_79_1 : C 9 79 1 := by decide +kernel
theorem cell_9_79_2 : C 9 79 2 := by decide +kernel
theorem cell_9_79_3 : C 9 79 3 := by decide +kernel
theorem cell_9_79_4 : C 9 79 4 := by decide +kernel
theorem cell_9_79_5 : C 9 79 5 := by decide +kernel
theorem row_9_79 : ThresholdAt 9 79 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 79 0 cell_9_79_0
  | exact S 9 79 1 cell_9_79_1
  | exact S 9 79 2 cell_9_79_2
  | exact S 9 79 3 cell_9_79_3
  | exact S 9 79 4 cell_9_79_4
  | exact S 9 79 5 cell_9_79_5
theorem cell_9_80_0 : C 9 80 0 := by decide +kernel
theorem cell_9_80_1 : C 9 80 1 := by decide +kernel
theorem cell_9_80_2 : C 9 80 2 := by decide +kernel
theorem cell_9_80_3 : C 9 80 3 := by decide +kernel
theorem cell_9_80_4 : C 9 80 4 := by decide +kernel
theorem cell_9_80_5 : C 9 80 5 := by decide +kernel
theorem row_9_80 : ThresholdAt 9 80 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 80 0 cell_9_80_0
  | exact S 9 80 1 cell_9_80_1
  | exact S 9 80 2 cell_9_80_2
  | exact S 9 80 3 cell_9_80_3
  | exact S 9 80 4 cell_9_80_4
  | exact S 9 80 5 cell_9_80_5
theorem cell_9_81_0 : C 9 81 0 := by decide +kernel
theorem cell_9_81_1 : C 9 81 1 := by decide +kernel
theorem cell_9_81_2 : C 9 81 2 := by decide +kernel
theorem cell_9_81_3 : C 9 81 3 := by decide +kernel
theorem cell_9_81_4 : C 9 81 4 := by decide +kernel
theorem cell_9_81_5 : C 9 81 5 := by decide +kernel
theorem row_9_81 : ThresholdAt 9 81 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 81 0 cell_9_81_0
  | exact S 9 81 1 cell_9_81_1
  | exact S 9 81 2 cell_9_81_2
  | exact S 9 81 3 cell_9_81_3
  | exact S 9 81 4 cell_9_81_4
  | exact S 9 81 5 cell_9_81_5
theorem cell_9_82_0 : C 9 82 0 := by decide +kernel
theorem cell_9_82_1 : C 9 82 1 := by decide +kernel
theorem cell_9_82_2 : C 9 82 2 := by decide +kernel
theorem cell_9_82_3 : C 9 82 3 := by decide +kernel
theorem cell_9_82_4 : C 9 82 4 := by decide +kernel
theorem cell_9_82_5 : C 9 82 5 := by decide +kernel
theorem row_9_82 : ThresholdAt 9 82 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 82 0 cell_9_82_0
  | exact S 9 82 1 cell_9_82_1
  | exact S 9 82 2 cell_9_82_2
  | exact S 9 82 3 cell_9_82_3
  | exact S 9 82 4 cell_9_82_4
  | exact S 9 82 5 cell_9_82_5
theorem cell_9_83_0 : C 9 83 0 := by decide +kernel
theorem cell_9_83_1 : C 9 83 1 := by decide +kernel
theorem cell_9_83_2 : C 9 83 2 := by decide +kernel
theorem cell_9_83_3 : C 9 83 3 := by decide +kernel
theorem cell_9_83_4 : C 9 83 4 := by decide +kernel
theorem cell_9_83_5 : C 9 83 5 := by decide +kernel
theorem row_9_83 : ThresholdAt 9 83 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 83 0 cell_9_83_0
  | exact S 9 83 1 cell_9_83_1
  | exact S 9 83 2 cell_9_83_2
  | exact S 9 83 3 cell_9_83_3
  | exact S 9 83 4 cell_9_83_4
  | exact S 9 83 5 cell_9_83_5
theorem cell_9_84_0 : C 9 84 0 := by decide +kernel
theorem cell_9_84_1 : C 9 84 1 := by decide +kernel
theorem cell_9_84_2 : C 9 84 2 := by decide +kernel
theorem cell_9_84_3 : C 9 84 3 := by decide +kernel
theorem cell_9_84_4 : C 9 84 4 := by decide +kernel
theorem cell_9_84_5 : C 9 84 5 := by decide +kernel
theorem row_9_84 : ThresholdAt 9 84 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 84 0 cell_9_84_0
  | exact S 9 84 1 cell_9_84_1
  | exact S 9 84 2 cell_9_84_2
  | exact S 9 84 3 cell_9_84_3
  | exact S 9 84 4 cell_9_84_4
  | exact S 9 84 5 cell_9_84_5
theorem cell_9_85_0 : C 9 85 0 := by decide +kernel
theorem cell_9_85_1 : C 9 85 1 := by decide +kernel
theorem cell_9_85_2 : C 9 85 2 := by decide +kernel
theorem cell_9_85_3 : C 9 85 3 := by decide +kernel
theorem cell_9_85_4 : C 9 85 4 := by decide +kernel
theorem cell_9_85_5 : C 9 85 5 := by decide +kernel
theorem row_9_85 : ThresholdAt 9 85 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 85 0 cell_9_85_0
  | exact S 9 85 1 cell_9_85_1
  | exact S 9 85 2 cell_9_85_2
  | exact S 9 85 3 cell_9_85_3
  | exact S 9 85 4 cell_9_85_4
  | exact S 9 85 5 cell_9_85_5
theorem cell_9_86_0 : C 9 86 0 := by decide +kernel
theorem cell_9_86_1 : C 9 86 1 := by decide +kernel
theorem cell_9_86_2 : C 9 86 2 := by decide +kernel
theorem cell_9_86_3 : C 9 86 3 := by decide +kernel
theorem cell_9_86_4 : C 9 86 4 := by decide +kernel
theorem cell_9_86_5 : C 9 86 5 := by decide +kernel
theorem row_9_86 : ThresholdAt 9 86 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 86 0 cell_9_86_0
  | exact S 9 86 1 cell_9_86_1
  | exact S 9 86 2 cell_9_86_2
  | exact S 9 86 3 cell_9_86_3
  | exact S 9 86 4 cell_9_86_4
  | exact S 9 86 5 cell_9_86_5
theorem cell_9_87_0 : C 9 87 0 := by decide +kernel
theorem cell_9_87_1 : C 9 87 1 := by decide +kernel
theorem cell_9_87_2 : C 9 87 2 := by decide +kernel
theorem cell_9_87_3 : C 9 87 3 := by decide +kernel
theorem cell_9_87_4 : C 9 87 4 := by decide +kernel
theorem cell_9_87_5 : C 9 87 5 := by decide +kernel
theorem row_9_87 : ThresholdAt 9 87 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 87 0 cell_9_87_0
  | exact S 9 87 1 cell_9_87_1
  | exact S 9 87 2 cell_9_87_2
  | exact S 9 87 3 cell_9_87_3
  | exact S 9 87 4 cell_9_87_4
  | exact S 9 87 5 cell_9_87_5
theorem cell_9_88_0 : C 9 88 0 := by decide +kernel
theorem cell_9_88_1 : C 9 88 1 := by decide +kernel
theorem cell_9_88_2 : C 9 88 2 := by decide +kernel
theorem cell_9_88_3 : C 9 88 3 := by decide +kernel
theorem cell_9_88_4 : C 9 88 4 := by decide +kernel
theorem cell_9_88_5 : C 9 88 5 := by decide +kernel
theorem row_9_88 : ThresholdAt 9 88 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 88 0 cell_9_88_0
  | exact S 9 88 1 cell_9_88_1
  | exact S 9 88 2 cell_9_88_2
  | exact S 9 88 3 cell_9_88_3
  | exact S 9 88 4 cell_9_88_4
  | exact S 9 88 5 cell_9_88_5
theorem cell_9_89_0 : C 9 89 0 := by decide +kernel
theorem cell_9_89_1 : C 9 89 1 := by decide +kernel
theorem cell_9_89_2 : C 9 89 2 := by decide +kernel
theorem cell_9_89_3 : C 9 89 3 := by decide +kernel
theorem cell_9_89_4 : C 9 89 4 := by decide +kernel
theorem cell_9_89_5 : C 9 89 5 := by decide +kernel
theorem row_9_89 : ThresholdAt 9 89 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 89 0 cell_9_89_0
  | exact S 9 89 1 cell_9_89_1
  | exact S 9 89 2 cell_9_89_2
  | exact S 9 89 3 cell_9_89_3
  | exact S 9 89 4 cell_9_89_4
  | exact S 9 89 5 cell_9_89_5
theorem cell_9_90_0 : C 9 90 0 := by decide +kernel
theorem cell_9_90_1 : C 9 90 1 := by decide +kernel
theorem cell_9_90_2 : C 9 90 2 := by decide +kernel
theorem cell_9_90_3 : C 9 90 3 := by decide +kernel
theorem cell_9_90_4 : C 9 90 4 := by decide +kernel
theorem cell_9_90_5 : C 9 90 5 := by decide +kernel
theorem row_9_90 : ThresholdAt 9 90 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 90 0 cell_9_90_0
  | exact S 9 90 1 cell_9_90_1
  | exact S 9 90 2 cell_9_90_2
  | exact S 9 90 3 cell_9_90_3
  | exact S 9 90 4 cell_9_90_4
  | exact S 9 90 5 cell_9_90_5
theorem cell_9_91_0 : C 9 91 0 := by decide +kernel
theorem cell_9_91_1 : C 9 91 1 := by decide +kernel
theorem cell_9_91_2 : C 9 91 2 := by decide +kernel
theorem cell_9_91_3 : C 9 91 3 := by decide +kernel
theorem cell_9_91_4 : C 9 91 4 := by decide +kernel
theorem cell_9_91_5 : C 9 91 5 := by decide +kernel
theorem row_9_91 : ThresholdAt 9 91 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 91 0 cell_9_91_0
  | exact S 9 91 1 cell_9_91_1
  | exact S 9 91 2 cell_9_91_2
  | exact S 9 91 3 cell_9_91_3
  | exact S 9 91 4 cell_9_91_4
  | exact S 9 91 5 cell_9_91_5
theorem cell_9_92_0 : C 9 92 0 := by decide +kernel
theorem cell_9_92_1 : C 9 92 1 := by decide +kernel
theorem cell_9_92_2 : C 9 92 2 := by decide +kernel
theorem cell_9_92_3 : C 9 92 3 := by decide +kernel
theorem cell_9_92_4 : C 9 92 4 := by decide +kernel
theorem cell_9_92_5 : C 9 92 5 := by decide +kernel
theorem row_9_92 : ThresholdAt 9 92 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 92 0 cell_9_92_0
  | exact S 9 92 1 cell_9_92_1
  | exact S 9 92 2 cell_9_92_2
  | exact S 9 92 3 cell_9_92_3
  | exact S 9 92 4 cell_9_92_4
  | exact S 9 92 5 cell_9_92_5
theorem cell_9_93_0 : C 9 93 0 := by decide +kernel
theorem cell_9_93_1 : C 9 93 1 := by decide +kernel
theorem cell_9_93_2 : C 9 93 2 := by decide +kernel
theorem cell_9_93_3 : C 9 93 3 := by decide +kernel
theorem cell_9_93_4 : C 9 93 4 := by decide +kernel
theorem cell_9_93_5 : C 9 93 5 := by decide +kernel
theorem row_9_93 : ThresholdAt 9 93 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 93 0 cell_9_93_0
  | exact S 9 93 1 cell_9_93_1
  | exact S 9 93 2 cell_9_93_2
  | exact S 9 93 3 cell_9_93_3
  | exact S 9 93 4 cell_9_93_4
  | exact S 9 93 5 cell_9_93_5
theorem cell_9_94_0 : C 9 94 0 := by decide +kernel
theorem cell_9_94_1 : C 9 94 1 := by decide +kernel
theorem cell_9_94_2 : C 9 94 2 := by decide +kernel
theorem cell_9_94_3 : C 9 94 3 := by decide +kernel
theorem cell_9_94_4 : C 9 94 4 := by decide +kernel
theorem cell_9_94_5 : C 9 94 5 := by decide +kernel
theorem row_9_94 : ThresholdAt 9 94 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 94 0 cell_9_94_0
  | exact S 9 94 1 cell_9_94_1
  | exact S 9 94 2 cell_9_94_2
  | exact S 9 94 3 cell_9_94_3
  | exact S 9 94 4 cell_9_94_4
  | exact S 9 94 5 cell_9_94_5
theorem cell_9_95_0 : C 9 95 0 := by decide +kernel
theorem cell_9_95_1 : C 9 95 1 := by decide +kernel
theorem cell_9_95_2 : C 9 95 2 := by decide +kernel
theorem cell_9_95_3 : C 9 95 3 := by decide +kernel
theorem cell_9_95_4 : C 9 95 4 := by decide +kernel
theorem cell_9_95_5 : C 9 95 5 := by decide +kernel
theorem row_9_95 : ThresholdAt 9 95 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 95 0 cell_9_95_0
  | exact S 9 95 1 cell_9_95_1
  | exact S 9 95 2 cell_9_95_2
  | exact S 9 95 3 cell_9_95_3
  | exact S 9 95 4 cell_9_95_4
  | exact S 9 95 5 cell_9_95_5
theorem cell_9_96_0 : C 9 96 0 := by decide +kernel
theorem cell_9_96_1 : C 9 96 1 := by decide +kernel
theorem cell_9_96_2 : C 9 96 2 := by decide +kernel
theorem cell_9_96_3 : C 9 96 3 := by decide +kernel
theorem cell_9_96_4 : C 9 96 4 := by decide +kernel
theorem cell_9_96_5 : C 9 96 5 := by decide +kernel
theorem row_9_96 : ThresholdAt 9 96 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 96 0 cell_9_96_0
  | exact S 9 96 1 cell_9_96_1
  | exact S 9 96 2 cell_9_96_2
  | exact S 9 96 3 cell_9_96_3
  | exact S 9 96 4 cell_9_96_4
  | exact S 9 96 5 cell_9_96_5
theorem cell_9_97_0 : C 9 97 0 := by decide +kernel
theorem cell_9_97_1 : C 9 97 1 := by decide +kernel
theorem cell_9_97_2 : C 9 97 2 := by decide +kernel
theorem cell_9_97_3 : C 9 97 3 := by decide +kernel
theorem cell_9_97_4 : C 9 97 4 := by decide +kernel
theorem cell_9_97_5 : C 9 97 5 := by decide +kernel
theorem row_9_97 : ThresholdAt 9 97 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 97 0 cell_9_97_0
  | exact S 9 97 1 cell_9_97_1
  | exact S 9 97 2 cell_9_97_2
  | exact S 9 97 3 cell_9_97_3
  | exact S 9 97 4 cell_9_97_4
  | exact S 9 97 5 cell_9_97_5
theorem cell_9_98_0 : C 9 98 0 := by decide +kernel
theorem cell_9_98_1 : C 9 98 1 := by decide +kernel
theorem cell_9_98_2 : C 9 98 2 := by decide +kernel
theorem cell_9_98_3 : C 9 98 3 := by decide +kernel
theorem cell_9_98_4 : C 9 98 4 := by decide +kernel
theorem cell_9_98_5 : C 9 98 5 := by decide +kernel
theorem row_9_98 : ThresholdAt 9 98 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 98 0 cell_9_98_0
  | exact S 9 98 1 cell_9_98_1
  | exact S 9 98 2 cell_9_98_2
  | exact S 9 98 3 cell_9_98_3
  | exact S 9 98 4 cell_9_98_4
  | exact S 9 98 5 cell_9_98_5
theorem cell_9_99_0 : C 9 99 0 := by decide +kernel
theorem cell_9_99_1 : C 9 99 1 := by decide +kernel
theorem cell_9_99_2 : C 9 99 2 := by decide +kernel
theorem cell_9_99_3 : C 9 99 3 := by decide +kernel
theorem cell_9_99_4 : C 9 99 4 := by decide +kernel
theorem cell_9_99_5 : C 9 99 5 := by decide +kernel
theorem row_9_99 : ThresholdAt 9 99 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 99 0 cell_9_99_0
  | exact S 9 99 1 cell_9_99_1
  | exact S 9 99 2 cell_9_99_2
  | exact S 9 99 3 cell_9_99_3
  | exact S 9 99 4 cell_9_99_4
  | exact S 9 99 5 cell_9_99_5
theorem cell_9_100_0 : C 9 100 0 := by decide +kernel
theorem cell_9_100_1 : C 9 100 1 := by decide +kernel
theorem cell_9_100_2 : C 9 100 2 := by decide +kernel
theorem cell_9_100_3 : C 9 100 3 := by decide +kernel
theorem cell_9_100_4 : C 9 100 4 := by decide +kernel
theorem cell_9_100_5 : C 9 100 5 := by decide +kernel
theorem row_9_100 : ThresholdAt 9 100 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 100 0 cell_9_100_0
  | exact S 9 100 1 cell_9_100_1
  | exact S 9 100 2 cell_9_100_2
  | exact S 9 100 3 cell_9_100_3
  | exact S 9 100 4 cell_9_100_4
  | exact S 9 100 5 cell_9_100_5
theorem cell_9_101_0 : C 9 101 0 := by decide +kernel
theorem cell_9_101_1 : C 9 101 1 := by decide +kernel
theorem cell_9_101_2 : C 9 101 2 := by decide +kernel
theorem cell_9_101_3 : C 9 101 3 := by decide +kernel
theorem cell_9_101_4 : C 9 101 4 := by decide +kernel
theorem cell_9_101_5 : C 9 101 5 := by decide +kernel
theorem row_9_101 : ThresholdAt 9 101 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 101 0 cell_9_101_0
  | exact S 9 101 1 cell_9_101_1
  | exact S 9 101 2 cell_9_101_2
  | exact S 9 101 3 cell_9_101_3
  | exact S 9 101 4 cell_9_101_4
  | exact S 9 101 5 cell_9_101_5
theorem cell_9_102_0 : C 9 102 0 := by decide +kernel
theorem cell_9_102_1 : C 9 102 1 := by decide +kernel
theorem cell_9_102_2 : C 9 102 2 := by decide +kernel
theorem cell_9_102_3 : C 9 102 3 := by decide +kernel
theorem cell_9_102_4 : C 9 102 4 := by decide +kernel
theorem cell_9_102_5 : C 9 102 5 := by decide +kernel
theorem row_9_102 : ThresholdAt 9 102 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 102 0 cell_9_102_0
  | exact S 9 102 1 cell_9_102_1
  | exact S 9 102 2 cell_9_102_2
  | exact S 9 102 3 cell_9_102_3
  | exact S 9 102 4 cell_9_102_4
  | exact S 9 102 5 cell_9_102_5
theorem cell_9_103_0 : C 9 103 0 := by decide +kernel
theorem cell_9_103_1 : C 9 103 1 := by decide +kernel
theorem cell_9_103_2 : C 9 103 2 := by decide +kernel
theorem cell_9_103_3 : C 9 103 3 := by decide +kernel
theorem cell_9_103_4 : C 9 103 4 := by decide +kernel
theorem cell_9_103_5 : C 9 103 5 := by decide +kernel
theorem row_9_103 : ThresholdAt 9 103 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 103 0 cell_9_103_0
  | exact S 9 103 1 cell_9_103_1
  | exact S 9 103 2 cell_9_103_2
  | exact S 9 103 3 cell_9_103_3
  | exact S 9 103 4 cell_9_103_4
  | exact S 9 103 5 cell_9_103_5
theorem cell_9_104_0 : C 9 104 0 := by decide +kernel
theorem cell_9_104_1 : C 9 104 1 := by decide +kernel
theorem cell_9_104_2 : C 9 104 2 := by decide +kernel
theorem cell_9_104_3 : C 9 104 3 := by decide +kernel
theorem cell_9_104_4 : C 9 104 4 := by decide +kernel
theorem cell_9_104_5 : C 9 104 5 := by decide +kernel
theorem row_9_104 : ThresholdAt 9 104 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 104 0 cell_9_104_0
  | exact S 9 104 1 cell_9_104_1
  | exact S 9 104 2 cell_9_104_2
  | exact S 9 104 3 cell_9_104_3
  | exact S 9 104 4 cell_9_104_4
  | exact S 9 104 5 cell_9_104_5
theorem cell_9_105_0 : C 9 105 0 := by decide +kernel
theorem cell_9_105_1 : C 9 105 1 := by decide +kernel
theorem cell_9_105_2 : C 9 105 2 := by decide +kernel
theorem cell_9_105_3 : C 9 105 3 := by decide +kernel
theorem cell_9_105_4 : C 9 105 4 := by decide +kernel
theorem cell_9_105_5 : C 9 105 5 := by decide +kernel
theorem row_9_105 : ThresholdAt 9 105 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 105 0 cell_9_105_0
  | exact S 9 105 1 cell_9_105_1
  | exact S 9 105 2 cell_9_105_2
  | exact S 9 105 3 cell_9_105_3
  | exact S 9 105 4 cell_9_105_4
  | exact S 9 105 5 cell_9_105_5
theorem cell_9_106_0 : C 9 106 0 := by decide +kernel
theorem cell_9_106_1 : C 9 106 1 := by decide +kernel
theorem cell_9_106_2 : C 9 106 2 := by decide +kernel
theorem cell_9_106_3 : C 9 106 3 := by decide +kernel
theorem cell_9_106_4 : C 9 106 4 := by decide +kernel
theorem cell_9_106_5 : C 9 106 5 := by decide +kernel
theorem row_9_106 : ThresholdAt 9 106 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 106 0 cell_9_106_0
  | exact S 9 106 1 cell_9_106_1
  | exact S 9 106 2 cell_9_106_2
  | exact S 9 106 3 cell_9_106_3
  | exact S 9 106 4 cell_9_106_4
  | exact S 9 106 5 cell_9_106_5
theorem cell_9_107_0 : C 9 107 0 := by decide +kernel
theorem cell_9_107_1 : C 9 107 1 := by decide +kernel
theorem cell_9_107_2 : C 9 107 2 := by decide +kernel
theorem cell_9_107_3 : C 9 107 3 := by decide +kernel
theorem cell_9_107_4 : C 9 107 4 := by decide +kernel
theorem cell_9_107_5 : C 9 107 5 := by decide +kernel
theorem row_9_107 : ThresholdAt 9 107 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 107 0 cell_9_107_0
  | exact S 9 107 1 cell_9_107_1
  | exact S 9 107 2 cell_9_107_2
  | exact S 9 107 3 cell_9_107_3
  | exact S 9 107 4 cell_9_107_4
  | exact S 9 107 5 cell_9_107_5
theorem cell_9_108_0 : C 9 108 0 := by decide +kernel
theorem cell_9_108_1 : C 9 108 1 := by decide +kernel
theorem cell_9_108_2 : C 9 108 2 := by decide +kernel
theorem cell_9_108_3 : C 9 108 3 := by decide +kernel
theorem cell_9_108_4 : C 9 108 4 := by decide +kernel
theorem cell_9_108_5 : C 9 108 5 := by decide +kernel
theorem row_9_108 : ThresholdAt 9 108 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 108 0 cell_9_108_0
  | exact S 9 108 1 cell_9_108_1
  | exact S 9 108 2 cell_9_108_2
  | exact S 9 108 3 cell_9_108_3
  | exact S 9 108 4 cell_9_108_4
  | exact S 9 108 5 cell_9_108_5
theorem cell_9_109_0 : C 9 109 0 := by decide +kernel
theorem cell_9_109_1 : C 9 109 1 := by decide +kernel
theorem cell_9_109_2 : C 9 109 2 := by decide +kernel
theorem cell_9_109_3 : C 9 109 3 := by decide +kernel
theorem cell_9_109_4 : C 9 109 4 := by decide +kernel
theorem cell_9_109_5 : C 9 109 5 := by decide +kernel
theorem row_9_109 : ThresholdAt 9 109 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 109 0 cell_9_109_0
  | exact S 9 109 1 cell_9_109_1
  | exact S 9 109 2 cell_9_109_2
  | exact S 9 109 3 cell_9_109_3
  | exact S 9 109 4 cell_9_109_4
  | exact S 9 109 5 cell_9_109_5
theorem cell_9_110_0 : C 9 110 0 := by decide +kernel
theorem cell_9_110_1 : C 9 110 1 := by decide +kernel
theorem cell_9_110_2 : C 9 110 2 := by decide +kernel
theorem cell_9_110_3 : C 9 110 3 := by decide +kernel
theorem cell_9_110_4 : C 9 110 4 := by decide +kernel
theorem cell_9_110_5 : C 9 110 5 := by decide +kernel
theorem row_9_110 : ThresholdAt 9 110 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 110 0 cell_9_110_0
  | exact S 9 110 1 cell_9_110_1
  | exact S 9 110 2 cell_9_110_2
  | exact S 9 110 3 cell_9_110_3
  | exact S 9 110 4 cell_9_110_4
  | exact S 9 110 5 cell_9_110_5
theorem cell_9_111_0 : C 9 111 0 := by decide +kernel
theorem cell_9_111_1 : C 9 111 1 := by decide +kernel
theorem cell_9_111_2 : C 9 111 2 := by decide +kernel
theorem cell_9_111_3 : C 9 111 3 := by decide +kernel
theorem cell_9_111_4 : C 9 111 4 := by decide +kernel
theorem cell_9_111_5 : C 9 111 5 := by decide +kernel
theorem row_9_111 : ThresholdAt 9 111 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 111 0 cell_9_111_0
  | exact S 9 111 1 cell_9_111_1
  | exact S 9 111 2 cell_9_111_2
  | exact S 9 111 3 cell_9_111_3
  | exact S 9 111 4 cell_9_111_4
  | exact S 9 111 5 cell_9_111_5
theorem cell_9_112_0 : C 9 112 0 := by decide +kernel
theorem cell_9_112_1 : C 9 112 1 := by decide +kernel
theorem cell_9_112_2 : C 9 112 2 := by decide +kernel
theorem cell_9_112_3 : C 9 112 3 := by decide +kernel
theorem cell_9_112_4 : C 9 112 4 := by decide +kernel
theorem cell_9_112_5 : C 9 112 5 := by decide +kernel
theorem row_9_112 : ThresholdAt 9 112 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 112 0 cell_9_112_0
  | exact S 9 112 1 cell_9_112_1
  | exact S 9 112 2 cell_9_112_2
  | exact S 9 112 3 cell_9_112_3
  | exact S 9 112 4 cell_9_112_4
  | exact S 9 112 5 cell_9_112_5
theorem cell_9_113_0 : C 9 113 0 := by decide +kernel
theorem cell_9_113_1 : C 9 113 1 := by decide +kernel
theorem cell_9_113_2 : C 9 113 2 := by decide +kernel
theorem cell_9_113_3 : C 9 113 3 := by decide +kernel
theorem cell_9_113_4 : C 9 113 4 := by decide +kernel
theorem cell_9_113_5 : C 9 113 5 := by decide +kernel
theorem row_9_113 : ThresholdAt 9 113 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 113 0 cell_9_113_0
  | exact S 9 113 1 cell_9_113_1
  | exact S 9 113 2 cell_9_113_2
  | exact S 9 113 3 cell_9_113_3
  | exact S 9 113 4 cell_9_113_4
  | exact S 9 113 5 cell_9_113_5
theorem cell_9_114_0 : C 9 114 0 := by decide +kernel
theorem cell_9_114_1 : C 9 114 1 := by decide +kernel
theorem cell_9_114_2 : C 9 114 2 := by decide +kernel
theorem cell_9_114_3 : C 9 114 3 := by decide +kernel
theorem cell_9_114_4 : C 9 114 4 := by decide +kernel
theorem cell_9_114_5 : C 9 114 5 := by decide +kernel
theorem row_9_114 : ThresholdAt 9 114 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 114 0 cell_9_114_0
  | exact S 9 114 1 cell_9_114_1
  | exact S 9 114 2 cell_9_114_2
  | exact S 9 114 3 cell_9_114_3
  | exact S 9 114 4 cell_9_114_4
  | exact S 9 114 5 cell_9_114_5
theorem cell_9_115_0 : C 9 115 0 := by decide +kernel
theorem cell_9_115_1 : C 9 115 1 := by decide +kernel
theorem cell_9_115_2 : C 9 115 2 := by decide +kernel
theorem cell_9_115_3 : C 9 115 3 := by decide +kernel
theorem cell_9_115_4 : C 9 115 4 := by decide +kernel
theorem cell_9_115_5 : C 9 115 5 := by decide +kernel
theorem row_9_115 : ThresholdAt 9 115 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 115 0 cell_9_115_0
  | exact S 9 115 1 cell_9_115_1
  | exact S 9 115 2 cell_9_115_2
  | exact S 9 115 3 cell_9_115_3
  | exact S 9 115 4 cell_9_115_4
  | exact S 9 115 5 cell_9_115_5
theorem cell_9_116_0 : C 9 116 0 := by decide +kernel
theorem cell_9_116_1 : C 9 116 1 := by decide +kernel
theorem cell_9_116_2 : C 9 116 2 := by decide +kernel
theorem cell_9_116_3 : C 9 116 3 := by decide +kernel
theorem cell_9_116_4 : C 9 116 4 := by decide +kernel
theorem cell_9_116_5 : C 9 116 5 := by decide +kernel
theorem row_9_116 : ThresholdAt 9 116 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 116 0 cell_9_116_0
  | exact S 9 116 1 cell_9_116_1
  | exact S 9 116 2 cell_9_116_2
  | exact S 9 116 3 cell_9_116_3
  | exact S 9 116 4 cell_9_116_4
  | exact S 9 116 5 cell_9_116_5
theorem cell_9_117_0 : C 9 117 0 := by decide +kernel
theorem cell_9_117_1 : C 9 117 1 := by decide +kernel
theorem cell_9_117_2 : C 9 117 2 := by decide +kernel
theorem cell_9_117_3 : C 9 117 3 := by decide +kernel
theorem cell_9_117_4 : C 9 117 4 := by decide +kernel
theorem cell_9_117_5 : C 9 117 5 := by decide +kernel
theorem row_9_117 : ThresholdAt 9 117 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 117 0 cell_9_117_0
  | exact S 9 117 1 cell_9_117_1
  | exact S 9 117 2 cell_9_117_2
  | exact S 9 117 3 cell_9_117_3
  | exact S 9 117 4 cell_9_117_4
  | exact S 9 117 5 cell_9_117_5
theorem cell_9_118_0 : C 9 118 0 := by decide +kernel
theorem cell_9_118_1 : C 9 118 1 := by decide +kernel
theorem cell_9_118_2 : C 9 118 2 := by decide +kernel
theorem cell_9_118_3 : C 9 118 3 := by decide +kernel
theorem cell_9_118_4 : C 9 118 4 := by decide +kernel
theorem cell_9_118_5 : C 9 118 5 := by decide +kernel
theorem row_9_118 : ThresholdAt 9 118 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 118 0 cell_9_118_0
  | exact S 9 118 1 cell_9_118_1
  | exact S 9 118 2 cell_9_118_2
  | exact S 9 118 3 cell_9_118_3
  | exact S 9 118 4 cell_9_118_4
  | exact S 9 118 5 cell_9_118_5
theorem cell_9_119_0 : C 9 119 0 := by decide +kernel
theorem cell_9_119_1 : C 9 119 1 := by decide +kernel
theorem cell_9_119_2 : C 9 119 2 := by decide +kernel
theorem cell_9_119_3 : C 9 119 3 := by decide +kernel
theorem cell_9_119_4 : C 9 119 4 := by decide +kernel
theorem cell_9_119_5 : C 9 119 5 := by decide +kernel
theorem row_9_119 : ThresholdAt 9 119 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 119 0 cell_9_119_0
  | exact S 9 119 1 cell_9_119_1
  | exact S 9 119 2 cell_9_119_2
  | exact S 9 119 3 cell_9_119_3
  | exact S 9 119 4 cell_9_119_4
  | exact S 9 119 5 cell_9_119_5
theorem cell_9_120_0 : C 9 120 0 := by decide +kernel
theorem cell_9_120_1 : C 9 120 1 := by decide +kernel
theorem cell_9_120_2 : C 9 120 2 := by decide +kernel
theorem cell_9_120_3 : C 9 120 3 := by decide +kernel
theorem cell_9_120_4 : C 9 120 4 := by decide +kernel
theorem cell_9_120_5 : C 9 120 5 := by decide +kernel
theorem row_9_120 : ThresholdAt 9 120 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 120 0 cell_9_120_0
  | exact S 9 120 1 cell_9_120_1
  | exact S 9 120 2 cell_9_120_2
  | exact S 9 120 3 cell_9_120_3
  | exact S 9 120 4 cell_9_120_4
  | exact S 9 120 5 cell_9_120_5
theorem cell_9_121_0 : C 9 121 0 := by decide +kernel
theorem cell_9_121_1 : C 9 121 1 := by decide +kernel
theorem cell_9_121_2 : C 9 121 2 := by decide +kernel
theorem cell_9_121_3 : C 9 121 3 := by decide +kernel
theorem cell_9_121_4 : C 9 121 4 := by decide +kernel
theorem cell_9_121_5 : C 9 121 5 := by decide +kernel
theorem row_9_121 : ThresholdAt 9 121 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 121 0 cell_9_121_0
  | exact S 9 121 1 cell_9_121_1
  | exact S 9 121 2 cell_9_121_2
  | exact S 9 121 3 cell_9_121_3
  | exact S 9 121 4 cell_9_121_4
  | exact S 9 121 5 cell_9_121_5
theorem cell_9_122_0 : C 9 122 0 := by decide +kernel
theorem cell_9_122_1 : C 9 122 1 := by decide +kernel
theorem cell_9_122_2 : C 9 122 2 := by decide +kernel
theorem cell_9_122_3 : C 9 122 3 := by decide +kernel
theorem cell_9_122_4 : C 9 122 4 := by decide +kernel
theorem cell_9_122_5 : C 9 122 5 := by decide +kernel
theorem row_9_122 : ThresholdAt 9 122 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 122 0 cell_9_122_0
  | exact S 9 122 1 cell_9_122_1
  | exact S 9 122 2 cell_9_122_2
  | exact S 9 122 3 cell_9_122_3
  | exact S 9 122 4 cell_9_122_4
  | exact S 9 122 5 cell_9_122_5
theorem cell_9_123_0 : C 9 123 0 := by decide +kernel
theorem cell_9_123_1 : C 9 123 1 := by decide +kernel
theorem cell_9_123_2 : C 9 123 2 := by decide +kernel
theorem cell_9_123_3 : C 9 123 3 := by decide +kernel
theorem cell_9_123_4 : C 9 123 4 := by decide +kernel
theorem cell_9_123_5 : C 9 123 5 := by decide +kernel
theorem row_9_123 : ThresholdAt 9 123 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 123 0 cell_9_123_0
  | exact S 9 123 1 cell_9_123_1
  | exact S 9 123 2 cell_9_123_2
  | exact S 9 123 3 cell_9_123_3
  | exact S 9 123 4 cell_9_123_4
  | exact S 9 123 5 cell_9_123_5
theorem cell_9_124_0 : C 9 124 0 := by decide +kernel
theorem cell_9_124_1 : C 9 124 1 := by decide +kernel
theorem cell_9_124_2 : C 9 124 2 := by decide +kernel
theorem cell_9_124_3 : C 9 124 3 := by decide +kernel
theorem cell_9_124_4 : C 9 124 4 := by decide +kernel
theorem cell_9_124_5 : C 9 124 5 := by decide +kernel
theorem row_9_124 : ThresholdAt 9 124 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 124 0 cell_9_124_0
  | exact S 9 124 1 cell_9_124_1
  | exact S 9 124 2 cell_9_124_2
  | exact S 9 124 3 cell_9_124_3
  | exact S 9 124 4 cell_9_124_4
  | exact S 9 124 5 cell_9_124_5
theorem cell_9_125_0 : C 9 125 0 := by decide +kernel
theorem cell_9_125_1 : C 9 125 1 := by decide +kernel
theorem cell_9_125_2 : C 9 125 2 := by decide +kernel
theorem cell_9_125_3 : C 9 125 3 := by decide +kernel
theorem cell_9_125_4 : C 9 125 4 := by decide +kernel
theorem cell_9_125_5 : C 9 125 5 := by decide +kernel
theorem row_9_125 : ThresholdAt 9 125 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 125 0 cell_9_125_0
  | exact S 9 125 1 cell_9_125_1
  | exact S 9 125 2 cell_9_125_2
  | exact S 9 125 3 cell_9_125_3
  | exact S 9 125 4 cell_9_125_4
  | exact S 9 125 5 cell_9_125_5
theorem cell_9_126_0 : C 9 126 0 := by decide +kernel
theorem cell_9_126_1 : C 9 126 1 := by decide +kernel
theorem cell_9_126_2 : C 9 126 2 := by decide +kernel
theorem cell_9_126_3 : C 9 126 3 := by decide +kernel
theorem cell_9_126_4 : C 9 126 4 := by decide +kernel
theorem cell_9_126_5 : C 9 126 5 := by decide +kernel
theorem row_9_126 : ThresholdAt 9 126 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 126 0 cell_9_126_0
  | exact S 9 126 1 cell_9_126_1
  | exact S 9 126 2 cell_9_126_2
  | exact S 9 126 3 cell_9_126_3
  | exact S 9 126 4 cell_9_126_4
  | exact S 9 126 5 cell_9_126_5
theorem cell_9_127_0 : C 9 127 0 := by decide +kernel
theorem cell_9_127_1 : C 9 127 1 := by decide +kernel
theorem cell_9_127_2 : C 9 127 2 := by decide +kernel
theorem cell_9_127_3 : C 9 127 3 := by decide +kernel
theorem cell_9_127_4 : C 9 127 4 := by decide +kernel
theorem cell_9_127_5 : C 9 127 5 := by decide +kernel
theorem row_9_127 : ThresholdAt 9 127 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 127 0 cell_9_127_0
  | exact S 9 127 1 cell_9_127_1
  | exact S 9 127 2 cell_9_127_2
  | exact S 9 127 3 cell_9_127_3
  | exact S 9 127 4 cell_9_127_4
  | exact S 9 127 5 cell_9_127_5
theorem cell_9_128_0 : C 9 128 0 := by decide +kernel
theorem cell_9_128_1 : C 9 128 1 := by decide +kernel
theorem cell_9_128_2 : C 9 128 2 := by decide +kernel
theorem cell_9_128_3 : C 9 128 3 := by decide +kernel
theorem cell_9_128_4 : C 9 128 4 := by decide +kernel
theorem cell_9_128_5 : C 9 128 5 := by decide +kernel
theorem row_9_128 : ThresholdAt 9 128 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 128 0 cell_9_128_0
  | exact S 9 128 1 cell_9_128_1
  | exact S 9 128 2 cell_9_128_2
  | exact S 9 128 3 cell_9_128_3
  | exact S 9 128 4 cell_9_128_4
  | exact S 9 128 5 cell_9_128_5
theorem cell_9_129_0 : C 9 129 0 := by decide +kernel
theorem cell_9_129_1 : C 9 129 1 := by decide +kernel
theorem cell_9_129_2 : C 9 129 2 := by decide +kernel
theorem cell_9_129_3 : C 9 129 3 := by decide +kernel
theorem cell_9_129_4 : C 9 129 4 := by decide +kernel
theorem cell_9_129_5 : C 9 129 5 := by decide +kernel
theorem row_9_129 : ThresholdAt 9 129 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 129 0 cell_9_129_0
  | exact S 9 129 1 cell_9_129_1
  | exact S 9 129 2 cell_9_129_2
  | exact S 9 129 3 cell_9_129_3
  | exact S 9 129 4 cell_9_129_4
  | exact S 9 129 5 cell_9_129_5
theorem cell_9_130_0 : C 9 130 0 := by decide +kernel
theorem cell_9_130_1 : C 9 130 1 := by decide +kernel
theorem cell_9_130_2 : C 9 130 2 := by decide +kernel
theorem cell_9_130_3 : C 9 130 3 := by decide +kernel
theorem cell_9_130_4 : C 9 130 4 := by decide +kernel
theorem cell_9_130_5 : C 9 130 5 := by decide +kernel
theorem row_9_130 : ThresholdAt 9 130 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 9 130 0 cell_9_130_0
  | exact S 9 130 1 cell_9_130_1
  | exact S 9 130 2 cell_9_130_2
  | exact S 9 130 3 cell_9_130_3
  | exact S 9 130 4 cell_9_130_4
  | exact S 9 130 5 cell_9_130_5
theorem checkedR9 : ∀ V ∈ List.range 131, ThresholdAt 9 V := by
  intro V hV
  have hv : V < 131 := List.mem_range.mp hV
  by_cases h0_131 : V < 65
  · by_cases h0_65 : V < 32
    · by_cases h0_32 : V < 16
      · by_cases h0_16 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have he : V = 0 := by omega
                subst V
                exact row_9_0
              · have he : V = 1 := by omega
                subst V
                exact row_9_1
            · by_cases h2_4 : V < 3
              · have he : V = 2 := by omega
                subst V
                exact row_9_2
              · have he : V = 3 := by omega
                subst V
                exact row_9_3
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have he : V = 4 := by omega
                subst V
                exact row_9_4
              · have he : V = 5 := by omega
                subst V
                exact row_9_5
            · by_cases h6_8 : V < 7
              · have he : V = 6 := by omega
                subst V
                exact row_9_6
              · have he : V = 7 := by omega
                subst V
                exact row_9_7
        · by_cases h8_16 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have he : V = 8 := by omega
                subst V
                exact row_9_8
              · have he : V = 9 := by omega
                subst V
                exact row_9_9
            · by_cases h10_12 : V < 11
              · have he : V = 10 := by omega
                subst V
                exact row_9_10
              · have he : V = 11 := by omega
                subst V
                exact row_9_11
          · by_cases h12_16 : V < 14
            · by_cases h12_14 : V < 13
              · have he : V = 12 := by omega
                subst V
                exact row_9_12
              · have he : V = 13 := by omega
                subst V
                exact row_9_13
            · by_cases h14_16 : V < 15
              · have he : V = 14 := by omega
                subst V
                exact row_9_14
              · have he : V = 15 := by omega
                subst V
                exact row_9_15
      · by_cases h16_32 : V < 24
        · by_cases h16_24 : V < 20
          · by_cases h16_20 : V < 18
            · by_cases h16_18 : V < 17
              · have he : V = 16 := by omega
                subst V
                exact row_9_16
              · have he : V = 17 := by omega
                subst V
                exact row_9_17
            · by_cases h18_20 : V < 19
              · have he : V = 18 := by omega
                subst V
                exact row_9_18
              · have he : V = 19 := by omega
                subst V
                exact row_9_19
          · by_cases h20_24 : V < 22
            · by_cases h20_22 : V < 21
              · have he : V = 20 := by omega
                subst V
                exact row_9_20
              · have he : V = 21 := by omega
                subst V
                exact row_9_21
            · by_cases h22_24 : V < 23
              · have he : V = 22 := by omega
                subst V
                exact row_9_22
              · have he : V = 23 := by omega
                subst V
                exact row_9_23
        · by_cases h24_32 : V < 28
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have he : V = 24 := by omega
                subst V
                exact row_9_24
              · have he : V = 25 := by omega
                subst V
                exact row_9_25
            · by_cases h26_28 : V < 27
              · have he : V = 26 := by omega
                subst V
                exact row_9_26
              · have he : V = 27 := by omega
                subst V
                exact row_9_27
          · by_cases h28_32 : V < 30
            · by_cases h28_30 : V < 29
              · have he : V = 28 := by omega
                subst V
                exact row_9_28
              · have he : V = 29 := by omega
                subst V
                exact row_9_29
            · by_cases h30_32 : V < 31
              · have he : V = 30 := by omega
                subst V
                exact row_9_30
              · have he : V = 31 := by omega
                subst V
                exact row_9_31
    · by_cases h32_65 : V < 48
      · by_cases h32_48 : V < 40
        · by_cases h32_40 : V < 36
          · by_cases h32_36 : V < 34
            · by_cases h32_34 : V < 33
              · have he : V = 32 := by omega
                subst V
                exact row_9_32
              · have he : V = 33 := by omega
                subst V
                exact row_9_33
            · by_cases h34_36 : V < 35
              · have he : V = 34 := by omega
                subst V
                exact row_9_34
              · have he : V = 35 := by omega
                subst V
                exact row_9_35
          · by_cases h36_40 : V < 38
            · by_cases h36_38 : V < 37
              · have he : V = 36 := by omega
                subst V
                exact row_9_36
              · have he : V = 37 := by omega
                subst V
                exact row_9_37
            · by_cases h38_40 : V < 39
              · have he : V = 38 := by omega
                subst V
                exact row_9_38
              · have he : V = 39 := by omega
                subst V
                exact row_9_39
        · by_cases h40_48 : V < 44
          · by_cases h40_44 : V < 42
            · by_cases h40_42 : V < 41
              · have he : V = 40 := by omega
                subst V
                exact row_9_40
              · have he : V = 41 := by omega
                subst V
                exact row_9_41
            · by_cases h42_44 : V < 43
              · have he : V = 42 := by omega
                subst V
                exact row_9_42
              · have he : V = 43 := by omega
                subst V
                exact row_9_43
          · by_cases h44_48 : V < 46
            · by_cases h44_46 : V < 45
              · have he : V = 44 := by omega
                subst V
                exact row_9_44
              · have he : V = 45 := by omega
                subst V
                exact row_9_45
            · by_cases h46_48 : V < 47
              · have he : V = 46 := by omega
                subst V
                exact row_9_46
              · have he : V = 47 := by omega
                subst V
                exact row_9_47
      · by_cases h48_65 : V < 56
        · by_cases h48_56 : V < 52
          · by_cases h48_52 : V < 50
            · by_cases h48_50 : V < 49
              · have he : V = 48 := by omega
                subst V
                exact row_9_48
              · have he : V = 49 := by omega
                subst V
                exact row_9_49
            · by_cases h50_52 : V < 51
              · have he : V = 50 := by omega
                subst V
                exact row_9_50
              · have he : V = 51 := by omega
                subst V
                exact row_9_51
          · by_cases h52_56 : V < 54
            · by_cases h52_54 : V < 53
              · have he : V = 52 := by omega
                subst V
                exact row_9_52
              · have he : V = 53 := by omega
                subst V
                exact row_9_53
            · by_cases h54_56 : V < 55
              · have he : V = 54 := by omega
                subst V
                exact row_9_54
              · have he : V = 55 := by omega
                subst V
                exact row_9_55
        · by_cases h56_65 : V < 60
          · by_cases h56_60 : V < 58
            · by_cases h56_58 : V < 57
              · have he : V = 56 := by omega
                subst V
                exact row_9_56
              · have he : V = 57 := by omega
                subst V
                exact row_9_57
            · by_cases h58_60 : V < 59
              · have he : V = 58 := by omega
                subst V
                exact row_9_58
              · have he : V = 59 := by omega
                subst V
                exact row_9_59
          · by_cases h60_65 : V < 62
            · by_cases h60_62 : V < 61
              · have he : V = 60 := by omega
                subst V
                exact row_9_60
              · have he : V = 61 := by omega
                subst V
                exact row_9_61
            · by_cases h62_65 : V < 63
              · have he : V = 62 := by omega
                subst V
                exact row_9_62
              · by_cases h63_65 : V < 64
                · have he : V = 63 := by omega
                  subst V
                  exact row_9_63
                · have he : V = 64 := by omega
                  subst V
                  exact row_9_64
  · by_cases h65_131 : V < 98
    · by_cases h65_98 : V < 81
      · by_cases h65_81 : V < 73
        · by_cases h65_73 : V < 69
          · by_cases h65_69 : V < 67
            · by_cases h65_67 : V < 66
              · have he : V = 65 := by omega
                subst V
                exact row_9_65
              · have he : V = 66 := by omega
                subst V
                exact row_9_66
            · by_cases h67_69 : V < 68
              · have he : V = 67 := by omega
                subst V
                exact row_9_67
              · have he : V = 68 := by omega
                subst V
                exact row_9_68
          · by_cases h69_73 : V < 71
            · by_cases h69_71 : V < 70
              · have he : V = 69 := by omega
                subst V
                exact row_9_69
              · have he : V = 70 := by omega
                subst V
                exact row_9_70
            · by_cases h71_73 : V < 72
              · have he : V = 71 := by omega
                subst V
                exact row_9_71
              · have he : V = 72 := by omega
                subst V
                exact row_9_72
        · by_cases h73_81 : V < 77
          · by_cases h73_77 : V < 75
            · by_cases h73_75 : V < 74
              · have he : V = 73 := by omega
                subst V
                exact row_9_73
              · have he : V = 74 := by omega
                subst V
                exact row_9_74
            · by_cases h75_77 : V < 76
              · have he : V = 75 := by omega
                subst V
                exact row_9_75
              · have he : V = 76 := by omega
                subst V
                exact row_9_76
          · by_cases h77_81 : V < 79
            · by_cases h77_79 : V < 78
              · have he : V = 77 := by omega
                subst V
                exact row_9_77
              · have he : V = 78 := by omega
                subst V
                exact row_9_78
            · by_cases h79_81 : V < 80
              · have he : V = 79 := by omega
                subst V
                exact row_9_79
              · have he : V = 80 := by omega
                subst V
                exact row_9_80
      · by_cases h81_98 : V < 89
        · by_cases h81_89 : V < 85
          · by_cases h81_85 : V < 83
            · by_cases h81_83 : V < 82
              · have he : V = 81 := by omega
                subst V
                exact row_9_81
              · have he : V = 82 := by omega
                subst V
                exact row_9_82
            · by_cases h83_85 : V < 84
              · have he : V = 83 := by omega
                subst V
                exact row_9_83
              · have he : V = 84 := by omega
                subst V
                exact row_9_84
          · by_cases h85_89 : V < 87
            · by_cases h85_87 : V < 86
              · have he : V = 85 := by omega
                subst V
                exact row_9_85
              · have he : V = 86 := by omega
                subst V
                exact row_9_86
            · by_cases h87_89 : V < 88
              · have he : V = 87 := by omega
                subst V
                exact row_9_87
              · have he : V = 88 := by omega
                subst V
                exact row_9_88
        · by_cases h89_98 : V < 93
          · by_cases h89_93 : V < 91
            · by_cases h89_91 : V < 90
              · have he : V = 89 := by omega
                subst V
                exact row_9_89
              · have he : V = 90 := by omega
                subst V
                exact row_9_90
            · by_cases h91_93 : V < 92
              · have he : V = 91 := by omega
                subst V
                exact row_9_91
              · have he : V = 92 := by omega
                subst V
                exact row_9_92
          · by_cases h93_98 : V < 95
            · by_cases h93_95 : V < 94
              · have he : V = 93 := by omega
                subst V
                exact row_9_93
              · have he : V = 94 := by omega
                subst V
                exact row_9_94
            · by_cases h95_98 : V < 96
              · have he : V = 95 := by omega
                subst V
                exact row_9_95
              · by_cases h96_98 : V < 97
                · have he : V = 96 := by omega
                  subst V
                  exact row_9_96
                · have he : V = 97 := by omega
                  subst V
                  exact row_9_97
    · by_cases h98_131 : V < 114
      · by_cases h98_114 : V < 106
        · by_cases h98_106 : V < 102
          · by_cases h98_102 : V < 100
            · by_cases h98_100 : V < 99
              · have he : V = 98 := by omega
                subst V
                exact row_9_98
              · have he : V = 99 := by omega
                subst V
                exact row_9_99
            · by_cases h100_102 : V < 101
              · have he : V = 100 := by omega
                subst V
                exact row_9_100
              · have he : V = 101 := by omega
                subst V
                exact row_9_101
          · by_cases h102_106 : V < 104
            · by_cases h102_104 : V < 103
              · have he : V = 102 := by omega
                subst V
                exact row_9_102
              · have he : V = 103 := by omega
                subst V
                exact row_9_103
            · by_cases h104_106 : V < 105
              · have he : V = 104 := by omega
                subst V
                exact row_9_104
              · have he : V = 105 := by omega
                subst V
                exact row_9_105
        · by_cases h106_114 : V < 110
          · by_cases h106_110 : V < 108
            · by_cases h106_108 : V < 107
              · have he : V = 106 := by omega
                subst V
                exact row_9_106
              · have he : V = 107 := by omega
                subst V
                exact row_9_107
            · by_cases h108_110 : V < 109
              · have he : V = 108 := by omega
                subst V
                exact row_9_108
              · have he : V = 109 := by omega
                subst V
                exact row_9_109
          · by_cases h110_114 : V < 112
            · by_cases h110_112 : V < 111
              · have he : V = 110 := by omega
                subst V
                exact row_9_110
              · have he : V = 111 := by omega
                subst V
                exact row_9_111
            · by_cases h112_114 : V < 113
              · have he : V = 112 := by omega
                subst V
                exact row_9_112
              · have he : V = 113 := by omega
                subst V
                exact row_9_113
      · by_cases h114_131 : V < 122
        · by_cases h114_122 : V < 118
          · by_cases h114_118 : V < 116
            · by_cases h114_116 : V < 115
              · have he : V = 114 := by omega
                subst V
                exact row_9_114
              · have he : V = 115 := by omega
                subst V
                exact row_9_115
            · by_cases h116_118 : V < 117
              · have he : V = 116 := by omega
                subst V
                exact row_9_116
              · have he : V = 117 := by omega
                subst V
                exact row_9_117
          · by_cases h118_122 : V < 120
            · by_cases h118_120 : V < 119
              · have he : V = 118 := by omega
                subst V
                exact row_9_118
              · have he : V = 119 := by omega
                subst V
                exact row_9_119
            · by_cases h120_122 : V < 121
              · have he : V = 120 := by omega
                subst V
                exact row_9_120
              · have he : V = 121 := by omega
                subst V
                exact row_9_121
        · by_cases h122_131 : V < 126
          · by_cases h122_126 : V < 124
            · by_cases h122_124 : V < 123
              · have he : V = 122 := by omega
                subst V
                exact row_9_122
              · have he : V = 123 := by omega
                subst V
                exact row_9_123
            · by_cases h124_126 : V < 125
              · have he : V = 124 := by omega
                subst V
                exact row_9_124
              · have he : V = 125 := by omega
                subst V
                exact row_9_125
          · by_cases h126_131 : V < 128
            · by_cases h126_128 : V < 127
              · have he : V = 126 := by omega
                subst V
                exact row_9_126
              · have he : V = 127 := by omega
                subst V
                exact row_9_127
            · by_cases h128_131 : V < 129
              · have he : V = 128 := by omega
                subst V
                exact row_9_128
              · by_cases h129_131 : V < 130
                · have he : V = 129 := by omega
                  subst V
                  exact row_9_129
                · have he : V = 130 := by omega
                  subst V
                  exact row_9_130
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
