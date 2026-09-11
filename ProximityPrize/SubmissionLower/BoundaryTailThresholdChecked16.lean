import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked15

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem cell_16_0_0 : C 16 0 0 := by decide +kernel
theorem cell_16_0_1 : C 16 0 1 := by decide +kernel
theorem cell_16_0_2 : C 16 0 2 := by decide +kernel
theorem cell_16_0_3 : C 16 0 3 := by decide +kernel
theorem cell_16_0_4 : C 16 0 4 := by decide +kernel
theorem cell_16_0_5 : C 16 0 5 := by decide +kernel
theorem row_16_0 : ThresholdAt 16 0 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 0 0 cell_16_0_0
  | exact S 16 0 1 cell_16_0_1
  | exact S 16 0 2 cell_16_0_2
  | exact S 16 0 3 cell_16_0_3
  | exact S 16 0 4 cell_16_0_4
  | exact S 16 0 5 cell_16_0_5
theorem cell_16_1_0 : C 16 1 0 := by decide +kernel
theorem cell_16_1_1 : C 16 1 1 := by decide +kernel
theorem cell_16_1_2 : C 16 1 2 := by decide +kernel
theorem cell_16_1_3 : C 16 1 3 := by decide +kernel
theorem cell_16_1_4 : C 16 1 4 := by decide +kernel
theorem cell_16_1_5 : C 16 1 5 := by decide +kernel
theorem row_16_1 : ThresholdAt 16 1 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 1 0 cell_16_1_0
  | exact S 16 1 1 cell_16_1_1
  | exact S 16 1 2 cell_16_1_2
  | exact S 16 1 3 cell_16_1_3
  | exact S 16 1 4 cell_16_1_4
  | exact S 16 1 5 cell_16_1_5
theorem cell_16_2_0 : C 16 2 0 := by decide +kernel
theorem cell_16_2_1 : C 16 2 1 := by decide +kernel
theorem cell_16_2_2 : C 16 2 2 := by decide +kernel
theorem cell_16_2_3 : C 16 2 3 := by decide +kernel
theorem cell_16_2_4 : C 16 2 4 := by decide +kernel
theorem cell_16_2_5 : C 16 2 5 := by decide +kernel
theorem row_16_2 : ThresholdAt 16 2 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 2 0 cell_16_2_0
  | exact S 16 2 1 cell_16_2_1
  | exact S 16 2 2 cell_16_2_2
  | exact S 16 2 3 cell_16_2_3
  | exact S 16 2 4 cell_16_2_4
  | exact S 16 2 5 cell_16_2_5
theorem cell_16_3_0 : C 16 3 0 := by decide +kernel
theorem cell_16_3_1 : C 16 3 1 := by decide +kernel
theorem cell_16_3_2 : C 16 3 2 := by decide +kernel
theorem cell_16_3_3 : C 16 3 3 := by decide +kernel
theorem cell_16_3_4 : C 16 3 4 := by decide +kernel
theorem cell_16_3_5 : C 16 3 5 := by decide +kernel
theorem row_16_3 : ThresholdAt 16 3 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 3 0 cell_16_3_0
  | exact S 16 3 1 cell_16_3_1
  | exact S 16 3 2 cell_16_3_2
  | exact S 16 3 3 cell_16_3_3
  | exact S 16 3 4 cell_16_3_4
  | exact S 16 3 5 cell_16_3_5
theorem cell_16_4_0 : C 16 4 0 := by decide +kernel
theorem cell_16_4_1 : C 16 4 1 := by decide +kernel
theorem cell_16_4_2 : C 16 4 2 := by decide +kernel
theorem cell_16_4_3 : C 16 4 3 := by decide +kernel
theorem cell_16_4_4 : C 16 4 4 := by decide +kernel
theorem cell_16_4_5 : C 16 4 5 := by decide +kernel
theorem row_16_4 : ThresholdAt 16 4 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 4 0 cell_16_4_0
  | exact S 16 4 1 cell_16_4_1
  | exact S 16 4 2 cell_16_4_2
  | exact S 16 4 3 cell_16_4_3
  | exact S 16 4 4 cell_16_4_4
  | exact S 16 4 5 cell_16_4_5
theorem cell_16_5_0 : C 16 5 0 := by decide +kernel
theorem cell_16_5_1 : C 16 5 1 := by decide +kernel
theorem cell_16_5_2 : C 16 5 2 := by decide +kernel
theorem cell_16_5_3 : C 16 5 3 := by decide +kernel
theorem cell_16_5_4 : C 16 5 4 := by decide +kernel
theorem cell_16_5_5 : C 16 5 5 := by decide +kernel
theorem row_16_5 : ThresholdAt 16 5 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 5 0 cell_16_5_0
  | exact S 16 5 1 cell_16_5_1
  | exact S 16 5 2 cell_16_5_2
  | exact S 16 5 3 cell_16_5_3
  | exact S 16 5 4 cell_16_5_4
  | exact S 16 5 5 cell_16_5_5
theorem cell_16_6_0 : C 16 6 0 := by decide +kernel
theorem cell_16_6_1 : C 16 6 1 := by decide +kernel
theorem cell_16_6_2 : C 16 6 2 := by decide +kernel
theorem cell_16_6_3 : C 16 6 3 := by decide +kernel
theorem cell_16_6_4 : C 16 6 4 := by decide +kernel
theorem cell_16_6_5 : C 16 6 5 := by decide +kernel
theorem row_16_6 : ThresholdAt 16 6 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 6 0 cell_16_6_0
  | exact S 16 6 1 cell_16_6_1
  | exact S 16 6 2 cell_16_6_2
  | exact S 16 6 3 cell_16_6_3
  | exact S 16 6 4 cell_16_6_4
  | exact S 16 6 5 cell_16_6_5
theorem cell_16_7_0 : C 16 7 0 := by decide +kernel
theorem cell_16_7_1 : C 16 7 1 := by decide +kernel
theorem cell_16_7_2 : C 16 7 2 := by decide +kernel
theorem cell_16_7_3 : C 16 7 3 := by decide +kernel
theorem cell_16_7_4 : C 16 7 4 := by decide +kernel
theorem cell_16_7_5 : C 16 7 5 := by decide +kernel
theorem row_16_7 : ThresholdAt 16 7 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 7 0 cell_16_7_0
  | exact S 16 7 1 cell_16_7_1
  | exact S 16 7 2 cell_16_7_2
  | exact S 16 7 3 cell_16_7_3
  | exact S 16 7 4 cell_16_7_4
  | exact S 16 7 5 cell_16_7_5
theorem cell_16_8_0 : C 16 8 0 := by decide +kernel
theorem cell_16_8_1 : C 16 8 1 := by decide +kernel
theorem cell_16_8_2 : C 16 8 2 := by decide +kernel
theorem cell_16_8_3 : C 16 8 3 := by decide +kernel
theorem cell_16_8_4 : C 16 8 4 := by decide +kernel
theorem cell_16_8_5 : C 16 8 5 := by decide +kernel
theorem row_16_8 : ThresholdAt 16 8 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 8 0 cell_16_8_0
  | exact S 16 8 1 cell_16_8_1
  | exact S 16 8 2 cell_16_8_2
  | exact S 16 8 3 cell_16_8_3
  | exact S 16 8 4 cell_16_8_4
  | exact S 16 8 5 cell_16_8_5
theorem cell_16_9_0 : C 16 9 0 := by decide +kernel
theorem cell_16_9_1 : C 16 9 1 := by decide +kernel
theorem cell_16_9_2 : C 16 9 2 := by decide +kernel
theorem cell_16_9_3 : C 16 9 3 := by decide +kernel
theorem cell_16_9_4 : C 16 9 4 := by decide +kernel
theorem cell_16_9_5 : C 16 9 5 := by decide +kernel
theorem row_16_9 : ThresholdAt 16 9 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 9 0 cell_16_9_0
  | exact S 16 9 1 cell_16_9_1
  | exact S 16 9 2 cell_16_9_2
  | exact S 16 9 3 cell_16_9_3
  | exact S 16 9 4 cell_16_9_4
  | exact S 16 9 5 cell_16_9_5
theorem cell_16_10_0 : C 16 10 0 := by decide +kernel
theorem cell_16_10_1 : C 16 10 1 := by decide +kernel
theorem cell_16_10_2 : C 16 10 2 := by decide +kernel
theorem cell_16_10_3 : C 16 10 3 := by decide +kernel
theorem cell_16_10_4 : C 16 10 4 := by decide +kernel
theorem cell_16_10_5 : C 16 10 5 := by decide +kernel
theorem row_16_10 : ThresholdAt 16 10 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 10 0 cell_16_10_0
  | exact S 16 10 1 cell_16_10_1
  | exact S 16 10 2 cell_16_10_2
  | exact S 16 10 3 cell_16_10_3
  | exact S 16 10 4 cell_16_10_4
  | exact S 16 10 5 cell_16_10_5
theorem cell_16_11_0 : C 16 11 0 := by decide +kernel
theorem cell_16_11_1 : C 16 11 1 := by decide +kernel
theorem cell_16_11_2 : C 16 11 2 := by decide +kernel
theorem cell_16_11_3 : C 16 11 3 := by decide +kernel
theorem cell_16_11_4 : C 16 11 4 := by decide +kernel
theorem cell_16_11_5 : C 16 11 5 := by decide +kernel
theorem row_16_11 : ThresholdAt 16 11 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 11 0 cell_16_11_0
  | exact S 16 11 1 cell_16_11_1
  | exact S 16 11 2 cell_16_11_2
  | exact S 16 11 3 cell_16_11_3
  | exact S 16 11 4 cell_16_11_4
  | exact S 16 11 5 cell_16_11_5
theorem cell_16_12_0 : C 16 12 0 := by decide +kernel
theorem cell_16_12_1 : C 16 12 1 := by decide +kernel
theorem cell_16_12_2 : C 16 12 2 := by decide +kernel
theorem cell_16_12_3 : C 16 12 3 := by decide +kernel
theorem cell_16_12_4 : C 16 12 4 := by decide +kernel
theorem cell_16_12_5 : C 16 12 5 := by decide +kernel
theorem row_16_12 : ThresholdAt 16 12 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 12 0 cell_16_12_0
  | exact S 16 12 1 cell_16_12_1
  | exact S 16 12 2 cell_16_12_2
  | exact S 16 12 3 cell_16_12_3
  | exact S 16 12 4 cell_16_12_4
  | exact S 16 12 5 cell_16_12_5
theorem cell_16_13_0 : C 16 13 0 := by decide +kernel
theorem cell_16_13_1 : C 16 13 1 := by decide +kernel
theorem cell_16_13_2 : C 16 13 2 := by decide +kernel
theorem cell_16_13_3 : C 16 13 3 := by decide +kernel
theorem cell_16_13_4 : C 16 13 4 := by decide +kernel
theorem cell_16_13_5 : C 16 13 5 := by decide +kernel
theorem row_16_13 : ThresholdAt 16 13 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 13 0 cell_16_13_0
  | exact S 16 13 1 cell_16_13_1
  | exact S 16 13 2 cell_16_13_2
  | exact S 16 13 3 cell_16_13_3
  | exact S 16 13 4 cell_16_13_4
  | exact S 16 13 5 cell_16_13_5
theorem cell_16_14_0 : C 16 14 0 := by decide +kernel
theorem cell_16_14_1 : C 16 14 1 := by decide +kernel
theorem cell_16_14_2 : C 16 14 2 := by decide +kernel
theorem cell_16_14_3 : C 16 14 3 := by decide +kernel
theorem cell_16_14_4 : C 16 14 4 := by decide +kernel
theorem cell_16_14_5 : C 16 14 5 := by decide +kernel
theorem row_16_14 : ThresholdAt 16 14 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 14 0 cell_16_14_0
  | exact S 16 14 1 cell_16_14_1
  | exact S 16 14 2 cell_16_14_2
  | exact S 16 14 3 cell_16_14_3
  | exact S 16 14 4 cell_16_14_4
  | exact S 16 14 5 cell_16_14_5
theorem cell_16_15_0 : C 16 15 0 := by decide +kernel
theorem cell_16_15_1 : C 16 15 1 := by decide +kernel
theorem cell_16_15_2 : C 16 15 2 := by decide +kernel
theorem cell_16_15_3 : C 16 15 3 := by decide +kernel
theorem cell_16_15_4 : C 16 15 4 := by decide +kernel
theorem cell_16_15_5 : C 16 15 5 := by decide +kernel
theorem row_16_15 : ThresholdAt 16 15 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 15 0 cell_16_15_0
  | exact S 16 15 1 cell_16_15_1
  | exact S 16 15 2 cell_16_15_2
  | exact S 16 15 3 cell_16_15_3
  | exact S 16 15 4 cell_16_15_4
  | exact S 16 15 5 cell_16_15_5
theorem cell_16_16_0 : C 16 16 0 := by decide +kernel
theorem cell_16_16_1 : C 16 16 1 := by decide +kernel
theorem cell_16_16_2 : C 16 16 2 := by decide +kernel
theorem cell_16_16_3 : C 16 16 3 := by decide +kernel
theorem cell_16_16_4 : C 16 16 4 := by decide +kernel
theorem cell_16_16_5 : C 16 16 5 := by decide +kernel
theorem row_16_16 : ThresholdAt 16 16 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 16 0 cell_16_16_0
  | exact S 16 16 1 cell_16_16_1
  | exact S 16 16 2 cell_16_16_2
  | exact S 16 16 3 cell_16_16_3
  | exact S 16 16 4 cell_16_16_4
  | exact S 16 16 5 cell_16_16_5
theorem cell_16_17_0 : C 16 17 0 := by decide +kernel
theorem cell_16_17_1 : C 16 17 1 := by decide +kernel
theorem cell_16_17_2 : C 16 17 2 := by decide +kernel
theorem cell_16_17_3 : C 16 17 3 := by decide +kernel
theorem cell_16_17_4 : C 16 17 4 := by decide +kernel
theorem cell_16_17_5 : C 16 17 5 := by decide +kernel
theorem row_16_17 : ThresholdAt 16 17 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 17 0 cell_16_17_0
  | exact S 16 17 1 cell_16_17_1
  | exact S 16 17 2 cell_16_17_2
  | exact S 16 17 3 cell_16_17_3
  | exact S 16 17 4 cell_16_17_4
  | exact S 16 17 5 cell_16_17_5
theorem cell_16_18_0 : C 16 18 0 := by decide +kernel
theorem cell_16_18_1 : C 16 18 1 := by decide +kernel
theorem cell_16_18_2 : C 16 18 2 := by decide +kernel
theorem cell_16_18_3 : C 16 18 3 := by decide +kernel
theorem cell_16_18_4 : C 16 18 4 := by decide +kernel
theorem cell_16_18_5 : C 16 18 5 := by decide +kernel
theorem row_16_18 : ThresholdAt 16 18 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 18 0 cell_16_18_0
  | exact S 16 18 1 cell_16_18_1
  | exact S 16 18 2 cell_16_18_2
  | exact S 16 18 3 cell_16_18_3
  | exact S 16 18 4 cell_16_18_4
  | exact S 16 18 5 cell_16_18_5
theorem cell_16_19_0 : C 16 19 0 := by decide +kernel
theorem cell_16_19_1 : C 16 19 1 := by decide +kernel
theorem cell_16_19_2 : C 16 19 2 := by decide +kernel
theorem cell_16_19_3 : C 16 19 3 := by decide +kernel
theorem cell_16_19_4 : C 16 19 4 := by decide +kernel
theorem cell_16_19_5 : C 16 19 5 := by decide +kernel
theorem row_16_19 : ThresholdAt 16 19 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 19 0 cell_16_19_0
  | exact S 16 19 1 cell_16_19_1
  | exact S 16 19 2 cell_16_19_2
  | exact S 16 19 3 cell_16_19_3
  | exact S 16 19 4 cell_16_19_4
  | exact S 16 19 5 cell_16_19_5
theorem cell_16_20_0 : C 16 20 0 := by decide +kernel
theorem cell_16_20_1 : C 16 20 1 := by decide +kernel
theorem cell_16_20_2 : C 16 20 2 := by decide +kernel
theorem cell_16_20_3 : C 16 20 3 := by decide +kernel
theorem cell_16_20_4 : C 16 20 4 := by decide +kernel
theorem cell_16_20_5 : C 16 20 5 := by decide +kernel
theorem row_16_20 : ThresholdAt 16 20 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 20 0 cell_16_20_0
  | exact S 16 20 1 cell_16_20_1
  | exact S 16 20 2 cell_16_20_2
  | exact S 16 20 3 cell_16_20_3
  | exact S 16 20 4 cell_16_20_4
  | exact S 16 20 5 cell_16_20_5
theorem cell_16_21_0 : C 16 21 0 := by decide +kernel
theorem cell_16_21_1 : C 16 21 1 := by decide +kernel
theorem cell_16_21_2 : C 16 21 2 := by decide +kernel
theorem cell_16_21_3 : C 16 21 3 := by decide +kernel
theorem cell_16_21_4 : C 16 21 4 := by decide +kernel
theorem cell_16_21_5 : C 16 21 5 := by decide +kernel
theorem row_16_21 : ThresholdAt 16 21 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 21 0 cell_16_21_0
  | exact S 16 21 1 cell_16_21_1
  | exact S 16 21 2 cell_16_21_2
  | exact S 16 21 3 cell_16_21_3
  | exact S 16 21 4 cell_16_21_4
  | exact S 16 21 5 cell_16_21_5
theorem cell_16_22_0 : C 16 22 0 := by decide +kernel
theorem cell_16_22_1 : C 16 22 1 := by decide +kernel
theorem cell_16_22_2 : C 16 22 2 := by decide +kernel
theorem cell_16_22_3 : C 16 22 3 := by decide +kernel
theorem cell_16_22_4 : C 16 22 4 := by decide +kernel
theorem cell_16_22_5 : C 16 22 5 := by decide +kernel
theorem row_16_22 : ThresholdAt 16 22 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 22 0 cell_16_22_0
  | exact S 16 22 1 cell_16_22_1
  | exact S 16 22 2 cell_16_22_2
  | exact S 16 22 3 cell_16_22_3
  | exact S 16 22 4 cell_16_22_4
  | exact S 16 22 5 cell_16_22_5
theorem cell_16_23_0 : C 16 23 0 := by decide +kernel
theorem cell_16_23_1 : C 16 23 1 := by decide +kernel
theorem cell_16_23_2 : C 16 23 2 := by decide +kernel
theorem cell_16_23_3 : C 16 23 3 := by decide +kernel
theorem cell_16_23_4 : C 16 23 4 := by decide +kernel
theorem cell_16_23_5 : C 16 23 5 := by decide +kernel
theorem row_16_23 : ThresholdAt 16 23 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 23 0 cell_16_23_0
  | exact S 16 23 1 cell_16_23_1
  | exact S 16 23 2 cell_16_23_2
  | exact S 16 23 3 cell_16_23_3
  | exact S 16 23 4 cell_16_23_4
  | exact S 16 23 5 cell_16_23_5
theorem cell_16_24_0 : C 16 24 0 := by decide +kernel
theorem cell_16_24_1 : C 16 24 1 := by decide +kernel
theorem cell_16_24_2 : C 16 24 2 := by decide +kernel
theorem cell_16_24_3 : C 16 24 3 := by decide +kernel
theorem cell_16_24_4 : C 16 24 4 := by decide +kernel
theorem cell_16_24_5 : C 16 24 5 := by decide +kernel
theorem row_16_24 : ThresholdAt 16 24 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 24 0 cell_16_24_0
  | exact S 16 24 1 cell_16_24_1
  | exact S 16 24 2 cell_16_24_2
  | exact S 16 24 3 cell_16_24_3
  | exact S 16 24 4 cell_16_24_4
  | exact S 16 24 5 cell_16_24_5
theorem cell_16_25_0 : C 16 25 0 := by decide +kernel
theorem cell_16_25_1 : C 16 25 1 := by decide +kernel
theorem cell_16_25_2 : C 16 25 2 := by decide +kernel
theorem cell_16_25_3 : C 16 25 3 := by decide +kernel
theorem cell_16_25_4 : C 16 25 4 := by decide +kernel
theorem cell_16_25_5 : C 16 25 5 := by decide +kernel
theorem row_16_25 : ThresholdAt 16 25 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 25 0 cell_16_25_0
  | exact S 16 25 1 cell_16_25_1
  | exact S 16 25 2 cell_16_25_2
  | exact S 16 25 3 cell_16_25_3
  | exact S 16 25 4 cell_16_25_4
  | exact S 16 25 5 cell_16_25_5
theorem cell_16_26_0 : C 16 26 0 := by decide +kernel
theorem cell_16_26_1 : C 16 26 1 := by decide +kernel
theorem cell_16_26_2 : C 16 26 2 := by decide +kernel
theorem cell_16_26_3 : C 16 26 3 := by decide +kernel
theorem cell_16_26_4 : C 16 26 4 := by decide +kernel
theorem cell_16_26_5 : C 16 26 5 := by decide +kernel
theorem row_16_26 : ThresholdAt 16 26 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 26 0 cell_16_26_0
  | exact S 16 26 1 cell_16_26_1
  | exact S 16 26 2 cell_16_26_2
  | exact S 16 26 3 cell_16_26_3
  | exact S 16 26 4 cell_16_26_4
  | exact S 16 26 5 cell_16_26_5
theorem cell_16_27_0 : C 16 27 0 := by decide +kernel
theorem cell_16_27_1 : C 16 27 1 := by decide +kernel
theorem cell_16_27_2 : C 16 27 2 := by decide +kernel
theorem cell_16_27_3 : C 16 27 3 := by decide +kernel
theorem cell_16_27_4 : C 16 27 4 := by decide +kernel
theorem cell_16_27_5 : C 16 27 5 := by decide +kernel
theorem row_16_27 : ThresholdAt 16 27 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 27 0 cell_16_27_0
  | exact S 16 27 1 cell_16_27_1
  | exact S 16 27 2 cell_16_27_2
  | exact S 16 27 3 cell_16_27_3
  | exact S 16 27 4 cell_16_27_4
  | exact S 16 27 5 cell_16_27_5
theorem cell_16_28_0 : C 16 28 0 := by decide +kernel
theorem cell_16_28_1 : C 16 28 1 := by decide +kernel
theorem cell_16_28_2 : C 16 28 2 := by decide +kernel
theorem cell_16_28_3 : C 16 28 3 := by decide +kernel
theorem cell_16_28_4 : C 16 28 4 := by decide +kernel
theorem cell_16_28_5 : C 16 28 5 := by decide +kernel
theorem row_16_28 : ThresholdAt 16 28 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 28 0 cell_16_28_0
  | exact S 16 28 1 cell_16_28_1
  | exact S 16 28 2 cell_16_28_2
  | exact S 16 28 3 cell_16_28_3
  | exact S 16 28 4 cell_16_28_4
  | exact S 16 28 5 cell_16_28_5
theorem cell_16_29_0 : C 16 29 0 := by decide +kernel
theorem cell_16_29_1 : C 16 29 1 := by decide +kernel
theorem cell_16_29_2 : C 16 29 2 := by decide +kernel
theorem cell_16_29_3 : C 16 29 3 := by decide +kernel
theorem cell_16_29_4 : C 16 29 4 := by decide +kernel
theorem cell_16_29_5 : C 16 29 5 := by decide +kernel
theorem row_16_29 : ThresholdAt 16 29 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 29 0 cell_16_29_0
  | exact S 16 29 1 cell_16_29_1
  | exact S 16 29 2 cell_16_29_2
  | exact S 16 29 3 cell_16_29_3
  | exact S 16 29 4 cell_16_29_4
  | exact S 16 29 5 cell_16_29_5
theorem cell_16_30_0 : C 16 30 0 := by decide +kernel
theorem cell_16_30_1 : C 16 30 1 := by decide +kernel
theorem cell_16_30_2 : C 16 30 2 := by decide +kernel
theorem cell_16_30_3 : C 16 30 3 := by decide +kernel
theorem cell_16_30_4 : C 16 30 4 := by decide +kernel
theorem cell_16_30_5 : C 16 30 5 := by decide +kernel
theorem row_16_30 : ThresholdAt 16 30 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 30 0 cell_16_30_0
  | exact S 16 30 1 cell_16_30_1
  | exact S 16 30 2 cell_16_30_2
  | exact S 16 30 3 cell_16_30_3
  | exact S 16 30 4 cell_16_30_4
  | exact S 16 30 5 cell_16_30_5
theorem cell_16_31_0 : C 16 31 0 := by decide +kernel
theorem cell_16_31_1 : C 16 31 1 := by decide +kernel
theorem cell_16_31_2 : C 16 31 2 := by decide +kernel
theorem cell_16_31_3 : C 16 31 3 := by decide +kernel
theorem cell_16_31_4 : C 16 31 4 := by decide +kernel
theorem cell_16_31_5 : C 16 31 5 := by decide +kernel
theorem row_16_31 : ThresholdAt 16 31 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 31 0 cell_16_31_0
  | exact S 16 31 1 cell_16_31_1
  | exact S 16 31 2 cell_16_31_2
  | exact S 16 31 3 cell_16_31_3
  | exact S 16 31 4 cell_16_31_4
  | exact S 16 31 5 cell_16_31_5
theorem cell_16_32_0 : C 16 32 0 := by decide +kernel
theorem cell_16_32_1 : C 16 32 1 := by decide +kernel
theorem cell_16_32_2 : C 16 32 2 := by decide +kernel
theorem cell_16_32_3 : C 16 32 3 := by decide +kernel
theorem cell_16_32_4 : C 16 32 4 := by decide +kernel
theorem cell_16_32_5 : C 16 32 5 := by decide +kernel
theorem row_16_32 : ThresholdAt 16 32 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 32 0 cell_16_32_0
  | exact S 16 32 1 cell_16_32_1
  | exact S 16 32 2 cell_16_32_2
  | exact S 16 32 3 cell_16_32_3
  | exact S 16 32 4 cell_16_32_4
  | exact S 16 32 5 cell_16_32_5
theorem cell_16_33_0 : C 16 33 0 := by decide +kernel
theorem cell_16_33_1 : C 16 33 1 := by decide +kernel
theorem cell_16_33_2 : C 16 33 2 := by decide +kernel
theorem cell_16_33_3 : C 16 33 3 := by decide +kernel
theorem cell_16_33_4 : C 16 33 4 := by decide +kernel
theorem cell_16_33_5 : C 16 33 5 := by decide +kernel
theorem row_16_33 : ThresholdAt 16 33 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 33 0 cell_16_33_0
  | exact S 16 33 1 cell_16_33_1
  | exact S 16 33 2 cell_16_33_2
  | exact S 16 33 3 cell_16_33_3
  | exact S 16 33 4 cell_16_33_4
  | exact S 16 33 5 cell_16_33_5
theorem cell_16_34_0 : C 16 34 0 := by decide +kernel
theorem cell_16_34_1 : C 16 34 1 := by decide +kernel
theorem cell_16_34_2 : C 16 34 2 := by decide +kernel
theorem cell_16_34_3 : C 16 34 3 := by decide +kernel
theorem cell_16_34_4 : C 16 34 4 := by decide +kernel
theorem cell_16_34_5 : C 16 34 5 := by decide +kernel
theorem row_16_34 : ThresholdAt 16 34 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 34 0 cell_16_34_0
  | exact S 16 34 1 cell_16_34_1
  | exact S 16 34 2 cell_16_34_2
  | exact S 16 34 3 cell_16_34_3
  | exact S 16 34 4 cell_16_34_4
  | exact S 16 34 5 cell_16_34_5
theorem cell_16_35_0 : C 16 35 0 := by decide +kernel
theorem cell_16_35_1 : C 16 35 1 := by decide +kernel
theorem cell_16_35_2 : C 16 35 2 := by decide +kernel
theorem cell_16_35_3 : C 16 35 3 := by decide +kernel
theorem cell_16_35_4 : C 16 35 4 := by decide +kernel
theorem cell_16_35_5 : C 16 35 5 := by decide +kernel
theorem row_16_35 : ThresholdAt 16 35 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 35 0 cell_16_35_0
  | exact S 16 35 1 cell_16_35_1
  | exact S 16 35 2 cell_16_35_2
  | exact S 16 35 3 cell_16_35_3
  | exact S 16 35 4 cell_16_35_4
  | exact S 16 35 5 cell_16_35_5
theorem cell_16_36_0 : C 16 36 0 := by decide +kernel
theorem cell_16_36_1 : C 16 36 1 := by decide +kernel
theorem cell_16_36_2 : C 16 36 2 := by decide +kernel
theorem cell_16_36_3 : C 16 36 3 := by decide +kernel
theorem cell_16_36_4 : C 16 36 4 := by decide +kernel
theorem cell_16_36_5 : C 16 36 5 := by decide +kernel
theorem row_16_36 : ThresholdAt 16 36 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 36 0 cell_16_36_0
  | exact S 16 36 1 cell_16_36_1
  | exact S 16 36 2 cell_16_36_2
  | exact S 16 36 3 cell_16_36_3
  | exact S 16 36 4 cell_16_36_4
  | exact S 16 36 5 cell_16_36_5
theorem cell_16_37_0 : C 16 37 0 := by decide +kernel
theorem cell_16_37_1 : C 16 37 1 := by decide +kernel
theorem cell_16_37_2 : C 16 37 2 := by decide +kernel
theorem cell_16_37_3 : C 16 37 3 := by decide +kernel
theorem cell_16_37_4 : C 16 37 4 := by decide +kernel
theorem cell_16_37_5 : C 16 37 5 := by decide +kernel
theorem row_16_37 : ThresholdAt 16 37 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 37 0 cell_16_37_0
  | exact S 16 37 1 cell_16_37_1
  | exact S 16 37 2 cell_16_37_2
  | exact S 16 37 3 cell_16_37_3
  | exact S 16 37 4 cell_16_37_4
  | exact S 16 37 5 cell_16_37_5
theorem cell_16_38_0 : C 16 38 0 := by decide +kernel
theorem cell_16_38_1 : C 16 38 1 := by decide +kernel
theorem cell_16_38_2 : C 16 38 2 := by decide +kernel
theorem cell_16_38_3 : C 16 38 3 := by decide +kernel
theorem cell_16_38_4 : C 16 38 4 := by decide +kernel
theorem cell_16_38_5 : C 16 38 5 := by decide +kernel
theorem row_16_38 : ThresholdAt 16 38 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 38 0 cell_16_38_0
  | exact S 16 38 1 cell_16_38_1
  | exact S 16 38 2 cell_16_38_2
  | exact S 16 38 3 cell_16_38_3
  | exact S 16 38 4 cell_16_38_4
  | exact S 16 38 5 cell_16_38_5
theorem cell_16_39_0 : C 16 39 0 := by decide +kernel
theorem cell_16_39_1 : C 16 39 1 := by decide +kernel
theorem cell_16_39_2 : C 16 39 2 := by decide +kernel
theorem cell_16_39_3 : C 16 39 3 := by decide +kernel
theorem cell_16_39_4 : C 16 39 4 := by decide +kernel
theorem cell_16_39_5 : C 16 39 5 := by decide +kernel
theorem row_16_39 : ThresholdAt 16 39 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 39 0 cell_16_39_0
  | exact S 16 39 1 cell_16_39_1
  | exact S 16 39 2 cell_16_39_2
  | exact S 16 39 3 cell_16_39_3
  | exact S 16 39 4 cell_16_39_4
  | exact S 16 39 5 cell_16_39_5
theorem cell_16_40_0 : C 16 40 0 := by decide +kernel
theorem cell_16_40_1 : C 16 40 1 := by decide +kernel
theorem cell_16_40_2 : C 16 40 2 := by decide +kernel
theorem cell_16_40_3 : C 16 40 3 := by decide +kernel
theorem cell_16_40_4 : C 16 40 4 := by decide +kernel
theorem cell_16_40_5 : C 16 40 5 := by decide +kernel
theorem row_16_40 : ThresholdAt 16 40 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 40 0 cell_16_40_0
  | exact S 16 40 1 cell_16_40_1
  | exact S 16 40 2 cell_16_40_2
  | exact S 16 40 3 cell_16_40_3
  | exact S 16 40 4 cell_16_40_4
  | exact S 16 40 5 cell_16_40_5
theorem cell_16_41_0 : C 16 41 0 := by decide +kernel
theorem cell_16_41_1 : C 16 41 1 := by decide +kernel
theorem cell_16_41_2 : C 16 41 2 := by decide +kernel
theorem cell_16_41_3 : C 16 41 3 := by decide +kernel
theorem cell_16_41_4 : C 16 41 4 := by decide +kernel
theorem cell_16_41_5 : C 16 41 5 := by decide +kernel
theorem row_16_41 : ThresholdAt 16 41 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 41 0 cell_16_41_0
  | exact S 16 41 1 cell_16_41_1
  | exact S 16 41 2 cell_16_41_2
  | exact S 16 41 3 cell_16_41_3
  | exact S 16 41 4 cell_16_41_4
  | exact S 16 41 5 cell_16_41_5
theorem cell_16_42_0 : C 16 42 0 := by decide +kernel
theorem cell_16_42_1 : C 16 42 1 := by decide +kernel
theorem cell_16_42_2 : C 16 42 2 := by decide +kernel
theorem cell_16_42_3 : C 16 42 3 := by decide +kernel
theorem cell_16_42_4 : C 16 42 4 := by decide +kernel
theorem cell_16_42_5 : C 16 42 5 := by decide +kernel
theorem row_16_42 : ThresholdAt 16 42 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 42 0 cell_16_42_0
  | exact S 16 42 1 cell_16_42_1
  | exact S 16 42 2 cell_16_42_2
  | exact S 16 42 3 cell_16_42_3
  | exact S 16 42 4 cell_16_42_4
  | exact S 16 42 5 cell_16_42_5
theorem cell_16_43_0 : C 16 43 0 := by decide +kernel
theorem cell_16_43_1 : C 16 43 1 := by decide +kernel
theorem cell_16_43_2 : C 16 43 2 := by decide +kernel
theorem cell_16_43_3 : C 16 43 3 := by decide +kernel
theorem cell_16_43_4 : C 16 43 4 := by decide +kernel
theorem cell_16_43_5 : C 16 43 5 := by decide +kernel
theorem row_16_43 : ThresholdAt 16 43 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 43 0 cell_16_43_0
  | exact S 16 43 1 cell_16_43_1
  | exact S 16 43 2 cell_16_43_2
  | exact S 16 43 3 cell_16_43_3
  | exact S 16 43 4 cell_16_43_4
  | exact S 16 43 5 cell_16_43_5
theorem cell_16_44_0 : C 16 44 0 := by decide +kernel
theorem cell_16_44_1 : C 16 44 1 := by decide +kernel
theorem cell_16_44_2 : C 16 44 2 := by decide +kernel
theorem cell_16_44_3 : C 16 44 3 := by decide +kernel
theorem cell_16_44_4 : C 16 44 4 := by decide +kernel
theorem cell_16_44_5 : C 16 44 5 := by decide +kernel
theorem row_16_44 : ThresholdAt 16 44 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 44 0 cell_16_44_0
  | exact S 16 44 1 cell_16_44_1
  | exact S 16 44 2 cell_16_44_2
  | exact S 16 44 3 cell_16_44_3
  | exact S 16 44 4 cell_16_44_4
  | exact S 16 44 5 cell_16_44_5
theorem cell_16_45_0 : C 16 45 0 := by decide +kernel
theorem cell_16_45_1 : C 16 45 1 := by decide +kernel
theorem cell_16_45_2 : C 16 45 2 := by decide +kernel
theorem cell_16_45_3 : C 16 45 3 := by decide +kernel
theorem cell_16_45_4 : C 16 45 4 := by decide +kernel
theorem cell_16_45_5 : C 16 45 5 := by decide +kernel
theorem row_16_45 : ThresholdAt 16 45 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 45 0 cell_16_45_0
  | exact S 16 45 1 cell_16_45_1
  | exact S 16 45 2 cell_16_45_2
  | exact S 16 45 3 cell_16_45_3
  | exact S 16 45 4 cell_16_45_4
  | exact S 16 45 5 cell_16_45_5
theorem cell_16_46_0 : C 16 46 0 := by decide +kernel
theorem cell_16_46_1 : C 16 46 1 := by decide +kernel
theorem cell_16_46_2 : C 16 46 2 := by decide +kernel
theorem cell_16_46_3 : C 16 46 3 := by decide +kernel
theorem cell_16_46_4 : C 16 46 4 := by decide +kernel
theorem cell_16_46_5 : C 16 46 5 := by decide +kernel
theorem row_16_46 : ThresholdAt 16 46 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 46 0 cell_16_46_0
  | exact S 16 46 1 cell_16_46_1
  | exact S 16 46 2 cell_16_46_2
  | exact S 16 46 3 cell_16_46_3
  | exact S 16 46 4 cell_16_46_4
  | exact S 16 46 5 cell_16_46_5
theorem cell_16_47_0 : C 16 47 0 := by decide +kernel
theorem cell_16_47_1 : C 16 47 1 := by decide +kernel
theorem cell_16_47_2 : C 16 47 2 := by decide +kernel
theorem cell_16_47_3 : C 16 47 3 := by decide +kernel
theorem cell_16_47_4 : C 16 47 4 := by decide +kernel
theorem cell_16_47_5 : C 16 47 5 := by decide +kernel
theorem row_16_47 : ThresholdAt 16 47 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 47 0 cell_16_47_0
  | exact S 16 47 1 cell_16_47_1
  | exact S 16 47 2 cell_16_47_2
  | exact S 16 47 3 cell_16_47_3
  | exact S 16 47 4 cell_16_47_4
  | exact S 16 47 5 cell_16_47_5
theorem cell_16_48_0 : C 16 48 0 := by decide +kernel
theorem cell_16_48_1 : C 16 48 1 := by decide +kernel
theorem cell_16_48_2 : C 16 48 2 := by decide +kernel
theorem cell_16_48_3 : C 16 48 3 := by decide +kernel
theorem cell_16_48_4 : C 16 48 4 := by decide +kernel
theorem cell_16_48_5 : C 16 48 5 := by decide +kernel
theorem row_16_48 : ThresholdAt 16 48 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 48 0 cell_16_48_0
  | exact S 16 48 1 cell_16_48_1
  | exact S 16 48 2 cell_16_48_2
  | exact S 16 48 3 cell_16_48_3
  | exact S 16 48 4 cell_16_48_4
  | exact S 16 48 5 cell_16_48_5
theorem cell_16_49_0 : C 16 49 0 := by decide +kernel
theorem cell_16_49_1 : C 16 49 1 := by decide +kernel
theorem cell_16_49_2 : C 16 49 2 := by decide +kernel
theorem cell_16_49_3 : C 16 49 3 := by decide +kernel
theorem cell_16_49_4 : C 16 49 4 := by decide +kernel
theorem cell_16_49_5 : C 16 49 5 := by decide +kernel
theorem row_16_49 : ThresholdAt 16 49 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 49 0 cell_16_49_0
  | exact S 16 49 1 cell_16_49_1
  | exact S 16 49 2 cell_16_49_2
  | exact S 16 49 3 cell_16_49_3
  | exact S 16 49 4 cell_16_49_4
  | exact S 16 49 5 cell_16_49_5
theorem cell_16_50_0 : C 16 50 0 := by decide +kernel
theorem cell_16_50_1 : C 16 50 1 := by decide +kernel
theorem cell_16_50_2 : C 16 50 2 := by decide +kernel
theorem cell_16_50_3 : C 16 50 3 := by decide +kernel
theorem cell_16_50_4 : C 16 50 4 := by decide +kernel
theorem cell_16_50_5 : C 16 50 5 := by decide +kernel
theorem row_16_50 : ThresholdAt 16 50 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 50 0 cell_16_50_0
  | exact S 16 50 1 cell_16_50_1
  | exact S 16 50 2 cell_16_50_2
  | exact S 16 50 3 cell_16_50_3
  | exact S 16 50 4 cell_16_50_4
  | exact S 16 50 5 cell_16_50_5
theorem cell_16_51_0 : C 16 51 0 := by decide +kernel
theorem cell_16_51_1 : C 16 51 1 := by decide +kernel
theorem cell_16_51_2 : C 16 51 2 := by decide +kernel
theorem cell_16_51_3 : C 16 51 3 := by decide +kernel
theorem cell_16_51_4 : C 16 51 4 := by decide +kernel
theorem cell_16_51_5 : C 16 51 5 := by decide +kernel
theorem row_16_51 : ThresholdAt 16 51 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 51 0 cell_16_51_0
  | exact S 16 51 1 cell_16_51_1
  | exact S 16 51 2 cell_16_51_2
  | exact S 16 51 3 cell_16_51_3
  | exact S 16 51 4 cell_16_51_4
  | exact S 16 51 5 cell_16_51_5
theorem cell_16_52_0 : C 16 52 0 := by decide +kernel
theorem cell_16_52_1 : C 16 52 1 := by decide +kernel
theorem cell_16_52_2 : C 16 52 2 := by decide +kernel
theorem cell_16_52_3 : C 16 52 3 := by decide +kernel
theorem cell_16_52_4 : C 16 52 4 := by decide +kernel
theorem cell_16_52_5 : C 16 52 5 := by decide +kernel
theorem row_16_52 : ThresholdAt 16 52 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 52 0 cell_16_52_0
  | exact S 16 52 1 cell_16_52_1
  | exact S 16 52 2 cell_16_52_2
  | exact S 16 52 3 cell_16_52_3
  | exact S 16 52 4 cell_16_52_4
  | exact S 16 52 5 cell_16_52_5
theorem cell_16_53_0 : C 16 53 0 := by decide +kernel
theorem cell_16_53_1 : C 16 53 1 := by decide +kernel
theorem cell_16_53_2 : C 16 53 2 := by decide +kernel
theorem cell_16_53_3 : C 16 53 3 := by decide +kernel
theorem cell_16_53_4 : C 16 53 4 := by decide +kernel
theorem cell_16_53_5 : C 16 53 5 := by decide +kernel
theorem row_16_53 : ThresholdAt 16 53 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 53 0 cell_16_53_0
  | exact S 16 53 1 cell_16_53_1
  | exact S 16 53 2 cell_16_53_2
  | exact S 16 53 3 cell_16_53_3
  | exact S 16 53 4 cell_16_53_4
  | exact S 16 53 5 cell_16_53_5
theorem cell_16_54_0 : C 16 54 0 := by decide +kernel
theorem cell_16_54_1 : C 16 54 1 := by decide +kernel
theorem cell_16_54_2 : C 16 54 2 := by decide +kernel
theorem cell_16_54_3 : C 16 54 3 := by decide +kernel
theorem cell_16_54_4 : C 16 54 4 := by decide +kernel
theorem cell_16_54_5 : C 16 54 5 := by decide +kernel
theorem row_16_54 : ThresholdAt 16 54 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 54 0 cell_16_54_0
  | exact S 16 54 1 cell_16_54_1
  | exact S 16 54 2 cell_16_54_2
  | exact S 16 54 3 cell_16_54_3
  | exact S 16 54 4 cell_16_54_4
  | exact S 16 54 5 cell_16_54_5
theorem cell_16_55_0 : C 16 55 0 := by decide +kernel
theorem cell_16_55_1 : C 16 55 1 := by decide +kernel
theorem cell_16_55_2 : C 16 55 2 := by decide +kernel
theorem cell_16_55_3 : C 16 55 3 := by decide +kernel
theorem cell_16_55_4 : C 16 55 4 := by decide +kernel
theorem cell_16_55_5 : C 16 55 5 := by decide +kernel
theorem row_16_55 : ThresholdAt 16 55 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 55 0 cell_16_55_0
  | exact S 16 55 1 cell_16_55_1
  | exact S 16 55 2 cell_16_55_2
  | exact S 16 55 3 cell_16_55_3
  | exact S 16 55 4 cell_16_55_4
  | exact S 16 55 5 cell_16_55_5
theorem cell_16_56_0 : C 16 56 0 := by decide +kernel
theorem cell_16_56_1 : C 16 56 1 := by decide +kernel
theorem cell_16_56_2 : C 16 56 2 := by decide +kernel
theorem cell_16_56_3 : C 16 56 3 := by decide +kernel
theorem cell_16_56_4 : C 16 56 4 := by decide +kernel
theorem cell_16_56_5 : C 16 56 5 := by decide +kernel
theorem row_16_56 : ThresholdAt 16 56 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 56 0 cell_16_56_0
  | exact S 16 56 1 cell_16_56_1
  | exact S 16 56 2 cell_16_56_2
  | exact S 16 56 3 cell_16_56_3
  | exact S 16 56 4 cell_16_56_4
  | exact S 16 56 5 cell_16_56_5
theorem cell_16_57_0 : C 16 57 0 := by decide +kernel
theorem cell_16_57_1 : C 16 57 1 := by decide +kernel
theorem cell_16_57_2 : C 16 57 2 := by decide +kernel
theorem cell_16_57_3 : C 16 57 3 := by decide +kernel
theorem cell_16_57_4 : C 16 57 4 := by decide +kernel
theorem cell_16_57_5 : C 16 57 5 := by decide +kernel
theorem row_16_57 : ThresholdAt 16 57 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 57 0 cell_16_57_0
  | exact S 16 57 1 cell_16_57_1
  | exact S 16 57 2 cell_16_57_2
  | exact S 16 57 3 cell_16_57_3
  | exact S 16 57 4 cell_16_57_4
  | exact S 16 57 5 cell_16_57_5
theorem cell_16_58_0 : C 16 58 0 := by decide +kernel
theorem cell_16_58_1 : C 16 58 1 := by decide +kernel
theorem cell_16_58_2 : C 16 58 2 := by decide +kernel
theorem cell_16_58_3 : C 16 58 3 := by decide +kernel
theorem cell_16_58_4 : C 16 58 4 := by decide +kernel
theorem cell_16_58_5 : C 16 58 5 := by decide +kernel
theorem row_16_58 : ThresholdAt 16 58 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 58 0 cell_16_58_0
  | exact S 16 58 1 cell_16_58_1
  | exact S 16 58 2 cell_16_58_2
  | exact S 16 58 3 cell_16_58_3
  | exact S 16 58 4 cell_16_58_4
  | exact S 16 58 5 cell_16_58_5
theorem cell_16_59_0 : C 16 59 0 := by decide +kernel
theorem cell_16_59_1 : C 16 59 1 := by decide +kernel
theorem cell_16_59_2 : C 16 59 2 := by decide +kernel
theorem cell_16_59_3 : C 16 59 3 := by decide +kernel
theorem cell_16_59_4 : C 16 59 4 := by decide +kernel
theorem cell_16_59_5 : C 16 59 5 := by decide +kernel
theorem row_16_59 : ThresholdAt 16 59 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 59 0 cell_16_59_0
  | exact S 16 59 1 cell_16_59_1
  | exact S 16 59 2 cell_16_59_2
  | exact S 16 59 3 cell_16_59_3
  | exact S 16 59 4 cell_16_59_4
  | exact S 16 59 5 cell_16_59_5
theorem cell_16_60_0 : C 16 60 0 := by decide +kernel
theorem cell_16_60_1 : C 16 60 1 := by decide +kernel
theorem cell_16_60_2 : C 16 60 2 := by decide +kernel
theorem cell_16_60_3 : C 16 60 3 := by decide +kernel
theorem cell_16_60_4 : C 16 60 4 := by decide +kernel
theorem cell_16_60_5 : C 16 60 5 := by decide +kernel
theorem row_16_60 : ThresholdAt 16 60 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 60 0 cell_16_60_0
  | exact S 16 60 1 cell_16_60_1
  | exact S 16 60 2 cell_16_60_2
  | exact S 16 60 3 cell_16_60_3
  | exact S 16 60 4 cell_16_60_4
  | exact S 16 60 5 cell_16_60_5
theorem cell_16_61_0 : C 16 61 0 := by decide +kernel
theorem cell_16_61_1 : C 16 61 1 := by decide +kernel
theorem cell_16_61_2 : C 16 61 2 := by decide +kernel
theorem cell_16_61_3 : C 16 61 3 := by decide +kernel
theorem cell_16_61_4 : C 16 61 4 := by decide +kernel
theorem cell_16_61_5 : C 16 61 5 := by decide +kernel
theorem row_16_61 : ThresholdAt 16 61 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 61 0 cell_16_61_0
  | exact S 16 61 1 cell_16_61_1
  | exact S 16 61 2 cell_16_61_2
  | exact S 16 61 3 cell_16_61_3
  | exact S 16 61 4 cell_16_61_4
  | exact S 16 61 5 cell_16_61_5
theorem cell_16_62_0 : C 16 62 0 := by decide +kernel
theorem cell_16_62_1 : C 16 62 1 := by decide +kernel
theorem cell_16_62_2 : C 16 62 2 := by decide +kernel
theorem cell_16_62_3 : C 16 62 3 := by decide +kernel
theorem cell_16_62_4 : C 16 62 4 := by decide +kernel
theorem cell_16_62_5 : C 16 62 5 := by decide +kernel
theorem row_16_62 : ThresholdAt 16 62 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 62 0 cell_16_62_0
  | exact S 16 62 1 cell_16_62_1
  | exact S 16 62 2 cell_16_62_2
  | exact S 16 62 3 cell_16_62_3
  | exact S 16 62 4 cell_16_62_4
  | exact S 16 62 5 cell_16_62_5
theorem cell_16_63_0 : C 16 63 0 := by decide +kernel
theorem cell_16_63_1 : C 16 63 1 := by decide +kernel
theorem cell_16_63_2 : C 16 63 2 := by decide +kernel
theorem cell_16_63_3 : C 16 63 3 := by decide +kernel
theorem cell_16_63_4 : C 16 63 4 := by decide +kernel
theorem cell_16_63_5 : C 16 63 5 := by decide +kernel
theorem row_16_63 : ThresholdAt 16 63 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 63 0 cell_16_63_0
  | exact S 16 63 1 cell_16_63_1
  | exact S 16 63 2 cell_16_63_2
  | exact S 16 63 3 cell_16_63_3
  | exact S 16 63 4 cell_16_63_4
  | exact S 16 63 5 cell_16_63_5
theorem cell_16_64_0 : C 16 64 0 := by decide +kernel
theorem cell_16_64_1 : C 16 64 1 := by decide +kernel
theorem cell_16_64_2 : C 16 64 2 := by decide +kernel
theorem cell_16_64_3 : C 16 64 3 := by decide +kernel
theorem cell_16_64_4 : C 16 64 4 := by decide +kernel
theorem cell_16_64_5 : C 16 64 5 := by decide +kernel
theorem row_16_64 : ThresholdAt 16 64 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 64 0 cell_16_64_0
  | exact S 16 64 1 cell_16_64_1
  | exact S 16 64 2 cell_16_64_2
  | exact S 16 64 3 cell_16_64_3
  | exact S 16 64 4 cell_16_64_4
  | exact S 16 64 5 cell_16_64_5
theorem cell_16_65_0 : C 16 65 0 := by decide +kernel
theorem cell_16_65_1 : C 16 65 1 := by decide +kernel
theorem cell_16_65_2 : C 16 65 2 := by decide +kernel
theorem cell_16_65_3 : C 16 65 3 := by decide +kernel
theorem cell_16_65_4 : C 16 65 4 := by decide +kernel
theorem cell_16_65_5 : C 16 65 5 := by decide +kernel
theorem row_16_65 : ThresholdAt 16 65 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 65 0 cell_16_65_0
  | exact S 16 65 1 cell_16_65_1
  | exact S 16 65 2 cell_16_65_2
  | exact S 16 65 3 cell_16_65_3
  | exact S 16 65 4 cell_16_65_4
  | exact S 16 65 5 cell_16_65_5
theorem cell_16_66_0 : C 16 66 0 := by decide +kernel
theorem cell_16_66_1 : C 16 66 1 := by decide +kernel
theorem cell_16_66_2 : C 16 66 2 := by decide +kernel
theorem cell_16_66_3 : C 16 66 3 := by decide +kernel
theorem cell_16_66_4 : C 16 66 4 := by decide +kernel
theorem cell_16_66_5 : C 16 66 5 := by decide +kernel
theorem row_16_66 : ThresholdAt 16 66 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 66 0 cell_16_66_0
  | exact S 16 66 1 cell_16_66_1
  | exact S 16 66 2 cell_16_66_2
  | exact S 16 66 3 cell_16_66_3
  | exact S 16 66 4 cell_16_66_4
  | exact S 16 66 5 cell_16_66_5
theorem cell_16_67_0 : C 16 67 0 := by decide +kernel
theorem cell_16_67_1 : C 16 67 1 := by decide +kernel
theorem cell_16_67_2 : C 16 67 2 := by decide +kernel
theorem cell_16_67_3 : C 16 67 3 := by decide +kernel
theorem cell_16_67_4 : C 16 67 4 := by decide +kernel
theorem cell_16_67_5 : C 16 67 5 := by decide +kernel
theorem row_16_67 : ThresholdAt 16 67 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 67 0 cell_16_67_0
  | exact S 16 67 1 cell_16_67_1
  | exact S 16 67 2 cell_16_67_2
  | exact S 16 67 3 cell_16_67_3
  | exact S 16 67 4 cell_16_67_4
  | exact S 16 67 5 cell_16_67_5
theorem cell_16_68_0 : C 16 68 0 := by decide +kernel
theorem cell_16_68_1 : C 16 68 1 := by decide +kernel
theorem cell_16_68_2 : C 16 68 2 := by decide +kernel
theorem cell_16_68_3 : C 16 68 3 := by decide +kernel
theorem cell_16_68_4 : C 16 68 4 := by decide +kernel
theorem cell_16_68_5 : C 16 68 5 := by decide +kernel
theorem row_16_68 : ThresholdAt 16 68 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 68 0 cell_16_68_0
  | exact S 16 68 1 cell_16_68_1
  | exact S 16 68 2 cell_16_68_2
  | exact S 16 68 3 cell_16_68_3
  | exact S 16 68 4 cell_16_68_4
  | exact S 16 68 5 cell_16_68_5
theorem cell_16_69_0 : C 16 69 0 := by decide +kernel
theorem cell_16_69_1 : C 16 69 1 := by decide +kernel
theorem cell_16_69_2 : C 16 69 2 := by decide +kernel
theorem cell_16_69_3 : C 16 69 3 := by decide +kernel
theorem cell_16_69_4 : C 16 69 4 := by decide +kernel
theorem cell_16_69_5 : C 16 69 5 := by decide +kernel
theorem row_16_69 : ThresholdAt 16 69 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 69 0 cell_16_69_0
  | exact S 16 69 1 cell_16_69_1
  | exact S 16 69 2 cell_16_69_2
  | exact S 16 69 3 cell_16_69_3
  | exact S 16 69 4 cell_16_69_4
  | exact S 16 69 5 cell_16_69_5
theorem cell_16_70_0 : C 16 70 0 := by decide +kernel
theorem cell_16_70_1 : C 16 70 1 := by decide +kernel
theorem cell_16_70_2 : C 16 70 2 := by decide +kernel
theorem cell_16_70_3 : C 16 70 3 := by decide +kernel
theorem cell_16_70_4 : C 16 70 4 := by decide +kernel
theorem cell_16_70_5 : C 16 70 5 := by decide +kernel
theorem row_16_70 : ThresholdAt 16 70 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 70 0 cell_16_70_0
  | exact S 16 70 1 cell_16_70_1
  | exact S 16 70 2 cell_16_70_2
  | exact S 16 70 3 cell_16_70_3
  | exact S 16 70 4 cell_16_70_4
  | exact S 16 70 5 cell_16_70_5
theorem cell_16_71_0 : C 16 71 0 := by decide +kernel
theorem cell_16_71_1 : C 16 71 1 := by decide +kernel
theorem cell_16_71_2 : C 16 71 2 := by decide +kernel
theorem cell_16_71_3 : C 16 71 3 := by decide +kernel
theorem cell_16_71_4 : C 16 71 4 := by decide +kernel
theorem cell_16_71_5 : C 16 71 5 := by decide +kernel
theorem row_16_71 : ThresholdAt 16 71 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 71 0 cell_16_71_0
  | exact S 16 71 1 cell_16_71_1
  | exact S 16 71 2 cell_16_71_2
  | exact S 16 71 3 cell_16_71_3
  | exact S 16 71 4 cell_16_71_4
  | exact S 16 71 5 cell_16_71_5
theorem cell_16_72_0 : C 16 72 0 := by decide +kernel
theorem cell_16_72_1 : C 16 72 1 := by decide +kernel
theorem cell_16_72_2 : C 16 72 2 := by decide +kernel
theorem cell_16_72_3 : C 16 72 3 := by decide +kernel
theorem cell_16_72_4 : C 16 72 4 := by decide +kernel
theorem cell_16_72_5 : C 16 72 5 := by decide +kernel
theorem row_16_72 : ThresholdAt 16 72 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 72 0 cell_16_72_0
  | exact S 16 72 1 cell_16_72_1
  | exact S 16 72 2 cell_16_72_2
  | exact S 16 72 3 cell_16_72_3
  | exact S 16 72 4 cell_16_72_4
  | exact S 16 72 5 cell_16_72_5
theorem cell_16_73_0 : C 16 73 0 := by decide +kernel
theorem cell_16_73_1 : C 16 73 1 := by decide +kernel
theorem cell_16_73_2 : C 16 73 2 := by decide +kernel
theorem cell_16_73_3 : C 16 73 3 := by decide +kernel
theorem cell_16_73_4 : C 16 73 4 := by decide +kernel
theorem cell_16_73_5 : C 16 73 5 := by decide +kernel
theorem row_16_73 : ThresholdAt 16 73 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 73 0 cell_16_73_0
  | exact S 16 73 1 cell_16_73_1
  | exact S 16 73 2 cell_16_73_2
  | exact S 16 73 3 cell_16_73_3
  | exact S 16 73 4 cell_16_73_4
  | exact S 16 73 5 cell_16_73_5
theorem cell_16_74_0 : C 16 74 0 := by decide +kernel
theorem cell_16_74_1 : C 16 74 1 := by decide +kernel
theorem cell_16_74_2 : C 16 74 2 := by decide +kernel
theorem cell_16_74_3 : C 16 74 3 := by decide +kernel
theorem cell_16_74_4 : C 16 74 4 := by decide +kernel
theorem cell_16_74_5 : C 16 74 5 := by decide +kernel
theorem row_16_74 : ThresholdAt 16 74 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 74 0 cell_16_74_0
  | exact S 16 74 1 cell_16_74_1
  | exact S 16 74 2 cell_16_74_2
  | exact S 16 74 3 cell_16_74_3
  | exact S 16 74 4 cell_16_74_4
  | exact S 16 74 5 cell_16_74_5
theorem cell_16_75_0 : C 16 75 0 := by decide +kernel
theorem cell_16_75_1 : C 16 75 1 := by decide +kernel
theorem cell_16_75_2 : C 16 75 2 := by decide +kernel
theorem cell_16_75_3 : C 16 75 3 := by decide +kernel
theorem cell_16_75_4 : C 16 75 4 := by decide +kernel
theorem cell_16_75_5 : C 16 75 5 := by decide +kernel
theorem row_16_75 : ThresholdAt 16 75 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 75 0 cell_16_75_0
  | exact S 16 75 1 cell_16_75_1
  | exact S 16 75 2 cell_16_75_2
  | exact S 16 75 3 cell_16_75_3
  | exact S 16 75 4 cell_16_75_4
  | exact S 16 75 5 cell_16_75_5
theorem cell_16_76_0 : C 16 76 0 := by decide +kernel
theorem cell_16_76_1 : C 16 76 1 := by decide +kernel
theorem cell_16_76_2 : C 16 76 2 := by decide +kernel
theorem cell_16_76_3 : C 16 76 3 := by decide +kernel
theorem cell_16_76_4 : C 16 76 4 := by decide +kernel
theorem cell_16_76_5 : C 16 76 5 := by decide +kernel
theorem row_16_76 : ThresholdAt 16 76 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 76 0 cell_16_76_0
  | exact S 16 76 1 cell_16_76_1
  | exact S 16 76 2 cell_16_76_2
  | exact S 16 76 3 cell_16_76_3
  | exact S 16 76 4 cell_16_76_4
  | exact S 16 76 5 cell_16_76_5
theorem cell_16_77_0 : C 16 77 0 := by decide +kernel
theorem cell_16_77_1 : C 16 77 1 := by decide +kernel
theorem cell_16_77_2 : C 16 77 2 := by decide +kernel
theorem cell_16_77_3 : C 16 77 3 := by decide +kernel
theorem cell_16_77_4 : C 16 77 4 := by decide +kernel
theorem cell_16_77_5 : C 16 77 5 := by decide +kernel
theorem row_16_77 : ThresholdAt 16 77 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 77 0 cell_16_77_0
  | exact S 16 77 1 cell_16_77_1
  | exact S 16 77 2 cell_16_77_2
  | exact S 16 77 3 cell_16_77_3
  | exact S 16 77 4 cell_16_77_4
  | exact S 16 77 5 cell_16_77_5
theorem cell_16_78_0 : C 16 78 0 := by decide +kernel
theorem cell_16_78_1 : C 16 78 1 := by decide +kernel
theorem cell_16_78_2 : C 16 78 2 := by decide +kernel
theorem cell_16_78_3 : C 16 78 3 := by decide +kernel
theorem cell_16_78_4 : C 16 78 4 := by decide +kernel
theorem cell_16_78_5 : C 16 78 5 := by decide +kernel
theorem row_16_78 : ThresholdAt 16 78 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 78 0 cell_16_78_0
  | exact S 16 78 1 cell_16_78_1
  | exact S 16 78 2 cell_16_78_2
  | exact S 16 78 3 cell_16_78_3
  | exact S 16 78 4 cell_16_78_4
  | exact S 16 78 5 cell_16_78_5
theorem cell_16_79_0 : C 16 79 0 := by decide +kernel
theorem cell_16_79_1 : C 16 79 1 := by decide +kernel
theorem cell_16_79_2 : C 16 79 2 := by decide +kernel
theorem cell_16_79_3 : C 16 79 3 := by decide +kernel
theorem cell_16_79_4 : C 16 79 4 := by decide +kernel
theorem cell_16_79_5 : C 16 79 5 := by decide +kernel
theorem row_16_79 : ThresholdAt 16 79 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 79 0 cell_16_79_0
  | exact S 16 79 1 cell_16_79_1
  | exact S 16 79 2 cell_16_79_2
  | exact S 16 79 3 cell_16_79_3
  | exact S 16 79 4 cell_16_79_4
  | exact S 16 79 5 cell_16_79_5
theorem cell_16_80_0 : C 16 80 0 := by decide +kernel
theorem cell_16_80_1 : C 16 80 1 := by decide +kernel
theorem cell_16_80_2 : C 16 80 2 := by decide +kernel
theorem cell_16_80_3 : C 16 80 3 := by decide +kernel
theorem cell_16_80_4 : C 16 80 4 := by decide +kernel
theorem cell_16_80_5 : C 16 80 5 := by decide +kernel
theorem row_16_80 : ThresholdAt 16 80 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 80 0 cell_16_80_0
  | exact S 16 80 1 cell_16_80_1
  | exact S 16 80 2 cell_16_80_2
  | exact S 16 80 3 cell_16_80_3
  | exact S 16 80 4 cell_16_80_4
  | exact S 16 80 5 cell_16_80_5
theorem cell_16_81_0 : C 16 81 0 := by decide +kernel
theorem cell_16_81_1 : C 16 81 1 := by decide +kernel
theorem cell_16_81_2 : C 16 81 2 := by decide +kernel
theorem cell_16_81_3 : C 16 81 3 := by decide +kernel
theorem cell_16_81_4 : C 16 81 4 := by decide +kernel
theorem cell_16_81_5 : C 16 81 5 := by decide +kernel
theorem row_16_81 : ThresholdAt 16 81 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 81 0 cell_16_81_0
  | exact S 16 81 1 cell_16_81_1
  | exact S 16 81 2 cell_16_81_2
  | exact S 16 81 3 cell_16_81_3
  | exact S 16 81 4 cell_16_81_4
  | exact S 16 81 5 cell_16_81_5
theorem cell_16_82_0 : C 16 82 0 := by decide +kernel
theorem cell_16_82_1 : C 16 82 1 := by decide +kernel
theorem cell_16_82_2 : C 16 82 2 := by decide +kernel
theorem cell_16_82_3 : C 16 82 3 := by decide +kernel
theorem cell_16_82_4 : C 16 82 4 := by decide +kernel
theorem cell_16_82_5 : C 16 82 5 := by decide +kernel
theorem row_16_82 : ThresholdAt 16 82 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 82 0 cell_16_82_0
  | exact S 16 82 1 cell_16_82_1
  | exact S 16 82 2 cell_16_82_2
  | exact S 16 82 3 cell_16_82_3
  | exact S 16 82 4 cell_16_82_4
  | exact S 16 82 5 cell_16_82_5
theorem cell_16_83_0 : C 16 83 0 := by decide +kernel
theorem cell_16_83_1 : C 16 83 1 := by decide +kernel
theorem cell_16_83_2 : C 16 83 2 := by decide +kernel
theorem cell_16_83_3 : C 16 83 3 := by decide +kernel
theorem cell_16_83_4 : C 16 83 4 := by decide +kernel
theorem cell_16_83_5 : C 16 83 5 := by decide +kernel
theorem row_16_83 : ThresholdAt 16 83 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 83 0 cell_16_83_0
  | exact S 16 83 1 cell_16_83_1
  | exact S 16 83 2 cell_16_83_2
  | exact S 16 83 3 cell_16_83_3
  | exact S 16 83 4 cell_16_83_4
  | exact S 16 83 5 cell_16_83_5
theorem cell_16_84_0 : C 16 84 0 := by decide +kernel
theorem cell_16_84_1 : C 16 84 1 := by decide +kernel
theorem cell_16_84_2 : C 16 84 2 := by decide +kernel
theorem cell_16_84_3 : C 16 84 3 := by decide +kernel
theorem cell_16_84_4 : C 16 84 4 := by decide +kernel
theorem cell_16_84_5 : C 16 84 5 := by decide +kernel
theorem row_16_84 : ThresholdAt 16 84 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 84 0 cell_16_84_0
  | exact S 16 84 1 cell_16_84_1
  | exact S 16 84 2 cell_16_84_2
  | exact S 16 84 3 cell_16_84_3
  | exact S 16 84 4 cell_16_84_4
  | exact S 16 84 5 cell_16_84_5
theorem cell_16_85_0 : C 16 85 0 := by decide +kernel
theorem cell_16_85_1 : C 16 85 1 := by decide +kernel
theorem cell_16_85_2 : C 16 85 2 := by decide +kernel
theorem cell_16_85_3 : C 16 85 3 := by decide +kernel
theorem cell_16_85_4 : C 16 85 4 := by decide +kernel
theorem cell_16_85_5 : C 16 85 5 := by decide +kernel
theorem row_16_85 : ThresholdAt 16 85 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 85 0 cell_16_85_0
  | exact S 16 85 1 cell_16_85_1
  | exact S 16 85 2 cell_16_85_2
  | exact S 16 85 3 cell_16_85_3
  | exact S 16 85 4 cell_16_85_4
  | exact S 16 85 5 cell_16_85_5
theorem cell_16_86_0 : C 16 86 0 := by decide +kernel
theorem cell_16_86_1 : C 16 86 1 := by decide +kernel
theorem cell_16_86_2 : C 16 86 2 := by decide +kernel
theorem cell_16_86_3 : C 16 86 3 := by decide +kernel
theorem cell_16_86_4 : C 16 86 4 := by decide +kernel
theorem cell_16_86_5 : C 16 86 5 := by decide +kernel
theorem row_16_86 : ThresholdAt 16 86 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 86 0 cell_16_86_0
  | exact S 16 86 1 cell_16_86_1
  | exact S 16 86 2 cell_16_86_2
  | exact S 16 86 3 cell_16_86_3
  | exact S 16 86 4 cell_16_86_4
  | exact S 16 86 5 cell_16_86_5
theorem cell_16_87_0 : C 16 87 0 := by decide +kernel
theorem cell_16_87_1 : C 16 87 1 := by decide +kernel
theorem cell_16_87_2 : C 16 87 2 := by decide +kernel
theorem cell_16_87_3 : C 16 87 3 := by decide +kernel
theorem cell_16_87_4 : C 16 87 4 := by decide +kernel
theorem cell_16_87_5 : C 16 87 5 := by decide +kernel
theorem row_16_87 : ThresholdAt 16 87 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 87 0 cell_16_87_0
  | exact S 16 87 1 cell_16_87_1
  | exact S 16 87 2 cell_16_87_2
  | exact S 16 87 3 cell_16_87_3
  | exact S 16 87 4 cell_16_87_4
  | exact S 16 87 5 cell_16_87_5
theorem cell_16_88_0 : C 16 88 0 := by decide +kernel
theorem cell_16_88_1 : C 16 88 1 := by decide +kernel
theorem cell_16_88_2 : C 16 88 2 := by decide +kernel
theorem cell_16_88_3 : C 16 88 3 := by decide +kernel
theorem cell_16_88_4 : C 16 88 4 := by decide +kernel
theorem cell_16_88_5 : C 16 88 5 := by decide +kernel
theorem row_16_88 : ThresholdAt 16 88 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 88 0 cell_16_88_0
  | exact S 16 88 1 cell_16_88_1
  | exact S 16 88 2 cell_16_88_2
  | exact S 16 88 3 cell_16_88_3
  | exact S 16 88 4 cell_16_88_4
  | exact S 16 88 5 cell_16_88_5
theorem cell_16_89_0 : C 16 89 0 := by decide +kernel
theorem cell_16_89_1 : C 16 89 1 := by decide +kernel
theorem cell_16_89_2 : C 16 89 2 := by decide +kernel
theorem cell_16_89_3 : C 16 89 3 := by decide +kernel
theorem cell_16_89_4 : C 16 89 4 := by decide +kernel
theorem cell_16_89_5 : C 16 89 5 := by decide +kernel
theorem row_16_89 : ThresholdAt 16 89 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 89 0 cell_16_89_0
  | exact S 16 89 1 cell_16_89_1
  | exact S 16 89 2 cell_16_89_2
  | exact S 16 89 3 cell_16_89_3
  | exact S 16 89 4 cell_16_89_4
  | exact S 16 89 5 cell_16_89_5
theorem cell_16_90_0 : C 16 90 0 := by decide +kernel
theorem cell_16_90_1 : C 16 90 1 := by decide +kernel
theorem cell_16_90_2 : C 16 90 2 := by decide +kernel
theorem cell_16_90_3 : C 16 90 3 := by decide +kernel
theorem cell_16_90_4 : C 16 90 4 := by decide +kernel
theorem cell_16_90_5 : C 16 90 5 := by decide +kernel
theorem row_16_90 : ThresholdAt 16 90 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 90 0 cell_16_90_0
  | exact S 16 90 1 cell_16_90_1
  | exact S 16 90 2 cell_16_90_2
  | exact S 16 90 3 cell_16_90_3
  | exact S 16 90 4 cell_16_90_4
  | exact S 16 90 5 cell_16_90_5
theorem cell_16_91_0 : C 16 91 0 := by decide +kernel
theorem cell_16_91_1 : C 16 91 1 := by decide +kernel
theorem cell_16_91_2 : C 16 91 2 := by decide +kernel
theorem cell_16_91_3 : C 16 91 3 := by decide +kernel
theorem cell_16_91_4 : C 16 91 4 := by decide +kernel
theorem cell_16_91_5 : C 16 91 5 := by decide +kernel
theorem row_16_91 : ThresholdAt 16 91 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 91 0 cell_16_91_0
  | exact S 16 91 1 cell_16_91_1
  | exact S 16 91 2 cell_16_91_2
  | exact S 16 91 3 cell_16_91_3
  | exact S 16 91 4 cell_16_91_4
  | exact S 16 91 5 cell_16_91_5
theorem cell_16_92_0 : C 16 92 0 := by decide +kernel
theorem cell_16_92_1 : C 16 92 1 := by decide +kernel
theorem cell_16_92_2 : C 16 92 2 := by decide +kernel
theorem cell_16_92_3 : C 16 92 3 := by decide +kernel
theorem cell_16_92_4 : C 16 92 4 := by decide +kernel
theorem cell_16_92_5 : C 16 92 5 := by decide +kernel
theorem row_16_92 : ThresholdAt 16 92 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 92 0 cell_16_92_0
  | exact S 16 92 1 cell_16_92_1
  | exact S 16 92 2 cell_16_92_2
  | exact S 16 92 3 cell_16_92_3
  | exact S 16 92 4 cell_16_92_4
  | exact S 16 92 5 cell_16_92_5
theorem cell_16_93_0 : C 16 93 0 := by decide +kernel
theorem cell_16_93_1 : C 16 93 1 := by decide +kernel
theorem cell_16_93_2 : C 16 93 2 := by decide +kernel
theorem cell_16_93_3 : C 16 93 3 := by decide +kernel
theorem cell_16_93_4 : C 16 93 4 := by decide +kernel
theorem cell_16_93_5 : C 16 93 5 := by decide +kernel
theorem row_16_93 : ThresholdAt 16 93 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 93 0 cell_16_93_0
  | exact S 16 93 1 cell_16_93_1
  | exact S 16 93 2 cell_16_93_2
  | exact S 16 93 3 cell_16_93_3
  | exact S 16 93 4 cell_16_93_4
  | exact S 16 93 5 cell_16_93_5
theorem cell_16_94_0 : C 16 94 0 := by decide +kernel
theorem cell_16_94_1 : C 16 94 1 := by decide +kernel
theorem cell_16_94_2 : C 16 94 2 := by decide +kernel
theorem cell_16_94_3 : C 16 94 3 := by decide +kernel
theorem cell_16_94_4 : C 16 94 4 := by decide +kernel
theorem cell_16_94_5 : C 16 94 5 := by decide +kernel
theorem row_16_94 : ThresholdAt 16 94 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 94 0 cell_16_94_0
  | exact S 16 94 1 cell_16_94_1
  | exact S 16 94 2 cell_16_94_2
  | exact S 16 94 3 cell_16_94_3
  | exact S 16 94 4 cell_16_94_4
  | exact S 16 94 5 cell_16_94_5
theorem cell_16_95_0 : C 16 95 0 := by decide +kernel
theorem cell_16_95_1 : C 16 95 1 := by decide +kernel
theorem cell_16_95_2 : C 16 95 2 := by decide +kernel
theorem cell_16_95_3 : C 16 95 3 := by decide +kernel
theorem cell_16_95_4 : C 16 95 4 := by decide +kernel
theorem cell_16_95_5 : C 16 95 5 := by decide +kernel
theorem row_16_95 : ThresholdAt 16 95 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 95 0 cell_16_95_0
  | exact S 16 95 1 cell_16_95_1
  | exact S 16 95 2 cell_16_95_2
  | exact S 16 95 3 cell_16_95_3
  | exact S 16 95 4 cell_16_95_4
  | exact S 16 95 5 cell_16_95_5
theorem cell_16_96_0 : C 16 96 0 := by decide +kernel
theorem cell_16_96_1 : C 16 96 1 := by decide +kernel
theorem cell_16_96_2 : C 16 96 2 := by decide +kernel
theorem cell_16_96_3 : C 16 96 3 := by decide +kernel
theorem cell_16_96_4 : C 16 96 4 := by decide +kernel
theorem cell_16_96_5 : C 16 96 5 := by decide +kernel
theorem row_16_96 : ThresholdAt 16 96 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 96 0 cell_16_96_0
  | exact S 16 96 1 cell_16_96_1
  | exact S 16 96 2 cell_16_96_2
  | exact S 16 96 3 cell_16_96_3
  | exact S 16 96 4 cell_16_96_4
  | exact S 16 96 5 cell_16_96_5
theorem cell_16_97_0 : C 16 97 0 := by decide +kernel
theorem cell_16_97_1 : C 16 97 1 := by decide +kernel
theorem cell_16_97_2 : C 16 97 2 := by decide +kernel
theorem cell_16_97_3 : C 16 97 3 := by decide +kernel
theorem cell_16_97_4 : C 16 97 4 := by decide +kernel
theorem cell_16_97_5 : C 16 97 5 := by decide +kernel
theorem row_16_97 : ThresholdAt 16 97 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 97 0 cell_16_97_0
  | exact S 16 97 1 cell_16_97_1
  | exact S 16 97 2 cell_16_97_2
  | exact S 16 97 3 cell_16_97_3
  | exact S 16 97 4 cell_16_97_4
  | exact S 16 97 5 cell_16_97_5
theorem cell_16_98_0 : C 16 98 0 := by decide +kernel
theorem cell_16_98_1 : C 16 98 1 := by decide +kernel
theorem cell_16_98_2 : C 16 98 2 := by decide +kernel
theorem cell_16_98_3 : C 16 98 3 := by decide +kernel
theorem cell_16_98_4 : C 16 98 4 := by decide +kernel
theorem cell_16_98_5 : C 16 98 5 := by decide +kernel
theorem row_16_98 : ThresholdAt 16 98 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 98 0 cell_16_98_0
  | exact S 16 98 1 cell_16_98_1
  | exact S 16 98 2 cell_16_98_2
  | exact S 16 98 3 cell_16_98_3
  | exact S 16 98 4 cell_16_98_4
  | exact S 16 98 5 cell_16_98_5
theorem cell_16_99_0 : C 16 99 0 := by decide +kernel
theorem cell_16_99_1 : C 16 99 1 := by decide +kernel
theorem cell_16_99_2 : C 16 99 2 := by decide +kernel
theorem cell_16_99_3 : C 16 99 3 := by decide +kernel
theorem cell_16_99_4 : C 16 99 4 := by decide +kernel
theorem cell_16_99_5 : C 16 99 5 := by decide +kernel
theorem row_16_99 : ThresholdAt 16 99 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 99 0 cell_16_99_0
  | exact S 16 99 1 cell_16_99_1
  | exact S 16 99 2 cell_16_99_2
  | exact S 16 99 3 cell_16_99_3
  | exact S 16 99 4 cell_16_99_4
  | exact S 16 99 5 cell_16_99_5
theorem cell_16_100_0 : C 16 100 0 := by decide +kernel
theorem cell_16_100_1 : C 16 100 1 := by decide +kernel
theorem cell_16_100_2 : C 16 100 2 := by decide +kernel
theorem cell_16_100_3 : C 16 100 3 := by decide +kernel
theorem cell_16_100_4 : C 16 100 4 := by decide +kernel
theorem cell_16_100_5 : C 16 100 5 := by decide +kernel
theorem row_16_100 : ThresholdAt 16 100 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 100 0 cell_16_100_0
  | exact S 16 100 1 cell_16_100_1
  | exact S 16 100 2 cell_16_100_2
  | exact S 16 100 3 cell_16_100_3
  | exact S 16 100 4 cell_16_100_4
  | exact S 16 100 5 cell_16_100_5
theorem cell_16_101_0 : C 16 101 0 := by decide +kernel
theorem cell_16_101_1 : C 16 101 1 := by decide +kernel
theorem cell_16_101_2 : C 16 101 2 := by decide +kernel
theorem cell_16_101_3 : C 16 101 3 := by decide +kernel
theorem cell_16_101_4 : C 16 101 4 := by decide +kernel
theorem cell_16_101_5 : C 16 101 5 := by decide +kernel
theorem row_16_101 : ThresholdAt 16 101 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 101 0 cell_16_101_0
  | exact S 16 101 1 cell_16_101_1
  | exact S 16 101 2 cell_16_101_2
  | exact S 16 101 3 cell_16_101_3
  | exact S 16 101 4 cell_16_101_4
  | exact S 16 101 5 cell_16_101_5
theorem cell_16_102_0 : C 16 102 0 := by decide +kernel
theorem cell_16_102_1 : C 16 102 1 := by decide +kernel
theorem cell_16_102_2 : C 16 102 2 := by decide +kernel
theorem cell_16_102_3 : C 16 102 3 := by decide +kernel
theorem cell_16_102_4 : C 16 102 4 := by decide +kernel
theorem cell_16_102_5 : C 16 102 5 := by decide +kernel
theorem row_16_102 : ThresholdAt 16 102 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 102 0 cell_16_102_0
  | exact S 16 102 1 cell_16_102_1
  | exact S 16 102 2 cell_16_102_2
  | exact S 16 102 3 cell_16_102_3
  | exact S 16 102 4 cell_16_102_4
  | exact S 16 102 5 cell_16_102_5
theorem cell_16_103_0 : C 16 103 0 := by decide +kernel
theorem cell_16_103_1 : C 16 103 1 := by decide +kernel
theorem cell_16_103_2 : C 16 103 2 := by decide +kernel
theorem cell_16_103_3 : C 16 103 3 := by decide +kernel
theorem cell_16_103_4 : C 16 103 4 := by decide +kernel
theorem cell_16_103_5 : C 16 103 5 := by decide +kernel
theorem row_16_103 : ThresholdAt 16 103 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 103 0 cell_16_103_0
  | exact S 16 103 1 cell_16_103_1
  | exact S 16 103 2 cell_16_103_2
  | exact S 16 103 3 cell_16_103_3
  | exact S 16 103 4 cell_16_103_4
  | exact S 16 103 5 cell_16_103_5
theorem cell_16_104_0 : C 16 104 0 := by decide +kernel
theorem cell_16_104_1 : C 16 104 1 := by decide +kernel
theorem cell_16_104_2 : C 16 104 2 := by decide +kernel
theorem cell_16_104_3 : C 16 104 3 := by decide +kernel
theorem cell_16_104_4 : C 16 104 4 := by decide +kernel
theorem cell_16_104_5 : C 16 104 5 := by decide +kernel
theorem row_16_104 : ThresholdAt 16 104 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 104 0 cell_16_104_0
  | exact S 16 104 1 cell_16_104_1
  | exact S 16 104 2 cell_16_104_2
  | exact S 16 104 3 cell_16_104_3
  | exact S 16 104 4 cell_16_104_4
  | exact S 16 104 5 cell_16_104_5
theorem cell_16_105_0 : C 16 105 0 := by decide +kernel
theorem cell_16_105_1 : C 16 105 1 := by decide +kernel
theorem cell_16_105_2 : C 16 105 2 := by decide +kernel
theorem cell_16_105_3 : C 16 105 3 := by decide +kernel
theorem cell_16_105_4 : C 16 105 4 := by decide +kernel
theorem cell_16_105_5 : C 16 105 5 := by decide +kernel
theorem row_16_105 : ThresholdAt 16 105 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 105 0 cell_16_105_0
  | exact S 16 105 1 cell_16_105_1
  | exact S 16 105 2 cell_16_105_2
  | exact S 16 105 3 cell_16_105_3
  | exact S 16 105 4 cell_16_105_4
  | exact S 16 105 5 cell_16_105_5
theorem cell_16_106_0 : C 16 106 0 := by decide +kernel
theorem cell_16_106_1 : C 16 106 1 := by decide +kernel
theorem cell_16_106_2 : C 16 106 2 := by decide +kernel
theorem cell_16_106_3 : C 16 106 3 := by decide +kernel
theorem cell_16_106_4 : C 16 106 4 := by decide +kernel
theorem cell_16_106_5 : C 16 106 5 := by decide +kernel
theorem row_16_106 : ThresholdAt 16 106 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 106 0 cell_16_106_0
  | exact S 16 106 1 cell_16_106_1
  | exact S 16 106 2 cell_16_106_2
  | exact S 16 106 3 cell_16_106_3
  | exact S 16 106 4 cell_16_106_4
  | exact S 16 106 5 cell_16_106_5
theorem cell_16_107_0 : C 16 107 0 := by decide +kernel
theorem cell_16_107_1 : C 16 107 1 := by decide +kernel
theorem cell_16_107_2 : C 16 107 2 := by decide +kernel
theorem cell_16_107_3 : C 16 107 3 := by decide +kernel
theorem cell_16_107_4 : C 16 107 4 := by decide +kernel
theorem cell_16_107_5 : C 16 107 5 := by decide +kernel
theorem row_16_107 : ThresholdAt 16 107 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 107 0 cell_16_107_0
  | exact S 16 107 1 cell_16_107_1
  | exact S 16 107 2 cell_16_107_2
  | exact S 16 107 3 cell_16_107_3
  | exact S 16 107 4 cell_16_107_4
  | exact S 16 107 5 cell_16_107_5
theorem cell_16_108_0 : C 16 108 0 := by decide +kernel
theorem cell_16_108_1 : C 16 108 1 := by decide +kernel
theorem cell_16_108_2 : C 16 108 2 := by decide +kernel
theorem cell_16_108_3 : C 16 108 3 := by decide +kernel
theorem cell_16_108_4 : C 16 108 4 := by decide +kernel
theorem cell_16_108_5 : C 16 108 5 := by decide +kernel
theorem row_16_108 : ThresholdAt 16 108 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 108 0 cell_16_108_0
  | exact S 16 108 1 cell_16_108_1
  | exact S 16 108 2 cell_16_108_2
  | exact S 16 108 3 cell_16_108_3
  | exact S 16 108 4 cell_16_108_4
  | exact S 16 108 5 cell_16_108_5
theorem cell_16_109_0 : C 16 109 0 := by decide +kernel
theorem cell_16_109_1 : C 16 109 1 := by decide +kernel
theorem cell_16_109_2 : C 16 109 2 := by decide +kernel
theorem cell_16_109_3 : C 16 109 3 := by decide +kernel
theorem cell_16_109_4 : C 16 109 4 := by decide +kernel
theorem cell_16_109_5 : C 16 109 5 := by decide +kernel
theorem row_16_109 : ThresholdAt 16 109 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 109 0 cell_16_109_0
  | exact S 16 109 1 cell_16_109_1
  | exact S 16 109 2 cell_16_109_2
  | exact S 16 109 3 cell_16_109_3
  | exact S 16 109 4 cell_16_109_4
  | exact S 16 109 5 cell_16_109_5
theorem cell_16_110_0 : C 16 110 0 := by decide +kernel
theorem cell_16_110_1 : C 16 110 1 := by decide +kernel
theorem cell_16_110_2 : C 16 110 2 := by decide +kernel
theorem cell_16_110_3 : C 16 110 3 := by decide +kernel
theorem cell_16_110_4 : C 16 110 4 := by decide +kernel
theorem cell_16_110_5 : C 16 110 5 := by decide +kernel
theorem row_16_110 : ThresholdAt 16 110 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 110 0 cell_16_110_0
  | exact S 16 110 1 cell_16_110_1
  | exact S 16 110 2 cell_16_110_2
  | exact S 16 110 3 cell_16_110_3
  | exact S 16 110 4 cell_16_110_4
  | exact S 16 110 5 cell_16_110_5
theorem cell_16_111_0 : C 16 111 0 := by decide +kernel
theorem cell_16_111_1 : C 16 111 1 := by decide +kernel
theorem cell_16_111_2 : C 16 111 2 := by decide +kernel
theorem cell_16_111_3 : C 16 111 3 := by decide +kernel
theorem cell_16_111_4 : C 16 111 4 := by decide +kernel
theorem cell_16_111_5 : C 16 111 5 := by decide +kernel
theorem row_16_111 : ThresholdAt 16 111 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 111 0 cell_16_111_0
  | exact S 16 111 1 cell_16_111_1
  | exact S 16 111 2 cell_16_111_2
  | exact S 16 111 3 cell_16_111_3
  | exact S 16 111 4 cell_16_111_4
  | exact S 16 111 5 cell_16_111_5
theorem cell_16_112_0 : C 16 112 0 := by decide +kernel
theorem cell_16_112_1 : C 16 112 1 := by decide +kernel
theorem cell_16_112_2 : C 16 112 2 := by decide +kernel
theorem cell_16_112_3 : C 16 112 3 := by decide +kernel
theorem cell_16_112_4 : C 16 112 4 := by decide +kernel
theorem cell_16_112_5 : C 16 112 5 := by decide +kernel
theorem row_16_112 : ThresholdAt 16 112 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 112 0 cell_16_112_0
  | exact S 16 112 1 cell_16_112_1
  | exact S 16 112 2 cell_16_112_2
  | exact S 16 112 3 cell_16_112_3
  | exact S 16 112 4 cell_16_112_4
  | exact S 16 112 5 cell_16_112_5
theorem cell_16_113_0 : C 16 113 0 := by decide +kernel
theorem cell_16_113_1 : C 16 113 1 := by decide +kernel
theorem cell_16_113_2 : C 16 113 2 := by decide +kernel
theorem cell_16_113_3 : C 16 113 3 := by decide +kernel
theorem cell_16_113_4 : C 16 113 4 := by decide +kernel
theorem cell_16_113_5 : C 16 113 5 := by decide +kernel
theorem row_16_113 : ThresholdAt 16 113 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 113 0 cell_16_113_0
  | exact S 16 113 1 cell_16_113_1
  | exact S 16 113 2 cell_16_113_2
  | exact S 16 113 3 cell_16_113_3
  | exact S 16 113 4 cell_16_113_4
  | exact S 16 113 5 cell_16_113_5
theorem cell_16_114_0 : C 16 114 0 := by decide +kernel
theorem cell_16_114_1 : C 16 114 1 := by decide +kernel
theorem cell_16_114_2 : C 16 114 2 := by decide +kernel
theorem cell_16_114_3 : C 16 114 3 := by decide +kernel
theorem cell_16_114_4 : C 16 114 4 := by decide +kernel
theorem cell_16_114_5 : C 16 114 5 := by decide +kernel
theorem row_16_114 : ThresholdAt 16 114 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 114 0 cell_16_114_0
  | exact S 16 114 1 cell_16_114_1
  | exact S 16 114 2 cell_16_114_2
  | exact S 16 114 3 cell_16_114_3
  | exact S 16 114 4 cell_16_114_4
  | exact S 16 114 5 cell_16_114_5
theorem cell_16_115_0 : C 16 115 0 := by decide +kernel
theorem cell_16_115_1 : C 16 115 1 := by decide +kernel
theorem cell_16_115_2 : C 16 115 2 := by decide +kernel
theorem cell_16_115_3 : C 16 115 3 := by decide +kernel
theorem cell_16_115_4 : C 16 115 4 := by decide +kernel
theorem cell_16_115_5 : C 16 115 5 := by decide +kernel
theorem row_16_115 : ThresholdAt 16 115 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 115 0 cell_16_115_0
  | exact S 16 115 1 cell_16_115_1
  | exact S 16 115 2 cell_16_115_2
  | exact S 16 115 3 cell_16_115_3
  | exact S 16 115 4 cell_16_115_4
  | exact S 16 115 5 cell_16_115_5
theorem cell_16_116_0 : C 16 116 0 := by decide +kernel
theorem cell_16_116_1 : C 16 116 1 := by decide +kernel
theorem cell_16_116_2 : C 16 116 2 := by decide +kernel
theorem cell_16_116_3 : C 16 116 3 := by decide +kernel
theorem cell_16_116_4 : C 16 116 4 := by decide +kernel
theorem cell_16_116_5 : C 16 116 5 := by decide +kernel
theorem row_16_116 : ThresholdAt 16 116 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 116 0 cell_16_116_0
  | exact S 16 116 1 cell_16_116_1
  | exact S 16 116 2 cell_16_116_2
  | exact S 16 116 3 cell_16_116_3
  | exact S 16 116 4 cell_16_116_4
  | exact S 16 116 5 cell_16_116_5
theorem cell_16_117_0 : C 16 117 0 := by decide +kernel
theorem cell_16_117_1 : C 16 117 1 := by decide +kernel
theorem cell_16_117_2 : C 16 117 2 := by decide +kernel
theorem cell_16_117_3 : C 16 117 3 := by decide +kernel
theorem cell_16_117_4 : C 16 117 4 := by decide +kernel
theorem cell_16_117_5 : C 16 117 5 := by decide +kernel
theorem row_16_117 : ThresholdAt 16 117 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 117 0 cell_16_117_0
  | exact S 16 117 1 cell_16_117_1
  | exact S 16 117 2 cell_16_117_2
  | exact S 16 117 3 cell_16_117_3
  | exact S 16 117 4 cell_16_117_4
  | exact S 16 117 5 cell_16_117_5
theorem cell_16_118_0 : C 16 118 0 := by decide +kernel
theorem cell_16_118_1 : C 16 118 1 := by decide +kernel
theorem cell_16_118_2 : C 16 118 2 := by decide +kernel
theorem cell_16_118_3 : C 16 118 3 := by decide +kernel
theorem cell_16_118_4 : C 16 118 4 := by decide +kernel
theorem cell_16_118_5 : C 16 118 5 := by decide +kernel
theorem row_16_118 : ThresholdAt 16 118 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 118 0 cell_16_118_0
  | exact S 16 118 1 cell_16_118_1
  | exact S 16 118 2 cell_16_118_2
  | exact S 16 118 3 cell_16_118_3
  | exact S 16 118 4 cell_16_118_4
  | exact S 16 118 5 cell_16_118_5
theorem cell_16_119_0 : C 16 119 0 := by decide +kernel
theorem cell_16_119_1 : C 16 119 1 := by decide +kernel
theorem cell_16_119_2 : C 16 119 2 := by decide +kernel
theorem cell_16_119_3 : C 16 119 3 := by decide +kernel
theorem cell_16_119_4 : C 16 119 4 := by decide +kernel
theorem cell_16_119_5 : C 16 119 5 := by decide +kernel
theorem row_16_119 : ThresholdAt 16 119 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 119 0 cell_16_119_0
  | exact S 16 119 1 cell_16_119_1
  | exact S 16 119 2 cell_16_119_2
  | exact S 16 119 3 cell_16_119_3
  | exact S 16 119 4 cell_16_119_4
  | exact S 16 119 5 cell_16_119_5
theorem cell_16_120_0 : C 16 120 0 := by decide +kernel
theorem cell_16_120_1 : C 16 120 1 := by decide +kernel
theorem cell_16_120_2 : C 16 120 2 := by decide +kernel
theorem cell_16_120_3 : C 16 120 3 := by decide +kernel
theorem cell_16_120_4 : C 16 120 4 := by decide +kernel
theorem cell_16_120_5 : C 16 120 5 := by decide +kernel
theorem row_16_120 : ThresholdAt 16 120 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 120 0 cell_16_120_0
  | exact S 16 120 1 cell_16_120_1
  | exact S 16 120 2 cell_16_120_2
  | exact S 16 120 3 cell_16_120_3
  | exact S 16 120 4 cell_16_120_4
  | exact S 16 120 5 cell_16_120_5
theorem cell_16_121_0 : C 16 121 0 := by decide +kernel
theorem cell_16_121_1 : C 16 121 1 := by decide +kernel
theorem cell_16_121_2 : C 16 121 2 := by decide +kernel
theorem cell_16_121_3 : C 16 121 3 := by decide +kernel
theorem cell_16_121_4 : C 16 121 4 := by decide +kernel
theorem cell_16_121_5 : C 16 121 5 := by decide +kernel
theorem row_16_121 : ThresholdAt 16 121 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 121 0 cell_16_121_0
  | exact S 16 121 1 cell_16_121_1
  | exact S 16 121 2 cell_16_121_2
  | exact S 16 121 3 cell_16_121_3
  | exact S 16 121 4 cell_16_121_4
  | exact S 16 121 5 cell_16_121_5
theorem cell_16_122_0 : C 16 122 0 := by decide +kernel
theorem cell_16_122_1 : C 16 122 1 := by decide +kernel
theorem cell_16_122_2 : C 16 122 2 := by decide +kernel
theorem cell_16_122_3 : C 16 122 3 := by decide +kernel
theorem cell_16_122_4 : C 16 122 4 := by decide +kernel
theorem cell_16_122_5 : C 16 122 5 := by decide +kernel
theorem row_16_122 : ThresholdAt 16 122 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 122 0 cell_16_122_0
  | exact S 16 122 1 cell_16_122_1
  | exact S 16 122 2 cell_16_122_2
  | exact S 16 122 3 cell_16_122_3
  | exact S 16 122 4 cell_16_122_4
  | exact S 16 122 5 cell_16_122_5
theorem cell_16_123_0 : C 16 123 0 := by decide +kernel
theorem cell_16_123_1 : C 16 123 1 := by decide +kernel
theorem cell_16_123_2 : C 16 123 2 := by decide +kernel
theorem cell_16_123_3 : C 16 123 3 := by decide +kernel
theorem cell_16_123_4 : C 16 123 4 := by decide +kernel
theorem cell_16_123_5 : C 16 123 5 := by decide +kernel
theorem row_16_123 : ThresholdAt 16 123 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 16 123 0 cell_16_123_0
  | exact S 16 123 1 cell_16_123_1
  | exact S 16 123 2 cell_16_123_2
  | exact S 16 123 3 cell_16_123_3
  | exact S 16 123 4 cell_16_123_4
  | exact S 16 123 5 cell_16_123_5
theorem checkedR16 : ∀ V ∈ List.range 124, ThresholdAt 16 V := by
  intro V hV
  have hv : V < 124 := List.mem_range.mp hV
  by_cases h0_124 : V < 62
  · by_cases h0_62 : V < 31
    · by_cases h0_31 : V < 15
      · by_cases h0_15 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have he : V = 0 := by omega
              subst V
              exact row_16_0
            · by_cases h1_3 : V < 2
              · have he : V = 1 := by omega
                subst V
                exact row_16_1
              · have he : V = 2 := by omega
                subst V
                exact row_16_2
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have he : V = 3 := by omega
                subst V
                exact row_16_3
              · have he : V = 4 := by omega
                subst V
                exact row_16_4
            · by_cases h5_7 : V < 6
              · have he : V = 5 := by omega
                subst V
                exact row_16_5
              · have he : V = 6 := by omega
                subst V
                exact row_16_6
        · by_cases h7_15 : V < 11
          · by_cases h7_11 : V < 9
            · by_cases h7_9 : V < 8
              · have he : V = 7 := by omega
                subst V
                exact row_16_7
              · have he : V = 8 := by omega
                subst V
                exact row_16_8
            · by_cases h9_11 : V < 10
              · have he : V = 9 := by omega
                subst V
                exact row_16_9
              · have he : V = 10 := by omega
                subst V
                exact row_16_10
          · by_cases h11_15 : V < 13
            · by_cases h11_13 : V < 12
              · have he : V = 11 := by omega
                subst V
                exact row_16_11
              · have he : V = 12 := by omega
                subst V
                exact row_16_12
            · by_cases h13_15 : V < 14
              · have he : V = 13 := by omega
                subst V
                exact row_16_13
              · have he : V = 14 := by omega
                subst V
                exact row_16_14
      · by_cases h15_31 : V < 23
        · by_cases h15_23 : V < 19
          · by_cases h15_19 : V < 17
            · by_cases h15_17 : V < 16
              · have he : V = 15 := by omega
                subst V
                exact row_16_15
              · have he : V = 16 := by omega
                subst V
                exact row_16_16
            · by_cases h17_19 : V < 18
              · have he : V = 17 := by omega
                subst V
                exact row_16_17
              · have he : V = 18 := by omega
                subst V
                exact row_16_18
          · by_cases h19_23 : V < 21
            · by_cases h19_21 : V < 20
              · have he : V = 19 := by omega
                subst V
                exact row_16_19
              · have he : V = 20 := by omega
                subst V
                exact row_16_20
            · by_cases h21_23 : V < 22
              · have he : V = 21 := by omega
                subst V
                exact row_16_21
              · have he : V = 22 := by omega
                subst V
                exact row_16_22
        · by_cases h23_31 : V < 27
          · by_cases h23_27 : V < 25
            · by_cases h23_25 : V < 24
              · have he : V = 23 := by omega
                subst V
                exact row_16_23
              · have he : V = 24 := by omega
                subst V
                exact row_16_24
            · by_cases h25_27 : V < 26
              · have he : V = 25 := by omega
                subst V
                exact row_16_25
              · have he : V = 26 := by omega
                subst V
                exact row_16_26
          · by_cases h27_31 : V < 29
            · by_cases h27_29 : V < 28
              · have he : V = 27 := by omega
                subst V
                exact row_16_27
              · have he : V = 28 := by omega
                subst V
                exact row_16_28
            · by_cases h29_31 : V < 30
              · have he : V = 29 := by omega
                subst V
                exact row_16_29
              · have he : V = 30 := by omega
                subst V
                exact row_16_30
    · by_cases h31_62 : V < 46
      · by_cases h31_46 : V < 38
        · by_cases h31_38 : V < 34
          · by_cases h31_34 : V < 32
            · have he : V = 31 := by omega
              subst V
              exact row_16_31
            · by_cases h32_34 : V < 33
              · have he : V = 32 := by omega
                subst V
                exact row_16_32
              · have he : V = 33 := by omega
                subst V
                exact row_16_33
          · by_cases h34_38 : V < 36
            · by_cases h34_36 : V < 35
              · have he : V = 34 := by omega
                subst V
                exact row_16_34
              · have he : V = 35 := by omega
                subst V
                exact row_16_35
            · by_cases h36_38 : V < 37
              · have he : V = 36 := by omega
                subst V
                exact row_16_36
              · have he : V = 37 := by omega
                subst V
                exact row_16_37
        · by_cases h38_46 : V < 42
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have he : V = 38 := by omega
                subst V
                exact row_16_38
              · have he : V = 39 := by omega
                subst V
                exact row_16_39
            · by_cases h40_42 : V < 41
              · have he : V = 40 := by omega
                subst V
                exact row_16_40
              · have he : V = 41 := by omega
                subst V
                exact row_16_41
          · by_cases h42_46 : V < 44
            · by_cases h42_44 : V < 43
              · have he : V = 42 := by omega
                subst V
                exact row_16_42
              · have he : V = 43 := by omega
                subst V
                exact row_16_43
            · by_cases h44_46 : V < 45
              · have he : V = 44 := by omega
                subst V
                exact row_16_44
              · have he : V = 45 := by omega
                subst V
                exact row_16_45
      · by_cases h46_62 : V < 54
        · by_cases h46_54 : V < 50
          · by_cases h46_50 : V < 48
            · by_cases h46_48 : V < 47
              · have he : V = 46 := by omega
                subst V
                exact row_16_46
              · have he : V = 47 := by omega
                subst V
                exact row_16_47
            · by_cases h48_50 : V < 49
              · have he : V = 48 := by omega
                subst V
                exact row_16_48
              · have he : V = 49 := by omega
                subst V
                exact row_16_49
          · by_cases h50_54 : V < 52
            · by_cases h50_52 : V < 51
              · have he : V = 50 := by omega
                subst V
                exact row_16_50
              · have he : V = 51 := by omega
                subst V
                exact row_16_51
            · by_cases h52_54 : V < 53
              · have he : V = 52 := by omega
                subst V
                exact row_16_52
              · have he : V = 53 := by omega
                subst V
                exact row_16_53
        · by_cases h54_62 : V < 58
          · by_cases h54_58 : V < 56
            · by_cases h54_56 : V < 55
              · have he : V = 54 := by omega
                subst V
                exact row_16_54
              · have he : V = 55 := by omega
                subst V
                exact row_16_55
            · by_cases h56_58 : V < 57
              · have he : V = 56 := by omega
                subst V
                exact row_16_56
              · have he : V = 57 := by omega
                subst V
                exact row_16_57
          · by_cases h58_62 : V < 60
            · by_cases h58_60 : V < 59
              · have he : V = 58 := by omega
                subst V
                exact row_16_58
              · have he : V = 59 := by omega
                subst V
                exact row_16_59
            · by_cases h60_62 : V < 61
              · have he : V = 60 := by omega
                subst V
                exact row_16_60
              · have he : V = 61 := by omega
                subst V
                exact row_16_61
  · by_cases h62_124 : V < 93
    · by_cases h62_93 : V < 77
      · by_cases h62_77 : V < 69
        · by_cases h62_69 : V < 65
          · by_cases h62_65 : V < 63
            · have he : V = 62 := by omega
              subst V
              exact row_16_62
            · by_cases h63_65 : V < 64
              · have he : V = 63 := by omega
                subst V
                exact row_16_63
              · have he : V = 64 := by omega
                subst V
                exact row_16_64
          · by_cases h65_69 : V < 67
            · by_cases h65_67 : V < 66
              · have he : V = 65 := by omega
                subst V
                exact row_16_65
              · have he : V = 66 := by omega
                subst V
                exact row_16_66
            · by_cases h67_69 : V < 68
              · have he : V = 67 := by omega
                subst V
                exact row_16_67
              · have he : V = 68 := by omega
                subst V
                exact row_16_68
        · by_cases h69_77 : V < 73
          · by_cases h69_73 : V < 71
            · by_cases h69_71 : V < 70
              · have he : V = 69 := by omega
                subst V
                exact row_16_69
              · have he : V = 70 := by omega
                subst V
                exact row_16_70
            · by_cases h71_73 : V < 72
              · have he : V = 71 := by omega
                subst V
                exact row_16_71
              · have he : V = 72 := by omega
                subst V
                exact row_16_72
          · by_cases h73_77 : V < 75
            · by_cases h73_75 : V < 74
              · have he : V = 73 := by omega
                subst V
                exact row_16_73
              · have he : V = 74 := by omega
                subst V
                exact row_16_74
            · by_cases h75_77 : V < 76
              · have he : V = 75 := by omega
                subst V
                exact row_16_75
              · have he : V = 76 := by omega
                subst V
                exact row_16_76
      · by_cases h77_93 : V < 85
        · by_cases h77_85 : V < 81
          · by_cases h77_81 : V < 79
            · by_cases h77_79 : V < 78
              · have he : V = 77 := by omega
                subst V
                exact row_16_77
              · have he : V = 78 := by omega
                subst V
                exact row_16_78
            · by_cases h79_81 : V < 80
              · have he : V = 79 := by omega
                subst V
                exact row_16_79
              · have he : V = 80 := by omega
                subst V
                exact row_16_80
          · by_cases h81_85 : V < 83
            · by_cases h81_83 : V < 82
              · have he : V = 81 := by omega
                subst V
                exact row_16_81
              · have he : V = 82 := by omega
                subst V
                exact row_16_82
            · by_cases h83_85 : V < 84
              · have he : V = 83 := by omega
                subst V
                exact row_16_83
              · have he : V = 84 := by omega
                subst V
                exact row_16_84
        · by_cases h85_93 : V < 89
          · by_cases h85_89 : V < 87
            · by_cases h85_87 : V < 86
              · have he : V = 85 := by omega
                subst V
                exact row_16_85
              · have he : V = 86 := by omega
                subst V
                exact row_16_86
            · by_cases h87_89 : V < 88
              · have he : V = 87 := by omega
                subst V
                exact row_16_87
              · have he : V = 88 := by omega
                subst V
                exact row_16_88
          · by_cases h89_93 : V < 91
            · by_cases h89_91 : V < 90
              · have he : V = 89 := by omega
                subst V
                exact row_16_89
              · have he : V = 90 := by omega
                subst V
                exact row_16_90
            · by_cases h91_93 : V < 92
              · have he : V = 91 := by omega
                subst V
                exact row_16_91
              · have he : V = 92 := by omega
                subst V
                exact row_16_92
    · by_cases h93_124 : V < 108
      · by_cases h93_108 : V < 100
        · by_cases h93_100 : V < 96
          · by_cases h93_96 : V < 94
            · have he : V = 93 := by omega
              subst V
              exact row_16_93
            · by_cases h94_96 : V < 95
              · have he : V = 94 := by omega
                subst V
                exact row_16_94
              · have he : V = 95 := by omega
                subst V
                exact row_16_95
          · by_cases h96_100 : V < 98
            · by_cases h96_98 : V < 97
              · have he : V = 96 := by omega
                subst V
                exact row_16_96
              · have he : V = 97 := by omega
                subst V
                exact row_16_97
            · by_cases h98_100 : V < 99
              · have he : V = 98 := by omega
                subst V
                exact row_16_98
              · have he : V = 99 := by omega
                subst V
                exact row_16_99
        · by_cases h100_108 : V < 104
          · by_cases h100_104 : V < 102
            · by_cases h100_102 : V < 101
              · have he : V = 100 := by omega
                subst V
                exact row_16_100
              · have he : V = 101 := by omega
                subst V
                exact row_16_101
            · by_cases h102_104 : V < 103
              · have he : V = 102 := by omega
                subst V
                exact row_16_102
              · have he : V = 103 := by omega
                subst V
                exact row_16_103
          · by_cases h104_108 : V < 106
            · by_cases h104_106 : V < 105
              · have he : V = 104 := by omega
                subst V
                exact row_16_104
              · have he : V = 105 := by omega
                subst V
                exact row_16_105
            · by_cases h106_108 : V < 107
              · have he : V = 106 := by omega
                subst V
                exact row_16_106
              · have he : V = 107 := by omega
                subst V
                exact row_16_107
      · by_cases h108_124 : V < 116
        · by_cases h108_116 : V < 112
          · by_cases h108_112 : V < 110
            · by_cases h108_110 : V < 109
              · have he : V = 108 := by omega
                subst V
                exact row_16_108
              · have he : V = 109 := by omega
                subst V
                exact row_16_109
            · by_cases h110_112 : V < 111
              · have he : V = 110 := by omega
                subst V
                exact row_16_110
              · have he : V = 111 := by omega
                subst V
                exact row_16_111
          · by_cases h112_116 : V < 114
            · by_cases h112_114 : V < 113
              · have he : V = 112 := by omega
                subst V
                exact row_16_112
              · have he : V = 113 := by omega
                subst V
                exact row_16_113
            · by_cases h114_116 : V < 115
              · have he : V = 114 := by omega
                subst V
                exact row_16_114
              · have he : V = 115 := by omega
                subst V
                exact row_16_115
        · by_cases h116_124 : V < 120
          · by_cases h116_120 : V < 118
            · by_cases h116_118 : V < 117
              · have he : V = 116 := by omega
                subst V
                exact row_16_116
              · have he : V = 117 := by omega
                subst V
                exact row_16_117
            · by_cases h118_120 : V < 119
              · have he : V = 118 := by omega
                subst V
                exact row_16_118
              · have he : V = 119 := by omega
                subst V
                exact row_16_119
          · by_cases h120_124 : V < 122
            · by_cases h120_122 : V < 121
              · have he : V = 120 := by omega
                subst V
                exact row_16_120
              · have he : V = 121 := by omega
                subst V
                exact row_16_121
            · by_cases h122_124 : V < 123
              · have he : V = 122 := by omega
                subst V
                exact row_16_122
              · have he : V = 123 := by omega
                subst V
                exact row_16_123
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
