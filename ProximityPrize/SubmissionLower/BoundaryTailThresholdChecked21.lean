import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked20

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem cell_21_0_0 : C 21 0 0 := by decide +kernel
theorem cell_21_0_1 : C 21 0 1 := by decide +kernel
theorem cell_21_0_2 : C 21 0 2 := by decide +kernel
theorem cell_21_0_3 : C 21 0 3 := by decide +kernel
theorem cell_21_0_4 : C 21 0 4 := by decide +kernel
theorem cell_21_0_5 : C 21 0 5 := by decide +kernel
theorem row_21_0 : ThresholdAt 21 0 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 0 0 cell_21_0_0
  | exact S 21 0 1 cell_21_0_1
  | exact S 21 0 2 cell_21_0_2
  | exact S 21 0 3 cell_21_0_3
  | exact S 21 0 4 cell_21_0_4
  | exact S 21 0 5 cell_21_0_5
theorem cell_21_1_0 : C 21 1 0 := by decide +kernel
theorem cell_21_1_1 : C 21 1 1 := by decide +kernel
theorem cell_21_1_2 : C 21 1 2 := by decide +kernel
theorem cell_21_1_3 : C 21 1 3 := by decide +kernel
theorem cell_21_1_4 : C 21 1 4 := by decide +kernel
theorem cell_21_1_5 : C 21 1 5 := by decide +kernel
theorem row_21_1 : ThresholdAt 21 1 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 1 0 cell_21_1_0
  | exact S 21 1 1 cell_21_1_1
  | exact S 21 1 2 cell_21_1_2
  | exact S 21 1 3 cell_21_1_3
  | exact S 21 1 4 cell_21_1_4
  | exact S 21 1 5 cell_21_1_5
theorem cell_21_2_0 : C 21 2 0 := by decide +kernel
theorem cell_21_2_1 : C 21 2 1 := by decide +kernel
theorem cell_21_2_2 : C 21 2 2 := by decide +kernel
theorem cell_21_2_3 : C 21 2 3 := by decide +kernel
theorem cell_21_2_4 : C 21 2 4 := by decide +kernel
theorem cell_21_2_5 : C 21 2 5 := by decide +kernel
theorem row_21_2 : ThresholdAt 21 2 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 2 0 cell_21_2_0
  | exact S 21 2 1 cell_21_2_1
  | exact S 21 2 2 cell_21_2_2
  | exact S 21 2 3 cell_21_2_3
  | exact S 21 2 4 cell_21_2_4
  | exact S 21 2 5 cell_21_2_5
theorem cell_21_3_0 : C 21 3 0 := by decide +kernel
theorem cell_21_3_1 : C 21 3 1 := by decide +kernel
theorem cell_21_3_2 : C 21 3 2 := by decide +kernel
theorem cell_21_3_3 : C 21 3 3 := by decide +kernel
theorem cell_21_3_4 : C 21 3 4 := by decide +kernel
theorem cell_21_3_5 : C 21 3 5 := by decide +kernel
theorem row_21_3 : ThresholdAt 21 3 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 3 0 cell_21_3_0
  | exact S 21 3 1 cell_21_3_1
  | exact S 21 3 2 cell_21_3_2
  | exact S 21 3 3 cell_21_3_3
  | exact S 21 3 4 cell_21_3_4
  | exact S 21 3 5 cell_21_3_5
theorem cell_21_4_0 : C 21 4 0 := by decide +kernel
theorem cell_21_4_1 : C 21 4 1 := by decide +kernel
theorem cell_21_4_2 : C 21 4 2 := by decide +kernel
theorem cell_21_4_3 : C 21 4 3 := by decide +kernel
theorem cell_21_4_4 : C 21 4 4 := by decide +kernel
theorem cell_21_4_5 : C 21 4 5 := by decide +kernel
theorem row_21_4 : ThresholdAt 21 4 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 4 0 cell_21_4_0
  | exact S 21 4 1 cell_21_4_1
  | exact S 21 4 2 cell_21_4_2
  | exact S 21 4 3 cell_21_4_3
  | exact S 21 4 4 cell_21_4_4
  | exact S 21 4 5 cell_21_4_5
theorem cell_21_5_0 : C 21 5 0 := by decide +kernel
theorem cell_21_5_1 : C 21 5 1 := by decide +kernel
theorem cell_21_5_2 : C 21 5 2 := by decide +kernel
theorem cell_21_5_3 : C 21 5 3 := by decide +kernel
theorem cell_21_5_4 : C 21 5 4 := by decide +kernel
theorem cell_21_5_5 : C 21 5 5 := by decide +kernel
theorem row_21_5 : ThresholdAt 21 5 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 5 0 cell_21_5_0
  | exact S 21 5 1 cell_21_5_1
  | exact S 21 5 2 cell_21_5_2
  | exact S 21 5 3 cell_21_5_3
  | exact S 21 5 4 cell_21_5_4
  | exact S 21 5 5 cell_21_5_5
theorem cell_21_6_0 : C 21 6 0 := by decide +kernel
theorem cell_21_6_1 : C 21 6 1 := by decide +kernel
theorem cell_21_6_2 : C 21 6 2 := by decide +kernel
theorem cell_21_6_3 : C 21 6 3 := by decide +kernel
theorem cell_21_6_4 : C 21 6 4 := by decide +kernel
theorem cell_21_6_5 : C 21 6 5 := by decide +kernel
theorem row_21_6 : ThresholdAt 21 6 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 6 0 cell_21_6_0
  | exact S 21 6 1 cell_21_6_1
  | exact S 21 6 2 cell_21_6_2
  | exact S 21 6 3 cell_21_6_3
  | exact S 21 6 4 cell_21_6_4
  | exact S 21 6 5 cell_21_6_5
theorem cell_21_7_0 : C 21 7 0 := by decide +kernel
theorem cell_21_7_1 : C 21 7 1 := by decide +kernel
theorem cell_21_7_2 : C 21 7 2 := by decide +kernel
theorem cell_21_7_3 : C 21 7 3 := by decide +kernel
theorem cell_21_7_4 : C 21 7 4 := by decide +kernel
theorem cell_21_7_5 : C 21 7 5 := by decide +kernel
theorem row_21_7 : ThresholdAt 21 7 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 7 0 cell_21_7_0
  | exact S 21 7 1 cell_21_7_1
  | exact S 21 7 2 cell_21_7_2
  | exact S 21 7 3 cell_21_7_3
  | exact S 21 7 4 cell_21_7_4
  | exact S 21 7 5 cell_21_7_5
theorem cell_21_8_0 : C 21 8 0 := by decide +kernel
theorem cell_21_8_1 : C 21 8 1 := by decide +kernel
theorem cell_21_8_2 : C 21 8 2 := by decide +kernel
theorem cell_21_8_3 : C 21 8 3 := by decide +kernel
theorem cell_21_8_4 : C 21 8 4 := by decide +kernel
theorem cell_21_8_5 : C 21 8 5 := by decide +kernel
theorem row_21_8 : ThresholdAt 21 8 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 8 0 cell_21_8_0
  | exact S 21 8 1 cell_21_8_1
  | exact S 21 8 2 cell_21_8_2
  | exact S 21 8 3 cell_21_8_3
  | exact S 21 8 4 cell_21_8_4
  | exact S 21 8 5 cell_21_8_5
theorem cell_21_9_0 : C 21 9 0 := by decide +kernel
theorem cell_21_9_1 : C 21 9 1 := by decide +kernel
theorem cell_21_9_2 : C 21 9 2 := by decide +kernel
theorem cell_21_9_3 : C 21 9 3 := by decide +kernel
theorem cell_21_9_4 : C 21 9 4 := by decide +kernel
theorem cell_21_9_5 : C 21 9 5 := by decide +kernel
theorem row_21_9 : ThresholdAt 21 9 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 9 0 cell_21_9_0
  | exact S 21 9 1 cell_21_9_1
  | exact S 21 9 2 cell_21_9_2
  | exact S 21 9 3 cell_21_9_3
  | exact S 21 9 4 cell_21_9_4
  | exact S 21 9 5 cell_21_9_5
theorem cell_21_10_0 : C 21 10 0 := by decide +kernel
theorem cell_21_10_1 : C 21 10 1 := by decide +kernel
theorem cell_21_10_2 : C 21 10 2 := by decide +kernel
theorem cell_21_10_3 : C 21 10 3 := by decide +kernel
theorem cell_21_10_4 : C 21 10 4 := by decide +kernel
theorem cell_21_10_5 : C 21 10 5 := by decide +kernel
theorem row_21_10 : ThresholdAt 21 10 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 10 0 cell_21_10_0
  | exact S 21 10 1 cell_21_10_1
  | exact S 21 10 2 cell_21_10_2
  | exact S 21 10 3 cell_21_10_3
  | exact S 21 10 4 cell_21_10_4
  | exact S 21 10 5 cell_21_10_5
theorem cell_21_11_0 : C 21 11 0 := by decide +kernel
theorem cell_21_11_1 : C 21 11 1 := by decide +kernel
theorem cell_21_11_2 : C 21 11 2 := by decide +kernel
theorem cell_21_11_3 : C 21 11 3 := by decide +kernel
theorem cell_21_11_4 : C 21 11 4 := by decide +kernel
theorem cell_21_11_5 : C 21 11 5 := by decide +kernel
theorem row_21_11 : ThresholdAt 21 11 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 11 0 cell_21_11_0
  | exact S 21 11 1 cell_21_11_1
  | exact S 21 11 2 cell_21_11_2
  | exact S 21 11 3 cell_21_11_3
  | exact S 21 11 4 cell_21_11_4
  | exact S 21 11 5 cell_21_11_5
theorem cell_21_12_0 : C 21 12 0 := by decide +kernel
theorem cell_21_12_1 : C 21 12 1 := by decide +kernel
theorem cell_21_12_2 : C 21 12 2 := by decide +kernel
theorem cell_21_12_3 : C 21 12 3 := by decide +kernel
theorem cell_21_12_4 : C 21 12 4 := by decide +kernel
theorem cell_21_12_5 : C 21 12 5 := by decide +kernel
theorem row_21_12 : ThresholdAt 21 12 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 12 0 cell_21_12_0
  | exact S 21 12 1 cell_21_12_1
  | exact S 21 12 2 cell_21_12_2
  | exact S 21 12 3 cell_21_12_3
  | exact S 21 12 4 cell_21_12_4
  | exact S 21 12 5 cell_21_12_5
theorem cell_21_13_0 : C 21 13 0 := by decide +kernel
theorem cell_21_13_1 : C 21 13 1 := by decide +kernel
theorem cell_21_13_2 : C 21 13 2 := by decide +kernel
theorem cell_21_13_3 : C 21 13 3 := by decide +kernel
theorem cell_21_13_4 : C 21 13 4 := by decide +kernel
theorem cell_21_13_5 : C 21 13 5 := by decide +kernel
theorem row_21_13 : ThresholdAt 21 13 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 13 0 cell_21_13_0
  | exact S 21 13 1 cell_21_13_1
  | exact S 21 13 2 cell_21_13_2
  | exact S 21 13 3 cell_21_13_3
  | exact S 21 13 4 cell_21_13_4
  | exact S 21 13 5 cell_21_13_5
theorem cell_21_14_0 : C 21 14 0 := by decide +kernel
theorem cell_21_14_1 : C 21 14 1 := by decide +kernel
theorem cell_21_14_2 : C 21 14 2 := by decide +kernel
theorem cell_21_14_3 : C 21 14 3 := by decide +kernel
theorem cell_21_14_4 : C 21 14 4 := by decide +kernel
theorem cell_21_14_5 : C 21 14 5 := by decide +kernel
theorem row_21_14 : ThresholdAt 21 14 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 14 0 cell_21_14_0
  | exact S 21 14 1 cell_21_14_1
  | exact S 21 14 2 cell_21_14_2
  | exact S 21 14 3 cell_21_14_3
  | exact S 21 14 4 cell_21_14_4
  | exact S 21 14 5 cell_21_14_5
theorem cell_21_15_0 : C 21 15 0 := by decide +kernel
theorem cell_21_15_1 : C 21 15 1 := by decide +kernel
theorem cell_21_15_2 : C 21 15 2 := by decide +kernel
theorem cell_21_15_3 : C 21 15 3 := by decide +kernel
theorem cell_21_15_4 : C 21 15 4 := by decide +kernel
theorem cell_21_15_5 : C 21 15 5 := by decide +kernel
theorem row_21_15 : ThresholdAt 21 15 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 15 0 cell_21_15_0
  | exact S 21 15 1 cell_21_15_1
  | exact S 21 15 2 cell_21_15_2
  | exact S 21 15 3 cell_21_15_3
  | exact S 21 15 4 cell_21_15_4
  | exact S 21 15 5 cell_21_15_5
theorem cell_21_16_0 : C 21 16 0 := by decide +kernel
theorem cell_21_16_1 : C 21 16 1 := by decide +kernel
theorem cell_21_16_2 : C 21 16 2 := by decide +kernel
theorem cell_21_16_3 : C 21 16 3 := by decide +kernel
theorem cell_21_16_4 : C 21 16 4 := by decide +kernel
theorem cell_21_16_5 : C 21 16 5 := by decide +kernel
theorem row_21_16 : ThresholdAt 21 16 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 16 0 cell_21_16_0
  | exact S 21 16 1 cell_21_16_1
  | exact S 21 16 2 cell_21_16_2
  | exact S 21 16 3 cell_21_16_3
  | exact S 21 16 4 cell_21_16_4
  | exact S 21 16 5 cell_21_16_5
theorem cell_21_17_0 : C 21 17 0 := by decide +kernel
theorem cell_21_17_1 : C 21 17 1 := by decide +kernel
theorem cell_21_17_2 : C 21 17 2 := by decide +kernel
theorem cell_21_17_3 : C 21 17 3 := by decide +kernel
theorem cell_21_17_4 : C 21 17 4 := by decide +kernel
theorem cell_21_17_5 : C 21 17 5 := by decide +kernel
theorem row_21_17 : ThresholdAt 21 17 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 17 0 cell_21_17_0
  | exact S 21 17 1 cell_21_17_1
  | exact S 21 17 2 cell_21_17_2
  | exact S 21 17 3 cell_21_17_3
  | exact S 21 17 4 cell_21_17_4
  | exact S 21 17 5 cell_21_17_5
theorem cell_21_18_0 : C 21 18 0 := by decide +kernel
theorem cell_21_18_1 : C 21 18 1 := by decide +kernel
theorem cell_21_18_2 : C 21 18 2 := by decide +kernel
theorem cell_21_18_3 : C 21 18 3 := by decide +kernel
theorem cell_21_18_4 : C 21 18 4 := by decide +kernel
theorem cell_21_18_5 : C 21 18 5 := by decide +kernel
theorem row_21_18 : ThresholdAt 21 18 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 18 0 cell_21_18_0
  | exact S 21 18 1 cell_21_18_1
  | exact S 21 18 2 cell_21_18_2
  | exact S 21 18 3 cell_21_18_3
  | exact S 21 18 4 cell_21_18_4
  | exact S 21 18 5 cell_21_18_5
theorem cell_21_19_0 : C 21 19 0 := by decide +kernel
theorem cell_21_19_1 : C 21 19 1 := by decide +kernel
theorem cell_21_19_2 : C 21 19 2 := by decide +kernel
theorem cell_21_19_3 : C 21 19 3 := by decide +kernel
theorem cell_21_19_4 : C 21 19 4 := by decide +kernel
theorem cell_21_19_5 : C 21 19 5 := by decide +kernel
theorem row_21_19 : ThresholdAt 21 19 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 19 0 cell_21_19_0
  | exact S 21 19 1 cell_21_19_1
  | exact S 21 19 2 cell_21_19_2
  | exact S 21 19 3 cell_21_19_3
  | exact S 21 19 4 cell_21_19_4
  | exact S 21 19 5 cell_21_19_5
theorem cell_21_20_0 : C 21 20 0 := by decide +kernel
theorem cell_21_20_1 : C 21 20 1 := by decide +kernel
theorem cell_21_20_2 : C 21 20 2 := by decide +kernel
theorem cell_21_20_3 : C 21 20 3 := by decide +kernel
theorem cell_21_20_4 : C 21 20 4 := by decide +kernel
theorem cell_21_20_5 : C 21 20 5 := by decide +kernel
theorem row_21_20 : ThresholdAt 21 20 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 20 0 cell_21_20_0
  | exact S 21 20 1 cell_21_20_1
  | exact S 21 20 2 cell_21_20_2
  | exact S 21 20 3 cell_21_20_3
  | exact S 21 20 4 cell_21_20_4
  | exact S 21 20 5 cell_21_20_5
theorem cell_21_21_0 : C 21 21 0 := by decide +kernel
theorem cell_21_21_1 : C 21 21 1 := by decide +kernel
theorem cell_21_21_2 : C 21 21 2 := by decide +kernel
theorem cell_21_21_3 : C 21 21 3 := by decide +kernel
theorem cell_21_21_4 : C 21 21 4 := by decide +kernel
theorem cell_21_21_5 : C 21 21 5 := by decide +kernel
theorem row_21_21 : ThresholdAt 21 21 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 21 0 cell_21_21_0
  | exact S 21 21 1 cell_21_21_1
  | exact S 21 21 2 cell_21_21_2
  | exact S 21 21 3 cell_21_21_3
  | exact S 21 21 4 cell_21_21_4
  | exact S 21 21 5 cell_21_21_5
theorem cell_21_22_0 : C 21 22 0 := by decide +kernel
theorem cell_21_22_1 : C 21 22 1 := by decide +kernel
theorem cell_21_22_2 : C 21 22 2 := by decide +kernel
theorem cell_21_22_3 : C 21 22 3 := by decide +kernel
theorem cell_21_22_4 : C 21 22 4 := by decide +kernel
theorem cell_21_22_5 : C 21 22 5 := by decide +kernel
theorem row_21_22 : ThresholdAt 21 22 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 22 0 cell_21_22_0
  | exact S 21 22 1 cell_21_22_1
  | exact S 21 22 2 cell_21_22_2
  | exact S 21 22 3 cell_21_22_3
  | exact S 21 22 4 cell_21_22_4
  | exact S 21 22 5 cell_21_22_5
theorem cell_21_23_0 : C 21 23 0 := by decide +kernel
theorem cell_21_23_1 : C 21 23 1 := by decide +kernel
theorem cell_21_23_2 : C 21 23 2 := by decide +kernel
theorem cell_21_23_3 : C 21 23 3 := by decide +kernel
theorem cell_21_23_4 : C 21 23 4 := by decide +kernel
theorem cell_21_23_5 : C 21 23 5 := by decide +kernel
theorem row_21_23 : ThresholdAt 21 23 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 23 0 cell_21_23_0
  | exact S 21 23 1 cell_21_23_1
  | exact S 21 23 2 cell_21_23_2
  | exact S 21 23 3 cell_21_23_3
  | exact S 21 23 4 cell_21_23_4
  | exact S 21 23 5 cell_21_23_5
theorem cell_21_24_0 : C 21 24 0 := by decide +kernel
theorem cell_21_24_1 : C 21 24 1 := by decide +kernel
theorem cell_21_24_2 : C 21 24 2 := by decide +kernel
theorem cell_21_24_3 : C 21 24 3 := by decide +kernel
theorem cell_21_24_4 : C 21 24 4 := by decide +kernel
theorem cell_21_24_5 : C 21 24 5 := by decide +kernel
theorem row_21_24 : ThresholdAt 21 24 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 24 0 cell_21_24_0
  | exact S 21 24 1 cell_21_24_1
  | exact S 21 24 2 cell_21_24_2
  | exact S 21 24 3 cell_21_24_3
  | exact S 21 24 4 cell_21_24_4
  | exact S 21 24 5 cell_21_24_5
theorem cell_21_25_0 : C 21 25 0 := by decide +kernel
theorem cell_21_25_1 : C 21 25 1 := by decide +kernel
theorem cell_21_25_2 : C 21 25 2 := by decide +kernel
theorem cell_21_25_3 : C 21 25 3 := by decide +kernel
theorem cell_21_25_4 : C 21 25 4 := by decide +kernel
theorem cell_21_25_5 : C 21 25 5 := by decide +kernel
theorem row_21_25 : ThresholdAt 21 25 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 25 0 cell_21_25_0
  | exact S 21 25 1 cell_21_25_1
  | exact S 21 25 2 cell_21_25_2
  | exact S 21 25 3 cell_21_25_3
  | exact S 21 25 4 cell_21_25_4
  | exact S 21 25 5 cell_21_25_5
theorem cell_21_26_0 : C 21 26 0 := by decide +kernel
theorem cell_21_26_1 : C 21 26 1 := by decide +kernel
theorem cell_21_26_2 : C 21 26 2 := by decide +kernel
theorem cell_21_26_3 : C 21 26 3 := by decide +kernel
theorem cell_21_26_4 : C 21 26 4 := by decide +kernel
theorem cell_21_26_5 : C 21 26 5 := by decide +kernel
theorem row_21_26 : ThresholdAt 21 26 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 26 0 cell_21_26_0
  | exact S 21 26 1 cell_21_26_1
  | exact S 21 26 2 cell_21_26_2
  | exact S 21 26 3 cell_21_26_3
  | exact S 21 26 4 cell_21_26_4
  | exact S 21 26 5 cell_21_26_5
theorem cell_21_27_0 : C 21 27 0 := by decide +kernel
theorem cell_21_27_1 : C 21 27 1 := by decide +kernel
theorem cell_21_27_2 : C 21 27 2 := by decide +kernel
theorem cell_21_27_3 : C 21 27 3 := by decide +kernel
theorem cell_21_27_4 : C 21 27 4 := by decide +kernel
theorem cell_21_27_5 : C 21 27 5 := by decide +kernel
theorem row_21_27 : ThresholdAt 21 27 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 27 0 cell_21_27_0
  | exact S 21 27 1 cell_21_27_1
  | exact S 21 27 2 cell_21_27_2
  | exact S 21 27 3 cell_21_27_3
  | exact S 21 27 4 cell_21_27_4
  | exact S 21 27 5 cell_21_27_5
theorem cell_21_28_0 : C 21 28 0 := by decide +kernel
theorem cell_21_28_1 : C 21 28 1 := by decide +kernel
theorem cell_21_28_2 : C 21 28 2 := by decide +kernel
theorem cell_21_28_3 : C 21 28 3 := by decide +kernel
theorem cell_21_28_4 : C 21 28 4 := by decide +kernel
theorem cell_21_28_5 : C 21 28 5 := by decide +kernel
theorem row_21_28 : ThresholdAt 21 28 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 28 0 cell_21_28_0
  | exact S 21 28 1 cell_21_28_1
  | exact S 21 28 2 cell_21_28_2
  | exact S 21 28 3 cell_21_28_3
  | exact S 21 28 4 cell_21_28_4
  | exact S 21 28 5 cell_21_28_5
theorem cell_21_29_0 : C 21 29 0 := by decide +kernel
theorem cell_21_29_1 : C 21 29 1 := by decide +kernel
theorem cell_21_29_2 : C 21 29 2 := by decide +kernel
theorem cell_21_29_3 : C 21 29 3 := by decide +kernel
theorem cell_21_29_4 : C 21 29 4 := by decide +kernel
theorem cell_21_29_5 : C 21 29 5 := by decide +kernel
theorem row_21_29 : ThresholdAt 21 29 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 29 0 cell_21_29_0
  | exact S 21 29 1 cell_21_29_1
  | exact S 21 29 2 cell_21_29_2
  | exact S 21 29 3 cell_21_29_3
  | exact S 21 29 4 cell_21_29_4
  | exact S 21 29 5 cell_21_29_5
theorem cell_21_30_0 : C 21 30 0 := by decide +kernel
theorem cell_21_30_1 : C 21 30 1 := by decide +kernel
theorem cell_21_30_2 : C 21 30 2 := by decide +kernel
theorem cell_21_30_3 : C 21 30 3 := by decide +kernel
theorem cell_21_30_4 : C 21 30 4 := by decide +kernel
theorem cell_21_30_5 : C 21 30 5 := by decide +kernel
theorem row_21_30 : ThresholdAt 21 30 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 30 0 cell_21_30_0
  | exact S 21 30 1 cell_21_30_1
  | exact S 21 30 2 cell_21_30_2
  | exact S 21 30 3 cell_21_30_3
  | exact S 21 30 4 cell_21_30_4
  | exact S 21 30 5 cell_21_30_5
theorem cell_21_31_0 : C 21 31 0 := by decide +kernel
theorem cell_21_31_1 : C 21 31 1 := by decide +kernel
theorem cell_21_31_2 : C 21 31 2 := by decide +kernel
theorem cell_21_31_3 : C 21 31 3 := by decide +kernel
theorem cell_21_31_4 : C 21 31 4 := by decide +kernel
theorem cell_21_31_5 : C 21 31 5 := by decide +kernel
theorem row_21_31 : ThresholdAt 21 31 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 31 0 cell_21_31_0
  | exact S 21 31 1 cell_21_31_1
  | exact S 21 31 2 cell_21_31_2
  | exact S 21 31 3 cell_21_31_3
  | exact S 21 31 4 cell_21_31_4
  | exact S 21 31 5 cell_21_31_5
theorem cell_21_32_0 : C 21 32 0 := by decide +kernel
theorem cell_21_32_1 : C 21 32 1 := by decide +kernel
theorem cell_21_32_2 : C 21 32 2 := by decide +kernel
theorem cell_21_32_3 : C 21 32 3 := by decide +kernel
theorem cell_21_32_4 : C 21 32 4 := by decide +kernel
theorem cell_21_32_5 : C 21 32 5 := by decide +kernel
theorem row_21_32 : ThresholdAt 21 32 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 32 0 cell_21_32_0
  | exact S 21 32 1 cell_21_32_1
  | exact S 21 32 2 cell_21_32_2
  | exact S 21 32 3 cell_21_32_3
  | exact S 21 32 4 cell_21_32_4
  | exact S 21 32 5 cell_21_32_5
theorem cell_21_33_0 : C 21 33 0 := by decide +kernel
theorem cell_21_33_1 : C 21 33 1 := by decide +kernel
theorem cell_21_33_2 : C 21 33 2 := by decide +kernel
theorem cell_21_33_3 : C 21 33 3 := by decide +kernel
theorem cell_21_33_4 : C 21 33 4 := by decide +kernel
theorem cell_21_33_5 : C 21 33 5 := by decide +kernel
theorem row_21_33 : ThresholdAt 21 33 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 33 0 cell_21_33_0
  | exact S 21 33 1 cell_21_33_1
  | exact S 21 33 2 cell_21_33_2
  | exact S 21 33 3 cell_21_33_3
  | exact S 21 33 4 cell_21_33_4
  | exact S 21 33 5 cell_21_33_5
theorem cell_21_34_0 : C 21 34 0 := by decide +kernel
theorem cell_21_34_1 : C 21 34 1 := by decide +kernel
theorem cell_21_34_2 : C 21 34 2 := by decide +kernel
theorem cell_21_34_3 : C 21 34 3 := by decide +kernel
theorem cell_21_34_4 : C 21 34 4 := by decide +kernel
theorem cell_21_34_5 : C 21 34 5 := by decide +kernel
theorem row_21_34 : ThresholdAt 21 34 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 34 0 cell_21_34_0
  | exact S 21 34 1 cell_21_34_1
  | exact S 21 34 2 cell_21_34_2
  | exact S 21 34 3 cell_21_34_3
  | exact S 21 34 4 cell_21_34_4
  | exact S 21 34 5 cell_21_34_5
theorem cell_21_35_0 : C 21 35 0 := by decide +kernel
theorem cell_21_35_1 : C 21 35 1 := by decide +kernel
theorem cell_21_35_2 : C 21 35 2 := by decide +kernel
theorem cell_21_35_3 : C 21 35 3 := by decide +kernel
theorem cell_21_35_4 : C 21 35 4 := by decide +kernel
theorem cell_21_35_5 : C 21 35 5 := by decide +kernel
theorem row_21_35 : ThresholdAt 21 35 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 35 0 cell_21_35_0
  | exact S 21 35 1 cell_21_35_1
  | exact S 21 35 2 cell_21_35_2
  | exact S 21 35 3 cell_21_35_3
  | exact S 21 35 4 cell_21_35_4
  | exact S 21 35 5 cell_21_35_5
theorem cell_21_36_0 : C 21 36 0 := by decide +kernel
theorem cell_21_36_1 : C 21 36 1 := by decide +kernel
theorem cell_21_36_2 : C 21 36 2 := by decide +kernel
theorem cell_21_36_3 : C 21 36 3 := by decide +kernel
theorem cell_21_36_4 : C 21 36 4 := by decide +kernel
theorem cell_21_36_5 : C 21 36 5 := by decide +kernel
theorem row_21_36 : ThresholdAt 21 36 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 36 0 cell_21_36_0
  | exact S 21 36 1 cell_21_36_1
  | exact S 21 36 2 cell_21_36_2
  | exact S 21 36 3 cell_21_36_3
  | exact S 21 36 4 cell_21_36_4
  | exact S 21 36 5 cell_21_36_5
theorem cell_21_37_0 : C 21 37 0 := by decide +kernel
theorem cell_21_37_1 : C 21 37 1 := by decide +kernel
theorem cell_21_37_2 : C 21 37 2 := by decide +kernel
theorem cell_21_37_3 : C 21 37 3 := by decide +kernel
theorem cell_21_37_4 : C 21 37 4 := by decide +kernel
theorem cell_21_37_5 : C 21 37 5 := by decide +kernel
theorem row_21_37 : ThresholdAt 21 37 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 37 0 cell_21_37_0
  | exact S 21 37 1 cell_21_37_1
  | exact S 21 37 2 cell_21_37_2
  | exact S 21 37 3 cell_21_37_3
  | exact S 21 37 4 cell_21_37_4
  | exact S 21 37 5 cell_21_37_5
theorem cell_21_38_0 : C 21 38 0 := by decide +kernel
theorem cell_21_38_1 : C 21 38 1 := by decide +kernel
theorem cell_21_38_2 : C 21 38 2 := by decide +kernel
theorem cell_21_38_3 : C 21 38 3 := by decide +kernel
theorem cell_21_38_4 : C 21 38 4 := by decide +kernel
theorem cell_21_38_5 : C 21 38 5 := by decide +kernel
theorem row_21_38 : ThresholdAt 21 38 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 38 0 cell_21_38_0
  | exact S 21 38 1 cell_21_38_1
  | exact S 21 38 2 cell_21_38_2
  | exact S 21 38 3 cell_21_38_3
  | exact S 21 38 4 cell_21_38_4
  | exact S 21 38 5 cell_21_38_5
theorem cell_21_39_0 : C 21 39 0 := by decide +kernel
theorem cell_21_39_1 : C 21 39 1 := by decide +kernel
theorem cell_21_39_2 : C 21 39 2 := by decide +kernel
theorem cell_21_39_3 : C 21 39 3 := by decide +kernel
theorem cell_21_39_4 : C 21 39 4 := by decide +kernel
theorem cell_21_39_5 : C 21 39 5 := by decide +kernel
theorem row_21_39 : ThresholdAt 21 39 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 39 0 cell_21_39_0
  | exact S 21 39 1 cell_21_39_1
  | exact S 21 39 2 cell_21_39_2
  | exact S 21 39 3 cell_21_39_3
  | exact S 21 39 4 cell_21_39_4
  | exact S 21 39 5 cell_21_39_5
theorem cell_21_40_0 : C 21 40 0 := by decide +kernel
theorem cell_21_40_1 : C 21 40 1 := by decide +kernel
theorem cell_21_40_2 : C 21 40 2 := by decide +kernel
theorem cell_21_40_3 : C 21 40 3 := by decide +kernel
theorem cell_21_40_4 : C 21 40 4 := by decide +kernel
theorem cell_21_40_5 : C 21 40 5 := by decide +kernel
theorem row_21_40 : ThresholdAt 21 40 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 40 0 cell_21_40_0
  | exact S 21 40 1 cell_21_40_1
  | exact S 21 40 2 cell_21_40_2
  | exact S 21 40 3 cell_21_40_3
  | exact S 21 40 4 cell_21_40_4
  | exact S 21 40 5 cell_21_40_5
theorem cell_21_41_0 : C 21 41 0 := by decide +kernel
theorem cell_21_41_1 : C 21 41 1 := by decide +kernel
theorem cell_21_41_2 : C 21 41 2 := by decide +kernel
theorem cell_21_41_3 : C 21 41 3 := by decide +kernel
theorem cell_21_41_4 : C 21 41 4 := by decide +kernel
theorem cell_21_41_5 : C 21 41 5 := by decide +kernel
theorem row_21_41 : ThresholdAt 21 41 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 41 0 cell_21_41_0
  | exact S 21 41 1 cell_21_41_1
  | exact S 21 41 2 cell_21_41_2
  | exact S 21 41 3 cell_21_41_3
  | exact S 21 41 4 cell_21_41_4
  | exact S 21 41 5 cell_21_41_5
theorem cell_21_42_0 : C 21 42 0 := by decide +kernel
theorem cell_21_42_1 : C 21 42 1 := by decide +kernel
theorem cell_21_42_2 : C 21 42 2 := by decide +kernel
theorem cell_21_42_3 : C 21 42 3 := by decide +kernel
theorem cell_21_42_4 : C 21 42 4 := by decide +kernel
theorem cell_21_42_5 : C 21 42 5 := by decide +kernel
theorem row_21_42 : ThresholdAt 21 42 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 42 0 cell_21_42_0
  | exact S 21 42 1 cell_21_42_1
  | exact S 21 42 2 cell_21_42_2
  | exact S 21 42 3 cell_21_42_3
  | exact S 21 42 4 cell_21_42_4
  | exact S 21 42 5 cell_21_42_5
theorem cell_21_43_0 : C 21 43 0 := by decide +kernel
theorem cell_21_43_1 : C 21 43 1 := by decide +kernel
theorem cell_21_43_2 : C 21 43 2 := by decide +kernel
theorem cell_21_43_3 : C 21 43 3 := by decide +kernel
theorem cell_21_43_4 : C 21 43 4 := by decide +kernel
theorem cell_21_43_5 : C 21 43 5 := by decide +kernel
theorem row_21_43 : ThresholdAt 21 43 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 43 0 cell_21_43_0
  | exact S 21 43 1 cell_21_43_1
  | exact S 21 43 2 cell_21_43_2
  | exact S 21 43 3 cell_21_43_3
  | exact S 21 43 4 cell_21_43_4
  | exact S 21 43 5 cell_21_43_5
theorem cell_21_44_0 : C 21 44 0 := by decide +kernel
theorem cell_21_44_1 : C 21 44 1 := by decide +kernel
theorem cell_21_44_2 : C 21 44 2 := by decide +kernel
theorem cell_21_44_3 : C 21 44 3 := by decide +kernel
theorem cell_21_44_4 : C 21 44 4 := by decide +kernel
theorem cell_21_44_5 : C 21 44 5 := by decide +kernel
theorem row_21_44 : ThresholdAt 21 44 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 44 0 cell_21_44_0
  | exact S 21 44 1 cell_21_44_1
  | exact S 21 44 2 cell_21_44_2
  | exact S 21 44 3 cell_21_44_3
  | exact S 21 44 4 cell_21_44_4
  | exact S 21 44 5 cell_21_44_5
theorem cell_21_45_0 : C 21 45 0 := by decide +kernel
theorem cell_21_45_1 : C 21 45 1 := by decide +kernel
theorem cell_21_45_2 : C 21 45 2 := by decide +kernel
theorem cell_21_45_3 : C 21 45 3 := by decide +kernel
theorem cell_21_45_4 : C 21 45 4 := by decide +kernel
theorem cell_21_45_5 : C 21 45 5 := by decide +kernel
theorem row_21_45 : ThresholdAt 21 45 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 45 0 cell_21_45_0
  | exact S 21 45 1 cell_21_45_1
  | exact S 21 45 2 cell_21_45_2
  | exact S 21 45 3 cell_21_45_3
  | exact S 21 45 4 cell_21_45_4
  | exact S 21 45 5 cell_21_45_5
theorem cell_21_46_0 : C 21 46 0 := by decide +kernel
theorem cell_21_46_1 : C 21 46 1 := by decide +kernel
theorem cell_21_46_2 : C 21 46 2 := by decide +kernel
theorem cell_21_46_3 : C 21 46 3 := by decide +kernel
theorem cell_21_46_4 : C 21 46 4 := by decide +kernel
theorem cell_21_46_5 : C 21 46 5 := by decide +kernel
theorem row_21_46 : ThresholdAt 21 46 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 46 0 cell_21_46_0
  | exact S 21 46 1 cell_21_46_1
  | exact S 21 46 2 cell_21_46_2
  | exact S 21 46 3 cell_21_46_3
  | exact S 21 46 4 cell_21_46_4
  | exact S 21 46 5 cell_21_46_5
theorem cell_21_47_0 : C 21 47 0 := by decide +kernel
theorem cell_21_47_1 : C 21 47 1 := by decide +kernel
theorem cell_21_47_2 : C 21 47 2 := by decide +kernel
theorem cell_21_47_3 : C 21 47 3 := by decide +kernel
theorem cell_21_47_4 : C 21 47 4 := by decide +kernel
theorem cell_21_47_5 : C 21 47 5 := by decide +kernel
theorem row_21_47 : ThresholdAt 21 47 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 47 0 cell_21_47_0
  | exact S 21 47 1 cell_21_47_1
  | exact S 21 47 2 cell_21_47_2
  | exact S 21 47 3 cell_21_47_3
  | exact S 21 47 4 cell_21_47_4
  | exact S 21 47 5 cell_21_47_5
theorem cell_21_48_0 : C 21 48 0 := by decide +kernel
theorem cell_21_48_1 : C 21 48 1 := by decide +kernel
theorem cell_21_48_2 : C 21 48 2 := by decide +kernel
theorem cell_21_48_3 : C 21 48 3 := by decide +kernel
theorem cell_21_48_4 : C 21 48 4 := by decide +kernel
theorem cell_21_48_5 : C 21 48 5 := by decide +kernel
theorem row_21_48 : ThresholdAt 21 48 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 48 0 cell_21_48_0
  | exact S 21 48 1 cell_21_48_1
  | exact S 21 48 2 cell_21_48_2
  | exact S 21 48 3 cell_21_48_3
  | exact S 21 48 4 cell_21_48_4
  | exact S 21 48 5 cell_21_48_5
theorem cell_21_49_0 : C 21 49 0 := by decide +kernel
theorem cell_21_49_1 : C 21 49 1 := by decide +kernel
theorem cell_21_49_2 : C 21 49 2 := by decide +kernel
theorem cell_21_49_3 : C 21 49 3 := by decide +kernel
theorem cell_21_49_4 : C 21 49 4 := by decide +kernel
theorem cell_21_49_5 : C 21 49 5 := by decide +kernel
theorem row_21_49 : ThresholdAt 21 49 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 49 0 cell_21_49_0
  | exact S 21 49 1 cell_21_49_1
  | exact S 21 49 2 cell_21_49_2
  | exact S 21 49 3 cell_21_49_3
  | exact S 21 49 4 cell_21_49_4
  | exact S 21 49 5 cell_21_49_5
theorem cell_21_50_0 : C 21 50 0 := by decide +kernel
theorem cell_21_50_1 : C 21 50 1 := by decide +kernel
theorem cell_21_50_2 : C 21 50 2 := by decide +kernel
theorem cell_21_50_3 : C 21 50 3 := by decide +kernel
theorem cell_21_50_4 : C 21 50 4 := by decide +kernel
theorem cell_21_50_5 : C 21 50 5 := by decide +kernel
theorem row_21_50 : ThresholdAt 21 50 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 50 0 cell_21_50_0
  | exact S 21 50 1 cell_21_50_1
  | exact S 21 50 2 cell_21_50_2
  | exact S 21 50 3 cell_21_50_3
  | exact S 21 50 4 cell_21_50_4
  | exact S 21 50 5 cell_21_50_5
theorem cell_21_51_0 : C 21 51 0 := by decide +kernel
theorem cell_21_51_1 : C 21 51 1 := by decide +kernel
theorem cell_21_51_2 : C 21 51 2 := by decide +kernel
theorem cell_21_51_3 : C 21 51 3 := by decide +kernel
theorem cell_21_51_4 : C 21 51 4 := by decide +kernel
theorem cell_21_51_5 : C 21 51 5 := by decide +kernel
theorem row_21_51 : ThresholdAt 21 51 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 51 0 cell_21_51_0
  | exact S 21 51 1 cell_21_51_1
  | exact S 21 51 2 cell_21_51_2
  | exact S 21 51 3 cell_21_51_3
  | exact S 21 51 4 cell_21_51_4
  | exact S 21 51 5 cell_21_51_5
theorem cell_21_52_0 : C 21 52 0 := by decide +kernel
theorem cell_21_52_1 : C 21 52 1 := by decide +kernel
theorem cell_21_52_2 : C 21 52 2 := by decide +kernel
theorem cell_21_52_3 : C 21 52 3 := by decide +kernel
theorem cell_21_52_4 : C 21 52 4 := by decide +kernel
theorem cell_21_52_5 : C 21 52 5 := by decide +kernel
theorem row_21_52 : ThresholdAt 21 52 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 52 0 cell_21_52_0
  | exact S 21 52 1 cell_21_52_1
  | exact S 21 52 2 cell_21_52_2
  | exact S 21 52 3 cell_21_52_3
  | exact S 21 52 4 cell_21_52_4
  | exact S 21 52 5 cell_21_52_5
theorem cell_21_53_0 : C 21 53 0 := by decide +kernel
theorem cell_21_53_1 : C 21 53 1 := by decide +kernel
theorem cell_21_53_2 : C 21 53 2 := by decide +kernel
theorem cell_21_53_3 : C 21 53 3 := by decide +kernel
theorem cell_21_53_4 : C 21 53 4 := by decide +kernel
theorem cell_21_53_5 : C 21 53 5 := by decide +kernel
theorem row_21_53 : ThresholdAt 21 53 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 53 0 cell_21_53_0
  | exact S 21 53 1 cell_21_53_1
  | exact S 21 53 2 cell_21_53_2
  | exact S 21 53 3 cell_21_53_3
  | exact S 21 53 4 cell_21_53_4
  | exact S 21 53 5 cell_21_53_5
theorem cell_21_54_0 : C 21 54 0 := by decide +kernel
theorem cell_21_54_1 : C 21 54 1 := by decide +kernel
theorem cell_21_54_2 : C 21 54 2 := by decide +kernel
theorem cell_21_54_3 : C 21 54 3 := by decide +kernel
theorem cell_21_54_4 : C 21 54 4 := by decide +kernel
theorem cell_21_54_5 : C 21 54 5 := by decide +kernel
theorem row_21_54 : ThresholdAt 21 54 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 54 0 cell_21_54_0
  | exact S 21 54 1 cell_21_54_1
  | exact S 21 54 2 cell_21_54_2
  | exact S 21 54 3 cell_21_54_3
  | exact S 21 54 4 cell_21_54_4
  | exact S 21 54 5 cell_21_54_5
theorem cell_21_55_0 : C 21 55 0 := by decide +kernel
theorem cell_21_55_1 : C 21 55 1 := by decide +kernel
theorem cell_21_55_2 : C 21 55 2 := by decide +kernel
theorem cell_21_55_3 : C 21 55 3 := by decide +kernel
theorem cell_21_55_4 : C 21 55 4 := by decide +kernel
theorem cell_21_55_5 : C 21 55 5 := by decide +kernel
theorem row_21_55 : ThresholdAt 21 55 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 55 0 cell_21_55_0
  | exact S 21 55 1 cell_21_55_1
  | exact S 21 55 2 cell_21_55_2
  | exact S 21 55 3 cell_21_55_3
  | exact S 21 55 4 cell_21_55_4
  | exact S 21 55 5 cell_21_55_5
theorem cell_21_56_0 : C 21 56 0 := by decide +kernel
theorem cell_21_56_1 : C 21 56 1 := by decide +kernel
theorem cell_21_56_2 : C 21 56 2 := by decide +kernel
theorem cell_21_56_3 : C 21 56 3 := by decide +kernel
theorem cell_21_56_4 : C 21 56 4 := by decide +kernel
theorem cell_21_56_5 : C 21 56 5 := by decide +kernel
theorem row_21_56 : ThresholdAt 21 56 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 56 0 cell_21_56_0
  | exact S 21 56 1 cell_21_56_1
  | exact S 21 56 2 cell_21_56_2
  | exact S 21 56 3 cell_21_56_3
  | exact S 21 56 4 cell_21_56_4
  | exact S 21 56 5 cell_21_56_5
theorem cell_21_57_0 : C 21 57 0 := by decide +kernel
theorem cell_21_57_1 : C 21 57 1 := by decide +kernel
theorem cell_21_57_2 : C 21 57 2 := by decide +kernel
theorem cell_21_57_3 : C 21 57 3 := by decide +kernel
theorem cell_21_57_4 : C 21 57 4 := by decide +kernel
theorem cell_21_57_5 : C 21 57 5 := by decide +kernel
theorem row_21_57 : ThresholdAt 21 57 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 57 0 cell_21_57_0
  | exact S 21 57 1 cell_21_57_1
  | exact S 21 57 2 cell_21_57_2
  | exact S 21 57 3 cell_21_57_3
  | exact S 21 57 4 cell_21_57_4
  | exact S 21 57 5 cell_21_57_5
theorem cell_21_58_0 : C 21 58 0 := by decide +kernel
theorem cell_21_58_1 : C 21 58 1 := by decide +kernel
theorem cell_21_58_2 : C 21 58 2 := by decide +kernel
theorem cell_21_58_3 : C 21 58 3 := by decide +kernel
theorem cell_21_58_4 : C 21 58 4 := by decide +kernel
theorem cell_21_58_5 : C 21 58 5 := by decide +kernel
theorem row_21_58 : ThresholdAt 21 58 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 58 0 cell_21_58_0
  | exact S 21 58 1 cell_21_58_1
  | exact S 21 58 2 cell_21_58_2
  | exact S 21 58 3 cell_21_58_3
  | exact S 21 58 4 cell_21_58_4
  | exact S 21 58 5 cell_21_58_5
theorem cell_21_59_0 : C 21 59 0 := by decide +kernel
theorem cell_21_59_1 : C 21 59 1 := by decide +kernel
theorem cell_21_59_2 : C 21 59 2 := by decide +kernel
theorem cell_21_59_3 : C 21 59 3 := by decide +kernel
theorem cell_21_59_4 : C 21 59 4 := by decide +kernel
theorem cell_21_59_5 : C 21 59 5 := by decide +kernel
theorem row_21_59 : ThresholdAt 21 59 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 59 0 cell_21_59_0
  | exact S 21 59 1 cell_21_59_1
  | exact S 21 59 2 cell_21_59_2
  | exact S 21 59 3 cell_21_59_3
  | exact S 21 59 4 cell_21_59_4
  | exact S 21 59 5 cell_21_59_5
theorem cell_21_60_0 : C 21 60 0 := by decide +kernel
theorem cell_21_60_1 : C 21 60 1 := by decide +kernel
theorem cell_21_60_2 : C 21 60 2 := by decide +kernel
theorem cell_21_60_3 : C 21 60 3 := by decide +kernel
theorem cell_21_60_4 : C 21 60 4 := by decide +kernel
theorem cell_21_60_5 : C 21 60 5 := by decide +kernel
theorem row_21_60 : ThresholdAt 21 60 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 60 0 cell_21_60_0
  | exact S 21 60 1 cell_21_60_1
  | exact S 21 60 2 cell_21_60_2
  | exact S 21 60 3 cell_21_60_3
  | exact S 21 60 4 cell_21_60_4
  | exact S 21 60 5 cell_21_60_5
theorem cell_21_61_0 : C 21 61 0 := by decide +kernel
theorem cell_21_61_1 : C 21 61 1 := by decide +kernel
theorem cell_21_61_2 : C 21 61 2 := by decide +kernel
theorem cell_21_61_3 : C 21 61 3 := by decide +kernel
theorem cell_21_61_4 : C 21 61 4 := by decide +kernel
theorem cell_21_61_5 : C 21 61 5 := by decide +kernel
theorem row_21_61 : ThresholdAt 21 61 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 61 0 cell_21_61_0
  | exact S 21 61 1 cell_21_61_1
  | exact S 21 61 2 cell_21_61_2
  | exact S 21 61 3 cell_21_61_3
  | exact S 21 61 4 cell_21_61_4
  | exact S 21 61 5 cell_21_61_5
theorem cell_21_62_0 : C 21 62 0 := by decide +kernel
theorem cell_21_62_1 : C 21 62 1 := by decide +kernel
theorem cell_21_62_2 : C 21 62 2 := by decide +kernel
theorem cell_21_62_3 : C 21 62 3 := by decide +kernel
theorem cell_21_62_4 : C 21 62 4 := by decide +kernel
theorem cell_21_62_5 : C 21 62 5 := by decide +kernel
theorem row_21_62 : ThresholdAt 21 62 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 62 0 cell_21_62_0
  | exact S 21 62 1 cell_21_62_1
  | exact S 21 62 2 cell_21_62_2
  | exact S 21 62 3 cell_21_62_3
  | exact S 21 62 4 cell_21_62_4
  | exact S 21 62 5 cell_21_62_5
theorem cell_21_63_0 : C 21 63 0 := by decide +kernel
theorem cell_21_63_1 : C 21 63 1 := by decide +kernel
theorem cell_21_63_2 : C 21 63 2 := by decide +kernel
theorem cell_21_63_3 : C 21 63 3 := by decide +kernel
theorem cell_21_63_4 : C 21 63 4 := by decide +kernel
theorem cell_21_63_5 : C 21 63 5 := by decide +kernel
theorem row_21_63 : ThresholdAt 21 63 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 63 0 cell_21_63_0
  | exact S 21 63 1 cell_21_63_1
  | exact S 21 63 2 cell_21_63_2
  | exact S 21 63 3 cell_21_63_3
  | exact S 21 63 4 cell_21_63_4
  | exact S 21 63 5 cell_21_63_5
theorem cell_21_64_0 : C 21 64 0 := by decide +kernel
theorem cell_21_64_1 : C 21 64 1 := by decide +kernel
theorem cell_21_64_2 : C 21 64 2 := by decide +kernel
theorem cell_21_64_3 : C 21 64 3 := by decide +kernel
theorem cell_21_64_4 : C 21 64 4 := by decide +kernel
theorem cell_21_64_5 : C 21 64 5 := by decide +kernel
theorem row_21_64 : ThresholdAt 21 64 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 64 0 cell_21_64_0
  | exact S 21 64 1 cell_21_64_1
  | exact S 21 64 2 cell_21_64_2
  | exact S 21 64 3 cell_21_64_3
  | exact S 21 64 4 cell_21_64_4
  | exact S 21 64 5 cell_21_64_5
theorem cell_21_65_0 : C 21 65 0 := by decide +kernel
theorem cell_21_65_1 : C 21 65 1 := by decide +kernel
theorem cell_21_65_2 : C 21 65 2 := by decide +kernel
theorem cell_21_65_3 : C 21 65 3 := by decide +kernel
theorem cell_21_65_4 : C 21 65 4 := by decide +kernel
theorem cell_21_65_5 : C 21 65 5 := by decide +kernel
theorem row_21_65 : ThresholdAt 21 65 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 65 0 cell_21_65_0
  | exact S 21 65 1 cell_21_65_1
  | exact S 21 65 2 cell_21_65_2
  | exact S 21 65 3 cell_21_65_3
  | exact S 21 65 4 cell_21_65_4
  | exact S 21 65 5 cell_21_65_5
theorem cell_21_66_0 : C 21 66 0 := by decide +kernel
theorem cell_21_66_1 : C 21 66 1 := by decide +kernel
theorem cell_21_66_2 : C 21 66 2 := by decide +kernel
theorem cell_21_66_3 : C 21 66 3 := by decide +kernel
theorem cell_21_66_4 : C 21 66 4 := by decide +kernel
theorem cell_21_66_5 : C 21 66 5 := by decide +kernel
theorem row_21_66 : ThresholdAt 21 66 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 66 0 cell_21_66_0
  | exact S 21 66 1 cell_21_66_1
  | exact S 21 66 2 cell_21_66_2
  | exact S 21 66 3 cell_21_66_3
  | exact S 21 66 4 cell_21_66_4
  | exact S 21 66 5 cell_21_66_5
theorem cell_21_67_0 : C 21 67 0 := by decide +kernel
theorem cell_21_67_1 : C 21 67 1 := by decide +kernel
theorem cell_21_67_2 : C 21 67 2 := by decide +kernel
theorem cell_21_67_3 : C 21 67 3 := by decide +kernel
theorem cell_21_67_4 : C 21 67 4 := by decide +kernel
theorem cell_21_67_5 : C 21 67 5 := by decide +kernel
theorem row_21_67 : ThresholdAt 21 67 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 67 0 cell_21_67_0
  | exact S 21 67 1 cell_21_67_1
  | exact S 21 67 2 cell_21_67_2
  | exact S 21 67 3 cell_21_67_3
  | exact S 21 67 4 cell_21_67_4
  | exact S 21 67 5 cell_21_67_5
theorem cell_21_68_0 : C 21 68 0 := by decide +kernel
theorem cell_21_68_1 : C 21 68 1 := by decide +kernel
theorem cell_21_68_2 : C 21 68 2 := by decide +kernel
theorem cell_21_68_3 : C 21 68 3 := by decide +kernel
theorem cell_21_68_4 : C 21 68 4 := by decide +kernel
theorem cell_21_68_5 : C 21 68 5 := by decide +kernel
theorem row_21_68 : ThresholdAt 21 68 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 68 0 cell_21_68_0
  | exact S 21 68 1 cell_21_68_1
  | exact S 21 68 2 cell_21_68_2
  | exact S 21 68 3 cell_21_68_3
  | exact S 21 68 4 cell_21_68_4
  | exact S 21 68 5 cell_21_68_5
theorem cell_21_69_0 : C 21 69 0 := by decide +kernel
theorem cell_21_69_1 : C 21 69 1 := by decide +kernel
theorem cell_21_69_2 : C 21 69 2 := by decide +kernel
theorem cell_21_69_3 : C 21 69 3 := by decide +kernel
theorem cell_21_69_4 : C 21 69 4 := by decide +kernel
theorem cell_21_69_5 : C 21 69 5 := by decide +kernel
theorem row_21_69 : ThresholdAt 21 69 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 69 0 cell_21_69_0
  | exact S 21 69 1 cell_21_69_1
  | exact S 21 69 2 cell_21_69_2
  | exact S 21 69 3 cell_21_69_3
  | exact S 21 69 4 cell_21_69_4
  | exact S 21 69 5 cell_21_69_5
theorem cell_21_70_0 : C 21 70 0 := by decide +kernel
theorem cell_21_70_1 : C 21 70 1 := by decide +kernel
theorem cell_21_70_2 : C 21 70 2 := by decide +kernel
theorem cell_21_70_3 : C 21 70 3 := by decide +kernel
theorem cell_21_70_4 : C 21 70 4 := by decide +kernel
theorem cell_21_70_5 : C 21 70 5 := by decide +kernel
theorem row_21_70 : ThresholdAt 21 70 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 70 0 cell_21_70_0
  | exact S 21 70 1 cell_21_70_1
  | exact S 21 70 2 cell_21_70_2
  | exact S 21 70 3 cell_21_70_3
  | exact S 21 70 4 cell_21_70_4
  | exact S 21 70 5 cell_21_70_5
theorem cell_21_71_0 : C 21 71 0 := by decide +kernel
theorem cell_21_71_1 : C 21 71 1 := by decide +kernel
theorem cell_21_71_2 : C 21 71 2 := by decide +kernel
theorem cell_21_71_3 : C 21 71 3 := by decide +kernel
theorem cell_21_71_4 : C 21 71 4 := by decide +kernel
theorem cell_21_71_5 : C 21 71 5 := by decide +kernel
theorem row_21_71 : ThresholdAt 21 71 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 71 0 cell_21_71_0
  | exact S 21 71 1 cell_21_71_1
  | exact S 21 71 2 cell_21_71_2
  | exact S 21 71 3 cell_21_71_3
  | exact S 21 71 4 cell_21_71_4
  | exact S 21 71 5 cell_21_71_5
theorem cell_21_72_0 : C 21 72 0 := by decide +kernel
theorem cell_21_72_1 : C 21 72 1 := by decide +kernel
theorem cell_21_72_2 : C 21 72 2 := by decide +kernel
theorem cell_21_72_3 : C 21 72 3 := by decide +kernel
theorem cell_21_72_4 : C 21 72 4 := by decide +kernel
theorem cell_21_72_5 : C 21 72 5 := by decide +kernel
theorem row_21_72 : ThresholdAt 21 72 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 72 0 cell_21_72_0
  | exact S 21 72 1 cell_21_72_1
  | exact S 21 72 2 cell_21_72_2
  | exact S 21 72 3 cell_21_72_3
  | exact S 21 72 4 cell_21_72_4
  | exact S 21 72 5 cell_21_72_5
theorem cell_21_73_0 : C 21 73 0 := by decide +kernel
theorem cell_21_73_1 : C 21 73 1 := by decide +kernel
theorem cell_21_73_2 : C 21 73 2 := by decide +kernel
theorem cell_21_73_3 : C 21 73 3 := by decide +kernel
theorem cell_21_73_4 : C 21 73 4 := by decide +kernel
theorem cell_21_73_5 : C 21 73 5 := by decide +kernel
theorem row_21_73 : ThresholdAt 21 73 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 73 0 cell_21_73_0
  | exact S 21 73 1 cell_21_73_1
  | exact S 21 73 2 cell_21_73_2
  | exact S 21 73 3 cell_21_73_3
  | exact S 21 73 4 cell_21_73_4
  | exact S 21 73 5 cell_21_73_5
theorem cell_21_74_0 : C 21 74 0 := by decide +kernel
theorem cell_21_74_1 : C 21 74 1 := by decide +kernel
theorem cell_21_74_2 : C 21 74 2 := by decide +kernel
theorem cell_21_74_3 : C 21 74 3 := by decide +kernel
theorem cell_21_74_4 : C 21 74 4 := by decide +kernel
theorem cell_21_74_5 : C 21 74 5 := by decide +kernel
theorem row_21_74 : ThresholdAt 21 74 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 74 0 cell_21_74_0
  | exact S 21 74 1 cell_21_74_1
  | exact S 21 74 2 cell_21_74_2
  | exact S 21 74 3 cell_21_74_3
  | exact S 21 74 4 cell_21_74_4
  | exact S 21 74 5 cell_21_74_5
theorem cell_21_75_0 : C 21 75 0 := by decide +kernel
theorem cell_21_75_1 : C 21 75 1 := by decide +kernel
theorem cell_21_75_2 : C 21 75 2 := by decide +kernel
theorem cell_21_75_3 : C 21 75 3 := by decide +kernel
theorem cell_21_75_4 : C 21 75 4 := by decide +kernel
theorem cell_21_75_5 : C 21 75 5 := by decide +kernel
theorem row_21_75 : ThresholdAt 21 75 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 75 0 cell_21_75_0
  | exact S 21 75 1 cell_21_75_1
  | exact S 21 75 2 cell_21_75_2
  | exact S 21 75 3 cell_21_75_3
  | exact S 21 75 4 cell_21_75_4
  | exact S 21 75 5 cell_21_75_5
theorem cell_21_76_0 : C 21 76 0 := by decide +kernel
theorem cell_21_76_1 : C 21 76 1 := by decide +kernel
theorem cell_21_76_2 : C 21 76 2 := by decide +kernel
theorem cell_21_76_3 : C 21 76 3 := by decide +kernel
theorem cell_21_76_4 : C 21 76 4 := by decide +kernel
theorem cell_21_76_5 : C 21 76 5 := by decide +kernel
theorem row_21_76 : ThresholdAt 21 76 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 76 0 cell_21_76_0
  | exact S 21 76 1 cell_21_76_1
  | exact S 21 76 2 cell_21_76_2
  | exact S 21 76 3 cell_21_76_3
  | exact S 21 76 4 cell_21_76_4
  | exact S 21 76 5 cell_21_76_5
theorem cell_21_77_0 : C 21 77 0 := by decide +kernel
theorem cell_21_77_1 : C 21 77 1 := by decide +kernel
theorem cell_21_77_2 : C 21 77 2 := by decide +kernel
theorem cell_21_77_3 : C 21 77 3 := by decide +kernel
theorem cell_21_77_4 : C 21 77 4 := by decide +kernel
theorem cell_21_77_5 : C 21 77 5 := by decide +kernel
theorem row_21_77 : ThresholdAt 21 77 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 77 0 cell_21_77_0
  | exact S 21 77 1 cell_21_77_1
  | exact S 21 77 2 cell_21_77_2
  | exact S 21 77 3 cell_21_77_3
  | exact S 21 77 4 cell_21_77_4
  | exact S 21 77 5 cell_21_77_5
theorem cell_21_78_0 : C 21 78 0 := by decide +kernel
theorem cell_21_78_1 : C 21 78 1 := by decide +kernel
theorem cell_21_78_2 : C 21 78 2 := by decide +kernel
theorem cell_21_78_3 : C 21 78 3 := by decide +kernel
theorem cell_21_78_4 : C 21 78 4 := by decide +kernel
theorem cell_21_78_5 : C 21 78 5 := by decide +kernel
theorem row_21_78 : ThresholdAt 21 78 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 78 0 cell_21_78_0
  | exact S 21 78 1 cell_21_78_1
  | exact S 21 78 2 cell_21_78_2
  | exact S 21 78 3 cell_21_78_3
  | exact S 21 78 4 cell_21_78_4
  | exact S 21 78 5 cell_21_78_5
theorem cell_21_79_0 : C 21 79 0 := by decide +kernel
theorem cell_21_79_1 : C 21 79 1 := by decide +kernel
theorem cell_21_79_2 : C 21 79 2 := by decide +kernel
theorem cell_21_79_3 : C 21 79 3 := by decide +kernel
theorem cell_21_79_4 : C 21 79 4 := by decide +kernel
theorem cell_21_79_5 : C 21 79 5 := by decide +kernel
theorem row_21_79 : ThresholdAt 21 79 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 79 0 cell_21_79_0
  | exact S 21 79 1 cell_21_79_1
  | exact S 21 79 2 cell_21_79_2
  | exact S 21 79 3 cell_21_79_3
  | exact S 21 79 4 cell_21_79_4
  | exact S 21 79 5 cell_21_79_5
theorem cell_21_80_0 : C 21 80 0 := by decide +kernel
theorem cell_21_80_1 : C 21 80 1 := by decide +kernel
theorem cell_21_80_2 : C 21 80 2 := by decide +kernel
theorem cell_21_80_3 : C 21 80 3 := by decide +kernel
theorem cell_21_80_4 : C 21 80 4 := by decide +kernel
theorem cell_21_80_5 : C 21 80 5 := by decide +kernel
theorem row_21_80 : ThresholdAt 21 80 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 80 0 cell_21_80_0
  | exact S 21 80 1 cell_21_80_1
  | exact S 21 80 2 cell_21_80_2
  | exact S 21 80 3 cell_21_80_3
  | exact S 21 80 4 cell_21_80_4
  | exact S 21 80 5 cell_21_80_5
theorem cell_21_81_0 : C 21 81 0 := by decide +kernel
theorem cell_21_81_1 : C 21 81 1 := by decide +kernel
theorem cell_21_81_2 : C 21 81 2 := by decide +kernel
theorem cell_21_81_3 : C 21 81 3 := by decide +kernel
theorem cell_21_81_4 : C 21 81 4 := by decide +kernel
theorem cell_21_81_5 : C 21 81 5 := by decide +kernel
theorem row_21_81 : ThresholdAt 21 81 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 81 0 cell_21_81_0
  | exact S 21 81 1 cell_21_81_1
  | exact S 21 81 2 cell_21_81_2
  | exact S 21 81 3 cell_21_81_3
  | exact S 21 81 4 cell_21_81_4
  | exact S 21 81 5 cell_21_81_5
theorem cell_21_82_0 : C 21 82 0 := by decide +kernel
theorem cell_21_82_1 : C 21 82 1 := by decide +kernel
theorem cell_21_82_2 : C 21 82 2 := by decide +kernel
theorem cell_21_82_3 : C 21 82 3 := by decide +kernel
theorem cell_21_82_4 : C 21 82 4 := by decide +kernel
theorem cell_21_82_5 : C 21 82 5 := by decide +kernel
theorem row_21_82 : ThresholdAt 21 82 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 82 0 cell_21_82_0
  | exact S 21 82 1 cell_21_82_1
  | exact S 21 82 2 cell_21_82_2
  | exact S 21 82 3 cell_21_82_3
  | exact S 21 82 4 cell_21_82_4
  | exact S 21 82 5 cell_21_82_5
theorem cell_21_83_0 : C 21 83 0 := by decide +kernel
theorem cell_21_83_1 : C 21 83 1 := by decide +kernel
theorem cell_21_83_2 : C 21 83 2 := by decide +kernel
theorem cell_21_83_3 : C 21 83 3 := by decide +kernel
theorem cell_21_83_4 : C 21 83 4 := by decide +kernel
theorem cell_21_83_5 : C 21 83 5 := by decide +kernel
theorem row_21_83 : ThresholdAt 21 83 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 83 0 cell_21_83_0
  | exact S 21 83 1 cell_21_83_1
  | exact S 21 83 2 cell_21_83_2
  | exact S 21 83 3 cell_21_83_3
  | exact S 21 83 4 cell_21_83_4
  | exact S 21 83 5 cell_21_83_5
theorem cell_21_84_0 : C 21 84 0 := by decide +kernel
theorem cell_21_84_1 : C 21 84 1 := by decide +kernel
theorem cell_21_84_2 : C 21 84 2 := by decide +kernel
theorem cell_21_84_3 : C 21 84 3 := by decide +kernel
theorem cell_21_84_4 : C 21 84 4 := by decide +kernel
theorem cell_21_84_5 : C 21 84 5 := by decide +kernel
theorem row_21_84 : ThresholdAt 21 84 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 84 0 cell_21_84_0
  | exact S 21 84 1 cell_21_84_1
  | exact S 21 84 2 cell_21_84_2
  | exact S 21 84 3 cell_21_84_3
  | exact S 21 84 4 cell_21_84_4
  | exact S 21 84 5 cell_21_84_5
theorem cell_21_85_0 : C 21 85 0 := by decide +kernel
theorem cell_21_85_1 : C 21 85 1 := by decide +kernel
theorem cell_21_85_2 : C 21 85 2 := by decide +kernel
theorem cell_21_85_3 : C 21 85 3 := by decide +kernel
theorem cell_21_85_4 : C 21 85 4 := by decide +kernel
theorem cell_21_85_5 : C 21 85 5 := by decide +kernel
theorem row_21_85 : ThresholdAt 21 85 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 85 0 cell_21_85_0
  | exact S 21 85 1 cell_21_85_1
  | exact S 21 85 2 cell_21_85_2
  | exact S 21 85 3 cell_21_85_3
  | exact S 21 85 4 cell_21_85_4
  | exact S 21 85 5 cell_21_85_5
theorem cell_21_86_0 : C 21 86 0 := by decide +kernel
theorem cell_21_86_1 : C 21 86 1 := by decide +kernel
theorem cell_21_86_2 : C 21 86 2 := by decide +kernel
theorem cell_21_86_3 : C 21 86 3 := by decide +kernel
theorem cell_21_86_4 : C 21 86 4 := by decide +kernel
theorem cell_21_86_5 : C 21 86 5 := by decide +kernel
theorem row_21_86 : ThresholdAt 21 86 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 86 0 cell_21_86_0
  | exact S 21 86 1 cell_21_86_1
  | exact S 21 86 2 cell_21_86_2
  | exact S 21 86 3 cell_21_86_3
  | exact S 21 86 4 cell_21_86_4
  | exact S 21 86 5 cell_21_86_5
theorem cell_21_87_0 : C 21 87 0 := by decide +kernel
theorem cell_21_87_1 : C 21 87 1 := by decide +kernel
theorem cell_21_87_2 : C 21 87 2 := by decide +kernel
theorem cell_21_87_3 : C 21 87 3 := by decide +kernel
theorem cell_21_87_4 : C 21 87 4 := by decide +kernel
theorem cell_21_87_5 : C 21 87 5 := by decide +kernel
theorem row_21_87 : ThresholdAt 21 87 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 87 0 cell_21_87_0
  | exact S 21 87 1 cell_21_87_1
  | exact S 21 87 2 cell_21_87_2
  | exact S 21 87 3 cell_21_87_3
  | exact S 21 87 4 cell_21_87_4
  | exact S 21 87 5 cell_21_87_5
theorem cell_21_88_0 : C 21 88 0 := by decide +kernel
theorem cell_21_88_1 : C 21 88 1 := by decide +kernel
theorem cell_21_88_2 : C 21 88 2 := by decide +kernel
theorem cell_21_88_3 : C 21 88 3 := by decide +kernel
theorem cell_21_88_4 : C 21 88 4 := by decide +kernel
theorem cell_21_88_5 : C 21 88 5 := by decide +kernel
theorem row_21_88 : ThresholdAt 21 88 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 88 0 cell_21_88_0
  | exact S 21 88 1 cell_21_88_1
  | exact S 21 88 2 cell_21_88_2
  | exact S 21 88 3 cell_21_88_3
  | exact S 21 88 4 cell_21_88_4
  | exact S 21 88 5 cell_21_88_5
theorem cell_21_89_0 : C 21 89 0 := by decide +kernel
theorem cell_21_89_1 : C 21 89 1 := by decide +kernel
theorem cell_21_89_2 : C 21 89 2 := by decide +kernel
theorem cell_21_89_3 : C 21 89 3 := by decide +kernel
theorem cell_21_89_4 : C 21 89 4 := by decide +kernel
theorem cell_21_89_5 : C 21 89 5 := by decide +kernel
theorem row_21_89 : ThresholdAt 21 89 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 89 0 cell_21_89_0
  | exact S 21 89 1 cell_21_89_1
  | exact S 21 89 2 cell_21_89_2
  | exact S 21 89 3 cell_21_89_3
  | exact S 21 89 4 cell_21_89_4
  | exact S 21 89 5 cell_21_89_5
theorem cell_21_90_0 : C 21 90 0 := by decide +kernel
theorem cell_21_90_1 : C 21 90 1 := by decide +kernel
theorem cell_21_90_2 : C 21 90 2 := by decide +kernel
theorem cell_21_90_3 : C 21 90 3 := by decide +kernel
theorem cell_21_90_4 : C 21 90 4 := by decide +kernel
theorem cell_21_90_5 : C 21 90 5 := by decide +kernel
theorem row_21_90 : ThresholdAt 21 90 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 90 0 cell_21_90_0
  | exact S 21 90 1 cell_21_90_1
  | exact S 21 90 2 cell_21_90_2
  | exact S 21 90 3 cell_21_90_3
  | exact S 21 90 4 cell_21_90_4
  | exact S 21 90 5 cell_21_90_5
theorem cell_21_91_0 : C 21 91 0 := by decide +kernel
theorem cell_21_91_1 : C 21 91 1 := by decide +kernel
theorem cell_21_91_2 : C 21 91 2 := by decide +kernel
theorem cell_21_91_3 : C 21 91 3 := by decide +kernel
theorem cell_21_91_4 : C 21 91 4 := by decide +kernel
theorem cell_21_91_5 : C 21 91 5 := by decide +kernel
theorem row_21_91 : ThresholdAt 21 91 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 91 0 cell_21_91_0
  | exact S 21 91 1 cell_21_91_1
  | exact S 21 91 2 cell_21_91_2
  | exact S 21 91 3 cell_21_91_3
  | exact S 21 91 4 cell_21_91_4
  | exact S 21 91 5 cell_21_91_5
theorem cell_21_92_0 : C 21 92 0 := by decide +kernel
theorem cell_21_92_1 : C 21 92 1 := by decide +kernel
theorem cell_21_92_2 : C 21 92 2 := by decide +kernel
theorem cell_21_92_3 : C 21 92 3 := by decide +kernel
theorem cell_21_92_4 : C 21 92 4 := by decide +kernel
theorem cell_21_92_5 : C 21 92 5 := by decide +kernel
theorem row_21_92 : ThresholdAt 21 92 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 92 0 cell_21_92_0
  | exact S 21 92 1 cell_21_92_1
  | exact S 21 92 2 cell_21_92_2
  | exact S 21 92 3 cell_21_92_3
  | exact S 21 92 4 cell_21_92_4
  | exact S 21 92 5 cell_21_92_5
theorem cell_21_93_0 : C 21 93 0 := by decide +kernel
theorem cell_21_93_1 : C 21 93 1 := by decide +kernel
theorem cell_21_93_2 : C 21 93 2 := by decide +kernel
theorem cell_21_93_3 : C 21 93 3 := by decide +kernel
theorem cell_21_93_4 : C 21 93 4 := by decide +kernel
theorem cell_21_93_5 : C 21 93 5 := by decide +kernel
theorem row_21_93 : ThresholdAt 21 93 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 93 0 cell_21_93_0
  | exact S 21 93 1 cell_21_93_1
  | exact S 21 93 2 cell_21_93_2
  | exact S 21 93 3 cell_21_93_3
  | exact S 21 93 4 cell_21_93_4
  | exact S 21 93 5 cell_21_93_5
theorem cell_21_94_0 : C 21 94 0 := by decide +kernel
theorem cell_21_94_1 : C 21 94 1 := by decide +kernel
theorem cell_21_94_2 : C 21 94 2 := by decide +kernel
theorem cell_21_94_3 : C 21 94 3 := by decide +kernel
theorem cell_21_94_4 : C 21 94 4 := by decide +kernel
theorem cell_21_94_5 : C 21 94 5 := by decide +kernel
theorem row_21_94 : ThresholdAt 21 94 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 94 0 cell_21_94_0
  | exact S 21 94 1 cell_21_94_1
  | exact S 21 94 2 cell_21_94_2
  | exact S 21 94 3 cell_21_94_3
  | exact S 21 94 4 cell_21_94_4
  | exact S 21 94 5 cell_21_94_5
theorem cell_21_95_0 : C 21 95 0 := by decide +kernel
theorem cell_21_95_1 : C 21 95 1 := by decide +kernel
theorem cell_21_95_2 : C 21 95 2 := by decide +kernel
theorem cell_21_95_3 : C 21 95 3 := by decide +kernel
theorem cell_21_95_4 : C 21 95 4 := by decide +kernel
theorem cell_21_95_5 : C 21 95 5 := by decide +kernel
theorem row_21_95 : ThresholdAt 21 95 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 95 0 cell_21_95_0
  | exact S 21 95 1 cell_21_95_1
  | exact S 21 95 2 cell_21_95_2
  | exact S 21 95 3 cell_21_95_3
  | exact S 21 95 4 cell_21_95_4
  | exact S 21 95 5 cell_21_95_5
theorem cell_21_96_0 : C 21 96 0 := by decide +kernel
theorem cell_21_96_1 : C 21 96 1 := by decide +kernel
theorem cell_21_96_2 : C 21 96 2 := by decide +kernel
theorem cell_21_96_3 : C 21 96 3 := by decide +kernel
theorem cell_21_96_4 : C 21 96 4 := by decide +kernel
theorem cell_21_96_5 : C 21 96 5 := by decide +kernel
theorem row_21_96 : ThresholdAt 21 96 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 96 0 cell_21_96_0
  | exact S 21 96 1 cell_21_96_1
  | exact S 21 96 2 cell_21_96_2
  | exact S 21 96 3 cell_21_96_3
  | exact S 21 96 4 cell_21_96_4
  | exact S 21 96 5 cell_21_96_5
theorem cell_21_97_0 : C 21 97 0 := by decide +kernel
theorem cell_21_97_1 : C 21 97 1 := by decide +kernel
theorem cell_21_97_2 : C 21 97 2 := by decide +kernel
theorem cell_21_97_3 : C 21 97 3 := by decide +kernel
theorem cell_21_97_4 : C 21 97 4 := by decide +kernel
theorem cell_21_97_5 : C 21 97 5 := by decide +kernel
theorem row_21_97 : ThresholdAt 21 97 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 97 0 cell_21_97_0
  | exact S 21 97 1 cell_21_97_1
  | exact S 21 97 2 cell_21_97_2
  | exact S 21 97 3 cell_21_97_3
  | exact S 21 97 4 cell_21_97_4
  | exact S 21 97 5 cell_21_97_5
theorem cell_21_98_0 : C 21 98 0 := by decide +kernel
theorem cell_21_98_1 : C 21 98 1 := by decide +kernel
theorem cell_21_98_2 : C 21 98 2 := by decide +kernel
theorem cell_21_98_3 : C 21 98 3 := by decide +kernel
theorem cell_21_98_4 : C 21 98 4 := by decide +kernel
theorem cell_21_98_5 : C 21 98 5 := by decide +kernel
theorem row_21_98 : ThresholdAt 21 98 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 98 0 cell_21_98_0
  | exact S 21 98 1 cell_21_98_1
  | exact S 21 98 2 cell_21_98_2
  | exact S 21 98 3 cell_21_98_3
  | exact S 21 98 4 cell_21_98_4
  | exact S 21 98 5 cell_21_98_5
theorem cell_21_99_0 : C 21 99 0 := by decide +kernel
theorem cell_21_99_1 : C 21 99 1 := by decide +kernel
theorem cell_21_99_2 : C 21 99 2 := by decide +kernel
theorem cell_21_99_3 : C 21 99 3 := by decide +kernel
theorem cell_21_99_4 : C 21 99 4 := by decide +kernel
theorem cell_21_99_5 : C 21 99 5 := by decide +kernel
theorem row_21_99 : ThresholdAt 21 99 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 99 0 cell_21_99_0
  | exact S 21 99 1 cell_21_99_1
  | exact S 21 99 2 cell_21_99_2
  | exact S 21 99 3 cell_21_99_3
  | exact S 21 99 4 cell_21_99_4
  | exact S 21 99 5 cell_21_99_5
theorem cell_21_100_0 : C 21 100 0 := by decide +kernel
theorem cell_21_100_1 : C 21 100 1 := by decide +kernel
theorem cell_21_100_2 : C 21 100 2 := by decide +kernel
theorem cell_21_100_3 : C 21 100 3 := by decide +kernel
theorem cell_21_100_4 : C 21 100 4 := by decide +kernel
theorem cell_21_100_5 : C 21 100 5 := by decide +kernel
theorem row_21_100 : ThresholdAt 21 100 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 100 0 cell_21_100_0
  | exact S 21 100 1 cell_21_100_1
  | exact S 21 100 2 cell_21_100_2
  | exact S 21 100 3 cell_21_100_3
  | exact S 21 100 4 cell_21_100_4
  | exact S 21 100 5 cell_21_100_5
theorem cell_21_101_0 : C 21 101 0 := by decide +kernel
theorem cell_21_101_1 : C 21 101 1 := by decide +kernel
theorem cell_21_101_2 : C 21 101 2 := by decide +kernel
theorem cell_21_101_3 : C 21 101 3 := by decide +kernel
theorem cell_21_101_4 : C 21 101 4 := by decide +kernel
theorem cell_21_101_5 : C 21 101 5 := by decide +kernel
theorem row_21_101 : ThresholdAt 21 101 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 101 0 cell_21_101_0
  | exact S 21 101 1 cell_21_101_1
  | exact S 21 101 2 cell_21_101_2
  | exact S 21 101 3 cell_21_101_3
  | exact S 21 101 4 cell_21_101_4
  | exact S 21 101 5 cell_21_101_5
theorem cell_21_102_0 : C 21 102 0 := by decide +kernel
theorem cell_21_102_1 : C 21 102 1 := by decide +kernel
theorem cell_21_102_2 : C 21 102 2 := by decide +kernel
theorem cell_21_102_3 : C 21 102 3 := by decide +kernel
theorem cell_21_102_4 : C 21 102 4 := by decide +kernel
theorem cell_21_102_5 : C 21 102 5 := by decide +kernel
theorem row_21_102 : ThresholdAt 21 102 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 102 0 cell_21_102_0
  | exact S 21 102 1 cell_21_102_1
  | exact S 21 102 2 cell_21_102_2
  | exact S 21 102 3 cell_21_102_3
  | exact S 21 102 4 cell_21_102_4
  | exact S 21 102 5 cell_21_102_5
theorem cell_21_103_0 : C 21 103 0 := by decide +kernel
theorem cell_21_103_1 : C 21 103 1 := by decide +kernel
theorem cell_21_103_2 : C 21 103 2 := by decide +kernel
theorem cell_21_103_3 : C 21 103 3 := by decide +kernel
theorem cell_21_103_4 : C 21 103 4 := by decide +kernel
theorem cell_21_103_5 : C 21 103 5 := by decide +kernel
theorem row_21_103 : ThresholdAt 21 103 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 103 0 cell_21_103_0
  | exact S 21 103 1 cell_21_103_1
  | exact S 21 103 2 cell_21_103_2
  | exact S 21 103 3 cell_21_103_3
  | exact S 21 103 4 cell_21_103_4
  | exact S 21 103 5 cell_21_103_5
theorem cell_21_104_0 : C 21 104 0 := by decide +kernel
theorem cell_21_104_1 : C 21 104 1 := by decide +kernel
theorem cell_21_104_2 : C 21 104 2 := by decide +kernel
theorem cell_21_104_3 : C 21 104 3 := by decide +kernel
theorem cell_21_104_4 : C 21 104 4 := by decide +kernel
theorem cell_21_104_5 : C 21 104 5 := by decide +kernel
theorem row_21_104 : ThresholdAt 21 104 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 104 0 cell_21_104_0
  | exact S 21 104 1 cell_21_104_1
  | exact S 21 104 2 cell_21_104_2
  | exact S 21 104 3 cell_21_104_3
  | exact S 21 104 4 cell_21_104_4
  | exact S 21 104 5 cell_21_104_5
theorem cell_21_105_0 : C 21 105 0 := by decide +kernel
theorem cell_21_105_1 : C 21 105 1 := by decide +kernel
theorem cell_21_105_2 : C 21 105 2 := by decide +kernel
theorem cell_21_105_3 : C 21 105 3 := by decide +kernel
theorem cell_21_105_4 : C 21 105 4 := by decide +kernel
theorem cell_21_105_5 : C 21 105 5 := by decide +kernel
theorem row_21_105 : ThresholdAt 21 105 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 105 0 cell_21_105_0
  | exact S 21 105 1 cell_21_105_1
  | exact S 21 105 2 cell_21_105_2
  | exact S 21 105 3 cell_21_105_3
  | exact S 21 105 4 cell_21_105_4
  | exact S 21 105 5 cell_21_105_5
theorem cell_21_106_0 : C 21 106 0 := by decide +kernel
theorem cell_21_106_1 : C 21 106 1 := by decide +kernel
theorem cell_21_106_2 : C 21 106 2 := by decide +kernel
theorem cell_21_106_3 : C 21 106 3 := by decide +kernel
theorem cell_21_106_4 : C 21 106 4 := by decide +kernel
theorem cell_21_106_5 : C 21 106 5 := by decide +kernel
theorem row_21_106 : ThresholdAt 21 106 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 106 0 cell_21_106_0
  | exact S 21 106 1 cell_21_106_1
  | exact S 21 106 2 cell_21_106_2
  | exact S 21 106 3 cell_21_106_3
  | exact S 21 106 4 cell_21_106_4
  | exact S 21 106 5 cell_21_106_5
theorem cell_21_107_0 : C 21 107 0 := by decide +kernel
theorem cell_21_107_1 : C 21 107 1 := by decide +kernel
theorem cell_21_107_2 : C 21 107 2 := by decide +kernel
theorem cell_21_107_3 : C 21 107 3 := by decide +kernel
theorem cell_21_107_4 : C 21 107 4 := by decide +kernel
theorem cell_21_107_5 : C 21 107 5 := by decide +kernel
theorem row_21_107 : ThresholdAt 21 107 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 107 0 cell_21_107_0
  | exact S 21 107 1 cell_21_107_1
  | exact S 21 107 2 cell_21_107_2
  | exact S 21 107 3 cell_21_107_3
  | exact S 21 107 4 cell_21_107_4
  | exact S 21 107 5 cell_21_107_5
theorem cell_21_108_0 : C 21 108 0 := by decide +kernel
theorem cell_21_108_1 : C 21 108 1 := by decide +kernel
theorem cell_21_108_2 : C 21 108 2 := by decide +kernel
theorem cell_21_108_3 : C 21 108 3 := by decide +kernel
theorem cell_21_108_4 : C 21 108 4 := by decide +kernel
theorem cell_21_108_5 : C 21 108 5 := by decide +kernel
theorem row_21_108 : ThresholdAt 21 108 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 108 0 cell_21_108_0
  | exact S 21 108 1 cell_21_108_1
  | exact S 21 108 2 cell_21_108_2
  | exact S 21 108 3 cell_21_108_3
  | exact S 21 108 4 cell_21_108_4
  | exact S 21 108 5 cell_21_108_5
theorem cell_21_109_0 : C 21 109 0 := by decide +kernel
theorem cell_21_109_1 : C 21 109 1 := by decide +kernel
theorem cell_21_109_2 : C 21 109 2 := by decide +kernel
theorem cell_21_109_3 : C 21 109 3 := by decide +kernel
theorem cell_21_109_4 : C 21 109 4 := by decide +kernel
theorem cell_21_109_5 : C 21 109 5 := by decide +kernel
theorem row_21_109 : ThresholdAt 21 109 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 109 0 cell_21_109_0
  | exact S 21 109 1 cell_21_109_1
  | exact S 21 109 2 cell_21_109_2
  | exact S 21 109 3 cell_21_109_3
  | exact S 21 109 4 cell_21_109_4
  | exact S 21 109 5 cell_21_109_5
theorem cell_21_110_0 : C 21 110 0 := by decide +kernel
theorem cell_21_110_1 : C 21 110 1 := by decide +kernel
theorem cell_21_110_2 : C 21 110 2 := by decide +kernel
theorem cell_21_110_3 : C 21 110 3 := by decide +kernel
theorem cell_21_110_4 : C 21 110 4 := by decide +kernel
theorem cell_21_110_5 : C 21 110 5 := by decide +kernel
theorem row_21_110 : ThresholdAt 21 110 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 110 0 cell_21_110_0
  | exact S 21 110 1 cell_21_110_1
  | exact S 21 110 2 cell_21_110_2
  | exact S 21 110 3 cell_21_110_3
  | exact S 21 110 4 cell_21_110_4
  | exact S 21 110 5 cell_21_110_5
theorem cell_21_111_0 : C 21 111 0 := by decide +kernel
theorem cell_21_111_1 : C 21 111 1 := by decide +kernel
theorem cell_21_111_2 : C 21 111 2 := by decide +kernel
theorem cell_21_111_3 : C 21 111 3 := by decide +kernel
theorem cell_21_111_4 : C 21 111 4 := by decide +kernel
theorem cell_21_111_5 : C 21 111 5 := by decide +kernel
theorem row_21_111 : ThresholdAt 21 111 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 111 0 cell_21_111_0
  | exact S 21 111 1 cell_21_111_1
  | exact S 21 111 2 cell_21_111_2
  | exact S 21 111 3 cell_21_111_3
  | exact S 21 111 4 cell_21_111_4
  | exact S 21 111 5 cell_21_111_5
theorem cell_21_112_0 : C 21 112 0 := by decide +kernel
theorem cell_21_112_1 : C 21 112 1 := by decide +kernel
theorem cell_21_112_2 : C 21 112 2 := by decide +kernel
theorem cell_21_112_3 : C 21 112 3 := by decide +kernel
theorem cell_21_112_4 : C 21 112 4 := by decide +kernel
theorem cell_21_112_5 : C 21 112 5 := by decide +kernel
theorem row_21_112 : ThresholdAt 21 112 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 112 0 cell_21_112_0
  | exact S 21 112 1 cell_21_112_1
  | exact S 21 112 2 cell_21_112_2
  | exact S 21 112 3 cell_21_112_3
  | exact S 21 112 4 cell_21_112_4
  | exact S 21 112 5 cell_21_112_5
theorem cell_21_113_0 : C 21 113 0 := by decide +kernel
theorem cell_21_113_1 : C 21 113 1 := by decide +kernel
theorem cell_21_113_2 : C 21 113 2 := by decide +kernel
theorem cell_21_113_3 : C 21 113 3 := by decide +kernel
theorem cell_21_113_4 : C 21 113 4 := by decide +kernel
theorem cell_21_113_5 : C 21 113 5 := by decide +kernel
theorem row_21_113 : ThresholdAt 21 113 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 113 0 cell_21_113_0
  | exact S 21 113 1 cell_21_113_1
  | exact S 21 113 2 cell_21_113_2
  | exact S 21 113 3 cell_21_113_3
  | exact S 21 113 4 cell_21_113_4
  | exact S 21 113 5 cell_21_113_5
theorem cell_21_114_0 : C 21 114 0 := by decide +kernel
theorem cell_21_114_1 : C 21 114 1 := by decide +kernel
theorem cell_21_114_2 : C 21 114 2 := by decide +kernel
theorem cell_21_114_3 : C 21 114 3 := by decide +kernel
theorem cell_21_114_4 : C 21 114 4 := by decide +kernel
theorem cell_21_114_5 : C 21 114 5 := by decide +kernel
theorem row_21_114 : ThresholdAt 21 114 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 114 0 cell_21_114_0
  | exact S 21 114 1 cell_21_114_1
  | exact S 21 114 2 cell_21_114_2
  | exact S 21 114 3 cell_21_114_3
  | exact S 21 114 4 cell_21_114_4
  | exact S 21 114 5 cell_21_114_5
theorem cell_21_115_0 : C 21 115 0 := by decide +kernel
theorem cell_21_115_1 : C 21 115 1 := by decide +kernel
theorem cell_21_115_2 : C 21 115 2 := by decide +kernel
theorem cell_21_115_3 : C 21 115 3 := by decide +kernel
theorem cell_21_115_4 : C 21 115 4 := by decide +kernel
theorem cell_21_115_5 : C 21 115 5 := by decide +kernel
theorem row_21_115 : ThresholdAt 21 115 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 115 0 cell_21_115_0
  | exact S 21 115 1 cell_21_115_1
  | exact S 21 115 2 cell_21_115_2
  | exact S 21 115 3 cell_21_115_3
  | exact S 21 115 4 cell_21_115_4
  | exact S 21 115 5 cell_21_115_5
theorem cell_21_116_0 : C 21 116 0 := by decide +kernel
theorem cell_21_116_1 : C 21 116 1 := by decide +kernel
theorem cell_21_116_2 : C 21 116 2 := by decide +kernel
theorem cell_21_116_3 : C 21 116 3 := by decide +kernel
theorem cell_21_116_4 : C 21 116 4 := by decide +kernel
theorem cell_21_116_5 : C 21 116 5 := by decide +kernel
theorem row_21_116 : ThresholdAt 21 116 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 116 0 cell_21_116_0
  | exact S 21 116 1 cell_21_116_1
  | exact S 21 116 2 cell_21_116_2
  | exact S 21 116 3 cell_21_116_3
  | exact S 21 116 4 cell_21_116_4
  | exact S 21 116 5 cell_21_116_5
theorem cell_21_117_0 : C 21 117 0 := by decide +kernel
theorem cell_21_117_1 : C 21 117 1 := by decide +kernel
theorem cell_21_117_2 : C 21 117 2 := by decide +kernel
theorem cell_21_117_3 : C 21 117 3 := by decide +kernel
theorem cell_21_117_4 : C 21 117 4 := by decide +kernel
theorem cell_21_117_5 : C 21 117 5 := by decide +kernel
theorem row_21_117 : ThresholdAt 21 117 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 117 0 cell_21_117_0
  | exact S 21 117 1 cell_21_117_1
  | exact S 21 117 2 cell_21_117_2
  | exact S 21 117 3 cell_21_117_3
  | exact S 21 117 4 cell_21_117_4
  | exact S 21 117 5 cell_21_117_5
theorem cell_21_118_0 : C 21 118 0 := by decide +kernel
theorem cell_21_118_1 : C 21 118 1 := by decide +kernel
theorem cell_21_118_2 : C 21 118 2 := by decide +kernel
theorem cell_21_118_3 : C 21 118 3 := by decide +kernel
theorem cell_21_118_4 : C 21 118 4 := by decide +kernel
theorem cell_21_118_5 : C 21 118 5 := by decide +kernel
theorem row_21_118 : ThresholdAt 21 118 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 21 118 0 cell_21_118_0
  | exact S 21 118 1 cell_21_118_1
  | exact S 21 118 2 cell_21_118_2
  | exact S 21 118 3 cell_21_118_3
  | exact S 21 118 4 cell_21_118_4
  | exact S 21 118 5 cell_21_118_5
theorem checkedR21 : ∀ V ∈ List.range 119, ThresholdAt 21 V := by
  intro V hV
  have hv : V < 119 := List.mem_range.mp hV
  by_cases h0_119 : V < 59
  · by_cases h0_59 : V < 29
    · by_cases h0_29 : V < 14
      · by_cases h0_14 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have he : V = 0 := by omega
              subst V
              exact row_21_0
            · by_cases h1_3 : V < 2
              · have he : V = 1 := by omega
                subst V
                exact row_21_1
              · have he : V = 2 := by omega
                subst V
                exact row_21_2
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have he : V = 3 := by omega
                subst V
                exact row_21_3
              · have he : V = 4 := by omega
                subst V
                exact row_21_4
            · by_cases h5_7 : V < 6
              · have he : V = 5 := by omega
                subst V
                exact row_21_5
              · have he : V = 6 := by omega
                subst V
                exact row_21_6
        · by_cases h7_14 : V < 10
          · by_cases h7_10 : V < 8
            · have he : V = 7 := by omega
              subst V
              exact row_21_7
            · by_cases h8_10 : V < 9
              · have he : V = 8 := by omega
                subst V
                exact row_21_8
              · have he : V = 9 := by omega
                subst V
                exact row_21_9
          · by_cases h10_14 : V < 12
            · by_cases h10_12 : V < 11
              · have he : V = 10 := by omega
                subst V
                exact row_21_10
              · have he : V = 11 := by omega
                subst V
                exact row_21_11
            · by_cases h12_14 : V < 13
              · have he : V = 12 := by omega
                subst V
                exact row_21_12
              · have he : V = 13 := by omega
                subst V
                exact row_21_13
      · by_cases h14_29 : V < 21
        · by_cases h14_21 : V < 17
          · by_cases h14_17 : V < 15
            · have he : V = 14 := by omega
              subst V
              exact row_21_14
            · by_cases h15_17 : V < 16
              · have he : V = 15 := by omega
                subst V
                exact row_21_15
              · have he : V = 16 := by omega
                subst V
                exact row_21_16
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have he : V = 17 := by omega
                subst V
                exact row_21_17
              · have he : V = 18 := by omega
                subst V
                exact row_21_18
            · by_cases h19_21 : V < 20
              · have he : V = 19 := by omega
                subst V
                exact row_21_19
              · have he : V = 20 := by omega
                subst V
                exact row_21_20
        · by_cases h21_29 : V < 25
          · by_cases h21_25 : V < 23
            · by_cases h21_23 : V < 22
              · have he : V = 21 := by omega
                subst V
                exact row_21_21
              · have he : V = 22 := by omega
                subst V
                exact row_21_22
            · by_cases h23_25 : V < 24
              · have he : V = 23 := by omega
                subst V
                exact row_21_23
              · have he : V = 24 := by omega
                subst V
                exact row_21_24
          · by_cases h25_29 : V < 27
            · by_cases h25_27 : V < 26
              · have he : V = 25 := by omega
                subst V
                exact row_21_25
              · have he : V = 26 := by omega
                subst V
                exact row_21_26
            · by_cases h27_29 : V < 28
              · have he : V = 27 := by omega
                subst V
                exact row_21_27
              · have he : V = 28 := by omega
                subst V
                exact row_21_28
    · by_cases h29_59 : V < 44
      · by_cases h29_44 : V < 36
        · by_cases h29_36 : V < 32
          · by_cases h29_32 : V < 30
            · have he : V = 29 := by omega
              subst V
              exact row_21_29
            · by_cases h30_32 : V < 31
              · have he : V = 30 := by omega
                subst V
                exact row_21_30
              · have he : V = 31 := by omega
                subst V
                exact row_21_31
          · by_cases h32_36 : V < 34
            · by_cases h32_34 : V < 33
              · have he : V = 32 := by omega
                subst V
                exact row_21_32
              · have he : V = 33 := by omega
                subst V
                exact row_21_33
            · by_cases h34_36 : V < 35
              · have he : V = 34 := by omega
                subst V
                exact row_21_34
              · have he : V = 35 := by omega
                subst V
                exact row_21_35
        · by_cases h36_44 : V < 40
          · by_cases h36_40 : V < 38
            · by_cases h36_38 : V < 37
              · have he : V = 36 := by omega
                subst V
                exact row_21_36
              · have he : V = 37 := by omega
                subst V
                exact row_21_37
            · by_cases h38_40 : V < 39
              · have he : V = 38 := by omega
                subst V
                exact row_21_38
              · have he : V = 39 := by omega
                subst V
                exact row_21_39
          · by_cases h40_44 : V < 42
            · by_cases h40_42 : V < 41
              · have he : V = 40 := by omega
                subst V
                exact row_21_40
              · have he : V = 41 := by omega
                subst V
                exact row_21_41
            · by_cases h42_44 : V < 43
              · have he : V = 42 := by omega
                subst V
                exact row_21_42
              · have he : V = 43 := by omega
                subst V
                exact row_21_43
      · by_cases h44_59 : V < 51
        · by_cases h44_51 : V < 47
          · by_cases h44_47 : V < 45
            · have he : V = 44 := by omega
              subst V
              exact row_21_44
            · by_cases h45_47 : V < 46
              · have he : V = 45 := by omega
                subst V
                exact row_21_45
              · have he : V = 46 := by omega
                subst V
                exact row_21_46
          · by_cases h47_51 : V < 49
            · by_cases h47_49 : V < 48
              · have he : V = 47 := by omega
                subst V
                exact row_21_47
              · have he : V = 48 := by omega
                subst V
                exact row_21_48
            · by_cases h49_51 : V < 50
              · have he : V = 49 := by omega
                subst V
                exact row_21_49
              · have he : V = 50 := by omega
                subst V
                exact row_21_50
        · by_cases h51_59 : V < 55
          · by_cases h51_55 : V < 53
            · by_cases h51_53 : V < 52
              · have he : V = 51 := by omega
                subst V
                exact row_21_51
              · have he : V = 52 := by omega
                subst V
                exact row_21_52
            · by_cases h53_55 : V < 54
              · have he : V = 53 := by omega
                subst V
                exact row_21_53
              · have he : V = 54 := by omega
                subst V
                exact row_21_54
          · by_cases h55_59 : V < 57
            · by_cases h55_57 : V < 56
              · have he : V = 55 := by omega
                subst V
                exact row_21_55
              · have he : V = 56 := by omega
                subst V
                exact row_21_56
            · by_cases h57_59 : V < 58
              · have he : V = 57 := by omega
                subst V
                exact row_21_57
              · have he : V = 58 := by omega
                subst V
                exact row_21_58
  · by_cases h59_119 : V < 89
    · by_cases h59_89 : V < 74
      · by_cases h59_74 : V < 66
        · by_cases h59_66 : V < 62
          · by_cases h59_62 : V < 60
            · have he : V = 59 := by omega
              subst V
              exact row_21_59
            · by_cases h60_62 : V < 61
              · have he : V = 60 := by omega
                subst V
                exact row_21_60
              · have he : V = 61 := by omega
                subst V
                exact row_21_61
          · by_cases h62_66 : V < 64
            · by_cases h62_64 : V < 63
              · have he : V = 62 := by omega
                subst V
                exact row_21_62
              · have he : V = 63 := by omega
                subst V
                exact row_21_63
            · by_cases h64_66 : V < 65
              · have he : V = 64 := by omega
                subst V
                exact row_21_64
              · have he : V = 65 := by omega
                subst V
                exact row_21_65
        · by_cases h66_74 : V < 70
          · by_cases h66_70 : V < 68
            · by_cases h66_68 : V < 67
              · have he : V = 66 := by omega
                subst V
                exact row_21_66
              · have he : V = 67 := by omega
                subst V
                exact row_21_67
            · by_cases h68_70 : V < 69
              · have he : V = 68 := by omega
                subst V
                exact row_21_68
              · have he : V = 69 := by omega
                subst V
                exact row_21_69
          · by_cases h70_74 : V < 72
            · by_cases h70_72 : V < 71
              · have he : V = 70 := by omega
                subst V
                exact row_21_70
              · have he : V = 71 := by omega
                subst V
                exact row_21_71
            · by_cases h72_74 : V < 73
              · have he : V = 72 := by omega
                subst V
                exact row_21_72
              · have he : V = 73 := by omega
                subst V
                exact row_21_73
      · by_cases h74_89 : V < 81
        · by_cases h74_81 : V < 77
          · by_cases h74_77 : V < 75
            · have he : V = 74 := by omega
              subst V
              exact row_21_74
            · by_cases h75_77 : V < 76
              · have he : V = 75 := by omega
                subst V
                exact row_21_75
              · have he : V = 76 := by omega
                subst V
                exact row_21_76
          · by_cases h77_81 : V < 79
            · by_cases h77_79 : V < 78
              · have he : V = 77 := by omega
                subst V
                exact row_21_77
              · have he : V = 78 := by omega
                subst V
                exact row_21_78
            · by_cases h79_81 : V < 80
              · have he : V = 79 := by omega
                subst V
                exact row_21_79
              · have he : V = 80 := by omega
                subst V
                exact row_21_80
        · by_cases h81_89 : V < 85
          · by_cases h81_85 : V < 83
            · by_cases h81_83 : V < 82
              · have he : V = 81 := by omega
                subst V
                exact row_21_81
              · have he : V = 82 := by omega
                subst V
                exact row_21_82
            · by_cases h83_85 : V < 84
              · have he : V = 83 := by omega
                subst V
                exact row_21_83
              · have he : V = 84 := by omega
                subst V
                exact row_21_84
          · by_cases h85_89 : V < 87
            · by_cases h85_87 : V < 86
              · have he : V = 85 := by omega
                subst V
                exact row_21_85
              · have he : V = 86 := by omega
                subst V
                exact row_21_86
            · by_cases h87_89 : V < 88
              · have he : V = 87 := by omega
                subst V
                exact row_21_87
              · have he : V = 88 := by omega
                subst V
                exact row_21_88
    · by_cases h89_119 : V < 104
      · by_cases h89_104 : V < 96
        · by_cases h89_96 : V < 92
          · by_cases h89_92 : V < 90
            · have he : V = 89 := by omega
              subst V
              exact row_21_89
            · by_cases h90_92 : V < 91
              · have he : V = 90 := by omega
                subst V
                exact row_21_90
              · have he : V = 91 := by omega
                subst V
                exact row_21_91
          · by_cases h92_96 : V < 94
            · by_cases h92_94 : V < 93
              · have he : V = 92 := by omega
                subst V
                exact row_21_92
              · have he : V = 93 := by omega
                subst V
                exact row_21_93
            · by_cases h94_96 : V < 95
              · have he : V = 94 := by omega
                subst V
                exact row_21_94
              · have he : V = 95 := by omega
                subst V
                exact row_21_95
        · by_cases h96_104 : V < 100
          · by_cases h96_100 : V < 98
            · by_cases h96_98 : V < 97
              · have he : V = 96 := by omega
                subst V
                exact row_21_96
              · have he : V = 97 := by omega
                subst V
                exact row_21_97
            · by_cases h98_100 : V < 99
              · have he : V = 98 := by omega
                subst V
                exact row_21_98
              · have he : V = 99 := by omega
                subst V
                exact row_21_99
          · by_cases h100_104 : V < 102
            · by_cases h100_102 : V < 101
              · have he : V = 100 := by omega
                subst V
                exact row_21_100
              · have he : V = 101 := by omega
                subst V
                exact row_21_101
            · by_cases h102_104 : V < 103
              · have he : V = 102 := by omega
                subst V
                exact row_21_102
              · have he : V = 103 := by omega
                subst V
                exact row_21_103
      · by_cases h104_119 : V < 111
        · by_cases h104_111 : V < 107
          · by_cases h104_107 : V < 105
            · have he : V = 104 := by omega
              subst V
              exact row_21_104
            · by_cases h105_107 : V < 106
              · have he : V = 105 := by omega
                subst V
                exact row_21_105
              · have he : V = 106 := by omega
                subst V
                exact row_21_106
          · by_cases h107_111 : V < 109
            · by_cases h107_109 : V < 108
              · have he : V = 107 := by omega
                subst V
                exact row_21_107
              · have he : V = 108 := by omega
                subst V
                exact row_21_108
            · by_cases h109_111 : V < 110
              · have he : V = 109 := by omega
                subst V
                exact row_21_109
              · have he : V = 110 := by omega
                subst V
                exact row_21_110
        · by_cases h111_119 : V < 115
          · by_cases h111_115 : V < 113
            · by_cases h111_113 : V < 112
              · have he : V = 111 := by omega
                subst V
                exact row_21_111
              · have he : V = 112 := by omega
                subst V
                exact row_21_112
            · by_cases h113_115 : V < 114
              · have he : V = 113 := by omega
                subst V
                exact row_21_113
              · have he : V = 114 := by omega
                subst V
                exact row_21_114
          · by_cases h115_119 : V < 117
            · by_cases h115_117 : V < 116
              · have he : V = 115 := by omega
                subst V
                exact row_21_115
              · have he : V = 116 := by omega
                subst V
                exact row_21_116
            · by_cases h117_119 : V < 118
              · have he : V = 117 := by omega
                subst V
                exact row_21_117
              · have he : V = 118 := by omega
                subst V
                exact row_21_118
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
