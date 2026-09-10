import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked01

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_2_0_0 : C 2 0 0 := by decide +kernel
theorem cell_2_0_1 : C 2 0 1 := by decide +kernel
theorem cell_2_0_2 : C 2 0 2 := by decide +kernel
theorem cell_2_0_3 : C 2 0 3 := by decide +kernel
theorem cell_2_0_4 : C 2 0 4 := by decide +kernel
theorem cell_2_0_5 : C 2 0 5 := by decide +kernel
theorem row_2_0 : ThresholdAt 2 0 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 0 0 cell_2_0_0
  | exact S 2 0 1 cell_2_0_1
  | exact S 2 0 2 cell_2_0_2
  | exact S 2 0 3 cell_2_0_3
  | exact S 2 0 4 cell_2_0_4
  | exact S 2 0 5 cell_2_0_5
theorem cell_2_1_0 : C 2 1 0 := by decide +kernel
theorem cell_2_1_1 : C 2 1 1 := by decide +kernel
theorem cell_2_1_2 : C 2 1 2 := by decide +kernel
theorem cell_2_1_3 : C 2 1 3 := by decide +kernel
theorem cell_2_1_4 : C 2 1 4 := by decide +kernel
theorem cell_2_1_5 : C 2 1 5 := by decide +kernel
theorem row_2_1 : ThresholdAt 2 1 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 1 0 cell_2_1_0
  | exact S 2 1 1 cell_2_1_1
  | exact S 2 1 2 cell_2_1_2
  | exact S 2 1 3 cell_2_1_3
  | exact S 2 1 4 cell_2_1_4
  | exact S 2 1 5 cell_2_1_5
theorem cell_2_2_0 : C 2 2 0 := by decide +kernel
theorem cell_2_2_1 : C 2 2 1 := by decide +kernel
theorem cell_2_2_2 : C 2 2 2 := by decide +kernel
theorem cell_2_2_3 : C 2 2 3 := by decide +kernel
theorem cell_2_2_4 : C 2 2 4 := by decide +kernel
theorem cell_2_2_5 : C 2 2 5 := by decide +kernel
theorem row_2_2 : ThresholdAt 2 2 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 2 0 cell_2_2_0
  | exact S 2 2 1 cell_2_2_1
  | exact S 2 2 2 cell_2_2_2
  | exact S 2 2 3 cell_2_2_3
  | exact S 2 2 4 cell_2_2_4
  | exact S 2 2 5 cell_2_2_5
theorem cell_2_3_0 : C 2 3 0 := by decide +kernel
theorem cell_2_3_1 : C 2 3 1 := by decide +kernel
theorem cell_2_3_2 : C 2 3 2 := by decide +kernel
theorem cell_2_3_3 : C 2 3 3 := by decide +kernel
theorem cell_2_3_4 : C 2 3 4 := by decide +kernel
theorem cell_2_3_5 : C 2 3 5 := by decide +kernel
theorem row_2_3 : ThresholdAt 2 3 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 3 0 cell_2_3_0
  | exact S 2 3 1 cell_2_3_1
  | exact S 2 3 2 cell_2_3_2
  | exact S 2 3 3 cell_2_3_3
  | exact S 2 3 4 cell_2_3_4
  | exact S 2 3 5 cell_2_3_5
theorem cell_2_4_0 : C 2 4 0 := by decide +kernel
theorem cell_2_4_1 : C 2 4 1 := by decide +kernel
theorem cell_2_4_2 : C 2 4 2 := by decide +kernel
theorem cell_2_4_3 : C 2 4 3 := by decide +kernel
theorem cell_2_4_4 : C 2 4 4 := by decide +kernel
theorem cell_2_4_5 : C 2 4 5 := by decide +kernel
theorem row_2_4 : ThresholdAt 2 4 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 4 0 cell_2_4_0
  | exact S 2 4 1 cell_2_4_1
  | exact S 2 4 2 cell_2_4_2
  | exact S 2 4 3 cell_2_4_3
  | exact S 2 4 4 cell_2_4_4
  | exact S 2 4 5 cell_2_4_5
theorem cell_2_5_0 : C 2 5 0 := by decide +kernel
theorem cell_2_5_1 : C 2 5 1 := by decide +kernel
theorem cell_2_5_2 : C 2 5 2 := by decide +kernel
theorem cell_2_5_3 : C 2 5 3 := by decide +kernel
theorem cell_2_5_4 : C 2 5 4 := by decide +kernel
theorem cell_2_5_5 : C 2 5 5 := by decide +kernel
theorem row_2_5 : ThresholdAt 2 5 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 5 0 cell_2_5_0
  | exact S 2 5 1 cell_2_5_1
  | exact S 2 5 2 cell_2_5_2
  | exact S 2 5 3 cell_2_5_3
  | exact S 2 5 4 cell_2_5_4
  | exact S 2 5 5 cell_2_5_5
theorem cell_2_6_0 : C 2 6 0 := by decide +kernel
theorem cell_2_6_1 : C 2 6 1 := by decide +kernel
theorem cell_2_6_2 : C 2 6 2 := by decide +kernel
theorem cell_2_6_3 : C 2 6 3 := by decide +kernel
theorem cell_2_6_4 : C 2 6 4 := by decide +kernel
theorem cell_2_6_5 : C 2 6 5 := by decide +kernel
theorem row_2_6 : ThresholdAt 2 6 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 6 0 cell_2_6_0
  | exact S 2 6 1 cell_2_6_1
  | exact S 2 6 2 cell_2_6_2
  | exact S 2 6 3 cell_2_6_3
  | exact S 2 6 4 cell_2_6_4
  | exact S 2 6 5 cell_2_6_5
theorem cell_2_7_0 : C 2 7 0 := by decide +kernel
theorem cell_2_7_1 : C 2 7 1 := by decide +kernel
theorem cell_2_7_2 : C 2 7 2 := by decide +kernel
theorem cell_2_7_3 : C 2 7 3 := by decide +kernel
theorem cell_2_7_4 : C 2 7 4 := by decide +kernel
theorem cell_2_7_5 : C 2 7 5 := by decide +kernel
theorem row_2_7 : ThresholdAt 2 7 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 7 0 cell_2_7_0
  | exact S 2 7 1 cell_2_7_1
  | exact S 2 7 2 cell_2_7_2
  | exact S 2 7 3 cell_2_7_3
  | exact S 2 7 4 cell_2_7_4
  | exact S 2 7 5 cell_2_7_5
theorem cell_2_8_0 : C 2 8 0 := by decide +kernel
theorem cell_2_8_1 : C 2 8 1 := by decide +kernel
theorem cell_2_8_2 : C 2 8 2 := by decide +kernel
theorem cell_2_8_3 : C 2 8 3 := by decide +kernel
theorem cell_2_8_4 : C 2 8 4 := by decide +kernel
theorem cell_2_8_5 : C 2 8 5 := by decide +kernel
theorem row_2_8 : ThresholdAt 2 8 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 8 0 cell_2_8_0
  | exact S 2 8 1 cell_2_8_1
  | exact S 2 8 2 cell_2_8_2
  | exact S 2 8 3 cell_2_8_3
  | exact S 2 8 4 cell_2_8_4
  | exact S 2 8 5 cell_2_8_5
theorem cell_2_9_0 : C 2 9 0 := by decide +kernel
theorem cell_2_9_1 : C 2 9 1 := by decide +kernel
theorem cell_2_9_2 : C 2 9 2 := by decide +kernel
theorem cell_2_9_3 : C 2 9 3 := by decide +kernel
theorem cell_2_9_4 : C 2 9 4 := by decide +kernel
theorem cell_2_9_5 : C 2 9 5 := by decide +kernel
theorem row_2_9 : ThresholdAt 2 9 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 9 0 cell_2_9_0
  | exact S 2 9 1 cell_2_9_1
  | exact S 2 9 2 cell_2_9_2
  | exact S 2 9 3 cell_2_9_3
  | exact S 2 9 4 cell_2_9_4
  | exact S 2 9 5 cell_2_9_5
theorem cell_2_10_0 : C 2 10 0 := by decide +kernel
theorem cell_2_10_1 : C 2 10 1 := by decide +kernel
theorem cell_2_10_2 : C 2 10 2 := by decide +kernel
theorem cell_2_10_3 : C 2 10 3 := by decide +kernel
theorem cell_2_10_4 : C 2 10 4 := by decide +kernel
theorem cell_2_10_5 : C 2 10 5 := by decide +kernel
theorem row_2_10 : ThresholdAt 2 10 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 10 0 cell_2_10_0
  | exact S 2 10 1 cell_2_10_1
  | exact S 2 10 2 cell_2_10_2
  | exact S 2 10 3 cell_2_10_3
  | exact S 2 10 4 cell_2_10_4
  | exact S 2 10 5 cell_2_10_5
theorem cell_2_11_0 : C 2 11 0 := by decide +kernel
theorem cell_2_11_1 : C 2 11 1 := by decide +kernel
theorem cell_2_11_2 : C 2 11 2 := by decide +kernel
theorem cell_2_11_3 : C 2 11 3 := by decide +kernel
theorem cell_2_11_4 : C 2 11 4 := by decide +kernel
theorem cell_2_11_5 : C 2 11 5 := by decide +kernel
theorem row_2_11 : ThresholdAt 2 11 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 11 0 cell_2_11_0
  | exact S 2 11 1 cell_2_11_1
  | exact S 2 11 2 cell_2_11_2
  | exact S 2 11 3 cell_2_11_3
  | exact S 2 11 4 cell_2_11_4
  | exact S 2 11 5 cell_2_11_5
theorem cell_2_12_0 : C 2 12 0 := by decide +kernel
theorem cell_2_12_1 : C 2 12 1 := by decide +kernel
theorem cell_2_12_2 : C 2 12 2 := by decide +kernel
theorem cell_2_12_3 : C 2 12 3 := by decide +kernel
theorem cell_2_12_4 : C 2 12 4 := by decide +kernel
theorem cell_2_12_5 : C 2 12 5 := by decide +kernel
theorem row_2_12 : ThresholdAt 2 12 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 12 0 cell_2_12_0
  | exact S 2 12 1 cell_2_12_1
  | exact S 2 12 2 cell_2_12_2
  | exact S 2 12 3 cell_2_12_3
  | exact S 2 12 4 cell_2_12_4
  | exact S 2 12 5 cell_2_12_5
theorem cell_2_13_0 : C 2 13 0 := by decide +kernel
theorem cell_2_13_1 : C 2 13 1 := by decide +kernel
theorem cell_2_13_2 : C 2 13 2 := by decide +kernel
theorem cell_2_13_3 : C 2 13 3 := by decide +kernel
theorem cell_2_13_4 : C 2 13 4 := by decide +kernel
theorem cell_2_13_5 : C 2 13 5 := by decide +kernel
theorem row_2_13 : ThresholdAt 2 13 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 13 0 cell_2_13_0
  | exact S 2 13 1 cell_2_13_1
  | exact S 2 13 2 cell_2_13_2
  | exact S 2 13 3 cell_2_13_3
  | exact S 2 13 4 cell_2_13_4
  | exact S 2 13 5 cell_2_13_5
theorem cell_2_14_0 : C 2 14 0 := by decide +kernel
theorem cell_2_14_1 : C 2 14 1 := by decide +kernel
theorem cell_2_14_2 : C 2 14 2 := by decide +kernel
theorem cell_2_14_3 : C 2 14 3 := by decide +kernel
theorem cell_2_14_4 : C 2 14 4 := by decide +kernel
theorem cell_2_14_5 : C 2 14 5 := by decide +kernel
theorem row_2_14 : ThresholdAt 2 14 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 14 0 cell_2_14_0
  | exact S 2 14 1 cell_2_14_1
  | exact S 2 14 2 cell_2_14_2
  | exact S 2 14 3 cell_2_14_3
  | exact S 2 14 4 cell_2_14_4
  | exact S 2 14 5 cell_2_14_5
theorem cell_2_15_0 : C 2 15 0 := by decide +kernel
theorem cell_2_15_1 : C 2 15 1 := by decide +kernel
theorem cell_2_15_2 : C 2 15 2 := by decide +kernel
theorem cell_2_15_3 : C 2 15 3 := by decide +kernel
theorem cell_2_15_4 : C 2 15 4 := by decide +kernel
theorem cell_2_15_5 : C 2 15 5 := by decide +kernel
theorem row_2_15 : ThresholdAt 2 15 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 15 0 cell_2_15_0
  | exact S 2 15 1 cell_2_15_1
  | exact S 2 15 2 cell_2_15_2
  | exact S 2 15 3 cell_2_15_3
  | exact S 2 15 4 cell_2_15_4
  | exact S 2 15 5 cell_2_15_5
theorem cell_2_16_0 : C 2 16 0 := by decide +kernel
theorem cell_2_16_1 : C 2 16 1 := by decide +kernel
theorem cell_2_16_2 : C 2 16 2 := by decide +kernel
theorem cell_2_16_3 : C 2 16 3 := by decide +kernel
theorem cell_2_16_4 : C 2 16 4 := by decide +kernel
theorem cell_2_16_5 : C 2 16 5 := by decide +kernel
theorem row_2_16 : ThresholdAt 2 16 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 16 0 cell_2_16_0
  | exact S 2 16 1 cell_2_16_1
  | exact S 2 16 2 cell_2_16_2
  | exact S 2 16 3 cell_2_16_3
  | exact S 2 16 4 cell_2_16_4
  | exact S 2 16 5 cell_2_16_5
theorem cell_2_17_0 : C 2 17 0 := by decide +kernel
theorem cell_2_17_1 : C 2 17 1 := by decide +kernel
theorem cell_2_17_2 : C 2 17 2 := by decide +kernel
theorem cell_2_17_3 : C 2 17 3 := by decide +kernel
theorem cell_2_17_4 : C 2 17 4 := by decide +kernel
theorem cell_2_17_5 : C 2 17 5 := by decide +kernel
theorem row_2_17 : ThresholdAt 2 17 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 17 0 cell_2_17_0
  | exact S 2 17 1 cell_2_17_1
  | exact S 2 17 2 cell_2_17_2
  | exact S 2 17 3 cell_2_17_3
  | exact S 2 17 4 cell_2_17_4
  | exact S 2 17 5 cell_2_17_5
theorem cell_2_18_0 : C 2 18 0 := by decide +kernel
theorem cell_2_18_1 : C 2 18 1 := by decide +kernel
theorem cell_2_18_2 : C 2 18 2 := by decide +kernel
theorem cell_2_18_3 : C 2 18 3 := by decide +kernel
theorem cell_2_18_4 : C 2 18 4 := by decide +kernel
theorem cell_2_18_5 : C 2 18 5 := by decide +kernel
theorem row_2_18 : ThresholdAt 2 18 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 18 0 cell_2_18_0
  | exact S 2 18 1 cell_2_18_1
  | exact S 2 18 2 cell_2_18_2
  | exact S 2 18 3 cell_2_18_3
  | exact S 2 18 4 cell_2_18_4
  | exact S 2 18 5 cell_2_18_5
theorem cell_2_19_0 : C 2 19 0 := by decide +kernel
theorem cell_2_19_1 : C 2 19 1 := by decide +kernel
theorem cell_2_19_2 : C 2 19 2 := by decide +kernel
theorem cell_2_19_3 : C 2 19 3 := by decide +kernel
theorem cell_2_19_4 : C 2 19 4 := by decide +kernel
theorem cell_2_19_5 : C 2 19 5 := by decide +kernel
theorem row_2_19 : ThresholdAt 2 19 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 19 0 cell_2_19_0
  | exact S 2 19 1 cell_2_19_1
  | exact S 2 19 2 cell_2_19_2
  | exact S 2 19 3 cell_2_19_3
  | exact S 2 19 4 cell_2_19_4
  | exact S 2 19 5 cell_2_19_5
theorem cell_2_20_0 : C 2 20 0 := by decide +kernel
theorem cell_2_20_1 : C 2 20 1 := by decide +kernel
theorem cell_2_20_2 : C 2 20 2 := by decide +kernel
theorem cell_2_20_3 : C 2 20 3 := by decide +kernel
theorem cell_2_20_4 : C 2 20 4 := by decide +kernel
theorem cell_2_20_5 : C 2 20 5 := by decide +kernel
theorem row_2_20 : ThresholdAt 2 20 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 20 0 cell_2_20_0
  | exact S 2 20 1 cell_2_20_1
  | exact S 2 20 2 cell_2_20_2
  | exact S 2 20 3 cell_2_20_3
  | exact S 2 20 4 cell_2_20_4
  | exact S 2 20 5 cell_2_20_5
theorem cell_2_21_0 : C 2 21 0 := by decide +kernel
theorem cell_2_21_1 : C 2 21 1 := by decide +kernel
theorem cell_2_21_2 : C 2 21 2 := by decide +kernel
theorem cell_2_21_3 : C 2 21 3 := by decide +kernel
theorem cell_2_21_4 : C 2 21 4 := by decide +kernel
theorem cell_2_21_5 : C 2 21 5 := by decide +kernel
theorem row_2_21 : ThresholdAt 2 21 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 21 0 cell_2_21_0
  | exact S 2 21 1 cell_2_21_1
  | exact S 2 21 2 cell_2_21_2
  | exact S 2 21 3 cell_2_21_3
  | exact S 2 21 4 cell_2_21_4
  | exact S 2 21 5 cell_2_21_5
theorem cell_2_22_0 : C 2 22 0 := by decide +kernel
theorem cell_2_22_1 : C 2 22 1 := by decide +kernel
theorem cell_2_22_2 : C 2 22 2 := by decide +kernel
theorem cell_2_22_3 : C 2 22 3 := by decide +kernel
theorem cell_2_22_4 : C 2 22 4 := by decide +kernel
theorem cell_2_22_5 : C 2 22 5 := by decide +kernel
theorem row_2_22 : ThresholdAt 2 22 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 22 0 cell_2_22_0
  | exact S 2 22 1 cell_2_22_1
  | exact S 2 22 2 cell_2_22_2
  | exact S 2 22 3 cell_2_22_3
  | exact S 2 22 4 cell_2_22_4
  | exact S 2 22 5 cell_2_22_5
theorem cell_2_23_0 : C 2 23 0 := by decide +kernel
theorem cell_2_23_1 : C 2 23 1 := by decide +kernel
theorem cell_2_23_2 : C 2 23 2 := by decide +kernel
theorem cell_2_23_3 : C 2 23 3 := by decide +kernel
theorem cell_2_23_4 : C 2 23 4 := by decide +kernel
theorem cell_2_23_5 : C 2 23 5 := by decide +kernel
theorem row_2_23 : ThresholdAt 2 23 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 23 0 cell_2_23_0
  | exact S 2 23 1 cell_2_23_1
  | exact S 2 23 2 cell_2_23_2
  | exact S 2 23 3 cell_2_23_3
  | exact S 2 23 4 cell_2_23_4
  | exact S 2 23 5 cell_2_23_5
theorem cell_2_24_0 : C 2 24 0 := by decide +kernel
theorem cell_2_24_1 : C 2 24 1 := by decide +kernel
theorem cell_2_24_2 : C 2 24 2 := by decide +kernel
theorem cell_2_24_3 : C 2 24 3 := by decide +kernel
theorem cell_2_24_4 : C 2 24 4 := by decide +kernel
theorem cell_2_24_5 : C 2 24 5 := by decide +kernel
theorem row_2_24 : ThresholdAt 2 24 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 24 0 cell_2_24_0
  | exact S 2 24 1 cell_2_24_1
  | exact S 2 24 2 cell_2_24_2
  | exact S 2 24 3 cell_2_24_3
  | exact S 2 24 4 cell_2_24_4
  | exact S 2 24 5 cell_2_24_5
theorem cell_2_25_0 : C 2 25 0 := by decide +kernel
theorem cell_2_25_1 : C 2 25 1 := by decide +kernel
theorem cell_2_25_2 : C 2 25 2 := by decide +kernel
theorem cell_2_25_3 : C 2 25 3 := by decide +kernel
theorem cell_2_25_4 : C 2 25 4 := by decide +kernel
theorem cell_2_25_5 : C 2 25 5 := by decide +kernel
theorem row_2_25 : ThresholdAt 2 25 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 25 0 cell_2_25_0
  | exact S 2 25 1 cell_2_25_1
  | exact S 2 25 2 cell_2_25_2
  | exact S 2 25 3 cell_2_25_3
  | exact S 2 25 4 cell_2_25_4
  | exact S 2 25 5 cell_2_25_5
theorem cell_2_26_0 : C 2 26 0 := by decide +kernel
theorem cell_2_26_1 : C 2 26 1 := by decide +kernel
theorem cell_2_26_2 : C 2 26 2 := by decide +kernel
theorem cell_2_26_3 : C 2 26 3 := by decide +kernel
theorem cell_2_26_4 : C 2 26 4 := by decide +kernel
theorem cell_2_26_5 : C 2 26 5 := by decide +kernel
theorem row_2_26 : ThresholdAt 2 26 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 26 0 cell_2_26_0
  | exact S 2 26 1 cell_2_26_1
  | exact S 2 26 2 cell_2_26_2
  | exact S 2 26 3 cell_2_26_3
  | exact S 2 26 4 cell_2_26_4
  | exact S 2 26 5 cell_2_26_5
theorem cell_2_27_0 : C 2 27 0 := by decide +kernel
theorem cell_2_27_1 : C 2 27 1 := by decide +kernel
theorem cell_2_27_2 : C 2 27 2 := by decide +kernel
theorem cell_2_27_3 : C 2 27 3 := by decide +kernel
theorem cell_2_27_4 : C 2 27 4 := by decide +kernel
theorem cell_2_27_5 : C 2 27 5 := by decide +kernel
theorem row_2_27 : ThresholdAt 2 27 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 27 0 cell_2_27_0
  | exact S 2 27 1 cell_2_27_1
  | exact S 2 27 2 cell_2_27_2
  | exact S 2 27 3 cell_2_27_3
  | exact S 2 27 4 cell_2_27_4
  | exact S 2 27 5 cell_2_27_5
theorem cell_2_28_0 : C 2 28 0 := by decide +kernel
theorem cell_2_28_1 : C 2 28 1 := by decide +kernel
theorem cell_2_28_2 : C 2 28 2 := by decide +kernel
theorem cell_2_28_3 : C 2 28 3 := by decide +kernel
theorem cell_2_28_4 : C 2 28 4 := by decide +kernel
theorem cell_2_28_5 : C 2 28 5 := by decide +kernel
theorem row_2_28 : ThresholdAt 2 28 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 28 0 cell_2_28_0
  | exact S 2 28 1 cell_2_28_1
  | exact S 2 28 2 cell_2_28_2
  | exact S 2 28 3 cell_2_28_3
  | exact S 2 28 4 cell_2_28_4
  | exact S 2 28 5 cell_2_28_5
theorem cell_2_29_0 : C 2 29 0 := by decide +kernel
theorem cell_2_29_1 : C 2 29 1 := by decide +kernel
theorem cell_2_29_2 : C 2 29 2 := by decide +kernel
theorem cell_2_29_3 : C 2 29 3 := by decide +kernel
theorem cell_2_29_4 : C 2 29 4 := by decide +kernel
theorem cell_2_29_5 : C 2 29 5 := by decide +kernel
theorem row_2_29 : ThresholdAt 2 29 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 29 0 cell_2_29_0
  | exact S 2 29 1 cell_2_29_1
  | exact S 2 29 2 cell_2_29_2
  | exact S 2 29 3 cell_2_29_3
  | exact S 2 29 4 cell_2_29_4
  | exact S 2 29 5 cell_2_29_5
theorem cell_2_30_0 : C 2 30 0 := by decide +kernel
theorem cell_2_30_1 : C 2 30 1 := by decide +kernel
theorem cell_2_30_2 : C 2 30 2 := by decide +kernel
theorem cell_2_30_3 : C 2 30 3 := by decide +kernel
theorem cell_2_30_4 : C 2 30 4 := by decide +kernel
theorem cell_2_30_5 : C 2 30 5 := by decide +kernel
theorem row_2_30 : ThresholdAt 2 30 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 30 0 cell_2_30_0
  | exact S 2 30 1 cell_2_30_1
  | exact S 2 30 2 cell_2_30_2
  | exact S 2 30 3 cell_2_30_3
  | exact S 2 30 4 cell_2_30_4
  | exact S 2 30 5 cell_2_30_5
theorem cell_2_31_0 : C 2 31 0 := by decide +kernel
theorem cell_2_31_1 : C 2 31 1 := by decide +kernel
theorem cell_2_31_2 : C 2 31 2 := by decide +kernel
theorem cell_2_31_3 : C 2 31 3 := by decide +kernel
theorem cell_2_31_4 : C 2 31 4 := by decide +kernel
theorem cell_2_31_5 : C 2 31 5 := by decide +kernel
theorem row_2_31 : ThresholdAt 2 31 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 31 0 cell_2_31_0
  | exact S 2 31 1 cell_2_31_1
  | exact S 2 31 2 cell_2_31_2
  | exact S 2 31 3 cell_2_31_3
  | exact S 2 31 4 cell_2_31_4
  | exact S 2 31 5 cell_2_31_5
theorem cell_2_32_0 : C 2 32 0 := by decide +kernel
theorem cell_2_32_1 : C 2 32 1 := by decide +kernel
theorem cell_2_32_2 : C 2 32 2 := by decide +kernel
theorem cell_2_32_3 : C 2 32 3 := by decide +kernel
theorem cell_2_32_4 : C 2 32 4 := by decide +kernel
theorem cell_2_32_5 : C 2 32 5 := by decide +kernel
theorem row_2_32 : ThresholdAt 2 32 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 32 0 cell_2_32_0
  | exact S 2 32 1 cell_2_32_1
  | exact S 2 32 2 cell_2_32_2
  | exact S 2 32 3 cell_2_32_3
  | exact S 2 32 4 cell_2_32_4
  | exact S 2 32 5 cell_2_32_5
theorem cell_2_33_0 : C 2 33 0 := by decide +kernel
theorem cell_2_33_1 : C 2 33 1 := by decide +kernel
theorem cell_2_33_2 : C 2 33 2 := by decide +kernel
theorem cell_2_33_3 : C 2 33 3 := by decide +kernel
theorem cell_2_33_4 : C 2 33 4 := by decide +kernel
theorem cell_2_33_5 : C 2 33 5 := by decide +kernel
theorem row_2_33 : ThresholdAt 2 33 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 33 0 cell_2_33_0
  | exact S 2 33 1 cell_2_33_1
  | exact S 2 33 2 cell_2_33_2
  | exact S 2 33 3 cell_2_33_3
  | exact S 2 33 4 cell_2_33_4
  | exact S 2 33 5 cell_2_33_5
theorem cell_2_34_0 : C 2 34 0 := by decide +kernel
theorem cell_2_34_1 : C 2 34 1 := by decide +kernel
theorem cell_2_34_2 : C 2 34 2 := by decide +kernel
theorem cell_2_34_3 : C 2 34 3 := by decide +kernel
theorem cell_2_34_4 : C 2 34 4 := by decide +kernel
theorem cell_2_34_5 : C 2 34 5 := by decide +kernel
theorem row_2_34 : ThresholdAt 2 34 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 34 0 cell_2_34_0
  | exact S 2 34 1 cell_2_34_1
  | exact S 2 34 2 cell_2_34_2
  | exact S 2 34 3 cell_2_34_3
  | exact S 2 34 4 cell_2_34_4
  | exact S 2 34 5 cell_2_34_5
theorem cell_2_35_0 : C 2 35 0 := by decide +kernel
theorem cell_2_35_1 : C 2 35 1 := by decide +kernel
theorem cell_2_35_2 : C 2 35 2 := by decide +kernel
theorem cell_2_35_3 : C 2 35 3 := by decide +kernel
theorem cell_2_35_4 : C 2 35 4 := by decide +kernel
theorem cell_2_35_5 : C 2 35 5 := by decide +kernel
theorem row_2_35 : ThresholdAt 2 35 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 35 0 cell_2_35_0
  | exact S 2 35 1 cell_2_35_1
  | exact S 2 35 2 cell_2_35_2
  | exact S 2 35 3 cell_2_35_3
  | exact S 2 35 4 cell_2_35_4
  | exact S 2 35 5 cell_2_35_5
theorem cell_2_36_0 : C 2 36 0 := by decide +kernel
theorem cell_2_36_1 : C 2 36 1 := by decide +kernel
theorem cell_2_36_2 : C 2 36 2 := by decide +kernel
theorem cell_2_36_3 : C 2 36 3 := by decide +kernel
theorem cell_2_36_4 : C 2 36 4 := by decide +kernel
theorem cell_2_36_5 : C 2 36 5 := by decide +kernel
theorem row_2_36 : ThresholdAt 2 36 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 36 0 cell_2_36_0
  | exact S 2 36 1 cell_2_36_1
  | exact S 2 36 2 cell_2_36_2
  | exact S 2 36 3 cell_2_36_3
  | exact S 2 36 4 cell_2_36_4
  | exact S 2 36 5 cell_2_36_5
theorem cell_2_37_0 : C 2 37 0 := by decide +kernel
theorem cell_2_37_1 : C 2 37 1 := by decide +kernel
theorem cell_2_37_2 : C 2 37 2 := by decide +kernel
theorem cell_2_37_3 : C 2 37 3 := by decide +kernel
theorem cell_2_37_4 : C 2 37 4 := by decide +kernel
theorem cell_2_37_5 : C 2 37 5 := by decide +kernel
theorem row_2_37 : ThresholdAt 2 37 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 37 0 cell_2_37_0
  | exact S 2 37 1 cell_2_37_1
  | exact S 2 37 2 cell_2_37_2
  | exact S 2 37 3 cell_2_37_3
  | exact S 2 37 4 cell_2_37_4
  | exact S 2 37 5 cell_2_37_5
theorem cell_2_38_0 : C 2 38 0 := by decide +kernel
theorem cell_2_38_1 : C 2 38 1 := by decide +kernel
theorem cell_2_38_2 : C 2 38 2 := by decide +kernel
theorem cell_2_38_3 : C 2 38 3 := by decide +kernel
theorem cell_2_38_4 : C 2 38 4 := by decide +kernel
theorem cell_2_38_5 : C 2 38 5 := by decide +kernel
theorem row_2_38 : ThresholdAt 2 38 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 38 0 cell_2_38_0
  | exact S 2 38 1 cell_2_38_1
  | exact S 2 38 2 cell_2_38_2
  | exact S 2 38 3 cell_2_38_3
  | exact S 2 38 4 cell_2_38_4
  | exact S 2 38 5 cell_2_38_5
theorem cell_2_39_0 : C 2 39 0 := by decide +kernel
theorem cell_2_39_1 : C 2 39 1 := by decide +kernel
theorem cell_2_39_2 : C 2 39 2 := by decide +kernel
theorem cell_2_39_3 : C 2 39 3 := by decide +kernel
theorem cell_2_39_4 : C 2 39 4 := by decide +kernel
theorem cell_2_39_5 : C 2 39 5 := by decide +kernel
theorem row_2_39 : ThresholdAt 2 39 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 39 0 cell_2_39_0
  | exact S 2 39 1 cell_2_39_1
  | exact S 2 39 2 cell_2_39_2
  | exact S 2 39 3 cell_2_39_3
  | exact S 2 39 4 cell_2_39_4
  | exact S 2 39 5 cell_2_39_5
theorem cell_2_40_0 : C 2 40 0 := by decide +kernel
theorem cell_2_40_1 : C 2 40 1 := by decide +kernel
theorem cell_2_40_2 : C 2 40 2 := by decide +kernel
theorem cell_2_40_3 : C 2 40 3 := by decide +kernel
theorem cell_2_40_4 : C 2 40 4 := by decide +kernel
theorem cell_2_40_5 : C 2 40 5 := by decide +kernel
theorem row_2_40 : ThresholdAt 2 40 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 40 0 cell_2_40_0
  | exact S 2 40 1 cell_2_40_1
  | exact S 2 40 2 cell_2_40_2
  | exact S 2 40 3 cell_2_40_3
  | exact S 2 40 4 cell_2_40_4
  | exact S 2 40 5 cell_2_40_5
theorem cell_2_41_0 : C 2 41 0 := by decide +kernel
theorem cell_2_41_1 : C 2 41 1 := by decide +kernel
theorem cell_2_41_2 : C 2 41 2 := by decide +kernel
theorem cell_2_41_3 : C 2 41 3 := by decide +kernel
theorem cell_2_41_4 : C 2 41 4 := by decide +kernel
theorem cell_2_41_5 : C 2 41 5 := by decide +kernel
theorem row_2_41 : ThresholdAt 2 41 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 41 0 cell_2_41_0
  | exact S 2 41 1 cell_2_41_1
  | exact S 2 41 2 cell_2_41_2
  | exact S 2 41 3 cell_2_41_3
  | exact S 2 41 4 cell_2_41_4
  | exact S 2 41 5 cell_2_41_5
theorem cell_2_42_0 : C 2 42 0 := by decide +kernel
theorem cell_2_42_1 : C 2 42 1 := by decide +kernel
theorem cell_2_42_2 : C 2 42 2 := by decide +kernel
theorem cell_2_42_3 : C 2 42 3 := by decide +kernel
theorem cell_2_42_4 : C 2 42 4 := by decide +kernel
theorem cell_2_42_5 : C 2 42 5 := by decide +kernel
theorem row_2_42 : ThresholdAt 2 42 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 42 0 cell_2_42_0
  | exact S 2 42 1 cell_2_42_1
  | exact S 2 42 2 cell_2_42_2
  | exact S 2 42 3 cell_2_42_3
  | exact S 2 42 4 cell_2_42_4
  | exact S 2 42 5 cell_2_42_5
theorem cell_2_43_0 : C 2 43 0 := by decide +kernel
theorem cell_2_43_1 : C 2 43 1 := by decide +kernel
theorem cell_2_43_2 : C 2 43 2 := by decide +kernel
theorem cell_2_43_3 : C 2 43 3 := by decide +kernel
theorem cell_2_43_4 : C 2 43 4 := by decide +kernel
theorem cell_2_43_5 : C 2 43 5 := by decide +kernel
theorem row_2_43 : ThresholdAt 2 43 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 43 0 cell_2_43_0
  | exact S 2 43 1 cell_2_43_1
  | exact S 2 43 2 cell_2_43_2
  | exact S 2 43 3 cell_2_43_3
  | exact S 2 43 4 cell_2_43_4
  | exact S 2 43 5 cell_2_43_5
theorem cell_2_44_0 : C 2 44 0 := by decide +kernel
theorem cell_2_44_1 : C 2 44 1 := by decide +kernel
theorem cell_2_44_2 : C 2 44 2 := by decide +kernel
theorem cell_2_44_3 : C 2 44 3 := by decide +kernel
theorem cell_2_44_4 : C 2 44 4 := by decide +kernel
theorem cell_2_44_5 : C 2 44 5 := by decide +kernel
theorem row_2_44 : ThresholdAt 2 44 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 44 0 cell_2_44_0
  | exact S 2 44 1 cell_2_44_1
  | exact S 2 44 2 cell_2_44_2
  | exact S 2 44 3 cell_2_44_3
  | exact S 2 44 4 cell_2_44_4
  | exact S 2 44 5 cell_2_44_5
theorem cell_2_45_0 : C 2 45 0 := by decide +kernel
theorem cell_2_45_1 : C 2 45 1 := by decide +kernel
theorem cell_2_45_2 : C 2 45 2 := by decide +kernel
theorem cell_2_45_3 : C 2 45 3 := by decide +kernel
theorem cell_2_45_4 : C 2 45 4 := by decide +kernel
theorem cell_2_45_5 : C 2 45 5 := by decide +kernel
theorem row_2_45 : ThresholdAt 2 45 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 45 0 cell_2_45_0
  | exact S 2 45 1 cell_2_45_1
  | exact S 2 45 2 cell_2_45_2
  | exact S 2 45 3 cell_2_45_3
  | exact S 2 45 4 cell_2_45_4
  | exact S 2 45 5 cell_2_45_5
theorem cell_2_46_0 : C 2 46 0 := by decide +kernel
theorem cell_2_46_1 : C 2 46 1 := by decide +kernel
theorem cell_2_46_2 : C 2 46 2 := by decide +kernel
theorem cell_2_46_3 : C 2 46 3 := by decide +kernel
theorem cell_2_46_4 : C 2 46 4 := by decide +kernel
theorem cell_2_46_5 : C 2 46 5 := by decide +kernel
theorem row_2_46 : ThresholdAt 2 46 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 46 0 cell_2_46_0
  | exact S 2 46 1 cell_2_46_1
  | exact S 2 46 2 cell_2_46_2
  | exact S 2 46 3 cell_2_46_3
  | exact S 2 46 4 cell_2_46_4
  | exact S 2 46 5 cell_2_46_5
theorem cell_2_47_0 : C 2 47 0 := by decide +kernel
theorem cell_2_47_1 : C 2 47 1 := by decide +kernel
theorem cell_2_47_2 : C 2 47 2 := by decide +kernel
theorem cell_2_47_3 : C 2 47 3 := by decide +kernel
theorem cell_2_47_4 : C 2 47 4 := by decide +kernel
theorem cell_2_47_5 : C 2 47 5 := by decide +kernel
theorem row_2_47 : ThresholdAt 2 47 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 47 0 cell_2_47_0
  | exact S 2 47 1 cell_2_47_1
  | exact S 2 47 2 cell_2_47_2
  | exact S 2 47 3 cell_2_47_3
  | exact S 2 47 4 cell_2_47_4
  | exact S 2 47 5 cell_2_47_5
theorem cell_2_48_0 : C 2 48 0 := by decide +kernel
theorem cell_2_48_1 : C 2 48 1 := by decide +kernel
theorem cell_2_48_2 : C 2 48 2 := by decide +kernel
theorem cell_2_48_3 : C 2 48 3 := by decide +kernel
theorem cell_2_48_4 : C 2 48 4 := by decide +kernel
theorem cell_2_48_5 : C 2 48 5 := by decide +kernel
theorem row_2_48 : ThresholdAt 2 48 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 48 0 cell_2_48_0
  | exact S 2 48 1 cell_2_48_1
  | exact S 2 48 2 cell_2_48_2
  | exact S 2 48 3 cell_2_48_3
  | exact S 2 48 4 cell_2_48_4
  | exact S 2 48 5 cell_2_48_5
theorem cell_2_49_0 : C 2 49 0 := by decide +kernel
theorem cell_2_49_1 : C 2 49 1 := by decide +kernel
theorem cell_2_49_2 : C 2 49 2 := by decide +kernel
theorem cell_2_49_3 : C 2 49 3 := by decide +kernel
theorem cell_2_49_4 : C 2 49 4 := by decide +kernel
theorem cell_2_49_5 : C 2 49 5 := by decide +kernel
theorem row_2_49 : ThresholdAt 2 49 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 49 0 cell_2_49_0
  | exact S 2 49 1 cell_2_49_1
  | exact S 2 49 2 cell_2_49_2
  | exact S 2 49 3 cell_2_49_3
  | exact S 2 49 4 cell_2_49_4
  | exact S 2 49 5 cell_2_49_5
theorem cell_2_50_0 : C 2 50 0 := by decide +kernel
theorem cell_2_50_1 : C 2 50 1 := by decide +kernel
theorem cell_2_50_2 : C 2 50 2 := by decide +kernel
theorem cell_2_50_3 : C 2 50 3 := by decide +kernel
theorem cell_2_50_4 : C 2 50 4 := by decide +kernel
theorem cell_2_50_5 : C 2 50 5 := by decide +kernel
theorem row_2_50 : ThresholdAt 2 50 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 50 0 cell_2_50_0
  | exact S 2 50 1 cell_2_50_1
  | exact S 2 50 2 cell_2_50_2
  | exact S 2 50 3 cell_2_50_3
  | exact S 2 50 4 cell_2_50_4
  | exact S 2 50 5 cell_2_50_5
theorem cell_2_51_0 : C 2 51 0 := by decide +kernel
theorem cell_2_51_1 : C 2 51 1 := by decide +kernel
theorem cell_2_51_2 : C 2 51 2 := by decide +kernel
theorem cell_2_51_3 : C 2 51 3 := by decide +kernel
theorem cell_2_51_4 : C 2 51 4 := by decide +kernel
theorem cell_2_51_5 : C 2 51 5 := by decide +kernel
theorem row_2_51 : ThresholdAt 2 51 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 51 0 cell_2_51_0
  | exact S 2 51 1 cell_2_51_1
  | exact S 2 51 2 cell_2_51_2
  | exact S 2 51 3 cell_2_51_3
  | exact S 2 51 4 cell_2_51_4
  | exact S 2 51 5 cell_2_51_5
theorem cell_2_52_0 : C 2 52 0 := by decide +kernel
theorem cell_2_52_1 : C 2 52 1 := by decide +kernel
theorem cell_2_52_2 : C 2 52 2 := by decide +kernel
theorem cell_2_52_3 : C 2 52 3 := by decide +kernel
theorem cell_2_52_4 : C 2 52 4 := by decide +kernel
theorem cell_2_52_5 : C 2 52 5 := by decide +kernel
theorem row_2_52 : ThresholdAt 2 52 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 52 0 cell_2_52_0
  | exact S 2 52 1 cell_2_52_1
  | exact S 2 52 2 cell_2_52_2
  | exact S 2 52 3 cell_2_52_3
  | exact S 2 52 4 cell_2_52_4
  | exact S 2 52 5 cell_2_52_5
theorem cell_2_53_0 : C 2 53 0 := by decide +kernel
theorem cell_2_53_1 : C 2 53 1 := by decide +kernel
theorem cell_2_53_2 : C 2 53 2 := by decide +kernel
theorem cell_2_53_3 : C 2 53 3 := by decide +kernel
theorem cell_2_53_4 : C 2 53 4 := by decide +kernel
theorem cell_2_53_5 : C 2 53 5 := by decide +kernel
theorem row_2_53 : ThresholdAt 2 53 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 53 0 cell_2_53_0
  | exact S 2 53 1 cell_2_53_1
  | exact S 2 53 2 cell_2_53_2
  | exact S 2 53 3 cell_2_53_3
  | exact S 2 53 4 cell_2_53_4
  | exact S 2 53 5 cell_2_53_5
theorem cell_2_54_0 : C 2 54 0 := by decide +kernel
theorem cell_2_54_1 : C 2 54 1 := by decide +kernel
theorem cell_2_54_2 : C 2 54 2 := by decide +kernel
theorem cell_2_54_3 : C 2 54 3 := by decide +kernel
theorem cell_2_54_4 : C 2 54 4 := by decide +kernel
theorem cell_2_54_5 : C 2 54 5 := by decide +kernel
theorem row_2_54 : ThresholdAt 2 54 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 54 0 cell_2_54_0
  | exact S 2 54 1 cell_2_54_1
  | exact S 2 54 2 cell_2_54_2
  | exact S 2 54 3 cell_2_54_3
  | exact S 2 54 4 cell_2_54_4
  | exact S 2 54 5 cell_2_54_5
theorem cell_2_55_0 : C 2 55 0 := by decide +kernel
theorem cell_2_55_1 : C 2 55 1 := by decide +kernel
theorem cell_2_55_2 : C 2 55 2 := by decide +kernel
theorem cell_2_55_3 : C 2 55 3 := by decide +kernel
theorem cell_2_55_4 : C 2 55 4 := by decide +kernel
theorem cell_2_55_5 : C 2 55 5 := by decide +kernel
theorem row_2_55 : ThresholdAt 2 55 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 55 0 cell_2_55_0
  | exact S 2 55 1 cell_2_55_1
  | exact S 2 55 2 cell_2_55_2
  | exact S 2 55 3 cell_2_55_3
  | exact S 2 55 4 cell_2_55_4
  | exact S 2 55 5 cell_2_55_5
theorem cell_2_56_0 : C 2 56 0 := by decide +kernel
theorem cell_2_56_1 : C 2 56 1 := by decide +kernel
theorem cell_2_56_2 : C 2 56 2 := by decide +kernel
theorem cell_2_56_3 : C 2 56 3 := by decide +kernel
theorem cell_2_56_4 : C 2 56 4 := by decide +kernel
theorem cell_2_56_5 : C 2 56 5 := by decide +kernel
theorem row_2_56 : ThresholdAt 2 56 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 56 0 cell_2_56_0
  | exact S 2 56 1 cell_2_56_1
  | exact S 2 56 2 cell_2_56_2
  | exact S 2 56 3 cell_2_56_3
  | exact S 2 56 4 cell_2_56_4
  | exact S 2 56 5 cell_2_56_5
theorem cell_2_57_0 : C 2 57 0 := by decide +kernel
theorem cell_2_57_1 : C 2 57 1 := by decide +kernel
theorem cell_2_57_2 : C 2 57 2 := by decide +kernel
theorem cell_2_57_3 : C 2 57 3 := by decide +kernel
theorem cell_2_57_4 : C 2 57 4 := by decide +kernel
theorem cell_2_57_5 : C 2 57 5 := by decide +kernel
theorem row_2_57 : ThresholdAt 2 57 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 57 0 cell_2_57_0
  | exact S 2 57 1 cell_2_57_1
  | exact S 2 57 2 cell_2_57_2
  | exact S 2 57 3 cell_2_57_3
  | exact S 2 57 4 cell_2_57_4
  | exact S 2 57 5 cell_2_57_5
theorem cell_2_58_0 : C 2 58 0 := by decide +kernel
theorem cell_2_58_1 : C 2 58 1 := by decide +kernel
theorem cell_2_58_2 : C 2 58 2 := by decide +kernel
theorem cell_2_58_3 : C 2 58 3 := by decide +kernel
theorem cell_2_58_4 : C 2 58 4 := by decide +kernel
theorem cell_2_58_5 : C 2 58 5 := by decide +kernel
theorem row_2_58 : ThresholdAt 2 58 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 58 0 cell_2_58_0
  | exact S 2 58 1 cell_2_58_1
  | exact S 2 58 2 cell_2_58_2
  | exact S 2 58 3 cell_2_58_3
  | exact S 2 58 4 cell_2_58_4
  | exact S 2 58 5 cell_2_58_5
theorem cell_2_59_0 : C 2 59 0 := by decide +kernel
theorem cell_2_59_1 : C 2 59 1 := by decide +kernel
theorem cell_2_59_2 : C 2 59 2 := by decide +kernel
theorem cell_2_59_3 : C 2 59 3 := by decide +kernel
theorem cell_2_59_4 : C 2 59 4 := by decide +kernel
theorem cell_2_59_5 : C 2 59 5 := by decide +kernel
theorem row_2_59 : ThresholdAt 2 59 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 59 0 cell_2_59_0
  | exact S 2 59 1 cell_2_59_1
  | exact S 2 59 2 cell_2_59_2
  | exact S 2 59 3 cell_2_59_3
  | exact S 2 59 4 cell_2_59_4
  | exact S 2 59 5 cell_2_59_5
theorem cell_2_60_0 : C 2 60 0 := by decide +kernel
theorem cell_2_60_1 : C 2 60 1 := by decide +kernel
theorem cell_2_60_2 : C 2 60 2 := by decide +kernel
theorem cell_2_60_3 : C 2 60 3 := by decide +kernel
theorem cell_2_60_4 : C 2 60 4 := by decide +kernel
theorem cell_2_60_5 : C 2 60 5 := by decide +kernel
theorem row_2_60 : ThresholdAt 2 60 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 60 0 cell_2_60_0
  | exact S 2 60 1 cell_2_60_1
  | exact S 2 60 2 cell_2_60_2
  | exact S 2 60 3 cell_2_60_3
  | exact S 2 60 4 cell_2_60_4
  | exact S 2 60 5 cell_2_60_5
theorem cell_2_61_0 : C 2 61 0 := by decide +kernel
theorem cell_2_61_1 : C 2 61 1 := by decide +kernel
theorem cell_2_61_2 : C 2 61 2 := by decide +kernel
theorem cell_2_61_3 : C 2 61 3 := by decide +kernel
theorem cell_2_61_4 : C 2 61 4 := by decide +kernel
theorem cell_2_61_5 : C 2 61 5 := by decide +kernel
theorem row_2_61 : ThresholdAt 2 61 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 61 0 cell_2_61_0
  | exact S 2 61 1 cell_2_61_1
  | exact S 2 61 2 cell_2_61_2
  | exact S 2 61 3 cell_2_61_3
  | exact S 2 61 4 cell_2_61_4
  | exact S 2 61 5 cell_2_61_5
theorem cell_2_62_0 : C 2 62 0 := by decide +kernel
theorem cell_2_62_1 : C 2 62 1 := by decide +kernel
theorem cell_2_62_2 : C 2 62 2 := by decide +kernel
theorem cell_2_62_3 : C 2 62 3 := by decide +kernel
theorem cell_2_62_4 : C 2 62 4 := by decide +kernel
theorem cell_2_62_5 : C 2 62 5 := by decide +kernel
theorem row_2_62 : ThresholdAt 2 62 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 62 0 cell_2_62_0
  | exact S 2 62 1 cell_2_62_1
  | exact S 2 62 2 cell_2_62_2
  | exact S 2 62 3 cell_2_62_3
  | exact S 2 62 4 cell_2_62_4
  | exact S 2 62 5 cell_2_62_5
theorem cell_2_63_0 : C 2 63 0 := by decide +kernel
theorem cell_2_63_1 : C 2 63 1 := by decide +kernel
theorem cell_2_63_2 : C 2 63 2 := by decide +kernel
theorem cell_2_63_3 : C 2 63 3 := by decide +kernel
theorem cell_2_63_4 : C 2 63 4 := by decide +kernel
theorem cell_2_63_5 : C 2 63 5 := by decide +kernel
theorem row_2_63 : ThresholdAt 2 63 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 63 0 cell_2_63_0
  | exact S 2 63 1 cell_2_63_1
  | exact S 2 63 2 cell_2_63_2
  | exact S 2 63 3 cell_2_63_3
  | exact S 2 63 4 cell_2_63_4
  | exact S 2 63 5 cell_2_63_5
theorem cell_2_64_0 : C 2 64 0 := by decide +kernel
theorem cell_2_64_1 : C 2 64 1 := by decide +kernel
theorem cell_2_64_2 : C 2 64 2 := by decide +kernel
theorem cell_2_64_3 : C 2 64 3 := by decide +kernel
theorem cell_2_64_4 : C 2 64 4 := by decide +kernel
theorem cell_2_64_5 : C 2 64 5 := by decide +kernel
theorem row_2_64 : ThresholdAt 2 64 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 64 0 cell_2_64_0
  | exact S 2 64 1 cell_2_64_1
  | exact S 2 64 2 cell_2_64_2
  | exact S 2 64 3 cell_2_64_3
  | exact S 2 64 4 cell_2_64_4
  | exact S 2 64 5 cell_2_64_5
theorem cell_2_65_0 : C 2 65 0 := by decide +kernel
theorem cell_2_65_1 : C 2 65 1 := by decide +kernel
theorem cell_2_65_2 : C 2 65 2 := by decide +kernel
theorem cell_2_65_3 : C 2 65 3 := by decide +kernel
theorem cell_2_65_4 : C 2 65 4 := by decide +kernel
theorem cell_2_65_5 : C 2 65 5 := by decide +kernel
theorem row_2_65 : ThresholdAt 2 65 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 65 0 cell_2_65_0
  | exact S 2 65 1 cell_2_65_1
  | exact S 2 65 2 cell_2_65_2
  | exact S 2 65 3 cell_2_65_3
  | exact S 2 65 4 cell_2_65_4
  | exact S 2 65 5 cell_2_65_5
theorem cell_2_66_0 : C 2 66 0 := by decide +kernel
theorem cell_2_66_1 : C 2 66 1 := by decide +kernel
theorem cell_2_66_2 : C 2 66 2 := by decide +kernel
theorem cell_2_66_3 : C 2 66 3 := by decide +kernel
theorem cell_2_66_4 : C 2 66 4 := by decide +kernel
theorem cell_2_66_5 : C 2 66 5 := by decide +kernel
theorem row_2_66 : ThresholdAt 2 66 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 66 0 cell_2_66_0
  | exact S 2 66 1 cell_2_66_1
  | exact S 2 66 2 cell_2_66_2
  | exact S 2 66 3 cell_2_66_3
  | exact S 2 66 4 cell_2_66_4
  | exact S 2 66 5 cell_2_66_5
theorem cell_2_67_0 : C 2 67 0 := by decide +kernel
theorem cell_2_67_1 : C 2 67 1 := by decide +kernel
theorem cell_2_67_2 : C 2 67 2 := by decide +kernel
theorem cell_2_67_3 : C 2 67 3 := by decide +kernel
theorem cell_2_67_4 : C 2 67 4 := by decide +kernel
theorem cell_2_67_5 : C 2 67 5 := by decide +kernel
theorem row_2_67 : ThresholdAt 2 67 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 67 0 cell_2_67_0
  | exact S 2 67 1 cell_2_67_1
  | exact S 2 67 2 cell_2_67_2
  | exact S 2 67 3 cell_2_67_3
  | exact S 2 67 4 cell_2_67_4
  | exact S 2 67 5 cell_2_67_5
theorem cell_2_68_0 : C 2 68 0 := by decide +kernel
theorem cell_2_68_1 : C 2 68 1 := by decide +kernel
theorem cell_2_68_2 : C 2 68 2 := by decide +kernel
theorem cell_2_68_3 : C 2 68 3 := by decide +kernel
theorem cell_2_68_4 : C 2 68 4 := by decide +kernel
theorem cell_2_68_5 : C 2 68 5 := by decide +kernel
theorem row_2_68 : ThresholdAt 2 68 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 68 0 cell_2_68_0
  | exact S 2 68 1 cell_2_68_1
  | exact S 2 68 2 cell_2_68_2
  | exact S 2 68 3 cell_2_68_3
  | exact S 2 68 4 cell_2_68_4
  | exact S 2 68 5 cell_2_68_5
theorem cell_2_69_0 : C 2 69 0 := by decide +kernel
theorem cell_2_69_1 : C 2 69 1 := by decide +kernel
theorem cell_2_69_2 : C 2 69 2 := by decide +kernel
theorem cell_2_69_3 : C 2 69 3 := by decide +kernel
theorem cell_2_69_4 : C 2 69 4 := by decide +kernel
theorem cell_2_69_5 : C 2 69 5 := by decide +kernel
theorem row_2_69 : ThresholdAt 2 69 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 69 0 cell_2_69_0
  | exact S 2 69 1 cell_2_69_1
  | exact S 2 69 2 cell_2_69_2
  | exact S 2 69 3 cell_2_69_3
  | exact S 2 69 4 cell_2_69_4
  | exact S 2 69 5 cell_2_69_5
theorem cell_2_70_0 : C 2 70 0 := by decide +kernel
theorem cell_2_70_1 : C 2 70 1 := by decide +kernel
theorem cell_2_70_2 : C 2 70 2 := by decide +kernel
theorem cell_2_70_3 : C 2 70 3 := by decide +kernel
theorem cell_2_70_4 : C 2 70 4 := by decide +kernel
theorem cell_2_70_5 : C 2 70 5 := by decide +kernel
theorem row_2_70 : ThresholdAt 2 70 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 70 0 cell_2_70_0
  | exact S 2 70 1 cell_2_70_1
  | exact S 2 70 2 cell_2_70_2
  | exact S 2 70 3 cell_2_70_3
  | exact S 2 70 4 cell_2_70_4
  | exact S 2 70 5 cell_2_70_5
theorem cell_2_71_0 : C 2 71 0 := by decide +kernel
theorem cell_2_71_1 : C 2 71 1 := by decide +kernel
theorem cell_2_71_2 : C 2 71 2 := by decide +kernel
theorem cell_2_71_3 : C 2 71 3 := by decide +kernel
theorem cell_2_71_4 : C 2 71 4 := by decide +kernel
theorem cell_2_71_5 : C 2 71 5 := by decide +kernel
theorem row_2_71 : ThresholdAt 2 71 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 71 0 cell_2_71_0
  | exact S 2 71 1 cell_2_71_1
  | exact S 2 71 2 cell_2_71_2
  | exact S 2 71 3 cell_2_71_3
  | exact S 2 71 4 cell_2_71_4
  | exact S 2 71 5 cell_2_71_5
theorem cell_2_72_0 : C 2 72 0 := by decide +kernel
theorem cell_2_72_1 : C 2 72 1 := by decide +kernel
theorem cell_2_72_2 : C 2 72 2 := by decide +kernel
theorem cell_2_72_3 : C 2 72 3 := by decide +kernel
theorem cell_2_72_4 : C 2 72 4 := by decide +kernel
theorem cell_2_72_5 : C 2 72 5 := by decide +kernel
theorem row_2_72 : ThresholdAt 2 72 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 72 0 cell_2_72_0
  | exact S 2 72 1 cell_2_72_1
  | exact S 2 72 2 cell_2_72_2
  | exact S 2 72 3 cell_2_72_3
  | exact S 2 72 4 cell_2_72_4
  | exact S 2 72 5 cell_2_72_5
theorem cell_2_73_0 : C 2 73 0 := by decide +kernel
theorem cell_2_73_1 : C 2 73 1 := by decide +kernel
theorem cell_2_73_2 : C 2 73 2 := by decide +kernel
theorem cell_2_73_3 : C 2 73 3 := by decide +kernel
theorem cell_2_73_4 : C 2 73 4 := by decide +kernel
theorem cell_2_73_5 : C 2 73 5 := by decide +kernel
theorem row_2_73 : ThresholdAt 2 73 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 73 0 cell_2_73_0
  | exact S 2 73 1 cell_2_73_1
  | exact S 2 73 2 cell_2_73_2
  | exact S 2 73 3 cell_2_73_3
  | exact S 2 73 4 cell_2_73_4
  | exact S 2 73 5 cell_2_73_5
theorem cell_2_74_0 : C 2 74 0 := by decide +kernel
theorem cell_2_74_1 : C 2 74 1 := by decide +kernel
theorem cell_2_74_2 : C 2 74 2 := by decide +kernel
theorem cell_2_74_3 : C 2 74 3 := by decide +kernel
theorem cell_2_74_4 : C 2 74 4 := by decide +kernel
theorem cell_2_74_5 : C 2 74 5 := by decide +kernel
theorem row_2_74 : ThresholdAt 2 74 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 74 0 cell_2_74_0
  | exact S 2 74 1 cell_2_74_1
  | exact S 2 74 2 cell_2_74_2
  | exact S 2 74 3 cell_2_74_3
  | exact S 2 74 4 cell_2_74_4
  | exact S 2 74 5 cell_2_74_5
theorem cell_2_75_0 : C 2 75 0 := by decide +kernel
theorem cell_2_75_1 : C 2 75 1 := by decide +kernel
theorem cell_2_75_2 : C 2 75 2 := by decide +kernel
theorem cell_2_75_3 : C 2 75 3 := by decide +kernel
theorem cell_2_75_4 : C 2 75 4 := by decide +kernel
theorem cell_2_75_5 : C 2 75 5 := by decide +kernel
theorem row_2_75 : ThresholdAt 2 75 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 75 0 cell_2_75_0
  | exact S 2 75 1 cell_2_75_1
  | exact S 2 75 2 cell_2_75_2
  | exact S 2 75 3 cell_2_75_3
  | exact S 2 75 4 cell_2_75_4
  | exact S 2 75 5 cell_2_75_5
theorem cell_2_76_0 : C 2 76 0 := by decide +kernel
theorem cell_2_76_1 : C 2 76 1 := by decide +kernel
theorem cell_2_76_2 : C 2 76 2 := by decide +kernel
theorem cell_2_76_3 : C 2 76 3 := by decide +kernel
theorem cell_2_76_4 : C 2 76 4 := by decide +kernel
theorem cell_2_76_5 : C 2 76 5 := by decide +kernel
theorem row_2_76 : ThresholdAt 2 76 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 76 0 cell_2_76_0
  | exact S 2 76 1 cell_2_76_1
  | exact S 2 76 2 cell_2_76_2
  | exact S 2 76 3 cell_2_76_3
  | exact S 2 76 4 cell_2_76_4
  | exact S 2 76 5 cell_2_76_5
theorem cell_2_77_0 : C 2 77 0 := by decide +kernel
theorem cell_2_77_1 : C 2 77 1 := by decide +kernel
theorem cell_2_77_2 : C 2 77 2 := by decide +kernel
theorem cell_2_77_3 : C 2 77 3 := by decide +kernel
theorem cell_2_77_4 : C 2 77 4 := by decide +kernel
theorem cell_2_77_5 : C 2 77 5 := by decide +kernel
theorem row_2_77 : ThresholdAt 2 77 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 77 0 cell_2_77_0
  | exact S 2 77 1 cell_2_77_1
  | exact S 2 77 2 cell_2_77_2
  | exact S 2 77 3 cell_2_77_3
  | exact S 2 77 4 cell_2_77_4
  | exact S 2 77 5 cell_2_77_5
theorem cell_2_78_0 : C 2 78 0 := by decide +kernel
theorem cell_2_78_1 : C 2 78 1 := by decide +kernel
theorem cell_2_78_2 : C 2 78 2 := by decide +kernel
theorem cell_2_78_3 : C 2 78 3 := by decide +kernel
theorem cell_2_78_4 : C 2 78 4 := by decide +kernel
theorem cell_2_78_5 : C 2 78 5 := by decide +kernel
theorem row_2_78 : ThresholdAt 2 78 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 78 0 cell_2_78_0
  | exact S 2 78 1 cell_2_78_1
  | exact S 2 78 2 cell_2_78_2
  | exact S 2 78 3 cell_2_78_3
  | exact S 2 78 4 cell_2_78_4
  | exact S 2 78 5 cell_2_78_5
theorem cell_2_79_0 : C 2 79 0 := by decide +kernel
theorem cell_2_79_1 : C 2 79 1 := by decide +kernel
theorem cell_2_79_2 : C 2 79 2 := by decide +kernel
theorem cell_2_79_3 : C 2 79 3 := by decide +kernel
theorem cell_2_79_4 : C 2 79 4 := by decide +kernel
theorem cell_2_79_5 : C 2 79 5 := by decide +kernel
theorem row_2_79 : ThresholdAt 2 79 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 79 0 cell_2_79_0
  | exact S 2 79 1 cell_2_79_1
  | exact S 2 79 2 cell_2_79_2
  | exact S 2 79 3 cell_2_79_3
  | exact S 2 79 4 cell_2_79_4
  | exact S 2 79 5 cell_2_79_5
theorem cell_2_80_0 : C 2 80 0 := by decide +kernel
theorem cell_2_80_1 : C 2 80 1 := by decide +kernel
theorem cell_2_80_2 : C 2 80 2 := by decide +kernel
theorem cell_2_80_3 : C 2 80 3 := by decide +kernel
theorem cell_2_80_4 : C 2 80 4 := by decide +kernel
theorem cell_2_80_5 : C 2 80 5 := by decide +kernel
theorem row_2_80 : ThresholdAt 2 80 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 80 0 cell_2_80_0
  | exact S 2 80 1 cell_2_80_1
  | exact S 2 80 2 cell_2_80_2
  | exact S 2 80 3 cell_2_80_3
  | exact S 2 80 4 cell_2_80_4
  | exact S 2 80 5 cell_2_80_5
theorem cell_2_81_0 : C 2 81 0 := by decide +kernel
theorem cell_2_81_1 : C 2 81 1 := by decide +kernel
theorem cell_2_81_2 : C 2 81 2 := by decide +kernel
theorem cell_2_81_3 : C 2 81 3 := by decide +kernel
theorem cell_2_81_4 : C 2 81 4 := by decide +kernel
theorem cell_2_81_5 : C 2 81 5 := by decide +kernel
theorem row_2_81 : ThresholdAt 2 81 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 81 0 cell_2_81_0
  | exact S 2 81 1 cell_2_81_1
  | exact S 2 81 2 cell_2_81_2
  | exact S 2 81 3 cell_2_81_3
  | exact S 2 81 4 cell_2_81_4
  | exact S 2 81 5 cell_2_81_5
theorem cell_2_82_0 : C 2 82 0 := by decide +kernel
theorem cell_2_82_1 : C 2 82 1 := by decide +kernel
theorem cell_2_82_2 : C 2 82 2 := by decide +kernel
theorem cell_2_82_3 : C 2 82 3 := by decide +kernel
theorem cell_2_82_4 : C 2 82 4 := by decide +kernel
theorem cell_2_82_5 : C 2 82 5 := by decide +kernel
theorem row_2_82 : ThresholdAt 2 82 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 82 0 cell_2_82_0
  | exact S 2 82 1 cell_2_82_1
  | exact S 2 82 2 cell_2_82_2
  | exact S 2 82 3 cell_2_82_3
  | exact S 2 82 4 cell_2_82_4
  | exact S 2 82 5 cell_2_82_5
theorem cell_2_83_0 : C 2 83 0 := by decide +kernel
theorem cell_2_83_1 : C 2 83 1 := by decide +kernel
theorem cell_2_83_2 : C 2 83 2 := by decide +kernel
theorem cell_2_83_3 : C 2 83 3 := by decide +kernel
theorem cell_2_83_4 : C 2 83 4 := by decide +kernel
theorem cell_2_83_5 : C 2 83 5 := by decide +kernel
theorem row_2_83 : ThresholdAt 2 83 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 83 0 cell_2_83_0
  | exact S 2 83 1 cell_2_83_1
  | exact S 2 83 2 cell_2_83_2
  | exact S 2 83 3 cell_2_83_3
  | exact S 2 83 4 cell_2_83_4
  | exact S 2 83 5 cell_2_83_5
theorem cell_2_84_0 : C 2 84 0 := by decide +kernel
theorem cell_2_84_1 : C 2 84 1 := by decide +kernel
theorem cell_2_84_2 : C 2 84 2 := by decide +kernel
theorem cell_2_84_3 : C 2 84 3 := by decide +kernel
theorem cell_2_84_4 : C 2 84 4 := by decide +kernel
theorem cell_2_84_5 : C 2 84 5 := by decide +kernel
theorem row_2_84 : ThresholdAt 2 84 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 84 0 cell_2_84_0
  | exact S 2 84 1 cell_2_84_1
  | exact S 2 84 2 cell_2_84_2
  | exact S 2 84 3 cell_2_84_3
  | exact S 2 84 4 cell_2_84_4
  | exact S 2 84 5 cell_2_84_5
theorem cell_2_85_0 : C 2 85 0 := by decide +kernel
theorem cell_2_85_1 : C 2 85 1 := by decide +kernel
theorem cell_2_85_2 : C 2 85 2 := by decide +kernel
theorem cell_2_85_3 : C 2 85 3 := by decide +kernel
theorem cell_2_85_4 : C 2 85 4 := by decide +kernel
theorem cell_2_85_5 : C 2 85 5 := by decide +kernel
theorem row_2_85 : ThresholdAt 2 85 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 85 0 cell_2_85_0
  | exact S 2 85 1 cell_2_85_1
  | exact S 2 85 2 cell_2_85_2
  | exact S 2 85 3 cell_2_85_3
  | exact S 2 85 4 cell_2_85_4
  | exact S 2 85 5 cell_2_85_5
theorem cell_2_86_0 : C 2 86 0 := by decide +kernel
theorem cell_2_86_1 : C 2 86 1 := by decide +kernel
theorem cell_2_86_2 : C 2 86 2 := by decide +kernel
theorem cell_2_86_3 : C 2 86 3 := by decide +kernel
theorem cell_2_86_4 : C 2 86 4 := by decide +kernel
theorem cell_2_86_5 : C 2 86 5 := by decide +kernel
theorem row_2_86 : ThresholdAt 2 86 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 86 0 cell_2_86_0
  | exact S 2 86 1 cell_2_86_1
  | exact S 2 86 2 cell_2_86_2
  | exact S 2 86 3 cell_2_86_3
  | exact S 2 86 4 cell_2_86_4
  | exact S 2 86 5 cell_2_86_5
theorem cell_2_87_0 : C 2 87 0 := by decide +kernel
theorem cell_2_87_1 : C 2 87 1 := by decide +kernel
theorem cell_2_87_2 : C 2 87 2 := by decide +kernel
theorem cell_2_87_3 : C 2 87 3 := by decide +kernel
theorem cell_2_87_4 : C 2 87 4 := by decide +kernel
theorem cell_2_87_5 : C 2 87 5 := by decide +kernel
theorem row_2_87 : ThresholdAt 2 87 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 87 0 cell_2_87_0
  | exact S 2 87 1 cell_2_87_1
  | exact S 2 87 2 cell_2_87_2
  | exact S 2 87 3 cell_2_87_3
  | exact S 2 87 4 cell_2_87_4
  | exact S 2 87 5 cell_2_87_5
theorem cell_2_88_0 : C 2 88 0 := by decide +kernel
theorem cell_2_88_1 : C 2 88 1 := by decide +kernel
theorem cell_2_88_2 : C 2 88 2 := by decide +kernel
theorem cell_2_88_3 : C 2 88 3 := by decide +kernel
theorem cell_2_88_4 : C 2 88 4 := by decide +kernel
theorem cell_2_88_5 : C 2 88 5 := by decide +kernel
theorem row_2_88 : ThresholdAt 2 88 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 88 0 cell_2_88_0
  | exact S 2 88 1 cell_2_88_1
  | exact S 2 88 2 cell_2_88_2
  | exact S 2 88 3 cell_2_88_3
  | exact S 2 88 4 cell_2_88_4
  | exact S 2 88 5 cell_2_88_5
theorem cell_2_89_0 : C 2 89 0 := by decide +kernel
theorem cell_2_89_1 : C 2 89 1 := by decide +kernel
theorem cell_2_89_2 : C 2 89 2 := by decide +kernel
theorem cell_2_89_3 : C 2 89 3 := by decide +kernel
theorem cell_2_89_4 : C 2 89 4 := by decide +kernel
theorem cell_2_89_5 : C 2 89 5 := by decide +kernel
theorem row_2_89 : ThresholdAt 2 89 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 89 0 cell_2_89_0
  | exact S 2 89 1 cell_2_89_1
  | exact S 2 89 2 cell_2_89_2
  | exact S 2 89 3 cell_2_89_3
  | exact S 2 89 4 cell_2_89_4
  | exact S 2 89 5 cell_2_89_5
theorem cell_2_90_0 : C 2 90 0 := by decide +kernel
theorem cell_2_90_1 : C 2 90 1 := by decide +kernel
theorem cell_2_90_2 : C 2 90 2 := by decide +kernel
theorem cell_2_90_3 : C 2 90 3 := by decide +kernel
theorem cell_2_90_4 : C 2 90 4 := by decide +kernel
theorem cell_2_90_5 : C 2 90 5 := by decide +kernel
theorem row_2_90 : ThresholdAt 2 90 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 90 0 cell_2_90_0
  | exact S 2 90 1 cell_2_90_1
  | exact S 2 90 2 cell_2_90_2
  | exact S 2 90 3 cell_2_90_3
  | exact S 2 90 4 cell_2_90_4
  | exact S 2 90 5 cell_2_90_5
theorem cell_2_91_0 : C 2 91 0 := by decide +kernel
theorem cell_2_91_1 : C 2 91 1 := by decide +kernel
theorem cell_2_91_2 : C 2 91 2 := by decide +kernel
theorem cell_2_91_3 : C 2 91 3 := by decide +kernel
theorem cell_2_91_4 : C 2 91 4 := by decide +kernel
theorem cell_2_91_5 : C 2 91 5 := by decide +kernel
theorem row_2_91 : ThresholdAt 2 91 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 91 0 cell_2_91_0
  | exact S 2 91 1 cell_2_91_1
  | exact S 2 91 2 cell_2_91_2
  | exact S 2 91 3 cell_2_91_3
  | exact S 2 91 4 cell_2_91_4
  | exact S 2 91 5 cell_2_91_5
theorem cell_2_92_0 : C 2 92 0 := by decide +kernel
theorem cell_2_92_1 : C 2 92 1 := by decide +kernel
theorem cell_2_92_2 : C 2 92 2 := by decide +kernel
theorem cell_2_92_3 : C 2 92 3 := by decide +kernel
theorem cell_2_92_4 : C 2 92 4 := by decide +kernel
theorem cell_2_92_5 : C 2 92 5 := by decide +kernel
theorem row_2_92 : ThresholdAt 2 92 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 92 0 cell_2_92_0
  | exact S 2 92 1 cell_2_92_1
  | exact S 2 92 2 cell_2_92_2
  | exact S 2 92 3 cell_2_92_3
  | exact S 2 92 4 cell_2_92_4
  | exact S 2 92 5 cell_2_92_5
theorem cell_2_93_0 : C 2 93 0 := by decide +kernel
theorem cell_2_93_1 : C 2 93 1 := by decide +kernel
theorem cell_2_93_2 : C 2 93 2 := by decide +kernel
theorem cell_2_93_3 : C 2 93 3 := by decide +kernel
theorem cell_2_93_4 : C 2 93 4 := by decide +kernel
theorem cell_2_93_5 : C 2 93 5 := by decide +kernel
theorem row_2_93 : ThresholdAt 2 93 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 93 0 cell_2_93_0
  | exact S 2 93 1 cell_2_93_1
  | exact S 2 93 2 cell_2_93_2
  | exact S 2 93 3 cell_2_93_3
  | exact S 2 93 4 cell_2_93_4
  | exact S 2 93 5 cell_2_93_5
theorem cell_2_94_0 : C 2 94 0 := by decide +kernel
theorem cell_2_94_1 : C 2 94 1 := by decide +kernel
theorem cell_2_94_2 : C 2 94 2 := by decide +kernel
theorem cell_2_94_3 : C 2 94 3 := by decide +kernel
theorem cell_2_94_4 : C 2 94 4 := by decide +kernel
theorem cell_2_94_5 : C 2 94 5 := by decide +kernel
theorem row_2_94 : ThresholdAt 2 94 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 94 0 cell_2_94_0
  | exact S 2 94 1 cell_2_94_1
  | exact S 2 94 2 cell_2_94_2
  | exact S 2 94 3 cell_2_94_3
  | exact S 2 94 4 cell_2_94_4
  | exact S 2 94 5 cell_2_94_5
theorem cell_2_95_0 : C 2 95 0 := by decide +kernel
theorem cell_2_95_1 : C 2 95 1 := by decide +kernel
theorem cell_2_95_2 : C 2 95 2 := by decide +kernel
theorem cell_2_95_3 : C 2 95 3 := by decide +kernel
theorem cell_2_95_4 : C 2 95 4 := by decide +kernel
theorem cell_2_95_5 : C 2 95 5 := by decide +kernel
theorem row_2_95 : ThresholdAt 2 95 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 95 0 cell_2_95_0
  | exact S 2 95 1 cell_2_95_1
  | exact S 2 95 2 cell_2_95_2
  | exact S 2 95 3 cell_2_95_3
  | exact S 2 95 4 cell_2_95_4
  | exact S 2 95 5 cell_2_95_5
theorem cell_2_96_0 : C 2 96 0 := by decide +kernel
theorem cell_2_96_1 : C 2 96 1 := by decide +kernel
theorem cell_2_96_2 : C 2 96 2 := by decide +kernel
theorem cell_2_96_3 : C 2 96 3 := by decide +kernel
theorem cell_2_96_4 : C 2 96 4 := by decide +kernel
theorem cell_2_96_5 : C 2 96 5 := by decide +kernel
theorem row_2_96 : ThresholdAt 2 96 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 96 0 cell_2_96_0
  | exact S 2 96 1 cell_2_96_1
  | exact S 2 96 2 cell_2_96_2
  | exact S 2 96 3 cell_2_96_3
  | exact S 2 96 4 cell_2_96_4
  | exact S 2 96 5 cell_2_96_5
theorem cell_2_97_0 : C 2 97 0 := by decide +kernel
theorem cell_2_97_1 : C 2 97 1 := by decide +kernel
theorem cell_2_97_2 : C 2 97 2 := by decide +kernel
theorem cell_2_97_3 : C 2 97 3 := by decide +kernel
theorem cell_2_97_4 : C 2 97 4 := by decide +kernel
theorem cell_2_97_5 : C 2 97 5 := by decide +kernel
theorem row_2_97 : ThresholdAt 2 97 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 97 0 cell_2_97_0
  | exact S 2 97 1 cell_2_97_1
  | exact S 2 97 2 cell_2_97_2
  | exact S 2 97 3 cell_2_97_3
  | exact S 2 97 4 cell_2_97_4
  | exact S 2 97 5 cell_2_97_5
theorem cell_2_98_0 : C 2 98 0 := by decide +kernel
theorem cell_2_98_1 : C 2 98 1 := by decide +kernel
theorem cell_2_98_2 : C 2 98 2 := by decide +kernel
theorem cell_2_98_3 : C 2 98 3 := by decide +kernel
theorem cell_2_98_4 : C 2 98 4 := by decide +kernel
theorem cell_2_98_5 : C 2 98 5 := by decide +kernel
theorem row_2_98 : ThresholdAt 2 98 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 98 0 cell_2_98_0
  | exact S 2 98 1 cell_2_98_1
  | exact S 2 98 2 cell_2_98_2
  | exact S 2 98 3 cell_2_98_3
  | exact S 2 98 4 cell_2_98_4
  | exact S 2 98 5 cell_2_98_5
theorem cell_2_99_0 : C 2 99 0 := by decide +kernel
theorem cell_2_99_1 : C 2 99 1 := by decide +kernel
theorem cell_2_99_2 : C 2 99 2 := by decide +kernel
theorem cell_2_99_3 : C 2 99 3 := by decide +kernel
theorem cell_2_99_4 : C 2 99 4 := by decide +kernel
theorem cell_2_99_5 : C 2 99 5 := by decide +kernel
theorem row_2_99 : ThresholdAt 2 99 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 99 0 cell_2_99_0
  | exact S 2 99 1 cell_2_99_1
  | exact S 2 99 2 cell_2_99_2
  | exact S 2 99 3 cell_2_99_3
  | exact S 2 99 4 cell_2_99_4
  | exact S 2 99 5 cell_2_99_5
theorem cell_2_100_0 : C 2 100 0 := by decide +kernel
theorem cell_2_100_1 : C 2 100 1 := by decide +kernel
theorem cell_2_100_2 : C 2 100 2 := by decide +kernel
theorem cell_2_100_3 : C 2 100 3 := by decide +kernel
theorem cell_2_100_4 : C 2 100 4 := by decide +kernel
theorem cell_2_100_5 : C 2 100 5 := by decide +kernel
theorem row_2_100 : ThresholdAt 2 100 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 100 0 cell_2_100_0
  | exact S 2 100 1 cell_2_100_1
  | exact S 2 100 2 cell_2_100_2
  | exact S 2 100 3 cell_2_100_3
  | exact S 2 100 4 cell_2_100_4
  | exact S 2 100 5 cell_2_100_5
theorem cell_2_101_0 : C 2 101 0 := by decide +kernel
theorem cell_2_101_1 : C 2 101 1 := by decide +kernel
theorem cell_2_101_2 : C 2 101 2 := by decide +kernel
theorem cell_2_101_3 : C 2 101 3 := by decide +kernel
theorem cell_2_101_4 : C 2 101 4 := by decide +kernel
theorem cell_2_101_5 : C 2 101 5 := by decide +kernel
theorem row_2_101 : ThresholdAt 2 101 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 101 0 cell_2_101_0
  | exact S 2 101 1 cell_2_101_1
  | exact S 2 101 2 cell_2_101_2
  | exact S 2 101 3 cell_2_101_3
  | exact S 2 101 4 cell_2_101_4
  | exact S 2 101 5 cell_2_101_5
theorem cell_2_102_0 : C 2 102 0 := by decide +kernel
theorem cell_2_102_1 : C 2 102 1 := by decide +kernel
theorem cell_2_102_2 : C 2 102 2 := by decide +kernel
theorem cell_2_102_3 : C 2 102 3 := by decide +kernel
theorem cell_2_102_4 : C 2 102 4 := by decide +kernel
theorem cell_2_102_5 : C 2 102 5 := by decide +kernel
theorem row_2_102 : ThresholdAt 2 102 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 102 0 cell_2_102_0
  | exact S 2 102 1 cell_2_102_1
  | exact S 2 102 2 cell_2_102_2
  | exact S 2 102 3 cell_2_102_3
  | exact S 2 102 4 cell_2_102_4
  | exact S 2 102 5 cell_2_102_5
theorem cell_2_103_0 : C 2 103 0 := by decide +kernel
theorem cell_2_103_1 : C 2 103 1 := by decide +kernel
theorem cell_2_103_2 : C 2 103 2 := by decide +kernel
theorem cell_2_103_3 : C 2 103 3 := by decide +kernel
theorem cell_2_103_4 : C 2 103 4 := by decide +kernel
theorem cell_2_103_5 : C 2 103 5 := by decide +kernel
theorem row_2_103 : ThresholdAt 2 103 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 103 0 cell_2_103_0
  | exact S 2 103 1 cell_2_103_1
  | exact S 2 103 2 cell_2_103_2
  | exact S 2 103 3 cell_2_103_3
  | exact S 2 103 4 cell_2_103_4
  | exact S 2 103 5 cell_2_103_5
theorem cell_2_104_0 : C 2 104 0 := by decide +kernel
theorem cell_2_104_1 : C 2 104 1 := by decide +kernel
theorem cell_2_104_2 : C 2 104 2 := by decide +kernel
theorem cell_2_104_3 : C 2 104 3 := by decide +kernel
theorem cell_2_104_4 : C 2 104 4 := by decide +kernel
theorem cell_2_104_5 : C 2 104 5 := by decide +kernel
theorem row_2_104 : ThresholdAt 2 104 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 104 0 cell_2_104_0
  | exact S 2 104 1 cell_2_104_1
  | exact S 2 104 2 cell_2_104_2
  | exact S 2 104 3 cell_2_104_3
  | exact S 2 104 4 cell_2_104_4
  | exact S 2 104 5 cell_2_104_5
theorem cell_2_105_0 : C 2 105 0 := by decide +kernel
theorem cell_2_105_1 : C 2 105 1 := by decide +kernel
theorem cell_2_105_2 : C 2 105 2 := by decide +kernel
theorem cell_2_105_3 : C 2 105 3 := by decide +kernel
theorem cell_2_105_4 : C 2 105 4 := by decide +kernel
theorem cell_2_105_5 : C 2 105 5 := by decide +kernel
theorem row_2_105 : ThresholdAt 2 105 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 105 0 cell_2_105_0
  | exact S 2 105 1 cell_2_105_1
  | exact S 2 105 2 cell_2_105_2
  | exact S 2 105 3 cell_2_105_3
  | exact S 2 105 4 cell_2_105_4
  | exact S 2 105 5 cell_2_105_5
theorem cell_2_106_0 : C 2 106 0 := by decide +kernel
theorem cell_2_106_1 : C 2 106 1 := by decide +kernel
theorem cell_2_106_2 : C 2 106 2 := by decide +kernel
theorem cell_2_106_3 : C 2 106 3 := by decide +kernel
theorem cell_2_106_4 : C 2 106 4 := by decide +kernel
theorem cell_2_106_5 : C 2 106 5 := by decide +kernel
theorem row_2_106 : ThresholdAt 2 106 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 106 0 cell_2_106_0
  | exact S 2 106 1 cell_2_106_1
  | exact S 2 106 2 cell_2_106_2
  | exact S 2 106 3 cell_2_106_3
  | exact S 2 106 4 cell_2_106_4
  | exact S 2 106 5 cell_2_106_5
theorem cell_2_107_0 : C 2 107 0 := by decide +kernel
theorem cell_2_107_1 : C 2 107 1 := by decide +kernel
theorem cell_2_107_2 : C 2 107 2 := by decide +kernel
theorem cell_2_107_3 : C 2 107 3 := by decide +kernel
theorem cell_2_107_4 : C 2 107 4 := by decide +kernel
theorem cell_2_107_5 : C 2 107 5 := by decide +kernel
theorem row_2_107 : ThresholdAt 2 107 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 107 0 cell_2_107_0
  | exact S 2 107 1 cell_2_107_1
  | exact S 2 107 2 cell_2_107_2
  | exact S 2 107 3 cell_2_107_3
  | exact S 2 107 4 cell_2_107_4
  | exact S 2 107 5 cell_2_107_5
theorem cell_2_108_0 : C 2 108 0 := by decide +kernel
theorem cell_2_108_1 : C 2 108 1 := by decide +kernel
theorem cell_2_108_2 : C 2 108 2 := by decide +kernel
theorem cell_2_108_3 : C 2 108 3 := by decide +kernel
theorem cell_2_108_4 : C 2 108 4 := by decide +kernel
theorem cell_2_108_5 : C 2 108 5 := by decide +kernel
theorem row_2_108 : ThresholdAt 2 108 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 108 0 cell_2_108_0
  | exact S 2 108 1 cell_2_108_1
  | exact S 2 108 2 cell_2_108_2
  | exact S 2 108 3 cell_2_108_3
  | exact S 2 108 4 cell_2_108_4
  | exact S 2 108 5 cell_2_108_5
theorem cell_2_109_0 : C 2 109 0 := by decide +kernel
theorem cell_2_109_1 : C 2 109 1 := by decide +kernel
theorem cell_2_109_2 : C 2 109 2 := by decide +kernel
theorem cell_2_109_3 : C 2 109 3 := by decide +kernel
theorem cell_2_109_4 : C 2 109 4 := by decide +kernel
theorem cell_2_109_5 : C 2 109 5 := by decide +kernel
theorem row_2_109 : ThresholdAt 2 109 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 109 0 cell_2_109_0
  | exact S 2 109 1 cell_2_109_1
  | exact S 2 109 2 cell_2_109_2
  | exact S 2 109 3 cell_2_109_3
  | exact S 2 109 4 cell_2_109_4
  | exact S 2 109 5 cell_2_109_5
theorem cell_2_110_0 : C 2 110 0 := by decide +kernel
theorem cell_2_110_1 : C 2 110 1 := by decide +kernel
theorem cell_2_110_2 : C 2 110 2 := by decide +kernel
theorem cell_2_110_3 : C 2 110 3 := by decide +kernel
theorem cell_2_110_4 : C 2 110 4 := by decide +kernel
theorem cell_2_110_5 : C 2 110 5 := by decide +kernel
theorem row_2_110 : ThresholdAt 2 110 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 110 0 cell_2_110_0
  | exact S 2 110 1 cell_2_110_1
  | exact S 2 110 2 cell_2_110_2
  | exact S 2 110 3 cell_2_110_3
  | exact S 2 110 4 cell_2_110_4
  | exact S 2 110 5 cell_2_110_5
theorem cell_2_111_0 : C 2 111 0 := by decide +kernel
theorem cell_2_111_1 : C 2 111 1 := by decide +kernel
theorem cell_2_111_2 : C 2 111 2 := by decide +kernel
theorem cell_2_111_3 : C 2 111 3 := by decide +kernel
theorem cell_2_111_4 : C 2 111 4 := by decide +kernel
theorem cell_2_111_5 : C 2 111 5 := by decide +kernel
theorem row_2_111 : ThresholdAt 2 111 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 111 0 cell_2_111_0
  | exact S 2 111 1 cell_2_111_1
  | exact S 2 111 2 cell_2_111_2
  | exact S 2 111 3 cell_2_111_3
  | exact S 2 111 4 cell_2_111_4
  | exact S 2 111 5 cell_2_111_5
theorem cell_2_112_0 : C 2 112 0 := by decide +kernel
theorem cell_2_112_1 : C 2 112 1 := by decide +kernel
theorem cell_2_112_2 : C 2 112 2 := by decide +kernel
theorem cell_2_112_3 : C 2 112 3 := by decide +kernel
theorem cell_2_112_4 : C 2 112 4 := by decide +kernel
theorem cell_2_112_5 : C 2 112 5 := by decide +kernel
theorem row_2_112 : ThresholdAt 2 112 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 112 0 cell_2_112_0
  | exact S 2 112 1 cell_2_112_1
  | exact S 2 112 2 cell_2_112_2
  | exact S 2 112 3 cell_2_112_3
  | exact S 2 112 4 cell_2_112_4
  | exact S 2 112 5 cell_2_112_5
theorem cell_2_113_0 : C 2 113 0 := by decide +kernel
theorem cell_2_113_1 : C 2 113 1 := by decide +kernel
theorem cell_2_113_2 : C 2 113 2 := by decide +kernel
theorem cell_2_113_3 : C 2 113 3 := by decide +kernel
theorem cell_2_113_4 : C 2 113 4 := by decide +kernel
theorem cell_2_113_5 : C 2 113 5 := by decide +kernel
theorem row_2_113 : ThresholdAt 2 113 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 113 0 cell_2_113_0
  | exact S 2 113 1 cell_2_113_1
  | exact S 2 113 2 cell_2_113_2
  | exact S 2 113 3 cell_2_113_3
  | exact S 2 113 4 cell_2_113_4
  | exact S 2 113 5 cell_2_113_5
theorem cell_2_114_0 : C 2 114 0 := by decide +kernel
theorem cell_2_114_1 : C 2 114 1 := by decide +kernel
theorem cell_2_114_2 : C 2 114 2 := by decide +kernel
theorem cell_2_114_3 : C 2 114 3 := by decide +kernel
theorem cell_2_114_4 : C 2 114 4 := by decide +kernel
theorem cell_2_114_5 : C 2 114 5 := by decide +kernel
theorem row_2_114 : ThresholdAt 2 114 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 114 0 cell_2_114_0
  | exact S 2 114 1 cell_2_114_1
  | exact S 2 114 2 cell_2_114_2
  | exact S 2 114 3 cell_2_114_3
  | exact S 2 114 4 cell_2_114_4
  | exact S 2 114 5 cell_2_114_5
theorem cell_2_115_0 : C 2 115 0 := by decide +kernel
theorem cell_2_115_1 : C 2 115 1 := by decide +kernel
theorem cell_2_115_2 : C 2 115 2 := by decide +kernel
theorem cell_2_115_3 : C 2 115 3 := by decide +kernel
theorem cell_2_115_4 : C 2 115 4 := by decide +kernel
theorem cell_2_115_5 : C 2 115 5 := by decide +kernel
theorem row_2_115 : ThresholdAt 2 115 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 115 0 cell_2_115_0
  | exact S 2 115 1 cell_2_115_1
  | exact S 2 115 2 cell_2_115_2
  | exact S 2 115 3 cell_2_115_3
  | exact S 2 115 4 cell_2_115_4
  | exact S 2 115 5 cell_2_115_5
theorem cell_2_116_0 : C 2 116 0 := by decide +kernel
theorem cell_2_116_1 : C 2 116 1 := by decide +kernel
theorem cell_2_116_2 : C 2 116 2 := by decide +kernel
theorem cell_2_116_3 : C 2 116 3 := by decide +kernel
theorem cell_2_116_4 : C 2 116 4 := by decide +kernel
theorem cell_2_116_5 : C 2 116 5 := by decide +kernel
theorem row_2_116 : ThresholdAt 2 116 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 116 0 cell_2_116_0
  | exact S 2 116 1 cell_2_116_1
  | exact S 2 116 2 cell_2_116_2
  | exact S 2 116 3 cell_2_116_3
  | exact S 2 116 4 cell_2_116_4
  | exact S 2 116 5 cell_2_116_5
theorem cell_2_117_0 : C 2 117 0 := by decide +kernel
theorem cell_2_117_1 : C 2 117 1 := by decide +kernel
theorem cell_2_117_2 : C 2 117 2 := by decide +kernel
theorem cell_2_117_3 : C 2 117 3 := by decide +kernel
theorem cell_2_117_4 : C 2 117 4 := by decide +kernel
theorem cell_2_117_5 : C 2 117 5 := by decide +kernel
theorem row_2_117 : ThresholdAt 2 117 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 117 0 cell_2_117_0
  | exact S 2 117 1 cell_2_117_1
  | exact S 2 117 2 cell_2_117_2
  | exact S 2 117 3 cell_2_117_3
  | exact S 2 117 4 cell_2_117_4
  | exact S 2 117 5 cell_2_117_5
theorem cell_2_118_0 : C 2 118 0 := by decide +kernel
theorem cell_2_118_1 : C 2 118 1 := by decide +kernel
theorem cell_2_118_2 : C 2 118 2 := by decide +kernel
theorem cell_2_118_3 : C 2 118 3 := by decide +kernel
theorem cell_2_118_4 : C 2 118 4 := by decide +kernel
theorem cell_2_118_5 : C 2 118 5 := by decide +kernel
theorem row_2_118 : ThresholdAt 2 118 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 118 0 cell_2_118_0
  | exact S 2 118 1 cell_2_118_1
  | exact S 2 118 2 cell_2_118_2
  | exact S 2 118 3 cell_2_118_3
  | exact S 2 118 4 cell_2_118_4
  | exact S 2 118 5 cell_2_118_5
theorem cell_2_119_0 : C 2 119 0 := by decide +kernel
theorem cell_2_119_1 : C 2 119 1 := by decide +kernel
theorem cell_2_119_2 : C 2 119 2 := by decide +kernel
theorem cell_2_119_3 : C 2 119 3 := by decide +kernel
theorem cell_2_119_4 : C 2 119 4 := by decide +kernel
theorem cell_2_119_5 : C 2 119 5 := by decide +kernel
theorem row_2_119 : ThresholdAt 2 119 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 119 0 cell_2_119_0
  | exact S 2 119 1 cell_2_119_1
  | exact S 2 119 2 cell_2_119_2
  | exact S 2 119 3 cell_2_119_3
  | exact S 2 119 4 cell_2_119_4
  | exact S 2 119 5 cell_2_119_5
theorem cell_2_120_0 : C 2 120 0 := by decide +kernel
theorem cell_2_120_1 : C 2 120 1 := by decide +kernel
theorem cell_2_120_2 : C 2 120 2 := by decide +kernel
theorem cell_2_120_3 : C 2 120 3 := by decide +kernel
theorem cell_2_120_4 : C 2 120 4 := by decide +kernel
theorem cell_2_120_5 : C 2 120 5 := by decide +kernel
theorem row_2_120 : ThresholdAt 2 120 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 120 0 cell_2_120_0
  | exact S 2 120 1 cell_2_120_1
  | exact S 2 120 2 cell_2_120_2
  | exact S 2 120 3 cell_2_120_3
  | exact S 2 120 4 cell_2_120_4
  | exact S 2 120 5 cell_2_120_5
theorem cell_2_121_0 : C 2 121 0 := by decide +kernel
theorem cell_2_121_1 : C 2 121 1 := by decide +kernel
theorem cell_2_121_2 : C 2 121 2 := by decide +kernel
theorem cell_2_121_3 : C 2 121 3 := by decide +kernel
theorem cell_2_121_4 : C 2 121 4 := by decide +kernel
theorem cell_2_121_5 : C 2 121 5 := by decide +kernel
theorem row_2_121 : ThresholdAt 2 121 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 121 0 cell_2_121_0
  | exact S 2 121 1 cell_2_121_1
  | exact S 2 121 2 cell_2_121_2
  | exact S 2 121 3 cell_2_121_3
  | exact S 2 121 4 cell_2_121_4
  | exact S 2 121 5 cell_2_121_5
theorem cell_2_122_0 : C 2 122 0 := by decide +kernel
theorem cell_2_122_1 : C 2 122 1 := by decide +kernel
theorem cell_2_122_2 : C 2 122 2 := by decide +kernel
theorem cell_2_122_3 : C 2 122 3 := by decide +kernel
theorem cell_2_122_4 : C 2 122 4 := by decide +kernel
theorem cell_2_122_5 : C 2 122 5 := by decide +kernel
theorem row_2_122 : ThresholdAt 2 122 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 122 0 cell_2_122_0
  | exact S 2 122 1 cell_2_122_1
  | exact S 2 122 2 cell_2_122_2
  | exact S 2 122 3 cell_2_122_3
  | exact S 2 122 4 cell_2_122_4
  | exact S 2 122 5 cell_2_122_5
theorem cell_2_123_0 : C 2 123 0 := by decide +kernel
theorem cell_2_123_1 : C 2 123 1 := by decide +kernel
theorem cell_2_123_2 : C 2 123 2 := by decide +kernel
theorem cell_2_123_3 : C 2 123 3 := by decide +kernel
theorem cell_2_123_4 : C 2 123 4 := by decide +kernel
theorem cell_2_123_5 : C 2 123 5 := by decide +kernel
theorem row_2_123 : ThresholdAt 2 123 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 123 0 cell_2_123_0
  | exact S 2 123 1 cell_2_123_1
  | exact S 2 123 2 cell_2_123_2
  | exact S 2 123 3 cell_2_123_3
  | exact S 2 123 4 cell_2_123_4
  | exact S 2 123 5 cell_2_123_5
theorem cell_2_124_0 : C 2 124 0 := by decide +kernel
theorem cell_2_124_1 : C 2 124 1 := by decide +kernel
theorem cell_2_124_2 : C 2 124 2 := by decide +kernel
theorem cell_2_124_3 : C 2 124 3 := by decide +kernel
theorem cell_2_124_4 : C 2 124 4 := by decide +kernel
theorem cell_2_124_5 : C 2 124 5 := by decide +kernel
theorem row_2_124 : ThresholdAt 2 124 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 124 0 cell_2_124_0
  | exact S 2 124 1 cell_2_124_1
  | exact S 2 124 2 cell_2_124_2
  | exact S 2 124 3 cell_2_124_3
  | exact S 2 124 4 cell_2_124_4
  | exact S 2 124 5 cell_2_124_5
theorem cell_2_125_0 : C 2 125 0 := by decide +kernel
theorem cell_2_125_1 : C 2 125 1 := by decide +kernel
theorem cell_2_125_2 : C 2 125 2 := by decide +kernel
theorem cell_2_125_3 : C 2 125 3 := by decide +kernel
theorem cell_2_125_4 : C 2 125 4 := by decide +kernel
theorem cell_2_125_5 : C 2 125 5 := by decide +kernel
theorem row_2_125 : ThresholdAt 2 125 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 125 0 cell_2_125_0
  | exact S 2 125 1 cell_2_125_1
  | exact S 2 125 2 cell_2_125_2
  | exact S 2 125 3 cell_2_125_3
  | exact S 2 125 4 cell_2_125_4
  | exact S 2 125 5 cell_2_125_5
theorem cell_2_126_0 : C 2 126 0 := by decide +kernel
theorem cell_2_126_1 : C 2 126 1 := by decide +kernel
theorem cell_2_126_2 : C 2 126 2 := by decide +kernel
theorem cell_2_126_3 : C 2 126 3 := by decide +kernel
theorem cell_2_126_4 : C 2 126 4 := by decide +kernel
theorem cell_2_126_5 : C 2 126 5 := by decide +kernel
theorem row_2_126 : ThresholdAt 2 126 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 126 0 cell_2_126_0
  | exact S 2 126 1 cell_2_126_1
  | exact S 2 126 2 cell_2_126_2
  | exact S 2 126 3 cell_2_126_3
  | exact S 2 126 4 cell_2_126_4
  | exact S 2 126 5 cell_2_126_5
theorem cell_2_127_0 : C 2 127 0 := by decide +kernel
theorem cell_2_127_1 : C 2 127 1 := by decide +kernel
theorem cell_2_127_2 : C 2 127 2 := by decide +kernel
theorem cell_2_127_3 : C 2 127 3 := by decide +kernel
theorem cell_2_127_4 : C 2 127 4 := by decide +kernel
theorem cell_2_127_5 : C 2 127 5 := by decide +kernel
theorem row_2_127 : ThresholdAt 2 127 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 127 0 cell_2_127_0
  | exact S 2 127 1 cell_2_127_1
  | exact S 2 127 2 cell_2_127_2
  | exact S 2 127 3 cell_2_127_3
  | exact S 2 127 4 cell_2_127_4
  | exact S 2 127 5 cell_2_127_5
theorem cell_2_128_0 : C 2 128 0 := by decide +kernel
theorem cell_2_128_1 : C 2 128 1 := by decide +kernel
theorem cell_2_128_2 : C 2 128 2 := by decide +kernel
theorem cell_2_128_3 : C 2 128 3 := by decide +kernel
theorem cell_2_128_4 : C 2 128 4 := by decide +kernel
theorem cell_2_128_5 : C 2 128 5 := by decide +kernel
theorem row_2_128 : ThresholdAt 2 128 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 128 0 cell_2_128_0
  | exact S 2 128 1 cell_2_128_1
  | exact S 2 128 2 cell_2_128_2
  | exact S 2 128 3 cell_2_128_3
  | exact S 2 128 4 cell_2_128_4
  | exact S 2 128 5 cell_2_128_5
theorem cell_2_129_0 : C 2 129 0 := by decide +kernel
theorem cell_2_129_1 : C 2 129 1 := by decide +kernel
theorem cell_2_129_2 : C 2 129 2 := by decide +kernel
theorem cell_2_129_3 : C 2 129 3 := by decide +kernel
theorem cell_2_129_4 : C 2 129 4 := by decide +kernel
theorem cell_2_129_5 : C 2 129 5 := by decide +kernel
theorem row_2_129 : ThresholdAt 2 129 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 129 0 cell_2_129_0
  | exact S 2 129 1 cell_2_129_1
  | exact S 2 129 2 cell_2_129_2
  | exact S 2 129 3 cell_2_129_3
  | exact S 2 129 4 cell_2_129_4
  | exact S 2 129 5 cell_2_129_5
theorem cell_2_130_0 : C 2 130 0 := by decide +kernel
theorem cell_2_130_1 : C 2 130 1 := by decide +kernel
theorem cell_2_130_2 : C 2 130 2 := by decide +kernel
theorem cell_2_130_3 : C 2 130 3 := by decide +kernel
theorem cell_2_130_4 : C 2 130 4 := by decide +kernel
theorem cell_2_130_5 : C 2 130 5 := by decide +kernel
theorem row_2_130 : ThresholdAt 2 130 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 130 0 cell_2_130_0
  | exact S 2 130 1 cell_2_130_1
  | exact S 2 130 2 cell_2_130_2
  | exact S 2 130 3 cell_2_130_3
  | exact S 2 130 4 cell_2_130_4
  | exact S 2 130 5 cell_2_130_5
theorem cell_2_131_0 : C 2 131 0 := by decide +kernel
theorem cell_2_131_1 : C 2 131 1 := by decide +kernel
theorem cell_2_131_2 : C 2 131 2 := by decide +kernel
theorem cell_2_131_3 : C 2 131 3 := by decide +kernel
theorem cell_2_131_4 : C 2 131 4 := by decide +kernel
theorem cell_2_131_5 : C 2 131 5 := by decide +kernel
theorem row_2_131 : ThresholdAt 2 131 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 131 0 cell_2_131_0
  | exact S 2 131 1 cell_2_131_1
  | exact S 2 131 2 cell_2_131_2
  | exact S 2 131 3 cell_2_131_3
  | exact S 2 131 4 cell_2_131_4
  | exact S 2 131 5 cell_2_131_5
theorem cell_2_132_0 : C 2 132 0 := by decide +kernel
theorem cell_2_132_1 : C 2 132 1 := by decide +kernel
theorem cell_2_132_2 : C 2 132 2 := by decide +kernel
theorem cell_2_132_3 : C 2 132 3 := by decide +kernel
theorem cell_2_132_4 : C 2 132 4 := by decide +kernel
theorem cell_2_132_5 : C 2 132 5 := by decide +kernel
theorem row_2_132 : ThresholdAt 2 132 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 132 0 cell_2_132_0
  | exact S 2 132 1 cell_2_132_1
  | exact S 2 132 2 cell_2_132_2
  | exact S 2 132 3 cell_2_132_3
  | exact S 2 132 4 cell_2_132_4
  | exact S 2 132 5 cell_2_132_5
theorem cell_2_133_0 : C 2 133 0 := by decide +kernel
theorem cell_2_133_1 : C 2 133 1 := by decide +kernel
theorem cell_2_133_2 : C 2 133 2 := by decide +kernel
theorem cell_2_133_3 : C 2 133 3 := by decide +kernel
theorem cell_2_133_4 : C 2 133 4 := by decide +kernel
theorem cell_2_133_5 : C 2 133 5 := by decide +kernel
theorem row_2_133 : ThresholdAt 2 133 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 133 0 cell_2_133_0
  | exact S 2 133 1 cell_2_133_1
  | exact S 2 133 2 cell_2_133_2
  | exact S 2 133 3 cell_2_133_3
  | exact S 2 133 4 cell_2_133_4
  | exact S 2 133 5 cell_2_133_5
theorem cell_2_134_0 : C 2 134 0 := by decide +kernel
theorem cell_2_134_1 : C 2 134 1 := by decide +kernel
theorem cell_2_134_2 : C 2 134 2 := by decide +kernel
theorem cell_2_134_3 : C 2 134 3 := by decide +kernel
theorem cell_2_134_4 : C 2 134 4 := by decide +kernel
theorem cell_2_134_5 : C 2 134 5 := by decide +kernel
theorem row_2_134 : ThresholdAt 2 134 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 134 0 cell_2_134_0
  | exact S 2 134 1 cell_2_134_1
  | exact S 2 134 2 cell_2_134_2
  | exact S 2 134 3 cell_2_134_3
  | exact S 2 134 4 cell_2_134_4
  | exact S 2 134 5 cell_2_134_5
theorem cell_2_135_0 : C 2 135 0 := by decide +kernel
theorem cell_2_135_1 : C 2 135 1 := by decide +kernel
theorem cell_2_135_2 : C 2 135 2 := by decide +kernel
theorem cell_2_135_3 : C 2 135 3 := by decide +kernel
theorem cell_2_135_4 : C 2 135 4 := by decide +kernel
theorem cell_2_135_5 : C 2 135 5 := by decide +kernel
theorem row_2_135 : ThresholdAt 2 135 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 135 0 cell_2_135_0
  | exact S 2 135 1 cell_2_135_1
  | exact S 2 135 2 cell_2_135_2
  | exact S 2 135 3 cell_2_135_3
  | exact S 2 135 4 cell_2_135_4
  | exact S 2 135 5 cell_2_135_5
theorem cell_2_136_0 : C 2 136 0 := by decide +kernel
theorem cell_2_136_1 : C 2 136 1 := by decide +kernel
theorem cell_2_136_2 : C 2 136 2 := by decide +kernel
theorem cell_2_136_3 : C 2 136 3 := by decide +kernel
theorem cell_2_136_4 : C 2 136 4 := by decide +kernel
theorem cell_2_136_5 : C 2 136 5 := by decide +kernel
theorem row_2_136 : ThresholdAt 2 136 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 136 0 cell_2_136_0
  | exact S 2 136 1 cell_2_136_1
  | exact S 2 136 2 cell_2_136_2
  | exact S 2 136 3 cell_2_136_3
  | exact S 2 136 4 cell_2_136_4
  | exact S 2 136 5 cell_2_136_5
theorem cell_2_137_0 : C 2 137 0 := by decide +kernel
theorem cell_2_137_1 : C 2 137 1 := by decide +kernel
theorem cell_2_137_2 : C 2 137 2 := by decide +kernel
theorem cell_2_137_3 : C 2 137 3 := by decide +kernel
theorem cell_2_137_4 : C 2 137 4 := by decide +kernel
theorem cell_2_137_5 : C 2 137 5 := by decide +kernel
theorem row_2_137 : ThresholdAt 2 137 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 2 137 0 cell_2_137_0
  | exact S 2 137 1 cell_2_137_1
  | exact S 2 137 2 cell_2_137_2
  | exact S 2 137 3 cell_2_137_3
  | exact S 2 137 4 cell_2_137_4
  | exact S 2 137 5 cell_2_137_5
theorem checkedR2 : ∀ V ∈ List.range 138, ThresholdAt 2 V := by
  intro V hV
  have hv : V < 138 := List.mem_range.mp hV
  by_cases h0_138 : V < 69
  · by_cases h0_69 : V < 34
    · by_cases h0_34 : V < 17
      · by_cases h0_17 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have he : V = 0 := by omega
                subst V
                exact row_2_0
              · have he : V = 1 := by omega
                subst V
                exact row_2_1
            · by_cases h2_4 : V < 3
              · have he : V = 2 := by omega
                subst V
                exact row_2_2
              · have he : V = 3 := by omega
                subst V
                exact row_2_3
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have he : V = 4 := by omega
                subst V
                exact row_2_4
              · have he : V = 5 := by omega
                subst V
                exact row_2_5
            · by_cases h6_8 : V < 7
              · have he : V = 6 := by omega
                subst V
                exact row_2_6
              · have he : V = 7 := by omega
                subst V
                exact row_2_7
        · by_cases h8_17 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have he : V = 8 := by omega
                subst V
                exact row_2_8
              · have he : V = 9 := by omega
                subst V
                exact row_2_9
            · by_cases h10_12 : V < 11
              · have he : V = 10 := by omega
                subst V
                exact row_2_10
              · have he : V = 11 := by omega
                subst V
                exact row_2_11
          · by_cases h12_17 : V < 14
            · by_cases h12_14 : V < 13
              · have he : V = 12 := by omega
                subst V
                exact row_2_12
              · have he : V = 13 := by omega
                subst V
                exact row_2_13
            · by_cases h14_17 : V < 15
              · have he : V = 14 := by omega
                subst V
                exact row_2_14
              · by_cases h15_17 : V < 16
                · have he : V = 15 := by omega
                  subst V
                  exact row_2_15
                · have he : V = 16 := by omega
                  subst V
                  exact row_2_16
      · by_cases h17_34 : V < 25
        · by_cases h17_25 : V < 21
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have he : V = 17 := by omega
                subst V
                exact row_2_17
              · have he : V = 18 := by omega
                subst V
                exact row_2_18
            · by_cases h19_21 : V < 20
              · have he : V = 19 := by omega
                subst V
                exact row_2_19
              · have he : V = 20 := by omega
                subst V
                exact row_2_20
          · by_cases h21_25 : V < 23
            · by_cases h21_23 : V < 22
              · have he : V = 21 := by omega
                subst V
                exact row_2_21
              · have he : V = 22 := by omega
                subst V
                exact row_2_22
            · by_cases h23_25 : V < 24
              · have he : V = 23 := by omega
                subst V
                exact row_2_23
              · have he : V = 24 := by omega
                subst V
                exact row_2_24
        · by_cases h25_34 : V < 29
          · by_cases h25_29 : V < 27
            · by_cases h25_27 : V < 26
              · have he : V = 25 := by omega
                subst V
                exact row_2_25
              · have he : V = 26 := by omega
                subst V
                exact row_2_26
            · by_cases h27_29 : V < 28
              · have he : V = 27 := by omega
                subst V
                exact row_2_27
              · have he : V = 28 := by omega
                subst V
                exact row_2_28
          · by_cases h29_34 : V < 31
            · by_cases h29_31 : V < 30
              · have he : V = 29 := by omega
                subst V
                exact row_2_29
              · have he : V = 30 := by omega
                subst V
                exact row_2_30
            · by_cases h31_34 : V < 32
              · have he : V = 31 := by omega
                subst V
                exact row_2_31
              · by_cases h32_34 : V < 33
                · have he : V = 32 := by omega
                  subst V
                  exact row_2_32
                · have he : V = 33 := by omega
                  subst V
                  exact row_2_33
    · by_cases h34_69 : V < 51
      · by_cases h34_51 : V < 42
        · by_cases h34_42 : V < 38
          · by_cases h34_38 : V < 36
            · by_cases h34_36 : V < 35
              · have he : V = 34 := by omega
                subst V
                exact row_2_34
              · have he : V = 35 := by omega
                subst V
                exact row_2_35
            · by_cases h36_38 : V < 37
              · have he : V = 36 := by omega
                subst V
                exact row_2_36
              · have he : V = 37 := by omega
                subst V
                exact row_2_37
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have he : V = 38 := by omega
                subst V
                exact row_2_38
              · have he : V = 39 := by omega
                subst V
                exact row_2_39
            · by_cases h40_42 : V < 41
              · have he : V = 40 := by omega
                subst V
                exact row_2_40
              · have he : V = 41 := by omega
                subst V
                exact row_2_41
        · by_cases h42_51 : V < 46
          · by_cases h42_46 : V < 44
            · by_cases h42_44 : V < 43
              · have he : V = 42 := by omega
                subst V
                exact row_2_42
              · have he : V = 43 := by omega
                subst V
                exact row_2_43
            · by_cases h44_46 : V < 45
              · have he : V = 44 := by omega
                subst V
                exact row_2_44
              · have he : V = 45 := by omega
                subst V
                exact row_2_45
          · by_cases h46_51 : V < 48
            · by_cases h46_48 : V < 47
              · have he : V = 46 := by omega
                subst V
                exact row_2_46
              · have he : V = 47 := by omega
                subst V
                exact row_2_47
            · by_cases h48_51 : V < 49
              · have he : V = 48 := by omega
                subst V
                exact row_2_48
              · by_cases h49_51 : V < 50
                · have he : V = 49 := by omega
                  subst V
                  exact row_2_49
                · have he : V = 50 := by omega
                  subst V
                  exact row_2_50
      · by_cases h51_69 : V < 60
        · by_cases h51_60 : V < 55
          · by_cases h51_55 : V < 53
            · by_cases h51_53 : V < 52
              · have he : V = 51 := by omega
                subst V
                exact row_2_51
              · have he : V = 52 := by omega
                subst V
                exact row_2_52
            · by_cases h53_55 : V < 54
              · have he : V = 53 := by omega
                subst V
                exact row_2_53
              · have he : V = 54 := by omega
                subst V
                exact row_2_54
          · by_cases h55_60 : V < 57
            · by_cases h55_57 : V < 56
              · have he : V = 55 := by omega
                subst V
                exact row_2_55
              · have he : V = 56 := by omega
                subst V
                exact row_2_56
            · by_cases h57_60 : V < 58
              · have he : V = 57 := by omega
                subst V
                exact row_2_57
              · by_cases h58_60 : V < 59
                · have he : V = 58 := by omega
                  subst V
                  exact row_2_58
                · have he : V = 59 := by omega
                  subst V
                  exact row_2_59
        · by_cases h60_69 : V < 64
          · by_cases h60_64 : V < 62
            · by_cases h60_62 : V < 61
              · have he : V = 60 := by omega
                subst V
                exact row_2_60
              · have he : V = 61 := by omega
                subst V
                exact row_2_61
            · by_cases h62_64 : V < 63
              · have he : V = 62 := by omega
                subst V
                exact row_2_62
              · have he : V = 63 := by omega
                subst V
                exact row_2_63
          · by_cases h64_69 : V < 66
            · by_cases h64_66 : V < 65
              · have he : V = 64 := by omega
                subst V
                exact row_2_64
              · have he : V = 65 := by omega
                subst V
                exact row_2_65
            · by_cases h66_69 : V < 67
              · have he : V = 66 := by omega
                subst V
                exact row_2_66
              · by_cases h67_69 : V < 68
                · have he : V = 67 := by omega
                  subst V
                  exact row_2_67
                · have he : V = 68 := by omega
                  subst V
                  exact row_2_68
  · by_cases h69_138 : V < 103
    · by_cases h69_103 : V < 86
      · by_cases h69_86 : V < 77
        · by_cases h69_77 : V < 73
          · by_cases h69_73 : V < 71
            · by_cases h69_71 : V < 70
              · have he : V = 69 := by omega
                subst V
                exact row_2_69
              · have he : V = 70 := by omega
                subst V
                exact row_2_70
            · by_cases h71_73 : V < 72
              · have he : V = 71 := by omega
                subst V
                exact row_2_71
              · have he : V = 72 := by omega
                subst V
                exact row_2_72
          · by_cases h73_77 : V < 75
            · by_cases h73_75 : V < 74
              · have he : V = 73 := by omega
                subst V
                exact row_2_73
              · have he : V = 74 := by omega
                subst V
                exact row_2_74
            · by_cases h75_77 : V < 76
              · have he : V = 75 := by omega
                subst V
                exact row_2_75
              · have he : V = 76 := by omega
                subst V
                exact row_2_76
        · by_cases h77_86 : V < 81
          · by_cases h77_81 : V < 79
            · by_cases h77_79 : V < 78
              · have he : V = 77 := by omega
                subst V
                exact row_2_77
              · have he : V = 78 := by omega
                subst V
                exact row_2_78
            · by_cases h79_81 : V < 80
              · have he : V = 79 := by omega
                subst V
                exact row_2_79
              · have he : V = 80 := by omega
                subst V
                exact row_2_80
          · by_cases h81_86 : V < 83
            · by_cases h81_83 : V < 82
              · have he : V = 81 := by omega
                subst V
                exact row_2_81
              · have he : V = 82 := by omega
                subst V
                exact row_2_82
            · by_cases h83_86 : V < 84
              · have he : V = 83 := by omega
                subst V
                exact row_2_83
              · by_cases h84_86 : V < 85
                · have he : V = 84 := by omega
                  subst V
                  exact row_2_84
                · have he : V = 85 := by omega
                  subst V
                  exact row_2_85
      · by_cases h86_103 : V < 94
        · by_cases h86_94 : V < 90
          · by_cases h86_90 : V < 88
            · by_cases h86_88 : V < 87
              · have he : V = 86 := by omega
                subst V
                exact row_2_86
              · have he : V = 87 := by omega
                subst V
                exact row_2_87
            · by_cases h88_90 : V < 89
              · have he : V = 88 := by omega
                subst V
                exact row_2_88
              · have he : V = 89 := by omega
                subst V
                exact row_2_89
          · by_cases h90_94 : V < 92
            · by_cases h90_92 : V < 91
              · have he : V = 90 := by omega
                subst V
                exact row_2_90
              · have he : V = 91 := by omega
                subst V
                exact row_2_91
            · by_cases h92_94 : V < 93
              · have he : V = 92 := by omega
                subst V
                exact row_2_92
              · have he : V = 93 := by omega
                subst V
                exact row_2_93
        · by_cases h94_103 : V < 98
          · by_cases h94_98 : V < 96
            · by_cases h94_96 : V < 95
              · have he : V = 94 := by omega
                subst V
                exact row_2_94
              · have he : V = 95 := by omega
                subst V
                exact row_2_95
            · by_cases h96_98 : V < 97
              · have he : V = 96 := by omega
                subst V
                exact row_2_96
              · have he : V = 97 := by omega
                subst V
                exact row_2_97
          · by_cases h98_103 : V < 100
            · by_cases h98_100 : V < 99
              · have he : V = 98 := by omega
                subst V
                exact row_2_98
              · have he : V = 99 := by omega
                subst V
                exact row_2_99
            · by_cases h100_103 : V < 101
              · have he : V = 100 := by omega
                subst V
                exact row_2_100
              · by_cases h101_103 : V < 102
                · have he : V = 101 := by omega
                  subst V
                  exact row_2_101
                · have he : V = 102 := by omega
                  subst V
                  exact row_2_102
    · by_cases h103_138 : V < 120
      · by_cases h103_120 : V < 111
        · by_cases h103_111 : V < 107
          · by_cases h103_107 : V < 105
            · by_cases h103_105 : V < 104
              · have he : V = 103 := by omega
                subst V
                exact row_2_103
              · have he : V = 104 := by omega
                subst V
                exact row_2_104
            · by_cases h105_107 : V < 106
              · have he : V = 105 := by omega
                subst V
                exact row_2_105
              · have he : V = 106 := by omega
                subst V
                exact row_2_106
          · by_cases h107_111 : V < 109
            · by_cases h107_109 : V < 108
              · have he : V = 107 := by omega
                subst V
                exact row_2_107
              · have he : V = 108 := by omega
                subst V
                exact row_2_108
            · by_cases h109_111 : V < 110
              · have he : V = 109 := by omega
                subst V
                exact row_2_109
              · have he : V = 110 := by omega
                subst V
                exact row_2_110
        · by_cases h111_120 : V < 115
          · by_cases h111_115 : V < 113
            · by_cases h111_113 : V < 112
              · have he : V = 111 := by omega
                subst V
                exact row_2_111
              · have he : V = 112 := by omega
                subst V
                exact row_2_112
            · by_cases h113_115 : V < 114
              · have he : V = 113 := by omega
                subst V
                exact row_2_113
              · have he : V = 114 := by omega
                subst V
                exact row_2_114
          · by_cases h115_120 : V < 117
            · by_cases h115_117 : V < 116
              · have he : V = 115 := by omega
                subst V
                exact row_2_115
              · have he : V = 116 := by omega
                subst V
                exact row_2_116
            · by_cases h117_120 : V < 118
              · have he : V = 117 := by omega
                subst V
                exact row_2_117
              · by_cases h118_120 : V < 119
                · have he : V = 118 := by omega
                  subst V
                  exact row_2_118
                · have he : V = 119 := by omega
                  subst V
                  exact row_2_119
      · by_cases h120_138 : V < 129
        · by_cases h120_129 : V < 124
          · by_cases h120_124 : V < 122
            · by_cases h120_122 : V < 121
              · have he : V = 120 := by omega
                subst V
                exact row_2_120
              · have he : V = 121 := by omega
                subst V
                exact row_2_121
            · by_cases h122_124 : V < 123
              · have he : V = 122 := by omega
                subst V
                exact row_2_122
              · have he : V = 123 := by omega
                subst V
                exact row_2_123
          · by_cases h124_129 : V < 126
            · by_cases h124_126 : V < 125
              · have he : V = 124 := by omega
                subst V
                exact row_2_124
              · have he : V = 125 := by omega
                subst V
                exact row_2_125
            · by_cases h126_129 : V < 127
              · have he : V = 126 := by omega
                subst V
                exact row_2_126
              · by_cases h127_129 : V < 128
                · have he : V = 127 := by omega
                  subst V
                  exact row_2_127
                · have he : V = 128 := by omega
                  subst V
                  exact row_2_128
        · by_cases h129_138 : V < 133
          · by_cases h129_133 : V < 131
            · by_cases h129_131 : V < 130
              · have he : V = 129 := by omega
                subst V
                exact row_2_129
              · have he : V = 130 := by omega
                subst V
                exact row_2_130
            · by_cases h131_133 : V < 132
              · have he : V = 131 := by omega
                subst V
                exact row_2_131
              · have he : V = 132 := by omega
                subst V
                exact row_2_132
          · by_cases h133_138 : V < 135
            · by_cases h133_135 : V < 134
              · have he : V = 133 := by omega
                subst V
                exact row_2_133
              · have he : V = 134 := by omega
                subst V
                exact row_2_134
            · by_cases h135_138 : V < 136
              · have he : V = 135 := by omega
                subst V
                exact row_2_135
              · by_cases h136_138 : V < 137
                · have he : V = 136 := by omega
                  subst V
                  exact row_2_136
                · have he : V = 137 := by omega
                  subst V
                  exact row_2_137
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
