import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked16

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_17_0_0 : C 17 0 0 := by decide +kernel
theorem cell_17_0_1 : C 17 0 1 := by decide +kernel
theorem cell_17_0_2 : C 17 0 2 := by decide +kernel
theorem cell_17_0_3 : C 17 0 3 := by decide +kernel
theorem cell_17_0_4 : C 17 0 4 := by decide +kernel
theorem cell_17_0_5 : C 17 0 5 := by decide +kernel
theorem row_17_0 : ThresholdAt 17 0 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 0 0 cell_17_0_0
  | exact S 17 0 1 cell_17_0_1
  | exact S 17 0 2 cell_17_0_2
  | exact S 17 0 3 cell_17_0_3
  | exact S 17 0 4 cell_17_0_4
  | exact S 17 0 5 cell_17_0_5
theorem cell_17_1_0 : C 17 1 0 := by decide +kernel
theorem cell_17_1_1 : C 17 1 1 := by decide +kernel
theorem cell_17_1_2 : C 17 1 2 := by decide +kernel
theorem cell_17_1_3 : C 17 1 3 := by decide +kernel
theorem cell_17_1_4 : C 17 1 4 := by decide +kernel
theorem cell_17_1_5 : C 17 1 5 := by decide +kernel
theorem row_17_1 : ThresholdAt 17 1 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 1 0 cell_17_1_0
  | exact S 17 1 1 cell_17_1_1
  | exact S 17 1 2 cell_17_1_2
  | exact S 17 1 3 cell_17_1_3
  | exact S 17 1 4 cell_17_1_4
  | exact S 17 1 5 cell_17_1_5
theorem cell_17_2_0 : C 17 2 0 := by decide +kernel
theorem cell_17_2_1 : C 17 2 1 := by decide +kernel
theorem cell_17_2_2 : C 17 2 2 := by decide +kernel
theorem cell_17_2_3 : C 17 2 3 := by decide +kernel
theorem cell_17_2_4 : C 17 2 4 := by decide +kernel
theorem cell_17_2_5 : C 17 2 5 := by decide +kernel
theorem row_17_2 : ThresholdAt 17 2 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 2 0 cell_17_2_0
  | exact S 17 2 1 cell_17_2_1
  | exact S 17 2 2 cell_17_2_2
  | exact S 17 2 3 cell_17_2_3
  | exact S 17 2 4 cell_17_2_4
  | exact S 17 2 5 cell_17_2_5
theorem cell_17_3_0 : C 17 3 0 := by decide +kernel
theorem cell_17_3_1 : C 17 3 1 := by decide +kernel
theorem cell_17_3_2 : C 17 3 2 := by decide +kernel
theorem cell_17_3_3 : C 17 3 3 := by decide +kernel
theorem cell_17_3_4 : C 17 3 4 := by decide +kernel
theorem cell_17_3_5 : C 17 3 5 := by decide +kernel
theorem row_17_3 : ThresholdAt 17 3 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 3 0 cell_17_3_0
  | exact S 17 3 1 cell_17_3_1
  | exact S 17 3 2 cell_17_3_2
  | exact S 17 3 3 cell_17_3_3
  | exact S 17 3 4 cell_17_3_4
  | exact S 17 3 5 cell_17_3_5
theorem cell_17_4_0 : C 17 4 0 := by decide +kernel
theorem cell_17_4_1 : C 17 4 1 := by decide +kernel
theorem cell_17_4_2 : C 17 4 2 := by decide +kernel
theorem cell_17_4_3 : C 17 4 3 := by decide +kernel
theorem cell_17_4_4 : C 17 4 4 := by decide +kernel
theorem cell_17_4_5 : C 17 4 5 := by decide +kernel
theorem row_17_4 : ThresholdAt 17 4 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 4 0 cell_17_4_0
  | exact S 17 4 1 cell_17_4_1
  | exact S 17 4 2 cell_17_4_2
  | exact S 17 4 3 cell_17_4_3
  | exact S 17 4 4 cell_17_4_4
  | exact S 17 4 5 cell_17_4_5
theorem cell_17_5_0 : C 17 5 0 := by decide +kernel
theorem cell_17_5_1 : C 17 5 1 := by decide +kernel
theorem cell_17_5_2 : C 17 5 2 := by decide +kernel
theorem cell_17_5_3 : C 17 5 3 := by decide +kernel
theorem cell_17_5_4 : C 17 5 4 := by decide +kernel
theorem cell_17_5_5 : C 17 5 5 := by decide +kernel
theorem row_17_5 : ThresholdAt 17 5 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 5 0 cell_17_5_0
  | exact S 17 5 1 cell_17_5_1
  | exact S 17 5 2 cell_17_5_2
  | exact S 17 5 3 cell_17_5_3
  | exact S 17 5 4 cell_17_5_4
  | exact S 17 5 5 cell_17_5_5
theorem cell_17_6_0 : C 17 6 0 := by decide +kernel
theorem cell_17_6_1 : C 17 6 1 := by decide +kernel
theorem cell_17_6_2 : C 17 6 2 := by decide +kernel
theorem cell_17_6_3 : C 17 6 3 := by decide +kernel
theorem cell_17_6_4 : C 17 6 4 := by decide +kernel
theorem cell_17_6_5 : C 17 6 5 := by decide +kernel
theorem row_17_6 : ThresholdAt 17 6 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 6 0 cell_17_6_0
  | exact S 17 6 1 cell_17_6_1
  | exact S 17 6 2 cell_17_6_2
  | exact S 17 6 3 cell_17_6_3
  | exact S 17 6 4 cell_17_6_4
  | exact S 17 6 5 cell_17_6_5
theorem cell_17_7_0 : C 17 7 0 := by decide +kernel
theorem cell_17_7_1 : C 17 7 1 := by decide +kernel
theorem cell_17_7_2 : C 17 7 2 := by decide +kernel
theorem cell_17_7_3 : C 17 7 3 := by decide +kernel
theorem cell_17_7_4 : C 17 7 4 := by decide +kernel
theorem cell_17_7_5 : C 17 7 5 := by decide +kernel
theorem row_17_7 : ThresholdAt 17 7 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 7 0 cell_17_7_0
  | exact S 17 7 1 cell_17_7_1
  | exact S 17 7 2 cell_17_7_2
  | exact S 17 7 3 cell_17_7_3
  | exact S 17 7 4 cell_17_7_4
  | exact S 17 7 5 cell_17_7_5
theorem cell_17_8_0 : C 17 8 0 := by decide +kernel
theorem cell_17_8_1 : C 17 8 1 := by decide +kernel
theorem cell_17_8_2 : C 17 8 2 := by decide +kernel
theorem cell_17_8_3 : C 17 8 3 := by decide +kernel
theorem cell_17_8_4 : C 17 8 4 := by decide +kernel
theorem cell_17_8_5 : C 17 8 5 := by decide +kernel
theorem row_17_8 : ThresholdAt 17 8 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 8 0 cell_17_8_0
  | exact S 17 8 1 cell_17_8_1
  | exact S 17 8 2 cell_17_8_2
  | exact S 17 8 3 cell_17_8_3
  | exact S 17 8 4 cell_17_8_4
  | exact S 17 8 5 cell_17_8_5
theorem cell_17_9_0 : C 17 9 0 := by decide +kernel
theorem cell_17_9_1 : C 17 9 1 := by decide +kernel
theorem cell_17_9_2 : C 17 9 2 := by decide +kernel
theorem cell_17_9_3 : C 17 9 3 := by decide +kernel
theorem cell_17_9_4 : C 17 9 4 := by decide +kernel
theorem cell_17_9_5 : C 17 9 5 := by decide +kernel
theorem row_17_9 : ThresholdAt 17 9 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 9 0 cell_17_9_0
  | exact S 17 9 1 cell_17_9_1
  | exact S 17 9 2 cell_17_9_2
  | exact S 17 9 3 cell_17_9_3
  | exact S 17 9 4 cell_17_9_4
  | exact S 17 9 5 cell_17_9_5
theorem cell_17_10_0 : C 17 10 0 := by decide +kernel
theorem cell_17_10_1 : C 17 10 1 := by decide +kernel
theorem cell_17_10_2 : C 17 10 2 := by decide +kernel
theorem cell_17_10_3 : C 17 10 3 := by decide +kernel
theorem cell_17_10_4 : C 17 10 4 := by decide +kernel
theorem cell_17_10_5 : C 17 10 5 := by decide +kernel
theorem row_17_10 : ThresholdAt 17 10 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 10 0 cell_17_10_0
  | exact S 17 10 1 cell_17_10_1
  | exact S 17 10 2 cell_17_10_2
  | exact S 17 10 3 cell_17_10_3
  | exact S 17 10 4 cell_17_10_4
  | exact S 17 10 5 cell_17_10_5
theorem cell_17_11_0 : C 17 11 0 := by decide +kernel
theorem cell_17_11_1 : C 17 11 1 := by decide +kernel
theorem cell_17_11_2 : C 17 11 2 := by decide +kernel
theorem cell_17_11_3 : C 17 11 3 := by decide +kernel
theorem cell_17_11_4 : C 17 11 4 := by decide +kernel
theorem cell_17_11_5 : C 17 11 5 := by decide +kernel
theorem row_17_11 : ThresholdAt 17 11 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 11 0 cell_17_11_0
  | exact S 17 11 1 cell_17_11_1
  | exact S 17 11 2 cell_17_11_2
  | exact S 17 11 3 cell_17_11_3
  | exact S 17 11 4 cell_17_11_4
  | exact S 17 11 5 cell_17_11_5
theorem cell_17_12_0 : C 17 12 0 := by decide +kernel
theorem cell_17_12_1 : C 17 12 1 := by decide +kernel
theorem cell_17_12_2 : C 17 12 2 := by decide +kernel
theorem cell_17_12_3 : C 17 12 3 := by decide +kernel
theorem cell_17_12_4 : C 17 12 4 := by decide +kernel
theorem cell_17_12_5 : C 17 12 5 := by decide +kernel
theorem row_17_12 : ThresholdAt 17 12 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 12 0 cell_17_12_0
  | exact S 17 12 1 cell_17_12_1
  | exact S 17 12 2 cell_17_12_2
  | exact S 17 12 3 cell_17_12_3
  | exact S 17 12 4 cell_17_12_4
  | exact S 17 12 5 cell_17_12_5
theorem cell_17_13_0 : C 17 13 0 := by decide +kernel
theorem cell_17_13_1 : C 17 13 1 := by decide +kernel
theorem cell_17_13_2 : C 17 13 2 := by decide +kernel
theorem cell_17_13_3 : C 17 13 3 := by decide +kernel
theorem cell_17_13_4 : C 17 13 4 := by decide +kernel
theorem cell_17_13_5 : C 17 13 5 := by decide +kernel
theorem row_17_13 : ThresholdAt 17 13 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 13 0 cell_17_13_0
  | exact S 17 13 1 cell_17_13_1
  | exact S 17 13 2 cell_17_13_2
  | exact S 17 13 3 cell_17_13_3
  | exact S 17 13 4 cell_17_13_4
  | exact S 17 13 5 cell_17_13_5
theorem cell_17_14_0 : C 17 14 0 := by decide +kernel
theorem cell_17_14_1 : C 17 14 1 := by decide +kernel
theorem cell_17_14_2 : C 17 14 2 := by decide +kernel
theorem cell_17_14_3 : C 17 14 3 := by decide +kernel
theorem cell_17_14_4 : C 17 14 4 := by decide +kernel
theorem cell_17_14_5 : C 17 14 5 := by decide +kernel
theorem row_17_14 : ThresholdAt 17 14 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 14 0 cell_17_14_0
  | exact S 17 14 1 cell_17_14_1
  | exact S 17 14 2 cell_17_14_2
  | exact S 17 14 3 cell_17_14_3
  | exact S 17 14 4 cell_17_14_4
  | exact S 17 14 5 cell_17_14_5
theorem cell_17_15_0 : C 17 15 0 := by decide +kernel
theorem cell_17_15_1 : C 17 15 1 := by decide +kernel
theorem cell_17_15_2 : C 17 15 2 := by decide +kernel
theorem cell_17_15_3 : C 17 15 3 := by decide +kernel
theorem cell_17_15_4 : C 17 15 4 := by decide +kernel
theorem cell_17_15_5 : C 17 15 5 := by decide +kernel
theorem row_17_15 : ThresholdAt 17 15 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 15 0 cell_17_15_0
  | exact S 17 15 1 cell_17_15_1
  | exact S 17 15 2 cell_17_15_2
  | exact S 17 15 3 cell_17_15_3
  | exact S 17 15 4 cell_17_15_4
  | exact S 17 15 5 cell_17_15_5
theorem cell_17_16_0 : C 17 16 0 := by decide +kernel
theorem cell_17_16_1 : C 17 16 1 := by decide +kernel
theorem cell_17_16_2 : C 17 16 2 := by decide +kernel
theorem cell_17_16_3 : C 17 16 3 := by decide +kernel
theorem cell_17_16_4 : C 17 16 4 := by decide +kernel
theorem cell_17_16_5 : C 17 16 5 := by decide +kernel
theorem row_17_16 : ThresholdAt 17 16 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 16 0 cell_17_16_0
  | exact S 17 16 1 cell_17_16_1
  | exact S 17 16 2 cell_17_16_2
  | exact S 17 16 3 cell_17_16_3
  | exact S 17 16 4 cell_17_16_4
  | exact S 17 16 5 cell_17_16_5
theorem cell_17_17_0 : C 17 17 0 := by decide +kernel
theorem cell_17_17_1 : C 17 17 1 := by decide +kernel
theorem cell_17_17_2 : C 17 17 2 := by decide +kernel
theorem cell_17_17_3 : C 17 17 3 := by decide +kernel
theorem cell_17_17_4 : C 17 17 4 := by decide +kernel
theorem cell_17_17_5 : C 17 17 5 := by decide +kernel
theorem row_17_17 : ThresholdAt 17 17 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 17 0 cell_17_17_0
  | exact S 17 17 1 cell_17_17_1
  | exact S 17 17 2 cell_17_17_2
  | exact S 17 17 3 cell_17_17_3
  | exact S 17 17 4 cell_17_17_4
  | exact S 17 17 5 cell_17_17_5
theorem cell_17_18_0 : C 17 18 0 := by decide +kernel
theorem cell_17_18_1 : C 17 18 1 := by decide +kernel
theorem cell_17_18_2 : C 17 18 2 := by decide +kernel
theorem cell_17_18_3 : C 17 18 3 := by decide +kernel
theorem cell_17_18_4 : C 17 18 4 := by decide +kernel
theorem cell_17_18_5 : C 17 18 5 := by decide +kernel
theorem row_17_18 : ThresholdAt 17 18 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 18 0 cell_17_18_0
  | exact S 17 18 1 cell_17_18_1
  | exact S 17 18 2 cell_17_18_2
  | exact S 17 18 3 cell_17_18_3
  | exact S 17 18 4 cell_17_18_4
  | exact S 17 18 5 cell_17_18_5
theorem cell_17_19_0 : C 17 19 0 := by decide +kernel
theorem cell_17_19_1 : C 17 19 1 := by decide +kernel
theorem cell_17_19_2 : C 17 19 2 := by decide +kernel
theorem cell_17_19_3 : C 17 19 3 := by decide +kernel
theorem cell_17_19_4 : C 17 19 4 := by decide +kernel
theorem cell_17_19_5 : C 17 19 5 := by decide +kernel
theorem row_17_19 : ThresholdAt 17 19 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 19 0 cell_17_19_0
  | exact S 17 19 1 cell_17_19_1
  | exact S 17 19 2 cell_17_19_2
  | exact S 17 19 3 cell_17_19_3
  | exact S 17 19 4 cell_17_19_4
  | exact S 17 19 5 cell_17_19_5
theorem cell_17_20_0 : C 17 20 0 := by decide +kernel
theorem cell_17_20_1 : C 17 20 1 := by decide +kernel
theorem cell_17_20_2 : C 17 20 2 := by decide +kernel
theorem cell_17_20_3 : C 17 20 3 := by decide +kernel
theorem cell_17_20_4 : C 17 20 4 := by decide +kernel
theorem cell_17_20_5 : C 17 20 5 := by decide +kernel
theorem row_17_20 : ThresholdAt 17 20 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 20 0 cell_17_20_0
  | exact S 17 20 1 cell_17_20_1
  | exact S 17 20 2 cell_17_20_2
  | exact S 17 20 3 cell_17_20_3
  | exact S 17 20 4 cell_17_20_4
  | exact S 17 20 5 cell_17_20_5
theorem cell_17_21_0 : C 17 21 0 := by decide +kernel
theorem cell_17_21_1 : C 17 21 1 := by decide +kernel
theorem cell_17_21_2 : C 17 21 2 := by decide +kernel
theorem cell_17_21_3 : C 17 21 3 := by decide +kernel
theorem cell_17_21_4 : C 17 21 4 := by decide +kernel
theorem cell_17_21_5 : C 17 21 5 := by decide +kernel
theorem row_17_21 : ThresholdAt 17 21 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 21 0 cell_17_21_0
  | exact S 17 21 1 cell_17_21_1
  | exact S 17 21 2 cell_17_21_2
  | exact S 17 21 3 cell_17_21_3
  | exact S 17 21 4 cell_17_21_4
  | exact S 17 21 5 cell_17_21_5
theorem cell_17_22_0 : C 17 22 0 := by decide +kernel
theorem cell_17_22_1 : C 17 22 1 := by decide +kernel
theorem cell_17_22_2 : C 17 22 2 := by decide +kernel
theorem cell_17_22_3 : C 17 22 3 := by decide +kernel
theorem cell_17_22_4 : C 17 22 4 := by decide +kernel
theorem cell_17_22_5 : C 17 22 5 := by decide +kernel
theorem row_17_22 : ThresholdAt 17 22 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 22 0 cell_17_22_0
  | exact S 17 22 1 cell_17_22_1
  | exact S 17 22 2 cell_17_22_2
  | exact S 17 22 3 cell_17_22_3
  | exact S 17 22 4 cell_17_22_4
  | exact S 17 22 5 cell_17_22_5
theorem cell_17_23_0 : C 17 23 0 := by decide +kernel
theorem cell_17_23_1 : C 17 23 1 := by decide +kernel
theorem cell_17_23_2 : C 17 23 2 := by decide +kernel
theorem cell_17_23_3 : C 17 23 3 := by decide +kernel
theorem cell_17_23_4 : C 17 23 4 := by decide +kernel
theorem cell_17_23_5 : C 17 23 5 := by decide +kernel
theorem row_17_23 : ThresholdAt 17 23 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 23 0 cell_17_23_0
  | exact S 17 23 1 cell_17_23_1
  | exact S 17 23 2 cell_17_23_2
  | exact S 17 23 3 cell_17_23_3
  | exact S 17 23 4 cell_17_23_4
  | exact S 17 23 5 cell_17_23_5
theorem cell_17_24_0 : C 17 24 0 := by decide +kernel
theorem cell_17_24_1 : C 17 24 1 := by decide +kernel
theorem cell_17_24_2 : C 17 24 2 := by decide +kernel
theorem cell_17_24_3 : C 17 24 3 := by decide +kernel
theorem cell_17_24_4 : C 17 24 4 := by decide +kernel
theorem cell_17_24_5 : C 17 24 5 := by decide +kernel
theorem row_17_24 : ThresholdAt 17 24 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 24 0 cell_17_24_0
  | exact S 17 24 1 cell_17_24_1
  | exact S 17 24 2 cell_17_24_2
  | exact S 17 24 3 cell_17_24_3
  | exact S 17 24 4 cell_17_24_4
  | exact S 17 24 5 cell_17_24_5
theorem cell_17_25_0 : C 17 25 0 := by decide +kernel
theorem cell_17_25_1 : C 17 25 1 := by decide +kernel
theorem cell_17_25_2 : C 17 25 2 := by decide +kernel
theorem cell_17_25_3 : C 17 25 3 := by decide +kernel
theorem cell_17_25_4 : C 17 25 4 := by decide +kernel
theorem cell_17_25_5 : C 17 25 5 := by decide +kernel
theorem row_17_25 : ThresholdAt 17 25 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 25 0 cell_17_25_0
  | exact S 17 25 1 cell_17_25_1
  | exact S 17 25 2 cell_17_25_2
  | exact S 17 25 3 cell_17_25_3
  | exact S 17 25 4 cell_17_25_4
  | exact S 17 25 5 cell_17_25_5
theorem cell_17_26_0 : C 17 26 0 := by decide +kernel
theorem cell_17_26_1 : C 17 26 1 := by decide +kernel
theorem cell_17_26_2 : C 17 26 2 := by decide +kernel
theorem cell_17_26_3 : C 17 26 3 := by decide +kernel
theorem cell_17_26_4 : C 17 26 4 := by decide +kernel
theorem cell_17_26_5 : C 17 26 5 := by decide +kernel
theorem row_17_26 : ThresholdAt 17 26 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 26 0 cell_17_26_0
  | exact S 17 26 1 cell_17_26_1
  | exact S 17 26 2 cell_17_26_2
  | exact S 17 26 3 cell_17_26_3
  | exact S 17 26 4 cell_17_26_4
  | exact S 17 26 5 cell_17_26_5
theorem cell_17_27_0 : C 17 27 0 := by decide +kernel
theorem cell_17_27_1 : C 17 27 1 := by decide +kernel
theorem cell_17_27_2 : C 17 27 2 := by decide +kernel
theorem cell_17_27_3 : C 17 27 3 := by decide +kernel
theorem cell_17_27_4 : C 17 27 4 := by decide +kernel
theorem cell_17_27_5 : C 17 27 5 := by decide +kernel
theorem row_17_27 : ThresholdAt 17 27 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 27 0 cell_17_27_0
  | exact S 17 27 1 cell_17_27_1
  | exact S 17 27 2 cell_17_27_2
  | exact S 17 27 3 cell_17_27_3
  | exact S 17 27 4 cell_17_27_4
  | exact S 17 27 5 cell_17_27_5
theorem cell_17_28_0 : C 17 28 0 := by decide +kernel
theorem cell_17_28_1 : C 17 28 1 := by decide +kernel
theorem cell_17_28_2 : C 17 28 2 := by decide +kernel
theorem cell_17_28_3 : C 17 28 3 := by decide +kernel
theorem cell_17_28_4 : C 17 28 4 := by decide +kernel
theorem cell_17_28_5 : C 17 28 5 := by decide +kernel
theorem row_17_28 : ThresholdAt 17 28 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 28 0 cell_17_28_0
  | exact S 17 28 1 cell_17_28_1
  | exact S 17 28 2 cell_17_28_2
  | exact S 17 28 3 cell_17_28_3
  | exact S 17 28 4 cell_17_28_4
  | exact S 17 28 5 cell_17_28_5
theorem cell_17_29_0 : C 17 29 0 := by decide +kernel
theorem cell_17_29_1 : C 17 29 1 := by decide +kernel
theorem cell_17_29_2 : C 17 29 2 := by decide +kernel
theorem cell_17_29_3 : C 17 29 3 := by decide +kernel
theorem cell_17_29_4 : C 17 29 4 := by decide +kernel
theorem cell_17_29_5 : C 17 29 5 := by decide +kernel
theorem row_17_29 : ThresholdAt 17 29 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 29 0 cell_17_29_0
  | exact S 17 29 1 cell_17_29_1
  | exact S 17 29 2 cell_17_29_2
  | exact S 17 29 3 cell_17_29_3
  | exact S 17 29 4 cell_17_29_4
  | exact S 17 29 5 cell_17_29_5
theorem cell_17_30_0 : C 17 30 0 := by decide +kernel
theorem cell_17_30_1 : C 17 30 1 := by decide +kernel
theorem cell_17_30_2 : C 17 30 2 := by decide +kernel
theorem cell_17_30_3 : C 17 30 3 := by decide +kernel
theorem cell_17_30_4 : C 17 30 4 := by decide +kernel
theorem cell_17_30_5 : C 17 30 5 := by decide +kernel
theorem row_17_30 : ThresholdAt 17 30 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 30 0 cell_17_30_0
  | exact S 17 30 1 cell_17_30_1
  | exact S 17 30 2 cell_17_30_2
  | exact S 17 30 3 cell_17_30_3
  | exact S 17 30 4 cell_17_30_4
  | exact S 17 30 5 cell_17_30_5
theorem cell_17_31_0 : C 17 31 0 := by decide +kernel
theorem cell_17_31_1 : C 17 31 1 := by decide +kernel
theorem cell_17_31_2 : C 17 31 2 := by decide +kernel
theorem cell_17_31_3 : C 17 31 3 := by decide +kernel
theorem cell_17_31_4 : C 17 31 4 := by decide +kernel
theorem cell_17_31_5 : C 17 31 5 := by decide +kernel
theorem row_17_31 : ThresholdAt 17 31 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 31 0 cell_17_31_0
  | exact S 17 31 1 cell_17_31_1
  | exact S 17 31 2 cell_17_31_2
  | exact S 17 31 3 cell_17_31_3
  | exact S 17 31 4 cell_17_31_4
  | exact S 17 31 5 cell_17_31_5
theorem cell_17_32_0 : C 17 32 0 := by decide +kernel
theorem cell_17_32_1 : C 17 32 1 := by decide +kernel
theorem cell_17_32_2 : C 17 32 2 := by decide +kernel
theorem cell_17_32_3 : C 17 32 3 := by decide +kernel
theorem cell_17_32_4 : C 17 32 4 := by decide +kernel
theorem cell_17_32_5 : C 17 32 5 := by decide +kernel
theorem row_17_32 : ThresholdAt 17 32 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 32 0 cell_17_32_0
  | exact S 17 32 1 cell_17_32_1
  | exact S 17 32 2 cell_17_32_2
  | exact S 17 32 3 cell_17_32_3
  | exact S 17 32 4 cell_17_32_4
  | exact S 17 32 5 cell_17_32_5
theorem cell_17_33_0 : C 17 33 0 := by decide +kernel
theorem cell_17_33_1 : C 17 33 1 := by decide +kernel
theorem cell_17_33_2 : C 17 33 2 := by decide +kernel
theorem cell_17_33_3 : C 17 33 3 := by decide +kernel
theorem cell_17_33_4 : C 17 33 4 := by decide +kernel
theorem cell_17_33_5 : C 17 33 5 := by decide +kernel
theorem row_17_33 : ThresholdAt 17 33 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 33 0 cell_17_33_0
  | exact S 17 33 1 cell_17_33_1
  | exact S 17 33 2 cell_17_33_2
  | exact S 17 33 3 cell_17_33_3
  | exact S 17 33 4 cell_17_33_4
  | exact S 17 33 5 cell_17_33_5
theorem cell_17_34_0 : C 17 34 0 := by decide +kernel
theorem cell_17_34_1 : C 17 34 1 := by decide +kernel
theorem cell_17_34_2 : C 17 34 2 := by decide +kernel
theorem cell_17_34_3 : C 17 34 3 := by decide +kernel
theorem cell_17_34_4 : C 17 34 4 := by decide +kernel
theorem cell_17_34_5 : C 17 34 5 := by decide +kernel
theorem row_17_34 : ThresholdAt 17 34 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 34 0 cell_17_34_0
  | exact S 17 34 1 cell_17_34_1
  | exact S 17 34 2 cell_17_34_2
  | exact S 17 34 3 cell_17_34_3
  | exact S 17 34 4 cell_17_34_4
  | exact S 17 34 5 cell_17_34_5
theorem cell_17_35_0 : C 17 35 0 := by decide +kernel
theorem cell_17_35_1 : C 17 35 1 := by decide +kernel
theorem cell_17_35_2 : C 17 35 2 := by decide +kernel
theorem cell_17_35_3 : C 17 35 3 := by decide +kernel
theorem cell_17_35_4 : C 17 35 4 := by decide +kernel
theorem cell_17_35_5 : C 17 35 5 := by decide +kernel
theorem row_17_35 : ThresholdAt 17 35 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 35 0 cell_17_35_0
  | exact S 17 35 1 cell_17_35_1
  | exact S 17 35 2 cell_17_35_2
  | exact S 17 35 3 cell_17_35_3
  | exact S 17 35 4 cell_17_35_4
  | exact S 17 35 5 cell_17_35_5
theorem cell_17_36_0 : C 17 36 0 := by decide +kernel
theorem cell_17_36_1 : C 17 36 1 := by decide +kernel
theorem cell_17_36_2 : C 17 36 2 := by decide +kernel
theorem cell_17_36_3 : C 17 36 3 := by decide +kernel
theorem cell_17_36_4 : C 17 36 4 := by decide +kernel
theorem cell_17_36_5 : C 17 36 5 := by decide +kernel
theorem row_17_36 : ThresholdAt 17 36 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 36 0 cell_17_36_0
  | exact S 17 36 1 cell_17_36_1
  | exact S 17 36 2 cell_17_36_2
  | exact S 17 36 3 cell_17_36_3
  | exact S 17 36 4 cell_17_36_4
  | exact S 17 36 5 cell_17_36_5
theorem cell_17_37_0 : C 17 37 0 := by decide +kernel
theorem cell_17_37_1 : C 17 37 1 := by decide +kernel
theorem cell_17_37_2 : C 17 37 2 := by decide +kernel
theorem cell_17_37_3 : C 17 37 3 := by decide +kernel
theorem cell_17_37_4 : C 17 37 4 := by decide +kernel
theorem cell_17_37_5 : C 17 37 5 := by decide +kernel
theorem row_17_37 : ThresholdAt 17 37 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 37 0 cell_17_37_0
  | exact S 17 37 1 cell_17_37_1
  | exact S 17 37 2 cell_17_37_2
  | exact S 17 37 3 cell_17_37_3
  | exact S 17 37 4 cell_17_37_4
  | exact S 17 37 5 cell_17_37_5
theorem cell_17_38_0 : C 17 38 0 := by decide +kernel
theorem cell_17_38_1 : C 17 38 1 := by decide +kernel
theorem cell_17_38_2 : C 17 38 2 := by decide +kernel
theorem cell_17_38_3 : C 17 38 3 := by decide +kernel
theorem cell_17_38_4 : C 17 38 4 := by decide +kernel
theorem cell_17_38_5 : C 17 38 5 := by decide +kernel
theorem row_17_38 : ThresholdAt 17 38 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 38 0 cell_17_38_0
  | exact S 17 38 1 cell_17_38_1
  | exact S 17 38 2 cell_17_38_2
  | exact S 17 38 3 cell_17_38_3
  | exact S 17 38 4 cell_17_38_4
  | exact S 17 38 5 cell_17_38_5
theorem cell_17_39_0 : C 17 39 0 := by decide +kernel
theorem cell_17_39_1 : C 17 39 1 := by decide +kernel
theorem cell_17_39_2 : C 17 39 2 := by decide +kernel
theorem cell_17_39_3 : C 17 39 3 := by decide +kernel
theorem cell_17_39_4 : C 17 39 4 := by decide +kernel
theorem cell_17_39_5 : C 17 39 5 := by decide +kernel
theorem row_17_39 : ThresholdAt 17 39 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 39 0 cell_17_39_0
  | exact S 17 39 1 cell_17_39_1
  | exact S 17 39 2 cell_17_39_2
  | exact S 17 39 3 cell_17_39_3
  | exact S 17 39 4 cell_17_39_4
  | exact S 17 39 5 cell_17_39_5
theorem cell_17_40_0 : C 17 40 0 := by decide +kernel
theorem cell_17_40_1 : C 17 40 1 := by decide +kernel
theorem cell_17_40_2 : C 17 40 2 := by decide +kernel
theorem cell_17_40_3 : C 17 40 3 := by decide +kernel
theorem cell_17_40_4 : C 17 40 4 := by decide +kernel
theorem cell_17_40_5 : C 17 40 5 := by decide +kernel
theorem row_17_40 : ThresholdAt 17 40 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 40 0 cell_17_40_0
  | exact S 17 40 1 cell_17_40_1
  | exact S 17 40 2 cell_17_40_2
  | exact S 17 40 3 cell_17_40_3
  | exact S 17 40 4 cell_17_40_4
  | exact S 17 40 5 cell_17_40_5
theorem cell_17_41_0 : C 17 41 0 := by decide +kernel
theorem cell_17_41_1 : C 17 41 1 := by decide +kernel
theorem cell_17_41_2 : C 17 41 2 := by decide +kernel
theorem cell_17_41_3 : C 17 41 3 := by decide +kernel
theorem cell_17_41_4 : C 17 41 4 := by decide +kernel
theorem cell_17_41_5 : C 17 41 5 := by decide +kernel
theorem row_17_41 : ThresholdAt 17 41 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 41 0 cell_17_41_0
  | exact S 17 41 1 cell_17_41_1
  | exact S 17 41 2 cell_17_41_2
  | exact S 17 41 3 cell_17_41_3
  | exact S 17 41 4 cell_17_41_4
  | exact S 17 41 5 cell_17_41_5
theorem cell_17_42_0 : C 17 42 0 := by decide +kernel
theorem cell_17_42_1 : C 17 42 1 := by decide +kernel
theorem cell_17_42_2 : C 17 42 2 := by decide +kernel
theorem cell_17_42_3 : C 17 42 3 := by decide +kernel
theorem cell_17_42_4 : C 17 42 4 := by decide +kernel
theorem cell_17_42_5 : C 17 42 5 := by decide +kernel
theorem row_17_42 : ThresholdAt 17 42 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 42 0 cell_17_42_0
  | exact S 17 42 1 cell_17_42_1
  | exact S 17 42 2 cell_17_42_2
  | exact S 17 42 3 cell_17_42_3
  | exact S 17 42 4 cell_17_42_4
  | exact S 17 42 5 cell_17_42_5
theorem cell_17_43_0 : C 17 43 0 := by decide +kernel
theorem cell_17_43_1 : C 17 43 1 := by decide +kernel
theorem cell_17_43_2 : C 17 43 2 := by decide +kernel
theorem cell_17_43_3 : C 17 43 3 := by decide +kernel
theorem cell_17_43_4 : C 17 43 4 := by decide +kernel
theorem cell_17_43_5 : C 17 43 5 := by decide +kernel
theorem row_17_43 : ThresholdAt 17 43 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 43 0 cell_17_43_0
  | exact S 17 43 1 cell_17_43_1
  | exact S 17 43 2 cell_17_43_2
  | exact S 17 43 3 cell_17_43_3
  | exact S 17 43 4 cell_17_43_4
  | exact S 17 43 5 cell_17_43_5
theorem cell_17_44_0 : C 17 44 0 := by decide +kernel
theorem cell_17_44_1 : C 17 44 1 := by decide +kernel
theorem cell_17_44_2 : C 17 44 2 := by decide +kernel
theorem cell_17_44_3 : C 17 44 3 := by decide +kernel
theorem cell_17_44_4 : C 17 44 4 := by decide +kernel
theorem cell_17_44_5 : C 17 44 5 := by decide +kernel
theorem row_17_44 : ThresholdAt 17 44 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 44 0 cell_17_44_0
  | exact S 17 44 1 cell_17_44_1
  | exact S 17 44 2 cell_17_44_2
  | exact S 17 44 3 cell_17_44_3
  | exact S 17 44 4 cell_17_44_4
  | exact S 17 44 5 cell_17_44_5
theorem cell_17_45_0 : C 17 45 0 := by decide +kernel
theorem cell_17_45_1 : C 17 45 1 := by decide +kernel
theorem cell_17_45_2 : C 17 45 2 := by decide +kernel
theorem cell_17_45_3 : C 17 45 3 := by decide +kernel
theorem cell_17_45_4 : C 17 45 4 := by decide +kernel
theorem cell_17_45_5 : C 17 45 5 := by decide +kernel
theorem row_17_45 : ThresholdAt 17 45 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 45 0 cell_17_45_0
  | exact S 17 45 1 cell_17_45_1
  | exact S 17 45 2 cell_17_45_2
  | exact S 17 45 3 cell_17_45_3
  | exact S 17 45 4 cell_17_45_4
  | exact S 17 45 5 cell_17_45_5
theorem cell_17_46_0 : C 17 46 0 := by decide +kernel
theorem cell_17_46_1 : C 17 46 1 := by decide +kernel
theorem cell_17_46_2 : C 17 46 2 := by decide +kernel
theorem cell_17_46_3 : C 17 46 3 := by decide +kernel
theorem cell_17_46_4 : C 17 46 4 := by decide +kernel
theorem cell_17_46_5 : C 17 46 5 := by decide +kernel
theorem row_17_46 : ThresholdAt 17 46 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 46 0 cell_17_46_0
  | exact S 17 46 1 cell_17_46_1
  | exact S 17 46 2 cell_17_46_2
  | exact S 17 46 3 cell_17_46_3
  | exact S 17 46 4 cell_17_46_4
  | exact S 17 46 5 cell_17_46_5
theorem cell_17_47_0 : C 17 47 0 := by decide +kernel
theorem cell_17_47_1 : C 17 47 1 := by decide +kernel
theorem cell_17_47_2 : C 17 47 2 := by decide +kernel
theorem cell_17_47_3 : C 17 47 3 := by decide +kernel
theorem cell_17_47_4 : C 17 47 4 := by decide +kernel
theorem cell_17_47_5 : C 17 47 5 := by decide +kernel
theorem row_17_47 : ThresholdAt 17 47 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 47 0 cell_17_47_0
  | exact S 17 47 1 cell_17_47_1
  | exact S 17 47 2 cell_17_47_2
  | exact S 17 47 3 cell_17_47_3
  | exact S 17 47 4 cell_17_47_4
  | exact S 17 47 5 cell_17_47_5
theorem cell_17_48_0 : C 17 48 0 := by decide +kernel
theorem cell_17_48_1 : C 17 48 1 := by decide +kernel
theorem cell_17_48_2 : C 17 48 2 := by decide +kernel
theorem cell_17_48_3 : C 17 48 3 := by decide +kernel
theorem cell_17_48_4 : C 17 48 4 := by decide +kernel
theorem cell_17_48_5 : C 17 48 5 := by decide +kernel
theorem row_17_48 : ThresholdAt 17 48 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 48 0 cell_17_48_0
  | exact S 17 48 1 cell_17_48_1
  | exact S 17 48 2 cell_17_48_2
  | exact S 17 48 3 cell_17_48_3
  | exact S 17 48 4 cell_17_48_4
  | exact S 17 48 5 cell_17_48_5
theorem cell_17_49_0 : C 17 49 0 := by decide +kernel
theorem cell_17_49_1 : C 17 49 1 := by decide +kernel
theorem cell_17_49_2 : C 17 49 2 := by decide +kernel
theorem cell_17_49_3 : C 17 49 3 := by decide +kernel
theorem cell_17_49_4 : C 17 49 4 := by decide +kernel
theorem cell_17_49_5 : C 17 49 5 := by decide +kernel
theorem row_17_49 : ThresholdAt 17 49 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 49 0 cell_17_49_0
  | exact S 17 49 1 cell_17_49_1
  | exact S 17 49 2 cell_17_49_2
  | exact S 17 49 3 cell_17_49_3
  | exact S 17 49 4 cell_17_49_4
  | exact S 17 49 5 cell_17_49_5
theorem cell_17_50_0 : C 17 50 0 := by decide +kernel
theorem cell_17_50_1 : C 17 50 1 := by decide +kernel
theorem cell_17_50_2 : C 17 50 2 := by decide +kernel
theorem cell_17_50_3 : C 17 50 3 := by decide +kernel
theorem cell_17_50_4 : C 17 50 4 := by decide +kernel
theorem cell_17_50_5 : C 17 50 5 := by decide +kernel
theorem row_17_50 : ThresholdAt 17 50 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 50 0 cell_17_50_0
  | exact S 17 50 1 cell_17_50_1
  | exact S 17 50 2 cell_17_50_2
  | exact S 17 50 3 cell_17_50_3
  | exact S 17 50 4 cell_17_50_4
  | exact S 17 50 5 cell_17_50_5
theorem cell_17_51_0 : C 17 51 0 := by decide +kernel
theorem cell_17_51_1 : C 17 51 1 := by decide +kernel
theorem cell_17_51_2 : C 17 51 2 := by decide +kernel
theorem cell_17_51_3 : C 17 51 3 := by decide +kernel
theorem cell_17_51_4 : C 17 51 4 := by decide +kernel
theorem cell_17_51_5 : C 17 51 5 := by decide +kernel
theorem row_17_51 : ThresholdAt 17 51 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 51 0 cell_17_51_0
  | exact S 17 51 1 cell_17_51_1
  | exact S 17 51 2 cell_17_51_2
  | exact S 17 51 3 cell_17_51_3
  | exact S 17 51 4 cell_17_51_4
  | exact S 17 51 5 cell_17_51_5
theorem cell_17_52_0 : C 17 52 0 := by decide +kernel
theorem cell_17_52_1 : C 17 52 1 := by decide +kernel
theorem cell_17_52_2 : C 17 52 2 := by decide +kernel
theorem cell_17_52_3 : C 17 52 3 := by decide +kernel
theorem cell_17_52_4 : C 17 52 4 := by decide +kernel
theorem cell_17_52_5 : C 17 52 5 := by decide +kernel
theorem row_17_52 : ThresholdAt 17 52 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 52 0 cell_17_52_0
  | exact S 17 52 1 cell_17_52_1
  | exact S 17 52 2 cell_17_52_2
  | exact S 17 52 3 cell_17_52_3
  | exact S 17 52 4 cell_17_52_4
  | exact S 17 52 5 cell_17_52_5
theorem cell_17_53_0 : C 17 53 0 := by decide +kernel
theorem cell_17_53_1 : C 17 53 1 := by decide +kernel
theorem cell_17_53_2 : C 17 53 2 := by decide +kernel
theorem cell_17_53_3 : C 17 53 3 := by decide +kernel
theorem cell_17_53_4 : C 17 53 4 := by decide +kernel
theorem cell_17_53_5 : C 17 53 5 := by decide +kernel
theorem row_17_53 : ThresholdAt 17 53 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 53 0 cell_17_53_0
  | exact S 17 53 1 cell_17_53_1
  | exact S 17 53 2 cell_17_53_2
  | exact S 17 53 3 cell_17_53_3
  | exact S 17 53 4 cell_17_53_4
  | exact S 17 53 5 cell_17_53_5
theorem cell_17_54_0 : C 17 54 0 := by decide +kernel
theorem cell_17_54_1 : C 17 54 1 := by decide +kernel
theorem cell_17_54_2 : C 17 54 2 := by decide +kernel
theorem cell_17_54_3 : C 17 54 3 := by decide +kernel
theorem cell_17_54_4 : C 17 54 4 := by decide +kernel
theorem cell_17_54_5 : C 17 54 5 := by decide +kernel
theorem row_17_54 : ThresholdAt 17 54 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 54 0 cell_17_54_0
  | exact S 17 54 1 cell_17_54_1
  | exact S 17 54 2 cell_17_54_2
  | exact S 17 54 3 cell_17_54_3
  | exact S 17 54 4 cell_17_54_4
  | exact S 17 54 5 cell_17_54_5
theorem cell_17_55_0 : C 17 55 0 := by decide +kernel
theorem cell_17_55_1 : C 17 55 1 := by decide +kernel
theorem cell_17_55_2 : C 17 55 2 := by decide +kernel
theorem cell_17_55_3 : C 17 55 3 := by decide +kernel
theorem cell_17_55_4 : C 17 55 4 := by decide +kernel
theorem cell_17_55_5 : C 17 55 5 := by decide +kernel
theorem row_17_55 : ThresholdAt 17 55 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 55 0 cell_17_55_0
  | exact S 17 55 1 cell_17_55_1
  | exact S 17 55 2 cell_17_55_2
  | exact S 17 55 3 cell_17_55_3
  | exact S 17 55 4 cell_17_55_4
  | exact S 17 55 5 cell_17_55_5
theorem cell_17_56_0 : C 17 56 0 := by decide +kernel
theorem cell_17_56_1 : C 17 56 1 := by decide +kernel
theorem cell_17_56_2 : C 17 56 2 := by decide +kernel
theorem cell_17_56_3 : C 17 56 3 := by decide +kernel
theorem cell_17_56_4 : C 17 56 4 := by decide +kernel
theorem cell_17_56_5 : C 17 56 5 := by decide +kernel
theorem row_17_56 : ThresholdAt 17 56 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 56 0 cell_17_56_0
  | exact S 17 56 1 cell_17_56_1
  | exact S 17 56 2 cell_17_56_2
  | exact S 17 56 3 cell_17_56_3
  | exact S 17 56 4 cell_17_56_4
  | exact S 17 56 5 cell_17_56_5
theorem cell_17_57_0 : C 17 57 0 := by decide +kernel
theorem cell_17_57_1 : C 17 57 1 := by decide +kernel
theorem cell_17_57_2 : C 17 57 2 := by decide +kernel
theorem cell_17_57_3 : C 17 57 3 := by decide +kernel
theorem cell_17_57_4 : C 17 57 4 := by decide +kernel
theorem cell_17_57_5 : C 17 57 5 := by decide +kernel
theorem row_17_57 : ThresholdAt 17 57 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 57 0 cell_17_57_0
  | exact S 17 57 1 cell_17_57_1
  | exact S 17 57 2 cell_17_57_2
  | exact S 17 57 3 cell_17_57_3
  | exact S 17 57 4 cell_17_57_4
  | exact S 17 57 5 cell_17_57_5
theorem cell_17_58_0 : C 17 58 0 := by decide +kernel
theorem cell_17_58_1 : C 17 58 1 := by decide +kernel
theorem cell_17_58_2 : C 17 58 2 := by decide +kernel
theorem cell_17_58_3 : C 17 58 3 := by decide +kernel
theorem cell_17_58_4 : C 17 58 4 := by decide +kernel
theorem cell_17_58_5 : C 17 58 5 := by decide +kernel
theorem row_17_58 : ThresholdAt 17 58 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 58 0 cell_17_58_0
  | exact S 17 58 1 cell_17_58_1
  | exact S 17 58 2 cell_17_58_2
  | exact S 17 58 3 cell_17_58_3
  | exact S 17 58 4 cell_17_58_4
  | exact S 17 58 5 cell_17_58_5
theorem cell_17_59_0 : C 17 59 0 := by decide +kernel
theorem cell_17_59_1 : C 17 59 1 := by decide +kernel
theorem cell_17_59_2 : C 17 59 2 := by decide +kernel
theorem cell_17_59_3 : C 17 59 3 := by decide +kernel
theorem cell_17_59_4 : C 17 59 4 := by decide +kernel
theorem cell_17_59_5 : C 17 59 5 := by decide +kernel
theorem row_17_59 : ThresholdAt 17 59 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 59 0 cell_17_59_0
  | exact S 17 59 1 cell_17_59_1
  | exact S 17 59 2 cell_17_59_2
  | exact S 17 59 3 cell_17_59_3
  | exact S 17 59 4 cell_17_59_4
  | exact S 17 59 5 cell_17_59_5
theorem cell_17_60_0 : C 17 60 0 := by decide +kernel
theorem cell_17_60_1 : C 17 60 1 := by decide +kernel
theorem cell_17_60_2 : C 17 60 2 := by decide +kernel
theorem cell_17_60_3 : C 17 60 3 := by decide +kernel
theorem cell_17_60_4 : C 17 60 4 := by decide +kernel
theorem cell_17_60_5 : C 17 60 5 := by decide +kernel
theorem row_17_60 : ThresholdAt 17 60 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 60 0 cell_17_60_0
  | exact S 17 60 1 cell_17_60_1
  | exact S 17 60 2 cell_17_60_2
  | exact S 17 60 3 cell_17_60_3
  | exact S 17 60 4 cell_17_60_4
  | exact S 17 60 5 cell_17_60_5
theorem cell_17_61_0 : C 17 61 0 := by decide +kernel
theorem cell_17_61_1 : C 17 61 1 := by decide +kernel
theorem cell_17_61_2 : C 17 61 2 := by decide +kernel
theorem cell_17_61_3 : C 17 61 3 := by decide +kernel
theorem cell_17_61_4 : C 17 61 4 := by decide +kernel
theorem cell_17_61_5 : C 17 61 5 := by decide +kernel
theorem row_17_61 : ThresholdAt 17 61 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 61 0 cell_17_61_0
  | exact S 17 61 1 cell_17_61_1
  | exact S 17 61 2 cell_17_61_2
  | exact S 17 61 3 cell_17_61_3
  | exact S 17 61 4 cell_17_61_4
  | exact S 17 61 5 cell_17_61_5
theorem cell_17_62_0 : C 17 62 0 := by decide +kernel
theorem cell_17_62_1 : C 17 62 1 := by decide +kernel
theorem cell_17_62_2 : C 17 62 2 := by decide +kernel
theorem cell_17_62_3 : C 17 62 3 := by decide +kernel
theorem cell_17_62_4 : C 17 62 4 := by decide +kernel
theorem cell_17_62_5 : C 17 62 5 := by decide +kernel
theorem row_17_62 : ThresholdAt 17 62 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 62 0 cell_17_62_0
  | exact S 17 62 1 cell_17_62_1
  | exact S 17 62 2 cell_17_62_2
  | exact S 17 62 3 cell_17_62_3
  | exact S 17 62 4 cell_17_62_4
  | exact S 17 62 5 cell_17_62_5
theorem cell_17_63_0 : C 17 63 0 := by decide +kernel
theorem cell_17_63_1 : C 17 63 1 := by decide +kernel
theorem cell_17_63_2 : C 17 63 2 := by decide +kernel
theorem cell_17_63_3 : C 17 63 3 := by decide +kernel
theorem cell_17_63_4 : C 17 63 4 := by decide +kernel
theorem cell_17_63_5 : C 17 63 5 := by decide +kernel
theorem row_17_63 : ThresholdAt 17 63 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 63 0 cell_17_63_0
  | exact S 17 63 1 cell_17_63_1
  | exact S 17 63 2 cell_17_63_2
  | exact S 17 63 3 cell_17_63_3
  | exact S 17 63 4 cell_17_63_4
  | exact S 17 63 5 cell_17_63_5
theorem cell_17_64_0 : C 17 64 0 := by decide +kernel
theorem cell_17_64_1 : C 17 64 1 := by decide +kernel
theorem cell_17_64_2 : C 17 64 2 := by decide +kernel
theorem cell_17_64_3 : C 17 64 3 := by decide +kernel
theorem cell_17_64_4 : C 17 64 4 := by decide +kernel
theorem cell_17_64_5 : C 17 64 5 := by decide +kernel
theorem row_17_64 : ThresholdAt 17 64 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 64 0 cell_17_64_0
  | exact S 17 64 1 cell_17_64_1
  | exact S 17 64 2 cell_17_64_2
  | exact S 17 64 3 cell_17_64_3
  | exact S 17 64 4 cell_17_64_4
  | exact S 17 64 5 cell_17_64_5
theorem cell_17_65_0 : C 17 65 0 := by decide +kernel
theorem cell_17_65_1 : C 17 65 1 := by decide +kernel
theorem cell_17_65_2 : C 17 65 2 := by decide +kernel
theorem cell_17_65_3 : C 17 65 3 := by decide +kernel
theorem cell_17_65_4 : C 17 65 4 := by decide +kernel
theorem cell_17_65_5 : C 17 65 5 := by decide +kernel
theorem row_17_65 : ThresholdAt 17 65 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 65 0 cell_17_65_0
  | exact S 17 65 1 cell_17_65_1
  | exact S 17 65 2 cell_17_65_2
  | exact S 17 65 3 cell_17_65_3
  | exact S 17 65 4 cell_17_65_4
  | exact S 17 65 5 cell_17_65_5
theorem cell_17_66_0 : C 17 66 0 := by decide +kernel
theorem cell_17_66_1 : C 17 66 1 := by decide +kernel
theorem cell_17_66_2 : C 17 66 2 := by decide +kernel
theorem cell_17_66_3 : C 17 66 3 := by decide +kernel
theorem cell_17_66_4 : C 17 66 4 := by decide +kernel
theorem cell_17_66_5 : C 17 66 5 := by decide +kernel
theorem row_17_66 : ThresholdAt 17 66 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 66 0 cell_17_66_0
  | exact S 17 66 1 cell_17_66_1
  | exact S 17 66 2 cell_17_66_2
  | exact S 17 66 3 cell_17_66_3
  | exact S 17 66 4 cell_17_66_4
  | exact S 17 66 5 cell_17_66_5
theorem cell_17_67_0 : C 17 67 0 := by decide +kernel
theorem cell_17_67_1 : C 17 67 1 := by decide +kernel
theorem cell_17_67_2 : C 17 67 2 := by decide +kernel
theorem cell_17_67_3 : C 17 67 3 := by decide +kernel
theorem cell_17_67_4 : C 17 67 4 := by decide +kernel
theorem cell_17_67_5 : C 17 67 5 := by decide +kernel
theorem row_17_67 : ThresholdAt 17 67 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 67 0 cell_17_67_0
  | exact S 17 67 1 cell_17_67_1
  | exact S 17 67 2 cell_17_67_2
  | exact S 17 67 3 cell_17_67_3
  | exact S 17 67 4 cell_17_67_4
  | exact S 17 67 5 cell_17_67_5
theorem cell_17_68_0 : C 17 68 0 := by decide +kernel
theorem cell_17_68_1 : C 17 68 1 := by decide +kernel
theorem cell_17_68_2 : C 17 68 2 := by decide +kernel
theorem cell_17_68_3 : C 17 68 3 := by decide +kernel
theorem cell_17_68_4 : C 17 68 4 := by decide +kernel
theorem cell_17_68_5 : C 17 68 5 := by decide +kernel
theorem row_17_68 : ThresholdAt 17 68 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 68 0 cell_17_68_0
  | exact S 17 68 1 cell_17_68_1
  | exact S 17 68 2 cell_17_68_2
  | exact S 17 68 3 cell_17_68_3
  | exact S 17 68 4 cell_17_68_4
  | exact S 17 68 5 cell_17_68_5
theorem cell_17_69_0 : C 17 69 0 := by decide +kernel
theorem cell_17_69_1 : C 17 69 1 := by decide +kernel
theorem cell_17_69_2 : C 17 69 2 := by decide +kernel
theorem cell_17_69_3 : C 17 69 3 := by decide +kernel
theorem cell_17_69_4 : C 17 69 4 := by decide +kernel
theorem cell_17_69_5 : C 17 69 5 := by decide +kernel
theorem row_17_69 : ThresholdAt 17 69 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 69 0 cell_17_69_0
  | exact S 17 69 1 cell_17_69_1
  | exact S 17 69 2 cell_17_69_2
  | exact S 17 69 3 cell_17_69_3
  | exact S 17 69 4 cell_17_69_4
  | exact S 17 69 5 cell_17_69_5
theorem cell_17_70_0 : C 17 70 0 := by decide +kernel
theorem cell_17_70_1 : C 17 70 1 := by decide +kernel
theorem cell_17_70_2 : C 17 70 2 := by decide +kernel
theorem cell_17_70_3 : C 17 70 3 := by decide +kernel
theorem cell_17_70_4 : C 17 70 4 := by decide +kernel
theorem cell_17_70_5 : C 17 70 5 := by decide +kernel
theorem row_17_70 : ThresholdAt 17 70 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 70 0 cell_17_70_0
  | exact S 17 70 1 cell_17_70_1
  | exact S 17 70 2 cell_17_70_2
  | exact S 17 70 3 cell_17_70_3
  | exact S 17 70 4 cell_17_70_4
  | exact S 17 70 5 cell_17_70_5
theorem cell_17_71_0 : C 17 71 0 := by decide +kernel
theorem cell_17_71_1 : C 17 71 1 := by decide +kernel
theorem cell_17_71_2 : C 17 71 2 := by decide +kernel
theorem cell_17_71_3 : C 17 71 3 := by decide +kernel
theorem cell_17_71_4 : C 17 71 4 := by decide +kernel
theorem cell_17_71_5 : C 17 71 5 := by decide +kernel
theorem row_17_71 : ThresholdAt 17 71 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 71 0 cell_17_71_0
  | exact S 17 71 1 cell_17_71_1
  | exact S 17 71 2 cell_17_71_2
  | exact S 17 71 3 cell_17_71_3
  | exact S 17 71 4 cell_17_71_4
  | exact S 17 71 5 cell_17_71_5
theorem cell_17_72_0 : C 17 72 0 := by decide +kernel
theorem cell_17_72_1 : C 17 72 1 := by decide +kernel
theorem cell_17_72_2 : C 17 72 2 := by decide +kernel
theorem cell_17_72_3 : C 17 72 3 := by decide +kernel
theorem cell_17_72_4 : C 17 72 4 := by decide +kernel
theorem cell_17_72_5 : C 17 72 5 := by decide +kernel
theorem row_17_72 : ThresholdAt 17 72 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 72 0 cell_17_72_0
  | exact S 17 72 1 cell_17_72_1
  | exact S 17 72 2 cell_17_72_2
  | exact S 17 72 3 cell_17_72_3
  | exact S 17 72 4 cell_17_72_4
  | exact S 17 72 5 cell_17_72_5
theorem cell_17_73_0 : C 17 73 0 := by decide +kernel
theorem cell_17_73_1 : C 17 73 1 := by decide +kernel
theorem cell_17_73_2 : C 17 73 2 := by decide +kernel
theorem cell_17_73_3 : C 17 73 3 := by decide +kernel
theorem cell_17_73_4 : C 17 73 4 := by decide +kernel
theorem cell_17_73_5 : C 17 73 5 := by decide +kernel
theorem row_17_73 : ThresholdAt 17 73 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 73 0 cell_17_73_0
  | exact S 17 73 1 cell_17_73_1
  | exact S 17 73 2 cell_17_73_2
  | exact S 17 73 3 cell_17_73_3
  | exact S 17 73 4 cell_17_73_4
  | exact S 17 73 5 cell_17_73_5
theorem cell_17_74_0 : C 17 74 0 := by decide +kernel
theorem cell_17_74_1 : C 17 74 1 := by decide +kernel
theorem cell_17_74_2 : C 17 74 2 := by decide +kernel
theorem cell_17_74_3 : C 17 74 3 := by decide +kernel
theorem cell_17_74_4 : C 17 74 4 := by decide +kernel
theorem cell_17_74_5 : C 17 74 5 := by decide +kernel
theorem row_17_74 : ThresholdAt 17 74 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 74 0 cell_17_74_0
  | exact S 17 74 1 cell_17_74_1
  | exact S 17 74 2 cell_17_74_2
  | exact S 17 74 3 cell_17_74_3
  | exact S 17 74 4 cell_17_74_4
  | exact S 17 74 5 cell_17_74_5
theorem cell_17_75_0 : C 17 75 0 := by decide +kernel
theorem cell_17_75_1 : C 17 75 1 := by decide +kernel
theorem cell_17_75_2 : C 17 75 2 := by decide +kernel
theorem cell_17_75_3 : C 17 75 3 := by decide +kernel
theorem cell_17_75_4 : C 17 75 4 := by decide +kernel
theorem cell_17_75_5 : C 17 75 5 := by decide +kernel
theorem row_17_75 : ThresholdAt 17 75 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 75 0 cell_17_75_0
  | exact S 17 75 1 cell_17_75_1
  | exact S 17 75 2 cell_17_75_2
  | exact S 17 75 3 cell_17_75_3
  | exact S 17 75 4 cell_17_75_4
  | exact S 17 75 5 cell_17_75_5
theorem cell_17_76_0 : C 17 76 0 := by decide +kernel
theorem cell_17_76_1 : C 17 76 1 := by decide +kernel
theorem cell_17_76_2 : C 17 76 2 := by decide +kernel
theorem cell_17_76_3 : C 17 76 3 := by decide +kernel
theorem cell_17_76_4 : C 17 76 4 := by decide +kernel
theorem cell_17_76_5 : C 17 76 5 := by decide +kernel
theorem row_17_76 : ThresholdAt 17 76 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 76 0 cell_17_76_0
  | exact S 17 76 1 cell_17_76_1
  | exact S 17 76 2 cell_17_76_2
  | exact S 17 76 3 cell_17_76_3
  | exact S 17 76 4 cell_17_76_4
  | exact S 17 76 5 cell_17_76_5
theorem cell_17_77_0 : C 17 77 0 := by decide +kernel
theorem cell_17_77_1 : C 17 77 1 := by decide +kernel
theorem cell_17_77_2 : C 17 77 2 := by decide +kernel
theorem cell_17_77_3 : C 17 77 3 := by decide +kernel
theorem cell_17_77_4 : C 17 77 4 := by decide +kernel
theorem cell_17_77_5 : C 17 77 5 := by decide +kernel
theorem row_17_77 : ThresholdAt 17 77 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 77 0 cell_17_77_0
  | exact S 17 77 1 cell_17_77_1
  | exact S 17 77 2 cell_17_77_2
  | exact S 17 77 3 cell_17_77_3
  | exact S 17 77 4 cell_17_77_4
  | exact S 17 77 5 cell_17_77_5
theorem cell_17_78_0 : C 17 78 0 := by decide +kernel
theorem cell_17_78_1 : C 17 78 1 := by decide +kernel
theorem cell_17_78_2 : C 17 78 2 := by decide +kernel
theorem cell_17_78_3 : C 17 78 3 := by decide +kernel
theorem cell_17_78_4 : C 17 78 4 := by decide +kernel
theorem cell_17_78_5 : C 17 78 5 := by decide +kernel
theorem row_17_78 : ThresholdAt 17 78 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 78 0 cell_17_78_0
  | exact S 17 78 1 cell_17_78_1
  | exact S 17 78 2 cell_17_78_2
  | exact S 17 78 3 cell_17_78_3
  | exact S 17 78 4 cell_17_78_4
  | exact S 17 78 5 cell_17_78_5
theorem cell_17_79_0 : C 17 79 0 := by decide +kernel
theorem cell_17_79_1 : C 17 79 1 := by decide +kernel
theorem cell_17_79_2 : C 17 79 2 := by decide +kernel
theorem cell_17_79_3 : C 17 79 3 := by decide +kernel
theorem cell_17_79_4 : C 17 79 4 := by decide +kernel
theorem cell_17_79_5 : C 17 79 5 := by decide +kernel
theorem row_17_79 : ThresholdAt 17 79 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 79 0 cell_17_79_0
  | exact S 17 79 1 cell_17_79_1
  | exact S 17 79 2 cell_17_79_2
  | exact S 17 79 3 cell_17_79_3
  | exact S 17 79 4 cell_17_79_4
  | exact S 17 79 5 cell_17_79_5
theorem cell_17_80_0 : C 17 80 0 := by decide +kernel
theorem cell_17_80_1 : C 17 80 1 := by decide +kernel
theorem cell_17_80_2 : C 17 80 2 := by decide +kernel
theorem cell_17_80_3 : C 17 80 3 := by decide +kernel
theorem cell_17_80_4 : C 17 80 4 := by decide +kernel
theorem cell_17_80_5 : C 17 80 5 := by decide +kernel
theorem row_17_80 : ThresholdAt 17 80 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 80 0 cell_17_80_0
  | exact S 17 80 1 cell_17_80_1
  | exact S 17 80 2 cell_17_80_2
  | exact S 17 80 3 cell_17_80_3
  | exact S 17 80 4 cell_17_80_4
  | exact S 17 80 5 cell_17_80_5
theorem cell_17_81_0 : C 17 81 0 := by decide +kernel
theorem cell_17_81_1 : C 17 81 1 := by decide +kernel
theorem cell_17_81_2 : C 17 81 2 := by decide +kernel
theorem cell_17_81_3 : C 17 81 3 := by decide +kernel
theorem cell_17_81_4 : C 17 81 4 := by decide +kernel
theorem cell_17_81_5 : C 17 81 5 := by decide +kernel
theorem row_17_81 : ThresholdAt 17 81 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 81 0 cell_17_81_0
  | exact S 17 81 1 cell_17_81_1
  | exact S 17 81 2 cell_17_81_2
  | exact S 17 81 3 cell_17_81_3
  | exact S 17 81 4 cell_17_81_4
  | exact S 17 81 5 cell_17_81_5
theorem cell_17_82_0 : C 17 82 0 := by decide +kernel
theorem cell_17_82_1 : C 17 82 1 := by decide +kernel
theorem cell_17_82_2 : C 17 82 2 := by decide +kernel
theorem cell_17_82_3 : C 17 82 3 := by decide +kernel
theorem cell_17_82_4 : C 17 82 4 := by decide +kernel
theorem cell_17_82_5 : C 17 82 5 := by decide +kernel
theorem row_17_82 : ThresholdAt 17 82 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 82 0 cell_17_82_0
  | exact S 17 82 1 cell_17_82_1
  | exact S 17 82 2 cell_17_82_2
  | exact S 17 82 3 cell_17_82_3
  | exact S 17 82 4 cell_17_82_4
  | exact S 17 82 5 cell_17_82_5
theorem cell_17_83_0 : C 17 83 0 := by decide +kernel
theorem cell_17_83_1 : C 17 83 1 := by decide +kernel
theorem cell_17_83_2 : C 17 83 2 := by decide +kernel
theorem cell_17_83_3 : C 17 83 3 := by decide +kernel
theorem cell_17_83_4 : C 17 83 4 := by decide +kernel
theorem cell_17_83_5 : C 17 83 5 := by decide +kernel
theorem row_17_83 : ThresholdAt 17 83 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 83 0 cell_17_83_0
  | exact S 17 83 1 cell_17_83_1
  | exact S 17 83 2 cell_17_83_2
  | exact S 17 83 3 cell_17_83_3
  | exact S 17 83 4 cell_17_83_4
  | exact S 17 83 5 cell_17_83_5
theorem cell_17_84_0 : C 17 84 0 := by decide +kernel
theorem cell_17_84_1 : C 17 84 1 := by decide +kernel
theorem cell_17_84_2 : C 17 84 2 := by decide +kernel
theorem cell_17_84_3 : C 17 84 3 := by decide +kernel
theorem cell_17_84_4 : C 17 84 4 := by decide +kernel
theorem cell_17_84_5 : C 17 84 5 := by decide +kernel
theorem row_17_84 : ThresholdAt 17 84 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 84 0 cell_17_84_0
  | exact S 17 84 1 cell_17_84_1
  | exact S 17 84 2 cell_17_84_2
  | exact S 17 84 3 cell_17_84_3
  | exact S 17 84 4 cell_17_84_4
  | exact S 17 84 5 cell_17_84_5
theorem cell_17_85_0 : C 17 85 0 := by decide +kernel
theorem cell_17_85_1 : C 17 85 1 := by decide +kernel
theorem cell_17_85_2 : C 17 85 2 := by decide +kernel
theorem cell_17_85_3 : C 17 85 3 := by decide +kernel
theorem cell_17_85_4 : C 17 85 4 := by decide +kernel
theorem cell_17_85_5 : C 17 85 5 := by decide +kernel
theorem row_17_85 : ThresholdAt 17 85 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 85 0 cell_17_85_0
  | exact S 17 85 1 cell_17_85_1
  | exact S 17 85 2 cell_17_85_2
  | exact S 17 85 3 cell_17_85_3
  | exact S 17 85 4 cell_17_85_4
  | exact S 17 85 5 cell_17_85_5
theorem cell_17_86_0 : C 17 86 0 := by decide +kernel
theorem cell_17_86_1 : C 17 86 1 := by decide +kernel
theorem cell_17_86_2 : C 17 86 2 := by decide +kernel
theorem cell_17_86_3 : C 17 86 3 := by decide +kernel
theorem cell_17_86_4 : C 17 86 4 := by decide +kernel
theorem cell_17_86_5 : C 17 86 5 := by decide +kernel
theorem row_17_86 : ThresholdAt 17 86 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 86 0 cell_17_86_0
  | exact S 17 86 1 cell_17_86_1
  | exact S 17 86 2 cell_17_86_2
  | exact S 17 86 3 cell_17_86_3
  | exact S 17 86 4 cell_17_86_4
  | exact S 17 86 5 cell_17_86_5
theorem cell_17_87_0 : C 17 87 0 := by decide +kernel
theorem cell_17_87_1 : C 17 87 1 := by decide +kernel
theorem cell_17_87_2 : C 17 87 2 := by decide +kernel
theorem cell_17_87_3 : C 17 87 3 := by decide +kernel
theorem cell_17_87_4 : C 17 87 4 := by decide +kernel
theorem cell_17_87_5 : C 17 87 5 := by decide +kernel
theorem row_17_87 : ThresholdAt 17 87 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 87 0 cell_17_87_0
  | exact S 17 87 1 cell_17_87_1
  | exact S 17 87 2 cell_17_87_2
  | exact S 17 87 3 cell_17_87_3
  | exact S 17 87 4 cell_17_87_4
  | exact S 17 87 5 cell_17_87_5
theorem cell_17_88_0 : C 17 88 0 := by decide +kernel
theorem cell_17_88_1 : C 17 88 1 := by decide +kernel
theorem cell_17_88_2 : C 17 88 2 := by decide +kernel
theorem cell_17_88_3 : C 17 88 3 := by decide +kernel
theorem cell_17_88_4 : C 17 88 4 := by decide +kernel
theorem cell_17_88_5 : C 17 88 5 := by decide +kernel
theorem row_17_88 : ThresholdAt 17 88 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 88 0 cell_17_88_0
  | exact S 17 88 1 cell_17_88_1
  | exact S 17 88 2 cell_17_88_2
  | exact S 17 88 3 cell_17_88_3
  | exact S 17 88 4 cell_17_88_4
  | exact S 17 88 5 cell_17_88_5
theorem cell_17_89_0 : C 17 89 0 := by decide +kernel
theorem cell_17_89_1 : C 17 89 1 := by decide +kernel
theorem cell_17_89_2 : C 17 89 2 := by decide +kernel
theorem cell_17_89_3 : C 17 89 3 := by decide +kernel
theorem cell_17_89_4 : C 17 89 4 := by decide +kernel
theorem cell_17_89_5 : C 17 89 5 := by decide +kernel
theorem row_17_89 : ThresholdAt 17 89 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 89 0 cell_17_89_0
  | exact S 17 89 1 cell_17_89_1
  | exact S 17 89 2 cell_17_89_2
  | exact S 17 89 3 cell_17_89_3
  | exact S 17 89 4 cell_17_89_4
  | exact S 17 89 5 cell_17_89_5
theorem cell_17_90_0 : C 17 90 0 := by decide +kernel
theorem cell_17_90_1 : C 17 90 1 := by decide +kernel
theorem cell_17_90_2 : C 17 90 2 := by decide +kernel
theorem cell_17_90_3 : C 17 90 3 := by decide +kernel
theorem cell_17_90_4 : C 17 90 4 := by decide +kernel
theorem cell_17_90_5 : C 17 90 5 := by decide +kernel
theorem row_17_90 : ThresholdAt 17 90 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 90 0 cell_17_90_0
  | exact S 17 90 1 cell_17_90_1
  | exact S 17 90 2 cell_17_90_2
  | exact S 17 90 3 cell_17_90_3
  | exact S 17 90 4 cell_17_90_4
  | exact S 17 90 5 cell_17_90_5
theorem cell_17_91_0 : C 17 91 0 := by decide +kernel
theorem cell_17_91_1 : C 17 91 1 := by decide +kernel
theorem cell_17_91_2 : C 17 91 2 := by decide +kernel
theorem cell_17_91_3 : C 17 91 3 := by decide +kernel
theorem cell_17_91_4 : C 17 91 4 := by decide +kernel
theorem cell_17_91_5 : C 17 91 5 := by decide +kernel
theorem row_17_91 : ThresholdAt 17 91 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 91 0 cell_17_91_0
  | exact S 17 91 1 cell_17_91_1
  | exact S 17 91 2 cell_17_91_2
  | exact S 17 91 3 cell_17_91_3
  | exact S 17 91 4 cell_17_91_4
  | exact S 17 91 5 cell_17_91_5
theorem cell_17_92_0 : C 17 92 0 := by decide +kernel
theorem cell_17_92_1 : C 17 92 1 := by decide +kernel
theorem cell_17_92_2 : C 17 92 2 := by decide +kernel
theorem cell_17_92_3 : C 17 92 3 := by decide +kernel
theorem cell_17_92_4 : C 17 92 4 := by decide +kernel
theorem cell_17_92_5 : C 17 92 5 := by decide +kernel
theorem row_17_92 : ThresholdAt 17 92 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 92 0 cell_17_92_0
  | exact S 17 92 1 cell_17_92_1
  | exact S 17 92 2 cell_17_92_2
  | exact S 17 92 3 cell_17_92_3
  | exact S 17 92 4 cell_17_92_4
  | exact S 17 92 5 cell_17_92_5
theorem cell_17_93_0 : C 17 93 0 := by decide +kernel
theorem cell_17_93_1 : C 17 93 1 := by decide +kernel
theorem cell_17_93_2 : C 17 93 2 := by decide +kernel
theorem cell_17_93_3 : C 17 93 3 := by decide +kernel
theorem cell_17_93_4 : C 17 93 4 := by decide +kernel
theorem cell_17_93_5 : C 17 93 5 := by decide +kernel
theorem row_17_93 : ThresholdAt 17 93 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 93 0 cell_17_93_0
  | exact S 17 93 1 cell_17_93_1
  | exact S 17 93 2 cell_17_93_2
  | exact S 17 93 3 cell_17_93_3
  | exact S 17 93 4 cell_17_93_4
  | exact S 17 93 5 cell_17_93_5
theorem cell_17_94_0 : C 17 94 0 := by decide +kernel
theorem cell_17_94_1 : C 17 94 1 := by decide +kernel
theorem cell_17_94_2 : C 17 94 2 := by decide +kernel
theorem cell_17_94_3 : C 17 94 3 := by decide +kernel
theorem cell_17_94_4 : C 17 94 4 := by decide +kernel
theorem cell_17_94_5 : C 17 94 5 := by decide +kernel
theorem row_17_94 : ThresholdAt 17 94 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 94 0 cell_17_94_0
  | exact S 17 94 1 cell_17_94_1
  | exact S 17 94 2 cell_17_94_2
  | exact S 17 94 3 cell_17_94_3
  | exact S 17 94 4 cell_17_94_4
  | exact S 17 94 5 cell_17_94_5
theorem cell_17_95_0 : C 17 95 0 := by decide +kernel
theorem cell_17_95_1 : C 17 95 1 := by decide +kernel
theorem cell_17_95_2 : C 17 95 2 := by decide +kernel
theorem cell_17_95_3 : C 17 95 3 := by decide +kernel
theorem cell_17_95_4 : C 17 95 4 := by decide +kernel
theorem cell_17_95_5 : C 17 95 5 := by decide +kernel
theorem row_17_95 : ThresholdAt 17 95 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 95 0 cell_17_95_0
  | exact S 17 95 1 cell_17_95_1
  | exact S 17 95 2 cell_17_95_2
  | exact S 17 95 3 cell_17_95_3
  | exact S 17 95 4 cell_17_95_4
  | exact S 17 95 5 cell_17_95_5
theorem cell_17_96_0 : C 17 96 0 := by decide +kernel
theorem cell_17_96_1 : C 17 96 1 := by decide +kernel
theorem cell_17_96_2 : C 17 96 2 := by decide +kernel
theorem cell_17_96_3 : C 17 96 3 := by decide +kernel
theorem cell_17_96_4 : C 17 96 4 := by decide +kernel
theorem cell_17_96_5 : C 17 96 5 := by decide +kernel
theorem row_17_96 : ThresholdAt 17 96 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 96 0 cell_17_96_0
  | exact S 17 96 1 cell_17_96_1
  | exact S 17 96 2 cell_17_96_2
  | exact S 17 96 3 cell_17_96_3
  | exact S 17 96 4 cell_17_96_4
  | exact S 17 96 5 cell_17_96_5
theorem cell_17_97_0 : C 17 97 0 := by decide +kernel
theorem cell_17_97_1 : C 17 97 1 := by decide +kernel
theorem cell_17_97_2 : C 17 97 2 := by decide +kernel
theorem cell_17_97_3 : C 17 97 3 := by decide +kernel
theorem cell_17_97_4 : C 17 97 4 := by decide +kernel
theorem cell_17_97_5 : C 17 97 5 := by decide +kernel
theorem row_17_97 : ThresholdAt 17 97 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 97 0 cell_17_97_0
  | exact S 17 97 1 cell_17_97_1
  | exact S 17 97 2 cell_17_97_2
  | exact S 17 97 3 cell_17_97_3
  | exact S 17 97 4 cell_17_97_4
  | exact S 17 97 5 cell_17_97_5
theorem cell_17_98_0 : C 17 98 0 := by decide +kernel
theorem cell_17_98_1 : C 17 98 1 := by decide +kernel
theorem cell_17_98_2 : C 17 98 2 := by decide +kernel
theorem cell_17_98_3 : C 17 98 3 := by decide +kernel
theorem cell_17_98_4 : C 17 98 4 := by decide +kernel
theorem cell_17_98_5 : C 17 98 5 := by decide +kernel
theorem row_17_98 : ThresholdAt 17 98 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 98 0 cell_17_98_0
  | exact S 17 98 1 cell_17_98_1
  | exact S 17 98 2 cell_17_98_2
  | exact S 17 98 3 cell_17_98_3
  | exact S 17 98 4 cell_17_98_4
  | exact S 17 98 5 cell_17_98_5
theorem cell_17_99_0 : C 17 99 0 := by decide +kernel
theorem cell_17_99_1 : C 17 99 1 := by decide +kernel
theorem cell_17_99_2 : C 17 99 2 := by decide +kernel
theorem cell_17_99_3 : C 17 99 3 := by decide +kernel
theorem cell_17_99_4 : C 17 99 4 := by decide +kernel
theorem cell_17_99_5 : C 17 99 5 := by decide +kernel
theorem row_17_99 : ThresholdAt 17 99 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 99 0 cell_17_99_0
  | exact S 17 99 1 cell_17_99_1
  | exact S 17 99 2 cell_17_99_2
  | exact S 17 99 3 cell_17_99_3
  | exact S 17 99 4 cell_17_99_4
  | exact S 17 99 5 cell_17_99_5
theorem cell_17_100_0 : C 17 100 0 := by decide +kernel
theorem cell_17_100_1 : C 17 100 1 := by decide +kernel
theorem cell_17_100_2 : C 17 100 2 := by decide +kernel
theorem cell_17_100_3 : C 17 100 3 := by decide +kernel
theorem cell_17_100_4 : C 17 100 4 := by decide +kernel
theorem cell_17_100_5 : C 17 100 5 := by decide +kernel
theorem row_17_100 : ThresholdAt 17 100 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 100 0 cell_17_100_0
  | exact S 17 100 1 cell_17_100_1
  | exact S 17 100 2 cell_17_100_2
  | exact S 17 100 3 cell_17_100_3
  | exact S 17 100 4 cell_17_100_4
  | exact S 17 100 5 cell_17_100_5
theorem cell_17_101_0 : C 17 101 0 := by decide +kernel
theorem cell_17_101_1 : C 17 101 1 := by decide +kernel
theorem cell_17_101_2 : C 17 101 2 := by decide +kernel
theorem cell_17_101_3 : C 17 101 3 := by decide +kernel
theorem cell_17_101_4 : C 17 101 4 := by decide +kernel
theorem cell_17_101_5 : C 17 101 5 := by decide +kernel
theorem row_17_101 : ThresholdAt 17 101 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 101 0 cell_17_101_0
  | exact S 17 101 1 cell_17_101_1
  | exact S 17 101 2 cell_17_101_2
  | exact S 17 101 3 cell_17_101_3
  | exact S 17 101 4 cell_17_101_4
  | exact S 17 101 5 cell_17_101_5
theorem cell_17_102_0 : C 17 102 0 := by decide +kernel
theorem cell_17_102_1 : C 17 102 1 := by decide +kernel
theorem cell_17_102_2 : C 17 102 2 := by decide +kernel
theorem cell_17_102_3 : C 17 102 3 := by decide +kernel
theorem cell_17_102_4 : C 17 102 4 := by decide +kernel
theorem cell_17_102_5 : C 17 102 5 := by decide +kernel
theorem row_17_102 : ThresholdAt 17 102 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 102 0 cell_17_102_0
  | exact S 17 102 1 cell_17_102_1
  | exact S 17 102 2 cell_17_102_2
  | exact S 17 102 3 cell_17_102_3
  | exact S 17 102 4 cell_17_102_4
  | exact S 17 102 5 cell_17_102_5
theorem cell_17_103_0 : C 17 103 0 := by decide +kernel
theorem cell_17_103_1 : C 17 103 1 := by decide +kernel
theorem cell_17_103_2 : C 17 103 2 := by decide +kernel
theorem cell_17_103_3 : C 17 103 3 := by decide +kernel
theorem cell_17_103_4 : C 17 103 4 := by decide +kernel
theorem cell_17_103_5 : C 17 103 5 := by decide +kernel
theorem row_17_103 : ThresholdAt 17 103 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 103 0 cell_17_103_0
  | exact S 17 103 1 cell_17_103_1
  | exact S 17 103 2 cell_17_103_2
  | exact S 17 103 3 cell_17_103_3
  | exact S 17 103 4 cell_17_103_4
  | exact S 17 103 5 cell_17_103_5
theorem cell_17_104_0 : C 17 104 0 := by decide +kernel
theorem cell_17_104_1 : C 17 104 1 := by decide +kernel
theorem cell_17_104_2 : C 17 104 2 := by decide +kernel
theorem cell_17_104_3 : C 17 104 3 := by decide +kernel
theorem cell_17_104_4 : C 17 104 4 := by decide +kernel
theorem cell_17_104_5 : C 17 104 5 := by decide +kernel
theorem row_17_104 : ThresholdAt 17 104 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 104 0 cell_17_104_0
  | exact S 17 104 1 cell_17_104_1
  | exact S 17 104 2 cell_17_104_2
  | exact S 17 104 3 cell_17_104_3
  | exact S 17 104 4 cell_17_104_4
  | exact S 17 104 5 cell_17_104_5
theorem cell_17_105_0 : C 17 105 0 := by decide +kernel
theorem cell_17_105_1 : C 17 105 1 := by decide +kernel
theorem cell_17_105_2 : C 17 105 2 := by decide +kernel
theorem cell_17_105_3 : C 17 105 3 := by decide +kernel
theorem cell_17_105_4 : C 17 105 4 := by decide +kernel
theorem cell_17_105_5 : C 17 105 5 := by decide +kernel
theorem row_17_105 : ThresholdAt 17 105 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 105 0 cell_17_105_0
  | exact S 17 105 1 cell_17_105_1
  | exact S 17 105 2 cell_17_105_2
  | exact S 17 105 3 cell_17_105_3
  | exact S 17 105 4 cell_17_105_4
  | exact S 17 105 5 cell_17_105_5
theorem cell_17_106_0 : C 17 106 0 := by decide +kernel
theorem cell_17_106_1 : C 17 106 1 := by decide +kernel
theorem cell_17_106_2 : C 17 106 2 := by decide +kernel
theorem cell_17_106_3 : C 17 106 3 := by decide +kernel
theorem cell_17_106_4 : C 17 106 4 := by decide +kernel
theorem cell_17_106_5 : C 17 106 5 := by decide +kernel
theorem row_17_106 : ThresholdAt 17 106 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 106 0 cell_17_106_0
  | exact S 17 106 1 cell_17_106_1
  | exact S 17 106 2 cell_17_106_2
  | exact S 17 106 3 cell_17_106_3
  | exact S 17 106 4 cell_17_106_4
  | exact S 17 106 5 cell_17_106_5
theorem cell_17_107_0 : C 17 107 0 := by decide +kernel
theorem cell_17_107_1 : C 17 107 1 := by decide +kernel
theorem cell_17_107_2 : C 17 107 2 := by decide +kernel
theorem cell_17_107_3 : C 17 107 3 := by decide +kernel
theorem cell_17_107_4 : C 17 107 4 := by decide +kernel
theorem cell_17_107_5 : C 17 107 5 := by decide +kernel
theorem row_17_107 : ThresholdAt 17 107 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 107 0 cell_17_107_0
  | exact S 17 107 1 cell_17_107_1
  | exact S 17 107 2 cell_17_107_2
  | exact S 17 107 3 cell_17_107_3
  | exact S 17 107 4 cell_17_107_4
  | exact S 17 107 5 cell_17_107_5
theorem cell_17_108_0 : C 17 108 0 := by decide +kernel
theorem cell_17_108_1 : C 17 108 1 := by decide +kernel
theorem cell_17_108_2 : C 17 108 2 := by decide +kernel
theorem cell_17_108_3 : C 17 108 3 := by decide +kernel
theorem cell_17_108_4 : C 17 108 4 := by decide +kernel
theorem cell_17_108_5 : C 17 108 5 := by decide +kernel
theorem row_17_108 : ThresholdAt 17 108 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 108 0 cell_17_108_0
  | exact S 17 108 1 cell_17_108_1
  | exact S 17 108 2 cell_17_108_2
  | exact S 17 108 3 cell_17_108_3
  | exact S 17 108 4 cell_17_108_4
  | exact S 17 108 5 cell_17_108_5
theorem cell_17_109_0 : C 17 109 0 := by decide +kernel
theorem cell_17_109_1 : C 17 109 1 := by decide +kernel
theorem cell_17_109_2 : C 17 109 2 := by decide +kernel
theorem cell_17_109_3 : C 17 109 3 := by decide +kernel
theorem cell_17_109_4 : C 17 109 4 := by decide +kernel
theorem cell_17_109_5 : C 17 109 5 := by decide +kernel
theorem row_17_109 : ThresholdAt 17 109 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 109 0 cell_17_109_0
  | exact S 17 109 1 cell_17_109_1
  | exact S 17 109 2 cell_17_109_2
  | exact S 17 109 3 cell_17_109_3
  | exact S 17 109 4 cell_17_109_4
  | exact S 17 109 5 cell_17_109_5
theorem cell_17_110_0 : C 17 110 0 := by decide +kernel
theorem cell_17_110_1 : C 17 110 1 := by decide +kernel
theorem cell_17_110_2 : C 17 110 2 := by decide +kernel
theorem cell_17_110_3 : C 17 110 3 := by decide +kernel
theorem cell_17_110_4 : C 17 110 4 := by decide +kernel
theorem cell_17_110_5 : C 17 110 5 := by decide +kernel
theorem row_17_110 : ThresholdAt 17 110 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 110 0 cell_17_110_0
  | exact S 17 110 1 cell_17_110_1
  | exact S 17 110 2 cell_17_110_2
  | exact S 17 110 3 cell_17_110_3
  | exact S 17 110 4 cell_17_110_4
  | exact S 17 110 5 cell_17_110_5
theorem cell_17_111_0 : C 17 111 0 := by decide +kernel
theorem cell_17_111_1 : C 17 111 1 := by decide +kernel
theorem cell_17_111_2 : C 17 111 2 := by decide +kernel
theorem cell_17_111_3 : C 17 111 3 := by decide +kernel
theorem cell_17_111_4 : C 17 111 4 := by decide +kernel
theorem cell_17_111_5 : C 17 111 5 := by decide +kernel
theorem row_17_111 : ThresholdAt 17 111 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 111 0 cell_17_111_0
  | exact S 17 111 1 cell_17_111_1
  | exact S 17 111 2 cell_17_111_2
  | exact S 17 111 3 cell_17_111_3
  | exact S 17 111 4 cell_17_111_4
  | exact S 17 111 5 cell_17_111_5
theorem cell_17_112_0 : C 17 112 0 := by decide +kernel
theorem cell_17_112_1 : C 17 112 1 := by decide +kernel
theorem cell_17_112_2 : C 17 112 2 := by decide +kernel
theorem cell_17_112_3 : C 17 112 3 := by decide +kernel
theorem cell_17_112_4 : C 17 112 4 := by decide +kernel
theorem cell_17_112_5 : C 17 112 5 := by decide +kernel
theorem row_17_112 : ThresholdAt 17 112 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 112 0 cell_17_112_0
  | exact S 17 112 1 cell_17_112_1
  | exact S 17 112 2 cell_17_112_2
  | exact S 17 112 3 cell_17_112_3
  | exact S 17 112 4 cell_17_112_4
  | exact S 17 112 5 cell_17_112_5
theorem cell_17_113_0 : C 17 113 0 := by decide +kernel
theorem cell_17_113_1 : C 17 113 1 := by decide +kernel
theorem cell_17_113_2 : C 17 113 2 := by decide +kernel
theorem cell_17_113_3 : C 17 113 3 := by decide +kernel
theorem cell_17_113_4 : C 17 113 4 := by decide +kernel
theorem cell_17_113_5 : C 17 113 5 := by decide +kernel
theorem row_17_113 : ThresholdAt 17 113 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 113 0 cell_17_113_0
  | exact S 17 113 1 cell_17_113_1
  | exact S 17 113 2 cell_17_113_2
  | exact S 17 113 3 cell_17_113_3
  | exact S 17 113 4 cell_17_113_4
  | exact S 17 113 5 cell_17_113_5
theorem cell_17_114_0 : C 17 114 0 := by decide +kernel
theorem cell_17_114_1 : C 17 114 1 := by decide +kernel
theorem cell_17_114_2 : C 17 114 2 := by decide +kernel
theorem cell_17_114_3 : C 17 114 3 := by decide +kernel
theorem cell_17_114_4 : C 17 114 4 := by decide +kernel
theorem cell_17_114_5 : C 17 114 5 := by decide +kernel
theorem row_17_114 : ThresholdAt 17 114 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 114 0 cell_17_114_0
  | exact S 17 114 1 cell_17_114_1
  | exact S 17 114 2 cell_17_114_2
  | exact S 17 114 3 cell_17_114_3
  | exact S 17 114 4 cell_17_114_4
  | exact S 17 114 5 cell_17_114_5
theorem cell_17_115_0 : C 17 115 0 := by decide +kernel
theorem cell_17_115_1 : C 17 115 1 := by decide +kernel
theorem cell_17_115_2 : C 17 115 2 := by decide +kernel
theorem cell_17_115_3 : C 17 115 3 := by decide +kernel
theorem cell_17_115_4 : C 17 115 4 := by decide +kernel
theorem cell_17_115_5 : C 17 115 5 := by decide +kernel
theorem row_17_115 : ThresholdAt 17 115 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 115 0 cell_17_115_0
  | exact S 17 115 1 cell_17_115_1
  | exact S 17 115 2 cell_17_115_2
  | exact S 17 115 3 cell_17_115_3
  | exact S 17 115 4 cell_17_115_4
  | exact S 17 115 5 cell_17_115_5
theorem cell_17_116_0 : C 17 116 0 := by decide +kernel
theorem cell_17_116_1 : C 17 116 1 := by decide +kernel
theorem cell_17_116_2 : C 17 116 2 := by decide +kernel
theorem cell_17_116_3 : C 17 116 3 := by decide +kernel
theorem cell_17_116_4 : C 17 116 4 := by decide +kernel
theorem cell_17_116_5 : C 17 116 5 := by decide +kernel
theorem row_17_116 : ThresholdAt 17 116 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 116 0 cell_17_116_0
  | exact S 17 116 1 cell_17_116_1
  | exact S 17 116 2 cell_17_116_2
  | exact S 17 116 3 cell_17_116_3
  | exact S 17 116 4 cell_17_116_4
  | exact S 17 116 5 cell_17_116_5
theorem cell_17_117_0 : C 17 117 0 := by decide +kernel
theorem cell_17_117_1 : C 17 117 1 := by decide +kernel
theorem cell_17_117_2 : C 17 117 2 := by decide +kernel
theorem cell_17_117_3 : C 17 117 3 := by decide +kernel
theorem cell_17_117_4 : C 17 117 4 := by decide +kernel
theorem cell_17_117_5 : C 17 117 5 := by decide +kernel
theorem row_17_117 : ThresholdAt 17 117 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 117 0 cell_17_117_0
  | exact S 17 117 1 cell_17_117_1
  | exact S 17 117 2 cell_17_117_2
  | exact S 17 117 3 cell_17_117_3
  | exact S 17 117 4 cell_17_117_4
  | exact S 17 117 5 cell_17_117_5
theorem cell_17_118_0 : C 17 118 0 := by decide +kernel
theorem cell_17_118_1 : C 17 118 1 := by decide +kernel
theorem cell_17_118_2 : C 17 118 2 := by decide +kernel
theorem cell_17_118_3 : C 17 118 3 := by decide +kernel
theorem cell_17_118_4 : C 17 118 4 := by decide +kernel
theorem cell_17_118_5 : C 17 118 5 := by decide +kernel
theorem row_17_118 : ThresholdAt 17 118 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 118 0 cell_17_118_0
  | exact S 17 118 1 cell_17_118_1
  | exact S 17 118 2 cell_17_118_2
  | exact S 17 118 3 cell_17_118_3
  | exact S 17 118 4 cell_17_118_4
  | exact S 17 118 5 cell_17_118_5
theorem cell_17_119_0 : C 17 119 0 := by decide +kernel
theorem cell_17_119_1 : C 17 119 1 := by decide +kernel
theorem cell_17_119_2 : C 17 119 2 := by decide +kernel
theorem cell_17_119_3 : C 17 119 3 := by decide +kernel
theorem cell_17_119_4 : C 17 119 4 := by decide +kernel
theorem cell_17_119_5 : C 17 119 5 := by decide +kernel
theorem row_17_119 : ThresholdAt 17 119 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 119 0 cell_17_119_0
  | exact S 17 119 1 cell_17_119_1
  | exact S 17 119 2 cell_17_119_2
  | exact S 17 119 3 cell_17_119_3
  | exact S 17 119 4 cell_17_119_4
  | exact S 17 119 5 cell_17_119_5
theorem cell_17_120_0 : C 17 120 0 := by decide +kernel
theorem cell_17_120_1 : C 17 120 1 := by decide +kernel
theorem cell_17_120_2 : C 17 120 2 := by decide +kernel
theorem cell_17_120_3 : C 17 120 3 := by decide +kernel
theorem cell_17_120_4 : C 17 120 4 := by decide +kernel
theorem cell_17_120_5 : C 17 120 5 := by decide +kernel
theorem row_17_120 : ThresholdAt 17 120 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 120 0 cell_17_120_0
  | exact S 17 120 1 cell_17_120_1
  | exact S 17 120 2 cell_17_120_2
  | exact S 17 120 3 cell_17_120_3
  | exact S 17 120 4 cell_17_120_4
  | exact S 17 120 5 cell_17_120_5
theorem cell_17_121_0 : C 17 121 0 := by decide +kernel
theorem cell_17_121_1 : C 17 121 1 := by decide +kernel
theorem cell_17_121_2 : C 17 121 2 := by decide +kernel
theorem cell_17_121_3 : C 17 121 3 := by decide +kernel
theorem cell_17_121_4 : C 17 121 4 := by decide +kernel
theorem cell_17_121_5 : C 17 121 5 := by decide +kernel
theorem row_17_121 : ThresholdAt 17 121 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 121 0 cell_17_121_0
  | exact S 17 121 1 cell_17_121_1
  | exact S 17 121 2 cell_17_121_2
  | exact S 17 121 3 cell_17_121_3
  | exact S 17 121 4 cell_17_121_4
  | exact S 17 121 5 cell_17_121_5
theorem cell_17_122_0 : C 17 122 0 := by decide +kernel
theorem cell_17_122_1 : C 17 122 1 := by decide +kernel
theorem cell_17_122_2 : C 17 122 2 := by decide +kernel
theorem cell_17_122_3 : C 17 122 3 := by decide +kernel
theorem cell_17_122_4 : C 17 122 4 := by decide +kernel
theorem cell_17_122_5 : C 17 122 5 := by decide +kernel
theorem row_17_122 : ThresholdAt 17 122 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 17 122 0 cell_17_122_0
  | exact S 17 122 1 cell_17_122_1
  | exact S 17 122 2 cell_17_122_2
  | exact S 17 122 3 cell_17_122_3
  | exact S 17 122 4 cell_17_122_4
  | exact S 17 122 5 cell_17_122_5
theorem checkedR17 : ∀ V ∈ List.range 123, ThresholdAt 17 V := by
  intro V hV
  have hv : V < 123 := List.mem_range.mp hV
  by_cases h0_123 : V < 61
  · by_cases h0_61 : V < 30
    · by_cases h0_30 : V < 15
      · by_cases h0_15 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have he : V = 0 := by omega
              subst V
              exact row_17_0
            · by_cases h1_3 : V < 2
              · have he : V = 1 := by omega
                subst V
                exact row_17_1
              · have he : V = 2 := by omega
                subst V
                exact row_17_2
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have he : V = 3 := by omega
                subst V
                exact row_17_3
              · have he : V = 4 := by omega
                subst V
                exact row_17_4
            · by_cases h5_7 : V < 6
              · have he : V = 5 := by omega
                subst V
                exact row_17_5
              · have he : V = 6 := by omega
                subst V
                exact row_17_6
        · by_cases h7_15 : V < 11
          · by_cases h7_11 : V < 9
            · by_cases h7_9 : V < 8
              · have he : V = 7 := by omega
                subst V
                exact row_17_7
              · have he : V = 8 := by omega
                subst V
                exact row_17_8
            · by_cases h9_11 : V < 10
              · have he : V = 9 := by omega
                subst V
                exact row_17_9
              · have he : V = 10 := by omega
                subst V
                exact row_17_10
          · by_cases h11_15 : V < 13
            · by_cases h11_13 : V < 12
              · have he : V = 11 := by omega
                subst V
                exact row_17_11
              · have he : V = 12 := by omega
                subst V
                exact row_17_12
            · by_cases h13_15 : V < 14
              · have he : V = 13 := by omega
                subst V
                exact row_17_13
              · have he : V = 14 := by omega
                subst V
                exact row_17_14
      · by_cases h15_30 : V < 22
        · by_cases h15_22 : V < 18
          · by_cases h15_18 : V < 16
            · have he : V = 15 := by omega
              subst V
              exact row_17_15
            · by_cases h16_18 : V < 17
              · have he : V = 16 := by omega
                subst V
                exact row_17_16
              · have he : V = 17 := by omega
                subst V
                exact row_17_17
          · by_cases h18_22 : V < 20
            · by_cases h18_20 : V < 19
              · have he : V = 18 := by omega
                subst V
                exact row_17_18
              · have he : V = 19 := by omega
                subst V
                exact row_17_19
            · by_cases h20_22 : V < 21
              · have he : V = 20 := by omega
                subst V
                exact row_17_20
              · have he : V = 21 := by omega
                subst V
                exact row_17_21
        · by_cases h22_30 : V < 26
          · by_cases h22_26 : V < 24
            · by_cases h22_24 : V < 23
              · have he : V = 22 := by omega
                subst V
                exact row_17_22
              · have he : V = 23 := by omega
                subst V
                exact row_17_23
            · by_cases h24_26 : V < 25
              · have he : V = 24 := by omega
                subst V
                exact row_17_24
              · have he : V = 25 := by omega
                subst V
                exact row_17_25
          · by_cases h26_30 : V < 28
            · by_cases h26_28 : V < 27
              · have he : V = 26 := by omega
                subst V
                exact row_17_26
              · have he : V = 27 := by omega
                subst V
                exact row_17_27
            · by_cases h28_30 : V < 29
              · have he : V = 28 := by omega
                subst V
                exact row_17_28
              · have he : V = 29 := by omega
                subst V
                exact row_17_29
    · by_cases h30_61 : V < 45
      · by_cases h30_45 : V < 37
        · by_cases h30_37 : V < 33
          · by_cases h30_33 : V < 31
            · have he : V = 30 := by omega
              subst V
              exact row_17_30
            · by_cases h31_33 : V < 32
              · have he : V = 31 := by omega
                subst V
                exact row_17_31
              · have he : V = 32 := by omega
                subst V
                exact row_17_32
          · by_cases h33_37 : V < 35
            · by_cases h33_35 : V < 34
              · have he : V = 33 := by omega
                subst V
                exact row_17_33
              · have he : V = 34 := by omega
                subst V
                exact row_17_34
            · by_cases h35_37 : V < 36
              · have he : V = 35 := by omega
                subst V
                exact row_17_35
              · have he : V = 36 := by omega
                subst V
                exact row_17_36
        · by_cases h37_45 : V < 41
          · by_cases h37_41 : V < 39
            · by_cases h37_39 : V < 38
              · have he : V = 37 := by omega
                subst V
                exact row_17_37
              · have he : V = 38 := by omega
                subst V
                exact row_17_38
            · by_cases h39_41 : V < 40
              · have he : V = 39 := by omega
                subst V
                exact row_17_39
              · have he : V = 40 := by omega
                subst V
                exact row_17_40
          · by_cases h41_45 : V < 43
            · by_cases h41_43 : V < 42
              · have he : V = 41 := by omega
                subst V
                exact row_17_41
              · have he : V = 42 := by omega
                subst V
                exact row_17_42
            · by_cases h43_45 : V < 44
              · have he : V = 43 := by omega
                subst V
                exact row_17_43
              · have he : V = 44 := by omega
                subst V
                exact row_17_44
      · by_cases h45_61 : V < 53
        · by_cases h45_53 : V < 49
          · by_cases h45_49 : V < 47
            · by_cases h45_47 : V < 46
              · have he : V = 45 := by omega
                subst V
                exact row_17_45
              · have he : V = 46 := by omega
                subst V
                exact row_17_46
            · by_cases h47_49 : V < 48
              · have he : V = 47 := by omega
                subst V
                exact row_17_47
              · have he : V = 48 := by omega
                subst V
                exact row_17_48
          · by_cases h49_53 : V < 51
            · by_cases h49_51 : V < 50
              · have he : V = 49 := by omega
                subst V
                exact row_17_49
              · have he : V = 50 := by omega
                subst V
                exact row_17_50
            · by_cases h51_53 : V < 52
              · have he : V = 51 := by omega
                subst V
                exact row_17_51
              · have he : V = 52 := by omega
                subst V
                exact row_17_52
        · by_cases h53_61 : V < 57
          · by_cases h53_57 : V < 55
            · by_cases h53_55 : V < 54
              · have he : V = 53 := by omega
                subst V
                exact row_17_53
              · have he : V = 54 := by omega
                subst V
                exact row_17_54
            · by_cases h55_57 : V < 56
              · have he : V = 55 := by omega
                subst V
                exact row_17_55
              · have he : V = 56 := by omega
                subst V
                exact row_17_56
          · by_cases h57_61 : V < 59
            · by_cases h57_59 : V < 58
              · have he : V = 57 := by omega
                subst V
                exact row_17_57
              · have he : V = 58 := by omega
                subst V
                exact row_17_58
            · by_cases h59_61 : V < 60
              · have he : V = 59 := by omega
                subst V
                exact row_17_59
              · have he : V = 60 := by omega
                subst V
                exact row_17_60
  · by_cases h61_123 : V < 92
    · by_cases h61_92 : V < 76
      · by_cases h61_76 : V < 68
        · by_cases h61_68 : V < 64
          · by_cases h61_64 : V < 62
            · have he : V = 61 := by omega
              subst V
              exact row_17_61
            · by_cases h62_64 : V < 63
              · have he : V = 62 := by omega
                subst V
                exact row_17_62
              · have he : V = 63 := by omega
                subst V
                exact row_17_63
          · by_cases h64_68 : V < 66
            · by_cases h64_66 : V < 65
              · have he : V = 64 := by omega
                subst V
                exact row_17_64
              · have he : V = 65 := by omega
                subst V
                exact row_17_65
            · by_cases h66_68 : V < 67
              · have he : V = 66 := by omega
                subst V
                exact row_17_66
              · have he : V = 67 := by omega
                subst V
                exact row_17_67
        · by_cases h68_76 : V < 72
          · by_cases h68_72 : V < 70
            · by_cases h68_70 : V < 69
              · have he : V = 68 := by omega
                subst V
                exact row_17_68
              · have he : V = 69 := by omega
                subst V
                exact row_17_69
            · by_cases h70_72 : V < 71
              · have he : V = 70 := by omega
                subst V
                exact row_17_70
              · have he : V = 71 := by omega
                subst V
                exact row_17_71
          · by_cases h72_76 : V < 74
            · by_cases h72_74 : V < 73
              · have he : V = 72 := by omega
                subst V
                exact row_17_72
              · have he : V = 73 := by omega
                subst V
                exact row_17_73
            · by_cases h74_76 : V < 75
              · have he : V = 74 := by omega
                subst V
                exact row_17_74
              · have he : V = 75 := by omega
                subst V
                exact row_17_75
      · by_cases h76_92 : V < 84
        · by_cases h76_84 : V < 80
          · by_cases h76_80 : V < 78
            · by_cases h76_78 : V < 77
              · have he : V = 76 := by omega
                subst V
                exact row_17_76
              · have he : V = 77 := by omega
                subst V
                exact row_17_77
            · by_cases h78_80 : V < 79
              · have he : V = 78 := by omega
                subst V
                exact row_17_78
              · have he : V = 79 := by omega
                subst V
                exact row_17_79
          · by_cases h80_84 : V < 82
            · by_cases h80_82 : V < 81
              · have he : V = 80 := by omega
                subst V
                exact row_17_80
              · have he : V = 81 := by omega
                subst V
                exact row_17_81
            · by_cases h82_84 : V < 83
              · have he : V = 82 := by omega
                subst V
                exact row_17_82
              · have he : V = 83 := by omega
                subst V
                exact row_17_83
        · by_cases h84_92 : V < 88
          · by_cases h84_88 : V < 86
            · by_cases h84_86 : V < 85
              · have he : V = 84 := by omega
                subst V
                exact row_17_84
              · have he : V = 85 := by omega
                subst V
                exact row_17_85
            · by_cases h86_88 : V < 87
              · have he : V = 86 := by omega
                subst V
                exact row_17_86
              · have he : V = 87 := by omega
                subst V
                exact row_17_87
          · by_cases h88_92 : V < 90
            · by_cases h88_90 : V < 89
              · have he : V = 88 := by omega
                subst V
                exact row_17_88
              · have he : V = 89 := by omega
                subst V
                exact row_17_89
            · by_cases h90_92 : V < 91
              · have he : V = 90 := by omega
                subst V
                exact row_17_90
              · have he : V = 91 := by omega
                subst V
                exact row_17_91
    · by_cases h92_123 : V < 107
      · by_cases h92_107 : V < 99
        · by_cases h92_99 : V < 95
          · by_cases h92_95 : V < 93
            · have he : V = 92 := by omega
              subst V
              exact row_17_92
            · by_cases h93_95 : V < 94
              · have he : V = 93 := by omega
                subst V
                exact row_17_93
              · have he : V = 94 := by omega
                subst V
                exact row_17_94
          · by_cases h95_99 : V < 97
            · by_cases h95_97 : V < 96
              · have he : V = 95 := by omega
                subst V
                exact row_17_95
              · have he : V = 96 := by omega
                subst V
                exact row_17_96
            · by_cases h97_99 : V < 98
              · have he : V = 97 := by omega
                subst V
                exact row_17_97
              · have he : V = 98 := by omega
                subst V
                exact row_17_98
        · by_cases h99_107 : V < 103
          · by_cases h99_103 : V < 101
            · by_cases h99_101 : V < 100
              · have he : V = 99 := by omega
                subst V
                exact row_17_99
              · have he : V = 100 := by omega
                subst V
                exact row_17_100
            · by_cases h101_103 : V < 102
              · have he : V = 101 := by omega
                subst V
                exact row_17_101
              · have he : V = 102 := by omega
                subst V
                exact row_17_102
          · by_cases h103_107 : V < 105
            · by_cases h103_105 : V < 104
              · have he : V = 103 := by omega
                subst V
                exact row_17_103
              · have he : V = 104 := by omega
                subst V
                exact row_17_104
            · by_cases h105_107 : V < 106
              · have he : V = 105 := by omega
                subst V
                exact row_17_105
              · have he : V = 106 := by omega
                subst V
                exact row_17_106
      · by_cases h107_123 : V < 115
        · by_cases h107_115 : V < 111
          · by_cases h107_111 : V < 109
            · by_cases h107_109 : V < 108
              · have he : V = 107 := by omega
                subst V
                exact row_17_107
              · have he : V = 108 := by omega
                subst V
                exact row_17_108
            · by_cases h109_111 : V < 110
              · have he : V = 109 := by omega
                subst V
                exact row_17_109
              · have he : V = 110 := by omega
                subst V
                exact row_17_110
          · by_cases h111_115 : V < 113
            · by_cases h111_113 : V < 112
              · have he : V = 111 := by omega
                subst V
                exact row_17_111
              · have he : V = 112 := by omega
                subst V
                exact row_17_112
            · by_cases h113_115 : V < 114
              · have he : V = 113 := by omega
                subst V
                exact row_17_113
              · have he : V = 114 := by omega
                subst V
                exact row_17_114
        · by_cases h115_123 : V < 119
          · by_cases h115_119 : V < 117
            · by_cases h115_117 : V < 116
              · have he : V = 115 := by omega
                subst V
                exact row_17_115
              · have he : V = 116 := by omega
                subst V
                exact row_17_116
            · by_cases h117_119 : V < 118
              · have he : V = 117 := by omega
                subst V
                exact row_17_117
              · have he : V = 118 := by omega
                subst V
                exact row_17_118
          · by_cases h119_123 : V < 121
            · by_cases h119_121 : V < 120
              · have he : V = 119 := by omega
                subst V
                exact row_17_119
              · have he : V = 120 := by omega
                subst V
                exact row_17_120
            · by_cases h121_123 : V < 122
              · have he : V = 121 := by omega
                subst V
                exact row_17_121
              · have he : V = 122 := by omega
                subst V
                exact row_17_122
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
