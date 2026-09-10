import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked05

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_6_0_0 : C 6 0 0 := by decide +kernel
theorem cell_6_0_1 : C 6 0 1 := by decide +kernel
theorem cell_6_0_2 : C 6 0 2 := by decide +kernel
theorem cell_6_0_3 : C 6 0 3 := by decide +kernel
theorem cell_6_0_4 : C 6 0 4 := by decide +kernel
theorem cell_6_0_5 : C 6 0 5 := by decide +kernel
theorem row_6_0 : ThresholdAt 6 0 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 0 0 cell_6_0_0
  | exact S 6 0 1 cell_6_0_1
  | exact S 6 0 2 cell_6_0_2
  | exact S 6 0 3 cell_6_0_3
  | exact S 6 0 4 cell_6_0_4
  | exact S 6 0 5 cell_6_0_5
theorem cell_6_1_0 : C 6 1 0 := by decide +kernel
theorem cell_6_1_1 : C 6 1 1 := by decide +kernel
theorem cell_6_1_2 : C 6 1 2 := by decide +kernel
theorem cell_6_1_3 : C 6 1 3 := by decide +kernel
theorem cell_6_1_4 : C 6 1 4 := by decide +kernel
theorem cell_6_1_5 : C 6 1 5 := by decide +kernel
theorem row_6_1 : ThresholdAt 6 1 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 1 0 cell_6_1_0
  | exact S 6 1 1 cell_6_1_1
  | exact S 6 1 2 cell_6_1_2
  | exact S 6 1 3 cell_6_1_3
  | exact S 6 1 4 cell_6_1_4
  | exact S 6 1 5 cell_6_1_5
theorem cell_6_2_0 : C 6 2 0 := by decide +kernel
theorem cell_6_2_1 : C 6 2 1 := by decide +kernel
theorem cell_6_2_2 : C 6 2 2 := by decide +kernel
theorem cell_6_2_3 : C 6 2 3 := by decide +kernel
theorem cell_6_2_4 : C 6 2 4 := by decide +kernel
theorem cell_6_2_5 : C 6 2 5 := by decide +kernel
theorem row_6_2 : ThresholdAt 6 2 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 2 0 cell_6_2_0
  | exact S 6 2 1 cell_6_2_1
  | exact S 6 2 2 cell_6_2_2
  | exact S 6 2 3 cell_6_2_3
  | exact S 6 2 4 cell_6_2_4
  | exact S 6 2 5 cell_6_2_5
theorem cell_6_3_0 : C 6 3 0 := by decide +kernel
theorem cell_6_3_1 : C 6 3 1 := by decide +kernel
theorem cell_6_3_2 : C 6 3 2 := by decide +kernel
theorem cell_6_3_3 : C 6 3 3 := by decide +kernel
theorem cell_6_3_4 : C 6 3 4 := by decide +kernel
theorem cell_6_3_5 : C 6 3 5 := by decide +kernel
theorem row_6_3 : ThresholdAt 6 3 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 3 0 cell_6_3_0
  | exact S 6 3 1 cell_6_3_1
  | exact S 6 3 2 cell_6_3_2
  | exact S 6 3 3 cell_6_3_3
  | exact S 6 3 4 cell_6_3_4
  | exact S 6 3 5 cell_6_3_5
theorem cell_6_4_0 : C 6 4 0 := by decide +kernel
theorem cell_6_4_1 : C 6 4 1 := by decide +kernel
theorem cell_6_4_2 : C 6 4 2 := by decide +kernel
theorem cell_6_4_3 : C 6 4 3 := by decide +kernel
theorem cell_6_4_4 : C 6 4 4 := by decide +kernel
theorem cell_6_4_5 : C 6 4 5 := by decide +kernel
theorem row_6_4 : ThresholdAt 6 4 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 4 0 cell_6_4_0
  | exact S 6 4 1 cell_6_4_1
  | exact S 6 4 2 cell_6_4_2
  | exact S 6 4 3 cell_6_4_3
  | exact S 6 4 4 cell_6_4_4
  | exact S 6 4 5 cell_6_4_5
theorem cell_6_5_0 : C 6 5 0 := by decide +kernel
theorem cell_6_5_1 : C 6 5 1 := by decide +kernel
theorem cell_6_5_2 : C 6 5 2 := by decide +kernel
theorem cell_6_5_3 : C 6 5 3 := by decide +kernel
theorem cell_6_5_4 : C 6 5 4 := by decide +kernel
theorem cell_6_5_5 : C 6 5 5 := by decide +kernel
theorem row_6_5 : ThresholdAt 6 5 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 5 0 cell_6_5_0
  | exact S 6 5 1 cell_6_5_1
  | exact S 6 5 2 cell_6_5_2
  | exact S 6 5 3 cell_6_5_3
  | exact S 6 5 4 cell_6_5_4
  | exact S 6 5 5 cell_6_5_5
theorem cell_6_6_0 : C 6 6 0 := by decide +kernel
theorem cell_6_6_1 : C 6 6 1 := by decide +kernel
theorem cell_6_6_2 : C 6 6 2 := by decide +kernel
theorem cell_6_6_3 : C 6 6 3 := by decide +kernel
theorem cell_6_6_4 : C 6 6 4 := by decide +kernel
theorem cell_6_6_5 : C 6 6 5 := by decide +kernel
theorem row_6_6 : ThresholdAt 6 6 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 6 0 cell_6_6_0
  | exact S 6 6 1 cell_6_6_1
  | exact S 6 6 2 cell_6_6_2
  | exact S 6 6 3 cell_6_6_3
  | exact S 6 6 4 cell_6_6_4
  | exact S 6 6 5 cell_6_6_5
theorem cell_6_7_0 : C 6 7 0 := by decide +kernel
theorem cell_6_7_1 : C 6 7 1 := by decide +kernel
theorem cell_6_7_2 : C 6 7 2 := by decide +kernel
theorem cell_6_7_3 : C 6 7 3 := by decide +kernel
theorem cell_6_7_4 : C 6 7 4 := by decide +kernel
theorem cell_6_7_5 : C 6 7 5 := by decide +kernel
theorem row_6_7 : ThresholdAt 6 7 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 7 0 cell_6_7_0
  | exact S 6 7 1 cell_6_7_1
  | exact S 6 7 2 cell_6_7_2
  | exact S 6 7 3 cell_6_7_3
  | exact S 6 7 4 cell_6_7_4
  | exact S 6 7 5 cell_6_7_5
theorem cell_6_8_0 : C 6 8 0 := by decide +kernel
theorem cell_6_8_1 : C 6 8 1 := by decide +kernel
theorem cell_6_8_2 : C 6 8 2 := by decide +kernel
theorem cell_6_8_3 : C 6 8 3 := by decide +kernel
theorem cell_6_8_4 : C 6 8 4 := by decide +kernel
theorem cell_6_8_5 : C 6 8 5 := by decide +kernel
theorem row_6_8 : ThresholdAt 6 8 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 8 0 cell_6_8_0
  | exact S 6 8 1 cell_6_8_1
  | exact S 6 8 2 cell_6_8_2
  | exact S 6 8 3 cell_6_8_3
  | exact S 6 8 4 cell_6_8_4
  | exact S 6 8 5 cell_6_8_5
theorem cell_6_9_0 : C 6 9 0 := by decide +kernel
theorem cell_6_9_1 : C 6 9 1 := by decide +kernel
theorem cell_6_9_2 : C 6 9 2 := by decide +kernel
theorem cell_6_9_3 : C 6 9 3 := by decide +kernel
theorem cell_6_9_4 : C 6 9 4 := by decide +kernel
theorem cell_6_9_5 : C 6 9 5 := by decide +kernel
theorem row_6_9 : ThresholdAt 6 9 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 9 0 cell_6_9_0
  | exact S 6 9 1 cell_6_9_1
  | exact S 6 9 2 cell_6_9_2
  | exact S 6 9 3 cell_6_9_3
  | exact S 6 9 4 cell_6_9_4
  | exact S 6 9 5 cell_6_9_5
theorem cell_6_10_0 : C 6 10 0 := by decide +kernel
theorem cell_6_10_1 : C 6 10 1 := by decide +kernel
theorem cell_6_10_2 : C 6 10 2 := by decide +kernel
theorem cell_6_10_3 : C 6 10 3 := by decide +kernel
theorem cell_6_10_4 : C 6 10 4 := by decide +kernel
theorem cell_6_10_5 : C 6 10 5 := by decide +kernel
theorem row_6_10 : ThresholdAt 6 10 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 10 0 cell_6_10_0
  | exact S 6 10 1 cell_6_10_1
  | exact S 6 10 2 cell_6_10_2
  | exact S 6 10 3 cell_6_10_3
  | exact S 6 10 4 cell_6_10_4
  | exact S 6 10 5 cell_6_10_5
theorem cell_6_11_0 : C 6 11 0 := by decide +kernel
theorem cell_6_11_1 : C 6 11 1 := by decide +kernel
theorem cell_6_11_2 : C 6 11 2 := by decide +kernel
theorem cell_6_11_3 : C 6 11 3 := by decide +kernel
theorem cell_6_11_4 : C 6 11 4 := by decide +kernel
theorem cell_6_11_5 : C 6 11 5 := by decide +kernel
theorem row_6_11 : ThresholdAt 6 11 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 11 0 cell_6_11_0
  | exact S 6 11 1 cell_6_11_1
  | exact S 6 11 2 cell_6_11_2
  | exact S 6 11 3 cell_6_11_3
  | exact S 6 11 4 cell_6_11_4
  | exact S 6 11 5 cell_6_11_5
theorem cell_6_12_0 : C 6 12 0 := by decide +kernel
theorem cell_6_12_1 : C 6 12 1 := by decide +kernel
theorem cell_6_12_2 : C 6 12 2 := by decide +kernel
theorem cell_6_12_3 : C 6 12 3 := by decide +kernel
theorem cell_6_12_4 : C 6 12 4 := by decide +kernel
theorem cell_6_12_5 : C 6 12 5 := by decide +kernel
theorem row_6_12 : ThresholdAt 6 12 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 12 0 cell_6_12_0
  | exact S 6 12 1 cell_6_12_1
  | exact S 6 12 2 cell_6_12_2
  | exact S 6 12 3 cell_6_12_3
  | exact S 6 12 4 cell_6_12_4
  | exact S 6 12 5 cell_6_12_5
theorem cell_6_13_0 : C 6 13 0 := by decide +kernel
theorem cell_6_13_1 : C 6 13 1 := by decide +kernel
theorem cell_6_13_2 : C 6 13 2 := by decide +kernel
theorem cell_6_13_3 : C 6 13 3 := by decide +kernel
theorem cell_6_13_4 : C 6 13 4 := by decide +kernel
theorem cell_6_13_5 : C 6 13 5 := by decide +kernel
theorem row_6_13 : ThresholdAt 6 13 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 13 0 cell_6_13_0
  | exact S 6 13 1 cell_6_13_1
  | exact S 6 13 2 cell_6_13_2
  | exact S 6 13 3 cell_6_13_3
  | exact S 6 13 4 cell_6_13_4
  | exact S 6 13 5 cell_6_13_5
theorem cell_6_14_0 : C 6 14 0 := by decide +kernel
theorem cell_6_14_1 : C 6 14 1 := by decide +kernel
theorem cell_6_14_2 : C 6 14 2 := by decide +kernel
theorem cell_6_14_3 : C 6 14 3 := by decide +kernel
theorem cell_6_14_4 : C 6 14 4 := by decide +kernel
theorem cell_6_14_5 : C 6 14 5 := by decide +kernel
theorem row_6_14 : ThresholdAt 6 14 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 14 0 cell_6_14_0
  | exact S 6 14 1 cell_6_14_1
  | exact S 6 14 2 cell_6_14_2
  | exact S 6 14 3 cell_6_14_3
  | exact S 6 14 4 cell_6_14_4
  | exact S 6 14 5 cell_6_14_5
theorem cell_6_15_0 : C 6 15 0 := by decide +kernel
theorem cell_6_15_1 : C 6 15 1 := by decide +kernel
theorem cell_6_15_2 : C 6 15 2 := by decide +kernel
theorem cell_6_15_3 : C 6 15 3 := by decide +kernel
theorem cell_6_15_4 : C 6 15 4 := by decide +kernel
theorem cell_6_15_5 : C 6 15 5 := by decide +kernel
theorem row_6_15 : ThresholdAt 6 15 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 15 0 cell_6_15_0
  | exact S 6 15 1 cell_6_15_1
  | exact S 6 15 2 cell_6_15_2
  | exact S 6 15 3 cell_6_15_3
  | exact S 6 15 4 cell_6_15_4
  | exact S 6 15 5 cell_6_15_5
theorem cell_6_16_0 : C 6 16 0 := by decide +kernel
theorem cell_6_16_1 : C 6 16 1 := by decide +kernel
theorem cell_6_16_2 : C 6 16 2 := by decide +kernel
theorem cell_6_16_3 : C 6 16 3 := by decide +kernel
theorem cell_6_16_4 : C 6 16 4 := by decide +kernel
theorem cell_6_16_5 : C 6 16 5 := by decide +kernel
theorem row_6_16 : ThresholdAt 6 16 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 16 0 cell_6_16_0
  | exact S 6 16 1 cell_6_16_1
  | exact S 6 16 2 cell_6_16_2
  | exact S 6 16 3 cell_6_16_3
  | exact S 6 16 4 cell_6_16_4
  | exact S 6 16 5 cell_6_16_5
theorem cell_6_17_0 : C 6 17 0 := by decide +kernel
theorem cell_6_17_1 : C 6 17 1 := by decide +kernel
theorem cell_6_17_2 : C 6 17 2 := by decide +kernel
theorem cell_6_17_3 : C 6 17 3 := by decide +kernel
theorem cell_6_17_4 : C 6 17 4 := by decide +kernel
theorem cell_6_17_5 : C 6 17 5 := by decide +kernel
theorem row_6_17 : ThresholdAt 6 17 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 17 0 cell_6_17_0
  | exact S 6 17 1 cell_6_17_1
  | exact S 6 17 2 cell_6_17_2
  | exact S 6 17 3 cell_6_17_3
  | exact S 6 17 4 cell_6_17_4
  | exact S 6 17 5 cell_6_17_5
theorem cell_6_18_0 : C 6 18 0 := by decide +kernel
theorem cell_6_18_1 : C 6 18 1 := by decide +kernel
theorem cell_6_18_2 : C 6 18 2 := by decide +kernel
theorem cell_6_18_3 : C 6 18 3 := by decide +kernel
theorem cell_6_18_4 : C 6 18 4 := by decide +kernel
theorem cell_6_18_5 : C 6 18 5 := by decide +kernel
theorem row_6_18 : ThresholdAt 6 18 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 18 0 cell_6_18_0
  | exact S 6 18 1 cell_6_18_1
  | exact S 6 18 2 cell_6_18_2
  | exact S 6 18 3 cell_6_18_3
  | exact S 6 18 4 cell_6_18_4
  | exact S 6 18 5 cell_6_18_5
theorem cell_6_19_0 : C 6 19 0 := by decide +kernel
theorem cell_6_19_1 : C 6 19 1 := by decide +kernel
theorem cell_6_19_2 : C 6 19 2 := by decide +kernel
theorem cell_6_19_3 : C 6 19 3 := by decide +kernel
theorem cell_6_19_4 : C 6 19 4 := by decide +kernel
theorem cell_6_19_5 : C 6 19 5 := by decide +kernel
theorem row_6_19 : ThresholdAt 6 19 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 19 0 cell_6_19_0
  | exact S 6 19 1 cell_6_19_1
  | exact S 6 19 2 cell_6_19_2
  | exact S 6 19 3 cell_6_19_3
  | exact S 6 19 4 cell_6_19_4
  | exact S 6 19 5 cell_6_19_5
theorem cell_6_20_0 : C 6 20 0 := by decide +kernel
theorem cell_6_20_1 : C 6 20 1 := by decide +kernel
theorem cell_6_20_2 : C 6 20 2 := by decide +kernel
theorem cell_6_20_3 : C 6 20 3 := by decide +kernel
theorem cell_6_20_4 : C 6 20 4 := by decide +kernel
theorem cell_6_20_5 : C 6 20 5 := by decide +kernel
theorem row_6_20 : ThresholdAt 6 20 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 20 0 cell_6_20_0
  | exact S 6 20 1 cell_6_20_1
  | exact S 6 20 2 cell_6_20_2
  | exact S 6 20 3 cell_6_20_3
  | exact S 6 20 4 cell_6_20_4
  | exact S 6 20 5 cell_6_20_5
theorem cell_6_21_0 : C 6 21 0 := by decide +kernel
theorem cell_6_21_1 : C 6 21 1 := by decide +kernel
theorem cell_6_21_2 : C 6 21 2 := by decide +kernel
theorem cell_6_21_3 : C 6 21 3 := by decide +kernel
theorem cell_6_21_4 : C 6 21 4 := by decide +kernel
theorem cell_6_21_5 : C 6 21 5 := by decide +kernel
theorem row_6_21 : ThresholdAt 6 21 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 21 0 cell_6_21_0
  | exact S 6 21 1 cell_6_21_1
  | exact S 6 21 2 cell_6_21_2
  | exact S 6 21 3 cell_6_21_3
  | exact S 6 21 4 cell_6_21_4
  | exact S 6 21 5 cell_6_21_5
theorem cell_6_22_0 : C 6 22 0 := by decide +kernel
theorem cell_6_22_1 : C 6 22 1 := by decide +kernel
theorem cell_6_22_2 : C 6 22 2 := by decide +kernel
theorem cell_6_22_3 : C 6 22 3 := by decide +kernel
theorem cell_6_22_4 : C 6 22 4 := by decide +kernel
theorem cell_6_22_5 : C 6 22 5 := by decide +kernel
theorem row_6_22 : ThresholdAt 6 22 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 22 0 cell_6_22_0
  | exact S 6 22 1 cell_6_22_1
  | exact S 6 22 2 cell_6_22_2
  | exact S 6 22 3 cell_6_22_3
  | exact S 6 22 4 cell_6_22_4
  | exact S 6 22 5 cell_6_22_5
theorem cell_6_23_0 : C 6 23 0 := by decide +kernel
theorem cell_6_23_1 : C 6 23 1 := by decide +kernel
theorem cell_6_23_2 : C 6 23 2 := by decide +kernel
theorem cell_6_23_3 : C 6 23 3 := by decide +kernel
theorem cell_6_23_4 : C 6 23 4 := by decide +kernel
theorem cell_6_23_5 : C 6 23 5 := by decide +kernel
theorem row_6_23 : ThresholdAt 6 23 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 23 0 cell_6_23_0
  | exact S 6 23 1 cell_6_23_1
  | exact S 6 23 2 cell_6_23_2
  | exact S 6 23 3 cell_6_23_3
  | exact S 6 23 4 cell_6_23_4
  | exact S 6 23 5 cell_6_23_5
theorem cell_6_24_0 : C 6 24 0 := by decide +kernel
theorem cell_6_24_1 : C 6 24 1 := by decide +kernel
theorem cell_6_24_2 : C 6 24 2 := by decide +kernel
theorem cell_6_24_3 : C 6 24 3 := by decide +kernel
theorem cell_6_24_4 : C 6 24 4 := by decide +kernel
theorem cell_6_24_5 : C 6 24 5 := by decide +kernel
theorem row_6_24 : ThresholdAt 6 24 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 24 0 cell_6_24_0
  | exact S 6 24 1 cell_6_24_1
  | exact S 6 24 2 cell_6_24_2
  | exact S 6 24 3 cell_6_24_3
  | exact S 6 24 4 cell_6_24_4
  | exact S 6 24 5 cell_6_24_5
theorem cell_6_25_0 : C 6 25 0 := by decide +kernel
theorem cell_6_25_1 : C 6 25 1 := by decide +kernel
theorem cell_6_25_2 : C 6 25 2 := by decide +kernel
theorem cell_6_25_3 : C 6 25 3 := by decide +kernel
theorem cell_6_25_4 : C 6 25 4 := by decide +kernel
theorem cell_6_25_5 : C 6 25 5 := by decide +kernel
theorem row_6_25 : ThresholdAt 6 25 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 25 0 cell_6_25_0
  | exact S 6 25 1 cell_6_25_1
  | exact S 6 25 2 cell_6_25_2
  | exact S 6 25 3 cell_6_25_3
  | exact S 6 25 4 cell_6_25_4
  | exact S 6 25 5 cell_6_25_5
theorem cell_6_26_0 : C 6 26 0 := by decide +kernel
theorem cell_6_26_1 : C 6 26 1 := by decide +kernel
theorem cell_6_26_2 : C 6 26 2 := by decide +kernel
theorem cell_6_26_3 : C 6 26 3 := by decide +kernel
theorem cell_6_26_4 : C 6 26 4 := by decide +kernel
theorem cell_6_26_5 : C 6 26 5 := by decide +kernel
theorem row_6_26 : ThresholdAt 6 26 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 26 0 cell_6_26_0
  | exact S 6 26 1 cell_6_26_1
  | exact S 6 26 2 cell_6_26_2
  | exact S 6 26 3 cell_6_26_3
  | exact S 6 26 4 cell_6_26_4
  | exact S 6 26 5 cell_6_26_5
theorem cell_6_27_0 : C 6 27 0 := by decide +kernel
theorem cell_6_27_1 : C 6 27 1 := by decide +kernel
theorem cell_6_27_2 : C 6 27 2 := by decide +kernel
theorem cell_6_27_3 : C 6 27 3 := by decide +kernel
theorem cell_6_27_4 : C 6 27 4 := by decide +kernel
theorem cell_6_27_5 : C 6 27 5 := by decide +kernel
theorem row_6_27 : ThresholdAt 6 27 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 27 0 cell_6_27_0
  | exact S 6 27 1 cell_6_27_1
  | exact S 6 27 2 cell_6_27_2
  | exact S 6 27 3 cell_6_27_3
  | exact S 6 27 4 cell_6_27_4
  | exact S 6 27 5 cell_6_27_5
theorem cell_6_28_0 : C 6 28 0 := by decide +kernel
theorem cell_6_28_1 : C 6 28 1 := by decide +kernel
theorem cell_6_28_2 : C 6 28 2 := by decide +kernel
theorem cell_6_28_3 : C 6 28 3 := by decide +kernel
theorem cell_6_28_4 : C 6 28 4 := by decide +kernel
theorem cell_6_28_5 : C 6 28 5 := by decide +kernel
theorem row_6_28 : ThresholdAt 6 28 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 28 0 cell_6_28_0
  | exact S 6 28 1 cell_6_28_1
  | exact S 6 28 2 cell_6_28_2
  | exact S 6 28 3 cell_6_28_3
  | exact S 6 28 4 cell_6_28_4
  | exact S 6 28 5 cell_6_28_5
theorem cell_6_29_0 : C 6 29 0 := by decide +kernel
theorem cell_6_29_1 : C 6 29 1 := by decide +kernel
theorem cell_6_29_2 : C 6 29 2 := by decide +kernel
theorem cell_6_29_3 : C 6 29 3 := by decide +kernel
theorem cell_6_29_4 : C 6 29 4 := by decide +kernel
theorem cell_6_29_5 : C 6 29 5 := by decide +kernel
theorem row_6_29 : ThresholdAt 6 29 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 29 0 cell_6_29_0
  | exact S 6 29 1 cell_6_29_1
  | exact S 6 29 2 cell_6_29_2
  | exact S 6 29 3 cell_6_29_3
  | exact S 6 29 4 cell_6_29_4
  | exact S 6 29 5 cell_6_29_5
theorem cell_6_30_0 : C 6 30 0 := by decide +kernel
theorem cell_6_30_1 : C 6 30 1 := by decide +kernel
theorem cell_6_30_2 : C 6 30 2 := by decide +kernel
theorem cell_6_30_3 : C 6 30 3 := by decide +kernel
theorem cell_6_30_4 : C 6 30 4 := by decide +kernel
theorem cell_6_30_5 : C 6 30 5 := by decide +kernel
theorem row_6_30 : ThresholdAt 6 30 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 30 0 cell_6_30_0
  | exact S 6 30 1 cell_6_30_1
  | exact S 6 30 2 cell_6_30_2
  | exact S 6 30 3 cell_6_30_3
  | exact S 6 30 4 cell_6_30_4
  | exact S 6 30 5 cell_6_30_5
theorem cell_6_31_0 : C 6 31 0 := by decide +kernel
theorem cell_6_31_1 : C 6 31 1 := by decide +kernel
theorem cell_6_31_2 : C 6 31 2 := by decide +kernel
theorem cell_6_31_3 : C 6 31 3 := by decide +kernel
theorem cell_6_31_4 : C 6 31 4 := by decide +kernel
theorem cell_6_31_5 : C 6 31 5 := by decide +kernel
theorem row_6_31 : ThresholdAt 6 31 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 31 0 cell_6_31_0
  | exact S 6 31 1 cell_6_31_1
  | exact S 6 31 2 cell_6_31_2
  | exact S 6 31 3 cell_6_31_3
  | exact S 6 31 4 cell_6_31_4
  | exact S 6 31 5 cell_6_31_5
theorem cell_6_32_0 : C 6 32 0 := by decide +kernel
theorem cell_6_32_1 : C 6 32 1 := by decide +kernel
theorem cell_6_32_2 : C 6 32 2 := by decide +kernel
theorem cell_6_32_3 : C 6 32 3 := by decide +kernel
theorem cell_6_32_4 : C 6 32 4 := by decide +kernel
theorem cell_6_32_5 : C 6 32 5 := by decide +kernel
theorem row_6_32 : ThresholdAt 6 32 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 32 0 cell_6_32_0
  | exact S 6 32 1 cell_6_32_1
  | exact S 6 32 2 cell_6_32_2
  | exact S 6 32 3 cell_6_32_3
  | exact S 6 32 4 cell_6_32_4
  | exact S 6 32 5 cell_6_32_5
theorem cell_6_33_0 : C 6 33 0 := by decide +kernel
theorem cell_6_33_1 : C 6 33 1 := by decide +kernel
theorem cell_6_33_2 : C 6 33 2 := by decide +kernel
theorem cell_6_33_3 : C 6 33 3 := by decide +kernel
theorem cell_6_33_4 : C 6 33 4 := by decide +kernel
theorem cell_6_33_5 : C 6 33 5 := by decide +kernel
theorem row_6_33 : ThresholdAt 6 33 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 33 0 cell_6_33_0
  | exact S 6 33 1 cell_6_33_1
  | exact S 6 33 2 cell_6_33_2
  | exact S 6 33 3 cell_6_33_3
  | exact S 6 33 4 cell_6_33_4
  | exact S 6 33 5 cell_6_33_5
theorem cell_6_34_0 : C 6 34 0 := by decide +kernel
theorem cell_6_34_1 : C 6 34 1 := by decide +kernel
theorem cell_6_34_2 : C 6 34 2 := by decide +kernel
theorem cell_6_34_3 : C 6 34 3 := by decide +kernel
theorem cell_6_34_4 : C 6 34 4 := by decide +kernel
theorem cell_6_34_5 : C 6 34 5 := by decide +kernel
theorem row_6_34 : ThresholdAt 6 34 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 34 0 cell_6_34_0
  | exact S 6 34 1 cell_6_34_1
  | exact S 6 34 2 cell_6_34_2
  | exact S 6 34 3 cell_6_34_3
  | exact S 6 34 4 cell_6_34_4
  | exact S 6 34 5 cell_6_34_5
theorem cell_6_35_0 : C 6 35 0 := by decide +kernel
theorem cell_6_35_1 : C 6 35 1 := by decide +kernel
theorem cell_6_35_2 : C 6 35 2 := by decide +kernel
theorem cell_6_35_3 : C 6 35 3 := by decide +kernel
theorem cell_6_35_4 : C 6 35 4 := by decide +kernel
theorem cell_6_35_5 : C 6 35 5 := by decide +kernel
theorem row_6_35 : ThresholdAt 6 35 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 35 0 cell_6_35_0
  | exact S 6 35 1 cell_6_35_1
  | exact S 6 35 2 cell_6_35_2
  | exact S 6 35 3 cell_6_35_3
  | exact S 6 35 4 cell_6_35_4
  | exact S 6 35 5 cell_6_35_5
theorem cell_6_36_0 : C 6 36 0 := by decide +kernel
theorem cell_6_36_1 : C 6 36 1 := by decide +kernel
theorem cell_6_36_2 : C 6 36 2 := by decide +kernel
theorem cell_6_36_3 : C 6 36 3 := by decide +kernel
theorem cell_6_36_4 : C 6 36 4 := by decide +kernel
theorem cell_6_36_5 : C 6 36 5 := by decide +kernel
theorem row_6_36 : ThresholdAt 6 36 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 36 0 cell_6_36_0
  | exact S 6 36 1 cell_6_36_1
  | exact S 6 36 2 cell_6_36_2
  | exact S 6 36 3 cell_6_36_3
  | exact S 6 36 4 cell_6_36_4
  | exact S 6 36 5 cell_6_36_5
theorem cell_6_37_0 : C 6 37 0 := by decide +kernel
theorem cell_6_37_1 : C 6 37 1 := by decide +kernel
theorem cell_6_37_2 : C 6 37 2 := by decide +kernel
theorem cell_6_37_3 : C 6 37 3 := by decide +kernel
theorem cell_6_37_4 : C 6 37 4 := by decide +kernel
theorem cell_6_37_5 : C 6 37 5 := by decide +kernel
theorem row_6_37 : ThresholdAt 6 37 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 37 0 cell_6_37_0
  | exact S 6 37 1 cell_6_37_1
  | exact S 6 37 2 cell_6_37_2
  | exact S 6 37 3 cell_6_37_3
  | exact S 6 37 4 cell_6_37_4
  | exact S 6 37 5 cell_6_37_5
theorem cell_6_38_0 : C 6 38 0 := by decide +kernel
theorem cell_6_38_1 : C 6 38 1 := by decide +kernel
theorem cell_6_38_2 : C 6 38 2 := by decide +kernel
theorem cell_6_38_3 : C 6 38 3 := by decide +kernel
theorem cell_6_38_4 : C 6 38 4 := by decide +kernel
theorem cell_6_38_5 : C 6 38 5 := by decide +kernel
theorem row_6_38 : ThresholdAt 6 38 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 38 0 cell_6_38_0
  | exact S 6 38 1 cell_6_38_1
  | exact S 6 38 2 cell_6_38_2
  | exact S 6 38 3 cell_6_38_3
  | exact S 6 38 4 cell_6_38_4
  | exact S 6 38 5 cell_6_38_5
theorem cell_6_39_0 : C 6 39 0 := by decide +kernel
theorem cell_6_39_1 : C 6 39 1 := by decide +kernel
theorem cell_6_39_2 : C 6 39 2 := by decide +kernel
theorem cell_6_39_3 : C 6 39 3 := by decide +kernel
theorem cell_6_39_4 : C 6 39 4 := by decide +kernel
theorem cell_6_39_5 : C 6 39 5 := by decide +kernel
theorem row_6_39 : ThresholdAt 6 39 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 39 0 cell_6_39_0
  | exact S 6 39 1 cell_6_39_1
  | exact S 6 39 2 cell_6_39_2
  | exact S 6 39 3 cell_6_39_3
  | exact S 6 39 4 cell_6_39_4
  | exact S 6 39 5 cell_6_39_5
theorem cell_6_40_0 : C 6 40 0 := by decide +kernel
theorem cell_6_40_1 : C 6 40 1 := by decide +kernel
theorem cell_6_40_2 : C 6 40 2 := by decide +kernel
theorem cell_6_40_3 : C 6 40 3 := by decide +kernel
theorem cell_6_40_4 : C 6 40 4 := by decide +kernel
theorem cell_6_40_5 : C 6 40 5 := by decide +kernel
theorem row_6_40 : ThresholdAt 6 40 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 40 0 cell_6_40_0
  | exact S 6 40 1 cell_6_40_1
  | exact S 6 40 2 cell_6_40_2
  | exact S 6 40 3 cell_6_40_3
  | exact S 6 40 4 cell_6_40_4
  | exact S 6 40 5 cell_6_40_5
theorem cell_6_41_0 : C 6 41 0 := by decide +kernel
theorem cell_6_41_1 : C 6 41 1 := by decide +kernel
theorem cell_6_41_2 : C 6 41 2 := by decide +kernel
theorem cell_6_41_3 : C 6 41 3 := by decide +kernel
theorem cell_6_41_4 : C 6 41 4 := by decide +kernel
theorem cell_6_41_5 : C 6 41 5 := by decide +kernel
theorem row_6_41 : ThresholdAt 6 41 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 41 0 cell_6_41_0
  | exact S 6 41 1 cell_6_41_1
  | exact S 6 41 2 cell_6_41_2
  | exact S 6 41 3 cell_6_41_3
  | exact S 6 41 4 cell_6_41_4
  | exact S 6 41 5 cell_6_41_5
theorem cell_6_42_0 : C 6 42 0 := by decide +kernel
theorem cell_6_42_1 : C 6 42 1 := by decide +kernel
theorem cell_6_42_2 : C 6 42 2 := by decide +kernel
theorem cell_6_42_3 : C 6 42 3 := by decide +kernel
theorem cell_6_42_4 : C 6 42 4 := by decide +kernel
theorem cell_6_42_5 : C 6 42 5 := by decide +kernel
theorem row_6_42 : ThresholdAt 6 42 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 42 0 cell_6_42_0
  | exact S 6 42 1 cell_6_42_1
  | exact S 6 42 2 cell_6_42_2
  | exact S 6 42 3 cell_6_42_3
  | exact S 6 42 4 cell_6_42_4
  | exact S 6 42 5 cell_6_42_5
theorem cell_6_43_0 : C 6 43 0 := by decide +kernel
theorem cell_6_43_1 : C 6 43 1 := by decide +kernel
theorem cell_6_43_2 : C 6 43 2 := by decide +kernel
theorem cell_6_43_3 : C 6 43 3 := by decide +kernel
theorem cell_6_43_4 : C 6 43 4 := by decide +kernel
theorem cell_6_43_5 : C 6 43 5 := by decide +kernel
theorem row_6_43 : ThresholdAt 6 43 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 43 0 cell_6_43_0
  | exact S 6 43 1 cell_6_43_1
  | exact S 6 43 2 cell_6_43_2
  | exact S 6 43 3 cell_6_43_3
  | exact S 6 43 4 cell_6_43_4
  | exact S 6 43 5 cell_6_43_5
theorem cell_6_44_0 : C 6 44 0 := by decide +kernel
theorem cell_6_44_1 : C 6 44 1 := by decide +kernel
theorem cell_6_44_2 : C 6 44 2 := by decide +kernel
theorem cell_6_44_3 : C 6 44 3 := by decide +kernel
theorem cell_6_44_4 : C 6 44 4 := by decide +kernel
theorem cell_6_44_5 : C 6 44 5 := by decide +kernel
theorem row_6_44 : ThresholdAt 6 44 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 44 0 cell_6_44_0
  | exact S 6 44 1 cell_6_44_1
  | exact S 6 44 2 cell_6_44_2
  | exact S 6 44 3 cell_6_44_3
  | exact S 6 44 4 cell_6_44_4
  | exact S 6 44 5 cell_6_44_5
theorem cell_6_45_0 : C 6 45 0 := by decide +kernel
theorem cell_6_45_1 : C 6 45 1 := by decide +kernel
theorem cell_6_45_2 : C 6 45 2 := by decide +kernel
theorem cell_6_45_3 : C 6 45 3 := by decide +kernel
theorem cell_6_45_4 : C 6 45 4 := by decide +kernel
theorem cell_6_45_5 : C 6 45 5 := by decide +kernel
theorem row_6_45 : ThresholdAt 6 45 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 45 0 cell_6_45_0
  | exact S 6 45 1 cell_6_45_1
  | exact S 6 45 2 cell_6_45_2
  | exact S 6 45 3 cell_6_45_3
  | exact S 6 45 4 cell_6_45_4
  | exact S 6 45 5 cell_6_45_5
theorem cell_6_46_0 : C 6 46 0 := by decide +kernel
theorem cell_6_46_1 : C 6 46 1 := by decide +kernel
theorem cell_6_46_2 : C 6 46 2 := by decide +kernel
theorem cell_6_46_3 : C 6 46 3 := by decide +kernel
theorem cell_6_46_4 : C 6 46 4 := by decide +kernel
theorem cell_6_46_5 : C 6 46 5 := by decide +kernel
theorem row_6_46 : ThresholdAt 6 46 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 46 0 cell_6_46_0
  | exact S 6 46 1 cell_6_46_1
  | exact S 6 46 2 cell_6_46_2
  | exact S 6 46 3 cell_6_46_3
  | exact S 6 46 4 cell_6_46_4
  | exact S 6 46 5 cell_6_46_5
theorem cell_6_47_0 : C 6 47 0 := by decide +kernel
theorem cell_6_47_1 : C 6 47 1 := by decide +kernel
theorem cell_6_47_2 : C 6 47 2 := by decide +kernel
theorem cell_6_47_3 : C 6 47 3 := by decide +kernel
theorem cell_6_47_4 : C 6 47 4 := by decide +kernel
theorem cell_6_47_5 : C 6 47 5 := by decide +kernel
theorem row_6_47 : ThresholdAt 6 47 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 47 0 cell_6_47_0
  | exact S 6 47 1 cell_6_47_1
  | exact S 6 47 2 cell_6_47_2
  | exact S 6 47 3 cell_6_47_3
  | exact S 6 47 4 cell_6_47_4
  | exact S 6 47 5 cell_6_47_5
theorem cell_6_48_0 : C 6 48 0 := by decide +kernel
theorem cell_6_48_1 : C 6 48 1 := by decide +kernel
theorem cell_6_48_2 : C 6 48 2 := by decide +kernel
theorem cell_6_48_3 : C 6 48 3 := by decide +kernel
theorem cell_6_48_4 : C 6 48 4 := by decide +kernel
theorem cell_6_48_5 : C 6 48 5 := by decide +kernel
theorem row_6_48 : ThresholdAt 6 48 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 48 0 cell_6_48_0
  | exact S 6 48 1 cell_6_48_1
  | exact S 6 48 2 cell_6_48_2
  | exact S 6 48 3 cell_6_48_3
  | exact S 6 48 4 cell_6_48_4
  | exact S 6 48 5 cell_6_48_5
theorem cell_6_49_0 : C 6 49 0 := by decide +kernel
theorem cell_6_49_1 : C 6 49 1 := by decide +kernel
theorem cell_6_49_2 : C 6 49 2 := by decide +kernel
theorem cell_6_49_3 : C 6 49 3 := by decide +kernel
theorem cell_6_49_4 : C 6 49 4 := by decide +kernel
theorem cell_6_49_5 : C 6 49 5 := by decide +kernel
theorem row_6_49 : ThresholdAt 6 49 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 49 0 cell_6_49_0
  | exact S 6 49 1 cell_6_49_1
  | exact S 6 49 2 cell_6_49_2
  | exact S 6 49 3 cell_6_49_3
  | exact S 6 49 4 cell_6_49_4
  | exact S 6 49 5 cell_6_49_5
theorem cell_6_50_0 : C 6 50 0 := by decide +kernel
theorem cell_6_50_1 : C 6 50 1 := by decide +kernel
theorem cell_6_50_2 : C 6 50 2 := by decide +kernel
theorem cell_6_50_3 : C 6 50 3 := by decide +kernel
theorem cell_6_50_4 : C 6 50 4 := by decide +kernel
theorem cell_6_50_5 : C 6 50 5 := by decide +kernel
theorem row_6_50 : ThresholdAt 6 50 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 50 0 cell_6_50_0
  | exact S 6 50 1 cell_6_50_1
  | exact S 6 50 2 cell_6_50_2
  | exact S 6 50 3 cell_6_50_3
  | exact S 6 50 4 cell_6_50_4
  | exact S 6 50 5 cell_6_50_5
theorem cell_6_51_0 : C 6 51 0 := by decide +kernel
theorem cell_6_51_1 : C 6 51 1 := by decide +kernel
theorem cell_6_51_2 : C 6 51 2 := by decide +kernel
theorem cell_6_51_3 : C 6 51 3 := by decide +kernel
theorem cell_6_51_4 : C 6 51 4 := by decide +kernel
theorem cell_6_51_5 : C 6 51 5 := by decide +kernel
theorem row_6_51 : ThresholdAt 6 51 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 51 0 cell_6_51_0
  | exact S 6 51 1 cell_6_51_1
  | exact S 6 51 2 cell_6_51_2
  | exact S 6 51 3 cell_6_51_3
  | exact S 6 51 4 cell_6_51_4
  | exact S 6 51 5 cell_6_51_5
theorem cell_6_52_0 : C 6 52 0 := by decide +kernel
theorem cell_6_52_1 : C 6 52 1 := by decide +kernel
theorem cell_6_52_2 : C 6 52 2 := by decide +kernel
theorem cell_6_52_3 : C 6 52 3 := by decide +kernel
theorem cell_6_52_4 : C 6 52 4 := by decide +kernel
theorem cell_6_52_5 : C 6 52 5 := by decide +kernel
theorem row_6_52 : ThresholdAt 6 52 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 52 0 cell_6_52_0
  | exact S 6 52 1 cell_6_52_1
  | exact S 6 52 2 cell_6_52_2
  | exact S 6 52 3 cell_6_52_3
  | exact S 6 52 4 cell_6_52_4
  | exact S 6 52 5 cell_6_52_5
theorem cell_6_53_0 : C 6 53 0 := by decide +kernel
theorem cell_6_53_1 : C 6 53 1 := by decide +kernel
theorem cell_6_53_2 : C 6 53 2 := by decide +kernel
theorem cell_6_53_3 : C 6 53 3 := by decide +kernel
theorem cell_6_53_4 : C 6 53 4 := by decide +kernel
theorem cell_6_53_5 : C 6 53 5 := by decide +kernel
theorem row_6_53 : ThresholdAt 6 53 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 53 0 cell_6_53_0
  | exact S 6 53 1 cell_6_53_1
  | exact S 6 53 2 cell_6_53_2
  | exact S 6 53 3 cell_6_53_3
  | exact S 6 53 4 cell_6_53_4
  | exact S 6 53 5 cell_6_53_5
theorem cell_6_54_0 : C 6 54 0 := by decide +kernel
theorem cell_6_54_1 : C 6 54 1 := by decide +kernel
theorem cell_6_54_2 : C 6 54 2 := by decide +kernel
theorem cell_6_54_3 : C 6 54 3 := by decide +kernel
theorem cell_6_54_4 : C 6 54 4 := by decide +kernel
theorem cell_6_54_5 : C 6 54 5 := by decide +kernel
theorem row_6_54 : ThresholdAt 6 54 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 54 0 cell_6_54_0
  | exact S 6 54 1 cell_6_54_1
  | exact S 6 54 2 cell_6_54_2
  | exact S 6 54 3 cell_6_54_3
  | exact S 6 54 4 cell_6_54_4
  | exact S 6 54 5 cell_6_54_5
theorem cell_6_55_0 : C 6 55 0 := by decide +kernel
theorem cell_6_55_1 : C 6 55 1 := by decide +kernel
theorem cell_6_55_2 : C 6 55 2 := by decide +kernel
theorem cell_6_55_3 : C 6 55 3 := by decide +kernel
theorem cell_6_55_4 : C 6 55 4 := by decide +kernel
theorem cell_6_55_5 : C 6 55 5 := by decide +kernel
theorem row_6_55 : ThresholdAt 6 55 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 55 0 cell_6_55_0
  | exact S 6 55 1 cell_6_55_1
  | exact S 6 55 2 cell_6_55_2
  | exact S 6 55 3 cell_6_55_3
  | exact S 6 55 4 cell_6_55_4
  | exact S 6 55 5 cell_6_55_5
theorem cell_6_56_0 : C 6 56 0 := by decide +kernel
theorem cell_6_56_1 : C 6 56 1 := by decide +kernel
theorem cell_6_56_2 : C 6 56 2 := by decide +kernel
theorem cell_6_56_3 : C 6 56 3 := by decide +kernel
theorem cell_6_56_4 : C 6 56 4 := by decide +kernel
theorem cell_6_56_5 : C 6 56 5 := by decide +kernel
theorem row_6_56 : ThresholdAt 6 56 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 56 0 cell_6_56_0
  | exact S 6 56 1 cell_6_56_1
  | exact S 6 56 2 cell_6_56_2
  | exact S 6 56 3 cell_6_56_3
  | exact S 6 56 4 cell_6_56_4
  | exact S 6 56 5 cell_6_56_5
theorem cell_6_57_0 : C 6 57 0 := by decide +kernel
theorem cell_6_57_1 : C 6 57 1 := by decide +kernel
theorem cell_6_57_2 : C 6 57 2 := by decide +kernel
theorem cell_6_57_3 : C 6 57 3 := by decide +kernel
theorem cell_6_57_4 : C 6 57 4 := by decide +kernel
theorem cell_6_57_5 : C 6 57 5 := by decide +kernel
theorem row_6_57 : ThresholdAt 6 57 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 57 0 cell_6_57_0
  | exact S 6 57 1 cell_6_57_1
  | exact S 6 57 2 cell_6_57_2
  | exact S 6 57 3 cell_6_57_3
  | exact S 6 57 4 cell_6_57_4
  | exact S 6 57 5 cell_6_57_5
theorem cell_6_58_0 : C 6 58 0 := by decide +kernel
theorem cell_6_58_1 : C 6 58 1 := by decide +kernel
theorem cell_6_58_2 : C 6 58 2 := by decide +kernel
theorem cell_6_58_3 : C 6 58 3 := by decide +kernel
theorem cell_6_58_4 : C 6 58 4 := by decide +kernel
theorem cell_6_58_5 : C 6 58 5 := by decide +kernel
theorem row_6_58 : ThresholdAt 6 58 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 58 0 cell_6_58_0
  | exact S 6 58 1 cell_6_58_1
  | exact S 6 58 2 cell_6_58_2
  | exact S 6 58 3 cell_6_58_3
  | exact S 6 58 4 cell_6_58_4
  | exact S 6 58 5 cell_6_58_5
theorem cell_6_59_0 : C 6 59 0 := by decide +kernel
theorem cell_6_59_1 : C 6 59 1 := by decide +kernel
theorem cell_6_59_2 : C 6 59 2 := by decide +kernel
theorem cell_6_59_3 : C 6 59 3 := by decide +kernel
theorem cell_6_59_4 : C 6 59 4 := by decide +kernel
theorem cell_6_59_5 : C 6 59 5 := by decide +kernel
theorem row_6_59 : ThresholdAt 6 59 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 59 0 cell_6_59_0
  | exact S 6 59 1 cell_6_59_1
  | exact S 6 59 2 cell_6_59_2
  | exact S 6 59 3 cell_6_59_3
  | exact S 6 59 4 cell_6_59_4
  | exact S 6 59 5 cell_6_59_5
theorem cell_6_60_0 : C 6 60 0 := by decide +kernel
theorem cell_6_60_1 : C 6 60 1 := by decide +kernel
theorem cell_6_60_2 : C 6 60 2 := by decide +kernel
theorem cell_6_60_3 : C 6 60 3 := by decide +kernel
theorem cell_6_60_4 : C 6 60 4 := by decide +kernel
theorem cell_6_60_5 : C 6 60 5 := by decide +kernel
theorem row_6_60 : ThresholdAt 6 60 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 60 0 cell_6_60_0
  | exact S 6 60 1 cell_6_60_1
  | exact S 6 60 2 cell_6_60_2
  | exact S 6 60 3 cell_6_60_3
  | exact S 6 60 4 cell_6_60_4
  | exact S 6 60 5 cell_6_60_5
theorem cell_6_61_0 : C 6 61 0 := by decide +kernel
theorem cell_6_61_1 : C 6 61 1 := by decide +kernel
theorem cell_6_61_2 : C 6 61 2 := by decide +kernel
theorem cell_6_61_3 : C 6 61 3 := by decide +kernel
theorem cell_6_61_4 : C 6 61 4 := by decide +kernel
theorem cell_6_61_5 : C 6 61 5 := by decide +kernel
theorem row_6_61 : ThresholdAt 6 61 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 61 0 cell_6_61_0
  | exact S 6 61 1 cell_6_61_1
  | exact S 6 61 2 cell_6_61_2
  | exact S 6 61 3 cell_6_61_3
  | exact S 6 61 4 cell_6_61_4
  | exact S 6 61 5 cell_6_61_5
theorem cell_6_62_0 : C 6 62 0 := by decide +kernel
theorem cell_6_62_1 : C 6 62 1 := by decide +kernel
theorem cell_6_62_2 : C 6 62 2 := by decide +kernel
theorem cell_6_62_3 : C 6 62 3 := by decide +kernel
theorem cell_6_62_4 : C 6 62 4 := by decide +kernel
theorem cell_6_62_5 : C 6 62 5 := by decide +kernel
theorem row_6_62 : ThresholdAt 6 62 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 62 0 cell_6_62_0
  | exact S 6 62 1 cell_6_62_1
  | exact S 6 62 2 cell_6_62_2
  | exact S 6 62 3 cell_6_62_3
  | exact S 6 62 4 cell_6_62_4
  | exact S 6 62 5 cell_6_62_5
theorem cell_6_63_0 : C 6 63 0 := by decide +kernel
theorem cell_6_63_1 : C 6 63 1 := by decide +kernel
theorem cell_6_63_2 : C 6 63 2 := by decide +kernel
theorem cell_6_63_3 : C 6 63 3 := by decide +kernel
theorem cell_6_63_4 : C 6 63 4 := by decide +kernel
theorem cell_6_63_5 : C 6 63 5 := by decide +kernel
theorem row_6_63 : ThresholdAt 6 63 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 63 0 cell_6_63_0
  | exact S 6 63 1 cell_6_63_1
  | exact S 6 63 2 cell_6_63_2
  | exact S 6 63 3 cell_6_63_3
  | exact S 6 63 4 cell_6_63_4
  | exact S 6 63 5 cell_6_63_5
theorem cell_6_64_0 : C 6 64 0 := by decide +kernel
theorem cell_6_64_1 : C 6 64 1 := by decide +kernel
theorem cell_6_64_2 : C 6 64 2 := by decide +kernel
theorem cell_6_64_3 : C 6 64 3 := by decide +kernel
theorem cell_6_64_4 : C 6 64 4 := by decide +kernel
theorem cell_6_64_5 : C 6 64 5 := by decide +kernel
theorem row_6_64 : ThresholdAt 6 64 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 64 0 cell_6_64_0
  | exact S 6 64 1 cell_6_64_1
  | exact S 6 64 2 cell_6_64_2
  | exact S 6 64 3 cell_6_64_3
  | exact S 6 64 4 cell_6_64_4
  | exact S 6 64 5 cell_6_64_5
theorem cell_6_65_0 : C 6 65 0 := by decide +kernel
theorem cell_6_65_1 : C 6 65 1 := by decide +kernel
theorem cell_6_65_2 : C 6 65 2 := by decide +kernel
theorem cell_6_65_3 : C 6 65 3 := by decide +kernel
theorem cell_6_65_4 : C 6 65 4 := by decide +kernel
theorem cell_6_65_5 : C 6 65 5 := by decide +kernel
theorem row_6_65 : ThresholdAt 6 65 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 65 0 cell_6_65_0
  | exact S 6 65 1 cell_6_65_1
  | exact S 6 65 2 cell_6_65_2
  | exact S 6 65 3 cell_6_65_3
  | exact S 6 65 4 cell_6_65_4
  | exact S 6 65 5 cell_6_65_5
theorem cell_6_66_0 : C 6 66 0 := by decide +kernel
theorem cell_6_66_1 : C 6 66 1 := by decide +kernel
theorem cell_6_66_2 : C 6 66 2 := by decide +kernel
theorem cell_6_66_3 : C 6 66 3 := by decide +kernel
theorem cell_6_66_4 : C 6 66 4 := by decide +kernel
theorem cell_6_66_5 : C 6 66 5 := by decide +kernel
theorem row_6_66 : ThresholdAt 6 66 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 66 0 cell_6_66_0
  | exact S 6 66 1 cell_6_66_1
  | exact S 6 66 2 cell_6_66_2
  | exact S 6 66 3 cell_6_66_3
  | exact S 6 66 4 cell_6_66_4
  | exact S 6 66 5 cell_6_66_5
theorem cell_6_67_0 : C 6 67 0 := by decide +kernel
theorem cell_6_67_1 : C 6 67 1 := by decide +kernel
theorem cell_6_67_2 : C 6 67 2 := by decide +kernel
theorem cell_6_67_3 : C 6 67 3 := by decide +kernel
theorem cell_6_67_4 : C 6 67 4 := by decide +kernel
theorem cell_6_67_5 : C 6 67 5 := by decide +kernel
theorem row_6_67 : ThresholdAt 6 67 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 67 0 cell_6_67_0
  | exact S 6 67 1 cell_6_67_1
  | exact S 6 67 2 cell_6_67_2
  | exact S 6 67 3 cell_6_67_3
  | exact S 6 67 4 cell_6_67_4
  | exact S 6 67 5 cell_6_67_5
theorem cell_6_68_0 : C 6 68 0 := by decide +kernel
theorem cell_6_68_1 : C 6 68 1 := by decide +kernel
theorem cell_6_68_2 : C 6 68 2 := by decide +kernel
theorem cell_6_68_3 : C 6 68 3 := by decide +kernel
theorem cell_6_68_4 : C 6 68 4 := by decide +kernel
theorem cell_6_68_5 : C 6 68 5 := by decide +kernel
theorem row_6_68 : ThresholdAt 6 68 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 68 0 cell_6_68_0
  | exact S 6 68 1 cell_6_68_1
  | exact S 6 68 2 cell_6_68_2
  | exact S 6 68 3 cell_6_68_3
  | exact S 6 68 4 cell_6_68_4
  | exact S 6 68 5 cell_6_68_5
theorem cell_6_69_0 : C 6 69 0 := by decide +kernel
theorem cell_6_69_1 : C 6 69 1 := by decide +kernel
theorem cell_6_69_2 : C 6 69 2 := by decide +kernel
theorem cell_6_69_3 : C 6 69 3 := by decide +kernel
theorem cell_6_69_4 : C 6 69 4 := by decide +kernel
theorem cell_6_69_5 : C 6 69 5 := by decide +kernel
theorem row_6_69 : ThresholdAt 6 69 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 69 0 cell_6_69_0
  | exact S 6 69 1 cell_6_69_1
  | exact S 6 69 2 cell_6_69_2
  | exact S 6 69 3 cell_6_69_3
  | exact S 6 69 4 cell_6_69_4
  | exact S 6 69 5 cell_6_69_5
theorem cell_6_70_0 : C 6 70 0 := by decide +kernel
theorem cell_6_70_1 : C 6 70 1 := by decide +kernel
theorem cell_6_70_2 : C 6 70 2 := by decide +kernel
theorem cell_6_70_3 : C 6 70 3 := by decide +kernel
theorem cell_6_70_4 : C 6 70 4 := by decide +kernel
theorem cell_6_70_5 : C 6 70 5 := by decide +kernel
theorem row_6_70 : ThresholdAt 6 70 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 70 0 cell_6_70_0
  | exact S 6 70 1 cell_6_70_1
  | exact S 6 70 2 cell_6_70_2
  | exact S 6 70 3 cell_6_70_3
  | exact S 6 70 4 cell_6_70_4
  | exact S 6 70 5 cell_6_70_5
theorem cell_6_71_0 : C 6 71 0 := by decide +kernel
theorem cell_6_71_1 : C 6 71 1 := by decide +kernel
theorem cell_6_71_2 : C 6 71 2 := by decide +kernel
theorem cell_6_71_3 : C 6 71 3 := by decide +kernel
theorem cell_6_71_4 : C 6 71 4 := by decide +kernel
theorem cell_6_71_5 : C 6 71 5 := by decide +kernel
theorem row_6_71 : ThresholdAt 6 71 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 71 0 cell_6_71_0
  | exact S 6 71 1 cell_6_71_1
  | exact S 6 71 2 cell_6_71_2
  | exact S 6 71 3 cell_6_71_3
  | exact S 6 71 4 cell_6_71_4
  | exact S 6 71 5 cell_6_71_5
theorem cell_6_72_0 : C 6 72 0 := by decide +kernel
theorem cell_6_72_1 : C 6 72 1 := by decide +kernel
theorem cell_6_72_2 : C 6 72 2 := by decide +kernel
theorem cell_6_72_3 : C 6 72 3 := by decide +kernel
theorem cell_6_72_4 : C 6 72 4 := by decide +kernel
theorem cell_6_72_5 : C 6 72 5 := by decide +kernel
theorem row_6_72 : ThresholdAt 6 72 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 72 0 cell_6_72_0
  | exact S 6 72 1 cell_6_72_1
  | exact S 6 72 2 cell_6_72_2
  | exact S 6 72 3 cell_6_72_3
  | exact S 6 72 4 cell_6_72_4
  | exact S 6 72 5 cell_6_72_5
theorem cell_6_73_0 : C 6 73 0 := by decide +kernel
theorem cell_6_73_1 : C 6 73 1 := by decide +kernel
theorem cell_6_73_2 : C 6 73 2 := by decide +kernel
theorem cell_6_73_3 : C 6 73 3 := by decide +kernel
theorem cell_6_73_4 : C 6 73 4 := by decide +kernel
theorem cell_6_73_5 : C 6 73 5 := by decide +kernel
theorem row_6_73 : ThresholdAt 6 73 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 73 0 cell_6_73_0
  | exact S 6 73 1 cell_6_73_1
  | exact S 6 73 2 cell_6_73_2
  | exact S 6 73 3 cell_6_73_3
  | exact S 6 73 4 cell_6_73_4
  | exact S 6 73 5 cell_6_73_5
theorem cell_6_74_0 : C 6 74 0 := by decide +kernel
theorem cell_6_74_1 : C 6 74 1 := by decide +kernel
theorem cell_6_74_2 : C 6 74 2 := by decide +kernel
theorem cell_6_74_3 : C 6 74 3 := by decide +kernel
theorem cell_6_74_4 : C 6 74 4 := by decide +kernel
theorem cell_6_74_5 : C 6 74 5 := by decide +kernel
theorem row_6_74 : ThresholdAt 6 74 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 74 0 cell_6_74_0
  | exact S 6 74 1 cell_6_74_1
  | exact S 6 74 2 cell_6_74_2
  | exact S 6 74 3 cell_6_74_3
  | exact S 6 74 4 cell_6_74_4
  | exact S 6 74 5 cell_6_74_5
theorem cell_6_75_0 : C 6 75 0 := by decide +kernel
theorem cell_6_75_1 : C 6 75 1 := by decide +kernel
theorem cell_6_75_2 : C 6 75 2 := by decide +kernel
theorem cell_6_75_3 : C 6 75 3 := by decide +kernel
theorem cell_6_75_4 : C 6 75 4 := by decide +kernel
theorem cell_6_75_5 : C 6 75 5 := by decide +kernel
theorem row_6_75 : ThresholdAt 6 75 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 75 0 cell_6_75_0
  | exact S 6 75 1 cell_6_75_1
  | exact S 6 75 2 cell_6_75_2
  | exact S 6 75 3 cell_6_75_3
  | exact S 6 75 4 cell_6_75_4
  | exact S 6 75 5 cell_6_75_5
theorem cell_6_76_0 : C 6 76 0 := by decide +kernel
theorem cell_6_76_1 : C 6 76 1 := by decide +kernel
theorem cell_6_76_2 : C 6 76 2 := by decide +kernel
theorem cell_6_76_3 : C 6 76 3 := by decide +kernel
theorem cell_6_76_4 : C 6 76 4 := by decide +kernel
theorem cell_6_76_5 : C 6 76 5 := by decide +kernel
theorem row_6_76 : ThresholdAt 6 76 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 76 0 cell_6_76_0
  | exact S 6 76 1 cell_6_76_1
  | exact S 6 76 2 cell_6_76_2
  | exact S 6 76 3 cell_6_76_3
  | exact S 6 76 4 cell_6_76_4
  | exact S 6 76 5 cell_6_76_5
theorem cell_6_77_0 : C 6 77 0 := by decide +kernel
theorem cell_6_77_1 : C 6 77 1 := by decide +kernel
theorem cell_6_77_2 : C 6 77 2 := by decide +kernel
theorem cell_6_77_3 : C 6 77 3 := by decide +kernel
theorem cell_6_77_4 : C 6 77 4 := by decide +kernel
theorem cell_6_77_5 : C 6 77 5 := by decide +kernel
theorem row_6_77 : ThresholdAt 6 77 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 77 0 cell_6_77_0
  | exact S 6 77 1 cell_6_77_1
  | exact S 6 77 2 cell_6_77_2
  | exact S 6 77 3 cell_6_77_3
  | exact S 6 77 4 cell_6_77_4
  | exact S 6 77 5 cell_6_77_5
theorem cell_6_78_0 : C 6 78 0 := by decide +kernel
theorem cell_6_78_1 : C 6 78 1 := by decide +kernel
theorem cell_6_78_2 : C 6 78 2 := by decide +kernel
theorem cell_6_78_3 : C 6 78 3 := by decide +kernel
theorem cell_6_78_4 : C 6 78 4 := by decide +kernel
theorem cell_6_78_5 : C 6 78 5 := by decide +kernel
theorem row_6_78 : ThresholdAt 6 78 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 78 0 cell_6_78_0
  | exact S 6 78 1 cell_6_78_1
  | exact S 6 78 2 cell_6_78_2
  | exact S 6 78 3 cell_6_78_3
  | exact S 6 78 4 cell_6_78_4
  | exact S 6 78 5 cell_6_78_5
theorem cell_6_79_0 : C 6 79 0 := by decide +kernel
theorem cell_6_79_1 : C 6 79 1 := by decide +kernel
theorem cell_6_79_2 : C 6 79 2 := by decide +kernel
theorem cell_6_79_3 : C 6 79 3 := by decide +kernel
theorem cell_6_79_4 : C 6 79 4 := by decide +kernel
theorem cell_6_79_5 : C 6 79 5 := by decide +kernel
theorem row_6_79 : ThresholdAt 6 79 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 79 0 cell_6_79_0
  | exact S 6 79 1 cell_6_79_1
  | exact S 6 79 2 cell_6_79_2
  | exact S 6 79 3 cell_6_79_3
  | exact S 6 79 4 cell_6_79_4
  | exact S 6 79 5 cell_6_79_5
theorem cell_6_80_0 : C 6 80 0 := by decide +kernel
theorem cell_6_80_1 : C 6 80 1 := by decide +kernel
theorem cell_6_80_2 : C 6 80 2 := by decide +kernel
theorem cell_6_80_3 : C 6 80 3 := by decide +kernel
theorem cell_6_80_4 : C 6 80 4 := by decide +kernel
theorem cell_6_80_5 : C 6 80 5 := by decide +kernel
theorem row_6_80 : ThresholdAt 6 80 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 80 0 cell_6_80_0
  | exact S 6 80 1 cell_6_80_1
  | exact S 6 80 2 cell_6_80_2
  | exact S 6 80 3 cell_6_80_3
  | exact S 6 80 4 cell_6_80_4
  | exact S 6 80 5 cell_6_80_5
theorem cell_6_81_0 : C 6 81 0 := by decide +kernel
theorem cell_6_81_1 : C 6 81 1 := by decide +kernel
theorem cell_6_81_2 : C 6 81 2 := by decide +kernel
theorem cell_6_81_3 : C 6 81 3 := by decide +kernel
theorem cell_6_81_4 : C 6 81 4 := by decide +kernel
theorem cell_6_81_5 : C 6 81 5 := by decide +kernel
theorem row_6_81 : ThresholdAt 6 81 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 81 0 cell_6_81_0
  | exact S 6 81 1 cell_6_81_1
  | exact S 6 81 2 cell_6_81_2
  | exact S 6 81 3 cell_6_81_3
  | exact S 6 81 4 cell_6_81_4
  | exact S 6 81 5 cell_6_81_5
theorem cell_6_82_0 : C 6 82 0 := by decide +kernel
theorem cell_6_82_1 : C 6 82 1 := by decide +kernel
theorem cell_6_82_2 : C 6 82 2 := by decide +kernel
theorem cell_6_82_3 : C 6 82 3 := by decide +kernel
theorem cell_6_82_4 : C 6 82 4 := by decide +kernel
theorem cell_6_82_5 : C 6 82 5 := by decide +kernel
theorem row_6_82 : ThresholdAt 6 82 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 82 0 cell_6_82_0
  | exact S 6 82 1 cell_6_82_1
  | exact S 6 82 2 cell_6_82_2
  | exact S 6 82 3 cell_6_82_3
  | exact S 6 82 4 cell_6_82_4
  | exact S 6 82 5 cell_6_82_5
theorem cell_6_83_0 : C 6 83 0 := by decide +kernel
theorem cell_6_83_1 : C 6 83 1 := by decide +kernel
theorem cell_6_83_2 : C 6 83 2 := by decide +kernel
theorem cell_6_83_3 : C 6 83 3 := by decide +kernel
theorem cell_6_83_4 : C 6 83 4 := by decide +kernel
theorem cell_6_83_5 : C 6 83 5 := by decide +kernel
theorem row_6_83 : ThresholdAt 6 83 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 83 0 cell_6_83_0
  | exact S 6 83 1 cell_6_83_1
  | exact S 6 83 2 cell_6_83_2
  | exact S 6 83 3 cell_6_83_3
  | exact S 6 83 4 cell_6_83_4
  | exact S 6 83 5 cell_6_83_5
theorem cell_6_84_0 : C 6 84 0 := by decide +kernel
theorem cell_6_84_1 : C 6 84 1 := by decide +kernel
theorem cell_6_84_2 : C 6 84 2 := by decide +kernel
theorem cell_6_84_3 : C 6 84 3 := by decide +kernel
theorem cell_6_84_4 : C 6 84 4 := by decide +kernel
theorem cell_6_84_5 : C 6 84 5 := by decide +kernel
theorem row_6_84 : ThresholdAt 6 84 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 84 0 cell_6_84_0
  | exact S 6 84 1 cell_6_84_1
  | exact S 6 84 2 cell_6_84_2
  | exact S 6 84 3 cell_6_84_3
  | exact S 6 84 4 cell_6_84_4
  | exact S 6 84 5 cell_6_84_5
theorem cell_6_85_0 : C 6 85 0 := by decide +kernel
theorem cell_6_85_1 : C 6 85 1 := by decide +kernel
theorem cell_6_85_2 : C 6 85 2 := by decide +kernel
theorem cell_6_85_3 : C 6 85 3 := by decide +kernel
theorem cell_6_85_4 : C 6 85 4 := by decide +kernel
theorem cell_6_85_5 : C 6 85 5 := by decide +kernel
theorem row_6_85 : ThresholdAt 6 85 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 85 0 cell_6_85_0
  | exact S 6 85 1 cell_6_85_1
  | exact S 6 85 2 cell_6_85_2
  | exact S 6 85 3 cell_6_85_3
  | exact S 6 85 4 cell_6_85_4
  | exact S 6 85 5 cell_6_85_5
theorem cell_6_86_0 : C 6 86 0 := by decide +kernel
theorem cell_6_86_1 : C 6 86 1 := by decide +kernel
theorem cell_6_86_2 : C 6 86 2 := by decide +kernel
theorem cell_6_86_3 : C 6 86 3 := by decide +kernel
theorem cell_6_86_4 : C 6 86 4 := by decide +kernel
theorem cell_6_86_5 : C 6 86 5 := by decide +kernel
theorem row_6_86 : ThresholdAt 6 86 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 86 0 cell_6_86_0
  | exact S 6 86 1 cell_6_86_1
  | exact S 6 86 2 cell_6_86_2
  | exact S 6 86 3 cell_6_86_3
  | exact S 6 86 4 cell_6_86_4
  | exact S 6 86 5 cell_6_86_5
theorem cell_6_87_0 : C 6 87 0 := by decide +kernel
theorem cell_6_87_1 : C 6 87 1 := by decide +kernel
theorem cell_6_87_2 : C 6 87 2 := by decide +kernel
theorem cell_6_87_3 : C 6 87 3 := by decide +kernel
theorem cell_6_87_4 : C 6 87 4 := by decide +kernel
theorem cell_6_87_5 : C 6 87 5 := by decide +kernel
theorem row_6_87 : ThresholdAt 6 87 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 87 0 cell_6_87_0
  | exact S 6 87 1 cell_6_87_1
  | exact S 6 87 2 cell_6_87_2
  | exact S 6 87 3 cell_6_87_3
  | exact S 6 87 4 cell_6_87_4
  | exact S 6 87 5 cell_6_87_5
theorem cell_6_88_0 : C 6 88 0 := by decide +kernel
theorem cell_6_88_1 : C 6 88 1 := by decide +kernel
theorem cell_6_88_2 : C 6 88 2 := by decide +kernel
theorem cell_6_88_3 : C 6 88 3 := by decide +kernel
theorem cell_6_88_4 : C 6 88 4 := by decide +kernel
theorem cell_6_88_5 : C 6 88 5 := by decide +kernel
theorem row_6_88 : ThresholdAt 6 88 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 88 0 cell_6_88_0
  | exact S 6 88 1 cell_6_88_1
  | exact S 6 88 2 cell_6_88_2
  | exact S 6 88 3 cell_6_88_3
  | exact S 6 88 4 cell_6_88_4
  | exact S 6 88 5 cell_6_88_5
theorem cell_6_89_0 : C 6 89 0 := by decide +kernel
theorem cell_6_89_1 : C 6 89 1 := by decide +kernel
theorem cell_6_89_2 : C 6 89 2 := by decide +kernel
theorem cell_6_89_3 : C 6 89 3 := by decide +kernel
theorem cell_6_89_4 : C 6 89 4 := by decide +kernel
theorem cell_6_89_5 : C 6 89 5 := by decide +kernel
theorem row_6_89 : ThresholdAt 6 89 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 89 0 cell_6_89_0
  | exact S 6 89 1 cell_6_89_1
  | exact S 6 89 2 cell_6_89_2
  | exact S 6 89 3 cell_6_89_3
  | exact S 6 89 4 cell_6_89_4
  | exact S 6 89 5 cell_6_89_5
theorem cell_6_90_0 : C 6 90 0 := by decide +kernel
theorem cell_6_90_1 : C 6 90 1 := by decide +kernel
theorem cell_6_90_2 : C 6 90 2 := by decide +kernel
theorem cell_6_90_3 : C 6 90 3 := by decide +kernel
theorem cell_6_90_4 : C 6 90 4 := by decide +kernel
theorem cell_6_90_5 : C 6 90 5 := by decide +kernel
theorem row_6_90 : ThresholdAt 6 90 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 90 0 cell_6_90_0
  | exact S 6 90 1 cell_6_90_1
  | exact S 6 90 2 cell_6_90_2
  | exact S 6 90 3 cell_6_90_3
  | exact S 6 90 4 cell_6_90_4
  | exact S 6 90 5 cell_6_90_5
theorem cell_6_91_0 : C 6 91 0 := by decide +kernel
theorem cell_6_91_1 : C 6 91 1 := by decide +kernel
theorem cell_6_91_2 : C 6 91 2 := by decide +kernel
theorem cell_6_91_3 : C 6 91 3 := by decide +kernel
theorem cell_6_91_4 : C 6 91 4 := by decide +kernel
theorem cell_6_91_5 : C 6 91 5 := by decide +kernel
theorem row_6_91 : ThresholdAt 6 91 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 91 0 cell_6_91_0
  | exact S 6 91 1 cell_6_91_1
  | exact S 6 91 2 cell_6_91_2
  | exact S 6 91 3 cell_6_91_3
  | exact S 6 91 4 cell_6_91_4
  | exact S 6 91 5 cell_6_91_5
theorem cell_6_92_0 : C 6 92 0 := by decide +kernel
theorem cell_6_92_1 : C 6 92 1 := by decide +kernel
theorem cell_6_92_2 : C 6 92 2 := by decide +kernel
theorem cell_6_92_3 : C 6 92 3 := by decide +kernel
theorem cell_6_92_4 : C 6 92 4 := by decide +kernel
theorem cell_6_92_5 : C 6 92 5 := by decide +kernel
theorem row_6_92 : ThresholdAt 6 92 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 92 0 cell_6_92_0
  | exact S 6 92 1 cell_6_92_1
  | exact S 6 92 2 cell_6_92_2
  | exact S 6 92 3 cell_6_92_3
  | exact S 6 92 4 cell_6_92_4
  | exact S 6 92 5 cell_6_92_5
theorem cell_6_93_0 : C 6 93 0 := by decide +kernel
theorem cell_6_93_1 : C 6 93 1 := by decide +kernel
theorem cell_6_93_2 : C 6 93 2 := by decide +kernel
theorem cell_6_93_3 : C 6 93 3 := by decide +kernel
theorem cell_6_93_4 : C 6 93 4 := by decide +kernel
theorem cell_6_93_5 : C 6 93 5 := by decide +kernel
theorem row_6_93 : ThresholdAt 6 93 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 93 0 cell_6_93_0
  | exact S 6 93 1 cell_6_93_1
  | exact S 6 93 2 cell_6_93_2
  | exact S 6 93 3 cell_6_93_3
  | exact S 6 93 4 cell_6_93_4
  | exact S 6 93 5 cell_6_93_5
theorem cell_6_94_0 : C 6 94 0 := by decide +kernel
theorem cell_6_94_1 : C 6 94 1 := by decide +kernel
theorem cell_6_94_2 : C 6 94 2 := by decide +kernel
theorem cell_6_94_3 : C 6 94 3 := by decide +kernel
theorem cell_6_94_4 : C 6 94 4 := by decide +kernel
theorem cell_6_94_5 : C 6 94 5 := by decide +kernel
theorem row_6_94 : ThresholdAt 6 94 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 94 0 cell_6_94_0
  | exact S 6 94 1 cell_6_94_1
  | exact S 6 94 2 cell_6_94_2
  | exact S 6 94 3 cell_6_94_3
  | exact S 6 94 4 cell_6_94_4
  | exact S 6 94 5 cell_6_94_5
theorem cell_6_95_0 : C 6 95 0 := by decide +kernel
theorem cell_6_95_1 : C 6 95 1 := by decide +kernel
theorem cell_6_95_2 : C 6 95 2 := by decide +kernel
theorem cell_6_95_3 : C 6 95 3 := by decide +kernel
theorem cell_6_95_4 : C 6 95 4 := by decide +kernel
theorem cell_6_95_5 : C 6 95 5 := by decide +kernel
theorem row_6_95 : ThresholdAt 6 95 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 95 0 cell_6_95_0
  | exact S 6 95 1 cell_6_95_1
  | exact S 6 95 2 cell_6_95_2
  | exact S 6 95 3 cell_6_95_3
  | exact S 6 95 4 cell_6_95_4
  | exact S 6 95 5 cell_6_95_5
theorem cell_6_96_0 : C 6 96 0 := by decide +kernel
theorem cell_6_96_1 : C 6 96 1 := by decide +kernel
theorem cell_6_96_2 : C 6 96 2 := by decide +kernel
theorem cell_6_96_3 : C 6 96 3 := by decide +kernel
theorem cell_6_96_4 : C 6 96 4 := by decide +kernel
theorem cell_6_96_5 : C 6 96 5 := by decide +kernel
theorem row_6_96 : ThresholdAt 6 96 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 96 0 cell_6_96_0
  | exact S 6 96 1 cell_6_96_1
  | exact S 6 96 2 cell_6_96_2
  | exact S 6 96 3 cell_6_96_3
  | exact S 6 96 4 cell_6_96_4
  | exact S 6 96 5 cell_6_96_5
theorem cell_6_97_0 : C 6 97 0 := by decide +kernel
theorem cell_6_97_1 : C 6 97 1 := by decide +kernel
theorem cell_6_97_2 : C 6 97 2 := by decide +kernel
theorem cell_6_97_3 : C 6 97 3 := by decide +kernel
theorem cell_6_97_4 : C 6 97 4 := by decide +kernel
theorem cell_6_97_5 : C 6 97 5 := by decide +kernel
theorem row_6_97 : ThresholdAt 6 97 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 97 0 cell_6_97_0
  | exact S 6 97 1 cell_6_97_1
  | exact S 6 97 2 cell_6_97_2
  | exact S 6 97 3 cell_6_97_3
  | exact S 6 97 4 cell_6_97_4
  | exact S 6 97 5 cell_6_97_5
theorem cell_6_98_0 : C 6 98 0 := by decide +kernel
theorem cell_6_98_1 : C 6 98 1 := by decide +kernel
theorem cell_6_98_2 : C 6 98 2 := by decide +kernel
theorem cell_6_98_3 : C 6 98 3 := by decide +kernel
theorem cell_6_98_4 : C 6 98 4 := by decide +kernel
theorem cell_6_98_5 : C 6 98 5 := by decide +kernel
theorem row_6_98 : ThresholdAt 6 98 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 98 0 cell_6_98_0
  | exact S 6 98 1 cell_6_98_1
  | exact S 6 98 2 cell_6_98_2
  | exact S 6 98 3 cell_6_98_3
  | exact S 6 98 4 cell_6_98_4
  | exact S 6 98 5 cell_6_98_5
theorem cell_6_99_0 : C 6 99 0 := by decide +kernel
theorem cell_6_99_1 : C 6 99 1 := by decide +kernel
theorem cell_6_99_2 : C 6 99 2 := by decide +kernel
theorem cell_6_99_3 : C 6 99 3 := by decide +kernel
theorem cell_6_99_4 : C 6 99 4 := by decide +kernel
theorem cell_6_99_5 : C 6 99 5 := by decide +kernel
theorem row_6_99 : ThresholdAt 6 99 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 99 0 cell_6_99_0
  | exact S 6 99 1 cell_6_99_1
  | exact S 6 99 2 cell_6_99_2
  | exact S 6 99 3 cell_6_99_3
  | exact S 6 99 4 cell_6_99_4
  | exact S 6 99 5 cell_6_99_5
theorem cell_6_100_0 : C 6 100 0 := by decide +kernel
theorem cell_6_100_1 : C 6 100 1 := by decide +kernel
theorem cell_6_100_2 : C 6 100 2 := by decide +kernel
theorem cell_6_100_3 : C 6 100 3 := by decide +kernel
theorem cell_6_100_4 : C 6 100 4 := by decide +kernel
theorem cell_6_100_5 : C 6 100 5 := by decide +kernel
theorem row_6_100 : ThresholdAt 6 100 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 100 0 cell_6_100_0
  | exact S 6 100 1 cell_6_100_1
  | exact S 6 100 2 cell_6_100_2
  | exact S 6 100 3 cell_6_100_3
  | exact S 6 100 4 cell_6_100_4
  | exact S 6 100 5 cell_6_100_5
theorem cell_6_101_0 : C 6 101 0 := by decide +kernel
theorem cell_6_101_1 : C 6 101 1 := by decide +kernel
theorem cell_6_101_2 : C 6 101 2 := by decide +kernel
theorem cell_6_101_3 : C 6 101 3 := by decide +kernel
theorem cell_6_101_4 : C 6 101 4 := by decide +kernel
theorem cell_6_101_5 : C 6 101 5 := by decide +kernel
theorem row_6_101 : ThresholdAt 6 101 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 101 0 cell_6_101_0
  | exact S 6 101 1 cell_6_101_1
  | exact S 6 101 2 cell_6_101_2
  | exact S 6 101 3 cell_6_101_3
  | exact S 6 101 4 cell_6_101_4
  | exact S 6 101 5 cell_6_101_5
theorem cell_6_102_0 : C 6 102 0 := by decide +kernel
theorem cell_6_102_1 : C 6 102 1 := by decide +kernel
theorem cell_6_102_2 : C 6 102 2 := by decide +kernel
theorem cell_6_102_3 : C 6 102 3 := by decide +kernel
theorem cell_6_102_4 : C 6 102 4 := by decide +kernel
theorem cell_6_102_5 : C 6 102 5 := by decide +kernel
theorem row_6_102 : ThresholdAt 6 102 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 102 0 cell_6_102_0
  | exact S 6 102 1 cell_6_102_1
  | exact S 6 102 2 cell_6_102_2
  | exact S 6 102 3 cell_6_102_3
  | exact S 6 102 4 cell_6_102_4
  | exact S 6 102 5 cell_6_102_5
theorem cell_6_103_0 : C 6 103 0 := by decide +kernel
theorem cell_6_103_1 : C 6 103 1 := by decide +kernel
theorem cell_6_103_2 : C 6 103 2 := by decide +kernel
theorem cell_6_103_3 : C 6 103 3 := by decide +kernel
theorem cell_6_103_4 : C 6 103 4 := by decide +kernel
theorem cell_6_103_5 : C 6 103 5 := by decide +kernel
theorem row_6_103 : ThresholdAt 6 103 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 103 0 cell_6_103_0
  | exact S 6 103 1 cell_6_103_1
  | exact S 6 103 2 cell_6_103_2
  | exact S 6 103 3 cell_6_103_3
  | exact S 6 103 4 cell_6_103_4
  | exact S 6 103 5 cell_6_103_5
theorem cell_6_104_0 : C 6 104 0 := by decide +kernel
theorem cell_6_104_1 : C 6 104 1 := by decide +kernel
theorem cell_6_104_2 : C 6 104 2 := by decide +kernel
theorem cell_6_104_3 : C 6 104 3 := by decide +kernel
theorem cell_6_104_4 : C 6 104 4 := by decide +kernel
theorem cell_6_104_5 : C 6 104 5 := by decide +kernel
theorem row_6_104 : ThresholdAt 6 104 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 104 0 cell_6_104_0
  | exact S 6 104 1 cell_6_104_1
  | exact S 6 104 2 cell_6_104_2
  | exact S 6 104 3 cell_6_104_3
  | exact S 6 104 4 cell_6_104_4
  | exact S 6 104 5 cell_6_104_5
theorem cell_6_105_0 : C 6 105 0 := by decide +kernel
theorem cell_6_105_1 : C 6 105 1 := by decide +kernel
theorem cell_6_105_2 : C 6 105 2 := by decide +kernel
theorem cell_6_105_3 : C 6 105 3 := by decide +kernel
theorem cell_6_105_4 : C 6 105 4 := by decide +kernel
theorem cell_6_105_5 : C 6 105 5 := by decide +kernel
theorem row_6_105 : ThresholdAt 6 105 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 105 0 cell_6_105_0
  | exact S 6 105 1 cell_6_105_1
  | exact S 6 105 2 cell_6_105_2
  | exact S 6 105 3 cell_6_105_3
  | exact S 6 105 4 cell_6_105_4
  | exact S 6 105 5 cell_6_105_5
theorem cell_6_106_0 : C 6 106 0 := by decide +kernel
theorem cell_6_106_1 : C 6 106 1 := by decide +kernel
theorem cell_6_106_2 : C 6 106 2 := by decide +kernel
theorem cell_6_106_3 : C 6 106 3 := by decide +kernel
theorem cell_6_106_4 : C 6 106 4 := by decide +kernel
theorem cell_6_106_5 : C 6 106 5 := by decide +kernel
theorem row_6_106 : ThresholdAt 6 106 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 106 0 cell_6_106_0
  | exact S 6 106 1 cell_6_106_1
  | exact S 6 106 2 cell_6_106_2
  | exact S 6 106 3 cell_6_106_3
  | exact S 6 106 4 cell_6_106_4
  | exact S 6 106 5 cell_6_106_5
theorem cell_6_107_0 : C 6 107 0 := by decide +kernel
theorem cell_6_107_1 : C 6 107 1 := by decide +kernel
theorem cell_6_107_2 : C 6 107 2 := by decide +kernel
theorem cell_6_107_3 : C 6 107 3 := by decide +kernel
theorem cell_6_107_4 : C 6 107 4 := by decide +kernel
theorem cell_6_107_5 : C 6 107 5 := by decide +kernel
theorem row_6_107 : ThresholdAt 6 107 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 107 0 cell_6_107_0
  | exact S 6 107 1 cell_6_107_1
  | exact S 6 107 2 cell_6_107_2
  | exact S 6 107 3 cell_6_107_3
  | exact S 6 107 4 cell_6_107_4
  | exact S 6 107 5 cell_6_107_5
theorem cell_6_108_0 : C 6 108 0 := by decide +kernel
theorem cell_6_108_1 : C 6 108 1 := by decide +kernel
theorem cell_6_108_2 : C 6 108 2 := by decide +kernel
theorem cell_6_108_3 : C 6 108 3 := by decide +kernel
theorem cell_6_108_4 : C 6 108 4 := by decide +kernel
theorem cell_6_108_5 : C 6 108 5 := by decide +kernel
theorem row_6_108 : ThresholdAt 6 108 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 108 0 cell_6_108_0
  | exact S 6 108 1 cell_6_108_1
  | exact S 6 108 2 cell_6_108_2
  | exact S 6 108 3 cell_6_108_3
  | exact S 6 108 4 cell_6_108_4
  | exact S 6 108 5 cell_6_108_5
theorem cell_6_109_0 : C 6 109 0 := by decide +kernel
theorem cell_6_109_1 : C 6 109 1 := by decide +kernel
theorem cell_6_109_2 : C 6 109 2 := by decide +kernel
theorem cell_6_109_3 : C 6 109 3 := by decide +kernel
theorem cell_6_109_4 : C 6 109 4 := by decide +kernel
theorem cell_6_109_5 : C 6 109 5 := by decide +kernel
theorem row_6_109 : ThresholdAt 6 109 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 109 0 cell_6_109_0
  | exact S 6 109 1 cell_6_109_1
  | exact S 6 109 2 cell_6_109_2
  | exact S 6 109 3 cell_6_109_3
  | exact S 6 109 4 cell_6_109_4
  | exact S 6 109 5 cell_6_109_5
theorem cell_6_110_0 : C 6 110 0 := by decide +kernel
theorem cell_6_110_1 : C 6 110 1 := by decide +kernel
theorem cell_6_110_2 : C 6 110 2 := by decide +kernel
theorem cell_6_110_3 : C 6 110 3 := by decide +kernel
theorem cell_6_110_4 : C 6 110 4 := by decide +kernel
theorem cell_6_110_5 : C 6 110 5 := by decide +kernel
theorem row_6_110 : ThresholdAt 6 110 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 110 0 cell_6_110_0
  | exact S 6 110 1 cell_6_110_1
  | exact S 6 110 2 cell_6_110_2
  | exact S 6 110 3 cell_6_110_3
  | exact S 6 110 4 cell_6_110_4
  | exact S 6 110 5 cell_6_110_5
theorem cell_6_111_0 : C 6 111 0 := by decide +kernel
theorem cell_6_111_1 : C 6 111 1 := by decide +kernel
theorem cell_6_111_2 : C 6 111 2 := by decide +kernel
theorem cell_6_111_3 : C 6 111 3 := by decide +kernel
theorem cell_6_111_4 : C 6 111 4 := by decide +kernel
theorem cell_6_111_5 : C 6 111 5 := by decide +kernel
theorem row_6_111 : ThresholdAt 6 111 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 111 0 cell_6_111_0
  | exact S 6 111 1 cell_6_111_1
  | exact S 6 111 2 cell_6_111_2
  | exact S 6 111 3 cell_6_111_3
  | exact S 6 111 4 cell_6_111_4
  | exact S 6 111 5 cell_6_111_5
theorem cell_6_112_0 : C 6 112 0 := by decide +kernel
theorem cell_6_112_1 : C 6 112 1 := by decide +kernel
theorem cell_6_112_2 : C 6 112 2 := by decide +kernel
theorem cell_6_112_3 : C 6 112 3 := by decide +kernel
theorem cell_6_112_4 : C 6 112 4 := by decide +kernel
theorem cell_6_112_5 : C 6 112 5 := by decide +kernel
theorem row_6_112 : ThresholdAt 6 112 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 112 0 cell_6_112_0
  | exact S 6 112 1 cell_6_112_1
  | exact S 6 112 2 cell_6_112_2
  | exact S 6 112 3 cell_6_112_3
  | exact S 6 112 4 cell_6_112_4
  | exact S 6 112 5 cell_6_112_5
theorem cell_6_113_0 : C 6 113 0 := by decide +kernel
theorem cell_6_113_1 : C 6 113 1 := by decide +kernel
theorem cell_6_113_2 : C 6 113 2 := by decide +kernel
theorem cell_6_113_3 : C 6 113 3 := by decide +kernel
theorem cell_6_113_4 : C 6 113 4 := by decide +kernel
theorem cell_6_113_5 : C 6 113 5 := by decide +kernel
theorem row_6_113 : ThresholdAt 6 113 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 113 0 cell_6_113_0
  | exact S 6 113 1 cell_6_113_1
  | exact S 6 113 2 cell_6_113_2
  | exact S 6 113 3 cell_6_113_3
  | exact S 6 113 4 cell_6_113_4
  | exact S 6 113 5 cell_6_113_5
theorem cell_6_114_0 : C 6 114 0 := by decide +kernel
theorem cell_6_114_1 : C 6 114 1 := by decide +kernel
theorem cell_6_114_2 : C 6 114 2 := by decide +kernel
theorem cell_6_114_3 : C 6 114 3 := by decide +kernel
theorem cell_6_114_4 : C 6 114 4 := by decide +kernel
theorem cell_6_114_5 : C 6 114 5 := by decide +kernel
theorem row_6_114 : ThresholdAt 6 114 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 114 0 cell_6_114_0
  | exact S 6 114 1 cell_6_114_1
  | exact S 6 114 2 cell_6_114_2
  | exact S 6 114 3 cell_6_114_3
  | exact S 6 114 4 cell_6_114_4
  | exact S 6 114 5 cell_6_114_5
theorem cell_6_115_0 : C 6 115 0 := by decide +kernel
theorem cell_6_115_1 : C 6 115 1 := by decide +kernel
theorem cell_6_115_2 : C 6 115 2 := by decide +kernel
theorem cell_6_115_3 : C 6 115 3 := by decide +kernel
theorem cell_6_115_4 : C 6 115 4 := by decide +kernel
theorem cell_6_115_5 : C 6 115 5 := by decide +kernel
theorem row_6_115 : ThresholdAt 6 115 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 115 0 cell_6_115_0
  | exact S 6 115 1 cell_6_115_1
  | exact S 6 115 2 cell_6_115_2
  | exact S 6 115 3 cell_6_115_3
  | exact S 6 115 4 cell_6_115_4
  | exact S 6 115 5 cell_6_115_5
theorem cell_6_116_0 : C 6 116 0 := by decide +kernel
theorem cell_6_116_1 : C 6 116 1 := by decide +kernel
theorem cell_6_116_2 : C 6 116 2 := by decide +kernel
theorem cell_6_116_3 : C 6 116 3 := by decide +kernel
theorem cell_6_116_4 : C 6 116 4 := by decide +kernel
theorem cell_6_116_5 : C 6 116 5 := by decide +kernel
theorem row_6_116 : ThresholdAt 6 116 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 116 0 cell_6_116_0
  | exact S 6 116 1 cell_6_116_1
  | exact S 6 116 2 cell_6_116_2
  | exact S 6 116 3 cell_6_116_3
  | exact S 6 116 4 cell_6_116_4
  | exact S 6 116 5 cell_6_116_5
theorem cell_6_117_0 : C 6 117 0 := by decide +kernel
theorem cell_6_117_1 : C 6 117 1 := by decide +kernel
theorem cell_6_117_2 : C 6 117 2 := by decide +kernel
theorem cell_6_117_3 : C 6 117 3 := by decide +kernel
theorem cell_6_117_4 : C 6 117 4 := by decide +kernel
theorem cell_6_117_5 : C 6 117 5 := by decide +kernel
theorem row_6_117 : ThresholdAt 6 117 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 117 0 cell_6_117_0
  | exact S 6 117 1 cell_6_117_1
  | exact S 6 117 2 cell_6_117_2
  | exact S 6 117 3 cell_6_117_3
  | exact S 6 117 4 cell_6_117_4
  | exact S 6 117 5 cell_6_117_5
theorem cell_6_118_0 : C 6 118 0 := by decide +kernel
theorem cell_6_118_1 : C 6 118 1 := by decide +kernel
theorem cell_6_118_2 : C 6 118 2 := by decide +kernel
theorem cell_6_118_3 : C 6 118 3 := by decide +kernel
theorem cell_6_118_4 : C 6 118 4 := by decide +kernel
theorem cell_6_118_5 : C 6 118 5 := by decide +kernel
theorem row_6_118 : ThresholdAt 6 118 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 118 0 cell_6_118_0
  | exact S 6 118 1 cell_6_118_1
  | exact S 6 118 2 cell_6_118_2
  | exact S 6 118 3 cell_6_118_3
  | exact S 6 118 4 cell_6_118_4
  | exact S 6 118 5 cell_6_118_5
theorem cell_6_119_0 : C 6 119 0 := by decide +kernel
theorem cell_6_119_1 : C 6 119 1 := by decide +kernel
theorem cell_6_119_2 : C 6 119 2 := by decide +kernel
theorem cell_6_119_3 : C 6 119 3 := by decide +kernel
theorem cell_6_119_4 : C 6 119 4 := by decide +kernel
theorem cell_6_119_5 : C 6 119 5 := by decide +kernel
theorem row_6_119 : ThresholdAt 6 119 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 119 0 cell_6_119_0
  | exact S 6 119 1 cell_6_119_1
  | exact S 6 119 2 cell_6_119_2
  | exact S 6 119 3 cell_6_119_3
  | exact S 6 119 4 cell_6_119_4
  | exact S 6 119 5 cell_6_119_5
theorem cell_6_120_0 : C 6 120 0 := by decide +kernel
theorem cell_6_120_1 : C 6 120 1 := by decide +kernel
theorem cell_6_120_2 : C 6 120 2 := by decide +kernel
theorem cell_6_120_3 : C 6 120 3 := by decide +kernel
theorem cell_6_120_4 : C 6 120 4 := by decide +kernel
theorem cell_6_120_5 : C 6 120 5 := by decide +kernel
theorem row_6_120 : ThresholdAt 6 120 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 120 0 cell_6_120_0
  | exact S 6 120 1 cell_6_120_1
  | exact S 6 120 2 cell_6_120_2
  | exact S 6 120 3 cell_6_120_3
  | exact S 6 120 4 cell_6_120_4
  | exact S 6 120 5 cell_6_120_5
theorem cell_6_121_0 : C 6 121 0 := by decide +kernel
theorem cell_6_121_1 : C 6 121 1 := by decide +kernel
theorem cell_6_121_2 : C 6 121 2 := by decide +kernel
theorem cell_6_121_3 : C 6 121 3 := by decide +kernel
theorem cell_6_121_4 : C 6 121 4 := by decide +kernel
theorem cell_6_121_5 : C 6 121 5 := by decide +kernel
theorem row_6_121 : ThresholdAt 6 121 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 121 0 cell_6_121_0
  | exact S 6 121 1 cell_6_121_1
  | exact S 6 121 2 cell_6_121_2
  | exact S 6 121 3 cell_6_121_3
  | exact S 6 121 4 cell_6_121_4
  | exact S 6 121 5 cell_6_121_5
theorem cell_6_122_0 : C 6 122 0 := by decide +kernel
theorem cell_6_122_1 : C 6 122 1 := by decide +kernel
theorem cell_6_122_2 : C 6 122 2 := by decide +kernel
theorem cell_6_122_3 : C 6 122 3 := by decide +kernel
theorem cell_6_122_4 : C 6 122 4 := by decide +kernel
theorem cell_6_122_5 : C 6 122 5 := by decide +kernel
theorem row_6_122 : ThresholdAt 6 122 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 122 0 cell_6_122_0
  | exact S 6 122 1 cell_6_122_1
  | exact S 6 122 2 cell_6_122_2
  | exact S 6 122 3 cell_6_122_3
  | exact S 6 122 4 cell_6_122_4
  | exact S 6 122 5 cell_6_122_5
theorem cell_6_123_0 : C 6 123 0 := by decide +kernel
theorem cell_6_123_1 : C 6 123 1 := by decide +kernel
theorem cell_6_123_2 : C 6 123 2 := by decide +kernel
theorem cell_6_123_3 : C 6 123 3 := by decide +kernel
theorem cell_6_123_4 : C 6 123 4 := by decide +kernel
theorem cell_6_123_5 : C 6 123 5 := by decide +kernel
theorem row_6_123 : ThresholdAt 6 123 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 123 0 cell_6_123_0
  | exact S 6 123 1 cell_6_123_1
  | exact S 6 123 2 cell_6_123_2
  | exact S 6 123 3 cell_6_123_3
  | exact S 6 123 4 cell_6_123_4
  | exact S 6 123 5 cell_6_123_5
theorem cell_6_124_0 : C 6 124 0 := by decide +kernel
theorem cell_6_124_1 : C 6 124 1 := by decide +kernel
theorem cell_6_124_2 : C 6 124 2 := by decide +kernel
theorem cell_6_124_3 : C 6 124 3 := by decide +kernel
theorem cell_6_124_4 : C 6 124 4 := by decide +kernel
theorem cell_6_124_5 : C 6 124 5 := by decide +kernel
theorem row_6_124 : ThresholdAt 6 124 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 124 0 cell_6_124_0
  | exact S 6 124 1 cell_6_124_1
  | exact S 6 124 2 cell_6_124_2
  | exact S 6 124 3 cell_6_124_3
  | exact S 6 124 4 cell_6_124_4
  | exact S 6 124 5 cell_6_124_5
theorem cell_6_125_0 : C 6 125 0 := by decide +kernel
theorem cell_6_125_1 : C 6 125 1 := by decide +kernel
theorem cell_6_125_2 : C 6 125 2 := by decide +kernel
theorem cell_6_125_3 : C 6 125 3 := by decide +kernel
theorem cell_6_125_4 : C 6 125 4 := by decide +kernel
theorem cell_6_125_5 : C 6 125 5 := by decide +kernel
theorem row_6_125 : ThresholdAt 6 125 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 125 0 cell_6_125_0
  | exact S 6 125 1 cell_6_125_1
  | exact S 6 125 2 cell_6_125_2
  | exact S 6 125 3 cell_6_125_3
  | exact S 6 125 4 cell_6_125_4
  | exact S 6 125 5 cell_6_125_5
theorem cell_6_126_0 : C 6 126 0 := by decide +kernel
theorem cell_6_126_1 : C 6 126 1 := by decide +kernel
theorem cell_6_126_2 : C 6 126 2 := by decide +kernel
theorem cell_6_126_3 : C 6 126 3 := by decide +kernel
theorem cell_6_126_4 : C 6 126 4 := by decide +kernel
theorem cell_6_126_5 : C 6 126 5 := by decide +kernel
theorem row_6_126 : ThresholdAt 6 126 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 126 0 cell_6_126_0
  | exact S 6 126 1 cell_6_126_1
  | exact S 6 126 2 cell_6_126_2
  | exact S 6 126 3 cell_6_126_3
  | exact S 6 126 4 cell_6_126_4
  | exact S 6 126 5 cell_6_126_5
theorem cell_6_127_0 : C 6 127 0 := by decide +kernel
theorem cell_6_127_1 : C 6 127 1 := by decide +kernel
theorem cell_6_127_2 : C 6 127 2 := by decide +kernel
theorem cell_6_127_3 : C 6 127 3 := by decide +kernel
theorem cell_6_127_4 : C 6 127 4 := by decide +kernel
theorem cell_6_127_5 : C 6 127 5 := by decide +kernel
theorem row_6_127 : ThresholdAt 6 127 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 127 0 cell_6_127_0
  | exact S 6 127 1 cell_6_127_1
  | exact S 6 127 2 cell_6_127_2
  | exact S 6 127 3 cell_6_127_3
  | exact S 6 127 4 cell_6_127_4
  | exact S 6 127 5 cell_6_127_5
theorem cell_6_128_0 : C 6 128 0 := by decide +kernel
theorem cell_6_128_1 : C 6 128 1 := by decide +kernel
theorem cell_6_128_2 : C 6 128 2 := by decide +kernel
theorem cell_6_128_3 : C 6 128 3 := by decide +kernel
theorem cell_6_128_4 : C 6 128 4 := by decide +kernel
theorem cell_6_128_5 : C 6 128 5 := by decide +kernel
theorem row_6_128 : ThresholdAt 6 128 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 128 0 cell_6_128_0
  | exact S 6 128 1 cell_6_128_1
  | exact S 6 128 2 cell_6_128_2
  | exact S 6 128 3 cell_6_128_3
  | exact S 6 128 4 cell_6_128_4
  | exact S 6 128 5 cell_6_128_5
theorem cell_6_129_0 : C 6 129 0 := by decide +kernel
theorem cell_6_129_1 : C 6 129 1 := by decide +kernel
theorem cell_6_129_2 : C 6 129 2 := by decide +kernel
theorem cell_6_129_3 : C 6 129 3 := by decide +kernel
theorem cell_6_129_4 : C 6 129 4 := by decide +kernel
theorem cell_6_129_5 : C 6 129 5 := by decide +kernel
theorem row_6_129 : ThresholdAt 6 129 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 129 0 cell_6_129_0
  | exact S 6 129 1 cell_6_129_1
  | exact S 6 129 2 cell_6_129_2
  | exact S 6 129 3 cell_6_129_3
  | exact S 6 129 4 cell_6_129_4
  | exact S 6 129 5 cell_6_129_5
theorem cell_6_130_0 : C 6 130 0 := by decide +kernel
theorem cell_6_130_1 : C 6 130 1 := by decide +kernel
theorem cell_6_130_2 : C 6 130 2 := by decide +kernel
theorem cell_6_130_3 : C 6 130 3 := by decide +kernel
theorem cell_6_130_4 : C 6 130 4 := by decide +kernel
theorem cell_6_130_5 : C 6 130 5 := by decide +kernel
theorem row_6_130 : ThresholdAt 6 130 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 130 0 cell_6_130_0
  | exact S 6 130 1 cell_6_130_1
  | exact S 6 130 2 cell_6_130_2
  | exact S 6 130 3 cell_6_130_3
  | exact S 6 130 4 cell_6_130_4
  | exact S 6 130 5 cell_6_130_5
theorem cell_6_131_0 : C 6 131 0 := by decide +kernel
theorem cell_6_131_1 : C 6 131 1 := by decide +kernel
theorem cell_6_131_2 : C 6 131 2 := by decide +kernel
theorem cell_6_131_3 : C 6 131 3 := by decide +kernel
theorem cell_6_131_4 : C 6 131 4 := by decide +kernel
theorem cell_6_131_5 : C 6 131 5 := by decide +kernel
theorem row_6_131 : ThresholdAt 6 131 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 131 0 cell_6_131_0
  | exact S 6 131 1 cell_6_131_1
  | exact S 6 131 2 cell_6_131_2
  | exact S 6 131 3 cell_6_131_3
  | exact S 6 131 4 cell_6_131_4
  | exact S 6 131 5 cell_6_131_5
theorem cell_6_132_0 : C 6 132 0 := by decide +kernel
theorem cell_6_132_1 : C 6 132 1 := by decide +kernel
theorem cell_6_132_2 : C 6 132 2 := by decide +kernel
theorem cell_6_132_3 : C 6 132 3 := by decide +kernel
theorem cell_6_132_4 : C 6 132 4 := by decide +kernel
theorem cell_6_132_5 : C 6 132 5 := by decide +kernel
theorem row_6_132 : ThresholdAt 6 132 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 132 0 cell_6_132_0
  | exact S 6 132 1 cell_6_132_1
  | exact S 6 132 2 cell_6_132_2
  | exact S 6 132 3 cell_6_132_3
  | exact S 6 132 4 cell_6_132_4
  | exact S 6 132 5 cell_6_132_5
theorem cell_6_133_0 : C 6 133 0 := by decide +kernel
theorem cell_6_133_1 : C 6 133 1 := by decide +kernel
theorem cell_6_133_2 : C 6 133 2 := by decide +kernel
theorem cell_6_133_3 : C 6 133 3 := by decide +kernel
theorem cell_6_133_4 : C 6 133 4 := by decide +kernel
theorem cell_6_133_5 : C 6 133 5 := by decide +kernel
theorem row_6_133 : ThresholdAt 6 133 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 6 133 0 cell_6_133_0
  | exact S 6 133 1 cell_6_133_1
  | exact S 6 133 2 cell_6_133_2
  | exact S 6 133 3 cell_6_133_3
  | exact S 6 133 4 cell_6_133_4
  | exact S 6 133 5 cell_6_133_5
theorem checkedR6 : ∀ V ∈ List.range 134, ThresholdAt 6 V := by
  intro V hV
  have hv : V < 134 := List.mem_range.mp hV
  by_cases h0_134 : V < 67
  · by_cases h0_67 : V < 33
    · by_cases h0_33 : V < 16
      · by_cases h0_16 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have he : V = 0 := by omega
                subst V
                exact row_6_0
              · have he : V = 1 := by omega
                subst V
                exact row_6_1
            · by_cases h2_4 : V < 3
              · have he : V = 2 := by omega
                subst V
                exact row_6_2
              · have he : V = 3 := by omega
                subst V
                exact row_6_3
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have he : V = 4 := by omega
                subst V
                exact row_6_4
              · have he : V = 5 := by omega
                subst V
                exact row_6_5
            · by_cases h6_8 : V < 7
              · have he : V = 6 := by omega
                subst V
                exact row_6_6
              · have he : V = 7 := by omega
                subst V
                exact row_6_7
        · by_cases h8_16 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have he : V = 8 := by omega
                subst V
                exact row_6_8
              · have he : V = 9 := by omega
                subst V
                exact row_6_9
            · by_cases h10_12 : V < 11
              · have he : V = 10 := by omega
                subst V
                exact row_6_10
              · have he : V = 11 := by omega
                subst V
                exact row_6_11
          · by_cases h12_16 : V < 14
            · by_cases h12_14 : V < 13
              · have he : V = 12 := by omega
                subst V
                exact row_6_12
              · have he : V = 13 := by omega
                subst V
                exact row_6_13
            · by_cases h14_16 : V < 15
              · have he : V = 14 := by omega
                subst V
                exact row_6_14
              · have he : V = 15 := by omega
                subst V
                exact row_6_15
      · by_cases h16_33 : V < 24
        · by_cases h16_24 : V < 20
          · by_cases h16_20 : V < 18
            · by_cases h16_18 : V < 17
              · have he : V = 16 := by omega
                subst V
                exact row_6_16
              · have he : V = 17 := by omega
                subst V
                exact row_6_17
            · by_cases h18_20 : V < 19
              · have he : V = 18 := by omega
                subst V
                exact row_6_18
              · have he : V = 19 := by omega
                subst V
                exact row_6_19
          · by_cases h20_24 : V < 22
            · by_cases h20_22 : V < 21
              · have he : V = 20 := by omega
                subst V
                exact row_6_20
              · have he : V = 21 := by omega
                subst V
                exact row_6_21
            · by_cases h22_24 : V < 23
              · have he : V = 22 := by omega
                subst V
                exact row_6_22
              · have he : V = 23 := by omega
                subst V
                exact row_6_23
        · by_cases h24_33 : V < 28
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have he : V = 24 := by omega
                subst V
                exact row_6_24
              · have he : V = 25 := by omega
                subst V
                exact row_6_25
            · by_cases h26_28 : V < 27
              · have he : V = 26 := by omega
                subst V
                exact row_6_26
              · have he : V = 27 := by omega
                subst V
                exact row_6_27
          · by_cases h28_33 : V < 30
            · by_cases h28_30 : V < 29
              · have he : V = 28 := by omega
                subst V
                exact row_6_28
              · have he : V = 29 := by omega
                subst V
                exact row_6_29
            · by_cases h30_33 : V < 31
              · have he : V = 30 := by omega
                subst V
                exact row_6_30
              · by_cases h31_33 : V < 32
                · have he : V = 31 := by omega
                  subst V
                  exact row_6_31
                · have he : V = 32 := by omega
                  subst V
                  exact row_6_32
    · by_cases h33_67 : V < 50
      · by_cases h33_50 : V < 41
        · by_cases h33_41 : V < 37
          · by_cases h33_37 : V < 35
            · by_cases h33_35 : V < 34
              · have he : V = 33 := by omega
                subst V
                exact row_6_33
              · have he : V = 34 := by omega
                subst V
                exact row_6_34
            · by_cases h35_37 : V < 36
              · have he : V = 35 := by omega
                subst V
                exact row_6_35
              · have he : V = 36 := by omega
                subst V
                exact row_6_36
          · by_cases h37_41 : V < 39
            · by_cases h37_39 : V < 38
              · have he : V = 37 := by omega
                subst V
                exact row_6_37
              · have he : V = 38 := by omega
                subst V
                exact row_6_38
            · by_cases h39_41 : V < 40
              · have he : V = 39 := by omega
                subst V
                exact row_6_39
              · have he : V = 40 := by omega
                subst V
                exact row_6_40
        · by_cases h41_50 : V < 45
          · by_cases h41_45 : V < 43
            · by_cases h41_43 : V < 42
              · have he : V = 41 := by omega
                subst V
                exact row_6_41
              · have he : V = 42 := by omega
                subst V
                exact row_6_42
            · by_cases h43_45 : V < 44
              · have he : V = 43 := by omega
                subst V
                exact row_6_43
              · have he : V = 44 := by omega
                subst V
                exact row_6_44
          · by_cases h45_50 : V < 47
            · by_cases h45_47 : V < 46
              · have he : V = 45 := by omega
                subst V
                exact row_6_45
              · have he : V = 46 := by omega
                subst V
                exact row_6_46
            · by_cases h47_50 : V < 48
              · have he : V = 47 := by omega
                subst V
                exact row_6_47
              · by_cases h48_50 : V < 49
                · have he : V = 48 := by omega
                  subst V
                  exact row_6_48
                · have he : V = 49 := by omega
                  subst V
                  exact row_6_49
      · by_cases h50_67 : V < 58
        · by_cases h50_58 : V < 54
          · by_cases h50_54 : V < 52
            · by_cases h50_52 : V < 51
              · have he : V = 50 := by omega
                subst V
                exact row_6_50
              · have he : V = 51 := by omega
                subst V
                exact row_6_51
            · by_cases h52_54 : V < 53
              · have he : V = 52 := by omega
                subst V
                exact row_6_52
              · have he : V = 53 := by omega
                subst V
                exact row_6_53
          · by_cases h54_58 : V < 56
            · by_cases h54_56 : V < 55
              · have he : V = 54 := by omega
                subst V
                exact row_6_54
              · have he : V = 55 := by omega
                subst V
                exact row_6_55
            · by_cases h56_58 : V < 57
              · have he : V = 56 := by omega
                subst V
                exact row_6_56
              · have he : V = 57 := by omega
                subst V
                exact row_6_57
        · by_cases h58_67 : V < 62
          · by_cases h58_62 : V < 60
            · by_cases h58_60 : V < 59
              · have he : V = 58 := by omega
                subst V
                exact row_6_58
              · have he : V = 59 := by omega
                subst V
                exact row_6_59
            · by_cases h60_62 : V < 61
              · have he : V = 60 := by omega
                subst V
                exact row_6_60
              · have he : V = 61 := by omega
                subst V
                exact row_6_61
          · by_cases h62_67 : V < 64
            · by_cases h62_64 : V < 63
              · have he : V = 62 := by omega
                subst V
                exact row_6_62
              · have he : V = 63 := by omega
                subst V
                exact row_6_63
            · by_cases h64_67 : V < 65
              · have he : V = 64 := by omega
                subst V
                exact row_6_64
              · by_cases h65_67 : V < 66
                · have he : V = 65 := by omega
                  subst V
                  exact row_6_65
                · have he : V = 66 := by omega
                  subst V
                  exact row_6_66
  · by_cases h67_134 : V < 100
    · by_cases h67_100 : V < 83
      · by_cases h67_83 : V < 75
        · by_cases h67_75 : V < 71
          · by_cases h67_71 : V < 69
            · by_cases h67_69 : V < 68
              · have he : V = 67 := by omega
                subst V
                exact row_6_67
              · have he : V = 68 := by omega
                subst V
                exact row_6_68
            · by_cases h69_71 : V < 70
              · have he : V = 69 := by omega
                subst V
                exact row_6_69
              · have he : V = 70 := by omega
                subst V
                exact row_6_70
          · by_cases h71_75 : V < 73
            · by_cases h71_73 : V < 72
              · have he : V = 71 := by omega
                subst V
                exact row_6_71
              · have he : V = 72 := by omega
                subst V
                exact row_6_72
            · by_cases h73_75 : V < 74
              · have he : V = 73 := by omega
                subst V
                exact row_6_73
              · have he : V = 74 := by omega
                subst V
                exact row_6_74
        · by_cases h75_83 : V < 79
          · by_cases h75_79 : V < 77
            · by_cases h75_77 : V < 76
              · have he : V = 75 := by omega
                subst V
                exact row_6_75
              · have he : V = 76 := by omega
                subst V
                exact row_6_76
            · by_cases h77_79 : V < 78
              · have he : V = 77 := by omega
                subst V
                exact row_6_77
              · have he : V = 78 := by omega
                subst V
                exact row_6_78
          · by_cases h79_83 : V < 81
            · by_cases h79_81 : V < 80
              · have he : V = 79 := by omega
                subst V
                exact row_6_79
              · have he : V = 80 := by omega
                subst V
                exact row_6_80
            · by_cases h81_83 : V < 82
              · have he : V = 81 := by omega
                subst V
                exact row_6_81
              · have he : V = 82 := by omega
                subst V
                exact row_6_82
      · by_cases h83_100 : V < 91
        · by_cases h83_91 : V < 87
          · by_cases h83_87 : V < 85
            · by_cases h83_85 : V < 84
              · have he : V = 83 := by omega
                subst V
                exact row_6_83
              · have he : V = 84 := by omega
                subst V
                exact row_6_84
            · by_cases h85_87 : V < 86
              · have he : V = 85 := by omega
                subst V
                exact row_6_85
              · have he : V = 86 := by omega
                subst V
                exact row_6_86
          · by_cases h87_91 : V < 89
            · by_cases h87_89 : V < 88
              · have he : V = 87 := by omega
                subst V
                exact row_6_87
              · have he : V = 88 := by omega
                subst V
                exact row_6_88
            · by_cases h89_91 : V < 90
              · have he : V = 89 := by omega
                subst V
                exact row_6_89
              · have he : V = 90 := by omega
                subst V
                exact row_6_90
        · by_cases h91_100 : V < 95
          · by_cases h91_95 : V < 93
            · by_cases h91_93 : V < 92
              · have he : V = 91 := by omega
                subst V
                exact row_6_91
              · have he : V = 92 := by omega
                subst V
                exact row_6_92
            · by_cases h93_95 : V < 94
              · have he : V = 93 := by omega
                subst V
                exact row_6_93
              · have he : V = 94 := by omega
                subst V
                exact row_6_94
          · by_cases h95_100 : V < 97
            · by_cases h95_97 : V < 96
              · have he : V = 95 := by omega
                subst V
                exact row_6_95
              · have he : V = 96 := by omega
                subst V
                exact row_6_96
            · by_cases h97_100 : V < 98
              · have he : V = 97 := by omega
                subst V
                exact row_6_97
              · by_cases h98_100 : V < 99
                · have he : V = 98 := by omega
                  subst V
                  exact row_6_98
                · have he : V = 99 := by omega
                  subst V
                  exact row_6_99
    · by_cases h100_134 : V < 117
      · by_cases h100_117 : V < 108
        · by_cases h100_108 : V < 104
          · by_cases h100_104 : V < 102
            · by_cases h100_102 : V < 101
              · have he : V = 100 := by omega
                subst V
                exact row_6_100
              · have he : V = 101 := by omega
                subst V
                exact row_6_101
            · by_cases h102_104 : V < 103
              · have he : V = 102 := by omega
                subst V
                exact row_6_102
              · have he : V = 103 := by omega
                subst V
                exact row_6_103
          · by_cases h104_108 : V < 106
            · by_cases h104_106 : V < 105
              · have he : V = 104 := by omega
                subst V
                exact row_6_104
              · have he : V = 105 := by omega
                subst V
                exact row_6_105
            · by_cases h106_108 : V < 107
              · have he : V = 106 := by omega
                subst V
                exact row_6_106
              · have he : V = 107 := by omega
                subst V
                exact row_6_107
        · by_cases h108_117 : V < 112
          · by_cases h108_112 : V < 110
            · by_cases h108_110 : V < 109
              · have he : V = 108 := by omega
                subst V
                exact row_6_108
              · have he : V = 109 := by omega
                subst V
                exact row_6_109
            · by_cases h110_112 : V < 111
              · have he : V = 110 := by omega
                subst V
                exact row_6_110
              · have he : V = 111 := by omega
                subst V
                exact row_6_111
          · by_cases h112_117 : V < 114
            · by_cases h112_114 : V < 113
              · have he : V = 112 := by omega
                subst V
                exact row_6_112
              · have he : V = 113 := by omega
                subst V
                exact row_6_113
            · by_cases h114_117 : V < 115
              · have he : V = 114 := by omega
                subst V
                exact row_6_114
              · by_cases h115_117 : V < 116
                · have he : V = 115 := by omega
                  subst V
                  exact row_6_115
                · have he : V = 116 := by omega
                  subst V
                  exact row_6_116
      · by_cases h117_134 : V < 125
        · by_cases h117_125 : V < 121
          · by_cases h117_121 : V < 119
            · by_cases h117_119 : V < 118
              · have he : V = 117 := by omega
                subst V
                exact row_6_117
              · have he : V = 118 := by omega
                subst V
                exact row_6_118
            · by_cases h119_121 : V < 120
              · have he : V = 119 := by omega
                subst V
                exact row_6_119
              · have he : V = 120 := by omega
                subst V
                exact row_6_120
          · by_cases h121_125 : V < 123
            · by_cases h121_123 : V < 122
              · have he : V = 121 := by omega
                subst V
                exact row_6_121
              · have he : V = 122 := by omega
                subst V
                exact row_6_122
            · by_cases h123_125 : V < 124
              · have he : V = 123 := by omega
                subst V
                exact row_6_123
              · have he : V = 124 := by omega
                subst V
                exact row_6_124
        · by_cases h125_134 : V < 129
          · by_cases h125_129 : V < 127
            · by_cases h125_127 : V < 126
              · have he : V = 125 := by omega
                subst V
                exact row_6_125
              · have he : V = 126 := by omega
                subst V
                exact row_6_126
            · by_cases h127_129 : V < 128
              · have he : V = 127 := by omega
                subst V
                exact row_6_127
              · have he : V = 128 := by omega
                subst V
                exact row_6_128
          · by_cases h129_134 : V < 131
            · by_cases h129_131 : V < 130
              · have he : V = 129 := by omega
                subst V
                exact row_6_129
              · have he : V = 130 := by omega
                subst V
                exact row_6_130
            · by_cases h131_134 : V < 132
              · have he : V = 131 := by omega
                subst V
                exact row_6_131
              · by_cases h132_134 : V < 133
                · have he : V = 132 := by omega
                  subst V
                  exact row_6_132
                · have he : V = 133 := by omega
                  subst V
                  exact row_6_133
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
