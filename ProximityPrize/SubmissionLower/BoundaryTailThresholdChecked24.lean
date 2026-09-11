import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked23

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_24_0_0 : C 24 0 0 := by decide +kernel
theorem cell_24_0_1 : C 24 0 1 := by decide +kernel
theorem cell_24_0_2 : C 24 0 2 := by decide +kernel
theorem cell_24_0_3 : C 24 0 3 := by decide +kernel
theorem cell_24_0_4 : C 24 0 4 := by decide +kernel
theorem cell_24_0_5 : C 24 0 5 := by decide +kernel
theorem row_24_0 : ThresholdAt 24 0 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 0 0 cell_24_0_0
  | exact S 24 0 1 cell_24_0_1
  | exact S 24 0 2 cell_24_0_2
  | exact S 24 0 3 cell_24_0_3
  | exact S 24 0 4 cell_24_0_4
  | exact S 24 0 5 cell_24_0_5
theorem cell_24_1_0 : C 24 1 0 := by decide +kernel
theorem cell_24_1_1 : C 24 1 1 := by decide +kernel
theorem cell_24_1_2 : C 24 1 2 := by decide +kernel
theorem cell_24_1_3 : C 24 1 3 := by decide +kernel
theorem cell_24_1_4 : C 24 1 4 := by decide +kernel
theorem cell_24_1_5 : C 24 1 5 := by decide +kernel
theorem row_24_1 : ThresholdAt 24 1 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 1 0 cell_24_1_0
  | exact S 24 1 1 cell_24_1_1
  | exact S 24 1 2 cell_24_1_2
  | exact S 24 1 3 cell_24_1_3
  | exact S 24 1 4 cell_24_1_4
  | exact S 24 1 5 cell_24_1_5
theorem cell_24_2_0 : C 24 2 0 := by decide +kernel
theorem cell_24_2_1 : C 24 2 1 := by decide +kernel
theorem cell_24_2_2 : C 24 2 2 := by decide +kernel
theorem cell_24_2_3 : C 24 2 3 := by decide +kernel
theorem cell_24_2_4 : C 24 2 4 := by decide +kernel
theorem cell_24_2_5 : C 24 2 5 := by decide +kernel
theorem row_24_2 : ThresholdAt 24 2 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 2 0 cell_24_2_0
  | exact S 24 2 1 cell_24_2_1
  | exact S 24 2 2 cell_24_2_2
  | exact S 24 2 3 cell_24_2_3
  | exact S 24 2 4 cell_24_2_4
  | exact S 24 2 5 cell_24_2_5
theorem cell_24_3_0 : C 24 3 0 := by decide +kernel
theorem cell_24_3_1 : C 24 3 1 := by decide +kernel
theorem cell_24_3_2 : C 24 3 2 := by decide +kernel
theorem cell_24_3_3 : C 24 3 3 := by decide +kernel
theorem cell_24_3_4 : C 24 3 4 := by decide +kernel
theorem cell_24_3_5 : C 24 3 5 := by decide +kernel
theorem row_24_3 : ThresholdAt 24 3 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 3 0 cell_24_3_0
  | exact S 24 3 1 cell_24_3_1
  | exact S 24 3 2 cell_24_3_2
  | exact S 24 3 3 cell_24_3_3
  | exact S 24 3 4 cell_24_3_4
  | exact S 24 3 5 cell_24_3_5
theorem cell_24_4_0 : C 24 4 0 := by decide +kernel
theorem cell_24_4_1 : C 24 4 1 := by decide +kernel
theorem cell_24_4_2 : C 24 4 2 := by decide +kernel
theorem cell_24_4_3 : C 24 4 3 := by decide +kernel
theorem cell_24_4_4 : C 24 4 4 := by decide +kernel
theorem cell_24_4_5 : C 24 4 5 := by decide +kernel
theorem row_24_4 : ThresholdAt 24 4 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 4 0 cell_24_4_0
  | exact S 24 4 1 cell_24_4_1
  | exact S 24 4 2 cell_24_4_2
  | exact S 24 4 3 cell_24_4_3
  | exact S 24 4 4 cell_24_4_4
  | exact S 24 4 5 cell_24_4_5
theorem cell_24_5_0 : C 24 5 0 := by decide +kernel
theorem cell_24_5_1 : C 24 5 1 := by decide +kernel
theorem cell_24_5_2 : C 24 5 2 := by decide +kernel
theorem cell_24_5_3 : C 24 5 3 := by decide +kernel
theorem cell_24_5_4 : C 24 5 4 := by decide +kernel
theorem cell_24_5_5 : C 24 5 5 := by decide +kernel
theorem row_24_5 : ThresholdAt 24 5 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 5 0 cell_24_5_0
  | exact S 24 5 1 cell_24_5_1
  | exact S 24 5 2 cell_24_5_2
  | exact S 24 5 3 cell_24_5_3
  | exact S 24 5 4 cell_24_5_4
  | exact S 24 5 5 cell_24_5_5
theorem cell_24_6_0 : C 24 6 0 := by decide +kernel
theorem cell_24_6_1 : C 24 6 1 := by decide +kernel
theorem cell_24_6_2 : C 24 6 2 := by decide +kernel
theorem cell_24_6_3 : C 24 6 3 := by decide +kernel
theorem cell_24_6_4 : C 24 6 4 := by decide +kernel
theorem cell_24_6_5 : C 24 6 5 := by decide +kernel
theorem row_24_6 : ThresholdAt 24 6 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 6 0 cell_24_6_0
  | exact S 24 6 1 cell_24_6_1
  | exact S 24 6 2 cell_24_6_2
  | exact S 24 6 3 cell_24_6_3
  | exact S 24 6 4 cell_24_6_4
  | exact S 24 6 5 cell_24_6_5
theorem cell_24_7_0 : C 24 7 0 := by decide +kernel
theorem cell_24_7_1 : C 24 7 1 := by decide +kernel
theorem cell_24_7_2 : C 24 7 2 := by decide +kernel
theorem cell_24_7_3 : C 24 7 3 := by decide +kernel
theorem cell_24_7_4 : C 24 7 4 := by decide +kernel
theorem cell_24_7_5 : C 24 7 5 := by decide +kernel
theorem row_24_7 : ThresholdAt 24 7 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 7 0 cell_24_7_0
  | exact S 24 7 1 cell_24_7_1
  | exact S 24 7 2 cell_24_7_2
  | exact S 24 7 3 cell_24_7_3
  | exact S 24 7 4 cell_24_7_4
  | exact S 24 7 5 cell_24_7_5
theorem cell_24_8_0 : C 24 8 0 := by decide +kernel
theorem cell_24_8_1 : C 24 8 1 := by decide +kernel
theorem cell_24_8_2 : C 24 8 2 := by decide +kernel
theorem cell_24_8_3 : C 24 8 3 := by decide +kernel
theorem cell_24_8_4 : C 24 8 4 := by decide +kernel
theorem cell_24_8_5 : C 24 8 5 := by decide +kernel
theorem row_24_8 : ThresholdAt 24 8 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 8 0 cell_24_8_0
  | exact S 24 8 1 cell_24_8_1
  | exact S 24 8 2 cell_24_8_2
  | exact S 24 8 3 cell_24_8_3
  | exact S 24 8 4 cell_24_8_4
  | exact S 24 8 5 cell_24_8_5
theorem cell_24_9_0 : C 24 9 0 := by decide +kernel
theorem cell_24_9_1 : C 24 9 1 := by decide +kernel
theorem cell_24_9_2 : C 24 9 2 := by decide +kernel
theorem cell_24_9_3 : C 24 9 3 := by decide +kernel
theorem cell_24_9_4 : C 24 9 4 := by decide +kernel
theorem cell_24_9_5 : C 24 9 5 := by decide +kernel
theorem row_24_9 : ThresholdAt 24 9 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 9 0 cell_24_9_0
  | exact S 24 9 1 cell_24_9_1
  | exact S 24 9 2 cell_24_9_2
  | exact S 24 9 3 cell_24_9_3
  | exact S 24 9 4 cell_24_9_4
  | exact S 24 9 5 cell_24_9_5
theorem cell_24_10_0 : C 24 10 0 := by decide +kernel
theorem cell_24_10_1 : C 24 10 1 := by decide +kernel
theorem cell_24_10_2 : C 24 10 2 := by decide +kernel
theorem cell_24_10_3 : C 24 10 3 := by decide +kernel
theorem cell_24_10_4 : C 24 10 4 := by decide +kernel
theorem cell_24_10_5 : C 24 10 5 := by decide +kernel
theorem row_24_10 : ThresholdAt 24 10 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 10 0 cell_24_10_0
  | exact S 24 10 1 cell_24_10_1
  | exact S 24 10 2 cell_24_10_2
  | exact S 24 10 3 cell_24_10_3
  | exact S 24 10 4 cell_24_10_4
  | exact S 24 10 5 cell_24_10_5
theorem cell_24_11_0 : C 24 11 0 := by decide +kernel
theorem cell_24_11_1 : C 24 11 1 := by decide +kernel
theorem cell_24_11_2 : C 24 11 2 := by decide +kernel
theorem cell_24_11_3 : C 24 11 3 := by decide +kernel
theorem cell_24_11_4 : C 24 11 4 := by decide +kernel
theorem cell_24_11_5 : C 24 11 5 := by decide +kernel
theorem row_24_11 : ThresholdAt 24 11 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 11 0 cell_24_11_0
  | exact S 24 11 1 cell_24_11_1
  | exact S 24 11 2 cell_24_11_2
  | exact S 24 11 3 cell_24_11_3
  | exact S 24 11 4 cell_24_11_4
  | exact S 24 11 5 cell_24_11_5
theorem cell_24_12_0 : C 24 12 0 := by decide +kernel
theorem cell_24_12_1 : C 24 12 1 := by decide +kernel
theorem cell_24_12_2 : C 24 12 2 := by decide +kernel
theorem cell_24_12_3 : C 24 12 3 := by decide +kernel
theorem cell_24_12_4 : C 24 12 4 := by decide +kernel
theorem cell_24_12_5 : C 24 12 5 := by decide +kernel
theorem row_24_12 : ThresholdAt 24 12 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 12 0 cell_24_12_0
  | exact S 24 12 1 cell_24_12_1
  | exact S 24 12 2 cell_24_12_2
  | exact S 24 12 3 cell_24_12_3
  | exact S 24 12 4 cell_24_12_4
  | exact S 24 12 5 cell_24_12_5
theorem cell_24_13_0 : C 24 13 0 := by decide +kernel
theorem cell_24_13_1 : C 24 13 1 := by decide +kernel
theorem cell_24_13_2 : C 24 13 2 := by decide +kernel
theorem cell_24_13_3 : C 24 13 3 := by decide +kernel
theorem cell_24_13_4 : C 24 13 4 := by decide +kernel
theorem cell_24_13_5 : C 24 13 5 := by decide +kernel
theorem row_24_13 : ThresholdAt 24 13 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 13 0 cell_24_13_0
  | exact S 24 13 1 cell_24_13_1
  | exact S 24 13 2 cell_24_13_2
  | exact S 24 13 3 cell_24_13_3
  | exact S 24 13 4 cell_24_13_4
  | exact S 24 13 5 cell_24_13_5
theorem cell_24_14_0 : C 24 14 0 := by decide +kernel
theorem cell_24_14_1 : C 24 14 1 := by decide +kernel
theorem cell_24_14_2 : C 24 14 2 := by decide +kernel
theorem cell_24_14_3 : C 24 14 3 := by decide +kernel
theorem cell_24_14_4 : C 24 14 4 := by decide +kernel
theorem cell_24_14_5 : C 24 14 5 := by decide +kernel
theorem row_24_14 : ThresholdAt 24 14 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 14 0 cell_24_14_0
  | exact S 24 14 1 cell_24_14_1
  | exact S 24 14 2 cell_24_14_2
  | exact S 24 14 3 cell_24_14_3
  | exact S 24 14 4 cell_24_14_4
  | exact S 24 14 5 cell_24_14_5
theorem cell_24_15_0 : C 24 15 0 := by decide +kernel
theorem cell_24_15_1 : C 24 15 1 := by decide +kernel
theorem cell_24_15_2 : C 24 15 2 := by decide +kernel
theorem cell_24_15_3 : C 24 15 3 := by decide +kernel
theorem cell_24_15_4 : C 24 15 4 := by decide +kernel
theorem cell_24_15_5 : C 24 15 5 := by decide +kernel
theorem row_24_15 : ThresholdAt 24 15 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 15 0 cell_24_15_0
  | exact S 24 15 1 cell_24_15_1
  | exact S 24 15 2 cell_24_15_2
  | exact S 24 15 3 cell_24_15_3
  | exact S 24 15 4 cell_24_15_4
  | exact S 24 15 5 cell_24_15_5
theorem cell_24_16_0 : C 24 16 0 := by decide +kernel
theorem cell_24_16_1 : C 24 16 1 := by decide +kernel
theorem cell_24_16_2 : C 24 16 2 := by decide +kernel
theorem cell_24_16_3 : C 24 16 3 := by decide +kernel
theorem cell_24_16_4 : C 24 16 4 := by decide +kernel
theorem cell_24_16_5 : C 24 16 5 := by decide +kernel
theorem row_24_16 : ThresholdAt 24 16 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 16 0 cell_24_16_0
  | exact S 24 16 1 cell_24_16_1
  | exact S 24 16 2 cell_24_16_2
  | exact S 24 16 3 cell_24_16_3
  | exact S 24 16 4 cell_24_16_4
  | exact S 24 16 5 cell_24_16_5
theorem cell_24_17_0 : C 24 17 0 := by decide +kernel
theorem cell_24_17_1 : C 24 17 1 := by decide +kernel
theorem cell_24_17_2 : C 24 17 2 := by decide +kernel
theorem cell_24_17_3 : C 24 17 3 := by decide +kernel
theorem cell_24_17_4 : C 24 17 4 := by decide +kernel
theorem cell_24_17_5 : C 24 17 5 := by decide +kernel
theorem row_24_17 : ThresholdAt 24 17 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 17 0 cell_24_17_0
  | exact S 24 17 1 cell_24_17_1
  | exact S 24 17 2 cell_24_17_2
  | exact S 24 17 3 cell_24_17_3
  | exact S 24 17 4 cell_24_17_4
  | exact S 24 17 5 cell_24_17_5
theorem cell_24_18_0 : C 24 18 0 := by decide +kernel
theorem cell_24_18_1 : C 24 18 1 := by decide +kernel
theorem cell_24_18_2 : C 24 18 2 := by decide +kernel
theorem cell_24_18_3 : C 24 18 3 := by decide +kernel
theorem cell_24_18_4 : C 24 18 4 := by decide +kernel
theorem cell_24_18_5 : C 24 18 5 := by decide +kernel
theorem row_24_18 : ThresholdAt 24 18 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 18 0 cell_24_18_0
  | exact S 24 18 1 cell_24_18_1
  | exact S 24 18 2 cell_24_18_2
  | exact S 24 18 3 cell_24_18_3
  | exact S 24 18 4 cell_24_18_4
  | exact S 24 18 5 cell_24_18_5
theorem cell_24_19_0 : C 24 19 0 := by decide +kernel
theorem cell_24_19_1 : C 24 19 1 := by decide +kernel
theorem cell_24_19_2 : C 24 19 2 := by decide +kernel
theorem cell_24_19_3 : C 24 19 3 := by decide +kernel
theorem cell_24_19_4 : C 24 19 4 := by decide +kernel
theorem cell_24_19_5 : C 24 19 5 := by decide +kernel
theorem row_24_19 : ThresholdAt 24 19 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 19 0 cell_24_19_0
  | exact S 24 19 1 cell_24_19_1
  | exact S 24 19 2 cell_24_19_2
  | exact S 24 19 3 cell_24_19_3
  | exact S 24 19 4 cell_24_19_4
  | exact S 24 19 5 cell_24_19_5
theorem cell_24_20_0 : C 24 20 0 := by decide +kernel
theorem cell_24_20_1 : C 24 20 1 := by decide +kernel
theorem cell_24_20_2 : C 24 20 2 := by decide +kernel
theorem cell_24_20_3 : C 24 20 3 := by decide +kernel
theorem cell_24_20_4 : C 24 20 4 := by decide +kernel
theorem cell_24_20_5 : C 24 20 5 := by decide +kernel
theorem row_24_20 : ThresholdAt 24 20 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 20 0 cell_24_20_0
  | exact S 24 20 1 cell_24_20_1
  | exact S 24 20 2 cell_24_20_2
  | exact S 24 20 3 cell_24_20_3
  | exact S 24 20 4 cell_24_20_4
  | exact S 24 20 5 cell_24_20_5
theorem cell_24_21_0 : C 24 21 0 := by decide +kernel
theorem cell_24_21_1 : C 24 21 1 := by decide +kernel
theorem cell_24_21_2 : C 24 21 2 := by decide +kernel
theorem cell_24_21_3 : C 24 21 3 := by decide +kernel
theorem cell_24_21_4 : C 24 21 4 := by decide +kernel
theorem cell_24_21_5 : C 24 21 5 := by decide +kernel
theorem row_24_21 : ThresholdAt 24 21 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 21 0 cell_24_21_0
  | exact S 24 21 1 cell_24_21_1
  | exact S 24 21 2 cell_24_21_2
  | exact S 24 21 3 cell_24_21_3
  | exact S 24 21 4 cell_24_21_4
  | exact S 24 21 5 cell_24_21_5
theorem cell_24_22_0 : C 24 22 0 := by decide +kernel
theorem cell_24_22_1 : C 24 22 1 := by decide +kernel
theorem cell_24_22_2 : C 24 22 2 := by decide +kernel
theorem cell_24_22_3 : C 24 22 3 := by decide +kernel
theorem cell_24_22_4 : C 24 22 4 := by decide +kernel
theorem cell_24_22_5 : C 24 22 5 := by decide +kernel
theorem row_24_22 : ThresholdAt 24 22 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 22 0 cell_24_22_0
  | exact S 24 22 1 cell_24_22_1
  | exact S 24 22 2 cell_24_22_2
  | exact S 24 22 3 cell_24_22_3
  | exact S 24 22 4 cell_24_22_4
  | exact S 24 22 5 cell_24_22_5
theorem cell_24_23_0 : C 24 23 0 := by decide +kernel
theorem cell_24_23_1 : C 24 23 1 := by decide +kernel
theorem cell_24_23_2 : C 24 23 2 := by decide +kernel
theorem cell_24_23_3 : C 24 23 3 := by decide +kernel
theorem cell_24_23_4 : C 24 23 4 := by decide +kernel
theorem cell_24_23_5 : C 24 23 5 := by decide +kernel
theorem row_24_23 : ThresholdAt 24 23 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 23 0 cell_24_23_0
  | exact S 24 23 1 cell_24_23_1
  | exact S 24 23 2 cell_24_23_2
  | exact S 24 23 3 cell_24_23_3
  | exact S 24 23 4 cell_24_23_4
  | exact S 24 23 5 cell_24_23_5
theorem cell_24_24_0 : C 24 24 0 := by decide +kernel
theorem cell_24_24_1 : C 24 24 1 := by decide +kernel
theorem cell_24_24_2 : C 24 24 2 := by decide +kernel
theorem cell_24_24_3 : C 24 24 3 := by decide +kernel
theorem cell_24_24_4 : C 24 24 4 := by decide +kernel
theorem cell_24_24_5 : C 24 24 5 := by decide +kernel
theorem row_24_24 : ThresholdAt 24 24 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 24 0 cell_24_24_0
  | exact S 24 24 1 cell_24_24_1
  | exact S 24 24 2 cell_24_24_2
  | exact S 24 24 3 cell_24_24_3
  | exact S 24 24 4 cell_24_24_4
  | exact S 24 24 5 cell_24_24_5
theorem cell_24_25_0 : C 24 25 0 := by decide +kernel
theorem cell_24_25_1 : C 24 25 1 := by decide +kernel
theorem cell_24_25_2 : C 24 25 2 := by decide +kernel
theorem cell_24_25_3 : C 24 25 3 := by decide +kernel
theorem cell_24_25_4 : C 24 25 4 := by decide +kernel
theorem cell_24_25_5 : C 24 25 5 := by decide +kernel
theorem row_24_25 : ThresholdAt 24 25 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 25 0 cell_24_25_0
  | exact S 24 25 1 cell_24_25_1
  | exact S 24 25 2 cell_24_25_2
  | exact S 24 25 3 cell_24_25_3
  | exact S 24 25 4 cell_24_25_4
  | exact S 24 25 5 cell_24_25_5
theorem cell_24_26_0 : C 24 26 0 := by decide +kernel
theorem cell_24_26_1 : C 24 26 1 := by decide +kernel
theorem cell_24_26_2 : C 24 26 2 := by decide +kernel
theorem cell_24_26_3 : C 24 26 3 := by decide +kernel
theorem cell_24_26_4 : C 24 26 4 := by decide +kernel
theorem cell_24_26_5 : C 24 26 5 := by decide +kernel
theorem row_24_26 : ThresholdAt 24 26 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 26 0 cell_24_26_0
  | exact S 24 26 1 cell_24_26_1
  | exact S 24 26 2 cell_24_26_2
  | exact S 24 26 3 cell_24_26_3
  | exact S 24 26 4 cell_24_26_4
  | exact S 24 26 5 cell_24_26_5
theorem cell_24_27_0 : C 24 27 0 := by decide +kernel
theorem cell_24_27_1 : C 24 27 1 := by decide +kernel
theorem cell_24_27_2 : C 24 27 2 := by decide +kernel
theorem cell_24_27_3 : C 24 27 3 := by decide +kernel
theorem cell_24_27_4 : C 24 27 4 := by decide +kernel
theorem cell_24_27_5 : C 24 27 5 := by decide +kernel
theorem row_24_27 : ThresholdAt 24 27 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 27 0 cell_24_27_0
  | exact S 24 27 1 cell_24_27_1
  | exact S 24 27 2 cell_24_27_2
  | exact S 24 27 3 cell_24_27_3
  | exact S 24 27 4 cell_24_27_4
  | exact S 24 27 5 cell_24_27_5
theorem cell_24_28_0 : C 24 28 0 := by decide +kernel
theorem cell_24_28_1 : C 24 28 1 := by decide +kernel
theorem cell_24_28_2 : C 24 28 2 := by decide +kernel
theorem cell_24_28_3 : C 24 28 3 := by decide +kernel
theorem cell_24_28_4 : C 24 28 4 := by decide +kernel
theorem cell_24_28_5 : C 24 28 5 := by decide +kernel
theorem row_24_28 : ThresholdAt 24 28 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 28 0 cell_24_28_0
  | exact S 24 28 1 cell_24_28_1
  | exact S 24 28 2 cell_24_28_2
  | exact S 24 28 3 cell_24_28_3
  | exact S 24 28 4 cell_24_28_4
  | exact S 24 28 5 cell_24_28_5
theorem cell_24_29_0 : C 24 29 0 := by decide +kernel
theorem cell_24_29_1 : C 24 29 1 := by decide +kernel
theorem cell_24_29_2 : C 24 29 2 := by decide +kernel
theorem cell_24_29_3 : C 24 29 3 := by decide +kernel
theorem cell_24_29_4 : C 24 29 4 := by decide +kernel
theorem cell_24_29_5 : C 24 29 5 := by decide +kernel
theorem row_24_29 : ThresholdAt 24 29 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 29 0 cell_24_29_0
  | exact S 24 29 1 cell_24_29_1
  | exact S 24 29 2 cell_24_29_2
  | exact S 24 29 3 cell_24_29_3
  | exact S 24 29 4 cell_24_29_4
  | exact S 24 29 5 cell_24_29_5
theorem cell_24_30_0 : C 24 30 0 := by decide +kernel
theorem cell_24_30_1 : C 24 30 1 := by decide +kernel
theorem cell_24_30_2 : C 24 30 2 := by decide +kernel
theorem cell_24_30_3 : C 24 30 3 := by decide +kernel
theorem cell_24_30_4 : C 24 30 4 := by decide +kernel
theorem cell_24_30_5 : C 24 30 5 := by decide +kernel
theorem row_24_30 : ThresholdAt 24 30 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 30 0 cell_24_30_0
  | exact S 24 30 1 cell_24_30_1
  | exact S 24 30 2 cell_24_30_2
  | exact S 24 30 3 cell_24_30_3
  | exact S 24 30 4 cell_24_30_4
  | exact S 24 30 5 cell_24_30_5
theorem cell_24_31_0 : C 24 31 0 := by decide +kernel
theorem cell_24_31_1 : C 24 31 1 := by decide +kernel
theorem cell_24_31_2 : C 24 31 2 := by decide +kernel
theorem cell_24_31_3 : C 24 31 3 := by decide +kernel
theorem cell_24_31_4 : C 24 31 4 := by decide +kernel
theorem cell_24_31_5 : C 24 31 5 := by decide +kernel
theorem row_24_31 : ThresholdAt 24 31 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 31 0 cell_24_31_0
  | exact S 24 31 1 cell_24_31_1
  | exact S 24 31 2 cell_24_31_2
  | exact S 24 31 3 cell_24_31_3
  | exact S 24 31 4 cell_24_31_4
  | exact S 24 31 5 cell_24_31_5
theorem cell_24_32_0 : C 24 32 0 := by decide +kernel
theorem cell_24_32_1 : C 24 32 1 := by decide +kernel
theorem cell_24_32_2 : C 24 32 2 := by decide +kernel
theorem cell_24_32_3 : C 24 32 3 := by decide +kernel
theorem cell_24_32_4 : C 24 32 4 := by decide +kernel
theorem cell_24_32_5 : C 24 32 5 := by decide +kernel
theorem row_24_32 : ThresholdAt 24 32 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 32 0 cell_24_32_0
  | exact S 24 32 1 cell_24_32_1
  | exact S 24 32 2 cell_24_32_2
  | exact S 24 32 3 cell_24_32_3
  | exact S 24 32 4 cell_24_32_4
  | exact S 24 32 5 cell_24_32_5
theorem cell_24_33_0 : C 24 33 0 := by decide +kernel
theorem cell_24_33_1 : C 24 33 1 := by decide +kernel
theorem cell_24_33_2 : C 24 33 2 := by decide +kernel
theorem cell_24_33_3 : C 24 33 3 := by decide +kernel
theorem cell_24_33_4 : C 24 33 4 := by decide +kernel
theorem cell_24_33_5 : C 24 33 5 := by decide +kernel
theorem row_24_33 : ThresholdAt 24 33 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 33 0 cell_24_33_0
  | exact S 24 33 1 cell_24_33_1
  | exact S 24 33 2 cell_24_33_2
  | exact S 24 33 3 cell_24_33_3
  | exact S 24 33 4 cell_24_33_4
  | exact S 24 33 5 cell_24_33_5
theorem cell_24_34_0 : C 24 34 0 := by decide +kernel
theorem cell_24_34_1 : C 24 34 1 := by decide +kernel
theorem cell_24_34_2 : C 24 34 2 := by decide +kernel
theorem cell_24_34_3 : C 24 34 3 := by decide +kernel
theorem cell_24_34_4 : C 24 34 4 := by decide +kernel
theorem cell_24_34_5 : C 24 34 5 := by decide +kernel
theorem row_24_34 : ThresholdAt 24 34 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 34 0 cell_24_34_0
  | exact S 24 34 1 cell_24_34_1
  | exact S 24 34 2 cell_24_34_2
  | exact S 24 34 3 cell_24_34_3
  | exact S 24 34 4 cell_24_34_4
  | exact S 24 34 5 cell_24_34_5
theorem cell_24_35_0 : C 24 35 0 := by decide +kernel
theorem cell_24_35_1 : C 24 35 1 := by decide +kernel
theorem cell_24_35_2 : C 24 35 2 := by decide +kernel
theorem cell_24_35_3 : C 24 35 3 := by decide +kernel
theorem cell_24_35_4 : C 24 35 4 := by decide +kernel
theorem cell_24_35_5 : C 24 35 5 := by decide +kernel
theorem row_24_35 : ThresholdAt 24 35 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 35 0 cell_24_35_0
  | exact S 24 35 1 cell_24_35_1
  | exact S 24 35 2 cell_24_35_2
  | exact S 24 35 3 cell_24_35_3
  | exact S 24 35 4 cell_24_35_4
  | exact S 24 35 5 cell_24_35_5
theorem cell_24_36_0 : C 24 36 0 := by decide +kernel
theorem cell_24_36_1 : C 24 36 1 := by decide +kernel
theorem cell_24_36_2 : C 24 36 2 := by decide +kernel
theorem cell_24_36_3 : C 24 36 3 := by decide +kernel
theorem cell_24_36_4 : C 24 36 4 := by decide +kernel
theorem cell_24_36_5 : C 24 36 5 := by decide +kernel
theorem row_24_36 : ThresholdAt 24 36 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 36 0 cell_24_36_0
  | exact S 24 36 1 cell_24_36_1
  | exact S 24 36 2 cell_24_36_2
  | exact S 24 36 3 cell_24_36_3
  | exact S 24 36 4 cell_24_36_4
  | exact S 24 36 5 cell_24_36_5
theorem cell_24_37_0 : C 24 37 0 := by decide +kernel
theorem cell_24_37_1 : C 24 37 1 := by decide +kernel
theorem cell_24_37_2 : C 24 37 2 := by decide +kernel
theorem cell_24_37_3 : C 24 37 3 := by decide +kernel
theorem cell_24_37_4 : C 24 37 4 := by decide +kernel
theorem cell_24_37_5 : C 24 37 5 := by decide +kernel
theorem row_24_37 : ThresholdAt 24 37 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 37 0 cell_24_37_0
  | exact S 24 37 1 cell_24_37_1
  | exact S 24 37 2 cell_24_37_2
  | exact S 24 37 3 cell_24_37_3
  | exact S 24 37 4 cell_24_37_4
  | exact S 24 37 5 cell_24_37_5
theorem cell_24_38_0 : C 24 38 0 := by decide +kernel
theorem cell_24_38_1 : C 24 38 1 := by decide +kernel
theorem cell_24_38_2 : C 24 38 2 := by decide +kernel
theorem cell_24_38_3 : C 24 38 3 := by decide +kernel
theorem cell_24_38_4 : C 24 38 4 := by decide +kernel
theorem cell_24_38_5 : C 24 38 5 := by decide +kernel
theorem row_24_38 : ThresholdAt 24 38 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 38 0 cell_24_38_0
  | exact S 24 38 1 cell_24_38_1
  | exact S 24 38 2 cell_24_38_2
  | exact S 24 38 3 cell_24_38_3
  | exact S 24 38 4 cell_24_38_4
  | exact S 24 38 5 cell_24_38_5
theorem cell_24_39_0 : C 24 39 0 := by decide +kernel
theorem cell_24_39_1 : C 24 39 1 := by decide +kernel
theorem cell_24_39_2 : C 24 39 2 := by decide +kernel
theorem cell_24_39_3 : C 24 39 3 := by decide +kernel
theorem cell_24_39_4 : C 24 39 4 := by decide +kernel
theorem cell_24_39_5 : C 24 39 5 := by decide +kernel
theorem row_24_39 : ThresholdAt 24 39 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 39 0 cell_24_39_0
  | exact S 24 39 1 cell_24_39_1
  | exact S 24 39 2 cell_24_39_2
  | exact S 24 39 3 cell_24_39_3
  | exact S 24 39 4 cell_24_39_4
  | exact S 24 39 5 cell_24_39_5
theorem cell_24_40_0 : C 24 40 0 := by decide +kernel
theorem cell_24_40_1 : C 24 40 1 := by decide +kernel
theorem cell_24_40_2 : C 24 40 2 := by decide +kernel
theorem cell_24_40_3 : C 24 40 3 := by decide +kernel
theorem cell_24_40_4 : C 24 40 4 := by decide +kernel
theorem cell_24_40_5 : C 24 40 5 := by decide +kernel
theorem row_24_40 : ThresholdAt 24 40 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 40 0 cell_24_40_0
  | exact S 24 40 1 cell_24_40_1
  | exact S 24 40 2 cell_24_40_2
  | exact S 24 40 3 cell_24_40_3
  | exact S 24 40 4 cell_24_40_4
  | exact S 24 40 5 cell_24_40_5
theorem cell_24_41_0 : C 24 41 0 := by decide +kernel
theorem cell_24_41_1 : C 24 41 1 := by decide +kernel
theorem cell_24_41_2 : C 24 41 2 := by decide +kernel
theorem cell_24_41_3 : C 24 41 3 := by decide +kernel
theorem cell_24_41_4 : C 24 41 4 := by decide +kernel
theorem cell_24_41_5 : C 24 41 5 := by decide +kernel
theorem row_24_41 : ThresholdAt 24 41 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 41 0 cell_24_41_0
  | exact S 24 41 1 cell_24_41_1
  | exact S 24 41 2 cell_24_41_2
  | exact S 24 41 3 cell_24_41_3
  | exact S 24 41 4 cell_24_41_4
  | exact S 24 41 5 cell_24_41_5
theorem cell_24_42_0 : C 24 42 0 := by decide +kernel
theorem cell_24_42_1 : C 24 42 1 := by decide +kernel
theorem cell_24_42_2 : C 24 42 2 := by decide +kernel
theorem cell_24_42_3 : C 24 42 3 := by decide +kernel
theorem cell_24_42_4 : C 24 42 4 := by decide +kernel
theorem cell_24_42_5 : C 24 42 5 := by decide +kernel
theorem row_24_42 : ThresholdAt 24 42 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 42 0 cell_24_42_0
  | exact S 24 42 1 cell_24_42_1
  | exact S 24 42 2 cell_24_42_2
  | exact S 24 42 3 cell_24_42_3
  | exact S 24 42 4 cell_24_42_4
  | exact S 24 42 5 cell_24_42_5
theorem cell_24_43_0 : C 24 43 0 := by decide +kernel
theorem cell_24_43_1 : C 24 43 1 := by decide +kernel
theorem cell_24_43_2 : C 24 43 2 := by decide +kernel
theorem cell_24_43_3 : C 24 43 3 := by decide +kernel
theorem cell_24_43_4 : C 24 43 4 := by decide +kernel
theorem cell_24_43_5 : C 24 43 5 := by decide +kernel
theorem row_24_43 : ThresholdAt 24 43 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 43 0 cell_24_43_0
  | exact S 24 43 1 cell_24_43_1
  | exact S 24 43 2 cell_24_43_2
  | exact S 24 43 3 cell_24_43_3
  | exact S 24 43 4 cell_24_43_4
  | exact S 24 43 5 cell_24_43_5
theorem cell_24_44_0 : C 24 44 0 := by decide +kernel
theorem cell_24_44_1 : C 24 44 1 := by decide +kernel
theorem cell_24_44_2 : C 24 44 2 := by decide +kernel
theorem cell_24_44_3 : C 24 44 3 := by decide +kernel
theorem cell_24_44_4 : C 24 44 4 := by decide +kernel
theorem cell_24_44_5 : C 24 44 5 := by decide +kernel
theorem row_24_44 : ThresholdAt 24 44 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 44 0 cell_24_44_0
  | exact S 24 44 1 cell_24_44_1
  | exact S 24 44 2 cell_24_44_2
  | exact S 24 44 3 cell_24_44_3
  | exact S 24 44 4 cell_24_44_4
  | exact S 24 44 5 cell_24_44_5
theorem cell_24_45_0 : C 24 45 0 := by decide +kernel
theorem cell_24_45_1 : C 24 45 1 := by decide +kernel
theorem cell_24_45_2 : C 24 45 2 := by decide +kernel
theorem cell_24_45_3 : C 24 45 3 := by decide +kernel
theorem cell_24_45_4 : C 24 45 4 := by decide +kernel
theorem cell_24_45_5 : C 24 45 5 := by decide +kernel
theorem row_24_45 : ThresholdAt 24 45 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 45 0 cell_24_45_0
  | exact S 24 45 1 cell_24_45_1
  | exact S 24 45 2 cell_24_45_2
  | exact S 24 45 3 cell_24_45_3
  | exact S 24 45 4 cell_24_45_4
  | exact S 24 45 5 cell_24_45_5
theorem cell_24_46_0 : C 24 46 0 := by decide +kernel
theorem cell_24_46_1 : C 24 46 1 := by decide +kernel
theorem cell_24_46_2 : C 24 46 2 := by decide +kernel
theorem cell_24_46_3 : C 24 46 3 := by decide +kernel
theorem cell_24_46_4 : C 24 46 4 := by decide +kernel
theorem cell_24_46_5 : C 24 46 5 := by decide +kernel
theorem row_24_46 : ThresholdAt 24 46 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 46 0 cell_24_46_0
  | exact S 24 46 1 cell_24_46_1
  | exact S 24 46 2 cell_24_46_2
  | exact S 24 46 3 cell_24_46_3
  | exact S 24 46 4 cell_24_46_4
  | exact S 24 46 5 cell_24_46_5
theorem cell_24_47_0 : C 24 47 0 := by decide +kernel
theorem cell_24_47_1 : C 24 47 1 := by decide +kernel
theorem cell_24_47_2 : C 24 47 2 := by decide +kernel
theorem cell_24_47_3 : C 24 47 3 := by decide +kernel
theorem cell_24_47_4 : C 24 47 4 := by decide +kernel
theorem cell_24_47_5 : C 24 47 5 := by decide +kernel
theorem row_24_47 : ThresholdAt 24 47 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 47 0 cell_24_47_0
  | exact S 24 47 1 cell_24_47_1
  | exact S 24 47 2 cell_24_47_2
  | exact S 24 47 3 cell_24_47_3
  | exact S 24 47 4 cell_24_47_4
  | exact S 24 47 5 cell_24_47_5
theorem cell_24_48_0 : C 24 48 0 := by decide +kernel
theorem cell_24_48_1 : C 24 48 1 := by decide +kernel
theorem cell_24_48_2 : C 24 48 2 := by decide +kernel
theorem cell_24_48_3 : C 24 48 3 := by decide +kernel
theorem cell_24_48_4 : C 24 48 4 := by decide +kernel
theorem cell_24_48_5 : C 24 48 5 := by decide +kernel
theorem row_24_48 : ThresholdAt 24 48 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 48 0 cell_24_48_0
  | exact S 24 48 1 cell_24_48_1
  | exact S 24 48 2 cell_24_48_2
  | exact S 24 48 3 cell_24_48_3
  | exact S 24 48 4 cell_24_48_4
  | exact S 24 48 5 cell_24_48_5
theorem cell_24_49_0 : C 24 49 0 := by decide +kernel
theorem cell_24_49_1 : C 24 49 1 := by decide +kernel
theorem cell_24_49_2 : C 24 49 2 := by decide +kernel
theorem cell_24_49_3 : C 24 49 3 := by decide +kernel
theorem cell_24_49_4 : C 24 49 4 := by decide +kernel
theorem cell_24_49_5 : C 24 49 5 := by decide +kernel
theorem row_24_49 : ThresholdAt 24 49 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 49 0 cell_24_49_0
  | exact S 24 49 1 cell_24_49_1
  | exact S 24 49 2 cell_24_49_2
  | exact S 24 49 3 cell_24_49_3
  | exact S 24 49 4 cell_24_49_4
  | exact S 24 49 5 cell_24_49_5
theorem cell_24_50_0 : C 24 50 0 := by decide +kernel
theorem cell_24_50_1 : C 24 50 1 := by decide +kernel
theorem cell_24_50_2 : C 24 50 2 := by decide +kernel
theorem cell_24_50_3 : C 24 50 3 := by decide +kernel
theorem cell_24_50_4 : C 24 50 4 := by decide +kernel
theorem cell_24_50_5 : C 24 50 5 := by decide +kernel
theorem row_24_50 : ThresholdAt 24 50 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 50 0 cell_24_50_0
  | exact S 24 50 1 cell_24_50_1
  | exact S 24 50 2 cell_24_50_2
  | exact S 24 50 3 cell_24_50_3
  | exact S 24 50 4 cell_24_50_4
  | exact S 24 50 5 cell_24_50_5
theorem cell_24_51_0 : C 24 51 0 := by decide +kernel
theorem cell_24_51_1 : C 24 51 1 := by decide +kernel
theorem cell_24_51_2 : C 24 51 2 := by decide +kernel
theorem cell_24_51_3 : C 24 51 3 := by decide +kernel
theorem cell_24_51_4 : C 24 51 4 := by decide +kernel
theorem cell_24_51_5 : C 24 51 5 := by decide +kernel
theorem row_24_51 : ThresholdAt 24 51 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 51 0 cell_24_51_0
  | exact S 24 51 1 cell_24_51_1
  | exact S 24 51 2 cell_24_51_2
  | exact S 24 51 3 cell_24_51_3
  | exact S 24 51 4 cell_24_51_4
  | exact S 24 51 5 cell_24_51_5
theorem cell_24_52_0 : C 24 52 0 := by decide +kernel
theorem cell_24_52_1 : C 24 52 1 := by decide +kernel
theorem cell_24_52_2 : C 24 52 2 := by decide +kernel
theorem cell_24_52_3 : C 24 52 3 := by decide +kernel
theorem cell_24_52_4 : C 24 52 4 := by decide +kernel
theorem cell_24_52_5 : C 24 52 5 := by decide +kernel
theorem row_24_52 : ThresholdAt 24 52 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 52 0 cell_24_52_0
  | exact S 24 52 1 cell_24_52_1
  | exact S 24 52 2 cell_24_52_2
  | exact S 24 52 3 cell_24_52_3
  | exact S 24 52 4 cell_24_52_4
  | exact S 24 52 5 cell_24_52_5
theorem cell_24_53_0 : C 24 53 0 := by decide +kernel
theorem cell_24_53_1 : C 24 53 1 := by decide +kernel
theorem cell_24_53_2 : C 24 53 2 := by decide +kernel
theorem cell_24_53_3 : C 24 53 3 := by decide +kernel
theorem cell_24_53_4 : C 24 53 4 := by decide +kernel
theorem cell_24_53_5 : C 24 53 5 := by decide +kernel
theorem row_24_53 : ThresholdAt 24 53 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 53 0 cell_24_53_0
  | exact S 24 53 1 cell_24_53_1
  | exact S 24 53 2 cell_24_53_2
  | exact S 24 53 3 cell_24_53_3
  | exact S 24 53 4 cell_24_53_4
  | exact S 24 53 5 cell_24_53_5
theorem cell_24_54_0 : C 24 54 0 := by decide +kernel
theorem cell_24_54_1 : C 24 54 1 := by decide +kernel
theorem cell_24_54_2 : C 24 54 2 := by decide +kernel
theorem cell_24_54_3 : C 24 54 3 := by decide +kernel
theorem cell_24_54_4 : C 24 54 4 := by decide +kernel
theorem cell_24_54_5 : C 24 54 5 := by decide +kernel
theorem row_24_54 : ThresholdAt 24 54 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 54 0 cell_24_54_0
  | exact S 24 54 1 cell_24_54_1
  | exact S 24 54 2 cell_24_54_2
  | exact S 24 54 3 cell_24_54_3
  | exact S 24 54 4 cell_24_54_4
  | exact S 24 54 5 cell_24_54_5
theorem cell_24_55_0 : C 24 55 0 := by decide +kernel
theorem cell_24_55_1 : C 24 55 1 := by decide +kernel
theorem cell_24_55_2 : C 24 55 2 := by decide +kernel
theorem cell_24_55_3 : C 24 55 3 := by decide +kernel
theorem cell_24_55_4 : C 24 55 4 := by decide +kernel
theorem cell_24_55_5 : C 24 55 5 := by decide +kernel
theorem row_24_55 : ThresholdAt 24 55 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 55 0 cell_24_55_0
  | exact S 24 55 1 cell_24_55_1
  | exact S 24 55 2 cell_24_55_2
  | exact S 24 55 3 cell_24_55_3
  | exact S 24 55 4 cell_24_55_4
  | exact S 24 55 5 cell_24_55_5
theorem cell_24_56_0 : C 24 56 0 := by decide +kernel
theorem cell_24_56_1 : C 24 56 1 := by decide +kernel
theorem cell_24_56_2 : C 24 56 2 := by decide +kernel
theorem cell_24_56_3 : C 24 56 3 := by decide +kernel
theorem cell_24_56_4 : C 24 56 4 := by decide +kernel
theorem cell_24_56_5 : C 24 56 5 := by decide +kernel
theorem row_24_56 : ThresholdAt 24 56 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 56 0 cell_24_56_0
  | exact S 24 56 1 cell_24_56_1
  | exact S 24 56 2 cell_24_56_2
  | exact S 24 56 3 cell_24_56_3
  | exact S 24 56 4 cell_24_56_4
  | exact S 24 56 5 cell_24_56_5
theorem cell_24_57_0 : C 24 57 0 := by decide +kernel
theorem cell_24_57_1 : C 24 57 1 := by decide +kernel
theorem cell_24_57_2 : C 24 57 2 := by decide +kernel
theorem cell_24_57_3 : C 24 57 3 := by decide +kernel
theorem cell_24_57_4 : C 24 57 4 := by decide +kernel
theorem cell_24_57_5 : C 24 57 5 := by decide +kernel
theorem row_24_57 : ThresholdAt 24 57 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 57 0 cell_24_57_0
  | exact S 24 57 1 cell_24_57_1
  | exact S 24 57 2 cell_24_57_2
  | exact S 24 57 3 cell_24_57_3
  | exact S 24 57 4 cell_24_57_4
  | exact S 24 57 5 cell_24_57_5
theorem cell_24_58_0 : C 24 58 0 := by decide +kernel
theorem cell_24_58_1 : C 24 58 1 := by decide +kernel
theorem cell_24_58_2 : C 24 58 2 := by decide +kernel
theorem cell_24_58_3 : C 24 58 3 := by decide +kernel
theorem cell_24_58_4 : C 24 58 4 := by decide +kernel
theorem cell_24_58_5 : C 24 58 5 := by decide +kernel
theorem row_24_58 : ThresholdAt 24 58 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 58 0 cell_24_58_0
  | exact S 24 58 1 cell_24_58_1
  | exact S 24 58 2 cell_24_58_2
  | exact S 24 58 3 cell_24_58_3
  | exact S 24 58 4 cell_24_58_4
  | exact S 24 58 5 cell_24_58_5
theorem cell_24_59_0 : C 24 59 0 := by decide +kernel
theorem cell_24_59_1 : C 24 59 1 := by decide +kernel
theorem cell_24_59_2 : C 24 59 2 := by decide +kernel
theorem cell_24_59_3 : C 24 59 3 := by decide +kernel
theorem cell_24_59_4 : C 24 59 4 := by decide +kernel
theorem cell_24_59_5 : C 24 59 5 := by decide +kernel
theorem row_24_59 : ThresholdAt 24 59 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 59 0 cell_24_59_0
  | exact S 24 59 1 cell_24_59_1
  | exact S 24 59 2 cell_24_59_2
  | exact S 24 59 3 cell_24_59_3
  | exact S 24 59 4 cell_24_59_4
  | exact S 24 59 5 cell_24_59_5
theorem cell_24_60_0 : C 24 60 0 := by decide +kernel
theorem cell_24_60_1 : C 24 60 1 := by decide +kernel
theorem cell_24_60_2 : C 24 60 2 := by decide +kernel
theorem cell_24_60_3 : C 24 60 3 := by decide +kernel
theorem cell_24_60_4 : C 24 60 4 := by decide +kernel
theorem cell_24_60_5 : C 24 60 5 := by decide +kernel
theorem row_24_60 : ThresholdAt 24 60 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 60 0 cell_24_60_0
  | exact S 24 60 1 cell_24_60_1
  | exact S 24 60 2 cell_24_60_2
  | exact S 24 60 3 cell_24_60_3
  | exact S 24 60 4 cell_24_60_4
  | exact S 24 60 5 cell_24_60_5
theorem cell_24_61_0 : C 24 61 0 := by decide +kernel
theorem cell_24_61_1 : C 24 61 1 := by decide +kernel
theorem cell_24_61_2 : C 24 61 2 := by decide +kernel
theorem cell_24_61_3 : C 24 61 3 := by decide +kernel
theorem cell_24_61_4 : C 24 61 4 := by decide +kernel
theorem cell_24_61_5 : C 24 61 5 := by decide +kernel
theorem row_24_61 : ThresholdAt 24 61 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 61 0 cell_24_61_0
  | exact S 24 61 1 cell_24_61_1
  | exact S 24 61 2 cell_24_61_2
  | exact S 24 61 3 cell_24_61_3
  | exact S 24 61 4 cell_24_61_4
  | exact S 24 61 5 cell_24_61_5
theorem cell_24_62_0 : C 24 62 0 := by decide +kernel
theorem cell_24_62_1 : C 24 62 1 := by decide +kernel
theorem cell_24_62_2 : C 24 62 2 := by decide +kernel
theorem cell_24_62_3 : C 24 62 3 := by decide +kernel
theorem cell_24_62_4 : C 24 62 4 := by decide +kernel
theorem cell_24_62_5 : C 24 62 5 := by decide +kernel
theorem row_24_62 : ThresholdAt 24 62 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 62 0 cell_24_62_0
  | exact S 24 62 1 cell_24_62_1
  | exact S 24 62 2 cell_24_62_2
  | exact S 24 62 3 cell_24_62_3
  | exact S 24 62 4 cell_24_62_4
  | exact S 24 62 5 cell_24_62_5
theorem cell_24_63_0 : C 24 63 0 := by decide +kernel
theorem cell_24_63_1 : C 24 63 1 := by decide +kernel
theorem cell_24_63_2 : C 24 63 2 := by decide +kernel
theorem cell_24_63_3 : C 24 63 3 := by decide +kernel
theorem cell_24_63_4 : C 24 63 4 := by decide +kernel
theorem cell_24_63_5 : C 24 63 5 := by decide +kernel
theorem row_24_63 : ThresholdAt 24 63 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 63 0 cell_24_63_0
  | exact S 24 63 1 cell_24_63_1
  | exact S 24 63 2 cell_24_63_2
  | exact S 24 63 3 cell_24_63_3
  | exact S 24 63 4 cell_24_63_4
  | exact S 24 63 5 cell_24_63_5
theorem cell_24_64_0 : C 24 64 0 := by decide +kernel
theorem cell_24_64_1 : C 24 64 1 := by decide +kernel
theorem cell_24_64_2 : C 24 64 2 := by decide +kernel
theorem cell_24_64_3 : C 24 64 3 := by decide +kernel
theorem cell_24_64_4 : C 24 64 4 := by decide +kernel
theorem cell_24_64_5 : C 24 64 5 := by decide +kernel
theorem row_24_64 : ThresholdAt 24 64 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 64 0 cell_24_64_0
  | exact S 24 64 1 cell_24_64_1
  | exact S 24 64 2 cell_24_64_2
  | exact S 24 64 3 cell_24_64_3
  | exact S 24 64 4 cell_24_64_4
  | exact S 24 64 5 cell_24_64_5
theorem cell_24_65_0 : C 24 65 0 := by decide +kernel
theorem cell_24_65_1 : C 24 65 1 := by decide +kernel
theorem cell_24_65_2 : C 24 65 2 := by decide +kernel
theorem cell_24_65_3 : C 24 65 3 := by decide +kernel
theorem cell_24_65_4 : C 24 65 4 := by decide +kernel
theorem cell_24_65_5 : C 24 65 5 := by decide +kernel
theorem row_24_65 : ThresholdAt 24 65 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 65 0 cell_24_65_0
  | exact S 24 65 1 cell_24_65_1
  | exact S 24 65 2 cell_24_65_2
  | exact S 24 65 3 cell_24_65_3
  | exact S 24 65 4 cell_24_65_4
  | exact S 24 65 5 cell_24_65_5
theorem cell_24_66_0 : C 24 66 0 := by decide +kernel
theorem cell_24_66_1 : C 24 66 1 := by decide +kernel
theorem cell_24_66_2 : C 24 66 2 := by decide +kernel
theorem cell_24_66_3 : C 24 66 3 := by decide +kernel
theorem cell_24_66_4 : C 24 66 4 := by decide +kernel
theorem cell_24_66_5 : C 24 66 5 := by decide +kernel
theorem row_24_66 : ThresholdAt 24 66 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 66 0 cell_24_66_0
  | exact S 24 66 1 cell_24_66_1
  | exact S 24 66 2 cell_24_66_2
  | exact S 24 66 3 cell_24_66_3
  | exact S 24 66 4 cell_24_66_4
  | exact S 24 66 5 cell_24_66_5
theorem cell_24_67_0 : C 24 67 0 := by decide +kernel
theorem cell_24_67_1 : C 24 67 1 := by decide +kernel
theorem cell_24_67_2 : C 24 67 2 := by decide +kernel
theorem cell_24_67_3 : C 24 67 3 := by decide +kernel
theorem cell_24_67_4 : C 24 67 4 := by decide +kernel
theorem cell_24_67_5 : C 24 67 5 := by decide +kernel
theorem row_24_67 : ThresholdAt 24 67 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 67 0 cell_24_67_0
  | exact S 24 67 1 cell_24_67_1
  | exact S 24 67 2 cell_24_67_2
  | exact S 24 67 3 cell_24_67_3
  | exact S 24 67 4 cell_24_67_4
  | exact S 24 67 5 cell_24_67_5
theorem cell_24_68_0 : C 24 68 0 := by decide +kernel
theorem cell_24_68_1 : C 24 68 1 := by decide +kernel
theorem cell_24_68_2 : C 24 68 2 := by decide +kernel
theorem cell_24_68_3 : C 24 68 3 := by decide +kernel
theorem cell_24_68_4 : C 24 68 4 := by decide +kernel
theorem cell_24_68_5 : C 24 68 5 := by decide +kernel
theorem row_24_68 : ThresholdAt 24 68 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 68 0 cell_24_68_0
  | exact S 24 68 1 cell_24_68_1
  | exact S 24 68 2 cell_24_68_2
  | exact S 24 68 3 cell_24_68_3
  | exact S 24 68 4 cell_24_68_4
  | exact S 24 68 5 cell_24_68_5
theorem cell_24_69_0 : C 24 69 0 := by decide +kernel
theorem cell_24_69_1 : C 24 69 1 := by decide +kernel
theorem cell_24_69_2 : C 24 69 2 := by decide +kernel
theorem cell_24_69_3 : C 24 69 3 := by decide +kernel
theorem cell_24_69_4 : C 24 69 4 := by decide +kernel
theorem cell_24_69_5 : C 24 69 5 := by decide +kernel
theorem row_24_69 : ThresholdAt 24 69 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 69 0 cell_24_69_0
  | exact S 24 69 1 cell_24_69_1
  | exact S 24 69 2 cell_24_69_2
  | exact S 24 69 3 cell_24_69_3
  | exact S 24 69 4 cell_24_69_4
  | exact S 24 69 5 cell_24_69_5
theorem cell_24_70_0 : C 24 70 0 := by decide +kernel
theorem cell_24_70_1 : C 24 70 1 := by decide +kernel
theorem cell_24_70_2 : C 24 70 2 := by decide +kernel
theorem cell_24_70_3 : C 24 70 3 := by decide +kernel
theorem cell_24_70_4 : C 24 70 4 := by decide +kernel
theorem cell_24_70_5 : C 24 70 5 := by decide +kernel
theorem row_24_70 : ThresholdAt 24 70 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 70 0 cell_24_70_0
  | exact S 24 70 1 cell_24_70_1
  | exact S 24 70 2 cell_24_70_2
  | exact S 24 70 3 cell_24_70_3
  | exact S 24 70 4 cell_24_70_4
  | exact S 24 70 5 cell_24_70_5
theorem cell_24_71_0 : C 24 71 0 := by decide +kernel
theorem cell_24_71_1 : C 24 71 1 := by decide +kernel
theorem cell_24_71_2 : C 24 71 2 := by decide +kernel
theorem cell_24_71_3 : C 24 71 3 := by decide +kernel
theorem cell_24_71_4 : C 24 71 4 := by decide +kernel
theorem cell_24_71_5 : C 24 71 5 := by decide +kernel
theorem row_24_71 : ThresholdAt 24 71 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 71 0 cell_24_71_0
  | exact S 24 71 1 cell_24_71_1
  | exact S 24 71 2 cell_24_71_2
  | exact S 24 71 3 cell_24_71_3
  | exact S 24 71 4 cell_24_71_4
  | exact S 24 71 5 cell_24_71_5
theorem cell_24_72_0 : C 24 72 0 := by decide +kernel
theorem cell_24_72_1 : C 24 72 1 := by decide +kernel
theorem cell_24_72_2 : C 24 72 2 := by decide +kernel
theorem cell_24_72_3 : C 24 72 3 := by decide +kernel
theorem cell_24_72_4 : C 24 72 4 := by decide +kernel
theorem cell_24_72_5 : C 24 72 5 := by decide +kernel
theorem row_24_72 : ThresholdAt 24 72 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 72 0 cell_24_72_0
  | exact S 24 72 1 cell_24_72_1
  | exact S 24 72 2 cell_24_72_2
  | exact S 24 72 3 cell_24_72_3
  | exact S 24 72 4 cell_24_72_4
  | exact S 24 72 5 cell_24_72_5
theorem cell_24_73_0 : C 24 73 0 := by decide +kernel
theorem cell_24_73_1 : C 24 73 1 := by decide +kernel
theorem cell_24_73_2 : C 24 73 2 := by decide +kernel
theorem cell_24_73_3 : C 24 73 3 := by decide +kernel
theorem cell_24_73_4 : C 24 73 4 := by decide +kernel
theorem cell_24_73_5 : C 24 73 5 := by decide +kernel
theorem row_24_73 : ThresholdAt 24 73 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 73 0 cell_24_73_0
  | exact S 24 73 1 cell_24_73_1
  | exact S 24 73 2 cell_24_73_2
  | exact S 24 73 3 cell_24_73_3
  | exact S 24 73 4 cell_24_73_4
  | exact S 24 73 5 cell_24_73_5
theorem cell_24_74_0 : C 24 74 0 := by decide +kernel
theorem cell_24_74_1 : C 24 74 1 := by decide +kernel
theorem cell_24_74_2 : C 24 74 2 := by decide +kernel
theorem cell_24_74_3 : C 24 74 3 := by decide +kernel
theorem cell_24_74_4 : C 24 74 4 := by decide +kernel
theorem cell_24_74_5 : C 24 74 5 := by decide +kernel
theorem row_24_74 : ThresholdAt 24 74 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 74 0 cell_24_74_0
  | exact S 24 74 1 cell_24_74_1
  | exact S 24 74 2 cell_24_74_2
  | exact S 24 74 3 cell_24_74_3
  | exact S 24 74 4 cell_24_74_4
  | exact S 24 74 5 cell_24_74_5
theorem cell_24_75_0 : C 24 75 0 := by decide +kernel
theorem cell_24_75_1 : C 24 75 1 := by decide +kernel
theorem cell_24_75_2 : C 24 75 2 := by decide +kernel
theorem cell_24_75_3 : C 24 75 3 := by decide +kernel
theorem cell_24_75_4 : C 24 75 4 := by decide +kernel
theorem cell_24_75_5 : C 24 75 5 := by decide +kernel
theorem row_24_75 : ThresholdAt 24 75 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 75 0 cell_24_75_0
  | exact S 24 75 1 cell_24_75_1
  | exact S 24 75 2 cell_24_75_2
  | exact S 24 75 3 cell_24_75_3
  | exact S 24 75 4 cell_24_75_4
  | exact S 24 75 5 cell_24_75_5
theorem cell_24_76_0 : C 24 76 0 := by decide +kernel
theorem cell_24_76_1 : C 24 76 1 := by decide +kernel
theorem cell_24_76_2 : C 24 76 2 := by decide +kernel
theorem cell_24_76_3 : C 24 76 3 := by decide +kernel
theorem cell_24_76_4 : C 24 76 4 := by decide +kernel
theorem cell_24_76_5 : C 24 76 5 := by decide +kernel
theorem row_24_76 : ThresholdAt 24 76 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 76 0 cell_24_76_0
  | exact S 24 76 1 cell_24_76_1
  | exact S 24 76 2 cell_24_76_2
  | exact S 24 76 3 cell_24_76_3
  | exact S 24 76 4 cell_24_76_4
  | exact S 24 76 5 cell_24_76_5
theorem cell_24_77_0 : C 24 77 0 := by decide +kernel
theorem cell_24_77_1 : C 24 77 1 := by decide +kernel
theorem cell_24_77_2 : C 24 77 2 := by decide +kernel
theorem cell_24_77_3 : C 24 77 3 := by decide +kernel
theorem cell_24_77_4 : C 24 77 4 := by decide +kernel
theorem cell_24_77_5 : C 24 77 5 := by decide +kernel
theorem row_24_77 : ThresholdAt 24 77 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 77 0 cell_24_77_0
  | exact S 24 77 1 cell_24_77_1
  | exact S 24 77 2 cell_24_77_2
  | exact S 24 77 3 cell_24_77_3
  | exact S 24 77 4 cell_24_77_4
  | exact S 24 77 5 cell_24_77_5
theorem cell_24_78_0 : C 24 78 0 := by decide +kernel
theorem cell_24_78_1 : C 24 78 1 := by decide +kernel
theorem cell_24_78_2 : C 24 78 2 := by decide +kernel
theorem cell_24_78_3 : C 24 78 3 := by decide +kernel
theorem cell_24_78_4 : C 24 78 4 := by decide +kernel
theorem cell_24_78_5 : C 24 78 5 := by decide +kernel
theorem row_24_78 : ThresholdAt 24 78 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 78 0 cell_24_78_0
  | exact S 24 78 1 cell_24_78_1
  | exact S 24 78 2 cell_24_78_2
  | exact S 24 78 3 cell_24_78_3
  | exact S 24 78 4 cell_24_78_4
  | exact S 24 78 5 cell_24_78_5
theorem cell_24_79_0 : C 24 79 0 := by decide +kernel
theorem cell_24_79_1 : C 24 79 1 := by decide +kernel
theorem cell_24_79_2 : C 24 79 2 := by decide +kernel
theorem cell_24_79_3 : C 24 79 3 := by decide +kernel
theorem cell_24_79_4 : C 24 79 4 := by decide +kernel
theorem cell_24_79_5 : C 24 79 5 := by decide +kernel
theorem row_24_79 : ThresholdAt 24 79 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 79 0 cell_24_79_0
  | exact S 24 79 1 cell_24_79_1
  | exact S 24 79 2 cell_24_79_2
  | exact S 24 79 3 cell_24_79_3
  | exact S 24 79 4 cell_24_79_4
  | exact S 24 79 5 cell_24_79_5
theorem cell_24_80_0 : C 24 80 0 := by decide +kernel
theorem cell_24_80_1 : C 24 80 1 := by decide +kernel
theorem cell_24_80_2 : C 24 80 2 := by decide +kernel
theorem cell_24_80_3 : C 24 80 3 := by decide +kernel
theorem cell_24_80_4 : C 24 80 4 := by decide +kernel
theorem cell_24_80_5 : C 24 80 5 := by decide +kernel
theorem row_24_80 : ThresholdAt 24 80 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 80 0 cell_24_80_0
  | exact S 24 80 1 cell_24_80_1
  | exact S 24 80 2 cell_24_80_2
  | exact S 24 80 3 cell_24_80_3
  | exact S 24 80 4 cell_24_80_4
  | exact S 24 80 5 cell_24_80_5
theorem cell_24_81_0 : C 24 81 0 := by decide +kernel
theorem cell_24_81_1 : C 24 81 1 := by decide +kernel
theorem cell_24_81_2 : C 24 81 2 := by decide +kernel
theorem cell_24_81_3 : C 24 81 3 := by decide +kernel
theorem cell_24_81_4 : C 24 81 4 := by decide +kernel
theorem cell_24_81_5 : C 24 81 5 := by decide +kernel
theorem row_24_81 : ThresholdAt 24 81 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 81 0 cell_24_81_0
  | exact S 24 81 1 cell_24_81_1
  | exact S 24 81 2 cell_24_81_2
  | exact S 24 81 3 cell_24_81_3
  | exact S 24 81 4 cell_24_81_4
  | exact S 24 81 5 cell_24_81_5
theorem cell_24_82_0 : C 24 82 0 := by decide +kernel
theorem cell_24_82_1 : C 24 82 1 := by decide +kernel
theorem cell_24_82_2 : C 24 82 2 := by decide +kernel
theorem cell_24_82_3 : C 24 82 3 := by decide +kernel
theorem cell_24_82_4 : C 24 82 4 := by decide +kernel
theorem cell_24_82_5 : C 24 82 5 := by decide +kernel
theorem row_24_82 : ThresholdAt 24 82 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 82 0 cell_24_82_0
  | exact S 24 82 1 cell_24_82_1
  | exact S 24 82 2 cell_24_82_2
  | exact S 24 82 3 cell_24_82_3
  | exact S 24 82 4 cell_24_82_4
  | exact S 24 82 5 cell_24_82_5
theorem cell_24_83_0 : C 24 83 0 := by decide +kernel
theorem cell_24_83_1 : C 24 83 1 := by decide +kernel
theorem cell_24_83_2 : C 24 83 2 := by decide +kernel
theorem cell_24_83_3 : C 24 83 3 := by decide +kernel
theorem cell_24_83_4 : C 24 83 4 := by decide +kernel
theorem cell_24_83_5 : C 24 83 5 := by decide +kernel
theorem row_24_83 : ThresholdAt 24 83 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 83 0 cell_24_83_0
  | exact S 24 83 1 cell_24_83_1
  | exact S 24 83 2 cell_24_83_2
  | exact S 24 83 3 cell_24_83_3
  | exact S 24 83 4 cell_24_83_4
  | exact S 24 83 5 cell_24_83_5
theorem cell_24_84_0 : C 24 84 0 := by decide +kernel
theorem cell_24_84_1 : C 24 84 1 := by decide +kernel
theorem cell_24_84_2 : C 24 84 2 := by decide +kernel
theorem cell_24_84_3 : C 24 84 3 := by decide +kernel
theorem cell_24_84_4 : C 24 84 4 := by decide +kernel
theorem cell_24_84_5 : C 24 84 5 := by decide +kernel
theorem row_24_84 : ThresholdAt 24 84 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 84 0 cell_24_84_0
  | exact S 24 84 1 cell_24_84_1
  | exact S 24 84 2 cell_24_84_2
  | exact S 24 84 3 cell_24_84_3
  | exact S 24 84 4 cell_24_84_4
  | exact S 24 84 5 cell_24_84_5
theorem cell_24_85_0 : C 24 85 0 := by decide +kernel
theorem cell_24_85_1 : C 24 85 1 := by decide +kernel
theorem cell_24_85_2 : C 24 85 2 := by decide +kernel
theorem cell_24_85_3 : C 24 85 3 := by decide +kernel
theorem cell_24_85_4 : C 24 85 4 := by decide +kernel
theorem cell_24_85_5 : C 24 85 5 := by decide +kernel
theorem row_24_85 : ThresholdAt 24 85 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 85 0 cell_24_85_0
  | exact S 24 85 1 cell_24_85_1
  | exact S 24 85 2 cell_24_85_2
  | exact S 24 85 3 cell_24_85_3
  | exact S 24 85 4 cell_24_85_4
  | exact S 24 85 5 cell_24_85_5
theorem cell_24_86_0 : C 24 86 0 := by decide +kernel
theorem cell_24_86_1 : C 24 86 1 := by decide +kernel
theorem cell_24_86_2 : C 24 86 2 := by decide +kernel
theorem cell_24_86_3 : C 24 86 3 := by decide +kernel
theorem cell_24_86_4 : C 24 86 4 := by decide +kernel
theorem cell_24_86_5 : C 24 86 5 := by decide +kernel
theorem row_24_86 : ThresholdAt 24 86 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 86 0 cell_24_86_0
  | exact S 24 86 1 cell_24_86_1
  | exact S 24 86 2 cell_24_86_2
  | exact S 24 86 3 cell_24_86_3
  | exact S 24 86 4 cell_24_86_4
  | exact S 24 86 5 cell_24_86_5
theorem cell_24_87_0 : C 24 87 0 := by decide +kernel
theorem cell_24_87_1 : C 24 87 1 := by decide +kernel
theorem cell_24_87_2 : C 24 87 2 := by decide +kernel
theorem cell_24_87_3 : C 24 87 3 := by decide +kernel
theorem cell_24_87_4 : C 24 87 4 := by decide +kernel
theorem cell_24_87_5 : C 24 87 5 := by decide +kernel
theorem row_24_87 : ThresholdAt 24 87 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 87 0 cell_24_87_0
  | exact S 24 87 1 cell_24_87_1
  | exact S 24 87 2 cell_24_87_2
  | exact S 24 87 3 cell_24_87_3
  | exact S 24 87 4 cell_24_87_4
  | exact S 24 87 5 cell_24_87_5
theorem cell_24_88_0 : C 24 88 0 := by decide +kernel
theorem cell_24_88_1 : C 24 88 1 := by decide +kernel
theorem cell_24_88_2 : C 24 88 2 := by decide +kernel
theorem cell_24_88_3 : C 24 88 3 := by decide +kernel
theorem cell_24_88_4 : C 24 88 4 := by decide +kernel
theorem cell_24_88_5 : C 24 88 5 := by decide +kernel
theorem row_24_88 : ThresholdAt 24 88 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 88 0 cell_24_88_0
  | exact S 24 88 1 cell_24_88_1
  | exact S 24 88 2 cell_24_88_2
  | exact S 24 88 3 cell_24_88_3
  | exact S 24 88 4 cell_24_88_4
  | exact S 24 88 5 cell_24_88_5
theorem cell_24_89_0 : C 24 89 0 := by decide +kernel
theorem cell_24_89_1 : C 24 89 1 := by decide +kernel
theorem cell_24_89_2 : C 24 89 2 := by decide +kernel
theorem cell_24_89_3 : C 24 89 3 := by decide +kernel
theorem cell_24_89_4 : C 24 89 4 := by decide +kernel
theorem cell_24_89_5 : C 24 89 5 := by decide +kernel
theorem row_24_89 : ThresholdAt 24 89 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 89 0 cell_24_89_0
  | exact S 24 89 1 cell_24_89_1
  | exact S 24 89 2 cell_24_89_2
  | exact S 24 89 3 cell_24_89_3
  | exact S 24 89 4 cell_24_89_4
  | exact S 24 89 5 cell_24_89_5
theorem cell_24_90_0 : C 24 90 0 := by decide +kernel
theorem cell_24_90_1 : C 24 90 1 := by decide +kernel
theorem cell_24_90_2 : C 24 90 2 := by decide +kernel
theorem cell_24_90_3 : C 24 90 3 := by decide +kernel
theorem cell_24_90_4 : C 24 90 4 := by decide +kernel
theorem cell_24_90_5 : C 24 90 5 := by decide +kernel
theorem row_24_90 : ThresholdAt 24 90 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 90 0 cell_24_90_0
  | exact S 24 90 1 cell_24_90_1
  | exact S 24 90 2 cell_24_90_2
  | exact S 24 90 3 cell_24_90_3
  | exact S 24 90 4 cell_24_90_4
  | exact S 24 90 5 cell_24_90_5
theorem cell_24_91_0 : C 24 91 0 := by decide +kernel
theorem cell_24_91_1 : C 24 91 1 := by decide +kernel
theorem cell_24_91_2 : C 24 91 2 := by decide +kernel
theorem cell_24_91_3 : C 24 91 3 := by decide +kernel
theorem cell_24_91_4 : C 24 91 4 := by decide +kernel
theorem cell_24_91_5 : C 24 91 5 := by decide +kernel
theorem row_24_91 : ThresholdAt 24 91 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 91 0 cell_24_91_0
  | exact S 24 91 1 cell_24_91_1
  | exact S 24 91 2 cell_24_91_2
  | exact S 24 91 3 cell_24_91_3
  | exact S 24 91 4 cell_24_91_4
  | exact S 24 91 5 cell_24_91_5
theorem cell_24_92_0 : C 24 92 0 := by decide +kernel
theorem cell_24_92_1 : C 24 92 1 := by decide +kernel
theorem cell_24_92_2 : C 24 92 2 := by decide +kernel
theorem cell_24_92_3 : C 24 92 3 := by decide +kernel
theorem cell_24_92_4 : C 24 92 4 := by decide +kernel
theorem cell_24_92_5 : C 24 92 5 := by decide +kernel
theorem row_24_92 : ThresholdAt 24 92 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 92 0 cell_24_92_0
  | exact S 24 92 1 cell_24_92_1
  | exact S 24 92 2 cell_24_92_2
  | exact S 24 92 3 cell_24_92_3
  | exact S 24 92 4 cell_24_92_4
  | exact S 24 92 5 cell_24_92_5
theorem cell_24_93_0 : C 24 93 0 := by decide +kernel
theorem cell_24_93_1 : C 24 93 1 := by decide +kernel
theorem cell_24_93_2 : C 24 93 2 := by decide +kernel
theorem cell_24_93_3 : C 24 93 3 := by decide +kernel
theorem cell_24_93_4 : C 24 93 4 := by decide +kernel
theorem cell_24_93_5 : C 24 93 5 := by decide +kernel
theorem row_24_93 : ThresholdAt 24 93 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 93 0 cell_24_93_0
  | exact S 24 93 1 cell_24_93_1
  | exact S 24 93 2 cell_24_93_2
  | exact S 24 93 3 cell_24_93_3
  | exact S 24 93 4 cell_24_93_4
  | exact S 24 93 5 cell_24_93_5
theorem cell_24_94_0 : C 24 94 0 := by decide +kernel
theorem cell_24_94_1 : C 24 94 1 := by decide +kernel
theorem cell_24_94_2 : C 24 94 2 := by decide +kernel
theorem cell_24_94_3 : C 24 94 3 := by decide +kernel
theorem cell_24_94_4 : C 24 94 4 := by decide +kernel
theorem cell_24_94_5 : C 24 94 5 := by decide +kernel
theorem row_24_94 : ThresholdAt 24 94 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 94 0 cell_24_94_0
  | exact S 24 94 1 cell_24_94_1
  | exact S 24 94 2 cell_24_94_2
  | exact S 24 94 3 cell_24_94_3
  | exact S 24 94 4 cell_24_94_4
  | exact S 24 94 5 cell_24_94_5
theorem cell_24_95_0 : C 24 95 0 := by decide +kernel
theorem cell_24_95_1 : C 24 95 1 := by decide +kernel
theorem cell_24_95_2 : C 24 95 2 := by decide +kernel
theorem cell_24_95_3 : C 24 95 3 := by decide +kernel
theorem cell_24_95_4 : C 24 95 4 := by decide +kernel
theorem cell_24_95_5 : C 24 95 5 := by decide +kernel
theorem row_24_95 : ThresholdAt 24 95 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 95 0 cell_24_95_0
  | exact S 24 95 1 cell_24_95_1
  | exact S 24 95 2 cell_24_95_2
  | exact S 24 95 3 cell_24_95_3
  | exact S 24 95 4 cell_24_95_4
  | exact S 24 95 5 cell_24_95_5
theorem cell_24_96_0 : C 24 96 0 := by decide +kernel
theorem cell_24_96_1 : C 24 96 1 := by decide +kernel
theorem cell_24_96_2 : C 24 96 2 := by decide +kernel
theorem cell_24_96_3 : C 24 96 3 := by decide +kernel
theorem cell_24_96_4 : C 24 96 4 := by decide +kernel
theorem cell_24_96_5 : C 24 96 5 := by decide +kernel
theorem row_24_96 : ThresholdAt 24 96 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 96 0 cell_24_96_0
  | exact S 24 96 1 cell_24_96_1
  | exact S 24 96 2 cell_24_96_2
  | exact S 24 96 3 cell_24_96_3
  | exact S 24 96 4 cell_24_96_4
  | exact S 24 96 5 cell_24_96_5
theorem cell_24_97_0 : C 24 97 0 := by decide +kernel
theorem cell_24_97_1 : C 24 97 1 := by decide +kernel
theorem cell_24_97_2 : C 24 97 2 := by decide +kernel
theorem cell_24_97_3 : C 24 97 3 := by decide +kernel
theorem cell_24_97_4 : C 24 97 4 := by decide +kernel
theorem cell_24_97_5 : C 24 97 5 := by decide +kernel
theorem row_24_97 : ThresholdAt 24 97 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 97 0 cell_24_97_0
  | exact S 24 97 1 cell_24_97_1
  | exact S 24 97 2 cell_24_97_2
  | exact S 24 97 3 cell_24_97_3
  | exact S 24 97 4 cell_24_97_4
  | exact S 24 97 5 cell_24_97_5
theorem cell_24_98_0 : C 24 98 0 := by decide +kernel
theorem cell_24_98_1 : C 24 98 1 := by decide +kernel
theorem cell_24_98_2 : C 24 98 2 := by decide +kernel
theorem cell_24_98_3 : C 24 98 3 := by decide +kernel
theorem cell_24_98_4 : C 24 98 4 := by decide +kernel
theorem cell_24_98_5 : C 24 98 5 := by decide +kernel
theorem row_24_98 : ThresholdAt 24 98 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 98 0 cell_24_98_0
  | exact S 24 98 1 cell_24_98_1
  | exact S 24 98 2 cell_24_98_2
  | exact S 24 98 3 cell_24_98_3
  | exact S 24 98 4 cell_24_98_4
  | exact S 24 98 5 cell_24_98_5
theorem cell_24_99_0 : C 24 99 0 := by decide +kernel
theorem cell_24_99_1 : C 24 99 1 := by decide +kernel
theorem cell_24_99_2 : C 24 99 2 := by decide +kernel
theorem cell_24_99_3 : C 24 99 3 := by decide +kernel
theorem cell_24_99_4 : C 24 99 4 := by decide +kernel
theorem cell_24_99_5 : C 24 99 5 := by decide +kernel
theorem row_24_99 : ThresholdAt 24 99 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 99 0 cell_24_99_0
  | exact S 24 99 1 cell_24_99_1
  | exact S 24 99 2 cell_24_99_2
  | exact S 24 99 3 cell_24_99_3
  | exact S 24 99 4 cell_24_99_4
  | exact S 24 99 5 cell_24_99_5
theorem cell_24_100_0 : C 24 100 0 := by decide +kernel
theorem cell_24_100_1 : C 24 100 1 := by decide +kernel
theorem cell_24_100_2 : C 24 100 2 := by decide +kernel
theorem cell_24_100_3 : C 24 100 3 := by decide +kernel
theorem cell_24_100_4 : C 24 100 4 := by decide +kernel
theorem cell_24_100_5 : C 24 100 5 := by decide +kernel
theorem row_24_100 : ThresholdAt 24 100 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 100 0 cell_24_100_0
  | exact S 24 100 1 cell_24_100_1
  | exact S 24 100 2 cell_24_100_2
  | exact S 24 100 3 cell_24_100_3
  | exact S 24 100 4 cell_24_100_4
  | exact S 24 100 5 cell_24_100_5
theorem cell_24_101_0 : C 24 101 0 := by decide +kernel
theorem cell_24_101_1 : C 24 101 1 := by decide +kernel
theorem cell_24_101_2 : C 24 101 2 := by decide +kernel
theorem cell_24_101_3 : C 24 101 3 := by decide +kernel
theorem cell_24_101_4 : C 24 101 4 := by decide +kernel
theorem cell_24_101_5 : C 24 101 5 := by decide +kernel
theorem row_24_101 : ThresholdAt 24 101 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 101 0 cell_24_101_0
  | exact S 24 101 1 cell_24_101_1
  | exact S 24 101 2 cell_24_101_2
  | exact S 24 101 3 cell_24_101_3
  | exact S 24 101 4 cell_24_101_4
  | exact S 24 101 5 cell_24_101_5
theorem cell_24_102_0 : C 24 102 0 := by decide +kernel
theorem cell_24_102_1 : C 24 102 1 := by decide +kernel
theorem cell_24_102_2 : C 24 102 2 := by decide +kernel
theorem cell_24_102_3 : C 24 102 3 := by decide +kernel
theorem cell_24_102_4 : C 24 102 4 := by decide +kernel
theorem cell_24_102_5 : C 24 102 5 := by decide +kernel
theorem row_24_102 : ThresholdAt 24 102 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 102 0 cell_24_102_0
  | exact S 24 102 1 cell_24_102_1
  | exact S 24 102 2 cell_24_102_2
  | exact S 24 102 3 cell_24_102_3
  | exact S 24 102 4 cell_24_102_4
  | exact S 24 102 5 cell_24_102_5
theorem cell_24_103_0 : C 24 103 0 := by decide +kernel
theorem cell_24_103_1 : C 24 103 1 := by decide +kernel
theorem cell_24_103_2 : C 24 103 2 := by decide +kernel
theorem cell_24_103_3 : C 24 103 3 := by decide +kernel
theorem cell_24_103_4 : C 24 103 4 := by decide +kernel
theorem cell_24_103_5 : C 24 103 5 := by decide +kernel
theorem row_24_103 : ThresholdAt 24 103 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 103 0 cell_24_103_0
  | exact S 24 103 1 cell_24_103_1
  | exact S 24 103 2 cell_24_103_2
  | exact S 24 103 3 cell_24_103_3
  | exact S 24 103 4 cell_24_103_4
  | exact S 24 103 5 cell_24_103_5
theorem cell_24_104_0 : C 24 104 0 := by decide +kernel
theorem cell_24_104_1 : C 24 104 1 := by decide +kernel
theorem cell_24_104_2 : C 24 104 2 := by decide +kernel
theorem cell_24_104_3 : C 24 104 3 := by decide +kernel
theorem cell_24_104_4 : C 24 104 4 := by decide +kernel
theorem cell_24_104_5 : C 24 104 5 := by decide +kernel
theorem row_24_104 : ThresholdAt 24 104 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 104 0 cell_24_104_0
  | exact S 24 104 1 cell_24_104_1
  | exact S 24 104 2 cell_24_104_2
  | exact S 24 104 3 cell_24_104_3
  | exact S 24 104 4 cell_24_104_4
  | exact S 24 104 5 cell_24_104_5
theorem cell_24_105_0 : C 24 105 0 := by decide +kernel
theorem cell_24_105_1 : C 24 105 1 := by decide +kernel
theorem cell_24_105_2 : C 24 105 2 := by decide +kernel
theorem cell_24_105_3 : C 24 105 3 := by decide +kernel
theorem cell_24_105_4 : C 24 105 4 := by decide +kernel
theorem cell_24_105_5 : C 24 105 5 := by decide +kernel
theorem row_24_105 : ThresholdAt 24 105 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 105 0 cell_24_105_0
  | exact S 24 105 1 cell_24_105_1
  | exact S 24 105 2 cell_24_105_2
  | exact S 24 105 3 cell_24_105_3
  | exact S 24 105 4 cell_24_105_4
  | exact S 24 105 5 cell_24_105_5
theorem cell_24_106_0 : C 24 106 0 := by decide +kernel
theorem cell_24_106_1 : C 24 106 1 := by decide +kernel
theorem cell_24_106_2 : C 24 106 2 := by decide +kernel
theorem cell_24_106_3 : C 24 106 3 := by decide +kernel
theorem cell_24_106_4 : C 24 106 4 := by decide +kernel
theorem cell_24_106_5 : C 24 106 5 := by decide +kernel
theorem row_24_106 : ThresholdAt 24 106 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 106 0 cell_24_106_0
  | exact S 24 106 1 cell_24_106_1
  | exact S 24 106 2 cell_24_106_2
  | exact S 24 106 3 cell_24_106_3
  | exact S 24 106 4 cell_24_106_4
  | exact S 24 106 5 cell_24_106_5
theorem cell_24_107_0 : C 24 107 0 := by decide +kernel
theorem cell_24_107_1 : C 24 107 1 := by decide +kernel
theorem cell_24_107_2 : C 24 107 2 := by decide +kernel
theorem cell_24_107_3 : C 24 107 3 := by decide +kernel
theorem cell_24_107_4 : C 24 107 4 := by decide +kernel
theorem cell_24_107_5 : C 24 107 5 := by decide +kernel
theorem row_24_107 : ThresholdAt 24 107 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 107 0 cell_24_107_0
  | exact S 24 107 1 cell_24_107_1
  | exact S 24 107 2 cell_24_107_2
  | exact S 24 107 3 cell_24_107_3
  | exact S 24 107 4 cell_24_107_4
  | exact S 24 107 5 cell_24_107_5
theorem cell_24_108_0 : C 24 108 0 := by decide +kernel
theorem cell_24_108_1 : C 24 108 1 := by decide +kernel
theorem cell_24_108_2 : C 24 108 2 := by decide +kernel
theorem cell_24_108_3 : C 24 108 3 := by decide +kernel
theorem cell_24_108_4 : C 24 108 4 := by decide +kernel
theorem cell_24_108_5 : C 24 108 5 := by decide +kernel
theorem row_24_108 : ThresholdAt 24 108 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 108 0 cell_24_108_0
  | exact S 24 108 1 cell_24_108_1
  | exact S 24 108 2 cell_24_108_2
  | exact S 24 108 3 cell_24_108_3
  | exact S 24 108 4 cell_24_108_4
  | exact S 24 108 5 cell_24_108_5
theorem cell_24_109_0 : C 24 109 0 := by decide +kernel
theorem cell_24_109_1 : C 24 109 1 := by decide +kernel
theorem cell_24_109_2 : C 24 109 2 := by decide +kernel
theorem cell_24_109_3 : C 24 109 3 := by decide +kernel
theorem cell_24_109_4 : C 24 109 4 := by decide +kernel
theorem cell_24_109_5 : C 24 109 5 := by decide +kernel
theorem row_24_109 : ThresholdAt 24 109 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 109 0 cell_24_109_0
  | exact S 24 109 1 cell_24_109_1
  | exact S 24 109 2 cell_24_109_2
  | exact S 24 109 3 cell_24_109_3
  | exact S 24 109 4 cell_24_109_4
  | exact S 24 109 5 cell_24_109_5
theorem cell_24_110_0 : C 24 110 0 := by decide +kernel
theorem cell_24_110_1 : C 24 110 1 := by decide +kernel
theorem cell_24_110_2 : C 24 110 2 := by decide +kernel
theorem cell_24_110_3 : C 24 110 3 := by decide +kernel
theorem cell_24_110_4 : C 24 110 4 := by decide +kernel
theorem cell_24_110_5 : C 24 110 5 := by decide +kernel
theorem row_24_110 : ThresholdAt 24 110 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 110 0 cell_24_110_0
  | exact S 24 110 1 cell_24_110_1
  | exact S 24 110 2 cell_24_110_2
  | exact S 24 110 3 cell_24_110_3
  | exact S 24 110 4 cell_24_110_4
  | exact S 24 110 5 cell_24_110_5
theorem cell_24_111_0 : C 24 111 0 := by decide +kernel
theorem cell_24_111_1 : C 24 111 1 := by decide +kernel
theorem cell_24_111_2 : C 24 111 2 := by decide +kernel
theorem cell_24_111_3 : C 24 111 3 := by decide +kernel
theorem cell_24_111_4 : C 24 111 4 := by decide +kernel
theorem cell_24_111_5 : C 24 111 5 := by decide +kernel
theorem row_24_111 : ThresholdAt 24 111 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 111 0 cell_24_111_0
  | exact S 24 111 1 cell_24_111_1
  | exact S 24 111 2 cell_24_111_2
  | exact S 24 111 3 cell_24_111_3
  | exact S 24 111 4 cell_24_111_4
  | exact S 24 111 5 cell_24_111_5
theorem cell_24_112_0 : C 24 112 0 := by decide +kernel
theorem cell_24_112_1 : C 24 112 1 := by decide +kernel
theorem cell_24_112_2 : C 24 112 2 := by decide +kernel
theorem cell_24_112_3 : C 24 112 3 := by decide +kernel
theorem cell_24_112_4 : C 24 112 4 := by decide +kernel
theorem cell_24_112_5 : C 24 112 5 := by decide +kernel
theorem row_24_112 : ThresholdAt 24 112 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 112 0 cell_24_112_0
  | exact S 24 112 1 cell_24_112_1
  | exact S 24 112 2 cell_24_112_2
  | exact S 24 112 3 cell_24_112_3
  | exact S 24 112 4 cell_24_112_4
  | exact S 24 112 5 cell_24_112_5
theorem cell_24_113_0 : C 24 113 0 := by decide +kernel
theorem cell_24_113_1 : C 24 113 1 := by decide +kernel
theorem cell_24_113_2 : C 24 113 2 := by decide +kernel
theorem cell_24_113_3 : C 24 113 3 := by decide +kernel
theorem cell_24_113_4 : C 24 113 4 := by decide +kernel
theorem cell_24_113_5 : C 24 113 5 := by decide +kernel
theorem row_24_113 : ThresholdAt 24 113 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 113 0 cell_24_113_0
  | exact S 24 113 1 cell_24_113_1
  | exact S 24 113 2 cell_24_113_2
  | exact S 24 113 3 cell_24_113_3
  | exact S 24 113 4 cell_24_113_4
  | exact S 24 113 5 cell_24_113_5
theorem cell_24_114_0 : C 24 114 0 := by decide +kernel
theorem cell_24_114_1 : C 24 114 1 := by decide +kernel
theorem cell_24_114_2 : C 24 114 2 := by decide +kernel
theorem cell_24_114_3 : C 24 114 3 := by decide +kernel
theorem cell_24_114_4 : C 24 114 4 := by decide +kernel
theorem cell_24_114_5 : C 24 114 5 := by decide +kernel
theorem row_24_114 : ThresholdAt 24 114 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 114 0 cell_24_114_0
  | exact S 24 114 1 cell_24_114_1
  | exact S 24 114 2 cell_24_114_2
  | exact S 24 114 3 cell_24_114_3
  | exact S 24 114 4 cell_24_114_4
  | exact S 24 114 5 cell_24_114_5
theorem cell_24_115_0 : C 24 115 0 := by decide +kernel
theorem cell_24_115_1 : C 24 115 1 := by decide +kernel
theorem cell_24_115_2 : C 24 115 2 := by decide +kernel
theorem cell_24_115_3 : C 24 115 3 := by decide +kernel
theorem cell_24_115_4 : C 24 115 4 := by decide +kernel
theorem cell_24_115_5 : C 24 115 5 := by decide +kernel
theorem row_24_115 : ThresholdAt 24 115 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 24 115 0 cell_24_115_0
  | exact S 24 115 1 cell_24_115_1
  | exact S 24 115 2 cell_24_115_2
  | exact S 24 115 3 cell_24_115_3
  | exact S 24 115 4 cell_24_115_4
  | exact S 24 115 5 cell_24_115_5
theorem checkedR24 : ∀ V ∈ List.range 116, ThresholdAt 24 V := by
  intro V hV
  have hv : V < 116 := List.mem_range.mp hV
  by_cases h0_116 : V < 58
  · by_cases h0_58 : V < 29
    · by_cases h0_29 : V < 14
      · by_cases h0_14 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have he : V = 0 := by omega
              subst V
              exact row_24_0
            · by_cases h1_3 : V < 2
              · have he : V = 1 := by omega
                subst V
                exact row_24_1
              · have he : V = 2 := by omega
                subst V
                exact row_24_2
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have he : V = 3 := by omega
                subst V
                exact row_24_3
              · have he : V = 4 := by omega
                subst V
                exact row_24_4
            · by_cases h5_7 : V < 6
              · have he : V = 5 := by omega
                subst V
                exact row_24_5
              · have he : V = 6 := by omega
                subst V
                exact row_24_6
        · by_cases h7_14 : V < 10
          · by_cases h7_10 : V < 8
            · have he : V = 7 := by omega
              subst V
              exact row_24_7
            · by_cases h8_10 : V < 9
              · have he : V = 8 := by omega
                subst V
                exact row_24_8
              · have he : V = 9 := by omega
                subst V
                exact row_24_9
          · by_cases h10_14 : V < 12
            · by_cases h10_12 : V < 11
              · have he : V = 10 := by omega
                subst V
                exact row_24_10
              · have he : V = 11 := by omega
                subst V
                exact row_24_11
            · by_cases h12_14 : V < 13
              · have he : V = 12 := by omega
                subst V
                exact row_24_12
              · have he : V = 13 := by omega
                subst V
                exact row_24_13
      · by_cases h14_29 : V < 21
        · by_cases h14_21 : V < 17
          · by_cases h14_17 : V < 15
            · have he : V = 14 := by omega
              subst V
              exact row_24_14
            · by_cases h15_17 : V < 16
              · have he : V = 15 := by omega
                subst V
                exact row_24_15
              · have he : V = 16 := by omega
                subst V
                exact row_24_16
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have he : V = 17 := by omega
                subst V
                exact row_24_17
              · have he : V = 18 := by omega
                subst V
                exact row_24_18
            · by_cases h19_21 : V < 20
              · have he : V = 19 := by omega
                subst V
                exact row_24_19
              · have he : V = 20 := by omega
                subst V
                exact row_24_20
        · by_cases h21_29 : V < 25
          · by_cases h21_25 : V < 23
            · by_cases h21_23 : V < 22
              · have he : V = 21 := by omega
                subst V
                exact row_24_21
              · have he : V = 22 := by omega
                subst V
                exact row_24_22
            · by_cases h23_25 : V < 24
              · have he : V = 23 := by omega
                subst V
                exact row_24_23
              · have he : V = 24 := by omega
                subst V
                exact row_24_24
          · by_cases h25_29 : V < 27
            · by_cases h25_27 : V < 26
              · have he : V = 25 := by omega
                subst V
                exact row_24_25
              · have he : V = 26 := by omega
                subst V
                exact row_24_26
            · by_cases h27_29 : V < 28
              · have he : V = 27 := by omega
                subst V
                exact row_24_27
              · have he : V = 28 := by omega
                subst V
                exact row_24_28
    · by_cases h29_58 : V < 43
      · by_cases h29_43 : V < 36
        · by_cases h29_36 : V < 32
          · by_cases h29_32 : V < 30
            · have he : V = 29 := by omega
              subst V
              exact row_24_29
            · by_cases h30_32 : V < 31
              · have he : V = 30 := by omega
                subst V
                exact row_24_30
              · have he : V = 31 := by omega
                subst V
                exact row_24_31
          · by_cases h32_36 : V < 34
            · by_cases h32_34 : V < 33
              · have he : V = 32 := by omega
                subst V
                exact row_24_32
              · have he : V = 33 := by omega
                subst V
                exact row_24_33
            · by_cases h34_36 : V < 35
              · have he : V = 34 := by omega
                subst V
                exact row_24_34
              · have he : V = 35 := by omega
                subst V
                exact row_24_35
        · by_cases h36_43 : V < 39
          · by_cases h36_39 : V < 37
            · have he : V = 36 := by omega
              subst V
              exact row_24_36
            · by_cases h37_39 : V < 38
              · have he : V = 37 := by omega
                subst V
                exact row_24_37
              · have he : V = 38 := by omega
                subst V
                exact row_24_38
          · by_cases h39_43 : V < 41
            · by_cases h39_41 : V < 40
              · have he : V = 39 := by omega
                subst V
                exact row_24_39
              · have he : V = 40 := by omega
                subst V
                exact row_24_40
            · by_cases h41_43 : V < 42
              · have he : V = 41 := by omega
                subst V
                exact row_24_41
              · have he : V = 42 := by omega
                subst V
                exact row_24_42
      · by_cases h43_58 : V < 50
        · by_cases h43_50 : V < 46
          · by_cases h43_46 : V < 44
            · have he : V = 43 := by omega
              subst V
              exact row_24_43
            · by_cases h44_46 : V < 45
              · have he : V = 44 := by omega
                subst V
                exact row_24_44
              · have he : V = 45 := by omega
                subst V
                exact row_24_45
          · by_cases h46_50 : V < 48
            · by_cases h46_48 : V < 47
              · have he : V = 46 := by omega
                subst V
                exact row_24_46
              · have he : V = 47 := by omega
                subst V
                exact row_24_47
            · by_cases h48_50 : V < 49
              · have he : V = 48 := by omega
                subst V
                exact row_24_48
              · have he : V = 49 := by omega
                subst V
                exact row_24_49
        · by_cases h50_58 : V < 54
          · by_cases h50_54 : V < 52
            · by_cases h50_52 : V < 51
              · have he : V = 50 := by omega
                subst V
                exact row_24_50
              · have he : V = 51 := by omega
                subst V
                exact row_24_51
            · by_cases h52_54 : V < 53
              · have he : V = 52 := by omega
                subst V
                exact row_24_52
              · have he : V = 53 := by omega
                subst V
                exact row_24_53
          · by_cases h54_58 : V < 56
            · by_cases h54_56 : V < 55
              · have he : V = 54 := by omega
                subst V
                exact row_24_54
              · have he : V = 55 := by omega
                subst V
                exact row_24_55
            · by_cases h56_58 : V < 57
              · have he : V = 56 := by omega
                subst V
                exact row_24_56
              · have he : V = 57 := by omega
                subst V
                exact row_24_57
  · by_cases h58_116 : V < 87
    · by_cases h58_87 : V < 72
      · by_cases h58_72 : V < 65
        · by_cases h58_65 : V < 61
          · by_cases h58_61 : V < 59
            · have he : V = 58 := by omega
              subst V
              exact row_24_58
            · by_cases h59_61 : V < 60
              · have he : V = 59 := by omega
                subst V
                exact row_24_59
              · have he : V = 60 := by omega
                subst V
                exact row_24_60
          · by_cases h61_65 : V < 63
            · by_cases h61_63 : V < 62
              · have he : V = 61 := by omega
                subst V
                exact row_24_61
              · have he : V = 62 := by omega
                subst V
                exact row_24_62
            · by_cases h63_65 : V < 64
              · have he : V = 63 := by omega
                subst V
                exact row_24_63
              · have he : V = 64 := by omega
                subst V
                exact row_24_64
        · by_cases h65_72 : V < 68
          · by_cases h65_68 : V < 66
            · have he : V = 65 := by omega
              subst V
              exact row_24_65
            · by_cases h66_68 : V < 67
              · have he : V = 66 := by omega
                subst V
                exact row_24_66
              · have he : V = 67 := by omega
                subst V
                exact row_24_67
          · by_cases h68_72 : V < 70
            · by_cases h68_70 : V < 69
              · have he : V = 68 := by omega
                subst V
                exact row_24_68
              · have he : V = 69 := by omega
                subst V
                exact row_24_69
            · by_cases h70_72 : V < 71
              · have he : V = 70 := by omega
                subst V
                exact row_24_70
              · have he : V = 71 := by omega
                subst V
                exact row_24_71
      · by_cases h72_87 : V < 79
        · by_cases h72_79 : V < 75
          · by_cases h72_75 : V < 73
            · have he : V = 72 := by omega
              subst V
              exact row_24_72
            · by_cases h73_75 : V < 74
              · have he : V = 73 := by omega
                subst V
                exact row_24_73
              · have he : V = 74 := by omega
                subst V
                exact row_24_74
          · by_cases h75_79 : V < 77
            · by_cases h75_77 : V < 76
              · have he : V = 75 := by omega
                subst V
                exact row_24_75
              · have he : V = 76 := by omega
                subst V
                exact row_24_76
            · by_cases h77_79 : V < 78
              · have he : V = 77 := by omega
                subst V
                exact row_24_77
              · have he : V = 78 := by omega
                subst V
                exact row_24_78
        · by_cases h79_87 : V < 83
          · by_cases h79_83 : V < 81
            · by_cases h79_81 : V < 80
              · have he : V = 79 := by omega
                subst V
                exact row_24_79
              · have he : V = 80 := by omega
                subst V
                exact row_24_80
            · by_cases h81_83 : V < 82
              · have he : V = 81 := by omega
                subst V
                exact row_24_81
              · have he : V = 82 := by omega
                subst V
                exact row_24_82
          · by_cases h83_87 : V < 85
            · by_cases h83_85 : V < 84
              · have he : V = 83 := by omega
                subst V
                exact row_24_83
              · have he : V = 84 := by omega
                subst V
                exact row_24_84
            · by_cases h85_87 : V < 86
              · have he : V = 85 := by omega
                subst V
                exact row_24_85
              · have he : V = 86 := by omega
                subst V
                exact row_24_86
    · by_cases h87_116 : V < 101
      · by_cases h87_101 : V < 94
        · by_cases h87_94 : V < 90
          · by_cases h87_90 : V < 88
            · have he : V = 87 := by omega
              subst V
              exact row_24_87
            · by_cases h88_90 : V < 89
              · have he : V = 88 := by omega
                subst V
                exact row_24_88
              · have he : V = 89 := by omega
                subst V
                exact row_24_89
          · by_cases h90_94 : V < 92
            · by_cases h90_92 : V < 91
              · have he : V = 90 := by omega
                subst V
                exact row_24_90
              · have he : V = 91 := by omega
                subst V
                exact row_24_91
            · by_cases h92_94 : V < 93
              · have he : V = 92 := by omega
                subst V
                exact row_24_92
              · have he : V = 93 := by omega
                subst V
                exact row_24_93
        · by_cases h94_101 : V < 97
          · by_cases h94_97 : V < 95
            · have he : V = 94 := by omega
              subst V
              exact row_24_94
            · by_cases h95_97 : V < 96
              · have he : V = 95 := by omega
                subst V
                exact row_24_95
              · have he : V = 96 := by omega
                subst V
                exact row_24_96
          · by_cases h97_101 : V < 99
            · by_cases h97_99 : V < 98
              · have he : V = 97 := by omega
                subst V
                exact row_24_97
              · have he : V = 98 := by omega
                subst V
                exact row_24_98
            · by_cases h99_101 : V < 100
              · have he : V = 99 := by omega
                subst V
                exact row_24_99
              · have he : V = 100 := by omega
                subst V
                exact row_24_100
      · by_cases h101_116 : V < 108
        · by_cases h101_108 : V < 104
          · by_cases h101_104 : V < 102
            · have he : V = 101 := by omega
              subst V
              exact row_24_101
            · by_cases h102_104 : V < 103
              · have he : V = 102 := by omega
                subst V
                exact row_24_102
              · have he : V = 103 := by omega
                subst V
                exact row_24_103
          · by_cases h104_108 : V < 106
            · by_cases h104_106 : V < 105
              · have he : V = 104 := by omega
                subst V
                exact row_24_104
              · have he : V = 105 := by omega
                subst V
                exact row_24_105
            · by_cases h106_108 : V < 107
              · have he : V = 106 := by omega
                subst V
                exact row_24_106
              · have he : V = 107 := by omega
                subst V
                exact row_24_107
        · by_cases h108_116 : V < 112
          · by_cases h108_112 : V < 110
            · by_cases h108_110 : V < 109
              · have he : V = 108 := by omega
                subst V
                exact row_24_108
              · have he : V = 109 := by omega
                subst V
                exact row_24_109
            · by_cases h110_112 : V < 111
              · have he : V = 110 := by omega
                subst V
                exact row_24_110
              · have he : V = 111 := by omega
                subst V
                exact row_24_111
          · by_cases h112_116 : V < 114
            · by_cases h112_114 : V < 113
              · have he : V = 112 := by omega
                subst V
                exact row_24_112
              · have he : V = 113 := by omega
                subst V
                exact row_24_113
            · by_cases h114_116 : V < 115
              · have he : V = 114 := by omega
                subst V
                exact row_24_114
              · have he : V = 115 := by omega
                subst V
                exact row_24_115
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
