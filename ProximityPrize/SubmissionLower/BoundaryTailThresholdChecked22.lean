import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked21

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_22_0_0 : C 22 0 0 := by decide +kernel
theorem cell_22_0_1 : C 22 0 1 := by decide +kernel
theorem cell_22_0_2 : C 22 0 2 := by decide +kernel
theorem cell_22_0_3 : C 22 0 3 := by decide +kernel
theorem cell_22_0_4 : C 22 0 4 := by decide +kernel
theorem cell_22_0_5 : C 22 0 5 := by decide +kernel
theorem row_22_0 : ThresholdAt 22 0 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 0 0 cell_22_0_0
  | exact S 22 0 1 cell_22_0_1
  | exact S 22 0 2 cell_22_0_2
  | exact S 22 0 3 cell_22_0_3
  | exact S 22 0 4 cell_22_0_4
  | exact S 22 0 5 cell_22_0_5
theorem cell_22_1_0 : C 22 1 0 := by decide +kernel
theorem cell_22_1_1 : C 22 1 1 := by decide +kernel
theorem cell_22_1_2 : C 22 1 2 := by decide +kernel
theorem cell_22_1_3 : C 22 1 3 := by decide +kernel
theorem cell_22_1_4 : C 22 1 4 := by decide +kernel
theorem cell_22_1_5 : C 22 1 5 := by decide +kernel
theorem row_22_1 : ThresholdAt 22 1 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 1 0 cell_22_1_0
  | exact S 22 1 1 cell_22_1_1
  | exact S 22 1 2 cell_22_1_2
  | exact S 22 1 3 cell_22_1_3
  | exact S 22 1 4 cell_22_1_4
  | exact S 22 1 5 cell_22_1_5
theorem cell_22_2_0 : C 22 2 0 := by decide +kernel
theorem cell_22_2_1 : C 22 2 1 := by decide +kernel
theorem cell_22_2_2 : C 22 2 2 := by decide +kernel
theorem cell_22_2_3 : C 22 2 3 := by decide +kernel
theorem cell_22_2_4 : C 22 2 4 := by decide +kernel
theorem cell_22_2_5 : C 22 2 5 := by decide +kernel
theorem row_22_2 : ThresholdAt 22 2 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 2 0 cell_22_2_0
  | exact S 22 2 1 cell_22_2_1
  | exact S 22 2 2 cell_22_2_2
  | exact S 22 2 3 cell_22_2_3
  | exact S 22 2 4 cell_22_2_4
  | exact S 22 2 5 cell_22_2_5
theorem cell_22_3_0 : C 22 3 0 := by decide +kernel
theorem cell_22_3_1 : C 22 3 1 := by decide +kernel
theorem cell_22_3_2 : C 22 3 2 := by decide +kernel
theorem cell_22_3_3 : C 22 3 3 := by decide +kernel
theorem cell_22_3_4 : C 22 3 4 := by decide +kernel
theorem cell_22_3_5 : C 22 3 5 := by decide +kernel
theorem row_22_3 : ThresholdAt 22 3 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 3 0 cell_22_3_0
  | exact S 22 3 1 cell_22_3_1
  | exact S 22 3 2 cell_22_3_2
  | exact S 22 3 3 cell_22_3_3
  | exact S 22 3 4 cell_22_3_4
  | exact S 22 3 5 cell_22_3_5
theorem cell_22_4_0 : C 22 4 0 := by decide +kernel
theorem cell_22_4_1 : C 22 4 1 := by decide +kernel
theorem cell_22_4_2 : C 22 4 2 := by decide +kernel
theorem cell_22_4_3 : C 22 4 3 := by decide +kernel
theorem cell_22_4_4 : C 22 4 4 := by decide +kernel
theorem cell_22_4_5 : C 22 4 5 := by decide +kernel
theorem row_22_4 : ThresholdAt 22 4 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 4 0 cell_22_4_0
  | exact S 22 4 1 cell_22_4_1
  | exact S 22 4 2 cell_22_4_2
  | exact S 22 4 3 cell_22_4_3
  | exact S 22 4 4 cell_22_4_4
  | exact S 22 4 5 cell_22_4_5
theorem cell_22_5_0 : C 22 5 0 := by decide +kernel
theorem cell_22_5_1 : C 22 5 1 := by decide +kernel
theorem cell_22_5_2 : C 22 5 2 := by decide +kernel
theorem cell_22_5_3 : C 22 5 3 := by decide +kernel
theorem cell_22_5_4 : C 22 5 4 := by decide +kernel
theorem cell_22_5_5 : C 22 5 5 := by decide +kernel
theorem row_22_5 : ThresholdAt 22 5 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 5 0 cell_22_5_0
  | exact S 22 5 1 cell_22_5_1
  | exact S 22 5 2 cell_22_5_2
  | exact S 22 5 3 cell_22_5_3
  | exact S 22 5 4 cell_22_5_4
  | exact S 22 5 5 cell_22_5_5
theorem cell_22_6_0 : C 22 6 0 := by decide +kernel
theorem cell_22_6_1 : C 22 6 1 := by decide +kernel
theorem cell_22_6_2 : C 22 6 2 := by decide +kernel
theorem cell_22_6_3 : C 22 6 3 := by decide +kernel
theorem cell_22_6_4 : C 22 6 4 := by decide +kernel
theorem cell_22_6_5 : C 22 6 5 := by decide +kernel
theorem row_22_6 : ThresholdAt 22 6 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 6 0 cell_22_6_0
  | exact S 22 6 1 cell_22_6_1
  | exact S 22 6 2 cell_22_6_2
  | exact S 22 6 3 cell_22_6_3
  | exact S 22 6 4 cell_22_6_4
  | exact S 22 6 5 cell_22_6_5
theorem cell_22_7_0 : C 22 7 0 := by decide +kernel
theorem cell_22_7_1 : C 22 7 1 := by decide +kernel
theorem cell_22_7_2 : C 22 7 2 := by decide +kernel
theorem cell_22_7_3 : C 22 7 3 := by decide +kernel
theorem cell_22_7_4 : C 22 7 4 := by decide +kernel
theorem cell_22_7_5 : C 22 7 5 := by decide +kernel
theorem row_22_7 : ThresholdAt 22 7 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 7 0 cell_22_7_0
  | exact S 22 7 1 cell_22_7_1
  | exact S 22 7 2 cell_22_7_2
  | exact S 22 7 3 cell_22_7_3
  | exact S 22 7 4 cell_22_7_4
  | exact S 22 7 5 cell_22_7_5
theorem cell_22_8_0 : C 22 8 0 := by decide +kernel
theorem cell_22_8_1 : C 22 8 1 := by decide +kernel
theorem cell_22_8_2 : C 22 8 2 := by decide +kernel
theorem cell_22_8_3 : C 22 8 3 := by decide +kernel
theorem cell_22_8_4 : C 22 8 4 := by decide +kernel
theorem cell_22_8_5 : C 22 8 5 := by decide +kernel
theorem row_22_8 : ThresholdAt 22 8 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 8 0 cell_22_8_0
  | exact S 22 8 1 cell_22_8_1
  | exact S 22 8 2 cell_22_8_2
  | exact S 22 8 3 cell_22_8_3
  | exact S 22 8 4 cell_22_8_4
  | exact S 22 8 5 cell_22_8_5
theorem cell_22_9_0 : C 22 9 0 := by decide +kernel
theorem cell_22_9_1 : C 22 9 1 := by decide +kernel
theorem cell_22_9_2 : C 22 9 2 := by decide +kernel
theorem cell_22_9_3 : C 22 9 3 := by decide +kernel
theorem cell_22_9_4 : C 22 9 4 := by decide +kernel
theorem cell_22_9_5 : C 22 9 5 := by decide +kernel
theorem row_22_9 : ThresholdAt 22 9 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 9 0 cell_22_9_0
  | exact S 22 9 1 cell_22_9_1
  | exact S 22 9 2 cell_22_9_2
  | exact S 22 9 3 cell_22_9_3
  | exact S 22 9 4 cell_22_9_4
  | exact S 22 9 5 cell_22_9_5
theorem cell_22_10_0 : C 22 10 0 := by decide +kernel
theorem cell_22_10_1 : C 22 10 1 := by decide +kernel
theorem cell_22_10_2 : C 22 10 2 := by decide +kernel
theorem cell_22_10_3 : C 22 10 3 := by decide +kernel
theorem cell_22_10_4 : C 22 10 4 := by decide +kernel
theorem cell_22_10_5 : C 22 10 5 := by decide +kernel
theorem row_22_10 : ThresholdAt 22 10 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 10 0 cell_22_10_0
  | exact S 22 10 1 cell_22_10_1
  | exact S 22 10 2 cell_22_10_2
  | exact S 22 10 3 cell_22_10_3
  | exact S 22 10 4 cell_22_10_4
  | exact S 22 10 5 cell_22_10_5
theorem cell_22_11_0 : C 22 11 0 := by decide +kernel
theorem cell_22_11_1 : C 22 11 1 := by decide +kernel
theorem cell_22_11_2 : C 22 11 2 := by decide +kernel
theorem cell_22_11_3 : C 22 11 3 := by decide +kernel
theorem cell_22_11_4 : C 22 11 4 := by decide +kernel
theorem cell_22_11_5 : C 22 11 5 := by decide +kernel
theorem row_22_11 : ThresholdAt 22 11 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 11 0 cell_22_11_0
  | exact S 22 11 1 cell_22_11_1
  | exact S 22 11 2 cell_22_11_2
  | exact S 22 11 3 cell_22_11_3
  | exact S 22 11 4 cell_22_11_4
  | exact S 22 11 5 cell_22_11_5
theorem cell_22_12_0 : C 22 12 0 := by decide +kernel
theorem cell_22_12_1 : C 22 12 1 := by decide +kernel
theorem cell_22_12_2 : C 22 12 2 := by decide +kernel
theorem cell_22_12_3 : C 22 12 3 := by decide +kernel
theorem cell_22_12_4 : C 22 12 4 := by decide +kernel
theorem cell_22_12_5 : C 22 12 5 := by decide +kernel
theorem row_22_12 : ThresholdAt 22 12 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 12 0 cell_22_12_0
  | exact S 22 12 1 cell_22_12_1
  | exact S 22 12 2 cell_22_12_2
  | exact S 22 12 3 cell_22_12_3
  | exact S 22 12 4 cell_22_12_4
  | exact S 22 12 5 cell_22_12_5
theorem cell_22_13_0 : C 22 13 0 := by decide +kernel
theorem cell_22_13_1 : C 22 13 1 := by decide +kernel
theorem cell_22_13_2 : C 22 13 2 := by decide +kernel
theorem cell_22_13_3 : C 22 13 3 := by decide +kernel
theorem cell_22_13_4 : C 22 13 4 := by decide +kernel
theorem cell_22_13_5 : C 22 13 5 := by decide +kernel
theorem row_22_13 : ThresholdAt 22 13 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 13 0 cell_22_13_0
  | exact S 22 13 1 cell_22_13_1
  | exact S 22 13 2 cell_22_13_2
  | exact S 22 13 3 cell_22_13_3
  | exact S 22 13 4 cell_22_13_4
  | exact S 22 13 5 cell_22_13_5
theorem cell_22_14_0 : C 22 14 0 := by decide +kernel
theorem cell_22_14_1 : C 22 14 1 := by decide +kernel
theorem cell_22_14_2 : C 22 14 2 := by decide +kernel
theorem cell_22_14_3 : C 22 14 3 := by decide +kernel
theorem cell_22_14_4 : C 22 14 4 := by decide +kernel
theorem cell_22_14_5 : C 22 14 5 := by decide +kernel
theorem row_22_14 : ThresholdAt 22 14 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 14 0 cell_22_14_0
  | exact S 22 14 1 cell_22_14_1
  | exact S 22 14 2 cell_22_14_2
  | exact S 22 14 3 cell_22_14_3
  | exact S 22 14 4 cell_22_14_4
  | exact S 22 14 5 cell_22_14_5
theorem cell_22_15_0 : C 22 15 0 := by decide +kernel
theorem cell_22_15_1 : C 22 15 1 := by decide +kernel
theorem cell_22_15_2 : C 22 15 2 := by decide +kernel
theorem cell_22_15_3 : C 22 15 3 := by decide +kernel
theorem cell_22_15_4 : C 22 15 4 := by decide +kernel
theorem cell_22_15_5 : C 22 15 5 := by decide +kernel
theorem row_22_15 : ThresholdAt 22 15 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 15 0 cell_22_15_0
  | exact S 22 15 1 cell_22_15_1
  | exact S 22 15 2 cell_22_15_2
  | exact S 22 15 3 cell_22_15_3
  | exact S 22 15 4 cell_22_15_4
  | exact S 22 15 5 cell_22_15_5
theorem cell_22_16_0 : C 22 16 0 := by decide +kernel
theorem cell_22_16_1 : C 22 16 1 := by decide +kernel
theorem cell_22_16_2 : C 22 16 2 := by decide +kernel
theorem cell_22_16_3 : C 22 16 3 := by decide +kernel
theorem cell_22_16_4 : C 22 16 4 := by decide +kernel
theorem cell_22_16_5 : C 22 16 5 := by decide +kernel
theorem row_22_16 : ThresholdAt 22 16 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 16 0 cell_22_16_0
  | exact S 22 16 1 cell_22_16_1
  | exact S 22 16 2 cell_22_16_2
  | exact S 22 16 3 cell_22_16_3
  | exact S 22 16 4 cell_22_16_4
  | exact S 22 16 5 cell_22_16_5
theorem cell_22_17_0 : C 22 17 0 := by decide +kernel
theorem cell_22_17_1 : C 22 17 1 := by decide +kernel
theorem cell_22_17_2 : C 22 17 2 := by decide +kernel
theorem cell_22_17_3 : C 22 17 3 := by decide +kernel
theorem cell_22_17_4 : C 22 17 4 := by decide +kernel
theorem cell_22_17_5 : C 22 17 5 := by decide +kernel
theorem row_22_17 : ThresholdAt 22 17 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 17 0 cell_22_17_0
  | exact S 22 17 1 cell_22_17_1
  | exact S 22 17 2 cell_22_17_2
  | exact S 22 17 3 cell_22_17_3
  | exact S 22 17 4 cell_22_17_4
  | exact S 22 17 5 cell_22_17_5
theorem cell_22_18_0 : C 22 18 0 := by decide +kernel
theorem cell_22_18_1 : C 22 18 1 := by decide +kernel
theorem cell_22_18_2 : C 22 18 2 := by decide +kernel
theorem cell_22_18_3 : C 22 18 3 := by decide +kernel
theorem cell_22_18_4 : C 22 18 4 := by decide +kernel
theorem cell_22_18_5 : C 22 18 5 := by decide +kernel
theorem row_22_18 : ThresholdAt 22 18 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 18 0 cell_22_18_0
  | exact S 22 18 1 cell_22_18_1
  | exact S 22 18 2 cell_22_18_2
  | exact S 22 18 3 cell_22_18_3
  | exact S 22 18 4 cell_22_18_4
  | exact S 22 18 5 cell_22_18_5
theorem cell_22_19_0 : C 22 19 0 := by decide +kernel
theorem cell_22_19_1 : C 22 19 1 := by decide +kernel
theorem cell_22_19_2 : C 22 19 2 := by decide +kernel
theorem cell_22_19_3 : C 22 19 3 := by decide +kernel
theorem cell_22_19_4 : C 22 19 4 := by decide +kernel
theorem cell_22_19_5 : C 22 19 5 := by decide +kernel
theorem row_22_19 : ThresholdAt 22 19 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 19 0 cell_22_19_0
  | exact S 22 19 1 cell_22_19_1
  | exact S 22 19 2 cell_22_19_2
  | exact S 22 19 3 cell_22_19_3
  | exact S 22 19 4 cell_22_19_4
  | exact S 22 19 5 cell_22_19_5
theorem cell_22_20_0 : C 22 20 0 := by decide +kernel
theorem cell_22_20_1 : C 22 20 1 := by decide +kernel
theorem cell_22_20_2 : C 22 20 2 := by decide +kernel
theorem cell_22_20_3 : C 22 20 3 := by decide +kernel
theorem cell_22_20_4 : C 22 20 4 := by decide +kernel
theorem cell_22_20_5 : C 22 20 5 := by decide +kernel
theorem row_22_20 : ThresholdAt 22 20 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 20 0 cell_22_20_0
  | exact S 22 20 1 cell_22_20_1
  | exact S 22 20 2 cell_22_20_2
  | exact S 22 20 3 cell_22_20_3
  | exact S 22 20 4 cell_22_20_4
  | exact S 22 20 5 cell_22_20_5
theorem cell_22_21_0 : C 22 21 0 := by decide +kernel
theorem cell_22_21_1 : C 22 21 1 := by decide +kernel
theorem cell_22_21_2 : C 22 21 2 := by decide +kernel
theorem cell_22_21_3 : C 22 21 3 := by decide +kernel
theorem cell_22_21_4 : C 22 21 4 := by decide +kernel
theorem cell_22_21_5 : C 22 21 5 := by decide +kernel
theorem row_22_21 : ThresholdAt 22 21 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 21 0 cell_22_21_0
  | exact S 22 21 1 cell_22_21_1
  | exact S 22 21 2 cell_22_21_2
  | exact S 22 21 3 cell_22_21_3
  | exact S 22 21 4 cell_22_21_4
  | exact S 22 21 5 cell_22_21_5
theorem cell_22_22_0 : C 22 22 0 := by decide +kernel
theorem cell_22_22_1 : C 22 22 1 := by decide +kernel
theorem cell_22_22_2 : C 22 22 2 := by decide +kernel
theorem cell_22_22_3 : C 22 22 3 := by decide +kernel
theorem cell_22_22_4 : C 22 22 4 := by decide +kernel
theorem cell_22_22_5 : C 22 22 5 := by decide +kernel
theorem row_22_22 : ThresholdAt 22 22 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 22 0 cell_22_22_0
  | exact S 22 22 1 cell_22_22_1
  | exact S 22 22 2 cell_22_22_2
  | exact S 22 22 3 cell_22_22_3
  | exact S 22 22 4 cell_22_22_4
  | exact S 22 22 5 cell_22_22_5
theorem cell_22_23_0 : C 22 23 0 := by decide +kernel
theorem cell_22_23_1 : C 22 23 1 := by decide +kernel
theorem cell_22_23_2 : C 22 23 2 := by decide +kernel
theorem cell_22_23_3 : C 22 23 3 := by decide +kernel
theorem cell_22_23_4 : C 22 23 4 := by decide +kernel
theorem cell_22_23_5 : C 22 23 5 := by decide +kernel
theorem row_22_23 : ThresholdAt 22 23 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 23 0 cell_22_23_0
  | exact S 22 23 1 cell_22_23_1
  | exact S 22 23 2 cell_22_23_2
  | exact S 22 23 3 cell_22_23_3
  | exact S 22 23 4 cell_22_23_4
  | exact S 22 23 5 cell_22_23_5
theorem cell_22_24_0 : C 22 24 0 := by decide +kernel
theorem cell_22_24_1 : C 22 24 1 := by decide +kernel
theorem cell_22_24_2 : C 22 24 2 := by decide +kernel
theorem cell_22_24_3 : C 22 24 3 := by decide +kernel
theorem cell_22_24_4 : C 22 24 4 := by decide +kernel
theorem cell_22_24_5 : C 22 24 5 := by decide +kernel
theorem row_22_24 : ThresholdAt 22 24 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 24 0 cell_22_24_0
  | exact S 22 24 1 cell_22_24_1
  | exact S 22 24 2 cell_22_24_2
  | exact S 22 24 3 cell_22_24_3
  | exact S 22 24 4 cell_22_24_4
  | exact S 22 24 5 cell_22_24_5
theorem cell_22_25_0 : C 22 25 0 := by decide +kernel
theorem cell_22_25_1 : C 22 25 1 := by decide +kernel
theorem cell_22_25_2 : C 22 25 2 := by decide +kernel
theorem cell_22_25_3 : C 22 25 3 := by decide +kernel
theorem cell_22_25_4 : C 22 25 4 := by decide +kernel
theorem cell_22_25_5 : C 22 25 5 := by decide +kernel
theorem row_22_25 : ThresholdAt 22 25 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 25 0 cell_22_25_0
  | exact S 22 25 1 cell_22_25_1
  | exact S 22 25 2 cell_22_25_2
  | exact S 22 25 3 cell_22_25_3
  | exact S 22 25 4 cell_22_25_4
  | exact S 22 25 5 cell_22_25_5
theorem cell_22_26_0 : C 22 26 0 := by decide +kernel
theorem cell_22_26_1 : C 22 26 1 := by decide +kernel
theorem cell_22_26_2 : C 22 26 2 := by decide +kernel
theorem cell_22_26_3 : C 22 26 3 := by decide +kernel
theorem cell_22_26_4 : C 22 26 4 := by decide +kernel
theorem cell_22_26_5 : C 22 26 5 := by decide +kernel
theorem row_22_26 : ThresholdAt 22 26 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 26 0 cell_22_26_0
  | exact S 22 26 1 cell_22_26_1
  | exact S 22 26 2 cell_22_26_2
  | exact S 22 26 3 cell_22_26_3
  | exact S 22 26 4 cell_22_26_4
  | exact S 22 26 5 cell_22_26_5
theorem cell_22_27_0 : C 22 27 0 := by decide +kernel
theorem cell_22_27_1 : C 22 27 1 := by decide +kernel
theorem cell_22_27_2 : C 22 27 2 := by decide +kernel
theorem cell_22_27_3 : C 22 27 3 := by decide +kernel
theorem cell_22_27_4 : C 22 27 4 := by decide +kernel
theorem cell_22_27_5 : C 22 27 5 := by decide +kernel
theorem row_22_27 : ThresholdAt 22 27 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 27 0 cell_22_27_0
  | exact S 22 27 1 cell_22_27_1
  | exact S 22 27 2 cell_22_27_2
  | exact S 22 27 3 cell_22_27_3
  | exact S 22 27 4 cell_22_27_4
  | exact S 22 27 5 cell_22_27_5
theorem cell_22_28_0 : C 22 28 0 := by decide +kernel
theorem cell_22_28_1 : C 22 28 1 := by decide +kernel
theorem cell_22_28_2 : C 22 28 2 := by decide +kernel
theorem cell_22_28_3 : C 22 28 3 := by decide +kernel
theorem cell_22_28_4 : C 22 28 4 := by decide +kernel
theorem cell_22_28_5 : C 22 28 5 := by decide +kernel
theorem row_22_28 : ThresholdAt 22 28 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 28 0 cell_22_28_0
  | exact S 22 28 1 cell_22_28_1
  | exact S 22 28 2 cell_22_28_2
  | exact S 22 28 3 cell_22_28_3
  | exact S 22 28 4 cell_22_28_4
  | exact S 22 28 5 cell_22_28_5
theorem cell_22_29_0 : C 22 29 0 := by decide +kernel
theorem cell_22_29_1 : C 22 29 1 := by decide +kernel
theorem cell_22_29_2 : C 22 29 2 := by decide +kernel
theorem cell_22_29_3 : C 22 29 3 := by decide +kernel
theorem cell_22_29_4 : C 22 29 4 := by decide +kernel
theorem cell_22_29_5 : C 22 29 5 := by decide +kernel
theorem row_22_29 : ThresholdAt 22 29 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 29 0 cell_22_29_0
  | exact S 22 29 1 cell_22_29_1
  | exact S 22 29 2 cell_22_29_2
  | exact S 22 29 3 cell_22_29_3
  | exact S 22 29 4 cell_22_29_4
  | exact S 22 29 5 cell_22_29_5
theorem cell_22_30_0 : C 22 30 0 := by decide +kernel
theorem cell_22_30_1 : C 22 30 1 := by decide +kernel
theorem cell_22_30_2 : C 22 30 2 := by decide +kernel
theorem cell_22_30_3 : C 22 30 3 := by decide +kernel
theorem cell_22_30_4 : C 22 30 4 := by decide +kernel
theorem cell_22_30_5 : C 22 30 5 := by decide +kernel
theorem row_22_30 : ThresholdAt 22 30 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 30 0 cell_22_30_0
  | exact S 22 30 1 cell_22_30_1
  | exact S 22 30 2 cell_22_30_2
  | exact S 22 30 3 cell_22_30_3
  | exact S 22 30 4 cell_22_30_4
  | exact S 22 30 5 cell_22_30_5
theorem cell_22_31_0 : C 22 31 0 := by decide +kernel
theorem cell_22_31_1 : C 22 31 1 := by decide +kernel
theorem cell_22_31_2 : C 22 31 2 := by decide +kernel
theorem cell_22_31_3 : C 22 31 3 := by decide +kernel
theorem cell_22_31_4 : C 22 31 4 := by decide +kernel
theorem cell_22_31_5 : C 22 31 5 := by decide +kernel
theorem row_22_31 : ThresholdAt 22 31 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 31 0 cell_22_31_0
  | exact S 22 31 1 cell_22_31_1
  | exact S 22 31 2 cell_22_31_2
  | exact S 22 31 3 cell_22_31_3
  | exact S 22 31 4 cell_22_31_4
  | exact S 22 31 5 cell_22_31_5
theorem cell_22_32_0 : C 22 32 0 := by decide +kernel
theorem cell_22_32_1 : C 22 32 1 := by decide +kernel
theorem cell_22_32_2 : C 22 32 2 := by decide +kernel
theorem cell_22_32_3 : C 22 32 3 := by decide +kernel
theorem cell_22_32_4 : C 22 32 4 := by decide +kernel
theorem cell_22_32_5 : C 22 32 5 := by decide +kernel
theorem row_22_32 : ThresholdAt 22 32 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 32 0 cell_22_32_0
  | exact S 22 32 1 cell_22_32_1
  | exact S 22 32 2 cell_22_32_2
  | exact S 22 32 3 cell_22_32_3
  | exact S 22 32 4 cell_22_32_4
  | exact S 22 32 5 cell_22_32_5
theorem cell_22_33_0 : C 22 33 0 := by decide +kernel
theorem cell_22_33_1 : C 22 33 1 := by decide +kernel
theorem cell_22_33_2 : C 22 33 2 := by decide +kernel
theorem cell_22_33_3 : C 22 33 3 := by decide +kernel
theorem cell_22_33_4 : C 22 33 4 := by decide +kernel
theorem cell_22_33_5 : C 22 33 5 := by decide +kernel
theorem row_22_33 : ThresholdAt 22 33 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 33 0 cell_22_33_0
  | exact S 22 33 1 cell_22_33_1
  | exact S 22 33 2 cell_22_33_2
  | exact S 22 33 3 cell_22_33_3
  | exact S 22 33 4 cell_22_33_4
  | exact S 22 33 5 cell_22_33_5
theorem cell_22_34_0 : C 22 34 0 := by decide +kernel
theorem cell_22_34_1 : C 22 34 1 := by decide +kernel
theorem cell_22_34_2 : C 22 34 2 := by decide +kernel
theorem cell_22_34_3 : C 22 34 3 := by decide +kernel
theorem cell_22_34_4 : C 22 34 4 := by decide +kernel
theorem cell_22_34_5 : C 22 34 5 := by decide +kernel
theorem row_22_34 : ThresholdAt 22 34 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 34 0 cell_22_34_0
  | exact S 22 34 1 cell_22_34_1
  | exact S 22 34 2 cell_22_34_2
  | exact S 22 34 3 cell_22_34_3
  | exact S 22 34 4 cell_22_34_4
  | exact S 22 34 5 cell_22_34_5
theorem cell_22_35_0 : C 22 35 0 := by decide +kernel
theorem cell_22_35_1 : C 22 35 1 := by decide +kernel
theorem cell_22_35_2 : C 22 35 2 := by decide +kernel
theorem cell_22_35_3 : C 22 35 3 := by decide +kernel
theorem cell_22_35_4 : C 22 35 4 := by decide +kernel
theorem cell_22_35_5 : C 22 35 5 := by decide +kernel
theorem row_22_35 : ThresholdAt 22 35 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 35 0 cell_22_35_0
  | exact S 22 35 1 cell_22_35_1
  | exact S 22 35 2 cell_22_35_2
  | exact S 22 35 3 cell_22_35_3
  | exact S 22 35 4 cell_22_35_4
  | exact S 22 35 5 cell_22_35_5
theorem cell_22_36_0 : C 22 36 0 := by decide +kernel
theorem cell_22_36_1 : C 22 36 1 := by decide +kernel
theorem cell_22_36_2 : C 22 36 2 := by decide +kernel
theorem cell_22_36_3 : C 22 36 3 := by decide +kernel
theorem cell_22_36_4 : C 22 36 4 := by decide +kernel
theorem cell_22_36_5 : C 22 36 5 := by decide +kernel
theorem row_22_36 : ThresholdAt 22 36 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 36 0 cell_22_36_0
  | exact S 22 36 1 cell_22_36_1
  | exact S 22 36 2 cell_22_36_2
  | exact S 22 36 3 cell_22_36_3
  | exact S 22 36 4 cell_22_36_4
  | exact S 22 36 5 cell_22_36_5
theorem cell_22_37_0 : C 22 37 0 := by decide +kernel
theorem cell_22_37_1 : C 22 37 1 := by decide +kernel
theorem cell_22_37_2 : C 22 37 2 := by decide +kernel
theorem cell_22_37_3 : C 22 37 3 := by decide +kernel
theorem cell_22_37_4 : C 22 37 4 := by decide +kernel
theorem cell_22_37_5 : C 22 37 5 := by decide +kernel
theorem row_22_37 : ThresholdAt 22 37 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 37 0 cell_22_37_0
  | exact S 22 37 1 cell_22_37_1
  | exact S 22 37 2 cell_22_37_2
  | exact S 22 37 3 cell_22_37_3
  | exact S 22 37 4 cell_22_37_4
  | exact S 22 37 5 cell_22_37_5
theorem cell_22_38_0 : C 22 38 0 := by decide +kernel
theorem cell_22_38_1 : C 22 38 1 := by decide +kernel
theorem cell_22_38_2 : C 22 38 2 := by decide +kernel
theorem cell_22_38_3 : C 22 38 3 := by decide +kernel
theorem cell_22_38_4 : C 22 38 4 := by decide +kernel
theorem cell_22_38_5 : C 22 38 5 := by decide +kernel
theorem row_22_38 : ThresholdAt 22 38 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 38 0 cell_22_38_0
  | exact S 22 38 1 cell_22_38_1
  | exact S 22 38 2 cell_22_38_2
  | exact S 22 38 3 cell_22_38_3
  | exact S 22 38 4 cell_22_38_4
  | exact S 22 38 5 cell_22_38_5
theorem cell_22_39_0 : C 22 39 0 := by decide +kernel
theorem cell_22_39_1 : C 22 39 1 := by decide +kernel
theorem cell_22_39_2 : C 22 39 2 := by decide +kernel
theorem cell_22_39_3 : C 22 39 3 := by decide +kernel
theorem cell_22_39_4 : C 22 39 4 := by decide +kernel
theorem cell_22_39_5 : C 22 39 5 := by decide +kernel
theorem row_22_39 : ThresholdAt 22 39 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 39 0 cell_22_39_0
  | exact S 22 39 1 cell_22_39_1
  | exact S 22 39 2 cell_22_39_2
  | exact S 22 39 3 cell_22_39_3
  | exact S 22 39 4 cell_22_39_4
  | exact S 22 39 5 cell_22_39_5
theorem cell_22_40_0 : C 22 40 0 := by decide +kernel
theorem cell_22_40_1 : C 22 40 1 := by decide +kernel
theorem cell_22_40_2 : C 22 40 2 := by decide +kernel
theorem cell_22_40_3 : C 22 40 3 := by decide +kernel
theorem cell_22_40_4 : C 22 40 4 := by decide +kernel
theorem cell_22_40_5 : C 22 40 5 := by decide +kernel
theorem row_22_40 : ThresholdAt 22 40 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 40 0 cell_22_40_0
  | exact S 22 40 1 cell_22_40_1
  | exact S 22 40 2 cell_22_40_2
  | exact S 22 40 3 cell_22_40_3
  | exact S 22 40 4 cell_22_40_4
  | exact S 22 40 5 cell_22_40_5
theorem cell_22_41_0 : C 22 41 0 := by decide +kernel
theorem cell_22_41_1 : C 22 41 1 := by decide +kernel
theorem cell_22_41_2 : C 22 41 2 := by decide +kernel
theorem cell_22_41_3 : C 22 41 3 := by decide +kernel
theorem cell_22_41_4 : C 22 41 4 := by decide +kernel
theorem cell_22_41_5 : C 22 41 5 := by decide +kernel
theorem row_22_41 : ThresholdAt 22 41 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 41 0 cell_22_41_0
  | exact S 22 41 1 cell_22_41_1
  | exact S 22 41 2 cell_22_41_2
  | exact S 22 41 3 cell_22_41_3
  | exact S 22 41 4 cell_22_41_4
  | exact S 22 41 5 cell_22_41_5
theorem cell_22_42_0 : C 22 42 0 := by decide +kernel
theorem cell_22_42_1 : C 22 42 1 := by decide +kernel
theorem cell_22_42_2 : C 22 42 2 := by decide +kernel
theorem cell_22_42_3 : C 22 42 3 := by decide +kernel
theorem cell_22_42_4 : C 22 42 4 := by decide +kernel
theorem cell_22_42_5 : C 22 42 5 := by decide +kernel
theorem row_22_42 : ThresholdAt 22 42 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 42 0 cell_22_42_0
  | exact S 22 42 1 cell_22_42_1
  | exact S 22 42 2 cell_22_42_2
  | exact S 22 42 3 cell_22_42_3
  | exact S 22 42 4 cell_22_42_4
  | exact S 22 42 5 cell_22_42_5
theorem cell_22_43_0 : C 22 43 0 := by decide +kernel
theorem cell_22_43_1 : C 22 43 1 := by decide +kernel
theorem cell_22_43_2 : C 22 43 2 := by decide +kernel
theorem cell_22_43_3 : C 22 43 3 := by decide +kernel
theorem cell_22_43_4 : C 22 43 4 := by decide +kernel
theorem cell_22_43_5 : C 22 43 5 := by decide +kernel
theorem row_22_43 : ThresholdAt 22 43 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 43 0 cell_22_43_0
  | exact S 22 43 1 cell_22_43_1
  | exact S 22 43 2 cell_22_43_2
  | exact S 22 43 3 cell_22_43_3
  | exact S 22 43 4 cell_22_43_4
  | exact S 22 43 5 cell_22_43_5
theorem cell_22_44_0 : C 22 44 0 := by decide +kernel
theorem cell_22_44_1 : C 22 44 1 := by decide +kernel
theorem cell_22_44_2 : C 22 44 2 := by decide +kernel
theorem cell_22_44_3 : C 22 44 3 := by decide +kernel
theorem cell_22_44_4 : C 22 44 4 := by decide +kernel
theorem cell_22_44_5 : C 22 44 5 := by decide +kernel
theorem row_22_44 : ThresholdAt 22 44 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 44 0 cell_22_44_0
  | exact S 22 44 1 cell_22_44_1
  | exact S 22 44 2 cell_22_44_2
  | exact S 22 44 3 cell_22_44_3
  | exact S 22 44 4 cell_22_44_4
  | exact S 22 44 5 cell_22_44_5
theorem cell_22_45_0 : C 22 45 0 := by decide +kernel
theorem cell_22_45_1 : C 22 45 1 := by decide +kernel
theorem cell_22_45_2 : C 22 45 2 := by decide +kernel
theorem cell_22_45_3 : C 22 45 3 := by decide +kernel
theorem cell_22_45_4 : C 22 45 4 := by decide +kernel
theorem cell_22_45_5 : C 22 45 5 := by decide +kernel
theorem row_22_45 : ThresholdAt 22 45 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 45 0 cell_22_45_0
  | exact S 22 45 1 cell_22_45_1
  | exact S 22 45 2 cell_22_45_2
  | exact S 22 45 3 cell_22_45_3
  | exact S 22 45 4 cell_22_45_4
  | exact S 22 45 5 cell_22_45_5
theorem cell_22_46_0 : C 22 46 0 := by decide +kernel
theorem cell_22_46_1 : C 22 46 1 := by decide +kernel
theorem cell_22_46_2 : C 22 46 2 := by decide +kernel
theorem cell_22_46_3 : C 22 46 3 := by decide +kernel
theorem cell_22_46_4 : C 22 46 4 := by decide +kernel
theorem cell_22_46_5 : C 22 46 5 := by decide +kernel
theorem row_22_46 : ThresholdAt 22 46 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 46 0 cell_22_46_0
  | exact S 22 46 1 cell_22_46_1
  | exact S 22 46 2 cell_22_46_2
  | exact S 22 46 3 cell_22_46_3
  | exact S 22 46 4 cell_22_46_4
  | exact S 22 46 5 cell_22_46_5
theorem cell_22_47_0 : C 22 47 0 := by decide +kernel
theorem cell_22_47_1 : C 22 47 1 := by decide +kernel
theorem cell_22_47_2 : C 22 47 2 := by decide +kernel
theorem cell_22_47_3 : C 22 47 3 := by decide +kernel
theorem cell_22_47_4 : C 22 47 4 := by decide +kernel
theorem cell_22_47_5 : C 22 47 5 := by decide +kernel
theorem row_22_47 : ThresholdAt 22 47 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 47 0 cell_22_47_0
  | exact S 22 47 1 cell_22_47_1
  | exact S 22 47 2 cell_22_47_2
  | exact S 22 47 3 cell_22_47_3
  | exact S 22 47 4 cell_22_47_4
  | exact S 22 47 5 cell_22_47_5
theorem cell_22_48_0 : C 22 48 0 := by decide +kernel
theorem cell_22_48_1 : C 22 48 1 := by decide +kernel
theorem cell_22_48_2 : C 22 48 2 := by decide +kernel
theorem cell_22_48_3 : C 22 48 3 := by decide +kernel
theorem cell_22_48_4 : C 22 48 4 := by decide +kernel
theorem cell_22_48_5 : C 22 48 5 := by decide +kernel
theorem row_22_48 : ThresholdAt 22 48 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 48 0 cell_22_48_0
  | exact S 22 48 1 cell_22_48_1
  | exact S 22 48 2 cell_22_48_2
  | exact S 22 48 3 cell_22_48_3
  | exact S 22 48 4 cell_22_48_4
  | exact S 22 48 5 cell_22_48_5
theorem cell_22_49_0 : C 22 49 0 := by decide +kernel
theorem cell_22_49_1 : C 22 49 1 := by decide +kernel
theorem cell_22_49_2 : C 22 49 2 := by decide +kernel
theorem cell_22_49_3 : C 22 49 3 := by decide +kernel
theorem cell_22_49_4 : C 22 49 4 := by decide +kernel
theorem cell_22_49_5 : C 22 49 5 := by decide +kernel
theorem row_22_49 : ThresholdAt 22 49 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 49 0 cell_22_49_0
  | exact S 22 49 1 cell_22_49_1
  | exact S 22 49 2 cell_22_49_2
  | exact S 22 49 3 cell_22_49_3
  | exact S 22 49 4 cell_22_49_4
  | exact S 22 49 5 cell_22_49_5
theorem cell_22_50_0 : C 22 50 0 := by decide +kernel
theorem cell_22_50_1 : C 22 50 1 := by decide +kernel
theorem cell_22_50_2 : C 22 50 2 := by decide +kernel
theorem cell_22_50_3 : C 22 50 3 := by decide +kernel
theorem cell_22_50_4 : C 22 50 4 := by decide +kernel
theorem cell_22_50_5 : C 22 50 5 := by decide +kernel
theorem row_22_50 : ThresholdAt 22 50 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 50 0 cell_22_50_0
  | exact S 22 50 1 cell_22_50_1
  | exact S 22 50 2 cell_22_50_2
  | exact S 22 50 3 cell_22_50_3
  | exact S 22 50 4 cell_22_50_4
  | exact S 22 50 5 cell_22_50_5
theorem cell_22_51_0 : C 22 51 0 := by decide +kernel
theorem cell_22_51_1 : C 22 51 1 := by decide +kernel
theorem cell_22_51_2 : C 22 51 2 := by decide +kernel
theorem cell_22_51_3 : C 22 51 3 := by decide +kernel
theorem cell_22_51_4 : C 22 51 4 := by decide +kernel
theorem cell_22_51_5 : C 22 51 5 := by decide +kernel
theorem row_22_51 : ThresholdAt 22 51 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 51 0 cell_22_51_0
  | exact S 22 51 1 cell_22_51_1
  | exact S 22 51 2 cell_22_51_2
  | exact S 22 51 3 cell_22_51_3
  | exact S 22 51 4 cell_22_51_4
  | exact S 22 51 5 cell_22_51_5
theorem cell_22_52_0 : C 22 52 0 := by decide +kernel
theorem cell_22_52_1 : C 22 52 1 := by decide +kernel
theorem cell_22_52_2 : C 22 52 2 := by decide +kernel
theorem cell_22_52_3 : C 22 52 3 := by decide +kernel
theorem cell_22_52_4 : C 22 52 4 := by decide +kernel
theorem cell_22_52_5 : C 22 52 5 := by decide +kernel
theorem row_22_52 : ThresholdAt 22 52 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 52 0 cell_22_52_0
  | exact S 22 52 1 cell_22_52_1
  | exact S 22 52 2 cell_22_52_2
  | exact S 22 52 3 cell_22_52_3
  | exact S 22 52 4 cell_22_52_4
  | exact S 22 52 5 cell_22_52_5
theorem cell_22_53_0 : C 22 53 0 := by decide +kernel
theorem cell_22_53_1 : C 22 53 1 := by decide +kernel
theorem cell_22_53_2 : C 22 53 2 := by decide +kernel
theorem cell_22_53_3 : C 22 53 3 := by decide +kernel
theorem cell_22_53_4 : C 22 53 4 := by decide +kernel
theorem cell_22_53_5 : C 22 53 5 := by decide +kernel
theorem row_22_53 : ThresholdAt 22 53 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 53 0 cell_22_53_0
  | exact S 22 53 1 cell_22_53_1
  | exact S 22 53 2 cell_22_53_2
  | exact S 22 53 3 cell_22_53_3
  | exact S 22 53 4 cell_22_53_4
  | exact S 22 53 5 cell_22_53_5
theorem cell_22_54_0 : C 22 54 0 := by decide +kernel
theorem cell_22_54_1 : C 22 54 1 := by decide +kernel
theorem cell_22_54_2 : C 22 54 2 := by decide +kernel
theorem cell_22_54_3 : C 22 54 3 := by decide +kernel
theorem cell_22_54_4 : C 22 54 4 := by decide +kernel
theorem cell_22_54_5 : C 22 54 5 := by decide +kernel
theorem row_22_54 : ThresholdAt 22 54 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 54 0 cell_22_54_0
  | exact S 22 54 1 cell_22_54_1
  | exact S 22 54 2 cell_22_54_2
  | exact S 22 54 3 cell_22_54_3
  | exact S 22 54 4 cell_22_54_4
  | exact S 22 54 5 cell_22_54_5
theorem cell_22_55_0 : C 22 55 0 := by decide +kernel
theorem cell_22_55_1 : C 22 55 1 := by decide +kernel
theorem cell_22_55_2 : C 22 55 2 := by decide +kernel
theorem cell_22_55_3 : C 22 55 3 := by decide +kernel
theorem cell_22_55_4 : C 22 55 4 := by decide +kernel
theorem cell_22_55_5 : C 22 55 5 := by decide +kernel
theorem row_22_55 : ThresholdAt 22 55 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 55 0 cell_22_55_0
  | exact S 22 55 1 cell_22_55_1
  | exact S 22 55 2 cell_22_55_2
  | exact S 22 55 3 cell_22_55_3
  | exact S 22 55 4 cell_22_55_4
  | exact S 22 55 5 cell_22_55_5
theorem cell_22_56_0 : C 22 56 0 := by decide +kernel
theorem cell_22_56_1 : C 22 56 1 := by decide +kernel
theorem cell_22_56_2 : C 22 56 2 := by decide +kernel
theorem cell_22_56_3 : C 22 56 3 := by decide +kernel
theorem cell_22_56_4 : C 22 56 4 := by decide +kernel
theorem cell_22_56_5 : C 22 56 5 := by decide +kernel
theorem row_22_56 : ThresholdAt 22 56 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 56 0 cell_22_56_0
  | exact S 22 56 1 cell_22_56_1
  | exact S 22 56 2 cell_22_56_2
  | exact S 22 56 3 cell_22_56_3
  | exact S 22 56 4 cell_22_56_4
  | exact S 22 56 5 cell_22_56_5
theorem cell_22_57_0 : C 22 57 0 := by decide +kernel
theorem cell_22_57_1 : C 22 57 1 := by decide +kernel
theorem cell_22_57_2 : C 22 57 2 := by decide +kernel
theorem cell_22_57_3 : C 22 57 3 := by decide +kernel
theorem cell_22_57_4 : C 22 57 4 := by decide +kernel
theorem cell_22_57_5 : C 22 57 5 := by decide +kernel
theorem row_22_57 : ThresholdAt 22 57 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 57 0 cell_22_57_0
  | exact S 22 57 1 cell_22_57_1
  | exact S 22 57 2 cell_22_57_2
  | exact S 22 57 3 cell_22_57_3
  | exact S 22 57 4 cell_22_57_4
  | exact S 22 57 5 cell_22_57_5
theorem cell_22_58_0 : C 22 58 0 := by decide +kernel
theorem cell_22_58_1 : C 22 58 1 := by decide +kernel
theorem cell_22_58_2 : C 22 58 2 := by decide +kernel
theorem cell_22_58_3 : C 22 58 3 := by decide +kernel
theorem cell_22_58_4 : C 22 58 4 := by decide +kernel
theorem cell_22_58_5 : C 22 58 5 := by decide +kernel
theorem row_22_58 : ThresholdAt 22 58 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 58 0 cell_22_58_0
  | exact S 22 58 1 cell_22_58_1
  | exact S 22 58 2 cell_22_58_2
  | exact S 22 58 3 cell_22_58_3
  | exact S 22 58 4 cell_22_58_4
  | exact S 22 58 5 cell_22_58_5
theorem cell_22_59_0 : C 22 59 0 := by decide +kernel
theorem cell_22_59_1 : C 22 59 1 := by decide +kernel
theorem cell_22_59_2 : C 22 59 2 := by decide +kernel
theorem cell_22_59_3 : C 22 59 3 := by decide +kernel
theorem cell_22_59_4 : C 22 59 4 := by decide +kernel
theorem cell_22_59_5 : C 22 59 5 := by decide +kernel
theorem row_22_59 : ThresholdAt 22 59 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 59 0 cell_22_59_0
  | exact S 22 59 1 cell_22_59_1
  | exact S 22 59 2 cell_22_59_2
  | exact S 22 59 3 cell_22_59_3
  | exact S 22 59 4 cell_22_59_4
  | exact S 22 59 5 cell_22_59_5
theorem cell_22_60_0 : C 22 60 0 := by decide +kernel
theorem cell_22_60_1 : C 22 60 1 := by decide +kernel
theorem cell_22_60_2 : C 22 60 2 := by decide +kernel
theorem cell_22_60_3 : C 22 60 3 := by decide +kernel
theorem cell_22_60_4 : C 22 60 4 := by decide +kernel
theorem cell_22_60_5 : C 22 60 5 := by decide +kernel
theorem row_22_60 : ThresholdAt 22 60 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 60 0 cell_22_60_0
  | exact S 22 60 1 cell_22_60_1
  | exact S 22 60 2 cell_22_60_2
  | exact S 22 60 3 cell_22_60_3
  | exact S 22 60 4 cell_22_60_4
  | exact S 22 60 5 cell_22_60_5
theorem cell_22_61_0 : C 22 61 0 := by decide +kernel
theorem cell_22_61_1 : C 22 61 1 := by decide +kernel
theorem cell_22_61_2 : C 22 61 2 := by decide +kernel
theorem cell_22_61_3 : C 22 61 3 := by decide +kernel
theorem cell_22_61_4 : C 22 61 4 := by decide +kernel
theorem cell_22_61_5 : C 22 61 5 := by decide +kernel
theorem row_22_61 : ThresholdAt 22 61 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 61 0 cell_22_61_0
  | exact S 22 61 1 cell_22_61_1
  | exact S 22 61 2 cell_22_61_2
  | exact S 22 61 3 cell_22_61_3
  | exact S 22 61 4 cell_22_61_4
  | exact S 22 61 5 cell_22_61_5
theorem cell_22_62_0 : C 22 62 0 := by decide +kernel
theorem cell_22_62_1 : C 22 62 1 := by decide +kernel
theorem cell_22_62_2 : C 22 62 2 := by decide +kernel
theorem cell_22_62_3 : C 22 62 3 := by decide +kernel
theorem cell_22_62_4 : C 22 62 4 := by decide +kernel
theorem cell_22_62_5 : C 22 62 5 := by decide +kernel
theorem row_22_62 : ThresholdAt 22 62 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 62 0 cell_22_62_0
  | exact S 22 62 1 cell_22_62_1
  | exact S 22 62 2 cell_22_62_2
  | exact S 22 62 3 cell_22_62_3
  | exact S 22 62 4 cell_22_62_4
  | exact S 22 62 5 cell_22_62_5
theorem cell_22_63_0 : C 22 63 0 := by decide +kernel
theorem cell_22_63_1 : C 22 63 1 := by decide +kernel
theorem cell_22_63_2 : C 22 63 2 := by decide +kernel
theorem cell_22_63_3 : C 22 63 3 := by decide +kernel
theorem cell_22_63_4 : C 22 63 4 := by decide +kernel
theorem cell_22_63_5 : C 22 63 5 := by decide +kernel
theorem row_22_63 : ThresholdAt 22 63 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 63 0 cell_22_63_0
  | exact S 22 63 1 cell_22_63_1
  | exact S 22 63 2 cell_22_63_2
  | exact S 22 63 3 cell_22_63_3
  | exact S 22 63 4 cell_22_63_4
  | exact S 22 63 5 cell_22_63_5
theorem cell_22_64_0 : C 22 64 0 := by decide +kernel
theorem cell_22_64_1 : C 22 64 1 := by decide +kernel
theorem cell_22_64_2 : C 22 64 2 := by decide +kernel
theorem cell_22_64_3 : C 22 64 3 := by decide +kernel
theorem cell_22_64_4 : C 22 64 4 := by decide +kernel
theorem cell_22_64_5 : C 22 64 5 := by decide +kernel
theorem row_22_64 : ThresholdAt 22 64 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 64 0 cell_22_64_0
  | exact S 22 64 1 cell_22_64_1
  | exact S 22 64 2 cell_22_64_2
  | exact S 22 64 3 cell_22_64_3
  | exact S 22 64 4 cell_22_64_4
  | exact S 22 64 5 cell_22_64_5
theorem cell_22_65_0 : C 22 65 0 := by decide +kernel
theorem cell_22_65_1 : C 22 65 1 := by decide +kernel
theorem cell_22_65_2 : C 22 65 2 := by decide +kernel
theorem cell_22_65_3 : C 22 65 3 := by decide +kernel
theorem cell_22_65_4 : C 22 65 4 := by decide +kernel
theorem cell_22_65_5 : C 22 65 5 := by decide +kernel
theorem row_22_65 : ThresholdAt 22 65 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 65 0 cell_22_65_0
  | exact S 22 65 1 cell_22_65_1
  | exact S 22 65 2 cell_22_65_2
  | exact S 22 65 3 cell_22_65_3
  | exact S 22 65 4 cell_22_65_4
  | exact S 22 65 5 cell_22_65_5
theorem cell_22_66_0 : C 22 66 0 := by decide +kernel
theorem cell_22_66_1 : C 22 66 1 := by decide +kernel
theorem cell_22_66_2 : C 22 66 2 := by decide +kernel
theorem cell_22_66_3 : C 22 66 3 := by decide +kernel
theorem cell_22_66_4 : C 22 66 4 := by decide +kernel
theorem cell_22_66_5 : C 22 66 5 := by decide +kernel
theorem row_22_66 : ThresholdAt 22 66 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 66 0 cell_22_66_0
  | exact S 22 66 1 cell_22_66_1
  | exact S 22 66 2 cell_22_66_2
  | exact S 22 66 3 cell_22_66_3
  | exact S 22 66 4 cell_22_66_4
  | exact S 22 66 5 cell_22_66_5
theorem cell_22_67_0 : C 22 67 0 := by decide +kernel
theorem cell_22_67_1 : C 22 67 1 := by decide +kernel
theorem cell_22_67_2 : C 22 67 2 := by decide +kernel
theorem cell_22_67_3 : C 22 67 3 := by decide +kernel
theorem cell_22_67_4 : C 22 67 4 := by decide +kernel
theorem cell_22_67_5 : C 22 67 5 := by decide +kernel
theorem row_22_67 : ThresholdAt 22 67 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 67 0 cell_22_67_0
  | exact S 22 67 1 cell_22_67_1
  | exact S 22 67 2 cell_22_67_2
  | exact S 22 67 3 cell_22_67_3
  | exact S 22 67 4 cell_22_67_4
  | exact S 22 67 5 cell_22_67_5
theorem cell_22_68_0 : C 22 68 0 := by decide +kernel
theorem cell_22_68_1 : C 22 68 1 := by decide +kernel
theorem cell_22_68_2 : C 22 68 2 := by decide +kernel
theorem cell_22_68_3 : C 22 68 3 := by decide +kernel
theorem cell_22_68_4 : C 22 68 4 := by decide +kernel
theorem cell_22_68_5 : C 22 68 5 := by decide +kernel
theorem row_22_68 : ThresholdAt 22 68 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 68 0 cell_22_68_0
  | exact S 22 68 1 cell_22_68_1
  | exact S 22 68 2 cell_22_68_2
  | exact S 22 68 3 cell_22_68_3
  | exact S 22 68 4 cell_22_68_4
  | exact S 22 68 5 cell_22_68_5
theorem cell_22_69_0 : C 22 69 0 := by decide +kernel
theorem cell_22_69_1 : C 22 69 1 := by decide +kernel
theorem cell_22_69_2 : C 22 69 2 := by decide +kernel
theorem cell_22_69_3 : C 22 69 3 := by decide +kernel
theorem cell_22_69_4 : C 22 69 4 := by decide +kernel
theorem cell_22_69_5 : C 22 69 5 := by decide +kernel
theorem row_22_69 : ThresholdAt 22 69 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 69 0 cell_22_69_0
  | exact S 22 69 1 cell_22_69_1
  | exact S 22 69 2 cell_22_69_2
  | exact S 22 69 3 cell_22_69_3
  | exact S 22 69 4 cell_22_69_4
  | exact S 22 69 5 cell_22_69_5
theorem cell_22_70_0 : C 22 70 0 := by decide +kernel
theorem cell_22_70_1 : C 22 70 1 := by decide +kernel
theorem cell_22_70_2 : C 22 70 2 := by decide +kernel
theorem cell_22_70_3 : C 22 70 3 := by decide +kernel
theorem cell_22_70_4 : C 22 70 4 := by decide +kernel
theorem cell_22_70_5 : C 22 70 5 := by decide +kernel
theorem row_22_70 : ThresholdAt 22 70 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 70 0 cell_22_70_0
  | exact S 22 70 1 cell_22_70_1
  | exact S 22 70 2 cell_22_70_2
  | exact S 22 70 3 cell_22_70_3
  | exact S 22 70 4 cell_22_70_4
  | exact S 22 70 5 cell_22_70_5
theorem cell_22_71_0 : C 22 71 0 := by decide +kernel
theorem cell_22_71_1 : C 22 71 1 := by decide +kernel
theorem cell_22_71_2 : C 22 71 2 := by decide +kernel
theorem cell_22_71_3 : C 22 71 3 := by decide +kernel
theorem cell_22_71_4 : C 22 71 4 := by decide +kernel
theorem cell_22_71_5 : C 22 71 5 := by decide +kernel
theorem row_22_71 : ThresholdAt 22 71 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 71 0 cell_22_71_0
  | exact S 22 71 1 cell_22_71_1
  | exact S 22 71 2 cell_22_71_2
  | exact S 22 71 3 cell_22_71_3
  | exact S 22 71 4 cell_22_71_4
  | exact S 22 71 5 cell_22_71_5
theorem cell_22_72_0 : C 22 72 0 := by decide +kernel
theorem cell_22_72_1 : C 22 72 1 := by decide +kernel
theorem cell_22_72_2 : C 22 72 2 := by decide +kernel
theorem cell_22_72_3 : C 22 72 3 := by decide +kernel
theorem cell_22_72_4 : C 22 72 4 := by decide +kernel
theorem cell_22_72_5 : C 22 72 5 := by decide +kernel
theorem row_22_72 : ThresholdAt 22 72 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 72 0 cell_22_72_0
  | exact S 22 72 1 cell_22_72_1
  | exact S 22 72 2 cell_22_72_2
  | exact S 22 72 3 cell_22_72_3
  | exact S 22 72 4 cell_22_72_4
  | exact S 22 72 5 cell_22_72_5
theorem cell_22_73_0 : C 22 73 0 := by decide +kernel
theorem cell_22_73_1 : C 22 73 1 := by decide +kernel
theorem cell_22_73_2 : C 22 73 2 := by decide +kernel
theorem cell_22_73_3 : C 22 73 3 := by decide +kernel
theorem cell_22_73_4 : C 22 73 4 := by decide +kernel
theorem cell_22_73_5 : C 22 73 5 := by decide +kernel
theorem row_22_73 : ThresholdAt 22 73 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 73 0 cell_22_73_0
  | exact S 22 73 1 cell_22_73_1
  | exact S 22 73 2 cell_22_73_2
  | exact S 22 73 3 cell_22_73_3
  | exact S 22 73 4 cell_22_73_4
  | exact S 22 73 5 cell_22_73_5
theorem cell_22_74_0 : C 22 74 0 := by decide +kernel
theorem cell_22_74_1 : C 22 74 1 := by decide +kernel
theorem cell_22_74_2 : C 22 74 2 := by decide +kernel
theorem cell_22_74_3 : C 22 74 3 := by decide +kernel
theorem cell_22_74_4 : C 22 74 4 := by decide +kernel
theorem cell_22_74_5 : C 22 74 5 := by decide +kernel
theorem row_22_74 : ThresholdAt 22 74 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 74 0 cell_22_74_0
  | exact S 22 74 1 cell_22_74_1
  | exact S 22 74 2 cell_22_74_2
  | exact S 22 74 3 cell_22_74_3
  | exact S 22 74 4 cell_22_74_4
  | exact S 22 74 5 cell_22_74_5
theorem cell_22_75_0 : C 22 75 0 := by decide +kernel
theorem cell_22_75_1 : C 22 75 1 := by decide +kernel
theorem cell_22_75_2 : C 22 75 2 := by decide +kernel
theorem cell_22_75_3 : C 22 75 3 := by decide +kernel
theorem cell_22_75_4 : C 22 75 4 := by decide +kernel
theorem cell_22_75_5 : C 22 75 5 := by decide +kernel
theorem row_22_75 : ThresholdAt 22 75 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 75 0 cell_22_75_0
  | exact S 22 75 1 cell_22_75_1
  | exact S 22 75 2 cell_22_75_2
  | exact S 22 75 3 cell_22_75_3
  | exact S 22 75 4 cell_22_75_4
  | exact S 22 75 5 cell_22_75_5
theorem cell_22_76_0 : C 22 76 0 := by decide +kernel
theorem cell_22_76_1 : C 22 76 1 := by decide +kernel
theorem cell_22_76_2 : C 22 76 2 := by decide +kernel
theorem cell_22_76_3 : C 22 76 3 := by decide +kernel
theorem cell_22_76_4 : C 22 76 4 := by decide +kernel
theorem cell_22_76_5 : C 22 76 5 := by decide +kernel
theorem row_22_76 : ThresholdAt 22 76 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 76 0 cell_22_76_0
  | exact S 22 76 1 cell_22_76_1
  | exact S 22 76 2 cell_22_76_2
  | exact S 22 76 3 cell_22_76_3
  | exact S 22 76 4 cell_22_76_4
  | exact S 22 76 5 cell_22_76_5
theorem cell_22_77_0 : C 22 77 0 := by decide +kernel
theorem cell_22_77_1 : C 22 77 1 := by decide +kernel
theorem cell_22_77_2 : C 22 77 2 := by decide +kernel
theorem cell_22_77_3 : C 22 77 3 := by decide +kernel
theorem cell_22_77_4 : C 22 77 4 := by decide +kernel
theorem cell_22_77_5 : C 22 77 5 := by decide +kernel
theorem row_22_77 : ThresholdAt 22 77 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 77 0 cell_22_77_0
  | exact S 22 77 1 cell_22_77_1
  | exact S 22 77 2 cell_22_77_2
  | exact S 22 77 3 cell_22_77_3
  | exact S 22 77 4 cell_22_77_4
  | exact S 22 77 5 cell_22_77_5
theorem cell_22_78_0 : C 22 78 0 := by decide +kernel
theorem cell_22_78_1 : C 22 78 1 := by decide +kernel
theorem cell_22_78_2 : C 22 78 2 := by decide +kernel
theorem cell_22_78_3 : C 22 78 3 := by decide +kernel
theorem cell_22_78_4 : C 22 78 4 := by decide +kernel
theorem cell_22_78_5 : C 22 78 5 := by decide +kernel
theorem row_22_78 : ThresholdAt 22 78 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 78 0 cell_22_78_0
  | exact S 22 78 1 cell_22_78_1
  | exact S 22 78 2 cell_22_78_2
  | exact S 22 78 3 cell_22_78_3
  | exact S 22 78 4 cell_22_78_4
  | exact S 22 78 5 cell_22_78_5
theorem cell_22_79_0 : C 22 79 0 := by decide +kernel
theorem cell_22_79_1 : C 22 79 1 := by decide +kernel
theorem cell_22_79_2 : C 22 79 2 := by decide +kernel
theorem cell_22_79_3 : C 22 79 3 := by decide +kernel
theorem cell_22_79_4 : C 22 79 4 := by decide +kernel
theorem cell_22_79_5 : C 22 79 5 := by decide +kernel
theorem row_22_79 : ThresholdAt 22 79 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 79 0 cell_22_79_0
  | exact S 22 79 1 cell_22_79_1
  | exact S 22 79 2 cell_22_79_2
  | exact S 22 79 3 cell_22_79_3
  | exact S 22 79 4 cell_22_79_4
  | exact S 22 79 5 cell_22_79_5
theorem cell_22_80_0 : C 22 80 0 := by decide +kernel
theorem cell_22_80_1 : C 22 80 1 := by decide +kernel
theorem cell_22_80_2 : C 22 80 2 := by decide +kernel
theorem cell_22_80_3 : C 22 80 3 := by decide +kernel
theorem cell_22_80_4 : C 22 80 4 := by decide +kernel
theorem cell_22_80_5 : C 22 80 5 := by decide +kernel
theorem row_22_80 : ThresholdAt 22 80 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 80 0 cell_22_80_0
  | exact S 22 80 1 cell_22_80_1
  | exact S 22 80 2 cell_22_80_2
  | exact S 22 80 3 cell_22_80_3
  | exact S 22 80 4 cell_22_80_4
  | exact S 22 80 5 cell_22_80_5
theorem cell_22_81_0 : C 22 81 0 := by decide +kernel
theorem cell_22_81_1 : C 22 81 1 := by decide +kernel
theorem cell_22_81_2 : C 22 81 2 := by decide +kernel
theorem cell_22_81_3 : C 22 81 3 := by decide +kernel
theorem cell_22_81_4 : C 22 81 4 := by decide +kernel
theorem cell_22_81_5 : C 22 81 5 := by decide +kernel
theorem row_22_81 : ThresholdAt 22 81 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 81 0 cell_22_81_0
  | exact S 22 81 1 cell_22_81_1
  | exact S 22 81 2 cell_22_81_2
  | exact S 22 81 3 cell_22_81_3
  | exact S 22 81 4 cell_22_81_4
  | exact S 22 81 5 cell_22_81_5
theorem cell_22_82_0 : C 22 82 0 := by decide +kernel
theorem cell_22_82_1 : C 22 82 1 := by decide +kernel
theorem cell_22_82_2 : C 22 82 2 := by decide +kernel
theorem cell_22_82_3 : C 22 82 3 := by decide +kernel
theorem cell_22_82_4 : C 22 82 4 := by decide +kernel
theorem cell_22_82_5 : C 22 82 5 := by decide +kernel
theorem row_22_82 : ThresholdAt 22 82 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 82 0 cell_22_82_0
  | exact S 22 82 1 cell_22_82_1
  | exact S 22 82 2 cell_22_82_2
  | exact S 22 82 3 cell_22_82_3
  | exact S 22 82 4 cell_22_82_4
  | exact S 22 82 5 cell_22_82_5
theorem cell_22_83_0 : C 22 83 0 := by decide +kernel
theorem cell_22_83_1 : C 22 83 1 := by decide +kernel
theorem cell_22_83_2 : C 22 83 2 := by decide +kernel
theorem cell_22_83_3 : C 22 83 3 := by decide +kernel
theorem cell_22_83_4 : C 22 83 4 := by decide +kernel
theorem cell_22_83_5 : C 22 83 5 := by decide +kernel
theorem row_22_83 : ThresholdAt 22 83 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 83 0 cell_22_83_0
  | exact S 22 83 1 cell_22_83_1
  | exact S 22 83 2 cell_22_83_2
  | exact S 22 83 3 cell_22_83_3
  | exact S 22 83 4 cell_22_83_4
  | exact S 22 83 5 cell_22_83_5
theorem cell_22_84_0 : C 22 84 0 := by decide +kernel
theorem cell_22_84_1 : C 22 84 1 := by decide +kernel
theorem cell_22_84_2 : C 22 84 2 := by decide +kernel
theorem cell_22_84_3 : C 22 84 3 := by decide +kernel
theorem cell_22_84_4 : C 22 84 4 := by decide +kernel
theorem cell_22_84_5 : C 22 84 5 := by decide +kernel
theorem row_22_84 : ThresholdAt 22 84 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 84 0 cell_22_84_0
  | exact S 22 84 1 cell_22_84_1
  | exact S 22 84 2 cell_22_84_2
  | exact S 22 84 3 cell_22_84_3
  | exact S 22 84 4 cell_22_84_4
  | exact S 22 84 5 cell_22_84_5
theorem cell_22_85_0 : C 22 85 0 := by decide +kernel
theorem cell_22_85_1 : C 22 85 1 := by decide +kernel
theorem cell_22_85_2 : C 22 85 2 := by decide +kernel
theorem cell_22_85_3 : C 22 85 3 := by decide +kernel
theorem cell_22_85_4 : C 22 85 4 := by decide +kernel
theorem cell_22_85_5 : C 22 85 5 := by decide +kernel
theorem row_22_85 : ThresholdAt 22 85 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 85 0 cell_22_85_0
  | exact S 22 85 1 cell_22_85_1
  | exact S 22 85 2 cell_22_85_2
  | exact S 22 85 3 cell_22_85_3
  | exact S 22 85 4 cell_22_85_4
  | exact S 22 85 5 cell_22_85_5
theorem cell_22_86_0 : C 22 86 0 := by decide +kernel
theorem cell_22_86_1 : C 22 86 1 := by decide +kernel
theorem cell_22_86_2 : C 22 86 2 := by decide +kernel
theorem cell_22_86_3 : C 22 86 3 := by decide +kernel
theorem cell_22_86_4 : C 22 86 4 := by decide +kernel
theorem cell_22_86_5 : C 22 86 5 := by decide +kernel
theorem row_22_86 : ThresholdAt 22 86 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 86 0 cell_22_86_0
  | exact S 22 86 1 cell_22_86_1
  | exact S 22 86 2 cell_22_86_2
  | exact S 22 86 3 cell_22_86_3
  | exact S 22 86 4 cell_22_86_4
  | exact S 22 86 5 cell_22_86_5
theorem cell_22_87_0 : C 22 87 0 := by decide +kernel
theorem cell_22_87_1 : C 22 87 1 := by decide +kernel
theorem cell_22_87_2 : C 22 87 2 := by decide +kernel
theorem cell_22_87_3 : C 22 87 3 := by decide +kernel
theorem cell_22_87_4 : C 22 87 4 := by decide +kernel
theorem cell_22_87_5 : C 22 87 5 := by decide +kernel
theorem row_22_87 : ThresholdAt 22 87 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 87 0 cell_22_87_0
  | exact S 22 87 1 cell_22_87_1
  | exact S 22 87 2 cell_22_87_2
  | exact S 22 87 3 cell_22_87_3
  | exact S 22 87 4 cell_22_87_4
  | exact S 22 87 5 cell_22_87_5
theorem cell_22_88_0 : C 22 88 0 := by decide +kernel
theorem cell_22_88_1 : C 22 88 1 := by decide +kernel
theorem cell_22_88_2 : C 22 88 2 := by decide +kernel
theorem cell_22_88_3 : C 22 88 3 := by decide +kernel
theorem cell_22_88_4 : C 22 88 4 := by decide +kernel
theorem cell_22_88_5 : C 22 88 5 := by decide +kernel
theorem row_22_88 : ThresholdAt 22 88 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 88 0 cell_22_88_0
  | exact S 22 88 1 cell_22_88_1
  | exact S 22 88 2 cell_22_88_2
  | exact S 22 88 3 cell_22_88_3
  | exact S 22 88 4 cell_22_88_4
  | exact S 22 88 5 cell_22_88_5
theorem cell_22_89_0 : C 22 89 0 := by decide +kernel
theorem cell_22_89_1 : C 22 89 1 := by decide +kernel
theorem cell_22_89_2 : C 22 89 2 := by decide +kernel
theorem cell_22_89_3 : C 22 89 3 := by decide +kernel
theorem cell_22_89_4 : C 22 89 4 := by decide +kernel
theorem cell_22_89_5 : C 22 89 5 := by decide +kernel
theorem row_22_89 : ThresholdAt 22 89 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 89 0 cell_22_89_0
  | exact S 22 89 1 cell_22_89_1
  | exact S 22 89 2 cell_22_89_2
  | exact S 22 89 3 cell_22_89_3
  | exact S 22 89 4 cell_22_89_4
  | exact S 22 89 5 cell_22_89_5
theorem cell_22_90_0 : C 22 90 0 := by decide +kernel
theorem cell_22_90_1 : C 22 90 1 := by decide +kernel
theorem cell_22_90_2 : C 22 90 2 := by decide +kernel
theorem cell_22_90_3 : C 22 90 3 := by decide +kernel
theorem cell_22_90_4 : C 22 90 4 := by decide +kernel
theorem cell_22_90_5 : C 22 90 5 := by decide +kernel
theorem row_22_90 : ThresholdAt 22 90 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 90 0 cell_22_90_0
  | exact S 22 90 1 cell_22_90_1
  | exact S 22 90 2 cell_22_90_2
  | exact S 22 90 3 cell_22_90_3
  | exact S 22 90 4 cell_22_90_4
  | exact S 22 90 5 cell_22_90_5
theorem cell_22_91_0 : C 22 91 0 := by decide +kernel
theorem cell_22_91_1 : C 22 91 1 := by decide +kernel
theorem cell_22_91_2 : C 22 91 2 := by decide +kernel
theorem cell_22_91_3 : C 22 91 3 := by decide +kernel
theorem cell_22_91_4 : C 22 91 4 := by decide +kernel
theorem cell_22_91_5 : C 22 91 5 := by decide +kernel
theorem row_22_91 : ThresholdAt 22 91 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 91 0 cell_22_91_0
  | exact S 22 91 1 cell_22_91_1
  | exact S 22 91 2 cell_22_91_2
  | exact S 22 91 3 cell_22_91_3
  | exact S 22 91 4 cell_22_91_4
  | exact S 22 91 5 cell_22_91_5
theorem cell_22_92_0 : C 22 92 0 := by decide +kernel
theorem cell_22_92_1 : C 22 92 1 := by decide +kernel
theorem cell_22_92_2 : C 22 92 2 := by decide +kernel
theorem cell_22_92_3 : C 22 92 3 := by decide +kernel
theorem cell_22_92_4 : C 22 92 4 := by decide +kernel
theorem cell_22_92_5 : C 22 92 5 := by decide +kernel
theorem row_22_92 : ThresholdAt 22 92 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 92 0 cell_22_92_0
  | exact S 22 92 1 cell_22_92_1
  | exact S 22 92 2 cell_22_92_2
  | exact S 22 92 3 cell_22_92_3
  | exact S 22 92 4 cell_22_92_4
  | exact S 22 92 5 cell_22_92_5
theorem cell_22_93_0 : C 22 93 0 := by decide +kernel
theorem cell_22_93_1 : C 22 93 1 := by decide +kernel
theorem cell_22_93_2 : C 22 93 2 := by decide +kernel
theorem cell_22_93_3 : C 22 93 3 := by decide +kernel
theorem cell_22_93_4 : C 22 93 4 := by decide +kernel
theorem cell_22_93_5 : C 22 93 5 := by decide +kernel
theorem row_22_93 : ThresholdAt 22 93 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 93 0 cell_22_93_0
  | exact S 22 93 1 cell_22_93_1
  | exact S 22 93 2 cell_22_93_2
  | exact S 22 93 3 cell_22_93_3
  | exact S 22 93 4 cell_22_93_4
  | exact S 22 93 5 cell_22_93_5
theorem cell_22_94_0 : C 22 94 0 := by decide +kernel
theorem cell_22_94_1 : C 22 94 1 := by decide +kernel
theorem cell_22_94_2 : C 22 94 2 := by decide +kernel
theorem cell_22_94_3 : C 22 94 3 := by decide +kernel
theorem cell_22_94_4 : C 22 94 4 := by decide +kernel
theorem cell_22_94_5 : C 22 94 5 := by decide +kernel
theorem row_22_94 : ThresholdAt 22 94 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 94 0 cell_22_94_0
  | exact S 22 94 1 cell_22_94_1
  | exact S 22 94 2 cell_22_94_2
  | exact S 22 94 3 cell_22_94_3
  | exact S 22 94 4 cell_22_94_4
  | exact S 22 94 5 cell_22_94_5
theorem cell_22_95_0 : C 22 95 0 := by decide +kernel
theorem cell_22_95_1 : C 22 95 1 := by decide +kernel
theorem cell_22_95_2 : C 22 95 2 := by decide +kernel
theorem cell_22_95_3 : C 22 95 3 := by decide +kernel
theorem cell_22_95_4 : C 22 95 4 := by decide +kernel
theorem cell_22_95_5 : C 22 95 5 := by decide +kernel
theorem row_22_95 : ThresholdAt 22 95 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 95 0 cell_22_95_0
  | exact S 22 95 1 cell_22_95_1
  | exact S 22 95 2 cell_22_95_2
  | exact S 22 95 3 cell_22_95_3
  | exact S 22 95 4 cell_22_95_4
  | exact S 22 95 5 cell_22_95_5
theorem cell_22_96_0 : C 22 96 0 := by decide +kernel
theorem cell_22_96_1 : C 22 96 1 := by decide +kernel
theorem cell_22_96_2 : C 22 96 2 := by decide +kernel
theorem cell_22_96_3 : C 22 96 3 := by decide +kernel
theorem cell_22_96_4 : C 22 96 4 := by decide +kernel
theorem cell_22_96_5 : C 22 96 5 := by decide +kernel
theorem row_22_96 : ThresholdAt 22 96 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 96 0 cell_22_96_0
  | exact S 22 96 1 cell_22_96_1
  | exact S 22 96 2 cell_22_96_2
  | exact S 22 96 3 cell_22_96_3
  | exact S 22 96 4 cell_22_96_4
  | exact S 22 96 5 cell_22_96_5
theorem cell_22_97_0 : C 22 97 0 := by decide +kernel
theorem cell_22_97_1 : C 22 97 1 := by decide +kernel
theorem cell_22_97_2 : C 22 97 2 := by decide +kernel
theorem cell_22_97_3 : C 22 97 3 := by decide +kernel
theorem cell_22_97_4 : C 22 97 4 := by decide +kernel
theorem cell_22_97_5 : C 22 97 5 := by decide +kernel
theorem row_22_97 : ThresholdAt 22 97 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 97 0 cell_22_97_0
  | exact S 22 97 1 cell_22_97_1
  | exact S 22 97 2 cell_22_97_2
  | exact S 22 97 3 cell_22_97_3
  | exact S 22 97 4 cell_22_97_4
  | exact S 22 97 5 cell_22_97_5
theorem cell_22_98_0 : C 22 98 0 := by decide +kernel
theorem cell_22_98_1 : C 22 98 1 := by decide +kernel
theorem cell_22_98_2 : C 22 98 2 := by decide +kernel
theorem cell_22_98_3 : C 22 98 3 := by decide +kernel
theorem cell_22_98_4 : C 22 98 4 := by decide +kernel
theorem cell_22_98_5 : C 22 98 5 := by decide +kernel
theorem row_22_98 : ThresholdAt 22 98 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 98 0 cell_22_98_0
  | exact S 22 98 1 cell_22_98_1
  | exact S 22 98 2 cell_22_98_2
  | exact S 22 98 3 cell_22_98_3
  | exact S 22 98 4 cell_22_98_4
  | exact S 22 98 5 cell_22_98_5
theorem cell_22_99_0 : C 22 99 0 := by decide +kernel
theorem cell_22_99_1 : C 22 99 1 := by decide +kernel
theorem cell_22_99_2 : C 22 99 2 := by decide +kernel
theorem cell_22_99_3 : C 22 99 3 := by decide +kernel
theorem cell_22_99_4 : C 22 99 4 := by decide +kernel
theorem cell_22_99_5 : C 22 99 5 := by decide +kernel
theorem row_22_99 : ThresholdAt 22 99 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 99 0 cell_22_99_0
  | exact S 22 99 1 cell_22_99_1
  | exact S 22 99 2 cell_22_99_2
  | exact S 22 99 3 cell_22_99_3
  | exact S 22 99 4 cell_22_99_4
  | exact S 22 99 5 cell_22_99_5
theorem cell_22_100_0 : C 22 100 0 := by decide +kernel
theorem cell_22_100_1 : C 22 100 1 := by decide +kernel
theorem cell_22_100_2 : C 22 100 2 := by decide +kernel
theorem cell_22_100_3 : C 22 100 3 := by decide +kernel
theorem cell_22_100_4 : C 22 100 4 := by decide +kernel
theorem cell_22_100_5 : C 22 100 5 := by decide +kernel
theorem row_22_100 : ThresholdAt 22 100 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 100 0 cell_22_100_0
  | exact S 22 100 1 cell_22_100_1
  | exact S 22 100 2 cell_22_100_2
  | exact S 22 100 3 cell_22_100_3
  | exact S 22 100 4 cell_22_100_4
  | exact S 22 100 5 cell_22_100_5
theorem cell_22_101_0 : C 22 101 0 := by decide +kernel
theorem cell_22_101_1 : C 22 101 1 := by decide +kernel
theorem cell_22_101_2 : C 22 101 2 := by decide +kernel
theorem cell_22_101_3 : C 22 101 3 := by decide +kernel
theorem cell_22_101_4 : C 22 101 4 := by decide +kernel
theorem cell_22_101_5 : C 22 101 5 := by decide +kernel
theorem row_22_101 : ThresholdAt 22 101 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 101 0 cell_22_101_0
  | exact S 22 101 1 cell_22_101_1
  | exact S 22 101 2 cell_22_101_2
  | exact S 22 101 3 cell_22_101_3
  | exact S 22 101 4 cell_22_101_4
  | exact S 22 101 5 cell_22_101_5
theorem cell_22_102_0 : C 22 102 0 := by decide +kernel
theorem cell_22_102_1 : C 22 102 1 := by decide +kernel
theorem cell_22_102_2 : C 22 102 2 := by decide +kernel
theorem cell_22_102_3 : C 22 102 3 := by decide +kernel
theorem cell_22_102_4 : C 22 102 4 := by decide +kernel
theorem cell_22_102_5 : C 22 102 5 := by decide +kernel
theorem row_22_102 : ThresholdAt 22 102 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 102 0 cell_22_102_0
  | exact S 22 102 1 cell_22_102_1
  | exact S 22 102 2 cell_22_102_2
  | exact S 22 102 3 cell_22_102_3
  | exact S 22 102 4 cell_22_102_4
  | exact S 22 102 5 cell_22_102_5
theorem cell_22_103_0 : C 22 103 0 := by decide +kernel
theorem cell_22_103_1 : C 22 103 1 := by decide +kernel
theorem cell_22_103_2 : C 22 103 2 := by decide +kernel
theorem cell_22_103_3 : C 22 103 3 := by decide +kernel
theorem cell_22_103_4 : C 22 103 4 := by decide +kernel
theorem cell_22_103_5 : C 22 103 5 := by decide +kernel
theorem row_22_103 : ThresholdAt 22 103 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 103 0 cell_22_103_0
  | exact S 22 103 1 cell_22_103_1
  | exact S 22 103 2 cell_22_103_2
  | exact S 22 103 3 cell_22_103_3
  | exact S 22 103 4 cell_22_103_4
  | exact S 22 103 5 cell_22_103_5
theorem cell_22_104_0 : C 22 104 0 := by decide +kernel
theorem cell_22_104_1 : C 22 104 1 := by decide +kernel
theorem cell_22_104_2 : C 22 104 2 := by decide +kernel
theorem cell_22_104_3 : C 22 104 3 := by decide +kernel
theorem cell_22_104_4 : C 22 104 4 := by decide +kernel
theorem cell_22_104_5 : C 22 104 5 := by decide +kernel
theorem row_22_104 : ThresholdAt 22 104 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 104 0 cell_22_104_0
  | exact S 22 104 1 cell_22_104_1
  | exact S 22 104 2 cell_22_104_2
  | exact S 22 104 3 cell_22_104_3
  | exact S 22 104 4 cell_22_104_4
  | exact S 22 104 5 cell_22_104_5
theorem cell_22_105_0 : C 22 105 0 := by decide +kernel
theorem cell_22_105_1 : C 22 105 1 := by decide +kernel
theorem cell_22_105_2 : C 22 105 2 := by decide +kernel
theorem cell_22_105_3 : C 22 105 3 := by decide +kernel
theorem cell_22_105_4 : C 22 105 4 := by decide +kernel
theorem cell_22_105_5 : C 22 105 5 := by decide +kernel
theorem row_22_105 : ThresholdAt 22 105 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 105 0 cell_22_105_0
  | exact S 22 105 1 cell_22_105_1
  | exact S 22 105 2 cell_22_105_2
  | exact S 22 105 3 cell_22_105_3
  | exact S 22 105 4 cell_22_105_4
  | exact S 22 105 5 cell_22_105_5
theorem cell_22_106_0 : C 22 106 0 := by decide +kernel
theorem cell_22_106_1 : C 22 106 1 := by decide +kernel
theorem cell_22_106_2 : C 22 106 2 := by decide +kernel
theorem cell_22_106_3 : C 22 106 3 := by decide +kernel
theorem cell_22_106_4 : C 22 106 4 := by decide +kernel
theorem cell_22_106_5 : C 22 106 5 := by decide +kernel
theorem row_22_106 : ThresholdAt 22 106 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 106 0 cell_22_106_0
  | exact S 22 106 1 cell_22_106_1
  | exact S 22 106 2 cell_22_106_2
  | exact S 22 106 3 cell_22_106_3
  | exact S 22 106 4 cell_22_106_4
  | exact S 22 106 5 cell_22_106_5
theorem cell_22_107_0 : C 22 107 0 := by decide +kernel
theorem cell_22_107_1 : C 22 107 1 := by decide +kernel
theorem cell_22_107_2 : C 22 107 2 := by decide +kernel
theorem cell_22_107_3 : C 22 107 3 := by decide +kernel
theorem cell_22_107_4 : C 22 107 4 := by decide +kernel
theorem cell_22_107_5 : C 22 107 5 := by decide +kernel
theorem row_22_107 : ThresholdAt 22 107 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 107 0 cell_22_107_0
  | exact S 22 107 1 cell_22_107_1
  | exact S 22 107 2 cell_22_107_2
  | exact S 22 107 3 cell_22_107_3
  | exact S 22 107 4 cell_22_107_4
  | exact S 22 107 5 cell_22_107_5
theorem cell_22_108_0 : C 22 108 0 := by decide +kernel
theorem cell_22_108_1 : C 22 108 1 := by decide +kernel
theorem cell_22_108_2 : C 22 108 2 := by decide +kernel
theorem cell_22_108_3 : C 22 108 3 := by decide +kernel
theorem cell_22_108_4 : C 22 108 4 := by decide +kernel
theorem cell_22_108_5 : C 22 108 5 := by decide +kernel
theorem row_22_108 : ThresholdAt 22 108 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 108 0 cell_22_108_0
  | exact S 22 108 1 cell_22_108_1
  | exact S 22 108 2 cell_22_108_2
  | exact S 22 108 3 cell_22_108_3
  | exact S 22 108 4 cell_22_108_4
  | exact S 22 108 5 cell_22_108_5
theorem cell_22_109_0 : C 22 109 0 := by decide +kernel
theorem cell_22_109_1 : C 22 109 1 := by decide +kernel
theorem cell_22_109_2 : C 22 109 2 := by decide +kernel
theorem cell_22_109_3 : C 22 109 3 := by decide +kernel
theorem cell_22_109_4 : C 22 109 4 := by decide +kernel
theorem cell_22_109_5 : C 22 109 5 := by decide +kernel
theorem row_22_109 : ThresholdAt 22 109 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 109 0 cell_22_109_0
  | exact S 22 109 1 cell_22_109_1
  | exact S 22 109 2 cell_22_109_2
  | exact S 22 109 3 cell_22_109_3
  | exact S 22 109 4 cell_22_109_4
  | exact S 22 109 5 cell_22_109_5
theorem cell_22_110_0 : C 22 110 0 := by decide +kernel
theorem cell_22_110_1 : C 22 110 1 := by decide +kernel
theorem cell_22_110_2 : C 22 110 2 := by decide +kernel
theorem cell_22_110_3 : C 22 110 3 := by decide +kernel
theorem cell_22_110_4 : C 22 110 4 := by decide +kernel
theorem cell_22_110_5 : C 22 110 5 := by decide +kernel
theorem row_22_110 : ThresholdAt 22 110 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 110 0 cell_22_110_0
  | exact S 22 110 1 cell_22_110_1
  | exact S 22 110 2 cell_22_110_2
  | exact S 22 110 3 cell_22_110_3
  | exact S 22 110 4 cell_22_110_4
  | exact S 22 110 5 cell_22_110_5
theorem cell_22_111_0 : C 22 111 0 := by decide +kernel
theorem cell_22_111_1 : C 22 111 1 := by decide +kernel
theorem cell_22_111_2 : C 22 111 2 := by decide +kernel
theorem cell_22_111_3 : C 22 111 3 := by decide +kernel
theorem cell_22_111_4 : C 22 111 4 := by decide +kernel
theorem cell_22_111_5 : C 22 111 5 := by decide +kernel
theorem row_22_111 : ThresholdAt 22 111 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 111 0 cell_22_111_0
  | exact S 22 111 1 cell_22_111_1
  | exact S 22 111 2 cell_22_111_2
  | exact S 22 111 3 cell_22_111_3
  | exact S 22 111 4 cell_22_111_4
  | exact S 22 111 5 cell_22_111_5
theorem cell_22_112_0 : C 22 112 0 := by decide +kernel
theorem cell_22_112_1 : C 22 112 1 := by decide +kernel
theorem cell_22_112_2 : C 22 112 2 := by decide +kernel
theorem cell_22_112_3 : C 22 112 3 := by decide +kernel
theorem cell_22_112_4 : C 22 112 4 := by decide +kernel
theorem cell_22_112_5 : C 22 112 5 := by decide +kernel
theorem row_22_112 : ThresholdAt 22 112 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 112 0 cell_22_112_0
  | exact S 22 112 1 cell_22_112_1
  | exact S 22 112 2 cell_22_112_2
  | exact S 22 112 3 cell_22_112_3
  | exact S 22 112 4 cell_22_112_4
  | exact S 22 112 5 cell_22_112_5
theorem cell_22_113_0 : C 22 113 0 := by decide +kernel
theorem cell_22_113_1 : C 22 113 1 := by decide +kernel
theorem cell_22_113_2 : C 22 113 2 := by decide +kernel
theorem cell_22_113_3 : C 22 113 3 := by decide +kernel
theorem cell_22_113_4 : C 22 113 4 := by decide +kernel
theorem cell_22_113_5 : C 22 113 5 := by decide +kernel
theorem row_22_113 : ThresholdAt 22 113 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 113 0 cell_22_113_0
  | exact S 22 113 1 cell_22_113_1
  | exact S 22 113 2 cell_22_113_2
  | exact S 22 113 3 cell_22_113_3
  | exact S 22 113 4 cell_22_113_4
  | exact S 22 113 5 cell_22_113_5
theorem cell_22_114_0 : C 22 114 0 := by decide +kernel
theorem cell_22_114_1 : C 22 114 1 := by decide +kernel
theorem cell_22_114_2 : C 22 114 2 := by decide +kernel
theorem cell_22_114_3 : C 22 114 3 := by decide +kernel
theorem cell_22_114_4 : C 22 114 4 := by decide +kernel
theorem cell_22_114_5 : C 22 114 5 := by decide +kernel
theorem row_22_114 : ThresholdAt 22 114 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 114 0 cell_22_114_0
  | exact S 22 114 1 cell_22_114_1
  | exact S 22 114 2 cell_22_114_2
  | exact S 22 114 3 cell_22_114_3
  | exact S 22 114 4 cell_22_114_4
  | exact S 22 114 5 cell_22_114_5
theorem cell_22_115_0 : C 22 115 0 := by decide +kernel
theorem cell_22_115_1 : C 22 115 1 := by decide +kernel
theorem cell_22_115_2 : C 22 115 2 := by decide +kernel
theorem cell_22_115_3 : C 22 115 3 := by decide +kernel
theorem cell_22_115_4 : C 22 115 4 := by decide +kernel
theorem cell_22_115_5 : C 22 115 5 := by decide +kernel
theorem row_22_115 : ThresholdAt 22 115 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 115 0 cell_22_115_0
  | exact S 22 115 1 cell_22_115_1
  | exact S 22 115 2 cell_22_115_2
  | exact S 22 115 3 cell_22_115_3
  | exact S 22 115 4 cell_22_115_4
  | exact S 22 115 5 cell_22_115_5
theorem cell_22_116_0 : C 22 116 0 := by decide +kernel
theorem cell_22_116_1 : C 22 116 1 := by decide +kernel
theorem cell_22_116_2 : C 22 116 2 := by decide +kernel
theorem cell_22_116_3 : C 22 116 3 := by decide +kernel
theorem cell_22_116_4 : C 22 116 4 := by decide +kernel
theorem cell_22_116_5 : C 22 116 5 := by decide +kernel
theorem row_22_116 : ThresholdAt 22 116 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 116 0 cell_22_116_0
  | exact S 22 116 1 cell_22_116_1
  | exact S 22 116 2 cell_22_116_2
  | exact S 22 116 3 cell_22_116_3
  | exact S 22 116 4 cell_22_116_4
  | exact S 22 116 5 cell_22_116_5
theorem cell_22_117_0 : C 22 117 0 := by decide +kernel
theorem cell_22_117_1 : C 22 117 1 := by decide +kernel
theorem cell_22_117_2 : C 22 117 2 := by decide +kernel
theorem cell_22_117_3 : C 22 117 3 := by decide +kernel
theorem cell_22_117_4 : C 22 117 4 := by decide +kernel
theorem cell_22_117_5 : C 22 117 5 := by decide +kernel
theorem row_22_117 : ThresholdAt 22 117 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 22 117 0 cell_22_117_0
  | exact S 22 117 1 cell_22_117_1
  | exact S 22 117 2 cell_22_117_2
  | exact S 22 117 3 cell_22_117_3
  | exact S 22 117 4 cell_22_117_4
  | exact S 22 117 5 cell_22_117_5
theorem checkedR22 : ∀ V ∈ List.range 118, ThresholdAt 22 V := by
  intro V hV
  have hv : V < 118 := List.mem_range.mp hV
  by_cases h0_118 : V < 59
  · by_cases h0_59 : V < 29
    · by_cases h0_29 : V < 14
      · by_cases h0_14 : V < 7
        · by_cases h0_7 : V < 3
          · by_cases h0_3 : V < 1
            · have he : V = 0 := by omega
              subst V
              exact row_22_0
            · by_cases h1_3 : V < 2
              · have he : V = 1 := by omega
                subst V
                exact row_22_1
              · have he : V = 2 := by omega
                subst V
                exact row_22_2
          · by_cases h3_7 : V < 5
            · by_cases h3_5 : V < 4
              · have he : V = 3 := by omega
                subst V
                exact row_22_3
              · have he : V = 4 := by omega
                subst V
                exact row_22_4
            · by_cases h5_7 : V < 6
              · have he : V = 5 := by omega
                subst V
                exact row_22_5
              · have he : V = 6 := by omega
                subst V
                exact row_22_6
        · by_cases h7_14 : V < 10
          · by_cases h7_10 : V < 8
            · have he : V = 7 := by omega
              subst V
              exact row_22_7
            · by_cases h8_10 : V < 9
              · have he : V = 8 := by omega
                subst V
                exact row_22_8
              · have he : V = 9 := by omega
                subst V
                exact row_22_9
          · by_cases h10_14 : V < 12
            · by_cases h10_12 : V < 11
              · have he : V = 10 := by omega
                subst V
                exact row_22_10
              · have he : V = 11 := by omega
                subst V
                exact row_22_11
            · by_cases h12_14 : V < 13
              · have he : V = 12 := by omega
                subst V
                exact row_22_12
              · have he : V = 13 := by omega
                subst V
                exact row_22_13
      · by_cases h14_29 : V < 21
        · by_cases h14_21 : V < 17
          · by_cases h14_17 : V < 15
            · have he : V = 14 := by omega
              subst V
              exact row_22_14
            · by_cases h15_17 : V < 16
              · have he : V = 15 := by omega
                subst V
                exact row_22_15
              · have he : V = 16 := by omega
                subst V
                exact row_22_16
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have he : V = 17 := by omega
                subst V
                exact row_22_17
              · have he : V = 18 := by omega
                subst V
                exact row_22_18
            · by_cases h19_21 : V < 20
              · have he : V = 19 := by omega
                subst V
                exact row_22_19
              · have he : V = 20 := by omega
                subst V
                exact row_22_20
        · by_cases h21_29 : V < 25
          · by_cases h21_25 : V < 23
            · by_cases h21_23 : V < 22
              · have he : V = 21 := by omega
                subst V
                exact row_22_21
              · have he : V = 22 := by omega
                subst V
                exact row_22_22
            · by_cases h23_25 : V < 24
              · have he : V = 23 := by omega
                subst V
                exact row_22_23
              · have he : V = 24 := by omega
                subst V
                exact row_22_24
          · by_cases h25_29 : V < 27
            · by_cases h25_27 : V < 26
              · have he : V = 25 := by omega
                subst V
                exact row_22_25
              · have he : V = 26 := by omega
                subst V
                exact row_22_26
            · by_cases h27_29 : V < 28
              · have he : V = 27 := by omega
                subst V
                exact row_22_27
              · have he : V = 28 := by omega
                subst V
                exact row_22_28
    · by_cases h29_59 : V < 44
      · by_cases h29_44 : V < 36
        · by_cases h29_36 : V < 32
          · by_cases h29_32 : V < 30
            · have he : V = 29 := by omega
              subst V
              exact row_22_29
            · by_cases h30_32 : V < 31
              · have he : V = 30 := by omega
                subst V
                exact row_22_30
              · have he : V = 31 := by omega
                subst V
                exact row_22_31
          · by_cases h32_36 : V < 34
            · by_cases h32_34 : V < 33
              · have he : V = 32 := by omega
                subst V
                exact row_22_32
              · have he : V = 33 := by omega
                subst V
                exact row_22_33
            · by_cases h34_36 : V < 35
              · have he : V = 34 := by omega
                subst V
                exact row_22_34
              · have he : V = 35 := by omega
                subst V
                exact row_22_35
        · by_cases h36_44 : V < 40
          · by_cases h36_40 : V < 38
            · by_cases h36_38 : V < 37
              · have he : V = 36 := by omega
                subst V
                exact row_22_36
              · have he : V = 37 := by omega
                subst V
                exact row_22_37
            · by_cases h38_40 : V < 39
              · have he : V = 38 := by omega
                subst V
                exact row_22_38
              · have he : V = 39 := by omega
                subst V
                exact row_22_39
          · by_cases h40_44 : V < 42
            · by_cases h40_42 : V < 41
              · have he : V = 40 := by omega
                subst V
                exact row_22_40
              · have he : V = 41 := by omega
                subst V
                exact row_22_41
            · by_cases h42_44 : V < 43
              · have he : V = 42 := by omega
                subst V
                exact row_22_42
              · have he : V = 43 := by omega
                subst V
                exact row_22_43
      · by_cases h44_59 : V < 51
        · by_cases h44_51 : V < 47
          · by_cases h44_47 : V < 45
            · have he : V = 44 := by omega
              subst V
              exact row_22_44
            · by_cases h45_47 : V < 46
              · have he : V = 45 := by omega
                subst V
                exact row_22_45
              · have he : V = 46 := by omega
                subst V
                exact row_22_46
          · by_cases h47_51 : V < 49
            · by_cases h47_49 : V < 48
              · have he : V = 47 := by omega
                subst V
                exact row_22_47
              · have he : V = 48 := by omega
                subst V
                exact row_22_48
            · by_cases h49_51 : V < 50
              · have he : V = 49 := by omega
                subst V
                exact row_22_49
              · have he : V = 50 := by omega
                subst V
                exact row_22_50
        · by_cases h51_59 : V < 55
          · by_cases h51_55 : V < 53
            · by_cases h51_53 : V < 52
              · have he : V = 51 := by omega
                subst V
                exact row_22_51
              · have he : V = 52 := by omega
                subst V
                exact row_22_52
            · by_cases h53_55 : V < 54
              · have he : V = 53 := by omega
                subst V
                exact row_22_53
              · have he : V = 54 := by omega
                subst V
                exact row_22_54
          · by_cases h55_59 : V < 57
            · by_cases h55_57 : V < 56
              · have he : V = 55 := by omega
                subst V
                exact row_22_55
              · have he : V = 56 := by omega
                subst V
                exact row_22_56
            · by_cases h57_59 : V < 58
              · have he : V = 57 := by omega
                subst V
                exact row_22_57
              · have he : V = 58 := by omega
                subst V
                exact row_22_58
  · by_cases h59_118 : V < 88
    · by_cases h59_88 : V < 73
      · by_cases h59_73 : V < 66
        · by_cases h59_66 : V < 62
          · by_cases h59_62 : V < 60
            · have he : V = 59 := by omega
              subst V
              exact row_22_59
            · by_cases h60_62 : V < 61
              · have he : V = 60 := by omega
                subst V
                exact row_22_60
              · have he : V = 61 := by omega
                subst V
                exact row_22_61
          · by_cases h62_66 : V < 64
            · by_cases h62_64 : V < 63
              · have he : V = 62 := by omega
                subst V
                exact row_22_62
              · have he : V = 63 := by omega
                subst V
                exact row_22_63
            · by_cases h64_66 : V < 65
              · have he : V = 64 := by omega
                subst V
                exact row_22_64
              · have he : V = 65 := by omega
                subst V
                exact row_22_65
        · by_cases h66_73 : V < 69
          · by_cases h66_69 : V < 67
            · have he : V = 66 := by omega
              subst V
              exact row_22_66
            · by_cases h67_69 : V < 68
              · have he : V = 67 := by omega
                subst V
                exact row_22_67
              · have he : V = 68 := by omega
                subst V
                exact row_22_68
          · by_cases h69_73 : V < 71
            · by_cases h69_71 : V < 70
              · have he : V = 69 := by omega
                subst V
                exact row_22_69
              · have he : V = 70 := by omega
                subst V
                exact row_22_70
            · by_cases h71_73 : V < 72
              · have he : V = 71 := by omega
                subst V
                exact row_22_71
              · have he : V = 72 := by omega
                subst V
                exact row_22_72
      · by_cases h73_88 : V < 80
        · by_cases h73_80 : V < 76
          · by_cases h73_76 : V < 74
            · have he : V = 73 := by omega
              subst V
              exact row_22_73
            · by_cases h74_76 : V < 75
              · have he : V = 74 := by omega
                subst V
                exact row_22_74
              · have he : V = 75 := by omega
                subst V
                exact row_22_75
          · by_cases h76_80 : V < 78
            · by_cases h76_78 : V < 77
              · have he : V = 76 := by omega
                subst V
                exact row_22_76
              · have he : V = 77 := by omega
                subst V
                exact row_22_77
            · by_cases h78_80 : V < 79
              · have he : V = 78 := by omega
                subst V
                exact row_22_78
              · have he : V = 79 := by omega
                subst V
                exact row_22_79
        · by_cases h80_88 : V < 84
          · by_cases h80_84 : V < 82
            · by_cases h80_82 : V < 81
              · have he : V = 80 := by omega
                subst V
                exact row_22_80
              · have he : V = 81 := by omega
                subst V
                exact row_22_81
            · by_cases h82_84 : V < 83
              · have he : V = 82 := by omega
                subst V
                exact row_22_82
              · have he : V = 83 := by omega
                subst V
                exact row_22_83
          · by_cases h84_88 : V < 86
            · by_cases h84_86 : V < 85
              · have he : V = 84 := by omega
                subst V
                exact row_22_84
              · have he : V = 85 := by omega
                subst V
                exact row_22_85
            · by_cases h86_88 : V < 87
              · have he : V = 86 := by omega
                subst V
                exact row_22_86
              · have he : V = 87 := by omega
                subst V
                exact row_22_87
    · by_cases h88_118 : V < 103
      · by_cases h88_103 : V < 95
        · by_cases h88_95 : V < 91
          · by_cases h88_91 : V < 89
            · have he : V = 88 := by omega
              subst V
              exact row_22_88
            · by_cases h89_91 : V < 90
              · have he : V = 89 := by omega
                subst V
                exact row_22_89
              · have he : V = 90 := by omega
                subst V
                exact row_22_90
          · by_cases h91_95 : V < 93
            · by_cases h91_93 : V < 92
              · have he : V = 91 := by omega
                subst V
                exact row_22_91
              · have he : V = 92 := by omega
                subst V
                exact row_22_92
            · by_cases h93_95 : V < 94
              · have he : V = 93 := by omega
                subst V
                exact row_22_93
              · have he : V = 94 := by omega
                subst V
                exact row_22_94
        · by_cases h95_103 : V < 99
          · by_cases h95_99 : V < 97
            · by_cases h95_97 : V < 96
              · have he : V = 95 := by omega
                subst V
                exact row_22_95
              · have he : V = 96 := by omega
                subst V
                exact row_22_96
            · by_cases h97_99 : V < 98
              · have he : V = 97 := by omega
                subst V
                exact row_22_97
              · have he : V = 98 := by omega
                subst V
                exact row_22_98
          · by_cases h99_103 : V < 101
            · by_cases h99_101 : V < 100
              · have he : V = 99 := by omega
                subst V
                exact row_22_99
              · have he : V = 100 := by omega
                subst V
                exact row_22_100
            · by_cases h101_103 : V < 102
              · have he : V = 101 := by omega
                subst V
                exact row_22_101
              · have he : V = 102 := by omega
                subst V
                exact row_22_102
      · by_cases h103_118 : V < 110
        · by_cases h103_110 : V < 106
          · by_cases h103_106 : V < 104
            · have he : V = 103 := by omega
              subst V
              exact row_22_103
            · by_cases h104_106 : V < 105
              · have he : V = 104 := by omega
                subst V
                exact row_22_104
              · have he : V = 105 := by omega
                subst V
                exact row_22_105
          · by_cases h106_110 : V < 108
            · by_cases h106_108 : V < 107
              · have he : V = 106 := by omega
                subst V
                exact row_22_106
              · have he : V = 107 := by omega
                subst V
                exact row_22_107
            · by_cases h108_110 : V < 109
              · have he : V = 108 := by omega
                subst V
                exact row_22_108
              · have he : V = 109 := by omega
                subst V
                exact row_22_109
        · by_cases h110_118 : V < 114
          · by_cases h110_114 : V < 112
            · by_cases h110_112 : V < 111
              · have he : V = 110 := by omega
                subst V
                exact row_22_110
              · have he : V = 111 := by omega
                subst V
                exact row_22_111
            · by_cases h112_114 : V < 113
              · have he : V = 112 := by omega
                subst V
                exact row_22_112
              · have he : V = 113 := by omega
                subst V
                exact row_22_113
          · by_cases h114_118 : V < 116
            · by_cases h114_116 : V < 115
              · have he : V = 114 := by omega
                subst V
                exact row_22_114
              · have he : V = 115 := by omega
                subst V
                exact row_22_115
            · by_cases h116_118 : V < 117
              · have he : V = 116 := by omega
                subst V
                exact row_22_116
              · have he : V = 117 := by omega
                subst V
                exact row_22_117
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
