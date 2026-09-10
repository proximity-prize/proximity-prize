import ProximityPrize.SubmissionLower.BoundaryTailThresholdData

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
local notation "C" => CertificateAt
local notation "S" => certificate_sound
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_1_0_0 : C 1 0 0 := by decide +kernel
theorem cell_1_0_1 : C 1 0 1 := by decide +kernel
theorem cell_1_0_2 : C 1 0 2 := by decide +kernel
theorem cell_1_0_3 : C 1 0 3 := by decide +kernel
theorem cell_1_0_4 : C 1 0 4 := by decide +kernel
theorem cell_1_0_5 : C 1 0 5 := by decide +kernel
theorem row_1_0 : ThresholdAt 1 0 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 0 0 cell_1_0_0
  | exact S 1 0 1 cell_1_0_1
  | exact S 1 0 2 cell_1_0_2
  | exact S 1 0 3 cell_1_0_3
  | exact S 1 0 4 cell_1_0_4
  | exact S 1 0 5 cell_1_0_5
theorem cell_1_1_0 : C 1 1 0 := by decide +kernel
theorem cell_1_1_1 : C 1 1 1 := by decide +kernel
theorem cell_1_1_2 : C 1 1 2 := by decide +kernel
theorem cell_1_1_3 : C 1 1 3 := by decide +kernel
theorem cell_1_1_4 : C 1 1 4 := by decide +kernel
theorem cell_1_1_5 : C 1 1 5 := by decide +kernel
theorem row_1_1 : ThresholdAt 1 1 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 1 0 cell_1_1_0
  | exact S 1 1 1 cell_1_1_1
  | exact S 1 1 2 cell_1_1_2
  | exact S 1 1 3 cell_1_1_3
  | exact S 1 1 4 cell_1_1_4
  | exact S 1 1 5 cell_1_1_5
theorem cell_1_2_0 : C 1 2 0 := by decide +kernel
theorem cell_1_2_1 : C 1 2 1 := by decide +kernel
theorem cell_1_2_2 : C 1 2 2 := by decide +kernel
theorem cell_1_2_3 : C 1 2 3 := by decide +kernel
theorem cell_1_2_4 : C 1 2 4 := by decide +kernel
theorem cell_1_2_5 : C 1 2 5 := by decide +kernel
theorem row_1_2 : ThresholdAt 1 2 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 2 0 cell_1_2_0
  | exact S 1 2 1 cell_1_2_1
  | exact S 1 2 2 cell_1_2_2
  | exact S 1 2 3 cell_1_2_3
  | exact S 1 2 4 cell_1_2_4
  | exact S 1 2 5 cell_1_2_5
theorem cell_1_3_0 : C 1 3 0 := by decide +kernel
theorem cell_1_3_1 : C 1 3 1 := by decide +kernel
theorem cell_1_3_2 : C 1 3 2 := by decide +kernel
theorem cell_1_3_3 : C 1 3 3 := by decide +kernel
theorem cell_1_3_4 : C 1 3 4 := by decide +kernel
theorem cell_1_3_5 : C 1 3 5 := by decide +kernel
theorem row_1_3 : ThresholdAt 1 3 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 3 0 cell_1_3_0
  | exact S 1 3 1 cell_1_3_1
  | exact S 1 3 2 cell_1_3_2
  | exact S 1 3 3 cell_1_3_3
  | exact S 1 3 4 cell_1_3_4
  | exact S 1 3 5 cell_1_3_5
theorem cell_1_4_0 : C 1 4 0 := by decide +kernel
theorem cell_1_4_1 : C 1 4 1 := by decide +kernel
theorem cell_1_4_2 : C 1 4 2 := by decide +kernel
theorem cell_1_4_3 : C 1 4 3 := by decide +kernel
theorem cell_1_4_4 : C 1 4 4 := by decide +kernel
theorem cell_1_4_5 : C 1 4 5 := by decide +kernel
theorem row_1_4 : ThresholdAt 1 4 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 4 0 cell_1_4_0
  | exact S 1 4 1 cell_1_4_1
  | exact S 1 4 2 cell_1_4_2
  | exact S 1 4 3 cell_1_4_3
  | exact S 1 4 4 cell_1_4_4
  | exact S 1 4 5 cell_1_4_5
theorem cell_1_5_0 : C 1 5 0 := by decide +kernel
theorem cell_1_5_1 : C 1 5 1 := by decide +kernel
theorem cell_1_5_2 : C 1 5 2 := by decide +kernel
theorem cell_1_5_3 : C 1 5 3 := by decide +kernel
theorem cell_1_5_4 : C 1 5 4 := by decide +kernel
theorem cell_1_5_5 : C 1 5 5 := by decide +kernel
theorem row_1_5 : ThresholdAt 1 5 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 5 0 cell_1_5_0
  | exact S 1 5 1 cell_1_5_1
  | exact S 1 5 2 cell_1_5_2
  | exact S 1 5 3 cell_1_5_3
  | exact S 1 5 4 cell_1_5_4
  | exact S 1 5 5 cell_1_5_5
theorem cell_1_6_0 : C 1 6 0 := by decide +kernel
theorem cell_1_6_1 : C 1 6 1 := by decide +kernel
theorem cell_1_6_2 : C 1 6 2 := by decide +kernel
theorem cell_1_6_3 : C 1 6 3 := by decide +kernel
theorem cell_1_6_4 : C 1 6 4 := by decide +kernel
theorem cell_1_6_5 : C 1 6 5 := by decide +kernel
theorem row_1_6 : ThresholdAt 1 6 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 6 0 cell_1_6_0
  | exact S 1 6 1 cell_1_6_1
  | exact S 1 6 2 cell_1_6_2
  | exact S 1 6 3 cell_1_6_3
  | exact S 1 6 4 cell_1_6_4
  | exact S 1 6 5 cell_1_6_5
theorem cell_1_7_0 : C 1 7 0 := by decide +kernel
theorem cell_1_7_1 : C 1 7 1 := by decide +kernel
theorem cell_1_7_2 : C 1 7 2 := by decide +kernel
theorem cell_1_7_3 : C 1 7 3 := by decide +kernel
theorem cell_1_7_4 : C 1 7 4 := by decide +kernel
theorem cell_1_7_5 : C 1 7 5 := by decide +kernel
theorem row_1_7 : ThresholdAt 1 7 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 7 0 cell_1_7_0
  | exact S 1 7 1 cell_1_7_1
  | exact S 1 7 2 cell_1_7_2
  | exact S 1 7 3 cell_1_7_3
  | exact S 1 7 4 cell_1_7_4
  | exact S 1 7 5 cell_1_7_5
theorem cell_1_8_0 : C 1 8 0 := by decide +kernel
theorem cell_1_8_1 : C 1 8 1 := by decide +kernel
theorem cell_1_8_2 : C 1 8 2 := by decide +kernel
theorem cell_1_8_3 : C 1 8 3 := by decide +kernel
theorem cell_1_8_4 : C 1 8 4 := by decide +kernel
theorem cell_1_8_5 : C 1 8 5 := by decide +kernel
theorem row_1_8 : ThresholdAt 1 8 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 8 0 cell_1_8_0
  | exact S 1 8 1 cell_1_8_1
  | exact S 1 8 2 cell_1_8_2
  | exact S 1 8 3 cell_1_8_3
  | exact S 1 8 4 cell_1_8_4
  | exact S 1 8 5 cell_1_8_5
theorem cell_1_9_0 : C 1 9 0 := by decide +kernel
theorem cell_1_9_1 : C 1 9 1 := by decide +kernel
theorem cell_1_9_2 : C 1 9 2 := by decide +kernel
theorem cell_1_9_3 : C 1 9 3 := by decide +kernel
theorem cell_1_9_4 : C 1 9 4 := by decide +kernel
theorem cell_1_9_5 : C 1 9 5 := by decide +kernel
theorem row_1_9 : ThresholdAt 1 9 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 9 0 cell_1_9_0
  | exact S 1 9 1 cell_1_9_1
  | exact S 1 9 2 cell_1_9_2
  | exact S 1 9 3 cell_1_9_3
  | exact S 1 9 4 cell_1_9_4
  | exact S 1 9 5 cell_1_9_5
theorem cell_1_10_0 : C 1 10 0 := by decide +kernel
theorem cell_1_10_1 : C 1 10 1 := by decide +kernel
theorem cell_1_10_2 : C 1 10 2 := by decide +kernel
theorem cell_1_10_3 : C 1 10 3 := by decide +kernel
theorem cell_1_10_4 : C 1 10 4 := by decide +kernel
theorem cell_1_10_5 : C 1 10 5 := by decide +kernel
theorem row_1_10 : ThresholdAt 1 10 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 10 0 cell_1_10_0
  | exact S 1 10 1 cell_1_10_1
  | exact S 1 10 2 cell_1_10_2
  | exact S 1 10 3 cell_1_10_3
  | exact S 1 10 4 cell_1_10_4
  | exact S 1 10 5 cell_1_10_5
theorem cell_1_11_0 : C 1 11 0 := by decide +kernel
theorem cell_1_11_1 : C 1 11 1 := by decide +kernel
theorem cell_1_11_2 : C 1 11 2 := by decide +kernel
theorem cell_1_11_3 : C 1 11 3 := by decide +kernel
theorem cell_1_11_4 : C 1 11 4 := by decide +kernel
theorem cell_1_11_5 : C 1 11 5 := by decide +kernel
theorem row_1_11 : ThresholdAt 1 11 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 11 0 cell_1_11_0
  | exact S 1 11 1 cell_1_11_1
  | exact S 1 11 2 cell_1_11_2
  | exact S 1 11 3 cell_1_11_3
  | exact S 1 11 4 cell_1_11_4
  | exact S 1 11 5 cell_1_11_5
theorem cell_1_12_0 : C 1 12 0 := by decide +kernel
theorem cell_1_12_1 : C 1 12 1 := by decide +kernel
theorem cell_1_12_2 : C 1 12 2 := by decide +kernel
theorem cell_1_12_3 : C 1 12 3 := by decide +kernel
theorem cell_1_12_4 : C 1 12 4 := by decide +kernel
theorem cell_1_12_5 : C 1 12 5 := by decide +kernel
theorem row_1_12 : ThresholdAt 1 12 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 12 0 cell_1_12_0
  | exact S 1 12 1 cell_1_12_1
  | exact S 1 12 2 cell_1_12_2
  | exact S 1 12 3 cell_1_12_3
  | exact S 1 12 4 cell_1_12_4
  | exact S 1 12 5 cell_1_12_5
theorem cell_1_13_0 : C 1 13 0 := by decide +kernel
theorem cell_1_13_1 : C 1 13 1 := by decide +kernel
theorem cell_1_13_2 : C 1 13 2 := by decide +kernel
theorem cell_1_13_3 : C 1 13 3 := by decide +kernel
theorem cell_1_13_4 : C 1 13 4 := by decide +kernel
theorem cell_1_13_5 : C 1 13 5 := by decide +kernel
theorem row_1_13 : ThresholdAt 1 13 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 13 0 cell_1_13_0
  | exact S 1 13 1 cell_1_13_1
  | exact S 1 13 2 cell_1_13_2
  | exact S 1 13 3 cell_1_13_3
  | exact S 1 13 4 cell_1_13_4
  | exact S 1 13 5 cell_1_13_5
theorem cell_1_14_0 : C 1 14 0 := by decide +kernel
theorem cell_1_14_1 : C 1 14 1 := by decide +kernel
theorem cell_1_14_2 : C 1 14 2 := by decide +kernel
theorem cell_1_14_3 : C 1 14 3 := by decide +kernel
theorem cell_1_14_4 : C 1 14 4 := by decide +kernel
theorem cell_1_14_5 : C 1 14 5 := by decide +kernel
theorem row_1_14 : ThresholdAt 1 14 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 14 0 cell_1_14_0
  | exact S 1 14 1 cell_1_14_1
  | exact S 1 14 2 cell_1_14_2
  | exact S 1 14 3 cell_1_14_3
  | exact S 1 14 4 cell_1_14_4
  | exact S 1 14 5 cell_1_14_5
theorem cell_1_15_0 : C 1 15 0 := by decide +kernel
theorem cell_1_15_1 : C 1 15 1 := by decide +kernel
theorem cell_1_15_2 : C 1 15 2 := by decide +kernel
theorem cell_1_15_3 : C 1 15 3 := by decide +kernel
theorem cell_1_15_4 : C 1 15 4 := by decide +kernel
theorem cell_1_15_5 : C 1 15 5 := by decide +kernel
theorem row_1_15 : ThresholdAt 1 15 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 15 0 cell_1_15_0
  | exact S 1 15 1 cell_1_15_1
  | exact S 1 15 2 cell_1_15_2
  | exact S 1 15 3 cell_1_15_3
  | exact S 1 15 4 cell_1_15_4
  | exact S 1 15 5 cell_1_15_5
theorem cell_1_16_0 : C 1 16 0 := by decide +kernel
theorem cell_1_16_1 : C 1 16 1 := by decide +kernel
theorem cell_1_16_2 : C 1 16 2 := by decide +kernel
theorem cell_1_16_3 : C 1 16 3 := by decide +kernel
theorem cell_1_16_4 : C 1 16 4 := by decide +kernel
theorem cell_1_16_5 : C 1 16 5 := by decide +kernel
theorem row_1_16 : ThresholdAt 1 16 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 16 0 cell_1_16_0
  | exact S 1 16 1 cell_1_16_1
  | exact S 1 16 2 cell_1_16_2
  | exact S 1 16 3 cell_1_16_3
  | exact S 1 16 4 cell_1_16_4
  | exact S 1 16 5 cell_1_16_5
theorem cell_1_17_0 : C 1 17 0 := by decide +kernel
theorem cell_1_17_1 : C 1 17 1 := by decide +kernel
theorem cell_1_17_2 : C 1 17 2 := by decide +kernel
theorem cell_1_17_3 : C 1 17 3 := by decide +kernel
theorem cell_1_17_4 : C 1 17 4 := by decide +kernel
theorem cell_1_17_5 : C 1 17 5 := by decide +kernel
theorem row_1_17 : ThresholdAt 1 17 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 17 0 cell_1_17_0
  | exact S 1 17 1 cell_1_17_1
  | exact S 1 17 2 cell_1_17_2
  | exact S 1 17 3 cell_1_17_3
  | exact S 1 17 4 cell_1_17_4
  | exact S 1 17 5 cell_1_17_5
theorem cell_1_18_0 : C 1 18 0 := by decide +kernel
theorem cell_1_18_1 : C 1 18 1 := by decide +kernel
theorem cell_1_18_2 : C 1 18 2 := by decide +kernel
theorem cell_1_18_3 : C 1 18 3 := by decide +kernel
theorem cell_1_18_4 : C 1 18 4 := by decide +kernel
theorem cell_1_18_5 : C 1 18 5 := by decide +kernel
theorem row_1_18 : ThresholdAt 1 18 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 18 0 cell_1_18_0
  | exact S 1 18 1 cell_1_18_1
  | exact S 1 18 2 cell_1_18_2
  | exact S 1 18 3 cell_1_18_3
  | exact S 1 18 4 cell_1_18_4
  | exact S 1 18 5 cell_1_18_5
theorem cell_1_19_0 : C 1 19 0 := by decide +kernel
theorem cell_1_19_1 : C 1 19 1 := by decide +kernel
theorem cell_1_19_2 : C 1 19 2 := by decide +kernel
theorem cell_1_19_3 : C 1 19 3 := by decide +kernel
theorem cell_1_19_4 : C 1 19 4 := by decide +kernel
theorem cell_1_19_5 : C 1 19 5 := by decide +kernel
theorem row_1_19 : ThresholdAt 1 19 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 19 0 cell_1_19_0
  | exact S 1 19 1 cell_1_19_1
  | exact S 1 19 2 cell_1_19_2
  | exact S 1 19 3 cell_1_19_3
  | exact S 1 19 4 cell_1_19_4
  | exact S 1 19 5 cell_1_19_5
theorem cell_1_20_0 : C 1 20 0 := by decide +kernel
theorem cell_1_20_1 : C 1 20 1 := by decide +kernel
theorem cell_1_20_2 : C 1 20 2 := by decide +kernel
theorem cell_1_20_3 : C 1 20 3 := by decide +kernel
theorem cell_1_20_4 : C 1 20 4 := by decide +kernel
theorem cell_1_20_5 : C 1 20 5 := by decide +kernel
theorem row_1_20 : ThresholdAt 1 20 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 20 0 cell_1_20_0
  | exact S 1 20 1 cell_1_20_1
  | exact S 1 20 2 cell_1_20_2
  | exact S 1 20 3 cell_1_20_3
  | exact S 1 20 4 cell_1_20_4
  | exact S 1 20 5 cell_1_20_5
theorem cell_1_21_0 : C 1 21 0 := by decide +kernel
theorem cell_1_21_1 : C 1 21 1 := by decide +kernel
theorem cell_1_21_2 : C 1 21 2 := by decide +kernel
theorem cell_1_21_3 : C 1 21 3 := by decide +kernel
theorem cell_1_21_4 : C 1 21 4 := by decide +kernel
theorem cell_1_21_5 : C 1 21 5 := by decide +kernel
theorem row_1_21 : ThresholdAt 1 21 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 21 0 cell_1_21_0
  | exact S 1 21 1 cell_1_21_1
  | exact S 1 21 2 cell_1_21_2
  | exact S 1 21 3 cell_1_21_3
  | exact S 1 21 4 cell_1_21_4
  | exact S 1 21 5 cell_1_21_5
theorem cell_1_22_0 : C 1 22 0 := by decide +kernel
theorem cell_1_22_1 : C 1 22 1 := by decide +kernel
theorem cell_1_22_2 : C 1 22 2 := by decide +kernel
theorem cell_1_22_3 : C 1 22 3 := by decide +kernel
theorem cell_1_22_4 : C 1 22 4 := by decide +kernel
theorem cell_1_22_5 : C 1 22 5 := by decide +kernel
theorem row_1_22 : ThresholdAt 1 22 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 22 0 cell_1_22_0
  | exact S 1 22 1 cell_1_22_1
  | exact S 1 22 2 cell_1_22_2
  | exact S 1 22 3 cell_1_22_3
  | exact S 1 22 4 cell_1_22_4
  | exact S 1 22 5 cell_1_22_5
theorem cell_1_23_0 : C 1 23 0 := by decide +kernel
theorem cell_1_23_1 : C 1 23 1 := by decide +kernel
theorem cell_1_23_2 : C 1 23 2 := by decide +kernel
theorem cell_1_23_3 : C 1 23 3 := by decide +kernel
theorem cell_1_23_4 : C 1 23 4 := by decide +kernel
theorem cell_1_23_5 : C 1 23 5 := by decide +kernel
theorem row_1_23 : ThresholdAt 1 23 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 23 0 cell_1_23_0
  | exact S 1 23 1 cell_1_23_1
  | exact S 1 23 2 cell_1_23_2
  | exact S 1 23 3 cell_1_23_3
  | exact S 1 23 4 cell_1_23_4
  | exact S 1 23 5 cell_1_23_5
theorem cell_1_24_0 : C 1 24 0 := by decide +kernel
theorem cell_1_24_1 : C 1 24 1 := by decide +kernel
theorem cell_1_24_2 : C 1 24 2 := by decide +kernel
theorem cell_1_24_3 : C 1 24 3 := by decide +kernel
theorem cell_1_24_4 : C 1 24 4 := by decide +kernel
theorem cell_1_24_5 : C 1 24 5 := by decide +kernel
theorem row_1_24 : ThresholdAt 1 24 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 24 0 cell_1_24_0
  | exact S 1 24 1 cell_1_24_1
  | exact S 1 24 2 cell_1_24_2
  | exact S 1 24 3 cell_1_24_3
  | exact S 1 24 4 cell_1_24_4
  | exact S 1 24 5 cell_1_24_5
theorem cell_1_25_0 : C 1 25 0 := by decide +kernel
theorem cell_1_25_1 : C 1 25 1 := by decide +kernel
theorem cell_1_25_2 : C 1 25 2 := by decide +kernel
theorem cell_1_25_3 : C 1 25 3 := by decide +kernel
theorem cell_1_25_4 : C 1 25 4 := by decide +kernel
theorem cell_1_25_5 : C 1 25 5 := by decide +kernel
theorem row_1_25 : ThresholdAt 1 25 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 25 0 cell_1_25_0
  | exact S 1 25 1 cell_1_25_1
  | exact S 1 25 2 cell_1_25_2
  | exact S 1 25 3 cell_1_25_3
  | exact S 1 25 4 cell_1_25_4
  | exact S 1 25 5 cell_1_25_5
theorem cell_1_26_0 : C 1 26 0 := by decide +kernel
theorem cell_1_26_1 : C 1 26 1 := by decide +kernel
theorem cell_1_26_2 : C 1 26 2 := by decide +kernel
theorem cell_1_26_3 : C 1 26 3 := by decide +kernel
theorem cell_1_26_4 : C 1 26 4 := by decide +kernel
theorem cell_1_26_5 : C 1 26 5 := by decide +kernel
theorem row_1_26 : ThresholdAt 1 26 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 26 0 cell_1_26_0
  | exact S 1 26 1 cell_1_26_1
  | exact S 1 26 2 cell_1_26_2
  | exact S 1 26 3 cell_1_26_3
  | exact S 1 26 4 cell_1_26_4
  | exact S 1 26 5 cell_1_26_5
theorem cell_1_27_0 : C 1 27 0 := by decide +kernel
theorem cell_1_27_1 : C 1 27 1 := by decide +kernel
theorem cell_1_27_2 : C 1 27 2 := by decide +kernel
theorem cell_1_27_3 : C 1 27 3 := by decide +kernel
theorem cell_1_27_4 : C 1 27 4 := by decide +kernel
theorem cell_1_27_5 : C 1 27 5 := by decide +kernel
theorem row_1_27 : ThresholdAt 1 27 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 27 0 cell_1_27_0
  | exact S 1 27 1 cell_1_27_1
  | exact S 1 27 2 cell_1_27_2
  | exact S 1 27 3 cell_1_27_3
  | exact S 1 27 4 cell_1_27_4
  | exact S 1 27 5 cell_1_27_5
theorem cell_1_28_0 : C 1 28 0 := by decide +kernel
theorem cell_1_28_1 : C 1 28 1 := by decide +kernel
theorem cell_1_28_2 : C 1 28 2 := by decide +kernel
theorem cell_1_28_3 : C 1 28 3 := by decide +kernel
theorem cell_1_28_4 : C 1 28 4 := by decide +kernel
theorem cell_1_28_5 : C 1 28 5 := by decide +kernel
theorem row_1_28 : ThresholdAt 1 28 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 28 0 cell_1_28_0
  | exact S 1 28 1 cell_1_28_1
  | exact S 1 28 2 cell_1_28_2
  | exact S 1 28 3 cell_1_28_3
  | exact S 1 28 4 cell_1_28_4
  | exact S 1 28 5 cell_1_28_5
theorem cell_1_29_0 : C 1 29 0 := by decide +kernel
theorem cell_1_29_1 : C 1 29 1 := by decide +kernel
theorem cell_1_29_2 : C 1 29 2 := by decide +kernel
theorem cell_1_29_3 : C 1 29 3 := by decide +kernel
theorem cell_1_29_4 : C 1 29 4 := by decide +kernel
theorem cell_1_29_5 : C 1 29 5 := by decide +kernel
theorem row_1_29 : ThresholdAt 1 29 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 29 0 cell_1_29_0
  | exact S 1 29 1 cell_1_29_1
  | exact S 1 29 2 cell_1_29_2
  | exact S 1 29 3 cell_1_29_3
  | exact S 1 29 4 cell_1_29_4
  | exact S 1 29 5 cell_1_29_5
theorem cell_1_30_0 : C 1 30 0 := by decide +kernel
theorem cell_1_30_1 : C 1 30 1 := by decide +kernel
theorem cell_1_30_2 : C 1 30 2 := by decide +kernel
theorem cell_1_30_3 : C 1 30 3 := by decide +kernel
theorem cell_1_30_4 : C 1 30 4 := by decide +kernel
theorem cell_1_30_5 : C 1 30 5 := by decide +kernel
theorem row_1_30 : ThresholdAt 1 30 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 30 0 cell_1_30_0
  | exact S 1 30 1 cell_1_30_1
  | exact S 1 30 2 cell_1_30_2
  | exact S 1 30 3 cell_1_30_3
  | exact S 1 30 4 cell_1_30_4
  | exact S 1 30 5 cell_1_30_5
theorem cell_1_31_0 : C 1 31 0 := by decide +kernel
theorem cell_1_31_1 : C 1 31 1 := by decide +kernel
theorem cell_1_31_2 : C 1 31 2 := by decide +kernel
theorem cell_1_31_3 : C 1 31 3 := by decide +kernel
theorem cell_1_31_4 : C 1 31 4 := by decide +kernel
theorem cell_1_31_5 : C 1 31 5 := by decide +kernel
theorem row_1_31 : ThresholdAt 1 31 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 31 0 cell_1_31_0
  | exact S 1 31 1 cell_1_31_1
  | exact S 1 31 2 cell_1_31_2
  | exact S 1 31 3 cell_1_31_3
  | exact S 1 31 4 cell_1_31_4
  | exact S 1 31 5 cell_1_31_5
theorem cell_1_32_0 : C 1 32 0 := by decide +kernel
theorem cell_1_32_1 : C 1 32 1 := by decide +kernel
theorem cell_1_32_2 : C 1 32 2 := by decide +kernel
theorem cell_1_32_3 : C 1 32 3 := by decide +kernel
theorem cell_1_32_4 : C 1 32 4 := by decide +kernel
theorem cell_1_32_5 : C 1 32 5 := by decide +kernel
theorem row_1_32 : ThresholdAt 1 32 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 32 0 cell_1_32_0
  | exact S 1 32 1 cell_1_32_1
  | exact S 1 32 2 cell_1_32_2
  | exact S 1 32 3 cell_1_32_3
  | exact S 1 32 4 cell_1_32_4
  | exact S 1 32 5 cell_1_32_5
theorem cell_1_33_0 : C 1 33 0 := by decide +kernel
theorem cell_1_33_1 : C 1 33 1 := by decide +kernel
theorem cell_1_33_2 : C 1 33 2 := by decide +kernel
theorem cell_1_33_3 : C 1 33 3 := by decide +kernel
theorem cell_1_33_4 : C 1 33 4 := by decide +kernel
theorem cell_1_33_5 : C 1 33 5 := by decide +kernel
theorem row_1_33 : ThresholdAt 1 33 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 33 0 cell_1_33_0
  | exact S 1 33 1 cell_1_33_1
  | exact S 1 33 2 cell_1_33_2
  | exact S 1 33 3 cell_1_33_3
  | exact S 1 33 4 cell_1_33_4
  | exact S 1 33 5 cell_1_33_5
theorem cell_1_34_0 : C 1 34 0 := by decide +kernel
theorem cell_1_34_1 : C 1 34 1 := by decide +kernel
theorem cell_1_34_2 : C 1 34 2 := by decide +kernel
theorem cell_1_34_3 : C 1 34 3 := by decide +kernel
theorem cell_1_34_4 : C 1 34 4 := by decide +kernel
theorem cell_1_34_5 : C 1 34 5 := by decide +kernel
theorem row_1_34 : ThresholdAt 1 34 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 34 0 cell_1_34_0
  | exact S 1 34 1 cell_1_34_1
  | exact S 1 34 2 cell_1_34_2
  | exact S 1 34 3 cell_1_34_3
  | exact S 1 34 4 cell_1_34_4
  | exact S 1 34 5 cell_1_34_5
theorem cell_1_35_0 : C 1 35 0 := by decide +kernel
theorem cell_1_35_1 : C 1 35 1 := by decide +kernel
theorem cell_1_35_2 : C 1 35 2 := by decide +kernel
theorem cell_1_35_3 : C 1 35 3 := by decide +kernel
theorem cell_1_35_4 : C 1 35 4 := by decide +kernel
theorem cell_1_35_5 : C 1 35 5 := by decide +kernel
theorem row_1_35 : ThresholdAt 1 35 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 35 0 cell_1_35_0
  | exact S 1 35 1 cell_1_35_1
  | exact S 1 35 2 cell_1_35_2
  | exact S 1 35 3 cell_1_35_3
  | exact S 1 35 4 cell_1_35_4
  | exact S 1 35 5 cell_1_35_5
theorem cell_1_36_0 : C 1 36 0 := by decide +kernel
theorem cell_1_36_1 : C 1 36 1 := by decide +kernel
theorem cell_1_36_2 : C 1 36 2 := by decide +kernel
theorem cell_1_36_3 : C 1 36 3 := by decide +kernel
theorem cell_1_36_4 : C 1 36 4 := by decide +kernel
theorem cell_1_36_5 : C 1 36 5 := by decide +kernel
theorem row_1_36 : ThresholdAt 1 36 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 36 0 cell_1_36_0
  | exact S 1 36 1 cell_1_36_1
  | exact S 1 36 2 cell_1_36_2
  | exact S 1 36 3 cell_1_36_3
  | exact S 1 36 4 cell_1_36_4
  | exact S 1 36 5 cell_1_36_5
theorem cell_1_37_0 : C 1 37 0 := by decide +kernel
theorem cell_1_37_1 : C 1 37 1 := by decide +kernel
theorem cell_1_37_2 : C 1 37 2 := by decide +kernel
theorem cell_1_37_3 : C 1 37 3 := by decide +kernel
theorem cell_1_37_4 : C 1 37 4 := by decide +kernel
theorem cell_1_37_5 : C 1 37 5 := by decide +kernel
theorem row_1_37 : ThresholdAt 1 37 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 37 0 cell_1_37_0
  | exact S 1 37 1 cell_1_37_1
  | exact S 1 37 2 cell_1_37_2
  | exact S 1 37 3 cell_1_37_3
  | exact S 1 37 4 cell_1_37_4
  | exact S 1 37 5 cell_1_37_5
theorem cell_1_38_0 : C 1 38 0 := by decide +kernel
theorem cell_1_38_1 : C 1 38 1 := by decide +kernel
theorem cell_1_38_2 : C 1 38 2 := by decide +kernel
theorem cell_1_38_3 : C 1 38 3 := by decide +kernel
theorem cell_1_38_4 : C 1 38 4 := by decide +kernel
theorem cell_1_38_5 : C 1 38 5 := by decide +kernel
theorem row_1_38 : ThresholdAt 1 38 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 38 0 cell_1_38_0
  | exact S 1 38 1 cell_1_38_1
  | exact S 1 38 2 cell_1_38_2
  | exact S 1 38 3 cell_1_38_3
  | exact S 1 38 4 cell_1_38_4
  | exact S 1 38 5 cell_1_38_5
theorem cell_1_39_0 : C 1 39 0 := by decide +kernel
theorem cell_1_39_1 : C 1 39 1 := by decide +kernel
theorem cell_1_39_2 : C 1 39 2 := by decide +kernel
theorem cell_1_39_3 : C 1 39 3 := by decide +kernel
theorem cell_1_39_4 : C 1 39 4 := by decide +kernel
theorem cell_1_39_5 : C 1 39 5 := by decide +kernel
theorem row_1_39 : ThresholdAt 1 39 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 39 0 cell_1_39_0
  | exact S 1 39 1 cell_1_39_1
  | exact S 1 39 2 cell_1_39_2
  | exact S 1 39 3 cell_1_39_3
  | exact S 1 39 4 cell_1_39_4
  | exact S 1 39 5 cell_1_39_5
theorem cell_1_40_0 : C 1 40 0 := by decide +kernel
theorem cell_1_40_1 : C 1 40 1 := by decide +kernel
theorem cell_1_40_2 : C 1 40 2 := by decide +kernel
theorem cell_1_40_3 : C 1 40 3 := by decide +kernel
theorem cell_1_40_4 : C 1 40 4 := by decide +kernel
theorem cell_1_40_5 : C 1 40 5 := by decide +kernel
theorem row_1_40 : ThresholdAt 1 40 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 40 0 cell_1_40_0
  | exact S 1 40 1 cell_1_40_1
  | exact S 1 40 2 cell_1_40_2
  | exact S 1 40 3 cell_1_40_3
  | exact S 1 40 4 cell_1_40_4
  | exact S 1 40 5 cell_1_40_5
theorem cell_1_41_0 : C 1 41 0 := by decide +kernel
theorem cell_1_41_1 : C 1 41 1 := by decide +kernel
theorem cell_1_41_2 : C 1 41 2 := by decide +kernel
theorem cell_1_41_3 : C 1 41 3 := by decide +kernel
theorem cell_1_41_4 : C 1 41 4 := by decide +kernel
theorem cell_1_41_5 : C 1 41 5 := by decide +kernel
theorem row_1_41 : ThresholdAt 1 41 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 41 0 cell_1_41_0
  | exact S 1 41 1 cell_1_41_1
  | exact S 1 41 2 cell_1_41_2
  | exact S 1 41 3 cell_1_41_3
  | exact S 1 41 4 cell_1_41_4
  | exact S 1 41 5 cell_1_41_5
theorem cell_1_42_0 : C 1 42 0 := by decide +kernel
theorem cell_1_42_1 : C 1 42 1 := by decide +kernel
theorem cell_1_42_2 : C 1 42 2 := by decide +kernel
theorem cell_1_42_3 : C 1 42 3 := by decide +kernel
theorem cell_1_42_4 : C 1 42 4 := by decide +kernel
theorem cell_1_42_5 : C 1 42 5 := by decide +kernel
theorem row_1_42 : ThresholdAt 1 42 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 42 0 cell_1_42_0
  | exact S 1 42 1 cell_1_42_1
  | exact S 1 42 2 cell_1_42_2
  | exact S 1 42 3 cell_1_42_3
  | exact S 1 42 4 cell_1_42_4
  | exact S 1 42 5 cell_1_42_5
theorem cell_1_43_0 : C 1 43 0 := by decide +kernel
theorem cell_1_43_1 : C 1 43 1 := by decide +kernel
theorem cell_1_43_2 : C 1 43 2 := by decide +kernel
theorem cell_1_43_3 : C 1 43 3 := by decide +kernel
theorem cell_1_43_4 : C 1 43 4 := by decide +kernel
theorem cell_1_43_5 : C 1 43 5 := by decide +kernel
theorem row_1_43 : ThresholdAt 1 43 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 43 0 cell_1_43_0
  | exact S 1 43 1 cell_1_43_1
  | exact S 1 43 2 cell_1_43_2
  | exact S 1 43 3 cell_1_43_3
  | exact S 1 43 4 cell_1_43_4
  | exact S 1 43 5 cell_1_43_5
theorem cell_1_44_0 : C 1 44 0 := by decide +kernel
theorem cell_1_44_1 : C 1 44 1 := by decide +kernel
theorem cell_1_44_2 : C 1 44 2 := by decide +kernel
theorem cell_1_44_3 : C 1 44 3 := by decide +kernel
theorem cell_1_44_4 : C 1 44 4 := by decide +kernel
theorem cell_1_44_5 : C 1 44 5 := by decide +kernel
theorem row_1_44 : ThresholdAt 1 44 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 44 0 cell_1_44_0
  | exact S 1 44 1 cell_1_44_1
  | exact S 1 44 2 cell_1_44_2
  | exact S 1 44 3 cell_1_44_3
  | exact S 1 44 4 cell_1_44_4
  | exact S 1 44 5 cell_1_44_5
theorem cell_1_45_0 : C 1 45 0 := by decide +kernel
theorem cell_1_45_1 : C 1 45 1 := by decide +kernel
theorem cell_1_45_2 : C 1 45 2 := by decide +kernel
theorem cell_1_45_3 : C 1 45 3 := by decide +kernel
theorem cell_1_45_4 : C 1 45 4 := by decide +kernel
theorem cell_1_45_5 : C 1 45 5 := by decide +kernel
theorem row_1_45 : ThresholdAt 1 45 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 45 0 cell_1_45_0
  | exact S 1 45 1 cell_1_45_1
  | exact S 1 45 2 cell_1_45_2
  | exact S 1 45 3 cell_1_45_3
  | exact S 1 45 4 cell_1_45_4
  | exact S 1 45 5 cell_1_45_5
theorem cell_1_46_0 : C 1 46 0 := by decide +kernel
theorem cell_1_46_1 : C 1 46 1 := by decide +kernel
theorem cell_1_46_2 : C 1 46 2 := by decide +kernel
theorem cell_1_46_3 : C 1 46 3 := by decide +kernel
theorem cell_1_46_4 : C 1 46 4 := by decide +kernel
theorem cell_1_46_5 : C 1 46 5 := by decide +kernel
theorem row_1_46 : ThresholdAt 1 46 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 46 0 cell_1_46_0
  | exact S 1 46 1 cell_1_46_1
  | exact S 1 46 2 cell_1_46_2
  | exact S 1 46 3 cell_1_46_3
  | exact S 1 46 4 cell_1_46_4
  | exact S 1 46 5 cell_1_46_5
theorem cell_1_47_0 : C 1 47 0 := by decide +kernel
theorem cell_1_47_1 : C 1 47 1 := by decide +kernel
theorem cell_1_47_2 : C 1 47 2 := by decide +kernel
theorem cell_1_47_3 : C 1 47 3 := by decide +kernel
theorem cell_1_47_4 : C 1 47 4 := by decide +kernel
theorem cell_1_47_5 : C 1 47 5 := by decide +kernel
theorem row_1_47 : ThresholdAt 1 47 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 47 0 cell_1_47_0
  | exact S 1 47 1 cell_1_47_1
  | exact S 1 47 2 cell_1_47_2
  | exact S 1 47 3 cell_1_47_3
  | exact S 1 47 4 cell_1_47_4
  | exact S 1 47 5 cell_1_47_5
theorem cell_1_48_0 : C 1 48 0 := by decide +kernel
theorem cell_1_48_1 : C 1 48 1 := by decide +kernel
theorem cell_1_48_2 : C 1 48 2 := by decide +kernel
theorem cell_1_48_3 : C 1 48 3 := by decide +kernel
theorem cell_1_48_4 : C 1 48 4 := by decide +kernel
theorem cell_1_48_5 : C 1 48 5 := by decide +kernel
theorem row_1_48 : ThresholdAt 1 48 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 48 0 cell_1_48_0
  | exact S 1 48 1 cell_1_48_1
  | exact S 1 48 2 cell_1_48_2
  | exact S 1 48 3 cell_1_48_3
  | exact S 1 48 4 cell_1_48_4
  | exact S 1 48 5 cell_1_48_5
theorem cell_1_49_0 : C 1 49 0 := by decide +kernel
theorem cell_1_49_1 : C 1 49 1 := by decide +kernel
theorem cell_1_49_2 : C 1 49 2 := by decide +kernel
theorem cell_1_49_3 : C 1 49 3 := by decide +kernel
theorem cell_1_49_4 : C 1 49 4 := by decide +kernel
theorem cell_1_49_5 : C 1 49 5 := by decide +kernel
theorem row_1_49 : ThresholdAt 1 49 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 49 0 cell_1_49_0
  | exact S 1 49 1 cell_1_49_1
  | exact S 1 49 2 cell_1_49_2
  | exact S 1 49 3 cell_1_49_3
  | exact S 1 49 4 cell_1_49_4
  | exact S 1 49 5 cell_1_49_5
theorem cell_1_50_0 : C 1 50 0 := by decide +kernel
theorem cell_1_50_1 : C 1 50 1 := by decide +kernel
theorem cell_1_50_2 : C 1 50 2 := by decide +kernel
theorem cell_1_50_3 : C 1 50 3 := by decide +kernel
theorem cell_1_50_4 : C 1 50 4 := by decide +kernel
theorem cell_1_50_5 : C 1 50 5 := by decide +kernel
theorem row_1_50 : ThresholdAt 1 50 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 50 0 cell_1_50_0
  | exact S 1 50 1 cell_1_50_1
  | exact S 1 50 2 cell_1_50_2
  | exact S 1 50 3 cell_1_50_3
  | exact S 1 50 4 cell_1_50_4
  | exact S 1 50 5 cell_1_50_5
theorem cell_1_51_0 : C 1 51 0 := by decide +kernel
theorem cell_1_51_1 : C 1 51 1 := by decide +kernel
theorem cell_1_51_2 : C 1 51 2 := by decide +kernel
theorem cell_1_51_3 : C 1 51 3 := by decide +kernel
theorem cell_1_51_4 : C 1 51 4 := by decide +kernel
theorem cell_1_51_5 : C 1 51 5 := by decide +kernel
theorem row_1_51 : ThresholdAt 1 51 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 51 0 cell_1_51_0
  | exact S 1 51 1 cell_1_51_1
  | exact S 1 51 2 cell_1_51_2
  | exact S 1 51 3 cell_1_51_3
  | exact S 1 51 4 cell_1_51_4
  | exact S 1 51 5 cell_1_51_5
theorem cell_1_52_0 : C 1 52 0 := by decide +kernel
theorem cell_1_52_1 : C 1 52 1 := by decide +kernel
theorem cell_1_52_2 : C 1 52 2 := by decide +kernel
theorem cell_1_52_3 : C 1 52 3 := by decide +kernel
theorem cell_1_52_4 : C 1 52 4 := by decide +kernel
theorem cell_1_52_5 : C 1 52 5 := by decide +kernel
theorem row_1_52 : ThresholdAt 1 52 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 52 0 cell_1_52_0
  | exact S 1 52 1 cell_1_52_1
  | exact S 1 52 2 cell_1_52_2
  | exact S 1 52 3 cell_1_52_3
  | exact S 1 52 4 cell_1_52_4
  | exact S 1 52 5 cell_1_52_5
theorem cell_1_53_0 : C 1 53 0 := by decide +kernel
theorem cell_1_53_1 : C 1 53 1 := by decide +kernel
theorem cell_1_53_2 : C 1 53 2 := by decide +kernel
theorem cell_1_53_3 : C 1 53 3 := by decide +kernel
theorem cell_1_53_4 : C 1 53 4 := by decide +kernel
theorem cell_1_53_5 : C 1 53 5 := by decide +kernel
theorem row_1_53 : ThresholdAt 1 53 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 53 0 cell_1_53_0
  | exact S 1 53 1 cell_1_53_1
  | exact S 1 53 2 cell_1_53_2
  | exact S 1 53 3 cell_1_53_3
  | exact S 1 53 4 cell_1_53_4
  | exact S 1 53 5 cell_1_53_5
theorem cell_1_54_0 : C 1 54 0 := by decide +kernel
theorem cell_1_54_1 : C 1 54 1 := by decide +kernel
theorem cell_1_54_2 : C 1 54 2 := by decide +kernel
theorem cell_1_54_3 : C 1 54 3 := by decide +kernel
theorem cell_1_54_4 : C 1 54 4 := by decide +kernel
theorem cell_1_54_5 : C 1 54 5 := by decide +kernel
theorem row_1_54 : ThresholdAt 1 54 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 54 0 cell_1_54_0
  | exact S 1 54 1 cell_1_54_1
  | exact S 1 54 2 cell_1_54_2
  | exact S 1 54 3 cell_1_54_3
  | exact S 1 54 4 cell_1_54_4
  | exact S 1 54 5 cell_1_54_5
theorem cell_1_55_0 : C 1 55 0 := by decide +kernel
theorem cell_1_55_1 : C 1 55 1 := by decide +kernel
theorem cell_1_55_2 : C 1 55 2 := by decide +kernel
theorem cell_1_55_3 : C 1 55 3 := by decide +kernel
theorem cell_1_55_4 : C 1 55 4 := by decide +kernel
theorem cell_1_55_5 : C 1 55 5 := by decide +kernel
theorem row_1_55 : ThresholdAt 1 55 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 55 0 cell_1_55_0
  | exact S 1 55 1 cell_1_55_1
  | exact S 1 55 2 cell_1_55_2
  | exact S 1 55 3 cell_1_55_3
  | exact S 1 55 4 cell_1_55_4
  | exact S 1 55 5 cell_1_55_5
theorem cell_1_56_0 : C 1 56 0 := by decide +kernel
theorem cell_1_56_1 : C 1 56 1 := by decide +kernel
theorem cell_1_56_2 : C 1 56 2 := by decide +kernel
theorem cell_1_56_3 : C 1 56 3 := by decide +kernel
theorem cell_1_56_4 : C 1 56 4 := by decide +kernel
theorem cell_1_56_5 : C 1 56 5 := by decide +kernel
theorem row_1_56 : ThresholdAt 1 56 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 56 0 cell_1_56_0
  | exact S 1 56 1 cell_1_56_1
  | exact S 1 56 2 cell_1_56_2
  | exact S 1 56 3 cell_1_56_3
  | exact S 1 56 4 cell_1_56_4
  | exact S 1 56 5 cell_1_56_5
theorem cell_1_57_0 : C 1 57 0 := by decide +kernel
theorem cell_1_57_1 : C 1 57 1 := by decide +kernel
theorem cell_1_57_2 : C 1 57 2 := by decide +kernel
theorem cell_1_57_3 : C 1 57 3 := by decide +kernel
theorem cell_1_57_4 : C 1 57 4 := by decide +kernel
theorem cell_1_57_5 : C 1 57 5 := by decide +kernel
theorem row_1_57 : ThresholdAt 1 57 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 57 0 cell_1_57_0
  | exact S 1 57 1 cell_1_57_1
  | exact S 1 57 2 cell_1_57_2
  | exact S 1 57 3 cell_1_57_3
  | exact S 1 57 4 cell_1_57_4
  | exact S 1 57 5 cell_1_57_5
theorem cell_1_58_0 : C 1 58 0 := by decide +kernel
theorem cell_1_58_1 : C 1 58 1 := by decide +kernel
theorem cell_1_58_2 : C 1 58 2 := by decide +kernel
theorem cell_1_58_3 : C 1 58 3 := by decide +kernel
theorem cell_1_58_4 : C 1 58 4 := by decide +kernel
theorem cell_1_58_5 : C 1 58 5 := by decide +kernel
theorem row_1_58 : ThresholdAt 1 58 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 58 0 cell_1_58_0
  | exact S 1 58 1 cell_1_58_1
  | exact S 1 58 2 cell_1_58_2
  | exact S 1 58 3 cell_1_58_3
  | exact S 1 58 4 cell_1_58_4
  | exact S 1 58 5 cell_1_58_5
theorem cell_1_59_0 : C 1 59 0 := by decide +kernel
theorem cell_1_59_1 : C 1 59 1 := by decide +kernel
theorem cell_1_59_2 : C 1 59 2 := by decide +kernel
theorem cell_1_59_3 : C 1 59 3 := by decide +kernel
theorem cell_1_59_4 : C 1 59 4 := by decide +kernel
theorem cell_1_59_5 : C 1 59 5 := by decide +kernel
theorem row_1_59 : ThresholdAt 1 59 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 59 0 cell_1_59_0
  | exact S 1 59 1 cell_1_59_1
  | exact S 1 59 2 cell_1_59_2
  | exact S 1 59 3 cell_1_59_3
  | exact S 1 59 4 cell_1_59_4
  | exact S 1 59 5 cell_1_59_5
theorem cell_1_60_0 : C 1 60 0 := by decide +kernel
theorem cell_1_60_1 : C 1 60 1 := by decide +kernel
theorem cell_1_60_2 : C 1 60 2 := by decide +kernel
theorem cell_1_60_3 : C 1 60 3 := by decide +kernel
theorem cell_1_60_4 : C 1 60 4 := by decide +kernel
theorem cell_1_60_5 : C 1 60 5 := by decide +kernel
theorem row_1_60 : ThresholdAt 1 60 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 60 0 cell_1_60_0
  | exact S 1 60 1 cell_1_60_1
  | exact S 1 60 2 cell_1_60_2
  | exact S 1 60 3 cell_1_60_3
  | exact S 1 60 4 cell_1_60_4
  | exact S 1 60 5 cell_1_60_5
theorem cell_1_61_0 : C 1 61 0 := by decide +kernel
theorem cell_1_61_1 : C 1 61 1 := by decide +kernel
theorem cell_1_61_2 : C 1 61 2 := by decide +kernel
theorem cell_1_61_3 : C 1 61 3 := by decide +kernel
theorem cell_1_61_4 : C 1 61 4 := by decide +kernel
theorem cell_1_61_5 : C 1 61 5 := by decide +kernel
theorem row_1_61 : ThresholdAt 1 61 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 61 0 cell_1_61_0
  | exact S 1 61 1 cell_1_61_1
  | exact S 1 61 2 cell_1_61_2
  | exact S 1 61 3 cell_1_61_3
  | exact S 1 61 4 cell_1_61_4
  | exact S 1 61 5 cell_1_61_5
theorem cell_1_62_0 : C 1 62 0 := by decide +kernel
theorem cell_1_62_1 : C 1 62 1 := by decide +kernel
theorem cell_1_62_2 : C 1 62 2 := by decide +kernel
theorem cell_1_62_3 : C 1 62 3 := by decide +kernel
theorem cell_1_62_4 : C 1 62 4 := by decide +kernel
theorem cell_1_62_5 : C 1 62 5 := by decide +kernel
theorem row_1_62 : ThresholdAt 1 62 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 62 0 cell_1_62_0
  | exact S 1 62 1 cell_1_62_1
  | exact S 1 62 2 cell_1_62_2
  | exact S 1 62 3 cell_1_62_3
  | exact S 1 62 4 cell_1_62_4
  | exact S 1 62 5 cell_1_62_5
theorem cell_1_63_0 : C 1 63 0 := by decide +kernel
theorem cell_1_63_1 : C 1 63 1 := by decide +kernel
theorem cell_1_63_2 : C 1 63 2 := by decide +kernel
theorem cell_1_63_3 : C 1 63 3 := by decide +kernel
theorem cell_1_63_4 : C 1 63 4 := by decide +kernel
theorem cell_1_63_5 : C 1 63 5 := by decide +kernel
theorem row_1_63 : ThresholdAt 1 63 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 63 0 cell_1_63_0
  | exact S 1 63 1 cell_1_63_1
  | exact S 1 63 2 cell_1_63_2
  | exact S 1 63 3 cell_1_63_3
  | exact S 1 63 4 cell_1_63_4
  | exact S 1 63 5 cell_1_63_5
theorem cell_1_64_0 : C 1 64 0 := by decide +kernel
theorem cell_1_64_1 : C 1 64 1 := by decide +kernel
theorem cell_1_64_2 : C 1 64 2 := by decide +kernel
theorem cell_1_64_3 : C 1 64 3 := by decide +kernel
theorem cell_1_64_4 : C 1 64 4 := by decide +kernel
theorem cell_1_64_5 : C 1 64 5 := by decide +kernel
theorem row_1_64 : ThresholdAt 1 64 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 64 0 cell_1_64_0
  | exact S 1 64 1 cell_1_64_1
  | exact S 1 64 2 cell_1_64_2
  | exact S 1 64 3 cell_1_64_3
  | exact S 1 64 4 cell_1_64_4
  | exact S 1 64 5 cell_1_64_5
theorem cell_1_65_0 : C 1 65 0 := by decide +kernel
theorem cell_1_65_1 : C 1 65 1 := by decide +kernel
theorem cell_1_65_2 : C 1 65 2 := by decide +kernel
theorem cell_1_65_3 : C 1 65 3 := by decide +kernel
theorem cell_1_65_4 : C 1 65 4 := by decide +kernel
theorem cell_1_65_5 : C 1 65 5 := by decide +kernel
theorem row_1_65 : ThresholdAt 1 65 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 65 0 cell_1_65_0
  | exact S 1 65 1 cell_1_65_1
  | exact S 1 65 2 cell_1_65_2
  | exact S 1 65 3 cell_1_65_3
  | exact S 1 65 4 cell_1_65_4
  | exact S 1 65 5 cell_1_65_5
theorem cell_1_66_0 : C 1 66 0 := by decide +kernel
theorem cell_1_66_1 : C 1 66 1 := by decide +kernel
theorem cell_1_66_2 : C 1 66 2 := by decide +kernel
theorem cell_1_66_3 : C 1 66 3 := by decide +kernel
theorem cell_1_66_4 : C 1 66 4 := by decide +kernel
theorem cell_1_66_5 : C 1 66 5 := by decide +kernel
theorem row_1_66 : ThresholdAt 1 66 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 66 0 cell_1_66_0
  | exact S 1 66 1 cell_1_66_1
  | exact S 1 66 2 cell_1_66_2
  | exact S 1 66 3 cell_1_66_3
  | exact S 1 66 4 cell_1_66_4
  | exact S 1 66 5 cell_1_66_5
theorem cell_1_67_0 : C 1 67 0 := by decide +kernel
theorem cell_1_67_1 : C 1 67 1 := by decide +kernel
theorem cell_1_67_2 : C 1 67 2 := by decide +kernel
theorem cell_1_67_3 : C 1 67 3 := by decide +kernel
theorem cell_1_67_4 : C 1 67 4 := by decide +kernel
theorem cell_1_67_5 : C 1 67 5 := by decide +kernel
theorem row_1_67 : ThresholdAt 1 67 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 67 0 cell_1_67_0
  | exact S 1 67 1 cell_1_67_1
  | exact S 1 67 2 cell_1_67_2
  | exact S 1 67 3 cell_1_67_3
  | exact S 1 67 4 cell_1_67_4
  | exact S 1 67 5 cell_1_67_5
theorem cell_1_68_0 : C 1 68 0 := by decide +kernel
theorem cell_1_68_1 : C 1 68 1 := by decide +kernel
theorem cell_1_68_2 : C 1 68 2 := by decide +kernel
theorem cell_1_68_3 : C 1 68 3 := by decide +kernel
theorem cell_1_68_4 : C 1 68 4 := by decide +kernel
theorem cell_1_68_5 : C 1 68 5 := by decide +kernel
theorem row_1_68 : ThresholdAt 1 68 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 68 0 cell_1_68_0
  | exact S 1 68 1 cell_1_68_1
  | exact S 1 68 2 cell_1_68_2
  | exact S 1 68 3 cell_1_68_3
  | exact S 1 68 4 cell_1_68_4
  | exact S 1 68 5 cell_1_68_5
theorem cell_1_69_0 : C 1 69 0 := by decide +kernel
theorem cell_1_69_1 : C 1 69 1 := by decide +kernel
theorem cell_1_69_2 : C 1 69 2 := by decide +kernel
theorem cell_1_69_3 : C 1 69 3 := by decide +kernel
theorem cell_1_69_4 : C 1 69 4 := by decide +kernel
theorem cell_1_69_5 : C 1 69 5 := by decide +kernel
theorem row_1_69 : ThresholdAt 1 69 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 69 0 cell_1_69_0
  | exact S 1 69 1 cell_1_69_1
  | exact S 1 69 2 cell_1_69_2
  | exact S 1 69 3 cell_1_69_3
  | exact S 1 69 4 cell_1_69_4
  | exact S 1 69 5 cell_1_69_5
theorem cell_1_70_0 : C 1 70 0 := by decide +kernel
theorem cell_1_70_1 : C 1 70 1 := by decide +kernel
theorem cell_1_70_2 : C 1 70 2 := by decide +kernel
theorem cell_1_70_3 : C 1 70 3 := by decide +kernel
theorem cell_1_70_4 : C 1 70 4 := by decide +kernel
theorem cell_1_70_5 : C 1 70 5 := by decide +kernel
theorem row_1_70 : ThresholdAt 1 70 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 70 0 cell_1_70_0
  | exact S 1 70 1 cell_1_70_1
  | exact S 1 70 2 cell_1_70_2
  | exact S 1 70 3 cell_1_70_3
  | exact S 1 70 4 cell_1_70_4
  | exact S 1 70 5 cell_1_70_5
theorem cell_1_71_0 : C 1 71 0 := by decide +kernel
theorem cell_1_71_1 : C 1 71 1 := by decide +kernel
theorem cell_1_71_2 : C 1 71 2 := by decide +kernel
theorem cell_1_71_3 : C 1 71 3 := by decide +kernel
theorem cell_1_71_4 : C 1 71 4 := by decide +kernel
theorem cell_1_71_5 : C 1 71 5 := by decide +kernel
theorem row_1_71 : ThresholdAt 1 71 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 71 0 cell_1_71_0
  | exact S 1 71 1 cell_1_71_1
  | exact S 1 71 2 cell_1_71_2
  | exact S 1 71 3 cell_1_71_3
  | exact S 1 71 4 cell_1_71_4
  | exact S 1 71 5 cell_1_71_5
theorem cell_1_72_0 : C 1 72 0 := by decide +kernel
theorem cell_1_72_1 : C 1 72 1 := by decide +kernel
theorem cell_1_72_2 : C 1 72 2 := by decide +kernel
theorem cell_1_72_3 : C 1 72 3 := by decide +kernel
theorem cell_1_72_4 : C 1 72 4 := by decide +kernel
theorem cell_1_72_5 : C 1 72 5 := by decide +kernel
theorem row_1_72 : ThresholdAt 1 72 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 72 0 cell_1_72_0
  | exact S 1 72 1 cell_1_72_1
  | exact S 1 72 2 cell_1_72_2
  | exact S 1 72 3 cell_1_72_3
  | exact S 1 72 4 cell_1_72_4
  | exact S 1 72 5 cell_1_72_5
theorem cell_1_73_0 : C 1 73 0 := by decide +kernel
theorem cell_1_73_1 : C 1 73 1 := by decide +kernel
theorem cell_1_73_2 : C 1 73 2 := by decide +kernel
theorem cell_1_73_3 : C 1 73 3 := by decide +kernel
theorem cell_1_73_4 : C 1 73 4 := by decide +kernel
theorem cell_1_73_5 : C 1 73 5 := by decide +kernel
theorem row_1_73 : ThresholdAt 1 73 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 73 0 cell_1_73_0
  | exact S 1 73 1 cell_1_73_1
  | exact S 1 73 2 cell_1_73_2
  | exact S 1 73 3 cell_1_73_3
  | exact S 1 73 4 cell_1_73_4
  | exact S 1 73 5 cell_1_73_5
theorem cell_1_74_0 : C 1 74 0 := by decide +kernel
theorem cell_1_74_1 : C 1 74 1 := by decide +kernel
theorem cell_1_74_2 : C 1 74 2 := by decide +kernel
theorem cell_1_74_3 : C 1 74 3 := by decide +kernel
theorem cell_1_74_4 : C 1 74 4 := by decide +kernel
theorem cell_1_74_5 : C 1 74 5 := by decide +kernel
theorem row_1_74 : ThresholdAt 1 74 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 74 0 cell_1_74_0
  | exact S 1 74 1 cell_1_74_1
  | exact S 1 74 2 cell_1_74_2
  | exact S 1 74 3 cell_1_74_3
  | exact S 1 74 4 cell_1_74_4
  | exact S 1 74 5 cell_1_74_5
theorem cell_1_75_0 : C 1 75 0 := by decide +kernel
theorem cell_1_75_1 : C 1 75 1 := by decide +kernel
theorem cell_1_75_2 : C 1 75 2 := by decide +kernel
theorem cell_1_75_3 : C 1 75 3 := by decide +kernel
theorem cell_1_75_4 : C 1 75 4 := by decide +kernel
theorem cell_1_75_5 : C 1 75 5 := by decide +kernel
theorem row_1_75 : ThresholdAt 1 75 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 75 0 cell_1_75_0
  | exact S 1 75 1 cell_1_75_1
  | exact S 1 75 2 cell_1_75_2
  | exact S 1 75 3 cell_1_75_3
  | exact S 1 75 4 cell_1_75_4
  | exact S 1 75 5 cell_1_75_5
theorem cell_1_76_0 : C 1 76 0 := by decide +kernel
theorem cell_1_76_1 : C 1 76 1 := by decide +kernel
theorem cell_1_76_2 : C 1 76 2 := by decide +kernel
theorem cell_1_76_3 : C 1 76 3 := by decide +kernel
theorem cell_1_76_4 : C 1 76 4 := by decide +kernel
theorem cell_1_76_5 : C 1 76 5 := by decide +kernel
theorem row_1_76 : ThresholdAt 1 76 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 76 0 cell_1_76_0
  | exact S 1 76 1 cell_1_76_1
  | exact S 1 76 2 cell_1_76_2
  | exact S 1 76 3 cell_1_76_3
  | exact S 1 76 4 cell_1_76_4
  | exact S 1 76 5 cell_1_76_5
theorem cell_1_77_0 : C 1 77 0 := by decide +kernel
theorem cell_1_77_1 : C 1 77 1 := by decide +kernel
theorem cell_1_77_2 : C 1 77 2 := by decide +kernel
theorem cell_1_77_3 : C 1 77 3 := by decide +kernel
theorem cell_1_77_4 : C 1 77 4 := by decide +kernel
theorem cell_1_77_5 : C 1 77 5 := by decide +kernel
theorem row_1_77 : ThresholdAt 1 77 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 77 0 cell_1_77_0
  | exact S 1 77 1 cell_1_77_1
  | exact S 1 77 2 cell_1_77_2
  | exact S 1 77 3 cell_1_77_3
  | exact S 1 77 4 cell_1_77_4
  | exact S 1 77 5 cell_1_77_5
theorem cell_1_78_0 : C 1 78 0 := by decide +kernel
theorem cell_1_78_1 : C 1 78 1 := by decide +kernel
theorem cell_1_78_2 : C 1 78 2 := by decide +kernel
theorem cell_1_78_3 : C 1 78 3 := by decide +kernel
theorem cell_1_78_4 : C 1 78 4 := by decide +kernel
theorem cell_1_78_5 : C 1 78 5 := by decide +kernel
theorem row_1_78 : ThresholdAt 1 78 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 78 0 cell_1_78_0
  | exact S 1 78 1 cell_1_78_1
  | exact S 1 78 2 cell_1_78_2
  | exact S 1 78 3 cell_1_78_3
  | exact S 1 78 4 cell_1_78_4
  | exact S 1 78 5 cell_1_78_5
theorem cell_1_79_0 : C 1 79 0 := by decide +kernel
theorem cell_1_79_1 : C 1 79 1 := by decide +kernel
theorem cell_1_79_2 : C 1 79 2 := by decide +kernel
theorem cell_1_79_3 : C 1 79 3 := by decide +kernel
theorem cell_1_79_4 : C 1 79 4 := by decide +kernel
theorem cell_1_79_5 : C 1 79 5 := by decide +kernel
theorem row_1_79 : ThresholdAt 1 79 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 79 0 cell_1_79_0
  | exact S 1 79 1 cell_1_79_1
  | exact S 1 79 2 cell_1_79_2
  | exact S 1 79 3 cell_1_79_3
  | exact S 1 79 4 cell_1_79_4
  | exact S 1 79 5 cell_1_79_5
theorem cell_1_80_0 : C 1 80 0 := by decide +kernel
theorem cell_1_80_1 : C 1 80 1 := by decide +kernel
theorem cell_1_80_2 : C 1 80 2 := by decide +kernel
theorem cell_1_80_3 : C 1 80 3 := by decide +kernel
theorem cell_1_80_4 : C 1 80 4 := by decide +kernel
theorem cell_1_80_5 : C 1 80 5 := by decide +kernel
theorem row_1_80 : ThresholdAt 1 80 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 80 0 cell_1_80_0
  | exact S 1 80 1 cell_1_80_1
  | exact S 1 80 2 cell_1_80_2
  | exact S 1 80 3 cell_1_80_3
  | exact S 1 80 4 cell_1_80_4
  | exact S 1 80 5 cell_1_80_5
theorem cell_1_81_0 : C 1 81 0 := by decide +kernel
theorem cell_1_81_1 : C 1 81 1 := by decide +kernel
theorem cell_1_81_2 : C 1 81 2 := by decide +kernel
theorem cell_1_81_3 : C 1 81 3 := by decide +kernel
theorem cell_1_81_4 : C 1 81 4 := by decide +kernel
theorem cell_1_81_5 : C 1 81 5 := by decide +kernel
theorem row_1_81 : ThresholdAt 1 81 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 81 0 cell_1_81_0
  | exact S 1 81 1 cell_1_81_1
  | exact S 1 81 2 cell_1_81_2
  | exact S 1 81 3 cell_1_81_3
  | exact S 1 81 4 cell_1_81_4
  | exact S 1 81 5 cell_1_81_5
theorem cell_1_82_0 : C 1 82 0 := by decide +kernel
theorem cell_1_82_1 : C 1 82 1 := by decide +kernel
theorem cell_1_82_2 : C 1 82 2 := by decide +kernel
theorem cell_1_82_3 : C 1 82 3 := by decide +kernel
theorem cell_1_82_4 : C 1 82 4 := by decide +kernel
theorem cell_1_82_5 : C 1 82 5 := by decide +kernel
theorem row_1_82 : ThresholdAt 1 82 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 82 0 cell_1_82_0
  | exact S 1 82 1 cell_1_82_1
  | exact S 1 82 2 cell_1_82_2
  | exact S 1 82 3 cell_1_82_3
  | exact S 1 82 4 cell_1_82_4
  | exact S 1 82 5 cell_1_82_5
theorem cell_1_83_0 : C 1 83 0 := by decide +kernel
theorem cell_1_83_1 : C 1 83 1 := by decide +kernel
theorem cell_1_83_2 : C 1 83 2 := by decide +kernel
theorem cell_1_83_3 : C 1 83 3 := by decide +kernel
theorem cell_1_83_4 : C 1 83 4 := by decide +kernel
theorem cell_1_83_5 : C 1 83 5 := by decide +kernel
theorem row_1_83 : ThresholdAt 1 83 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 83 0 cell_1_83_0
  | exact S 1 83 1 cell_1_83_1
  | exact S 1 83 2 cell_1_83_2
  | exact S 1 83 3 cell_1_83_3
  | exact S 1 83 4 cell_1_83_4
  | exact S 1 83 5 cell_1_83_5
theorem cell_1_84_0 : C 1 84 0 := by decide +kernel
theorem cell_1_84_1 : C 1 84 1 := by decide +kernel
theorem cell_1_84_2 : C 1 84 2 := by decide +kernel
theorem cell_1_84_3 : C 1 84 3 := by decide +kernel
theorem cell_1_84_4 : C 1 84 4 := by decide +kernel
theorem cell_1_84_5 : C 1 84 5 := by decide +kernel
theorem row_1_84 : ThresholdAt 1 84 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 84 0 cell_1_84_0
  | exact S 1 84 1 cell_1_84_1
  | exact S 1 84 2 cell_1_84_2
  | exact S 1 84 3 cell_1_84_3
  | exact S 1 84 4 cell_1_84_4
  | exact S 1 84 5 cell_1_84_5
theorem cell_1_85_0 : C 1 85 0 := by decide +kernel
theorem cell_1_85_1 : C 1 85 1 := by decide +kernel
theorem cell_1_85_2 : C 1 85 2 := by decide +kernel
theorem cell_1_85_3 : C 1 85 3 := by decide +kernel
theorem cell_1_85_4 : C 1 85 4 := by decide +kernel
theorem cell_1_85_5 : C 1 85 5 := by decide +kernel
theorem row_1_85 : ThresholdAt 1 85 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 85 0 cell_1_85_0
  | exact S 1 85 1 cell_1_85_1
  | exact S 1 85 2 cell_1_85_2
  | exact S 1 85 3 cell_1_85_3
  | exact S 1 85 4 cell_1_85_4
  | exact S 1 85 5 cell_1_85_5
theorem cell_1_86_0 : C 1 86 0 := by decide +kernel
theorem cell_1_86_1 : C 1 86 1 := by decide +kernel
theorem cell_1_86_2 : C 1 86 2 := by decide +kernel
theorem cell_1_86_3 : C 1 86 3 := by decide +kernel
theorem cell_1_86_4 : C 1 86 4 := by decide +kernel
theorem cell_1_86_5 : C 1 86 5 := by decide +kernel
theorem row_1_86 : ThresholdAt 1 86 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 86 0 cell_1_86_0
  | exact S 1 86 1 cell_1_86_1
  | exact S 1 86 2 cell_1_86_2
  | exact S 1 86 3 cell_1_86_3
  | exact S 1 86 4 cell_1_86_4
  | exact S 1 86 5 cell_1_86_5
theorem cell_1_87_0 : C 1 87 0 := by decide +kernel
theorem cell_1_87_1 : C 1 87 1 := by decide +kernel
theorem cell_1_87_2 : C 1 87 2 := by decide +kernel
theorem cell_1_87_3 : C 1 87 3 := by decide +kernel
theorem cell_1_87_4 : C 1 87 4 := by decide +kernel
theorem cell_1_87_5 : C 1 87 5 := by decide +kernel
theorem row_1_87 : ThresholdAt 1 87 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 87 0 cell_1_87_0
  | exact S 1 87 1 cell_1_87_1
  | exact S 1 87 2 cell_1_87_2
  | exact S 1 87 3 cell_1_87_3
  | exact S 1 87 4 cell_1_87_4
  | exact S 1 87 5 cell_1_87_5
theorem cell_1_88_0 : C 1 88 0 := by decide +kernel
theorem cell_1_88_1 : C 1 88 1 := by decide +kernel
theorem cell_1_88_2 : C 1 88 2 := by decide +kernel
theorem cell_1_88_3 : C 1 88 3 := by decide +kernel
theorem cell_1_88_4 : C 1 88 4 := by decide +kernel
theorem cell_1_88_5 : C 1 88 5 := by decide +kernel
theorem row_1_88 : ThresholdAt 1 88 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 88 0 cell_1_88_0
  | exact S 1 88 1 cell_1_88_1
  | exact S 1 88 2 cell_1_88_2
  | exact S 1 88 3 cell_1_88_3
  | exact S 1 88 4 cell_1_88_4
  | exact S 1 88 5 cell_1_88_5
theorem cell_1_89_0 : C 1 89 0 := by decide +kernel
theorem cell_1_89_1 : C 1 89 1 := by decide +kernel
theorem cell_1_89_2 : C 1 89 2 := by decide +kernel
theorem cell_1_89_3 : C 1 89 3 := by decide +kernel
theorem cell_1_89_4 : C 1 89 4 := by decide +kernel
theorem cell_1_89_5 : C 1 89 5 := by decide +kernel
theorem row_1_89 : ThresholdAt 1 89 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 89 0 cell_1_89_0
  | exact S 1 89 1 cell_1_89_1
  | exact S 1 89 2 cell_1_89_2
  | exact S 1 89 3 cell_1_89_3
  | exact S 1 89 4 cell_1_89_4
  | exact S 1 89 5 cell_1_89_5
theorem cell_1_90_0 : C 1 90 0 := by decide +kernel
theorem cell_1_90_1 : C 1 90 1 := by decide +kernel
theorem cell_1_90_2 : C 1 90 2 := by decide +kernel
theorem cell_1_90_3 : C 1 90 3 := by decide +kernel
theorem cell_1_90_4 : C 1 90 4 := by decide +kernel
theorem cell_1_90_5 : C 1 90 5 := by decide +kernel
theorem row_1_90 : ThresholdAt 1 90 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 90 0 cell_1_90_0
  | exact S 1 90 1 cell_1_90_1
  | exact S 1 90 2 cell_1_90_2
  | exact S 1 90 3 cell_1_90_3
  | exact S 1 90 4 cell_1_90_4
  | exact S 1 90 5 cell_1_90_5
theorem cell_1_91_0 : C 1 91 0 := by decide +kernel
theorem cell_1_91_1 : C 1 91 1 := by decide +kernel
theorem cell_1_91_2 : C 1 91 2 := by decide +kernel
theorem cell_1_91_3 : C 1 91 3 := by decide +kernel
theorem cell_1_91_4 : C 1 91 4 := by decide +kernel
theorem cell_1_91_5 : C 1 91 5 := by decide +kernel
theorem row_1_91 : ThresholdAt 1 91 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 91 0 cell_1_91_0
  | exact S 1 91 1 cell_1_91_1
  | exact S 1 91 2 cell_1_91_2
  | exact S 1 91 3 cell_1_91_3
  | exact S 1 91 4 cell_1_91_4
  | exact S 1 91 5 cell_1_91_5
theorem cell_1_92_0 : C 1 92 0 := by decide +kernel
theorem cell_1_92_1 : C 1 92 1 := by decide +kernel
theorem cell_1_92_2 : C 1 92 2 := by decide +kernel
theorem cell_1_92_3 : C 1 92 3 := by decide +kernel
theorem cell_1_92_4 : C 1 92 4 := by decide +kernel
theorem cell_1_92_5 : C 1 92 5 := by decide +kernel
theorem row_1_92 : ThresholdAt 1 92 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 92 0 cell_1_92_0
  | exact S 1 92 1 cell_1_92_1
  | exact S 1 92 2 cell_1_92_2
  | exact S 1 92 3 cell_1_92_3
  | exact S 1 92 4 cell_1_92_4
  | exact S 1 92 5 cell_1_92_5
theorem cell_1_93_0 : C 1 93 0 := by decide +kernel
theorem cell_1_93_1 : C 1 93 1 := by decide +kernel
theorem cell_1_93_2 : C 1 93 2 := by decide +kernel
theorem cell_1_93_3 : C 1 93 3 := by decide +kernel
theorem cell_1_93_4 : C 1 93 4 := by decide +kernel
theorem cell_1_93_5 : C 1 93 5 := by decide +kernel
theorem row_1_93 : ThresholdAt 1 93 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 93 0 cell_1_93_0
  | exact S 1 93 1 cell_1_93_1
  | exact S 1 93 2 cell_1_93_2
  | exact S 1 93 3 cell_1_93_3
  | exact S 1 93 4 cell_1_93_4
  | exact S 1 93 5 cell_1_93_5
theorem cell_1_94_0 : C 1 94 0 := by decide +kernel
theorem cell_1_94_1 : C 1 94 1 := by decide +kernel
theorem cell_1_94_2 : C 1 94 2 := by decide +kernel
theorem cell_1_94_3 : C 1 94 3 := by decide +kernel
theorem cell_1_94_4 : C 1 94 4 := by decide +kernel
theorem cell_1_94_5 : C 1 94 5 := by decide +kernel
theorem row_1_94 : ThresholdAt 1 94 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 94 0 cell_1_94_0
  | exact S 1 94 1 cell_1_94_1
  | exact S 1 94 2 cell_1_94_2
  | exact S 1 94 3 cell_1_94_3
  | exact S 1 94 4 cell_1_94_4
  | exact S 1 94 5 cell_1_94_5
theorem cell_1_95_0 : C 1 95 0 := by decide +kernel
theorem cell_1_95_1 : C 1 95 1 := by decide +kernel
theorem cell_1_95_2 : C 1 95 2 := by decide +kernel
theorem cell_1_95_3 : C 1 95 3 := by decide +kernel
theorem cell_1_95_4 : C 1 95 4 := by decide +kernel
theorem cell_1_95_5 : C 1 95 5 := by decide +kernel
theorem row_1_95 : ThresholdAt 1 95 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 95 0 cell_1_95_0
  | exact S 1 95 1 cell_1_95_1
  | exact S 1 95 2 cell_1_95_2
  | exact S 1 95 3 cell_1_95_3
  | exact S 1 95 4 cell_1_95_4
  | exact S 1 95 5 cell_1_95_5
theorem cell_1_96_0 : C 1 96 0 := by decide +kernel
theorem cell_1_96_1 : C 1 96 1 := by decide +kernel
theorem cell_1_96_2 : C 1 96 2 := by decide +kernel
theorem cell_1_96_3 : C 1 96 3 := by decide +kernel
theorem cell_1_96_4 : C 1 96 4 := by decide +kernel
theorem cell_1_96_5 : C 1 96 5 := by decide +kernel
theorem row_1_96 : ThresholdAt 1 96 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 96 0 cell_1_96_0
  | exact S 1 96 1 cell_1_96_1
  | exact S 1 96 2 cell_1_96_2
  | exact S 1 96 3 cell_1_96_3
  | exact S 1 96 4 cell_1_96_4
  | exact S 1 96 5 cell_1_96_5
theorem cell_1_97_0 : C 1 97 0 := by decide +kernel
theorem cell_1_97_1 : C 1 97 1 := by decide +kernel
theorem cell_1_97_2 : C 1 97 2 := by decide +kernel
theorem cell_1_97_3 : C 1 97 3 := by decide +kernel
theorem cell_1_97_4 : C 1 97 4 := by decide +kernel
theorem cell_1_97_5 : C 1 97 5 := by decide +kernel
theorem row_1_97 : ThresholdAt 1 97 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 97 0 cell_1_97_0
  | exact S 1 97 1 cell_1_97_1
  | exact S 1 97 2 cell_1_97_2
  | exact S 1 97 3 cell_1_97_3
  | exact S 1 97 4 cell_1_97_4
  | exact S 1 97 5 cell_1_97_5
theorem cell_1_98_0 : C 1 98 0 := by decide +kernel
theorem cell_1_98_1 : C 1 98 1 := by decide +kernel
theorem cell_1_98_2 : C 1 98 2 := by decide +kernel
theorem cell_1_98_3 : C 1 98 3 := by decide +kernel
theorem cell_1_98_4 : C 1 98 4 := by decide +kernel
theorem cell_1_98_5 : C 1 98 5 := by decide +kernel
theorem row_1_98 : ThresholdAt 1 98 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 98 0 cell_1_98_0
  | exact S 1 98 1 cell_1_98_1
  | exact S 1 98 2 cell_1_98_2
  | exact S 1 98 3 cell_1_98_3
  | exact S 1 98 4 cell_1_98_4
  | exact S 1 98 5 cell_1_98_5
theorem cell_1_99_0 : C 1 99 0 := by decide +kernel
theorem cell_1_99_1 : C 1 99 1 := by decide +kernel
theorem cell_1_99_2 : C 1 99 2 := by decide +kernel
theorem cell_1_99_3 : C 1 99 3 := by decide +kernel
theorem cell_1_99_4 : C 1 99 4 := by decide +kernel
theorem cell_1_99_5 : C 1 99 5 := by decide +kernel
theorem row_1_99 : ThresholdAt 1 99 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 99 0 cell_1_99_0
  | exact S 1 99 1 cell_1_99_1
  | exact S 1 99 2 cell_1_99_2
  | exact S 1 99 3 cell_1_99_3
  | exact S 1 99 4 cell_1_99_4
  | exact S 1 99 5 cell_1_99_5
theorem cell_1_100_0 : C 1 100 0 := by decide +kernel
theorem cell_1_100_1 : C 1 100 1 := by decide +kernel
theorem cell_1_100_2 : C 1 100 2 := by decide +kernel
theorem cell_1_100_3 : C 1 100 3 := by decide +kernel
theorem cell_1_100_4 : C 1 100 4 := by decide +kernel
theorem cell_1_100_5 : C 1 100 5 := by decide +kernel
theorem row_1_100 : ThresholdAt 1 100 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 100 0 cell_1_100_0
  | exact S 1 100 1 cell_1_100_1
  | exact S 1 100 2 cell_1_100_2
  | exact S 1 100 3 cell_1_100_3
  | exact S 1 100 4 cell_1_100_4
  | exact S 1 100 5 cell_1_100_5
theorem cell_1_101_0 : C 1 101 0 := by decide +kernel
theorem cell_1_101_1 : C 1 101 1 := by decide +kernel
theorem cell_1_101_2 : C 1 101 2 := by decide +kernel
theorem cell_1_101_3 : C 1 101 3 := by decide +kernel
theorem cell_1_101_4 : C 1 101 4 := by decide +kernel
theorem cell_1_101_5 : C 1 101 5 := by decide +kernel
theorem row_1_101 : ThresholdAt 1 101 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 101 0 cell_1_101_0
  | exact S 1 101 1 cell_1_101_1
  | exact S 1 101 2 cell_1_101_2
  | exact S 1 101 3 cell_1_101_3
  | exact S 1 101 4 cell_1_101_4
  | exact S 1 101 5 cell_1_101_5
theorem cell_1_102_0 : C 1 102 0 := by decide +kernel
theorem cell_1_102_1 : C 1 102 1 := by decide +kernel
theorem cell_1_102_2 : C 1 102 2 := by decide +kernel
theorem cell_1_102_3 : C 1 102 3 := by decide +kernel
theorem cell_1_102_4 : C 1 102 4 := by decide +kernel
theorem cell_1_102_5 : C 1 102 5 := by decide +kernel
theorem row_1_102 : ThresholdAt 1 102 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 102 0 cell_1_102_0
  | exact S 1 102 1 cell_1_102_1
  | exact S 1 102 2 cell_1_102_2
  | exact S 1 102 3 cell_1_102_3
  | exact S 1 102 4 cell_1_102_4
  | exact S 1 102 5 cell_1_102_5
theorem cell_1_103_0 : C 1 103 0 := by decide +kernel
theorem cell_1_103_1 : C 1 103 1 := by decide +kernel
theorem cell_1_103_2 : C 1 103 2 := by decide +kernel
theorem cell_1_103_3 : C 1 103 3 := by decide +kernel
theorem cell_1_103_4 : C 1 103 4 := by decide +kernel
theorem cell_1_103_5 : C 1 103 5 := by decide +kernel
theorem row_1_103 : ThresholdAt 1 103 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 103 0 cell_1_103_0
  | exact S 1 103 1 cell_1_103_1
  | exact S 1 103 2 cell_1_103_2
  | exact S 1 103 3 cell_1_103_3
  | exact S 1 103 4 cell_1_103_4
  | exact S 1 103 5 cell_1_103_5
theorem cell_1_104_0 : C 1 104 0 := by decide +kernel
theorem cell_1_104_1 : C 1 104 1 := by decide +kernel
theorem cell_1_104_2 : C 1 104 2 := by decide +kernel
theorem cell_1_104_3 : C 1 104 3 := by decide +kernel
theorem cell_1_104_4 : C 1 104 4 := by decide +kernel
theorem cell_1_104_5 : C 1 104 5 := by decide +kernel
theorem row_1_104 : ThresholdAt 1 104 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 104 0 cell_1_104_0
  | exact S 1 104 1 cell_1_104_1
  | exact S 1 104 2 cell_1_104_2
  | exact S 1 104 3 cell_1_104_3
  | exact S 1 104 4 cell_1_104_4
  | exact S 1 104 5 cell_1_104_5
theorem cell_1_105_0 : C 1 105 0 := by decide +kernel
theorem cell_1_105_1 : C 1 105 1 := by decide +kernel
theorem cell_1_105_2 : C 1 105 2 := by decide +kernel
theorem cell_1_105_3 : C 1 105 3 := by decide +kernel
theorem cell_1_105_4 : C 1 105 4 := by decide +kernel
theorem cell_1_105_5 : C 1 105 5 := by decide +kernel
theorem row_1_105 : ThresholdAt 1 105 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 105 0 cell_1_105_0
  | exact S 1 105 1 cell_1_105_1
  | exact S 1 105 2 cell_1_105_2
  | exact S 1 105 3 cell_1_105_3
  | exact S 1 105 4 cell_1_105_4
  | exact S 1 105 5 cell_1_105_5
theorem cell_1_106_0 : C 1 106 0 := by decide +kernel
theorem cell_1_106_1 : C 1 106 1 := by decide +kernel
theorem cell_1_106_2 : C 1 106 2 := by decide +kernel
theorem cell_1_106_3 : C 1 106 3 := by decide +kernel
theorem cell_1_106_4 : C 1 106 4 := by decide +kernel
theorem cell_1_106_5 : C 1 106 5 := by decide +kernel
theorem row_1_106 : ThresholdAt 1 106 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 106 0 cell_1_106_0
  | exact S 1 106 1 cell_1_106_1
  | exact S 1 106 2 cell_1_106_2
  | exact S 1 106 3 cell_1_106_3
  | exact S 1 106 4 cell_1_106_4
  | exact S 1 106 5 cell_1_106_5
theorem cell_1_107_0 : C 1 107 0 := by decide +kernel
theorem cell_1_107_1 : C 1 107 1 := by decide +kernel
theorem cell_1_107_2 : C 1 107 2 := by decide +kernel
theorem cell_1_107_3 : C 1 107 3 := by decide +kernel
theorem cell_1_107_4 : C 1 107 4 := by decide +kernel
theorem cell_1_107_5 : C 1 107 5 := by decide +kernel
theorem row_1_107 : ThresholdAt 1 107 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 107 0 cell_1_107_0
  | exact S 1 107 1 cell_1_107_1
  | exact S 1 107 2 cell_1_107_2
  | exact S 1 107 3 cell_1_107_3
  | exact S 1 107 4 cell_1_107_4
  | exact S 1 107 5 cell_1_107_5
theorem cell_1_108_0 : C 1 108 0 := by decide +kernel
theorem cell_1_108_1 : C 1 108 1 := by decide +kernel
theorem cell_1_108_2 : C 1 108 2 := by decide +kernel
theorem cell_1_108_3 : C 1 108 3 := by decide +kernel
theorem cell_1_108_4 : C 1 108 4 := by decide +kernel
theorem cell_1_108_5 : C 1 108 5 := by decide +kernel
theorem row_1_108 : ThresholdAt 1 108 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 108 0 cell_1_108_0
  | exact S 1 108 1 cell_1_108_1
  | exact S 1 108 2 cell_1_108_2
  | exact S 1 108 3 cell_1_108_3
  | exact S 1 108 4 cell_1_108_4
  | exact S 1 108 5 cell_1_108_5
theorem cell_1_109_0 : C 1 109 0 := by decide +kernel
theorem cell_1_109_1 : C 1 109 1 := by decide +kernel
theorem cell_1_109_2 : C 1 109 2 := by decide +kernel
theorem cell_1_109_3 : C 1 109 3 := by decide +kernel
theorem cell_1_109_4 : C 1 109 4 := by decide +kernel
theorem cell_1_109_5 : C 1 109 5 := by decide +kernel
theorem row_1_109 : ThresholdAt 1 109 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 109 0 cell_1_109_0
  | exact S 1 109 1 cell_1_109_1
  | exact S 1 109 2 cell_1_109_2
  | exact S 1 109 3 cell_1_109_3
  | exact S 1 109 4 cell_1_109_4
  | exact S 1 109 5 cell_1_109_5
theorem cell_1_110_0 : C 1 110 0 := by decide +kernel
theorem cell_1_110_1 : C 1 110 1 := by decide +kernel
theorem cell_1_110_2 : C 1 110 2 := by decide +kernel
theorem cell_1_110_3 : C 1 110 3 := by decide +kernel
theorem cell_1_110_4 : C 1 110 4 := by decide +kernel
theorem cell_1_110_5 : C 1 110 5 := by decide +kernel
theorem row_1_110 : ThresholdAt 1 110 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 110 0 cell_1_110_0
  | exact S 1 110 1 cell_1_110_1
  | exact S 1 110 2 cell_1_110_2
  | exact S 1 110 3 cell_1_110_3
  | exact S 1 110 4 cell_1_110_4
  | exact S 1 110 5 cell_1_110_5
theorem cell_1_111_0 : C 1 111 0 := by decide +kernel
theorem cell_1_111_1 : C 1 111 1 := by decide +kernel
theorem cell_1_111_2 : C 1 111 2 := by decide +kernel
theorem cell_1_111_3 : C 1 111 3 := by decide +kernel
theorem cell_1_111_4 : C 1 111 4 := by decide +kernel
theorem cell_1_111_5 : C 1 111 5 := by decide +kernel
theorem row_1_111 : ThresholdAt 1 111 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 111 0 cell_1_111_0
  | exact S 1 111 1 cell_1_111_1
  | exact S 1 111 2 cell_1_111_2
  | exact S 1 111 3 cell_1_111_3
  | exact S 1 111 4 cell_1_111_4
  | exact S 1 111 5 cell_1_111_5
theorem cell_1_112_0 : C 1 112 0 := by decide +kernel
theorem cell_1_112_1 : C 1 112 1 := by decide +kernel
theorem cell_1_112_2 : C 1 112 2 := by decide +kernel
theorem cell_1_112_3 : C 1 112 3 := by decide +kernel
theorem cell_1_112_4 : C 1 112 4 := by decide +kernel
theorem cell_1_112_5 : C 1 112 5 := by decide +kernel
theorem row_1_112 : ThresholdAt 1 112 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 112 0 cell_1_112_0
  | exact S 1 112 1 cell_1_112_1
  | exact S 1 112 2 cell_1_112_2
  | exact S 1 112 3 cell_1_112_3
  | exact S 1 112 4 cell_1_112_4
  | exact S 1 112 5 cell_1_112_5
theorem cell_1_113_0 : C 1 113 0 := by decide +kernel
theorem cell_1_113_1 : C 1 113 1 := by decide +kernel
theorem cell_1_113_2 : C 1 113 2 := by decide +kernel
theorem cell_1_113_3 : C 1 113 3 := by decide +kernel
theorem cell_1_113_4 : C 1 113 4 := by decide +kernel
theorem cell_1_113_5 : C 1 113 5 := by decide +kernel
theorem row_1_113 : ThresholdAt 1 113 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 113 0 cell_1_113_0
  | exact S 1 113 1 cell_1_113_1
  | exact S 1 113 2 cell_1_113_2
  | exact S 1 113 3 cell_1_113_3
  | exact S 1 113 4 cell_1_113_4
  | exact S 1 113 5 cell_1_113_5
theorem cell_1_114_0 : C 1 114 0 := by decide +kernel
theorem cell_1_114_1 : C 1 114 1 := by decide +kernel
theorem cell_1_114_2 : C 1 114 2 := by decide +kernel
theorem cell_1_114_3 : C 1 114 3 := by decide +kernel
theorem cell_1_114_4 : C 1 114 4 := by decide +kernel
theorem cell_1_114_5 : C 1 114 5 := by decide +kernel
theorem row_1_114 : ThresholdAt 1 114 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 114 0 cell_1_114_0
  | exact S 1 114 1 cell_1_114_1
  | exact S 1 114 2 cell_1_114_2
  | exact S 1 114 3 cell_1_114_3
  | exact S 1 114 4 cell_1_114_4
  | exact S 1 114 5 cell_1_114_5
theorem cell_1_115_0 : C 1 115 0 := by decide +kernel
theorem cell_1_115_1 : C 1 115 1 := by decide +kernel
theorem cell_1_115_2 : C 1 115 2 := by decide +kernel
theorem cell_1_115_3 : C 1 115 3 := by decide +kernel
theorem cell_1_115_4 : C 1 115 4 := by decide +kernel
theorem cell_1_115_5 : C 1 115 5 := by decide +kernel
theorem row_1_115 : ThresholdAt 1 115 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 115 0 cell_1_115_0
  | exact S 1 115 1 cell_1_115_1
  | exact S 1 115 2 cell_1_115_2
  | exact S 1 115 3 cell_1_115_3
  | exact S 1 115 4 cell_1_115_4
  | exact S 1 115 5 cell_1_115_5
theorem cell_1_116_0 : C 1 116 0 := by decide +kernel
theorem cell_1_116_1 : C 1 116 1 := by decide +kernel
theorem cell_1_116_2 : C 1 116 2 := by decide +kernel
theorem cell_1_116_3 : C 1 116 3 := by decide +kernel
theorem cell_1_116_4 : C 1 116 4 := by decide +kernel
theorem cell_1_116_5 : C 1 116 5 := by decide +kernel
theorem row_1_116 : ThresholdAt 1 116 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 116 0 cell_1_116_0
  | exact S 1 116 1 cell_1_116_1
  | exact S 1 116 2 cell_1_116_2
  | exact S 1 116 3 cell_1_116_3
  | exact S 1 116 4 cell_1_116_4
  | exact S 1 116 5 cell_1_116_5
theorem cell_1_117_0 : C 1 117 0 := by decide +kernel
theorem cell_1_117_1 : C 1 117 1 := by decide +kernel
theorem cell_1_117_2 : C 1 117 2 := by decide +kernel
theorem cell_1_117_3 : C 1 117 3 := by decide +kernel
theorem cell_1_117_4 : C 1 117 4 := by decide +kernel
theorem cell_1_117_5 : C 1 117 5 := by decide +kernel
theorem row_1_117 : ThresholdAt 1 117 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 117 0 cell_1_117_0
  | exact S 1 117 1 cell_1_117_1
  | exact S 1 117 2 cell_1_117_2
  | exact S 1 117 3 cell_1_117_3
  | exact S 1 117 4 cell_1_117_4
  | exact S 1 117 5 cell_1_117_5
theorem cell_1_118_0 : C 1 118 0 := by decide +kernel
theorem cell_1_118_1 : C 1 118 1 := by decide +kernel
theorem cell_1_118_2 : C 1 118 2 := by decide +kernel
theorem cell_1_118_3 : C 1 118 3 := by decide +kernel
theorem cell_1_118_4 : C 1 118 4 := by decide +kernel
theorem cell_1_118_5 : C 1 118 5 := by decide +kernel
theorem row_1_118 : ThresholdAt 1 118 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 118 0 cell_1_118_0
  | exact S 1 118 1 cell_1_118_1
  | exact S 1 118 2 cell_1_118_2
  | exact S 1 118 3 cell_1_118_3
  | exact S 1 118 4 cell_1_118_4
  | exact S 1 118 5 cell_1_118_5
theorem cell_1_119_0 : C 1 119 0 := by decide +kernel
theorem cell_1_119_1 : C 1 119 1 := by decide +kernel
theorem cell_1_119_2 : C 1 119 2 := by decide +kernel
theorem cell_1_119_3 : C 1 119 3 := by decide +kernel
theorem cell_1_119_4 : C 1 119 4 := by decide +kernel
theorem cell_1_119_5 : C 1 119 5 := by decide +kernel
theorem row_1_119 : ThresholdAt 1 119 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 119 0 cell_1_119_0
  | exact S 1 119 1 cell_1_119_1
  | exact S 1 119 2 cell_1_119_2
  | exact S 1 119 3 cell_1_119_3
  | exact S 1 119 4 cell_1_119_4
  | exact S 1 119 5 cell_1_119_5
theorem cell_1_120_0 : C 1 120 0 := by decide +kernel
theorem cell_1_120_1 : C 1 120 1 := by decide +kernel
theorem cell_1_120_2 : C 1 120 2 := by decide +kernel
theorem cell_1_120_3 : C 1 120 3 := by decide +kernel
theorem cell_1_120_4 : C 1 120 4 := by decide +kernel
theorem cell_1_120_5 : C 1 120 5 := by decide +kernel
theorem row_1_120 : ThresholdAt 1 120 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 120 0 cell_1_120_0
  | exact S 1 120 1 cell_1_120_1
  | exact S 1 120 2 cell_1_120_2
  | exact S 1 120 3 cell_1_120_3
  | exact S 1 120 4 cell_1_120_4
  | exact S 1 120 5 cell_1_120_5
theorem cell_1_121_0 : C 1 121 0 := by decide +kernel
theorem cell_1_121_1 : C 1 121 1 := by decide +kernel
theorem cell_1_121_2 : C 1 121 2 := by decide +kernel
theorem cell_1_121_3 : C 1 121 3 := by decide +kernel
theorem cell_1_121_4 : C 1 121 4 := by decide +kernel
theorem cell_1_121_5 : C 1 121 5 := by decide +kernel
theorem row_1_121 : ThresholdAt 1 121 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 121 0 cell_1_121_0
  | exact S 1 121 1 cell_1_121_1
  | exact S 1 121 2 cell_1_121_2
  | exact S 1 121 3 cell_1_121_3
  | exact S 1 121 4 cell_1_121_4
  | exact S 1 121 5 cell_1_121_5
theorem cell_1_122_0 : C 1 122 0 := by decide +kernel
theorem cell_1_122_1 : C 1 122 1 := by decide +kernel
theorem cell_1_122_2 : C 1 122 2 := by decide +kernel
theorem cell_1_122_3 : C 1 122 3 := by decide +kernel
theorem cell_1_122_4 : C 1 122 4 := by decide +kernel
theorem cell_1_122_5 : C 1 122 5 := by decide +kernel
theorem row_1_122 : ThresholdAt 1 122 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 122 0 cell_1_122_0
  | exact S 1 122 1 cell_1_122_1
  | exact S 1 122 2 cell_1_122_2
  | exact S 1 122 3 cell_1_122_3
  | exact S 1 122 4 cell_1_122_4
  | exact S 1 122 5 cell_1_122_5
theorem cell_1_123_0 : C 1 123 0 := by decide +kernel
theorem cell_1_123_1 : C 1 123 1 := by decide +kernel
theorem cell_1_123_2 : C 1 123 2 := by decide +kernel
theorem cell_1_123_3 : C 1 123 3 := by decide +kernel
theorem cell_1_123_4 : C 1 123 4 := by decide +kernel
theorem cell_1_123_5 : C 1 123 5 := by decide +kernel
theorem row_1_123 : ThresholdAt 1 123 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 123 0 cell_1_123_0
  | exact S 1 123 1 cell_1_123_1
  | exact S 1 123 2 cell_1_123_2
  | exact S 1 123 3 cell_1_123_3
  | exact S 1 123 4 cell_1_123_4
  | exact S 1 123 5 cell_1_123_5
theorem cell_1_124_0 : C 1 124 0 := by decide +kernel
theorem cell_1_124_1 : C 1 124 1 := by decide +kernel
theorem cell_1_124_2 : C 1 124 2 := by decide +kernel
theorem cell_1_124_3 : C 1 124 3 := by decide +kernel
theorem cell_1_124_4 : C 1 124 4 := by decide +kernel
theorem cell_1_124_5 : C 1 124 5 := by decide +kernel
theorem row_1_124 : ThresholdAt 1 124 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 124 0 cell_1_124_0
  | exact S 1 124 1 cell_1_124_1
  | exact S 1 124 2 cell_1_124_2
  | exact S 1 124 3 cell_1_124_3
  | exact S 1 124 4 cell_1_124_4
  | exact S 1 124 5 cell_1_124_5
theorem cell_1_125_0 : C 1 125 0 := by decide +kernel
theorem cell_1_125_1 : C 1 125 1 := by decide +kernel
theorem cell_1_125_2 : C 1 125 2 := by decide +kernel
theorem cell_1_125_3 : C 1 125 3 := by decide +kernel
theorem cell_1_125_4 : C 1 125 4 := by decide +kernel
theorem cell_1_125_5 : C 1 125 5 := by decide +kernel
theorem row_1_125 : ThresholdAt 1 125 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 125 0 cell_1_125_0
  | exact S 1 125 1 cell_1_125_1
  | exact S 1 125 2 cell_1_125_2
  | exact S 1 125 3 cell_1_125_3
  | exact S 1 125 4 cell_1_125_4
  | exact S 1 125 5 cell_1_125_5
theorem cell_1_126_0 : C 1 126 0 := by decide +kernel
theorem cell_1_126_1 : C 1 126 1 := by decide +kernel
theorem cell_1_126_2 : C 1 126 2 := by decide +kernel
theorem cell_1_126_3 : C 1 126 3 := by decide +kernel
theorem cell_1_126_4 : C 1 126 4 := by decide +kernel
theorem cell_1_126_5 : C 1 126 5 := by decide +kernel
theorem row_1_126 : ThresholdAt 1 126 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 126 0 cell_1_126_0
  | exact S 1 126 1 cell_1_126_1
  | exact S 1 126 2 cell_1_126_2
  | exact S 1 126 3 cell_1_126_3
  | exact S 1 126 4 cell_1_126_4
  | exact S 1 126 5 cell_1_126_5
theorem cell_1_127_0 : C 1 127 0 := by decide +kernel
theorem cell_1_127_1 : C 1 127 1 := by decide +kernel
theorem cell_1_127_2 : C 1 127 2 := by decide +kernel
theorem cell_1_127_3 : C 1 127 3 := by decide +kernel
theorem cell_1_127_4 : C 1 127 4 := by decide +kernel
theorem cell_1_127_5 : C 1 127 5 := by decide +kernel
theorem row_1_127 : ThresholdAt 1 127 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 127 0 cell_1_127_0
  | exact S 1 127 1 cell_1_127_1
  | exact S 1 127 2 cell_1_127_2
  | exact S 1 127 3 cell_1_127_3
  | exact S 1 127 4 cell_1_127_4
  | exact S 1 127 5 cell_1_127_5
theorem cell_1_128_0 : C 1 128 0 := by decide +kernel
theorem cell_1_128_1 : C 1 128 1 := by decide +kernel
theorem cell_1_128_2 : C 1 128 2 := by decide +kernel
theorem cell_1_128_3 : C 1 128 3 := by decide +kernel
theorem cell_1_128_4 : C 1 128 4 := by decide +kernel
theorem cell_1_128_5 : C 1 128 5 := by decide +kernel
theorem row_1_128 : ThresholdAt 1 128 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 128 0 cell_1_128_0
  | exact S 1 128 1 cell_1_128_1
  | exact S 1 128 2 cell_1_128_2
  | exact S 1 128 3 cell_1_128_3
  | exact S 1 128 4 cell_1_128_4
  | exact S 1 128 5 cell_1_128_5
theorem cell_1_129_0 : C 1 129 0 := by decide +kernel
theorem cell_1_129_1 : C 1 129 1 := by decide +kernel
theorem cell_1_129_2 : C 1 129 2 := by decide +kernel
theorem cell_1_129_3 : C 1 129 3 := by decide +kernel
theorem cell_1_129_4 : C 1 129 4 := by decide +kernel
theorem cell_1_129_5 : C 1 129 5 := by decide +kernel
theorem row_1_129 : ThresholdAt 1 129 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 129 0 cell_1_129_0
  | exact S 1 129 1 cell_1_129_1
  | exact S 1 129 2 cell_1_129_2
  | exact S 1 129 3 cell_1_129_3
  | exact S 1 129 4 cell_1_129_4
  | exact S 1 129 5 cell_1_129_5
theorem cell_1_130_0 : C 1 130 0 := by decide +kernel
theorem cell_1_130_1 : C 1 130 1 := by decide +kernel
theorem cell_1_130_2 : C 1 130 2 := by decide +kernel
theorem cell_1_130_3 : C 1 130 3 := by decide +kernel
theorem cell_1_130_4 : C 1 130 4 := by decide +kernel
theorem cell_1_130_5 : C 1 130 5 := by decide +kernel
theorem row_1_130 : ThresholdAt 1 130 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 130 0 cell_1_130_0
  | exact S 1 130 1 cell_1_130_1
  | exact S 1 130 2 cell_1_130_2
  | exact S 1 130 3 cell_1_130_3
  | exact S 1 130 4 cell_1_130_4
  | exact S 1 130 5 cell_1_130_5
theorem cell_1_131_0 : C 1 131 0 := by decide +kernel
theorem cell_1_131_1 : C 1 131 1 := by decide +kernel
theorem cell_1_131_2 : C 1 131 2 := by decide +kernel
theorem cell_1_131_3 : C 1 131 3 := by decide +kernel
theorem cell_1_131_4 : C 1 131 4 := by decide +kernel
theorem cell_1_131_5 : C 1 131 5 := by decide +kernel
theorem row_1_131 : ThresholdAt 1 131 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 131 0 cell_1_131_0
  | exact S 1 131 1 cell_1_131_1
  | exact S 1 131 2 cell_1_131_2
  | exact S 1 131 3 cell_1_131_3
  | exact S 1 131 4 cell_1_131_4
  | exact S 1 131 5 cell_1_131_5
theorem cell_1_132_0 : C 1 132 0 := by decide +kernel
theorem cell_1_132_1 : C 1 132 1 := by decide +kernel
theorem cell_1_132_2 : C 1 132 2 := by decide +kernel
theorem cell_1_132_3 : C 1 132 3 := by decide +kernel
theorem cell_1_132_4 : C 1 132 4 := by decide +kernel
theorem cell_1_132_5 : C 1 132 5 := by decide +kernel
theorem row_1_132 : ThresholdAt 1 132 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 132 0 cell_1_132_0
  | exact S 1 132 1 cell_1_132_1
  | exact S 1 132 2 cell_1_132_2
  | exact S 1 132 3 cell_1_132_3
  | exact S 1 132 4 cell_1_132_4
  | exact S 1 132 5 cell_1_132_5
theorem cell_1_133_0 : C 1 133 0 := by decide +kernel
theorem cell_1_133_1 : C 1 133 1 := by decide +kernel
theorem cell_1_133_2 : C 1 133 2 := by decide +kernel
theorem cell_1_133_3 : C 1 133 3 := by decide +kernel
theorem cell_1_133_4 : C 1 133 4 := by decide +kernel
theorem cell_1_133_5 : C 1 133 5 := by decide +kernel
theorem row_1_133 : ThresholdAt 1 133 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 133 0 cell_1_133_0
  | exact S 1 133 1 cell_1_133_1
  | exact S 1 133 2 cell_1_133_2
  | exact S 1 133 3 cell_1_133_3
  | exact S 1 133 4 cell_1_133_4
  | exact S 1 133 5 cell_1_133_5
theorem cell_1_134_0 : C 1 134 0 := by decide +kernel
theorem cell_1_134_1 : C 1 134 1 := by decide +kernel
theorem cell_1_134_2 : C 1 134 2 := by decide +kernel
theorem cell_1_134_3 : C 1 134 3 := by decide +kernel
theorem cell_1_134_4 : C 1 134 4 := by decide +kernel
theorem cell_1_134_5 : C 1 134 5 := by decide +kernel
theorem row_1_134 : ThresholdAt 1 134 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 134 0 cell_1_134_0
  | exact S 1 134 1 cell_1_134_1
  | exact S 1 134 2 cell_1_134_2
  | exact S 1 134 3 cell_1_134_3
  | exact S 1 134 4 cell_1_134_4
  | exact S 1 134 5 cell_1_134_5
theorem cell_1_135_0 : C 1 135 0 := by decide +kernel
theorem cell_1_135_1 : C 1 135 1 := by decide +kernel
theorem cell_1_135_2 : C 1 135 2 := by decide +kernel
theorem cell_1_135_3 : C 1 135 3 := by decide +kernel
theorem cell_1_135_4 : C 1 135 4 := by decide +kernel
theorem cell_1_135_5 : C 1 135 5 := by decide +kernel
theorem row_1_135 : ThresholdAt 1 135 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 135 0 cell_1_135_0
  | exact S 1 135 1 cell_1_135_1
  | exact S 1 135 2 cell_1_135_2
  | exact S 1 135 3 cell_1_135_3
  | exact S 1 135 4 cell_1_135_4
  | exact S 1 135 5 cell_1_135_5
theorem cell_1_136_0 : C 1 136 0 := by decide +kernel
theorem cell_1_136_1 : C 1 136 1 := by decide +kernel
theorem cell_1_136_2 : C 1 136 2 := by decide +kernel
theorem cell_1_136_3 : C 1 136 3 := by decide +kernel
theorem cell_1_136_4 : C 1 136 4 := by decide +kernel
theorem cell_1_136_5 : C 1 136 5 := by decide +kernel
theorem row_1_136 : ThresholdAt 1 136 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 136 0 cell_1_136_0
  | exact S 1 136 1 cell_1_136_1
  | exact S 1 136 2 cell_1_136_2
  | exact S 1 136 3 cell_1_136_3
  | exact S 1 136 4 cell_1_136_4
  | exact S 1 136 5 cell_1_136_5
theorem cell_1_137_0 : C 1 137 0 := by decide +kernel
theorem cell_1_137_1 : C 1 137 1 := by decide +kernel
theorem cell_1_137_2 : C 1 137 2 := by decide +kernel
theorem cell_1_137_3 : C 1 137 3 := by decide +kernel
theorem cell_1_137_4 : C 1 137 4 := by decide +kernel
theorem cell_1_137_5 : C 1 137 5 := by decide +kernel
theorem row_1_137 : ThresholdAt 1 137 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 137 0 cell_1_137_0
  | exact S 1 137 1 cell_1_137_1
  | exact S 1 137 2 cell_1_137_2
  | exact S 1 137 3 cell_1_137_3
  | exact S 1 137 4 cell_1_137_4
  | exact S 1 137 5 cell_1_137_5
theorem cell_1_138_0 : C 1 138 0 := by decide +kernel
theorem cell_1_138_1 : C 1 138 1 := by decide +kernel
theorem cell_1_138_2 : C 1 138 2 := by decide +kernel
theorem cell_1_138_3 : C 1 138 3 := by decide +kernel
theorem cell_1_138_4 : C 1 138 4 := by decide +kernel
theorem cell_1_138_5 : C 1 138 5 := by decide +kernel
theorem row_1_138 : ThresholdAt 1 138 := by
 intro j hj
 have hj6 : j < 6 := List.mem_range.mp hj
 interval_cases j <;> first
  | exact S 1 138 0 cell_1_138_0
  | exact S 1 138 1 cell_1_138_1
  | exact S 1 138 2 cell_1_138_2
  | exact S 1 138 3 cell_1_138_3
  | exact S 1 138 4 cell_1_138_4
  | exact S 1 138 5 cell_1_138_5
theorem checkedR1 : ∀ V ∈ List.range 139, ThresholdAt 1 V := by
  intro V hV
  have hv : V < 139 := List.mem_range.mp hV
  by_cases h0_139 : V < 69
  · by_cases h0_69 : V < 34
    · by_cases h0_34 : V < 17
      · by_cases h0_17 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have he : V = 0 := by omega
                subst V
                exact row_1_0
              · have he : V = 1 := by omega
                subst V
                exact row_1_1
            · by_cases h2_4 : V < 3
              · have he : V = 2 := by omega
                subst V
                exact row_1_2
              · have he : V = 3 := by omega
                subst V
                exact row_1_3
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have he : V = 4 := by omega
                subst V
                exact row_1_4
              · have he : V = 5 := by omega
                subst V
                exact row_1_5
            · by_cases h6_8 : V < 7
              · have he : V = 6 := by omega
                subst V
                exact row_1_6
              · have he : V = 7 := by omega
                subst V
                exact row_1_7
        · by_cases h8_17 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have he : V = 8 := by omega
                subst V
                exact row_1_8
              · have he : V = 9 := by omega
                subst V
                exact row_1_9
            · by_cases h10_12 : V < 11
              · have he : V = 10 := by omega
                subst V
                exact row_1_10
              · have he : V = 11 := by omega
                subst V
                exact row_1_11
          · by_cases h12_17 : V < 14
            · by_cases h12_14 : V < 13
              · have he : V = 12 := by omega
                subst V
                exact row_1_12
              · have he : V = 13 := by omega
                subst V
                exact row_1_13
            · by_cases h14_17 : V < 15
              · have he : V = 14 := by omega
                subst V
                exact row_1_14
              · by_cases h15_17 : V < 16
                · have he : V = 15 := by omega
                  subst V
                  exact row_1_15
                · have he : V = 16 := by omega
                  subst V
                  exact row_1_16
      · by_cases h17_34 : V < 25
        · by_cases h17_25 : V < 21
          · by_cases h17_21 : V < 19
            · by_cases h17_19 : V < 18
              · have he : V = 17 := by omega
                subst V
                exact row_1_17
              · have he : V = 18 := by omega
                subst V
                exact row_1_18
            · by_cases h19_21 : V < 20
              · have he : V = 19 := by omega
                subst V
                exact row_1_19
              · have he : V = 20 := by omega
                subst V
                exact row_1_20
          · by_cases h21_25 : V < 23
            · by_cases h21_23 : V < 22
              · have he : V = 21 := by omega
                subst V
                exact row_1_21
              · have he : V = 22 := by omega
                subst V
                exact row_1_22
            · by_cases h23_25 : V < 24
              · have he : V = 23 := by omega
                subst V
                exact row_1_23
              · have he : V = 24 := by omega
                subst V
                exact row_1_24
        · by_cases h25_34 : V < 29
          · by_cases h25_29 : V < 27
            · by_cases h25_27 : V < 26
              · have he : V = 25 := by omega
                subst V
                exact row_1_25
              · have he : V = 26 := by omega
                subst V
                exact row_1_26
            · by_cases h27_29 : V < 28
              · have he : V = 27 := by omega
                subst V
                exact row_1_27
              · have he : V = 28 := by omega
                subst V
                exact row_1_28
          · by_cases h29_34 : V < 31
            · by_cases h29_31 : V < 30
              · have he : V = 29 := by omega
                subst V
                exact row_1_29
              · have he : V = 30 := by omega
                subst V
                exact row_1_30
            · by_cases h31_34 : V < 32
              · have he : V = 31 := by omega
                subst V
                exact row_1_31
              · by_cases h32_34 : V < 33
                · have he : V = 32 := by omega
                  subst V
                  exact row_1_32
                · have he : V = 33 := by omega
                  subst V
                  exact row_1_33
    · by_cases h34_69 : V < 51
      · by_cases h34_51 : V < 42
        · by_cases h34_42 : V < 38
          · by_cases h34_38 : V < 36
            · by_cases h34_36 : V < 35
              · have he : V = 34 := by omega
                subst V
                exact row_1_34
              · have he : V = 35 := by omega
                subst V
                exact row_1_35
            · by_cases h36_38 : V < 37
              · have he : V = 36 := by omega
                subst V
                exact row_1_36
              · have he : V = 37 := by omega
                subst V
                exact row_1_37
          · by_cases h38_42 : V < 40
            · by_cases h38_40 : V < 39
              · have he : V = 38 := by omega
                subst V
                exact row_1_38
              · have he : V = 39 := by omega
                subst V
                exact row_1_39
            · by_cases h40_42 : V < 41
              · have he : V = 40 := by omega
                subst V
                exact row_1_40
              · have he : V = 41 := by omega
                subst V
                exact row_1_41
        · by_cases h42_51 : V < 46
          · by_cases h42_46 : V < 44
            · by_cases h42_44 : V < 43
              · have he : V = 42 := by omega
                subst V
                exact row_1_42
              · have he : V = 43 := by omega
                subst V
                exact row_1_43
            · by_cases h44_46 : V < 45
              · have he : V = 44 := by omega
                subst V
                exact row_1_44
              · have he : V = 45 := by omega
                subst V
                exact row_1_45
          · by_cases h46_51 : V < 48
            · by_cases h46_48 : V < 47
              · have he : V = 46 := by omega
                subst V
                exact row_1_46
              · have he : V = 47 := by omega
                subst V
                exact row_1_47
            · by_cases h48_51 : V < 49
              · have he : V = 48 := by omega
                subst V
                exact row_1_48
              · by_cases h49_51 : V < 50
                · have he : V = 49 := by omega
                  subst V
                  exact row_1_49
                · have he : V = 50 := by omega
                  subst V
                  exact row_1_50
      · by_cases h51_69 : V < 60
        · by_cases h51_60 : V < 55
          · by_cases h51_55 : V < 53
            · by_cases h51_53 : V < 52
              · have he : V = 51 := by omega
                subst V
                exact row_1_51
              · have he : V = 52 := by omega
                subst V
                exact row_1_52
            · by_cases h53_55 : V < 54
              · have he : V = 53 := by omega
                subst V
                exact row_1_53
              · have he : V = 54 := by omega
                subst V
                exact row_1_54
          · by_cases h55_60 : V < 57
            · by_cases h55_57 : V < 56
              · have he : V = 55 := by omega
                subst V
                exact row_1_55
              · have he : V = 56 := by omega
                subst V
                exact row_1_56
            · by_cases h57_60 : V < 58
              · have he : V = 57 := by omega
                subst V
                exact row_1_57
              · by_cases h58_60 : V < 59
                · have he : V = 58 := by omega
                  subst V
                  exact row_1_58
                · have he : V = 59 := by omega
                  subst V
                  exact row_1_59
        · by_cases h60_69 : V < 64
          · by_cases h60_64 : V < 62
            · by_cases h60_62 : V < 61
              · have he : V = 60 := by omega
                subst V
                exact row_1_60
              · have he : V = 61 := by omega
                subst V
                exact row_1_61
            · by_cases h62_64 : V < 63
              · have he : V = 62 := by omega
                subst V
                exact row_1_62
              · have he : V = 63 := by omega
                subst V
                exact row_1_63
          · by_cases h64_69 : V < 66
            · by_cases h64_66 : V < 65
              · have he : V = 64 := by omega
                subst V
                exact row_1_64
              · have he : V = 65 := by omega
                subst V
                exact row_1_65
            · by_cases h66_69 : V < 67
              · have he : V = 66 := by omega
                subst V
                exact row_1_66
              · by_cases h67_69 : V < 68
                · have he : V = 67 := by omega
                  subst V
                  exact row_1_67
                · have he : V = 68 := by omega
                  subst V
                  exact row_1_68
  · by_cases h69_139 : V < 104
    · by_cases h69_104 : V < 86
      · by_cases h69_86 : V < 77
        · by_cases h69_77 : V < 73
          · by_cases h69_73 : V < 71
            · by_cases h69_71 : V < 70
              · have he : V = 69 := by omega
                subst V
                exact row_1_69
              · have he : V = 70 := by omega
                subst V
                exact row_1_70
            · by_cases h71_73 : V < 72
              · have he : V = 71 := by omega
                subst V
                exact row_1_71
              · have he : V = 72 := by omega
                subst V
                exact row_1_72
          · by_cases h73_77 : V < 75
            · by_cases h73_75 : V < 74
              · have he : V = 73 := by omega
                subst V
                exact row_1_73
              · have he : V = 74 := by omega
                subst V
                exact row_1_74
            · by_cases h75_77 : V < 76
              · have he : V = 75 := by omega
                subst V
                exact row_1_75
              · have he : V = 76 := by omega
                subst V
                exact row_1_76
        · by_cases h77_86 : V < 81
          · by_cases h77_81 : V < 79
            · by_cases h77_79 : V < 78
              · have he : V = 77 := by omega
                subst V
                exact row_1_77
              · have he : V = 78 := by omega
                subst V
                exact row_1_78
            · by_cases h79_81 : V < 80
              · have he : V = 79 := by omega
                subst V
                exact row_1_79
              · have he : V = 80 := by omega
                subst V
                exact row_1_80
          · by_cases h81_86 : V < 83
            · by_cases h81_83 : V < 82
              · have he : V = 81 := by omega
                subst V
                exact row_1_81
              · have he : V = 82 := by omega
                subst V
                exact row_1_82
            · by_cases h83_86 : V < 84
              · have he : V = 83 := by omega
                subst V
                exact row_1_83
              · by_cases h84_86 : V < 85
                · have he : V = 84 := by omega
                  subst V
                  exact row_1_84
                · have he : V = 85 := by omega
                  subst V
                  exact row_1_85
      · by_cases h86_104 : V < 95
        · by_cases h86_95 : V < 90
          · by_cases h86_90 : V < 88
            · by_cases h86_88 : V < 87
              · have he : V = 86 := by omega
                subst V
                exact row_1_86
              · have he : V = 87 := by omega
                subst V
                exact row_1_87
            · by_cases h88_90 : V < 89
              · have he : V = 88 := by omega
                subst V
                exact row_1_88
              · have he : V = 89 := by omega
                subst V
                exact row_1_89
          · by_cases h90_95 : V < 92
            · by_cases h90_92 : V < 91
              · have he : V = 90 := by omega
                subst V
                exact row_1_90
              · have he : V = 91 := by omega
                subst V
                exact row_1_91
            · by_cases h92_95 : V < 93
              · have he : V = 92 := by omega
                subst V
                exact row_1_92
              · by_cases h93_95 : V < 94
                · have he : V = 93 := by omega
                  subst V
                  exact row_1_93
                · have he : V = 94 := by omega
                  subst V
                  exact row_1_94
        · by_cases h95_104 : V < 99
          · by_cases h95_99 : V < 97
            · by_cases h95_97 : V < 96
              · have he : V = 95 := by omega
                subst V
                exact row_1_95
              · have he : V = 96 := by omega
                subst V
                exact row_1_96
            · by_cases h97_99 : V < 98
              · have he : V = 97 := by omega
                subst V
                exact row_1_97
              · have he : V = 98 := by omega
                subst V
                exact row_1_98
          · by_cases h99_104 : V < 101
            · by_cases h99_101 : V < 100
              · have he : V = 99 := by omega
                subst V
                exact row_1_99
              · have he : V = 100 := by omega
                subst V
                exact row_1_100
            · by_cases h101_104 : V < 102
              · have he : V = 101 := by omega
                subst V
                exact row_1_101
              · by_cases h102_104 : V < 103
                · have he : V = 102 := by omega
                  subst V
                  exact row_1_102
                · have he : V = 103 := by omega
                  subst V
                  exact row_1_103
    · by_cases h104_139 : V < 121
      · by_cases h104_121 : V < 112
        · by_cases h104_112 : V < 108
          · by_cases h104_108 : V < 106
            · by_cases h104_106 : V < 105
              · have he : V = 104 := by omega
                subst V
                exact row_1_104
              · have he : V = 105 := by omega
                subst V
                exact row_1_105
            · by_cases h106_108 : V < 107
              · have he : V = 106 := by omega
                subst V
                exact row_1_106
              · have he : V = 107 := by omega
                subst V
                exact row_1_107
          · by_cases h108_112 : V < 110
            · by_cases h108_110 : V < 109
              · have he : V = 108 := by omega
                subst V
                exact row_1_108
              · have he : V = 109 := by omega
                subst V
                exact row_1_109
            · by_cases h110_112 : V < 111
              · have he : V = 110 := by omega
                subst V
                exact row_1_110
              · have he : V = 111 := by omega
                subst V
                exact row_1_111
        · by_cases h112_121 : V < 116
          · by_cases h112_116 : V < 114
            · by_cases h112_114 : V < 113
              · have he : V = 112 := by omega
                subst V
                exact row_1_112
              · have he : V = 113 := by omega
                subst V
                exact row_1_113
            · by_cases h114_116 : V < 115
              · have he : V = 114 := by omega
                subst V
                exact row_1_114
              · have he : V = 115 := by omega
                subst V
                exact row_1_115
          · by_cases h116_121 : V < 118
            · by_cases h116_118 : V < 117
              · have he : V = 116 := by omega
                subst V
                exact row_1_116
              · have he : V = 117 := by omega
                subst V
                exact row_1_117
            · by_cases h118_121 : V < 119
              · have he : V = 118 := by omega
                subst V
                exact row_1_118
              · by_cases h119_121 : V < 120
                · have he : V = 119 := by omega
                  subst V
                  exact row_1_119
                · have he : V = 120 := by omega
                  subst V
                  exact row_1_120
      · by_cases h121_139 : V < 130
        · by_cases h121_130 : V < 125
          · by_cases h121_125 : V < 123
            · by_cases h121_123 : V < 122
              · have he : V = 121 := by omega
                subst V
                exact row_1_121
              · have he : V = 122 := by omega
                subst V
                exact row_1_122
            · by_cases h123_125 : V < 124
              · have he : V = 123 := by omega
                subst V
                exact row_1_123
              · have he : V = 124 := by omega
                subst V
                exact row_1_124
          · by_cases h125_130 : V < 127
            · by_cases h125_127 : V < 126
              · have he : V = 125 := by omega
                subst V
                exact row_1_125
              · have he : V = 126 := by omega
                subst V
                exact row_1_126
            · by_cases h127_130 : V < 128
              · have he : V = 127 := by omega
                subst V
                exact row_1_127
              · by_cases h128_130 : V < 129
                · have he : V = 128 := by omega
                  subst V
                  exact row_1_128
                · have he : V = 129 := by omega
                  subst V
                  exact row_1_129
        · by_cases h130_139 : V < 134
          · by_cases h130_134 : V < 132
            · by_cases h130_132 : V < 131
              · have he : V = 130 := by omega
                subst V
                exact row_1_130
              · have he : V = 131 := by omega
                subst V
                exact row_1_131
            · by_cases h132_134 : V < 133
              · have he : V = 132 := by omega
                subst V
                exact row_1_132
              · have he : V = 133 := by omega
                subst V
                exact row_1_133
          · by_cases h134_139 : V < 136
            · by_cases h134_136 : V < 135
              · have he : V = 134 := by omega
                subst V
                exact row_1_134
              · have he : V = 135 := by omega
                subst V
                exact row_1_135
            · by_cases h136_139 : V < 137
              · have he : V = 136 := by omega
                subst V
                exact row_1_136
              · by_cases h137_139 : V < 138
                · have he : V = 137 := by omega
                  subst V
                  exact row_1_137
                · have he : V = 138 := by omega
                  subst V
                  exact row_1_138
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
