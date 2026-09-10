import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked28

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_29_0_0 : CertificateAt 29 0 0 := by decide +kernel
theorem cell_29_0_1 : CertificateAt 29 0 1 := by decide +kernel
theorem cell_29_0_2 : CertificateAt 29 0 2 := by decide +kernel
theorem cell_29_0_3 : CertificateAt 29 0 3 := by decide +kernel
theorem cell_29_0_4 : CertificateAt 29 0 4 := by decide +kernel
theorem cell_29_0_5 : CertificateAt 29 0 5 := by decide +kernel
theorem row_29_0 : ThresholdAt 29 0 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 0 0 cell_29_0_0
    | exact certificate_sound 29 0 1 cell_29_0_1
    | exact certificate_sound 29 0 2 cell_29_0_2
    | exact certificate_sound 29 0 3 cell_29_0_3
    | exact certificate_sound 29 0 4 cell_29_0_4
    | exact certificate_sound 29 0 5 cell_29_0_5
theorem cell_29_1_0 : CertificateAt 29 1 0 := by decide +kernel
theorem cell_29_1_1 : CertificateAt 29 1 1 := by decide +kernel
theorem cell_29_1_2 : CertificateAt 29 1 2 := by decide +kernel
theorem cell_29_1_3 : CertificateAt 29 1 3 := by decide +kernel
theorem cell_29_1_4 : CertificateAt 29 1 4 := by decide +kernel
theorem cell_29_1_5 : CertificateAt 29 1 5 := by decide +kernel
theorem row_29_1 : ThresholdAt 29 1 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 1 0 cell_29_1_0
    | exact certificate_sound 29 1 1 cell_29_1_1
    | exact certificate_sound 29 1 2 cell_29_1_2
    | exact certificate_sound 29 1 3 cell_29_1_3
    | exact certificate_sound 29 1 4 cell_29_1_4
    | exact certificate_sound 29 1 5 cell_29_1_5
theorem cell_29_2_0 : CertificateAt 29 2 0 := by decide +kernel
theorem cell_29_2_1 : CertificateAt 29 2 1 := by decide +kernel
theorem cell_29_2_2 : CertificateAt 29 2 2 := by decide +kernel
theorem cell_29_2_3 : CertificateAt 29 2 3 := by decide +kernel
theorem cell_29_2_4 : CertificateAt 29 2 4 := by decide +kernel
theorem cell_29_2_5 : CertificateAt 29 2 5 := by decide +kernel
theorem row_29_2 : ThresholdAt 29 2 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 2 0 cell_29_2_0
    | exact certificate_sound 29 2 1 cell_29_2_1
    | exact certificate_sound 29 2 2 cell_29_2_2
    | exact certificate_sound 29 2 3 cell_29_2_3
    | exact certificate_sound 29 2 4 cell_29_2_4
    | exact certificate_sound 29 2 5 cell_29_2_5
theorem cell_29_3_0 : CertificateAt 29 3 0 := by decide +kernel
theorem cell_29_3_1 : CertificateAt 29 3 1 := by decide +kernel
theorem cell_29_3_2 : CertificateAt 29 3 2 := by decide +kernel
theorem cell_29_3_3 : CertificateAt 29 3 3 := by decide +kernel
theorem cell_29_3_4 : CertificateAt 29 3 4 := by decide +kernel
theorem cell_29_3_5 : CertificateAt 29 3 5 := by decide +kernel
theorem row_29_3 : ThresholdAt 29 3 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 3 0 cell_29_3_0
    | exact certificate_sound 29 3 1 cell_29_3_1
    | exact certificate_sound 29 3 2 cell_29_3_2
    | exact certificate_sound 29 3 3 cell_29_3_3
    | exact certificate_sound 29 3 4 cell_29_3_4
    | exact certificate_sound 29 3 5 cell_29_3_5
theorem cell_29_4_0 : CertificateAt 29 4 0 := by decide +kernel
theorem cell_29_4_1 : CertificateAt 29 4 1 := by decide +kernel
theorem cell_29_4_2 : CertificateAt 29 4 2 := by decide +kernel
theorem cell_29_4_3 : CertificateAt 29 4 3 := by decide +kernel
theorem cell_29_4_4 : CertificateAt 29 4 4 := by decide +kernel
theorem cell_29_4_5 : CertificateAt 29 4 5 := by decide +kernel
theorem row_29_4 : ThresholdAt 29 4 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 4 0 cell_29_4_0
    | exact certificate_sound 29 4 1 cell_29_4_1
    | exact certificate_sound 29 4 2 cell_29_4_2
    | exact certificate_sound 29 4 3 cell_29_4_3
    | exact certificate_sound 29 4 4 cell_29_4_4
    | exact certificate_sound 29 4 5 cell_29_4_5
theorem cell_29_5_0 : CertificateAt 29 5 0 := by decide +kernel
theorem cell_29_5_1 : CertificateAt 29 5 1 := by decide +kernel
theorem cell_29_5_2 : CertificateAt 29 5 2 := by decide +kernel
theorem cell_29_5_3 : CertificateAt 29 5 3 := by decide +kernel
theorem cell_29_5_4 : CertificateAt 29 5 4 := by decide +kernel
theorem cell_29_5_5 : CertificateAt 29 5 5 := by decide +kernel
theorem row_29_5 : ThresholdAt 29 5 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 5 0 cell_29_5_0
    | exact certificate_sound 29 5 1 cell_29_5_1
    | exact certificate_sound 29 5 2 cell_29_5_2
    | exact certificate_sound 29 5 3 cell_29_5_3
    | exact certificate_sound 29 5 4 cell_29_5_4
    | exact certificate_sound 29 5 5 cell_29_5_5
theorem cell_29_6_0 : CertificateAt 29 6 0 := by decide +kernel
theorem cell_29_6_1 : CertificateAt 29 6 1 := by decide +kernel
theorem cell_29_6_2 : CertificateAt 29 6 2 := by decide +kernel
theorem cell_29_6_3 : CertificateAt 29 6 3 := by decide +kernel
theorem cell_29_6_4 : CertificateAt 29 6 4 := by decide +kernel
theorem cell_29_6_5 : CertificateAt 29 6 5 := by decide +kernel
theorem row_29_6 : ThresholdAt 29 6 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 6 0 cell_29_6_0
    | exact certificate_sound 29 6 1 cell_29_6_1
    | exact certificate_sound 29 6 2 cell_29_6_2
    | exact certificate_sound 29 6 3 cell_29_6_3
    | exact certificate_sound 29 6 4 cell_29_6_4
    | exact certificate_sound 29 6 5 cell_29_6_5
theorem cell_29_7_0 : CertificateAt 29 7 0 := by decide +kernel
theorem cell_29_7_1 : CertificateAt 29 7 1 := by decide +kernel
theorem cell_29_7_2 : CertificateAt 29 7 2 := by decide +kernel
theorem cell_29_7_3 : CertificateAt 29 7 3 := by decide +kernel
theorem cell_29_7_4 : CertificateAt 29 7 4 := by decide +kernel
theorem cell_29_7_5 : CertificateAt 29 7 5 := by decide +kernel
theorem row_29_7 : ThresholdAt 29 7 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 7 0 cell_29_7_0
    | exact certificate_sound 29 7 1 cell_29_7_1
    | exact certificate_sound 29 7 2 cell_29_7_2
    | exact certificate_sound 29 7 3 cell_29_7_3
    | exact certificate_sound 29 7 4 cell_29_7_4
    | exact certificate_sound 29 7 5 cell_29_7_5
theorem cell_29_8_0 : CertificateAt 29 8 0 := by decide +kernel
theorem cell_29_8_1 : CertificateAt 29 8 1 := by decide +kernel
theorem cell_29_8_2 : CertificateAt 29 8 2 := by decide +kernel
theorem cell_29_8_3 : CertificateAt 29 8 3 := by decide +kernel
theorem cell_29_8_4 : CertificateAt 29 8 4 := by decide +kernel
theorem cell_29_8_5 : CertificateAt 29 8 5 := by decide +kernel
theorem row_29_8 : ThresholdAt 29 8 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 8 0 cell_29_8_0
    | exact certificate_sound 29 8 1 cell_29_8_1
    | exact certificate_sound 29 8 2 cell_29_8_2
    | exact certificate_sound 29 8 3 cell_29_8_3
    | exact certificate_sound 29 8 4 cell_29_8_4
    | exact certificate_sound 29 8 5 cell_29_8_5
theorem cell_29_9_0 : CertificateAt 29 9 0 := by decide +kernel
theorem cell_29_9_1 : CertificateAt 29 9 1 := by decide +kernel
theorem cell_29_9_2 : CertificateAt 29 9 2 := by decide +kernel
theorem cell_29_9_3 : CertificateAt 29 9 3 := by decide +kernel
theorem cell_29_9_4 : CertificateAt 29 9 4 := by decide +kernel
theorem cell_29_9_5 : CertificateAt 29 9 5 := by decide +kernel
theorem row_29_9 : ThresholdAt 29 9 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 9 0 cell_29_9_0
    | exact certificate_sound 29 9 1 cell_29_9_1
    | exact certificate_sound 29 9 2 cell_29_9_2
    | exact certificate_sound 29 9 3 cell_29_9_3
    | exact certificate_sound 29 9 4 cell_29_9_4
    | exact certificate_sound 29 9 5 cell_29_9_5
theorem cell_29_10_0 : CertificateAt 29 10 0 := by decide +kernel
theorem cell_29_10_1 : CertificateAt 29 10 1 := by decide +kernel
theorem cell_29_10_2 : CertificateAt 29 10 2 := by decide +kernel
theorem cell_29_10_3 : CertificateAt 29 10 3 := by decide +kernel
theorem cell_29_10_4 : CertificateAt 29 10 4 := by decide +kernel
theorem cell_29_10_5 : CertificateAt 29 10 5 := by decide +kernel
theorem row_29_10 : ThresholdAt 29 10 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 10 0 cell_29_10_0
    | exact certificate_sound 29 10 1 cell_29_10_1
    | exact certificate_sound 29 10 2 cell_29_10_2
    | exact certificate_sound 29 10 3 cell_29_10_3
    | exact certificate_sound 29 10 4 cell_29_10_4
    | exact certificate_sound 29 10 5 cell_29_10_5
theorem cell_29_11_0 : CertificateAt 29 11 0 := by decide +kernel
theorem cell_29_11_1 : CertificateAt 29 11 1 := by decide +kernel
theorem cell_29_11_2 : CertificateAt 29 11 2 := by decide +kernel
theorem cell_29_11_3 : CertificateAt 29 11 3 := by decide +kernel
theorem cell_29_11_4 : CertificateAt 29 11 4 := by decide +kernel
theorem cell_29_11_5 : CertificateAt 29 11 5 := by decide +kernel
theorem row_29_11 : ThresholdAt 29 11 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 11 0 cell_29_11_0
    | exact certificate_sound 29 11 1 cell_29_11_1
    | exact certificate_sound 29 11 2 cell_29_11_2
    | exact certificate_sound 29 11 3 cell_29_11_3
    | exact certificate_sound 29 11 4 cell_29_11_4
    | exact certificate_sound 29 11 5 cell_29_11_5
theorem cell_29_12_0 : CertificateAt 29 12 0 := by decide +kernel
theorem cell_29_12_1 : CertificateAt 29 12 1 := by decide +kernel
theorem cell_29_12_2 : CertificateAt 29 12 2 := by decide +kernel
theorem cell_29_12_3 : CertificateAt 29 12 3 := by decide +kernel
theorem cell_29_12_4 : CertificateAt 29 12 4 := by decide +kernel
theorem cell_29_12_5 : CertificateAt 29 12 5 := by decide +kernel
theorem row_29_12 : ThresholdAt 29 12 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 12 0 cell_29_12_0
    | exact certificate_sound 29 12 1 cell_29_12_1
    | exact certificate_sound 29 12 2 cell_29_12_2
    | exact certificate_sound 29 12 3 cell_29_12_3
    | exact certificate_sound 29 12 4 cell_29_12_4
    | exact certificate_sound 29 12 5 cell_29_12_5
theorem cell_29_13_0 : CertificateAt 29 13 0 := by decide +kernel
theorem cell_29_13_1 : CertificateAt 29 13 1 := by decide +kernel
theorem cell_29_13_2 : CertificateAt 29 13 2 := by decide +kernel
theorem cell_29_13_3 : CertificateAt 29 13 3 := by decide +kernel
theorem cell_29_13_4 : CertificateAt 29 13 4 := by decide +kernel
theorem cell_29_13_5 : CertificateAt 29 13 5 := by decide +kernel
theorem row_29_13 : ThresholdAt 29 13 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 13 0 cell_29_13_0
    | exact certificate_sound 29 13 1 cell_29_13_1
    | exact certificate_sound 29 13 2 cell_29_13_2
    | exact certificate_sound 29 13 3 cell_29_13_3
    | exact certificate_sound 29 13 4 cell_29_13_4
    | exact certificate_sound 29 13 5 cell_29_13_5
theorem cell_29_14_0 : CertificateAt 29 14 0 := by decide +kernel
theorem cell_29_14_1 : CertificateAt 29 14 1 := by decide +kernel
theorem cell_29_14_2 : CertificateAt 29 14 2 := by decide +kernel
theorem cell_29_14_3 : CertificateAt 29 14 3 := by decide +kernel
theorem cell_29_14_4 : CertificateAt 29 14 4 := by decide +kernel
theorem cell_29_14_5 : CertificateAt 29 14 5 := by decide +kernel
theorem row_29_14 : ThresholdAt 29 14 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 14 0 cell_29_14_0
    | exact certificate_sound 29 14 1 cell_29_14_1
    | exact certificate_sound 29 14 2 cell_29_14_2
    | exact certificate_sound 29 14 3 cell_29_14_3
    | exact certificate_sound 29 14 4 cell_29_14_4
    | exact certificate_sound 29 14 5 cell_29_14_5
theorem cell_29_15_0 : CertificateAt 29 15 0 := by decide +kernel
theorem cell_29_15_1 : CertificateAt 29 15 1 := by decide +kernel
theorem cell_29_15_2 : CertificateAt 29 15 2 := by decide +kernel
theorem cell_29_15_3 : CertificateAt 29 15 3 := by decide +kernel
theorem cell_29_15_4 : CertificateAt 29 15 4 := by decide +kernel
theorem cell_29_15_5 : CertificateAt 29 15 5 := by decide +kernel
theorem row_29_15 : ThresholdAt 29 15 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 15 0 cell_29_15_0
    | exact certificate_sound 29 15 1 cell_29_15_1
    | exact certificate_sound 29 15 2 cell_29_15_2
    | exact certificate_sound 29 15 3 cell_29_15_3
    | exact certificate_sound 29 15 4 cell_29_15_4
    | exact certificate_sound 29 15 5 cell_29_15_5
theorem cell_29_16_0 : CertificateAt 29 16 0 := by decide +kernel
theorem cell_29_16_1 : CertificateAt 29 16 1 := by decide +kernel
theorem cell_29_16_2 : CertificateAt 29 16 2 := by decide +kernel
theorem cell_29_16_3 : CertificateAt 29 16 3 := by decide +kernel
theorem cell_29_16_4 : CertificateAt 29 16 4 := by decide +kernel
theorem cell_29_16_5 : CertificateAt 29 16 5 := by decide +kernel
theorem row_29_16 : ThresholdAt 29 16 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 16 0 cell_29_16_0
    | exact certificate_sound 29 16 1 cell_29_16_1
    | exact certificate_sound 29 16 2 cell_29_16_2
    | exact certificate_sound 29 16 3 cell_29_16_3
    | exact certificate_sound 29 16 4 cell_29_16_4
    | exact certificate_sound 29 16 5 cell_29_16_5
theorem cell_29_17_0 : CertificateAt 29 17 0 := by decide +kernel
theorem cell_29_17_1 : CertificateAt 29 17 1 := by decide +kernel
theorem cell_29_17_2 : CertificateAt 29 17 2 := by decide +kernel
theorem cell_29_17_3 : CertificateAt 29 17 3 := by decide +kernel
theorem cell_29_17_4 : CertificateAt 29 17 4 := by decide +kernel
theorem cell_29_17_5 : CertificateAt 29 17 5 := by decide +kernel
theorem row_29_17 : ThresholdAt 29 17 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 17 0 cell_29_17_0
    | exact certificate_sound 29 17 1 cell_29_17_1
    | exact certificate_sound 29 17 2 cell_29_17_2
    | exact certificate_sound 29 17 3 cell_29_17_3
    | exact certificate_sound 29 17 4 cell_29_17_4
    | exact certificate_sound 29 17 5 cell_29_17_5
theorem cell_29_18_0 : CertificateAt 29 18 0 := by decide +kernel
theorem cell_29_18_1 : CertificateAt 29 18 1 := by decide +kernel
theorem cell_29_18_2 : CertificateAt 29 18 2 := by decide +kernel
theorem cell_29_18_3 : CertificateAt 29 18 3 := by decide +kernel
theorem cell_29_18_4 : CertificateAt 29 18 4 := by decide +kernel
theorem cell_29_18_5 : CertificateAt 29 18 5 := by decide +kernel
theorem row_29_18 : ThresholdAt 29 18 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 18 0 cell_29_18_0
    | exact certificate_sound 29 18 1 cell_29_18_1
    | exact certificate_sound 29 18 2 cell_29_18_2
    | exact certificate_sound 29 18 3 cell_29_18_3
    | exact certificate_sound 29 18 4 cell_29_18_4
    | exact certificate_sound 29 18 5 cell_29_18_5
theorem cell_29_19_0 : CertificateAt 29 19 0 := by decide +kernel
theorem cell_29_19_1 : CertificateAt 29 19 1 := by decide +kernel
theorem cell_29_19_2 : CertificateAt 29 19 2 := by decide +kernel
theorem cell_29_19_3 : CertificateAt 29 19 3 := by decide +kernel
theorem cell_29_19_4 : CertificateAt 29 19 4 := by decide +kernel
theorem cell_29_19_5 : CertificateAt 29 19 5 := by decide +kernel
theorem row_29_19 : ThresholdAt 29 19 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 19 0 cell_29_19_0
    | exact certificate_sound 29 19 1 cell_29_19_1
    | exact certificate_sound 29 19 2 cell_29_19_2
    | exact certificate_sound 29 19 3 cell_29_19_3
    | exact certificate_sound 29 19 4 cell_29_19_4
    | exact certificate_sound 29 19 5 cell_29_19_5
theorem cell_29_20_0 : CertificateAt 29 20 0 := by decide +kernel
theorem cell_29_20_1 : CertificateAt 29 20 1 := by decide +kernel
theorem cell_29_20_2 : CertificateAt 29 20 2 := by decide +kernel
theorem cell_29_20_3 : CertificateAt 29 20 3 := by decide +kernel
theorem cell_29_20_4 : CertificateAt 29 20 4 := by decide +kernel
theorem cell_29_20_5 : CertificateAt 29 20 5 := by decide +kernel
theorem row_29_20 : ThresholdAt 29 20 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 20 0 cell_29_20_0
    | exact certificate_sound 29 20 1 cell_29_20_1
    | exact certificate_sound 29 20 2 cell_29_20_2
    | exact certificate_sound 29 20 3 cell_29_20_3
    | exact certificate_sound 29 20 4 cell_29_20_4
    | exact certificate_sound 29 20 5 cell_29_20_5
theorem cell_29_21_0 : CertificateAt 29 21 0 := by decide +kernel
theorem cell_29_21_1 : CertificateAt 29 21 1 := by decide +kernel
theorem cell_29_21_2 : CertificateAt 29 21 2 := by decide +kernel
theorem cell_29_21_3 : CertificateAt 29 21 3 := by decide +kernel
theorem cell_29_21_4 : CertificateAt 29 21 4 := by decide +kernel
theorem cell_29_21_5 : CertificateAt 29 21 5 := by decide +kernel
theorem row_29_21 : ThresholdAt 29 21 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 21 0 cell_29_21_0
    | exact certificate_sound 29 21 1 cell_29_21_1
    | exact certificate_sound 29 21 2 cell_29_21_2
    | exact certificate_sound 29 21 3 cell_29_21_3
    | exact certificate_sound 29 21 4 cell_29_21_4
    | exact certificate_sound 29 21 5 cell_29_21_5
theorem cell_29_22_0 : CertificateAt 29 22 0 := by decide +kernel
theorem cell_29_22_1 : CertificateAt 29 22 1 := by decide +kernel
theorem cell_29_22_2 : CertificateAt 29 22 2 := by decide +kernel
theorem cell_29_22_3 : CertificateAt 29 22 3 := by decide +kernel
theorem cell_29_22_4 : CertificateAt 29 22 4 := by decide +kernel
theorem cell_29_22_5 : CertificateAt 29 22 5 := by decide +kernel
theorem row_29_22 : ThresholdAt 29 22 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 22 0 cell_29_22_0
    | exact certificate_sound 29 22 1 cell_29_22_1
    | exact certificate_sound 29 22 2 cell_29_22_2
    | exact certificate_sound 29 22 3 cell_29_22_3
    | exact certificate_sound 29 22 4 cell_29_22_4
    | exact certificate_sound 29 22 5 cell_29_22_5
theorem cell_29_23_0 : CertificateAt 29 23 0 := by decide +kernel
theorem cell_29_23_1 : CertificateAt 29 23 1 := by decide +kernel
theorem cell_29_23_2 : CertificateAt 29 23 2 := by decide +kernel
theorem cell_29_23_3 : CertificateAt 29 23 3 := by decide +kernel
theorem cell_29_23_4 : CertificateAt 29 23 4 := by decide +kernel
theorem cell_29_23_5 : CertificateAt 29 23 5 := by decide +kernel
theorem row_29_23 : ThresholdAt 29 23 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 23 0 cell_29_23_0
    | exact certificate_sound 29 23 1 cell_29_23_1
    | exact certificate_sound 29 23 2 cell_29_23_2
    | exact certificate_sound 29 23 3 cell_29_23_3
    | exact certificate_sound 29 23 4 cell_29_23_4
    | exact certificate_sound 29 23 5 cell_29_23_5
theorem cell_29_24_0 : CertificateAt 29 24 0 := by decide +kernel
theorem cell_29_24_1 : CertificateAt 29 24 1 := by decide +kernel
theorem cell_29_24_2 : CertificateAt 29 24 2 := by decide +kernel
theorem cell_29_24_3 : CertificateAt 29 24 3 := by decide +kernel
theorem cell_29_24_4 : CertificateAt 29 24 4 := by decide +kernel
theorem cell_29_24_5 : CertificateAt 29 24 5 := by decide +kernel
theorem row_29_24 : ThresholdAt 29 24 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 24 0 cell_29_24_0
    | exact certificate_sound 29 24 1 cell_29_24_1
    | exact certificate_sound 29 24 2 cell_29_24_2
    | exact certificate_sound 29 24 3 cell_29_24_3
    | exact certificate_sound 29 24 4 cell_29_24_4
    | exact certificate_sound 29 24 5 cell_29_24_5
theorem cell_29_25_0 : CertificateAt 29 25 0 := by decide +kernel
theorem cell_29_25_1 : CertificateAt 29 25 1 := by decide +kernel
theorem cell_29_25_2 : CertificateAt 29 25 2 := by decide +kernel
theorem cell_29_25_3 : CertificateAt 29 25 3 := by decide +kernel
theorem cell_29_25_4 : CertificateAt 29 25 4 := by decide +kernel
theorem cell_29_25_5 : CertificateAt 29 25 5 := by decide +kernel
theorem row_29_25 : ThresholdAt 29 25 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 25 0 cell_29_25_0
    | exact certificate_sound 29 25 1 cell_29_25_1
    | exact certificate_sound 29 25 2 cell_29_25_2
    | exact certificate_sound 29 25 3 cell_29_25_3
    | exact certificate_sound 29 25 4 cell_29_25_4
    | exact certificate_sound 29 25 5 cell_29_25_5
theorem cell_29_26_0 : CertificateAt 29 26 0 := by decide +kernel
theorem cell_29_26_1 : CertificateAt 29 26 1 := by decide +kernel
theorem cell_29_26_2 : CertificateAt 29 26 2 := by decide +kernel
theorem cell_29_26_3 : CertificateAt 29 26 3 := by decide +kernel
theorem cell_29_26_4 : CertificateAt 29 26 4 := by decide +kernel
theorem cell_29_26_5 : CertificateAt 29 26 5 := by decide +kernel
theorem row_29_26 : ThresholdAt 29 26 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 26 0 cell_29_26_0
    | exact certificate_sound 29 26 1 cell_29_26_1
    | exact certificate_sound 29 26 2 cell_29_26_2
    | exact certificate_sound 29 26 3 cell_29_26_3
    | exact certificate_sound 29 26 4 cell_29_26_4
    | exact certificate_sound 29 26 5 cell_29_26_5
theorem cell_29_27_0 : CertificateAt 29 27 0 := by decide +kernel
theorem cell_29_27_1 : CertificateAt 29 27 1 := by decide +kernel
theorem cell_29_27_2 : CertificateAt 29 27 2 := by decide +kernel
theorem cell_29_27_3 : CertificateAt 29 27 3 := by decide +kernel
theorem cell_29_27_4 : CertificateAt 29 27 4 := by decide +kernel
theorem cell_29_27_5 : CertificateAt 29 27 5 := by decide +kernel
theorem row_29_27 : ThresholdAt 29 27 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 27 0 cell_29_27_0
    | exact certificate_sound 29 27 1 cell_29_27_1
    | exact certificate_sound 29 27 2 cell_29_27_2
    | exact certificate_sound 29 27 3 cell_29_27_3
    | exact certificate_sound 29 27 4 cell_29_27_4
    | exact certificate_sound 29 27 5 cell_29_27_5
theorem cell_29_28_0 : CertificateAt 29 28 0 := by decide +kernel
theorem cell_29_28_1 : CertificateAt 29 28 1 := by decide +kernel
theorem cell_29_28_2 : CertificateAt 29 28 2 := by decide +kernel
theorem cell_29_28_3 : CertificateAt 29 28 3 := by decide +kernel
theorem cell_29_28_4 : CertificateAt 29 28 4 := by decide +kernel
theorem cell_29_28_5 : CertificateAt 29 28 5 := by decide +kernel
theorem row_29_28 : ThresholdAt 29 28 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 28 0 cell_29_28_0
    | exact certificate_sound 29 28 1 cell_29_28_1
    | exact certificate_sound 29 28 2 cell_29_28_2
    | exact certificate_sound 29 28 3 cell_29_28_3
    | exact certificate_sound 29 28 4 cell_29_28_4
    | exact certificate_sound 29 28 5 cell_29_28_5
theorem cell_29_29_0 : CertificateAt 29 29 0 := by decide +kernel
theorem cell_29_29_1 : CertificateAt 29 29 1 := by decide +kernel
theorem cell_29_29_2 : CertificateAt 29 29 2 := by decide +kernel
theorem cell_29_29_3 : CertificateAt 29 29 3 := by decide +kernel
theorem cell_29_29_4 : CertificateAt 29 29 4 := by decide +kernel
theorem cell_29_29_5 : CertificateAt 29 29 5 := by decide +kernel
theorem row_29_29 : ThresholdAt 29 29 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 29 0 cell_29_29_0
    | exact certificate_sound 29 29 1 cell_29_29_1
    | exact certificate_sound 29 29 2 cell_29_29_2
    | exact certificate_sound 29 29 3 cell_29_29_3
    | exact certificate_sound 29 29 4 cell_29_29_4
    | exact certificate_sound 29 29 5 cell_29_29_5
theorem cell_29_30_0 : CertificateAt 29 30 0 := by decide +kernel
theorem cell_29_30_1 : CertificateAt 29 30 1 := by decide +kernel
theorem cell_29_30_2 : CertificateAt 29 30 2 := by decide +kernel
theorem cell_29_30_3 : CertificateAt 29 30 3 := by decide +kernel
theorem cell_29_30_4 : CertificateAt 29 30 4 := by decide +kernel
theorem cell_29_30_5 : CertificateAt 29 30 5 := by decide +kernel
theorem row_29_30 : ThresholdAt 29 30 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 30 0 cell_29_30_0
    | exact certificate_sound 29 30 1 cell_29_30_1
    | exact certificate_sound 29 30 2 cell_29_30_2
    | exact certificate_sound 29 30 3 cell_29_30_3
    | exact certificate_sound 29 30 4 cell_29_30_4
    | exact certificate_sound 29 30 5 cell_29_30_5
theorem cell_29_31_0 : CertificateAt 29 31 0 := by decide +kernel
theorem cell_29_31_1 : CertificateAt 29 31 1 := by decide +kernel
theorem cell_29_31_2 : CertificateAt 29 31 2 := by decide +kernel
theorem cell_29_31_3 : CertificateAt 29 31 3 := by decide +kernel
theorem cell_29_31_4 : CertificateAt 29 31 4 := by decide +kernel
theorem cell_29_31_5 : CertificateAt 29 31 5 := by decide +kernel
theorem row_29_31 : ThresholdAt 29 31 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 31 0 cell_29_31_0
    | exact certificate_sound 29 31 1 cell_29_31_1
    | exact certificate_sound 29 31 2 cell_29_31_2
    | exact certificate_sound 29 31 3 cell_29_31_3
    | exact certificate_sound 29 31 4 cell_29_31_4
    | exact certificate_sound 29 31 5 cell_29_31_5
theorem cell_29_32_0 : CertificateAt 29 32 0 := by decide +kernel
theorem cell_29_32_1 : CertificateAt 29 32 1 := by decide +kernel
theorem cell_29_32_2 : CertificateAt 29 32 2 := by decide +kernel
theorem cell_29_32_3 : CertificateAt 29 32 3 := by decide +kernel
theorem cell_29_32_4 : CertificateAt 29 32 4 := by decide +kernel
theorem cell_29_32_5 : CertificateAt 29 32 5 := by decide +kernel
theorem row_29_32 : ThresholdAt 29 32 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 32 0 cell_29_32_0
    | exact certificate_sound 29 32 1 cell_29_32_1
    | exact certificate_sound 29 32 2 cell_29_32_2
    | exact certificate_sound 29 32 3 cell_29_32_3
    | exact certificate_sound 29 32 4 cell_29_32_4
    | exact certificate_sound 29 32 5 cell_29_32_5
theorem cell_29_33_0 : CertificateAt 29 33 0 := by decide +kernel
theorem cell_29_33_1 : CertificateAt 29 33 1 := by decide +kernel
theorem cell_29_33_2 : CertificateAt 29 33 2 := by decide +kernel
theorem cell_29_33_3 : CertificateAt 29 33 3 := by decide +kernel
theorem cell_29_33_4 : CertificateAt 29 33 4 := by decide +kernel
theorem cell_29_33_5 : CertificateAt 29 33 5 := by decide +kernel
theorem row_29_33 : ThresholdAt 29 33 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 33 0 cell_29_33_0
    | exact certificate_sound 29 33 1 cell_29_33_1
    | exact certificate_sound 29 33 2 cell_29_33_2
    | exact certificate_sound 29 33 3 cell_29_33_3
    | exact certificate_sound 29 33 4 cell_29_33_4
    | exact certificate_sound 29 33 5 cell_29_33_5
theorem cell_29_34_0 : CertificateAt 29 34 0 := by decide +kernel
theorem cell_29_34_1 : CertificateAt 29 34 1 := by decide +kernel
theorem cell_29_34_2 : CertificateAt 29 34 2 := by decide +kernel
theorem cell_29_34_3 : CertificateAt 29 34 3 := by decide +kernel
theorem cell_29_34_4 : CertificateAt 29 34 4 := by decide +kernel
theorem cell_29_34_5 : CertificateAt 29 34 5 := by decide +kernel
theorem row_29_34 : ThresholdAt 29 34 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 34 0 cell_29_34_0
    | exact certificate_sound 29 34 1 cell_29_34_1
    | exact certificate_sound 29 34 2 cell_29_34_2
    | exact certificate_sound 29 34 3 cell_29_34_3
    | exact certificate_sound 29 34 4 cell_29_34_4
    | exact certificate_sound 29 34 5 cell_29_34_5
theorem cell_29_35_0 : CertificateAt 29 35 0 := by decide +kernel
theorem cell_29_35_1 : CertificateAt 29 35 1 := by decide +kernel
theorem cell_29_35_2 : CertificateAt 29 35 2 := by decide +kernel
theorem cell_29_35_3 : CertificateAt 29 35 3 := by decide +kernel
theorem cell_29_35_4 : CertificateAt 29 35 4 := by decide +kernel
theorem cell_29_35_5 : CertificateAt 29 35 5 := by decide +kernel
theorem row_29_35 : ThresholdAt 29 35 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 35 0 cell_29_35_0
    | exact certificate_sound 29 35 1 cell_29_35_1
    | exact certificate_sound 29 35 2 cell_29_35_2
    | exact certificate_sound 29 35 3 cell_29_35_3
    | exact certificate_sound 29 35 4 cell_29_35_4
    | exact certificate_sound 29 35 5 cell_29_35_5
theorem cell_29_36_0 : CertificateAt 29 36 0 := by decide +kernel
theorem cell_29_36_1 : CertificateAt 29 36 1 := by decide +kernel
theorem cell_29_36_2 : CertificateAt 29 36 2 := by decide +kernel
theorem cell_29_36_3 : CertificateAt 29 36 3 := by decide +kernel
theorem cell_29_36_4 : CertificateAt 29 36 4 := by decide +kernel
theorem cell_29_36_5 : CertificateAt 29 36 5 := by decide +kernel
theorem row_29_36 : ThresholdAt 29 36 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 36 0 cell_29_36_0
    | exact certificate_sound 29 36 1 cell_29_36_1
    | exact certificate_sound 29 36 2 cell_29_36_2
    | exact certificate_sound 29 36 3 cell_29_36_3
    | exact certificate_sound 29 36 4 cell_29_36_4
    | exact certificate_sound 29 36 5 cell_29_36_5
theorem cell_29_37_0 : CertificateAt 29 37 0 := by decide +kernel
theorem cell_29_37_1 : CertificateAt 29 37 1 := by decide +kernel
theorem cell_29_37_2 : CertificateAt 29 37 2 := by decide +kernel
theorem cell_29_37_3 : CertificateAt 29 37 3 := by decide +kernel
theorem cell_29_37_4 : CertificateAt 29 37 4 := by decide +kernel
theorem cell_29_37_5 : CertificateAt 29 37 5 := by decide +kernel
theorem row_29_37 : ThresholdAt 29 37 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 37 0 cell_29_37_0
    | exact certificate_sound 29 37 1 cell_29_37_1
    | exact certificate_sound 29 37 2 cell_29_37_2
    | exact certificate_sound 29 37 3 cell_29_37_3
    | exact certificate_sound 29 37 4 cell_29_37_4
    | exact certificate_sound 29 37 5 cell_29_37_5
theorem cell_29_38_0 : CertificateAt 29 38 0 := by decide +kernel
theorem cell_29_38_1 : CertificateAt 29 38 1 := by decide +kernel
theorem cell_29_38_2 : CertificateAt 29 38 2 := by decide +kernel
theorem cell_29_38_3 : CertificateAt 29 38 3 := by decide +kernel
theorem cell_29_38_4 : CertificateAt 29 38 4 := by decide +kernel
theorem cell_29_38_5 : CertificateAt 29 38 5 := by decide +kernel
theorem row_29_38 : ThresholdAt 29 38 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 38 0 cell_29_38_0
    | exact certificate_sound 29 38 1 cell_29_38_1
    | exact certificate_sound 29 38 2 cell_29_38_2
    | exact certificate_sound 29 38 3 cell_29_38_3
    | exact certificate_sound 29 38 4 cell_29_38_4
    | exact certificate_sound 29 38 5 cell_29_38_5
theorem cell_29_39_0 : CertificateAt 29 39 0 := by decide +kernel
theorem cell_29_39_1 : CertificateAt 29 39 1 := by decide +kernel
theorem cell_29_39_2 : CertificateAt 29 39 2 := by decide +kernel
theorem cell_29_39_3 : CertificateAt 29 39 3 := by decide +kernel
theorem cell_29_39_4 : CertificateAt 29 39 4 := by decide +kernel
theorem cell_29_39_5 : CertificateAt 29 39 5 := by decide +kernel
theorem row_29_39 : ThresholdAt 29 39 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 39 0 cell_29_39_0
    | exact certificate_sound 29 39 1 cell_29_39_1
    | exact certificate_sound 29 39 2 cell_29_39_2
    | exact certificate_sound 29 39 3 cell_29_39_3
    | exact certificate_sound 29 39 4 cell_29_39_4
    | exact certificate_sound 29 39 5 cell_29_39_5
theorem cell_29_40_0 : CertificateAt 29 40 0 := by decide +kernel
theorem cell_29_40_1 : CertificateAt 29 40 1 := by decide +kernel
theorem cell_29_40_2 : CertificateAt 29 40 2 := by decide +kernel
theorem cell_29_40_3 : CertificateAt 29 40 3 := by decide +kernel
theorem cell_29_40_4 : CertificateAt 29 40 4 := by decide +kernel
theorem cell_29_40_5 : CertificateAt 29 40 5 := by decide +kernel
theorem row_29_40 : ThresholdAt 29 40 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 40 0 cell_29_40_0
    | exact certificate_sound 29 40 1 cell_29_40_1
    | exact certificate_sound 29 40 2 cell_29_40_2
    | exact certificate_sound 29 40 3 cell_29_40_3
    | exact certificate_sound 29 40 4 cell_29_40_4
    | exact certificate_sound 29 40 5 cell_29_40_5
theorem cell_29_41_0 : CertificateAt 29 41 0 := by decide +kernel
theorem cell_29_41_1 : CertificateAt 29 41 1 := by decide +kernel
theorem cell_29_41_2 : CertificateAt 29 41 2 := by decide +kernel
theorem cell_29_41_3 : CertificateAt 29 41 3 := by decide +kernel
theorem cell_29_41_4 : CertificateAt 29 41 4 := by decide +kernel
theorem cell_29_41_5 : CertificateAt 29 41 5 := by decide +kernel
theorem row_29_41 : ThresholdAt 29 41 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 41 0 cell_29_41_0
    | exact certificate_sound 29 41 1 cell_29_41_1
    | exact certificate_sound 29 41 2 cell_29_41_2
    | exact certificate_sound 29 41 3 cell_29_41_3
    | exact certificate_sound 29 41 4 cell_29_41_4
    | exact certificate_sound 29 41 5 cell_29_41_5
theorem cell_29_42_0 : CertificateAt 29 42 0 := by decide +kernel
theorem cell_29_42_1 : CertificateAt 29 42 1 := by decide +kernel
theorem cell_29_42_2 : CertificateAt 29 42 2 := by decide +kernel
theorem cell_29_42_3 : CertificateAt 29 42 3 := by decide +kernel
theorem cell_29_42_4 : CertificateAt 29 42 4 := by decide +kernel
theorem cell_29_42_5 : CertificateAt 29 42 5 := by decide +kernel
theorem row_29_42 : ThresholdAt 29 42 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 42 0 cell_29_42_0
    | exact certificate_sound 29 42 1 cell_29_42_1
    | exact certificate_sound 29 42 2 cell_29_42_2
    | exact certificate_sound 29 42 3 cell_29_42_3
    | exact certificate_sound 29 42 4 cell_29_42_4
    | exact certificate_sound 29 42 5 cell_29_42_5
theorem cell_29_43_0 : CertificateAt 29 43 0 := by decide +kernel
theorem cell_29_43_1 : CertificateAt 29 43 1 := by decide +kernel
theorem cell_29_43_2 : CertificateAt 29 43 2 := by decide +kernel
theorem cell_29_43_3 : CertificateAt 29 43 3 := by decide +kernel
theorem cell_29_43_4 : CertificateAt 29 43 4 := by decide +kernel
theorem cell_29_43_5 : CertificateAt 29 43 5 := by decide +kernel
theorem row_29_43 : ThresholdAt 29 43 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 43 0 cell_29_43_0
    | exact certificate_sound 29 43 1 cell_29_43_1
    | exact certificate_sound 29 43 2 cell_29_43_2
    | exact certificate_sound 29 43 3 cell_29_43_3
    | exact certificate_sound 29 43 4 cell_29_43_4
    | exact certificate_sound 29 43 5 cell_29_43_5
theorem cell_29_44_0 : CertificateAt 29 44 0 := by decide +kernel
theorem cell_29_44_1 : CertificateAt 29 44 1 := by decide +kernel
theorem cell_29_44_2 : CertificateAt 29 44 2 := by decide +kernel
theorem cell_29_44_3 : CertificateAt 29 44 3 := by decide +kernel
theorem cell_29_44_4 : CertificateAt 29 44 4 := by decide +kernel
theorem cell_29_44_5 : CertificateAt 29 44 5 := by decide +kernel
theorem row_29_44 : ThresholdAt 29 44 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 44 0 cell_29_44_0
    | exact certificate_sound 29 44 1 cell_29_44_1
    | exact certificate_sound 29 44 2 cell_29_44_2
    | exact certificate_sound 29 44 3 cell_29_44_3
    | exact certificate_sound 29 44 4 cell_29_44_4
    | exact certificate_sound 29 44 5 cell_29_44_5
theorem cell_29_45_0 : CertificateAt 29 45 0 := by decide +kernel
theorem cell_29_45_1 : CertificateAt 29 45 1 := by decide +kernel
theorem cell_29_45_2 : CertificateAt 29 45 2 := by decide +kernel
theorem cell_29_45_3 : CertificateAt 29 45 3 := by decide +kernel
theorem cell_29_45_4 : CertificateAt 29 45 4 := by decide +kernel
theorem cell_29_45_5 : CertificateAt 29 45 5 := by decide +kernel
theorem row_29_45 : ThresholdAt 29 45 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 45 0 cell_29_45_0
    | exact certificate_sound 29 45 1 cell_29_45_1
    | exact certificate_sound 29 45 2 cell_29_45_2
    | exact certificate_sound 29 45 3 cell_29_45_3
    | exact certificate_sound 29 45 4 cell_29_45_4
    | exact certificate_sound 29 45 5 cell_29_45_5
theorem cell_29_46_0 : CertificateAt 29 46 0 := by decide +kernel
theorem cell_29_46_1 : CertificateAt 29 46 1 := by decide +kernel
theorem cell_29_46_2 : CertificateAt 29 46 2 := by decide +kernel
theorem cell_29_46_3 : CertificateAt 29 46 3 := by decide +kernel
theorem cell_29_46_4 : CertificateAt 29 46 4 := by decide +kernel
theorem cell_29_46_5 : CertificateAt 29 46 5 := by decide +kernel
theorem row_29_46 : ThresholdAt 29 46 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 46 0 cell_29_46_0
    | exact certificate_sound 29 46 1 cell_29_46_1
    | exact certificate_sound 29 46 2 cell_29_46_2
    | exact certificate_sound 29 46 3 cell_29_46_3
    | exact certificate_sound 29 46 4 cell_29_46_4
    | exact certificate_sound 29 46 5 cell_29_46_5
theorem cell_29_47_0 : CertificateAt 29 47 0 := by decide +kernel
theorem cell_29_47_1 : CertificateAt 29 47 1 := by decide +kernel
theorem cell_29_47_2 : CertificateAt 29 47 2 := by decide +kernel
theorem cell_29_47_3 : CertificateAt 29 47 3 := by decide +kernel
theorem cell_29_47_4 : CertificateAt 29 47 4 := by decide +kernel
theorem cell_29_47_5 : CertificateAt 29 47 5 := by decide +kernel
theorem row_29_47 : ThresholdAt 29 47 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 47 0 cell_29_47_0
    | exact certificate_sound 29 47 1 cell_29_47_1
    | exact certificate_sound 29 47 2 cell_29_47_2
    | exact certificate_sound 29 47 3 cell_29_47_3
    | exact certificate_sound 29 47 4 cell_29_47_4
    | exact certificate_sound 29 47 5 cell_29_47_5
theorem cell_29_48_0 : CertificateAt 29 48 0 := by decide +kernel
theorem cell_29_48_1 : CertificateAt 29 48 1 := by decide +kernel
theorem cell_29_48_2 : CertificateAt 29 48 2 := by decide +kernel
theorem cell_29_48_3 : CertificateAt 29 48 3 := by decide +kernel
theorem cell_29_48_4 : CertificateAt 29 48 4 := by decide +kernel
theorem cell_29_48_5 : CertificateAt 29 48 5 := by decide +kernel
theorem row_29_48 : ThresholdAt 29 48 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 48 0 cell_29_48_0
    | exact certificate_sound 29 48 1 cell_29_48_1
    | exact certificate_sound 29 48 2 cell_29_48_2
    | exact certificate_sound 29 48 3 cell_29_48_3
    | exact certificate_sound 29 48 4 cell_29_48_4
    | exact certificate_sound 29 48 5 cell_29_48_5
theorem cell_29_49_0 : CertificateAt 29 49 0 := by decide +kernel
theorem cell_29_49_1 : CertificateAt 29 49 1 := by decide +kernel
theorem cell_29_49_2 : CertificateAt 29 49 2 := by decide +kernel
theorem cell_29_49_3 : CertificateAt 29 49 3 := by decide +kernel
theorem cell_29_49_4 : CertificateAt 29 49 4 := by decide +kernel
theorem cell_29_49_5 : CertificateAt 29 49 5 := by decide +kernel
theorem row_29_49 : ThresholdAt 29 49 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 49 0 cell_29_49_0
    | exact certificate_sound 29 49 1 cell_29_49_1
    | exact certificate_sound 29 49 2 cell_29_49_2
    | exact certificate_sound 29 49 3 cell_29_49_3
    | exact certificate_sound 29 49 4 cell_29_49_4
    | exact certificate_sound 29 49 5 cell_29_49_5
theorem cell_29_50_0 : CertificateAt 29 50 0 := by decide +kernel
theorem cell_29_50_1 : CertificateAt 29 50 1 := by decide +kernel
theorem cell_29_50_2 : CertificateAt 29 50 2 := by decide +kernel
theorem cell_29_50_3 : CertificateAt 29 50 3 := by decide +kernel
theorem cell_29_50_4 : CertificateAt 29 50 4 := by decide +kernel
theorem cell_29_50_5 : CertificateAt 29 50 5 := by decide +kernel
theorem row_29_50 : ThresholdAt 29 50 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 50 0 cell_29_50_0
    | exact certificate_sound 29 50 1 cell_29_50_1
    | exact certificate_sound 29 50 2 cell_29_50_2
    | exact certificate_sound 29 50 3 cell_29_50_3
    | exact certificate_sound 29 50 4 cell_29_50_4
    | exact certificate_sound 29 50 5 cell_29_50_5
theorem cell_29_51_0 : CertificateAt 29 51 0 := by decide +kernel
theorem cell_29_51_1 : CertificateAt 29 51 1 := by decide +kernel
theorem cell_29_51_2 : CertificateAt 29 51 2 := by decide +kernel
theorem cell_29_51_3 : CertificateAt 29 51 3 := by decide +kernel
theorem cell_29_51_4 : CertificateAt 29 51 4 := by decide +kernel
theorem cell_29_51_5 : CertificateAt 29 51 5 := by decide +kernel
theorem row_29_51 : ThresholdAt 29 51 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 51 0 cell_29_51_0
    | exact certificate_sound 29 51 1 cell_29_51_1
    | exact certificate_sound 29 51 2 cell_29_51_2
    | exact certificate_sound 29 51 3 cell_29_51_3
    | exact certificate_sound 29 51 4 cell_29_51_4
    | exact certificate_sound 29 51 5 cell_29_51_5
theorem cell_29_52_0 : CertificateAt 29 52 0 := by decide +kernel
theorem cell_29_52_1 : CertificateAt 29 52 1 := by decide +kernel
theorem cell_29_52_2 : CertificateAt 29 52 2 := by decide +kernel
theorem cell_29_52_3 : CertificateAt 29 52 3 := by decide +kernel
theorem cell_29_52_4 : CertificateAt 29 52 4 := by decide +kernel
theorem cell_29_52_5 : CertificateAt 29 52 5 := by decide +kernel
theorem row_29_52 : ThresholdAt 29 52 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 52 0 cell_29_52_0
    | exact certificate_sound 29 52 1 cell_29_52_1
    | exact certificate_sound 29 52 2 cell_29_52_2
    | exact certificate_sound 29 52 3 cell_29_52_3
    | exact certificate_sound 29 52 4 cell_29_52_4
    | exact certificate_sound 29 52 5 cell_29_52_5
theorem cell_29_53_0 : CertificateAt 29 53 0 := by decide +kernel
theorem cell_29_53_1 : CertificateAt 29 53 1 := by decide +kernel
theorem cell_29_53_2 : CertificateAt 29 53 2 := by decide +kernel
theorem cell_29_53_3 : CertificateAt 29 53 3 := by decide +kernel
theorem cell_29_53_4 : CertificateAt 29 53 4 := by decide +kernel
theorem cell_29_53_5 : CertificateAt 29 53 5 := by decide +kernel
theorem row_29_53 : ThresholdAt 29 53 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 53 0 cell_29_53_0
    | exact certificate_sound 29 53 1 cell_29_53_1
    | exact certificate_sound 29 53 2 cell_29_53_2
    | exact certificate_sound 29 53 3 cell_29_53_3
    | exact certificate_sound 29 53 4 cell_29_53_4
    | exact certificate_sound 29 53 5 cell_29_53_5
theorem cell_29_54_0 : CertificateAt 29 54 0 := by decide +kernel
theorem cell_29_54_1 : CertificateAt 29 54 1 := by decide +kernel
theorem cell_29_54_2 : CertificateAt 29 54 2 := by decide +kernel
theorem cell_29_54_3 : CertificateAt 29 54 3 := by decide +kernel
theorem cell_29_54_4 : CertificateAt 29 54 4 := by decide +kernel
theorem cell_29_54_5 : CertificateAt 29 54 5 := by decide +kernel
theorem row_29_54 : ThresholdAt 29 54 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 54 0 cell_29_54_0
    | exact certificate_sound 29 54 1 cell_29_54_1
    | exact certificate_sound 29 54 2 cell_29_54_2
    | exact certificate_sound 29 54 3 cell_29_54_3
    | exact certificate_sound 29 54 4 cell_29_54_4
    | exact certificate_sound 29 54 5 cell_29_54_5
theorem cell_29_55_0 : CertificateAt 29 55 0 := by decide +kernel
theorem cell_29_55_1 : CertificateAt 29 55 1 := by decide +kernel
theorem cell_29_55_2 : CertificateAt 29 55 2 := by decide +kernel
theorem cell_29_55_3 : CertificateAt 29 55 3 := by decide +kernel
theorem cell_29_55_4 : CertificateAt 29 55 4 := by decide +kernel
theorem cell_29_55_5 : CertificateAt 29 55 5 := by decide +kernel
theorem row_29_55 : ThresholdAt 29 55 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 55 0 cell_29_55_0
    | exact certificate_sound 29 55 1 cell_29_55_1
    | exact certificate_sound 29 55 2 cell_29_55_2
    | exact certificate_sound 29 55 3 cell_29_55_3
    | exact certificate_sound 29 55 4 cell_29_55_4
    | exact certificate_sound 29 55 5 cell_29_55_5
theorem cell_29_56_0 : CertificateAt 29 56 0 := by decide +kernel
theorem cell_29_56_1 : CertificateAt 29 56 1 := by decide +kernel
theorem cell_29_56_2 : CertificateAt 29 56 2 := by decide +kernel
theorem cell_29_56_3 : CertificateAt 29 56 3 := by decide +kernel
theorem cell_29_56_4 : CertificateAt 29 56 4 := by decide +kernel
theorem cell_29_56_5 : CertificateAt 29 56 5 := by decide +kernel
theorem row_29_56 : ThresholdAt 29 56 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 56 0 cell_29_56_0
    | exact certificate_sound 29 56 1 cell_29_56_1
    | exact certificate_sound 29 56 2 cell_29_56_2
    | exact certificate_sound 29 56 3 cell_29_56_3
    | exact certificate_sound 29 56 4 cell_29_56_4
    | exact certificate_sound 29 56 5 cell_29_56_5
theorem cell_29_57_0 : CertificateAt 29 57 0 := by decide +kernel
theorem cell_29_57_1 : CertificateAt 29 57 1 := by decide +kernel
theorem cell_29_57_2 : CertificateAt 29 57 2 := by decide +kernel
theorem cell_29_57_3 : CertificateAt 29 57 3 := by decide +kernel
theorem cell_29_57_4 : CertificateAt 29 57 4 := by decide +kernel
theorem cell_29_57_5 : CertificateAt 29 57 5 := by decide +kernel
theorem row_29_57 : ThresholdAt 29 57 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 57 0 cell_29_57_0
    | exact certificate_sound 29 57 1 cell_29_57_1
    | exact certificate_sound 29 57 2 cell_29_57_2
    | exact certificate_sound 29 57 3 cell_29_57_3
    | exact certificate_sound 29 57 4 cell_29_57_4
    | exact certificate_sound 29 57 5 cell_29_57_5
theorem cell_29_58_0 : CertificateAt 29 58 0 := by decide +kernel
theorem cell_29_58_1 : CertificateAt 29 58 1 := by decide +kernel
theorem cell_29_58_2 : CertificateAt 29 58 2 := by decide +kernel
theorem cell_29_58_3 : CertificateAt 29 58 3 := by decide +kernel
theorem cell_29_58_4 : CertificateAt 29 58 4 := by decide +kernel
theorem cell_29_58_5 : CertificateAt 29 58 5 := by decide +kernel
theorem row_29_58 : ThresholdAt 29 58 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 58 0 cell_29_58_0
    | exact certificate_sound 29 58 1 cell_29_58_1
    | exact certificate_sound 29 58 2 cell_29_58_2
    | exact certificate_sound 29 58 3 cell_29_58_3
    | exact certificate_sound 29 58 4 cell_29_58_4
    | exact certificate_sound 29 58 5 cell_29_58_5
theorem cell_29_59_0 : CertificateAt 29 59 0 := by decide +kernel
theorem cell_29_59_1 : CertificateAt 29 59 1 := by decide +kernel
theorem cell_29_59_2 : CertificateAt 29 59 2 := by decide +kernel
theorem cell_29_59_3 : CertificateAt 29 59 3 := by decide +kernel
theorem cell_29_59_4 : CertificateAt 29 59 4 := by decide +kernel
theorem cell_29_59_5 : CertificateAt 29 59 5 := by decide +kernel
theorem row_29_59 : ThresholdAt 29 59 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 59 0 cell_29_59_0
    | exact certificate_sound 29 59 1 cell_29_59_1
    | exact certificate_sound 29 59 2 cell_29_59_2
    | exact certificate_sound 29 59 3 cell_29_59_3
    | exact certificate_sound 29 59 4 cell_29_59_4
    | exact certificate_sound 29 59 5 cell_29_59_5
theorem cell_29_60_0 : CertificateAt 29 60 0 := by decide +kernel
theorem cell_29_60_1 : CertificateAt 29 60 1 := by decide +kernel
theorem cell_29_60_2 : CertificateAt 29 60 2 := by decide +kernel
theorem cell_29_60_3 : CertificateAt 29 60 3 := by decide +kernel
theorem cell_29_60_4 : CertificateAt 29 60 4 := by decide +kernel
theorem cell_29_60_5 : CertificateAt 29 60 5 := by decide +kernel
theorem row_29_60 : ThresholdAt 29 60 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 60 0 cell_29_60_0
    | exact certificate_sound 29 60 1 cell_29_60_1
    | exact certificate_sound 29 60 2 cell_29_60_2
    | exact certificate_sound 29 60 3 cell_29_60_3
    | exact certificate_sound 29 60 4 cell_29_60_4
    | exact certificate_sound 29 60 5 cell_29_60_5
theorem cell_29_61_0 : CertificateAt 29 61 0 := by decide +kernel
theorem cell_29_61_1 : CertificateAt 29 61 1 := by decide +kernel
theorem cell_29_61_2 : CertificateAt 29 61 2 := by decide +kernel
theorem cell_29_61_3 : CertificateAt 29 61 3 := by decide +kernel
theorem cell_29_61_4 : CertificateAt 29 61 4 := by decide +kernel
theorem cell_29_61_5 : CertificateAt 29 61 5 := by decide +kernel
theorem row_29_61 : ThresholdAt 29 61 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 61 0 cell_29_61_0
    | exact certificate_sound 29 61 1 cell_29_61_1
    | exact certificate_sound 29 61 2 cell_29_61_2
    | exact certificate_sound 29 61 3 cell_29_61_3
    | exact certificate_sound 29 61 4 cell_29_61_4
    | exact certificate_sound 29 61 5 cell_29_61_5
theorem cell_29_62_0 : CertificateAt 29 62 0 := by decide +kernel
theorem cell_29_62_1 : CertificateAt 29 62 1 := by decide +kernel
theorem cell_29_62_2 : CertificateAt 29 62 2 := by decide +kernel
theorem cell_29_62_3 : CertificateAt 29 62 3 := by decide +kernel
theorem cell_29_62_4 : CertificateAt 29 62 4 := by decide +kernel
theorem cell_29_62_5 : CertificateAt 29 62 5 := by decide +kernel
theorem row_29_62 : ThresholdAt 29 62 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 62 0 cell_29_62_0
    | exact certificate_sound 29 62 1 cell_29_62_1
    | exact certificate_sound 29 62 2 cell_29_62_2
    | exact certificate_sound 29 62 3 cell_29_62_3
    | exact certificate_sound 29 62 4 cell_29_62_4
    | exact certificate_sound 29 62 5 cell_29_62_5
theorem cell_29_63_0 : CertificateAt 29 63 0 := by decide +kernel
theorem cell_29_63_1 : CertificateAt 29 63 1 := by decide +kernel
theorem cell_29_63_2 : CertificateAt 29 63 2 := by decide +kernel
theorem cell_29_63_3 : CertificateAt 29 63 3 := by decide +kernel
theorem cell_29_63_4 : CertificateAt 29 63 4 := by decide +kernel
theorem cell_29_63_5 : CertificateAt 29 63 5 := by decide +kernel
theorem row_29_63 : ThresholdAt 29 63 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 63 0 cell_29_63_0
    | exact certificate_sound 29 63 1 cell_29_63_1
    | exact certificate_sound 29 63 2 cell_29_63_2
    | exact certificate_sound 29 63 3 cell_29_63_3
    | exact certificate_sound 29 63 4 cell_29_63_4
    | exact certificate_sound 29 63 5 cell_29_63_5
theorem cell_29_64_0 : CertificateAt 29 64 0 := by decide +kernel
theorem cell_29_64_1 : CertificateAt 29 64 1 := by decide +kernel
theorem cell_29_64_2 : CertificateAt 29 64 2 := by decide +kernel
theorem cell_29_64_3 : CertificateAt 29 64 3 := by decide +kernel
theorem cell_29_64_4 : CertificateAt 29 64 4 := by decide +kernel
theorem cell_29_64_5 : CertificateAt 29 64 5 := by decide +kernel
theorem row_29_64 : ThresholdAt 29 64 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 64 0 cell_29_64_0
    | exact certificate_sound 29 64 1 cell_29_64_1
    | exact certificate_sound 29 64 2 cell_29_64_2
    | exact certificate_sound 29 64 3 cell_29_64_3
    | exact certificate_sound 29 64 4 cell_29_64_4
    | exact certificate_sound 29 64 5 cell_29_64_5
theorem cell_29_65_0 : CertificateAt 29 65 0 := by decide +kernel
theorem cell_29_65_1 : CertificateAt 29 65 1 := by decide +kernel
theorem cell_29_65_2 : CertificateAt 29 65 2 := by decide +kernel
theorem cell_29_65_3 : CertificateAt 29 65 3 := by decide +kernel
theorem cell_29_65_4 : CertificateAt 29 65 4 := by decide +kernel
theorem cell_29_65_5 : CertificateAt 29 65 5 := by decide +kernel
theorem row_29_65 : ThresholdAt 29 65 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 65 0 cell_29_65_0
    | exact certificate_sound 29 65 1 cell_29_65_1
    | exact certificate_sound 29 65 2 cell_29_65_2
    | exact certificate_sound 29 65 3 cell_29_65_3
    | exact certificate_sound 29 65 4 cell_29_65_4
    | exact certificate_sound 29 65 5 cell_29_65_5
theorem cell_29_66_0 : CertificateAt 29 66 0 := by decide +kernel
theorem cell_29_66_1 : CertificateAt 29 66 1 := by decide +kernel
theorem cell_29_66_2 : CertificateAt 29 66 2 := by decide +kernel
theorem cell_29_66_3 : CertificateAt 29 66 3 := by decide +kernel
theorem cell_29_66_4 : CertificateAt 29 66 4 := by decide +kernel
theorem cell_29_66_5 : CertificateAt 29 66 5 := by decide +kernel
theorem row_29_66 : ThresholdAt 29 66 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 66 0 cell_29_66_0
    | exact certificate_sound 29 66 1 cell_29_66_1
    | exact certificate_sound 29 66 2 cell_29_66_2
    | exact certificate_sound 29 66 3 cell_29_66_3
    | exact certificate_sound 29 66 4 cell_29_66_4
    | exact certificate_sound 29 66 5 cell_29_66_5
theorem cell_29_67_0 : CertificateAt 29 67 0 := by decide +kernel
theorem cell_29_67_1 : CertificateAt 29 67 1 := by decide +kernel
theorem cell_29_67_2 : CertificateAt 29 67 2 := by decide +kernel
theorem cell_29_67_3 : CertificateAt 29 67 3 := by decide +kernel
theorem cell_29_67_4 : CertificateAt 29 67 4 := by decide +kernel
theorem cell_29_67_5 : CertificateAt 29 67 5 := by decide +kernel
theorem row_29_67 : ThresholdAt 29 67 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 67 0 cell_29_67_0
    | exact certificate_sound 29 67 1 cell_29_67_1
    | exact certificate_sound 29 67 2 cell_29_67_2
    | exact certificate_sound 29 67 3 cell_29_67_3
    | exact certificate_sound 29 67 4 cell_29_67_4
    | exact certificate_sound 29 67 5 cell_29_67_5
theorem cell_29_68_0 : CertificateAt 29 68 0 := by decide +kernel
theorem cell_29_68_1 : CertificateAt 29 68 1 := by decide +kernel
theorem cell_29_68_2 : CertificateAt 29 68 2 := by decide +kernel
theorem cell_29_68_3 : CertificateAt 29 68 3 := by decide +kernel
theorem cell_29_68_4 : CertificateAt 29 68 4 := by decide +kernel
theorem cell_29_68_5 : CertificateAt 29 68 5 := by decide +kernel
theorem row_29_68 : ThresholdAt 29 68 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 68 0 cell_29_68_0
    | exact certificate_sound 29 68 1 cell_29_68_1
    | exact certificate_sound 29 68 2 cell_29_68_2
    | exact certificate_sound 29 68 3 cell_29_68_3
    | exact certificate_sound 29 68 4 cell_29_68_4
    | exact certificate_sound 29 68 5 cell_29_68_5
theorem cell_29_69_0 : CertificateAt 29 69 0 := by decide +kernel
theorem cell_29_69_1 : CertificateAt 29 69 1 := by decide +kernel
theorem cell_29_69_2 : CertificateAt 29 69 2 := by decide +kernel
theorem cell_29_69_3 : CertificateAt 29 69 3 := by decide +kernel
theorem cell_29_69_4 : CertificateAt 29 69 4 := by decide +kernel
theorem cell_29_69_5 : CertificateAt 29 69 5 := by decide +kernel
theorem row_29_69 : ThresholdAt 29 69 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 69 0 cell_29_69_0
    | exact certificate_sound 29 69 1 cell_29_69_1
    | exact certificate_sound 29 69 2 cell_29_69_2
    | exact certificate_sound 29 69 3 cell_29_69_3
    | exact certificate_sound 29 69 4 cell_29_69_4
    | exact certificate_sound 29 69 5 cell_29_69_5
theorem cell_29_70_0 : CertificateAt 29 70 0 := by decide +kernel
theorem cell_29_70_1 : CertificateAt 29 70 1 := by decide +kernel
theorem cell_29_70_2 : CertificateAt 29 70 2 := by decide +kernel
theorem cell_29_70_3 : CertificateAt 29 70 3 := by decide +kernel
theorem cell_29_70_4 : CertificateAt 29 70 4 := by decide +kernel
theorem cell_29_70_5 : CertificateAt 29 70 5 := by decide +kernel
theorem row_29_70 : ThresholdAt 29 70 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 70 0 cell_29_70_0
    | exact certificate_sound 29 70 1 cell_29_70_1
    | exact certificate_sound 29 70 2 cell_29_70_2
    | exact certificate_sound 29 70 3 cell_29_70_3
    | exact certificate_sound 29 70 4 cell_29_70_4
    | exact certificate_sound 29 70 5 cell_29_70_5
theorem cell_29_71_0 : CertificateAt 29 71 0 := by decide +kernel
theorem cell_29_71_1 : CertificateAt 29 71 1 := by decide +kernel
theorem cell_29_71_2 : CertificateAt 29 71 2 := by decide +kernel
theorem cell_29_71_3 : CertificateAt 29 71 3 := by decide +kernel
theorem cell_29_71_4 : CertificateAt 29 71 4 := by decide +kernel
theorem cell_29_71_5 : CertificateAt 29 71 5 := by decide +kernel
theorem row_29_71 : ThresholdAt 29 71 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 71 0 cell_29_71_0
    | exact certificate_sound 29 71 1 cell_29_71_1
    | exact certificate_sound 29 71 2 cell_29_71_2
    | exact certificate_sound 29 71 3 cell_29_71_3
    | exact certificate_sound 29 71 4 cell_29_71_4
    | exact certificate_sound 29 71 5 cell_29_71_5
theorem cell_29_72_0 : CertificateAt 29 72 0 := by decide +kernel
theorem cell_29_72_1 : CertificateAt 29 72 1 := by decide +kernel
theorem cell_29_72_2 : CertificateAt 29 72 2 := by decide +kernel
theorem cell_29_72_3 : CertificateAt 29 72 3 := by decide +kernel
theorem cell_29_72_4 : CertificateAt 29 72 4 := by decide +kernel
theorem cell_29_72_5 : CertificateAt 29 72 5 := by decide +kernel
theorem row_29_72 : ThresholdAt 29 72 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 72 0 cell_29_72_0
    | exact certificate_sound 29 72 1 cell_29_72_1
    | exact certificate_sound 29 72 2 cell_29_72_2
    | exact certificate_sound 29 72 3 cell_29_72_3
    | exact certificate_sound 29 72 4 cell_29_72_4
    | exact certificate_sound 29 72 5 cell_29_72_5
theorem cell_29_73_0 : CertificateAt 29 73 0 := by decide +kernel
theorem cell_29_73_1 : CertificateAt 29 73 1 := by decide +kernel
theorem cell_29_73_2 : CertificateAt 29 73 2 := by decide +kernel
theorem cell_29_73_3 : CertificateAt 29 73 3 := by decide +kernel
theorem cell_29_73_4 : CertificateAt 29 73 4 := by decide +kernel
theorem cell_29_73_5 : CertificateAt 29 73 5 := by decide +kernel
theorem row_29_73 : ThresholdAt 29 73 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 73 0 cell_29_73_0
    | exact certificate_sound 29 73 1 cell_29_73_1
    | exact certificate_sound 29 73 2 cell_29_73_2
    | exact certificate_sound 29 73 3 cell_29_73_3
    | exact certificate_sound 29 73 4 cell_29_73_4
    | exact certificate_sound 29 73 5 cell_29_73_5
theorem cell_29_74_0 : CertificateAt 29 74 0 := by decide +kernel
theorem cell_29_74_1 : CertificateAt 29 74 1 := by decide +kernel
theorem cell_29_74_2 : CertificateAt 29 74 2 := by decide +kernel
theorem cell_29_74_3 : CertificateAt 29 74 3 := by decide +kernel
theorem cell_29_74_4 : CertificateAt 29 74 4 := by decide +kernel
theorem cell_29_74_5 : CertificateAt 29 74 5 := by decide +kernel
theorem row_29_74 : ThresholdAt 29 74 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 74 0 cell_29_74_0
    | exact certificate_sound 29 74 1 cell_29_74_1
    | exact certificate_sound 29 74 2 cell_29_74_2
    | exact certificate_sound 29 74 3 cell_29_74_3
    | exact certificate_sound 29 74 4 cell_29_74_4
    | exact certificate_sound 29 74 5 cell_29_74_5
theorem cell_29_75_0 : CertificateAt 29 75 0 := by decide +kernel
theorem cell_29_75_1 : CertificateAt 29 75 1 := by decide +kernel
theorem cell_29_75_2 : CertificateAt 29 75 2 := by decide +kernel
theorem cell_29_75_3 : CertificateAt 29 75 3 := by decide +kernel
theorem cell_29_75_4 : CertificateAt 29 75 4 := by decide +kernel
theorem cell_29_75_5 : CertificateAt 29 75 5 := by decide +kernel
theorem row_29_75 : ThresholdAt 29 75 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 75 0 cell_29_75_0
    | exact certificate_sound 29 75 1 cell_29_75_1
    | exact certificate_sound 29 75 2 cell_29_75_2
    | exact certificate_sound 29 75 3 cell_29_75_3
    | exact certificate_sound 29 75 4 cell_29_75_4
    | exact certificate_sound 29 75 5 cell_29_75_5
theorem cell_29_76_0 : CertificateAt 29 76 0 := by decide +kernel
theorem cell_29_76_1 : CertificateAt 29 76 1 := by decide +kernel
theorem cell_29_76_2 : CertificateAt 29 76 2 := by decide +kernel
theorem cell_29_76_3 : CertificateAt 29 76 3 := by decide +kernel
theorem cell_29_76_4 : CertificateAt 29 76 4 := by decide +kernel
theorem cell_29_76_5 : CertificateAt 29 76 5 := by decide +kernel
theorem row_29_76 : ThresholdAt 29 76 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 76 0 cell_29_76_0
    | exact certificate_sound 29 76 1 cell_29_76_1
    | exact certificate_sound 29 76 2 cell_29_76_2
    | exact certificate_sound 29 76 3 cell_29_76_3
    | exact certificate_sound 29 76 4 cell_29_76_4
    | exact certificate_sound 29 76 5 cell_29_76_5
theorem cell_29_77_0 : CertificateAt 29 77 0 := by decide +kernel
theorem cell_29_77_1 : CertificateAt 29 77 1 := by decide +kernel
theorem cell_29_77_2 : CertificateAt 29 77 2 := by decide +kernel
theorem cell_29_77_3 : CertificateAt 29 77 3 := by decide +kernel
theorem cell_29_77_4 : CertificateAt 29 77 4 := by decide +kernel
theorem cell_29_77_5 : CertificateAt 29 77 5 := by decide +kernel
theorem row_29_77 : ThresholdAt 29 77 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 77 0 cell_29_77_0
    | exact certificate_sound 29 77 1 cell_29_77_1
    | exact certificate_sound 29 77 2 cell_29_77_2
    | exact certificate_sound 29 77 3 cell_29_77_3
    | exact certificate_sound 29 77 4 cell_29_77_4
    | exact certificate_sound 29 77 5 cell_29_77_5
theorem cell_29_78_0 : CertificateAt 29 78 0 := by decide +kernel
theorem cell_29_78_1 : CertificateAt 29 78 1 := by decide +kernel
theorem cell_29_78_2 : CertificateAt 29 78 2 := by decide +kernel
theorem cell_29_78_3 : CertificateAt 29 78 3 := by decide +kernel
theorem cell_29_78_4 : CertificateAt 29 78 4 := by decide +kernel
theorem cell_29_78_5 : CertificateAt 29 78 5 := by decide +kernel
theorem row_29_78 : ThresholdAt 29 78 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 78 0 cell_29_78_0
    | exact certificate_sound 29 78 1 cell_29_78_1
    | exact certificate_sound 29 78 2 cell_29_78_2
    | exact certificate_sound 29 78 3 cell_29_78_3
    | exact certificate_sound 29 78 4 cell_29_78_4
    | exact certificate_sound 29 78 5 cell_29_78_5
theorem cell_29_79_0 : CertificateAt 29 79 0 := by decide +kernel
theorem cell_29_79_1 : CertificateAt 29 79 1 := by decide +kernel
theorem cell_29_79_2 : CertificateAt 29 79 2 := by decide +kernel
theorem cell_29_79_3 : CertificateAt 29 79 3 := by decide +kernel
theorem cell_29_79_4 : CertificateAt 29 79 4 := by decide +kernel
theorem cell_29_79_5 : CertificateAt 29 79 5 := by decide +kernel
theorem row_29_79 : ThresholdAt 29 79 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 79 0 cell_29_79_0
    | exact certificate_sound 29 79 1 cell_29_79_1
    | exact certificate_sound 29 79 2 cell_29_79_2
    | exact certificate_sound 29 79 3 cell_29_79_3
    | exact certificate_sound 29 79 4 cell_29_79_4
    | exact certificate_sound 29 79 5 cell_29_79_5
theorem cell_29_80_0 : CertificateAt 29 80 0 := by decide +kernel
theorem cell_29_80_1 : CertificateAt 29 80 1 := by decide +kernel
theorem cell_29_80_2 : CertificateAt 29 80 2 := by decide +kernel
theorem cell_29_80_3 : CertificateAt 29 80 3 := by decide +kernel
theorem cell_29_80_4 : CertificateAt 29 80 4 := by decide +kernel
theorem cell_29_80_5 : CertificateAt 29 80 5 := by decide +kernel
theorem row_29_80 : ThresholdAt 29 80 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 80 0 cell_29_80_0
    | exact certificate_sound 29 80 1 cell_29_80_1
    | exact certificate_sound 29 80 2 cell_29_80_2
    | exact certificate_sound 29 80 3 cell_29_80_3
    | exact certificate_sound 29 80 4 cell_29_80_4
    | exact certificate_sound 29 80 5 cell_29_80_5
theorem cell_29_81_0 : CertificateAt 29 81 0 := by decide +kernel
theorem cell_29_81_1 : CertificateAt 29 81 1 := by decide +kernel
theorem cell_29_81_2 : CertificateAt 29 81 2 := by decide +kernel
theorem cell_29_81_3 : CertificateAt 29 81 3 := by decide +kernel
theorem cell_29_81_4 : CertificateAt 29 81 4 := by decide +kernel
theorem cell_29_81_5 : CertificateAt 29 81 5 := by decide +kernel
theorem row_29_81 : ThresholdAt 29 81 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 81 0 cell_29_81_0
    | exact certificate_sound 29 81 1 cell_29_81_1
    | exact certificate_sound 29 81 2 cell_29_81_2
    | exact certificate_sound 29 81 3 cell_29_81_3
    | exact certificate_sound 29 81 4 cell_29_81_4
    | exact certificate_sound 29 81 5 cell_29_81_5
theorem cell_29_82_0 : CertificateAt 29 82 0 := by decide +kernel
theorem cell_29_82_1 : CertificateAt 29 82 1 := by decide +kernel
theorem cell_29_82_2 : CertificateAt 29 82 2 := by decide +kernel
theorem cell_29_82_3 : CertificateAt 29 82 3 := by decide +kernel
theorem cell_29_82_4 : CertificateAt 29 82 4 := by decide +kernel
theorem cell_29_82_5 : CertificateAt 29 82 5 := by decide +kernel
theorem row_29_82 : ThresholdAt 29 82 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 82 0 cell_29_82_0
    | exact certificate_sound 29 82 1 cell_29_82_1
    | exact certificate_sound 29 82 2 cell_29_82_2
    | exact certificate_sound 29 82 3 cell_29_82_3
    | exact certificate_sound 29 82 4 cell_29_82_4
    | exact certificate_sound 29 82 5 cell_29_82_5
theorem cell_29_83_0 : CertificateAt 29 83 0 := by decide +kernel
theorem cell_29_83_1 : CertificateAt 29 83 1 := by decide +kernel
theorem cell_29_83_2 : CertificateAt 29 83 2 := by decide +kernel
theorem cell_29_83_3 : CertificateAt 29 83 3 := by decide +kernel
theorem cell_29_83_4 : CertificateAt 29 83 4 := by decide +kernel
theorem cell_29_83_5 : CertificateAt 29 83 5 := by decide +kernel
theorem row_29_83 : ThresholdAt 29 83 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 83 0 cell_29_83_0
    | exact certificate_sound 29 83 1 cell_29_83_1
    | exact certificate_sound 29 83 2 cell_29_83_2
    | exact certificate_sound 29 83 3 cell_29_83_3
    | exact certificate_sound 29 83 4 cell_29_83_4
    | exact certificate_sound 29 83 5 cell_29_83_5
theorem cell_29_84_0 : CertificateAt 29 84 0 := by decide +kernel
theorem cell_29_84_1 : CertificateAt 29 84 1 := by decide +kernel
theorem cell_29_84_2 : CertificateAt 29 84 2 := by decide +kernel
theorem cell_29_84_3 : CertificateAt 29 84 3 := by decide +kernel
theorem cell_29_84_4 : CertificateAt 29 84 4 := by decide +kernel
theorem cell_29_84_5 : CertificateAt 29 84 5 := by decide +kernel
theorem row_29_84 : ThresholdAt 29 84 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 84 0 cell_29_84_0
    | exact certificate_sound 29 84 1 cell_29_84_1
    | exact certificate_sound 29 84 2 cell_29_84_2
    | exact certificate_sound 29 84 3 cell_29_84_3
    | exact certificate_sound 29 84 4 cell_29_84_4
    | exact certificate_sound 29 84 5 cell_29_84_5
theorem cell_29_85_0 : CertificateAt 29 85 0 := by decide +kernel
theorem cell_29_85_1 : CertificateAt 29 85 1 := by decide +kernel
theorem cell_29_85_2 : CertificateAt 29 85 2 := by decide +kernel
theorem cell_29_85_3 : CertificateAt 29 85 3 := by decide +kernel
theorem cell_29_85_4 : CertificateAt 29 85 4 := by decide +kernel
theorem cell_29_85_5 : CertificateAt 29 85 5 := by decide +kernel
theorem row_29_85 : ThresholdAt 29 85 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 85 0 cell_29_85_0
    | exact certificate_sound 29 85 1 cell_29_85_1
    | exact certificate_sound 29 85 2 cell_29_85_2
    | exact certificate_sound 29 85 3 cell_29_85_3
    | exact certificate_sound 29 85 4 cell_29_85_4
    | exact certificate_sound 29 85 5 cell_29_85_5
theorem cell_29_86_0 : CertificateAt 29 86 0 := by decide +kernel
theorem cell_29_86_1 : CertificateAt 29 86 1 := by decide +kernel
theorem cell_29_86_2 : CertificateAt 29 86 2 := by decide +kernel
theorem cell_29_86_3 : CertificateAt 29 86 3 := by decide +kernel
theorem cell_29_86_4 : CertificateAt 29 86 4 := by decide +kernel
theorem cell_29_86_5 : CertificateAt 29 86 5 := by decide +kernel
theorem row_29_86 : ThresholdAt 29 86 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 86 0 cell_29_86_0
    | exact certificate_sound 29 86 1 cell_29_86_1
    | exact certificate_sound 29 86 2 cell_29_86_2
    | exact certificate_sound 29 86 3 cell_29_86_3
    | exact certificate_sound 29 86 4 cell_29_86_4
    | exact certificate_sound 29 86 5 cell_29_86_5
theorem cell_29_87_0 : CertificateAt 29 87 0 := by decide +kernel
theorem cell_29_87_1 : CertificateAt 29 87 1 := by decide +kernel
theorem cell_29_87_2 : CertificateAt 29 87 2 := by decide +kernel
theorem cell_29_87_3 : CertificateAt 29 87 3 := by decide +kernel
theorem cell_29_87_4 : CertificateAt 29 87 4 := by decide +kernel
theorem cell_29_87_5 : CertificateAt 29 87 5 := by decide +kernel
theorem row_29_87 : ThresholdAt 29 87 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 87 0 cell_29_87_0
    | exact certificate_sound 29 87 1 cell_29_87_1
    | exact certificate_sound 29 87 2 cell_29_87_2
    | exact certificate_sound 29 87 3 cell_29_87_3
    | exact certificate_sound 29 87 4 cell_29_87_4
    | exact certificate_sound 29 87 5 cell_29_87_5
theorem cell_29_88_0 : CertificateAt 29 88 0 := by decide +kernel
theorem cell_29_88_1 : CertificateAt 29 88 1 := by decide +kernel
theorem cell_29_88_2 : CertificateAt 29 88 2 := by decide +kernel
theorem cell_29_88_3 : CertificateAt 29 88 3 := by decide +kernel
theorem cell_29_88_4 : CertificateAt 29 88 4 := by decide +kernel
theorem cell_29_88_5 : CertificateAt 29 88 5 := by decide +kernel
theorem row_29_88 : ThresholdAt 29 88 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 88 0 cell_29_88_0
    | exact certificate_sound 29 88 1 cell_29_88_1
    | exact certificate_sound 29 88 2 cell_29_88_2
    | exact certificate_sound 29 88 3 cell_29_88_3
    | exact certificate_sound 29 88 4 cell_29_88_4
    | exact certificate_sound 29 88 5 cell_29_88_5
theorem cell_29_89_0 : CertificateAt 29 89 0 := by decide +kernel
theorem cell_29_89_1 : CertificateAt 29 89 1 := by decide +kernel
theorem cell_29_89_2 : CertificateAt 29 89 2 := by decide +kernel
theorem cell_29_89_3 : CertificateAt 29 89 3 := by decide +kernel
theorem cell_29_89_4 : CertificateAt 29 89 4 := by decide +kernel
theorem cell_29_89_5 : CertificateAt 29 89 5 := by decide +kernel
theorem row_29_89 : ThresholdAt 29 89 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 89 0 cell_29_89_0
    | exact certificate_sound 29 89 1 cell_29_89_1
    | exact certificate_sound 29 89 2 cell_29_89_2
    | exact certificate_sound 29 89 3 cell_29_89_3
    | exact certificate_sound 29 89 4 cell_29_89_4
    | exact certificate_sound 29 89 5 cell_29_89_5
theorem cell_29_90_0 : CertificateAt 29 90 0 := by decide +kernel
theorem cell_29_90_1 : CertificateAt 29 90 1 := by decide +kernel
theorem cell_29_90_2 : CertificateAt 29 90 2 := by decide +kernel
theorem cell_29_90_3 : CertificateAt 29 90 3 := by decide +kernel
theorem cell_29_90_4 : CertificateAt 29 90 4 := by decide +kernel
theorem cell_29_90_5 : CertificateAt 29 90 5 := by decide +kernel
theorem row_29_90 : ThresholdAt 29 90 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 90 0 cell_29_90_0
    | exact certificate_sound 29 90 1 cell_29_90_1
    | exact certificate_sound 29 90 2 cell_29_90_2
    | exact certificate_sound 29 90 3 cell_29_90_3
    | exact certificate_sound 29 90 4 cell_29_90_4
    | exact certificate_sound 29 90 5 cell_29_90_5
theorem cell_29_91_0 : CertificateAt 29 91 0 := by decide +kernel
theorem cell_29_91_1 : CertificateAt 29 91 1 := by decide +kernel
theorem cell_29_91_2 : CertificateAt 29 91 2 := by decide +kernel
theorem cell_29_91_3 : CertificateAt 29 91 3 := by decide +kernel
theorem cell_29_91_4 : CertificateAt 29 91 4 := by decide +kernel
theorem cell_29_91_5 : CertificateAt 29 91 5 := by decide +kernel
theorem row_29_91 : ThresholdAt 29 91 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 91 0 cell_29_91_0
    | exact certificate_sound 29 91 1 cell_29_91_1
    | exact certificate_sound 29 91 2 cell_29_91_2
    | exact certificate_sound 29 91 3 cell_29_91_3
    | exact certificate_sound 29 91 4 cell_29_91_4
    | exact certificate_sound 29 91 5 cell_29_91_5
theorem cell_29_92_0 : CertificateAt 29 92 0 := by decide +kernel
theorem cell_29_92_1 : CertificateAt 29 92 1 := by decide +kernel
theorem cell_29_92_2 : CertificateAt 29 92 2 := by decide +kernel
theorem cell_29_92_3 : CertificateAt 29 92 3 := by decide +kernel
theorem cell_29_92_4 : CertificateAt 29 92 4 := by decide +kernel
theorem cell_29_92_5 : CertificateAt 29 92 5 := by decide +kernel
theorem row_29_92 : ThresholdAt 29 92 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 92 0 cell_29_92_0
    | exact certificate_sound 29 92 1 cell_29_92_1
    | exact certificate_sound 29 92 2 cell_29_92_2
    | exact certificate_sound 29 92 3 cell_29_92_3
    | exact certificate_sound 29 92 4 cell_29_92_4
    | exact certificate_sound 29 92 5 cell_29_92_5
theorem cell_29_93_0 : CertificateAt 29 93 0 := by decide +kernel
theorem cell_29_93_1 : CertificateAt 29 93 1 := by decide +kernel
theorem cell_29_93_2 : CertificateAt 29 93 2 := by decide +kernel
theorem cell_29_93_3 : CertificateAt 29 93 3 := by decide +kernel
theorem cell_29_93_4 : CertificateAt 29 93 4 := by decide +kernel
theorem cell_29_93_5 : CertificateAt 29 93 5 := by decide +kernel
theorem row_29_93 : ThresholdAt 29 93 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 93 0 cell_29_93_0
    | exact certificate_sound 29 93 1 cell_29_93_1
    | exact certificate_sound 29 93 2 cell_29_93_2
    | exact certificate_sound 29 93 3 cell_29_93_3
    | exact certificate_sound 29 93 4 cell_29_93_4
    | exact certificate_sound 29 93 5 cell_29_93_5
theorem cell_29_94_0 : CertificateAt 29 94 0 := by decide +kernel
theorem cell_29_94_1 : CertificateAt 29 94 1 := by decide +kernel
theorem cell_29_94_2 : CertificateAt 29 94 2 := by decide +kernel
theorem cell_29_94_3 : CertificateAt 29 94 3 := by decide +kernel
theorem cell_29_94_4 : CertificateAt 29 94 4 := by decide +kernel
theorem cell_29_94_5 : CertificateAt 29 94 5 := by decide +kernel
theorem row_29_94 : ThresholdAt 29 94 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 94 0 cell_29_94_0
    | exact certificate_sound 29 94 1 cell_29_94_1
    | exact certificate_sound 29 94 2 cell_29_94_2
    | exact certificate_sound 29 94 3 cell_29_94_3
    | exact certificate_sound 29 94 4 cell_29_94_4
    | exact certificate_sound 29 94 5 cell_29_94_5
theorem cell_29_95_0 : CertificateAt 29 95 0 := by decide +kernel
theorem cell_29_95_1 : CertificateAt 29 95 1 := by decide +kernel
theorem cell_29_95_2 : CertificateAt 29 95 2 := by decide +kernel
theorem cell_29_95_3 : CertificateAt 29 95 3 := by decide +kernel
theorem cell_29_95_4 : CertificateAt 29 95 4 := by decide +kernel
theorem cell_29_95_5 : CertificateAt 29 95 5 := by decide +kernel
theorem row_29_95 : ThresholdAt 29 95 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 95 0 cell_29_95_0
    | exact certificate_sound 29 95 1 cell_29_95_1
    | exact certificate_sound 29 95 2 cell_29_95_2
    | exact certificate_sound 29 95 3 cell_29_95_3
    | exact certificate_sound 29 95 4 cell_29_95_4
    | exact certificate_sound 29 95 5 cell_29_95_5
theorem cell_29_96_0 : CertificateAt 29 96 0 := by decide +kernel
theorem cell_29_96_1 : CertificateAt 29 96 1 := by decide +kernel
theorem cell_29_96_2 : CertificateAt 29 96 2 := by decide +kernel
theorem cell_29_96_3 : CertificateAt 29 96 3 := by decide +kernel
theorem cell_29_96_4 : CertificateAt 29 96 4 := by decide +kernel
theorem cell_29_96_5 : CertificateAt 29 96 5 := by decide +kernel
theorem row_29_96 : ThresholdAt 29 96 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 96 0 cell_29_96_0
    | exact certificate_sound 29 96 1 cell_29_96_1
    | exact certificate_sound 29 96 2 cell_29_96_2
    | exact certificate_sound 29 96 3 cell_29_96_3
    | exact certificate_sound 29 96 4 cell_29_96_4
    | exact certificate_sound 29 96 5 cell_29_96_5
theorem cell_29_97_0 : CertificateAt 29 97 0 := by decide +kernel
theorem cell_29_97_1 : CertificateAt 29 97 1 := by decide +kernel
theorem cell_29_97_2 : CertificateAt 29 97 2 := by decide +kernel
theorem cell_29_97_3 : CertificateAt 29 97 3 := by decide +kernel
theorem cell_29_97_4 : CertificateAt 29 97 4 := by decide +kernel
theorem cell_29_97_5 : CertificateAt 29 97 5 := by decide +kernel
theorem row_29_97 : ThresholdAt 29 97 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 97 0 cell_29_97_0
    | exact certificate_sound 29 97 1 cell_29_97_1
    | exact certificate_sound 29 97 2 cell_29_97_2
    | exact certificate_sound 29 97 3 cell_29_97_3
    | exact certificate_sound 29 97 4 cell_29_97_4
    | exact certificate_sound 29 97 5 cell_29_97_5
theorem cell_29_98_0 : CertificateAt 29 98 0 := by decide +kernel
theorem cell_29_98_1 : CertificateAt 29 98 1 := by decide +kernel
theorem cell_29_98_2 : CertificateAt 29 98 2 := by decide +kernel
theorem cell_29_98_3 : CertificateAt 29 98 3 := by decide +kernel
theorem cell_29_98_4 : CertificateAt 29 98 4 := by decide +kernel
theorem cell_29_98_5 : CertificateAt 29 98 5 := by decide +kernel
theorem row_29_98 : ThresholdAt 29 98 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 98 0 cell_29_98_0
    | exact certificate_sound 29 98 1 cell_29_98_1
    | exact certificate_sound 29 98 2 cell_29_98_2
    | exact certificate_sound 29 98 3 cell_29_98_3
    | exact certificate_sound 29 98 4 cell_29_98_4
    | exact certificate_sound 29 98 5 cell_29_98_5
theorem cell_29_99_0 : CertificateAt 29 99 0 := by decide +kernel
theorem cell_29_99_1 : CertificateAt 29 99 1 := by decide +kernel
theorem cell_29_99_2 : CertificateAt 29 99 2 := by decide +kernel
theorem cell_29_99_3 : CertificateAt 29 99 3 := by decide +kernel
theorem cell_29_99_4 : CertificateAt 29 99 4 := by decide +kernel
theorem cell_29_99_5 : CertificateAt 29 99 5 := by decide +kernel
theorem row_29_99 : ThresholdAt 29 99 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 99 0 cell_29_99_0
    | exact certificate_sound 29 99 1 cell_29_99_1
    | exact certificate_sound 29 99 2 cell_29_99_2
    | exact certificate_sound 29 99 3 cell_29_99_3
    | exact certificate_sound 29 99 4 cell_29_99_4
    | exact certificate_sound 29 99 5 cell_29_99_5
theorem cell_29_100_0 : CertificateAt 29 100 0 := by decide +kernel
theorem cell_29_100_1 : CertificateAt 29 100 1 := by decide +kernel
theorem cell_29_100_2 : CertificateAt 29 100 2 := by decide +kernel
theorem cell_29_100_3 : CertificateAt 29 100 3 := by decide +kernel
theorem cell_29_100_4 : CertificateAt 29 100 4 := by decide +kernel
theorem cell_29_100_5 : CertificateAt 29 100 5 := by decide +kernel
theorem row_29_100 : ThresholdAt 29 100 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 100 0 cell_29_100_0
    | exact certificate_sound 29 100 1 cell_29_100_1
    | exact certificate_sound 29 100 2 cell_29_100_2
    | exact certificate_sound 29 100 3 cell_29_100_3
    | exact certificate_sound 29 100 4 cell_29_100_4
    | exact certificate_sound 29 100 5 cell_29_100_5
theorem cell_29_101_0 : CertificateAt 29 101 0 := by decide +kernel
theorem cell_29_101_1 : CertificateAt 29 101 1 := by decide +kernel
theorem cell_29_101_2 : CertificateAt 29 101 2 := by decide +kernel
theorem cell_29_101_3 : CertificateAt 29 101 3 := by decide +kernel
theorem cell_29_101_4 : CertificateAt 29 101 4 := by decide +kernel
theorem cell_29_101_5 : CertificateAt 29 101 5 := by decide +kernel
theorem row_29_101 : ThresholdAt 29 101 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 101 0 cell_29_101_0
    | exact certificate_sound 29 101 1 cell_29_101_1
    | exact certificate_sound 29 101 2 cell_29_101_2
    | exact certificate_sound 29 101 3 cell_29_101_3
    | exact certificate_sound 29 101 4 cell_29_101_4
    | exact certificate_sound 29 101 5 cell_29_101_5
theorem cell_29_102_0 : CertificateAt 29 102 0 := by decide +kernel
theorem cell_29_102_1 : CertificateAt 29 102 1 := by decide +kernel
theorem cell_29_102_2 : CertificateAt 29 102 2 := by decide +kernel
theorem cell_29_102_3 : CertificateAt 29 102 3 := by decide +kernel
theorem cell_29_102_4 : CertificateAt 29 102 4 := by decide +kernel
theorem cell_29_102_5 : CertificateAt 29 102 5 := by decide +kernel
theorem row_29_102 : ThresholdAt 29 102 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 102 0 cell_29_102_0
    | exact certificate_sound 29 102 1 cell_29_102_1
    | exact certificate_sound 29 102 2 cell_29_102_2
    | exact certificate_sound 29 102 3 cell_29_102_3
    | exact certificate_sound 29 102 4 cell_29_102_4
    | exact certificate_sound 29 102 5 cell_29_102_5
theorem cell_29_103_0 : CertificateAt 29 103 0 := by decide +kernel
theorem cell_29_103_1 : CertificateAt 29 103 1 := by decide +kernel
theorem cell_29_103_2 : CertificateAt 29 103 2 := by decide +kernel
theorem cell_29_103_3 : CertificateAt 29 103 3 := by decide +kernel
theorem cell_29_103_4 : CertificateAt 29 103 4 := by decide +kernel
theorem cell_29_103_5 : CertificateAt 29 103 5 := by decide +kernel
theorem row_29_103 : ThresholdAt 29 103 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 103 0 cell_29_103_0
    | exact certificate_sound 29 103 1 cell_29_103_1
    | exact certificate_sound 29 103 2 cell_29_103_2
    | exact certificate_sound 29 103 3 cell_29_103_3
    | exact certificate_sound 29 103 4 cell_29_103_4
    | exact certificate_sound 29 103 5 cell_29_103_5
theorem cell_29_104_0 : CertificateAt 29 104 0 := by decide +kernel
theorem cell_29_104_1 : CertificateAt 29 104 1 := by decide +kernel
theorem cell_29_104_2 : CertificateAt 29 104 2 := by decide +kernel
theorem cell_29_104_3 : CertificateAt 29 104 3 := by decide +kernel
theorem cell_29_104_4 : CertificateAt 29 104 4 := by decide +kernel
theorem cell_29_104_5 : CertificateAt 29 104 5 := by decide +kernel
theorem row_29_104 : ThresholdAt 29 104 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 104 0 cell_29_104_0
    | exact certificate_sound 29 104 1 cell_29_104_1
    | exact certificate_sound 29 104 2 cell_29_104_2
    | exact certificate_sound 29 104 3 cell_29_104_3
    | exact certificate_sound 29 104 4 cell_29_104_4
    | exact certificate_sound 29 104 5 cell_29_104_5
theorem cell_29_105_0 : CertificateAt 29 105 0 := by decide +kernel
theorem cell_29_105_1 : CertificateAt 29 105 1 := by decide +kernel
theorem cell_29_105_2 : CertificateAt 29 105 2 := by decide +kernel
theorem cell_29_105_3 : CertificateAt 29 105 3 := by decide +kernel
theorem cell_29_105_4 : CertificateAt 29 105 4 := by decide +kernel
theorem cell_29_105_5 : CertificateAt 29 105 5 := by decide +kernel
theorem row_29_105 : ThresholdAt 29 105 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 105 0 cell_29_105_0
    | exact certificate_sound 29 105 1 cell_29_105_1
    | exact certificate_sound 29 105 2 cell_29_105_2
    | exact certificate_sound 29 105 3 cell_29_105_3
    | exact certificate_sound 29 105 4 cell_29_105_4
    | exact certificate_sound 29 105 5 cell_29_105_5
theorem cell_29_106_0 : CertificateAt 29 106 0 := by decide +kernel
theorem cell_29_106_1 : CertificateAt 29 106 1 := by decide +kernel
theorem cell_29_106_2 : CertificateAt 29 106 2 := by decide +kernel
theorem cell_29_106_3 : CertificateAt 29 106 3 := by decide +kernel
theorem cell_29_106_4 : CertificateAt 29 106 4 := by decide +kernel
theorem cell_29_106_5 : CertificateAt 29 106 5 := by decide +kernel
theorem row_29_106 : ThresholdAt 29 106 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 106 0 cell_29_106_0
    | exact certificate_sound 29 106 1 cell_29_106_1
    | exact certificate_sound 29 106 2 cell_29_106_2
    | exact certificate_sound 29 106 3 cell_29_106_3
    | exact certificate_sound 29 106 4 cell_29_106_4
    | exact certificate_sound 29 106 5 cell_29_106_5
theorem cell_29_107_0 : CertificateAt 29 107 0 := by decide +kernel
theorem cell_29_107_1 : CertificateAt 29 107 1 := by decide +kernel
theorem cell_29_107_2 : CertificateAt 29 107 2 := by decide +kernel
theorem cell_29_107_3 : CertificateAt 29 107 3 := by decide +kernel
theorem cell_29_107_4 : CertificateAt 29 107 4 := by decide +kernel
theorem cell_29_107_5 : CertificateAt 29 107 5 := by decide +kernel
theorem row_29_107 : ThresholdAt 29 107 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 107 0 cell_29_107_0
    | exact certificate_sound 29 107 1 cell_29_107_1
    | exact certificate_sound 29 107 2 cell_29_107_2
    | exact certificate_sound 29 107 3 cell_29_107_3
    | exact certificate_sound 29 107 4 cell_29_107_4
    | exact certificate_sound 29 107 5 cell_29_107_5
theorem cell_29_108_0 : CertificateAt 29 108 0 := by decide +kernel
theorem cell_29_108_1 : CertificateAt 29 108 1 := by decide +kernel
theorem cell_29_108_2 : CertificateAt 29 108 2 := by decide +kernel
theorem cell_29_108_3 : CertificateAt 29 108 3 := by decide +kernel
theorem cell_29_108_4 : CertificateAt 29 108 4 := by decide +kernel
theorem cell_29_108_5 : CertificateAt 29 108 5 := by decide +kernel
theorem row_29_108 : ThresholdAt 29 108 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 108 0 cell_29_108_0
    | exact certificate_sound 29 108 1 cell_29_108_1
    | exact certificate_sound 29 108 2 cell_29_108_2
    | exact certificate_sound 29 108 3 cell_29_108_3
    | exact certificate_sound 29 108 4 cell_29_108_4
    | exact certificate_sound 29 108 5 cell_29_108_5
theorem cell_29_109_0 : CertificateAt 29 109 0 := by decide +kernel
theorem cell_29_109_1 : CertificateAt 29 109 1 := by decide +kernel
theorem cell_29_109_2 : CertificateAt 29 109 2 := by decide +kernel
theorem cell_29_109_3 : CertificateAt 29 109 3 := by decide +kernel
theorem cell_29_109_4 : CertificateAt 29 109 4 := by decide +kernel
theorem cell_29_109_5 : CertificateAt 29 109 5 := by decide +kernel
theorem row_29_109 : ThresholdAt 29 109 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 109 0 cell_29_109_0
    | exact certificate_sound 29 109 1 cell_29_109_1
    | exact certificate_sound 29 109 2 cell_29_109_2
    | exact certificate_sound 29 109 3 cell_29_109_3
    | exact certificate_sound 29 109 4 cell_29_109_4
    | exact certificate_sound 29 109 5 cell_29_109_5
theorem cell_29_110_0 : CertificateAt 29 110 0 := by decide +kernel
theorem cell_29_110_1 : CertificateAt 29 110 1 := by decide +kernel
theorem cell_29_110_2 : CertificateAt 29 110 2 := by decide +kernel
theorem cell_29_110_3 : CertificateAt 29 110 3 := by decide +kernel
theorem cell_29_110_4 : CertificateAt 29 110 4 := by decide +kernel
theorem cell_29_110_5 : CertificateAt 29 110 5 := by decide +kernel
theorem row_29_110 : ThresholdAt 29 110 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 29 110 0 cell_29_110_0
    | exact certificate_sound 29 110 1 cell_29_110_1
    | exact certificate_sound 29 110 2 cell_29_110_2
    | exact certificate_sound 29 110 3 cell_29_110_3
    | exact certificate_sound 29 110 4 cell_29_110_4
    | exact certificate_sound 29 110 5 cell_29_110_5
theorem checkedR29 : ∀ V ∈ List.range 111, ThresholdAt 29 V := by
  intro V hV
  have hv : V < 111 := List.mem_range.mp hV
  by_cases h0_111 : V < 55
  · by_cases h0_55 : V < 27
    · by_cases h0_27 : V < 13
      · by_cases h0_13 : V < 6
        · by_cases h0_6 : V < 3
          · by_cases h0_3 : V < 1
            · have he : V = 0 := by omega
              subst V
              exact row_29_0
            · by_cases h1_3 : V < 2
              · have he : V = 1 := by omega
                subst V
                exact row_29_1
              · have he : V = 2 := by omega
                subst V
                exact row_29_2
          · by_cases h3_6 : V < 4
            · have he : V = 3 := by omega
              subst V
              exact row_29_3
            · by_cases h4_6 : V < 5
              · have he : V = 4 := by omega
                subst V
                exact row_29_4
              · have he : V = 5 := by omega
                subst V
                exact row_29_5
        · by_cases h6_13 : V < 9
          · by_cases h6_9 : V < 7
            · have he : V = 6 := by omega
              subst V
              exact row_29_6
            · by_cases h7_9 : V < 8
              · have he : V = 7 := by omega
                subst V
                exact row_29_7
              · have he : V = 8 := by omega
                subst V
                exact row_29_8
          · by_cases h9_13 : V < 11
            · by_cases h9_11 : V < 10
              · have he : V = 9 := by omega
                subst V
                exact row_29_9
              · have he : V = 10 := by omega
                subst V
                exact row_29_10
            · by_cases h11_13 : V < 12
              · have he : V = 11 := by omega
                subst V
                exact row_29_11
              · have he : V = 12 := by omega
                subst V
                exact row_29_12
      · by_cases h13_27 : V < 20
        · by_cases h13_20 : V < 16
          · by_cases h13_16 : V < 14
            · have he : V = 13 := by omega
              subst V
              exact row_29_13
            · by_cases h14_16 : V < 15
              · have he : V = 14 := by omega
                subst V
                exact row_29_14
              · have he : V = 15 := by omega
                subst V
                exact row_29_15
          · by_cases h16_20 : V < 18
            · by_cases h16_18 : V < 17
              · have he : V = 16 := by omega
                subst V
                exact row_29_16
              · have he : V = 17 := by omega
                subst V
                exact row_29_17
            · by_cases h18_20 : V < 19
              · have he : V = 18 := by omega
                subst V
                exact row_29_18
              · have he : V = 19 := by omega
                subst V
                exact row_29_19
        · by_cases h20_27 : V < 23
          · by_cases h20_23 : V < 21
            · have he : V = 20 := by omega
              subst V
              exact row_29_20
            · by_cases h21_23 : V < 22
              · have he : V = 21 := by omega
                subst V
                exact row_29_21
              · have he : V = 22 := by omega
                subst V
                exact row_29_22
          · by_cases h23_27 : V < 25
            · by_cases h23_25 : V < 24
              · have he : V = 23 := by omega
                subst V
                exact row_29_23
              · have he : V = 24 := by omega
                subst V
                exact row_29_24
            · by_cases h25_27 : V < 26
              · have he : V = 25 := by omega
                subst V
                exact row_29_25
              · have he : V = 26 := by omega
                subst V
                exact row_29_26
    · by_cases h27_55 : V < 41
      · by_cases h27_41 : V < 34
        · by_cases h27_34 : V < 30
          · by_cases h27_30 : V < 28
            · have he : V = 27 := by omega
              subst V
              exact row_29_27
            · by_cases h28_30 : V < 29
              · have he : V = 28 := by omega
                subst V
                exact row_29_28
              · have he : V = 29 := by omega
                subst V
                exact row_29_29
          · by_cases h30_34 : V < 32
            · by_cases h30_32 : V < 31
              · have he : V = 30 := by omega
                subst V
                exact row_29_30
              · have he : V = 31 := by omega
                subst V
                exact row_29_31
            · by_cases h32_34 : V < 33
              · have he : V = 32 := by omega
                subst V
                exact row_29_32
              · have he : V = 33 := by omega
                subst V
                exact row_29_33
        · by_cases h34_41 : V < 37
          · by_cases h34_37 : V < 35
            · have he : V = 34 := by omega
              subst V
              exact row_29_34
            · by_cases h35_37 : V < 36
              · have he : V = 35 := by omega
                subst V
                exact row_29_35
              · have he : V = 36 := by omega
                subst V
                exact row_29_36
          · by_cases h37_41 : V < 39
            · by_cases h37_39 : V < 38
              · have he : V = 37 := by omega
                subst V
                exact row_29_37
              · have he : V = 38 := by omega
                subst V
                exact row_29_38
            · by_cases h39_41 : V < 40
              · have he : V = 39 := by omega
                subst V
                exact row_29_39
              · have he : V = 40 := by omega
                subst V
                exact row_29_40
      · by_cases h41_55 : V < 48
        · by_cases h41_48 : V < 44
          · by_cases h41_44 : V < 42
            · have he : V = 41 := by omega
              subst V
              exact row_29_41
            · by_cases h42_44 : V < 43
              · have he : V = 42 := by omega
                subst V
                exact row_29_42
              · have he : V = 43 := by omega
                subst V
                exact row_29_43
          · by_cases h44_48 : V < 46
            · by_cases h44_46 : V < 45
              · have he : V = 44 := by omega
                subst V
                exact row_29_44
              · have he : V = 45 := by omega
                subst V
                exact row_29_45
            · by_cases h46_48 : V < 47
              · have he : V = 46 := by omega
                subst V
                exact row_29_46
              · have he : V = 47 := by omega
                subst V
                exact row_29_47
        · by_cases h48_55 : V < 51
          · by_cases h48_51 : V < 49
            · have he : V = 48 := by omega
              subst V
              exact row_29_48
            · by_cases h49_51 : V < 50
              · have he : V = 49 := by omega
                subst V
                exact row_29_49
              · have he : V = 50 := by omega
                subst V
                exact row_29_50
          · by_cases h51_55 : V < 53
            · by_cases h51_53 : V < 52
              · have he : V = 51 := by omega
                subst V
                exact row_29_51
              · have he : V = 52 := by omega
                subst V
                exact row_29_52
            · by_cases h53_55 : V < 54
              · have he : V = 53 := by omega
                subst V
                exact row_29_53
              · have he : V = 54 := by omega
                subst V
                exact row_29_54
  · by_cases h55_111 : V < 83
    · by_cases h55_83 : V < 69
      · by_cases h55_69 : V < 62
        · by_cases h55_62 : V < 58
          · by_cases h55_58 : V < 56
            · have he : V = 55 := by omega
              subst V
              exact row_29_55
            · by_cases h56_58 : V < 57
              · have he : V = 56 := by omega
                subst V
                exact row_29_56
              · have he : V = 57 := by omega
                subst V
                exact row_29_57
          · by_cases h58_62 : V < 60
            · by_cases h58_60 : V < 59
              · have he : V = 58 := by omega
                subst V
                exact row_29_58
              · have he : V = 59 := by omega
                subst V
                exact row_29_59
            · by_cases h60_62 : V < 61
              · have he : V = 60 := by omega
                subst V
                exact row_29_60
              · have he : V = 61 := by omega
                subst V
                exact row_29_61
        · by_cases h62_69 : V < 65
          · by_cases h62_65 : V < 63
            · have he : V = 62 := by omega
              subst V
              exact row_29_62
            · by_cases h63_65 : V < 64
              · have he : V = 63 := by omega
                subst V
                exact row_29_63
              · have he : V = 64 := by omega
                subst V
                exact row_29_64
          · by_cases h65_69 : V < 67
            · by_cases h65_67 : V < 66
              · have he : V = 65 := by omega
                subst V
                exact row_29_65
              · have he : V = 66 := by omega
                subst V
                exact row_29_66
            · by_cases h67_69 : V < 68
              · have he : V = 67 := by omega
                subst V
                exact row_29_67
              · have he : V = 68 := by omega
                subst V
                exact row_29_68
      · by_cases h69_83 : V < 76
        · by_cases h69_76 : V < 72
          · by_cases h69_72 : V < 70
            · have he : V = 69 := by omega
              subst V
              exact row_29_69
            · by_cases h70_72 : V < 71
              · have he : V = 70 := by omega
                subst V
                exact row_29_70
              · have he : V = 71 := by omega
                subst V
                exact row_29_71
          · by_cases h72_76 : V < 74
            · by_cases h72_74 : V < 73
              · have he : V = 72 := by omega
                subst V
                exact row_29_72
              · have he : V = 73 := by omega
                subst V
                exact row_29_73
            · by_cases h74_76 : V < 75
              · have he : V = 74 := by omega
                subst V
                exact row_29_74
              · have he : V = 75 := by omega
                subst V
                exact row_29_75
        · by_cases h76_83 : V < 79
          · by_cases h76_79 : V < 77
            · have he : V = 76 := by omega
              subst V
              exact row_29_76
            · by_cases h77_79 : V < 78
              · have he : V = 77 := by omega
                subst V
                exact row_29_77
              · have he : V = 78 := by omega
                subst V
                exact row_29_78
          · by_cases h79_83 : V < 81
            · by_cases h79_81 : V < 80
              · have he : V = 79 := by omega
                subst V
                exact row_29_79
              · have he : V = 80 := by omega
                subst V
                exact row_29_80
            · by_cases h81_83 : V < 82
              · have he : V = 81 := by omega
                subst V
                exact row_29_81
              · have he : V = 82 := by omega
                subst V
                exact row_29_82
    · by_cases h83_111 : V < 97
      · by_cases h83_97 : V < 90
        · by_cases h83_90 : V < 86
          · by_cases h83_86 : V < 84
            · have he : V = 83 := by omega
              subst V
              exact row_29_83
            · by_cases h84_86 : V < 85
              · have he : V = 84 := by omega
                subst V
                exact row_29_84
              · have he : V = 85 := by omega
                subst V
                exact row_29_85
          · by_cases h86_90 : V < 88
            · by_cases h86_88 : V < 87
              · have he : V = 86 := by omega
                subst V
                exact row_29_86
              · have he : V = 87 := by omega
                subst V
                exact row_29_87
            · by_cases h88_90 : V < 89
              · have he : V = 88 := by omega
                subst V
                exact row_29_88
              · have he : V = 89 := by omega
                subst V
                exact row_29_89
        · by_cases h90_97 : V < 93
          · by_cases h90_93 : V < 91
            · have he : V = 90 := by omega
              subst V
              exact row_29_90
            · by_cases h91_93 : V < 92
              · have he : V = 91 := by omega
                subst V
                exact row_29_91
              · have he : V = 92 := by omega
                subst V
                exact row_29_92
          · by_cases h93_97 : V < 95
            · by_cases h93_95 : V < 94
              · have he : V = 93 := by omega
                subst V
                exact row_29_93
              · have he : V = 94 := by omega
                subst V
                exact row_29_94
            · by_cases h95_97 : V < 96
              · have he : V = 95 := by omega
                subst V
                exact row_29_95
              · have he : V = 96 := by omega
                subst V
                exact row_29_96
      · by_cases h97_111 : V < 104
        · by_cases h97_104 : V < 100
          · by_cases h97_100 : V < 98
            · have he : V = 97 := by omega
              subst V
              exact row_29_97
            · by_cases h98_100 : V < 99
              · have he : V = 98 := by omega
                subst V
                exact row_29_98
              · have he : V = 99 := by omega
                subst V
                exact row_29_99
          · by_cases h100_104 : V < 102
            · by_cases h100_102 : V < 101
              · have he : V = 100 := by omega
                subst V
                exact row_29_100
              · have he : V = 101 := by omega
                subst V
                exact row_29_101
            · by_cases h102_104 : V < 103
              · have he : V = 102 := by omega
                subst V
                exact row_29_102
              · have he : V = 103 := by omega
                subst V
                exact row_29_103
        · by_cases h104_111 : V < 107
          · by_cases h104_107 : V < 105
            · have he : V = 104 := by omega
              subst V
              exact row_29_104
            · by_cases h105_107 : V < 106
              · have he : V = 105 := by omega
                subst V
                exact row_29_105
              · have he : V = 106 := by omega
                subst V
                exact row_29_106
          · by_cases h107_111 : V < 109
            · by_cases h107_109 : V < 108
              · have he : V = 107 := by omega
                subst V
                exact row_29_107
              · have he : V = 108 := by omega
                subst V
                exact row_29_108
            · by_cases h109_111 : V < 110
              · have he : V = 109 := by omega
                subst V
                exact row_29_109
              · have he : V = 110 := by omega
                subst V
                exact row_29_110
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
