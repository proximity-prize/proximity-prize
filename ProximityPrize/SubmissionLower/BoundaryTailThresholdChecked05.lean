import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked04

namespace ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
open Lower80801.CompressedData Lower80801.PhaseChecks
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cell_5_0_0 : CertificateAt 5 0 0 := by decide +kernel
theorem cell_5_0_1 : CertificateAt 5 0 1 := by decide +kernel
theorem cell_5_0_2 : CertificateAt 5 0 2 := by decide +kernel
theorem cell_5_0_3 : CertificateAt 5 0 3 := by decide +kernel
theorem cell_5_0_4 : CertificateAt 5 0 4 := by decide +kernel
theorem cell_5_0_5 : CertificateAt 5 0 5 := by decide +kernel
theorem row_5_0 : ThresholdAt 5 0 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 0 0 cell_5_0_0
    | exact certificate_sound 5 0 1 cell_5_0_1
    | exact certificate_sound 5 0 2 cell_5_0_2
    | exact certificate_sound 5 0 3 cell_5_0_3
    | exact certificate_sound 5 0 4 cell_5_0_4
    | exact certificate_sound 5 0 5 cell_5_0_5
theorem cell_5_1_0 : CertificateAt 5 1 0 := by decide +kernel
theorem cell_5_1_1 : CertificateAt 5 1 1 := by decide +kernel
theorem cell_5_1_2 : CertificateAt 5 1 2 := by decide +kernel
theorem cell_5_1_3 : CertificateAt 5 1 3 := by decide +kernel
theorem cell_5_1_4 : CertificateAt 5 1 4 := by decide +kernel
theorem cell_5_1_5 : CertificateAt 5 1 5 := by decide +kernel
theorem row_5_1 : ThresholdAt 5 1 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 1 0 cell_5_1_0
    | exact certificate_sound 5 1 1 cell_5_1_1
    | exact certificate_sound 5 1 2 cell_5_1_2
    | exact certificate_sound 5 1 3 cell_5_1_3
    | exact certificate_sound 5 1 4 cell_5_1_4
    | exact certificate_sound 5 1 5 cell_5_1_5
theorem cell_5_2_0 : CertificateAt 5 2 0 := by decide +kernel
theorem cell_5_2_1 : CertificateAt 5 2 1 := by decide +kernel
theorem cell_5_2_2 : CertificateAt 5 2 2 := by decide +kernel
theorem cell_5_2_3 : CertificateAt 5 2 3 := by decide +kernel
theorem cell_5_2_4 : CertificateAt 5 2 4 := by decide +kernel
theorem cell_5_2_5 : CertificateAt 5 2 5 := by decide +kernel
theorem row_5_2 : ThresholdAt 5 2 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 2 0 cell_5_2_0
    | exact certificate_sound 5 2 1 cell_5_2_1
    | exact certificate_sound 5 2 2 cell_5_2_2
    | exact certificate_sound 5 2 3 cell_5_2_3
    | exact certificate_sound 5 2 4 cell_5_2_4
    | exact certificate_sound 5 2 5 cell_5_2_5
theorem cell_5_3_0 : CertificateAt 5 3 0 := by decide +kernel
theorem cell_5_3_1 : CertificateAt 5 3 1 := by decide +kernel
theorem cell_5_3_2 : CertificateAt 5 3 2 := by decide +kernel
theorem cell_5_3_3 : CertificateAt 5 3 3 := by decide +kernel
theorem cell_5_3_4 : CertificateAt 5 3 4 := by decide +kernel
theorem cell_5_3_5 : CertificateAt 5 3 5 := by decide +kernel
theorem row_5_3 : ThresholdAt 5 3 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 3 0 cell_5_3_0
    | exact certificate_sound 5 3 1 cell_5_3_1
    | exact certificate_sound 5 3 2 cell_5_3_2
    | exact certificate_sound 5 3 3 cell_5_3_3
    | exact certificate_sound 5 3 4 cell_5_3_4
    | exact certificate_sound 5 3 5 cell_5_3_5
theorem cell_5_4_0 : CertificateAt 5 4 0 := by decide +kernel
theorem cell_5_4_1 : CertificateAt 5 4 1 := by decide +kernel
theorem cell_5_4_2 : CertificateAt 5 4 2 := by decide +kernel
theorem cell_5_4_3 : CertificateAt 5 4 3 := by decide +kernel
theorem cell_5_4_4 : CertificateAt 5 4 4 := by decide +kernel
theorem cell_5_4_5 : CertificateAt 5 4 5 := by decide +kernel
theorem row_5_4 : ThresholdAt 5 4 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 4 0 cell_5_4_0
    | exact certificate_sound 5 4 1 cell_5_4_1
    | exact certificate_sound 5 4 2 cell_5_4_2
    | exact certificate_sound 5 4 3 cell_5_4_3
    | exact certificate_sound 5 4 4 cell_5_4_4
    | exact certificate_sound 5 4 5 cell_5_4_5
theorem cell_5_5_0 : CertificateAt 5 5 0 := by decide +kernel
theorem cell_5_5_1 : CertificateAt 5 5 1 := by decide +kernel
theorem cell_5_5_2 : CertificateAt 5 5 2 := by decide +kernel
theorem cell_5_5_3 : CertificateAt 5 5 3 := by decide +kernel
theorem cell_5_5_4 : CertificateAt 5 5 4 := by decide +kernel
theorem cell_5_5_5 : CertificateAt 5 5 5 := by decide +kernel
theorem row_5_5 : ThresholdAt 5 5 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 5 0 cell_5_5_0
    | exact certificate_sound 5 5 1 cell_5_5_1
    | exact certificate_sound 5 5 2 cell_5_5_2
    | exact certificate_sound 5 5 3 cell_5_5_3
    | exact certificate_sound 5 5 4 cell_5_5_4
    | exact certificate_sound 5 5 5 cell_5_5_5
theorem cell_5_6_0 : CertificateAt 5 6 0 := by decide +kernel
theorem cell_5_6_1 : CertificateAt 5 6 1 := by decide +kernel
theorem cell_5_6_2 : CertificateAt 5 6 2 := by decide +kernel
theorem cell_5_6_3 : CertificateAt 5 6 3 := by decide +kernel
theorem cell_5_6_4 : CertificateAt 5 6 4 := by decide +kernel
theorem cell_5_6_5 : CertificateAt 5 6 5 := by decide +kernel
theorem row_5_6 : ThresholdAt 5 6 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 6 0 cell_5_6_0
    | exact certificate_sound 5 6 1 cell_5_6_1
    | exact certificate_sound 5 6 2 cell_5_6_2
    | exact certificate_sound 5 6 3 cell_5_6_3
    | exact certificate_sound 5 6 4 cell_5_6_4
    | exact certificate_sound 5 6 5 cell_5_6_5
theorem cell_5_7_0 : CertificateAt 5 7 0 := by decide +kernel
theorem cell_5_7_1 : CertificateAt 5 7 1 := by decide +kernel
theorem cell_5_7_2 : CertificateAt 5 7 2 := by decide +kernel
theorem cell_5_7_3 : CertificateAt 5 7 3 := by decide +kernel
theorem cell_5_7_4 : CertificateAt 5 7 4 := by decide +kernel
theorem cell_5_7_5 : CertificateAt 5 7 5 := by decide +kernel
theorem row_5_7 : ThresholdAt 5 7 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 7 0 cell_5_7_0
    | exact certificate_sound 5 7 1 cell_5_7_1
    | exact certificate_sound 5 7 2 cell_5_7_2
    | exact certificate_sound 5 7 3 cell_5_7_3
    | exact certificate_sound 5 7 4 cell_5_7_4
    | exact certificate_sound 5 7 5 cell_5_7_5
theorem cell_5_8_0 : CertificateAt 5 8 0 := by decide +kernel
theorem cell_5_8_1 : CertificateAt 5 8 1 := by decide +kernel
theorem cell_5_8_2 : CertificateAt 5 8 2 := by decide +kernel
theorem cell_5_8_3 : CertificateAt 5 8 3 := by decide +kernel
theorem cell_5_8_4 : CertificateAt 5 8 4 := by decide +kernel
theorem cell_5_8_5 : CertificateAt 5 8 5 := by decide +kernel
theorem row_5_8 : ThresholdAt 5 8 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 8 0 cell_5_8_0
    | exact certificate_sound 5 8 1 cell_5_8_1
    | exact certificate_sound 5 8 2 cell_5_8_2
    | exact certificate_sound 5 8 3 cell_5_8_3
    | exact certificate_sound 5 8 4 cell_5_8_4
    | exact certificate_sound 5 8 5 cell_5_8_5
theorem cell_5_9_0 : CertificateAt 5 9 0 := by decide +kernel
theorem cell_5_9_1 : CertificateAt 5 9 1 := by decide +kernel
theorem cell_5_9_2 : CertificateAt 5 9 2 := by decide +kernel
theorem cell_5_9_3 : CertificateAt 5 9 3 := by decide +kernel
theorem cell_5_9_4 : CertificateAt 5 9 4 := by decide +kernel
theorem cell_5_9_5 : CertificateAt 5 9 5 := by decide +kernel
theorem row_5_9 : ThresholdAt 5 9 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 9 0 cell_5_9_0
    | exact certificate_sound 5 9 1 cell_5_9_1
    | exact certificate_sound 5 9 2 cell_5_9_2
    | exact certificate_sound 5 9 3 cell_5_9_3
    | exact certificate_sound 5 9 4 cell_5_9_4
    | exact certificate_sound 5 9 5 cell_5_9_5
theorem cell_5_10_0 : CertificateAt 5 10 0 := by decide +kernel
theorem cell_5_10_1 : CertificateAt 5 10 1 := by decide +kernel
theorem cell_5_10_2 : CertificateAt 5 10 2 := by decide +kernel
theorem cell_5_10_3 : CertificateAt 5 10 3 := by decide +kernel
theorem cell_5_10_4 : CertificateAt 5 10 4 := by decide +kernel
theorem cell_5_10_5 : CertificateAt 5 10 5 := by decide +kernel
theorem row_5_10 : ThresholdAt 5 10 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 10 0 cell_5_10_0
    | exact certificate_sound 5 10 1 cell_5_10_1
    | exact certificate_sound 5 10 2 cell_5_10_2
    | exact certificate_sound 5 10 3 cell_5_10_3
    | exact certificate_sound 5 10 4 cell_5_10_4
    | exact certificate_sound 5 10 5 cell_5_10_5
theorem cell_5_11_0 : CertificateAt 5 11 0 := by decide +kernel
theorem cell_5_11_1 : CertificateAt 5 11 1 := by decide +kernel
theorem cell_5_11_2 : CertificateAt 5 11 2 := by decide +kernel
theorem cell_5_11_3 : CertificateAt 5 11 3 := by decide +kernel
theorem cell_5_11_4 : CertificateAt 5 11 4 := by decide +kernel
theorem cell_5_11_5 : CertificateAt 5 11 5 := by decide +kernel
theorem row_5_11 : ThresholdAt 5 11 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 11 0 cell_5_11_0
    | exact certificate_sound 5 11 1 cell_5_11_1
    | exact certificate_sound 5 11 2 cell_5_11_2
    | exact certificate_sound 5 11 3 cell_5_11_3
    | exact certificate_sound 5 11 4 cell_5_11_4
    | exact certificate_sound 5 11 5 cell_5_11_5
theorem cell_5_12_0 : CertificateAt 5 12 0 := by decide +kernel
theorem cell_5_12_1 : CertificateAt 5 12 1 := by decide +kernel
theorem cell_5_12_2 : CertificateAt 5 12 2 := by decide +kernel
theorem cell_5_12_3 : CertificateAt 5 12 3 := by decide +kernel
theorem cell_5_12_4 : CertificateAt 5 12 4 := by decide +kernel
theorem cell_5_12_5 : CertificateAt 5 12 5 := by decide +kernel
theorem row_5_12 : ThresholdAt 5 12 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 12 0 cell_5_12_0
    | exact certificate_sound 5 12 1 cell_5_12_1
    | exact certificate_sound 5 12 2 cell_5_12_2
    | exact certificate_sound 5 12 3 cell_5_12_3
    | exact certificate_sound 5 12 4 cell_5_12_4
    | exact certificate_sound 5 12 5 cell_5_12_5
theorem cell_5_13_0 : CertificateAt 5 13 0 := by decide +kernel
theorem cell_5_13_1 : CertificateAt 5 13 1 := by decide +kernel
theorem cell_5_13_2 : CertificateAt 5 13 2 := by decide +kernel
theorem cell_5_13_3 : CertificateAt 5 13 3 := by decide +kernel
theorem cell_5_13_4 : CertificateAt 5 13 4 := by decide +kernel
theorem cell_5_13_5 : CertificateAt 5 13 5 := by decide +kernel
theorem row_5_13 : ThresholdAt 5 13 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 13 0 cell_5_13_0
    | exact certificate_sound 5 13 1 cell_5_13_1
    | exact certificate_sound 5 13 2 cell_5_13_2
    | exact certificate_sound 5 13 3 cell_5_13_3
    | exact certificate_sound 5 13 4 cell_5_13_4
    | exact certificate_sound 5 13 5 cell_5_13_5
theorem cell_5_14_0 : CertificateAt 5 14 0 := by decide +kernel
theorem cell_5_14_1 : CertificateAt 5 14 1 := by decide +kernel
theorem cell_5_14_2 : CertificateAt 5 14 2 := by decide +kernel
theorem cell_5_14_3 : CertificateAt 5 14 3 := by decide +kernel
theorem cell_5_14_4 : CertificateAt 5 14 4 := by decide +kernel
theorem cell_5_14_5 : CertificateAt 5 14 5 := by decide +kernel
theorem row_5_14 : ThresholdAt 5 14 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 14 0 cell_5_14_0
    | exact certificate_sound 5 14 1 cell_5_14_1
    | exact certificate_sound 5 14 2 cell_5_14_2
    | exact certificate_sound 5 14 3 cell_5_14_3
    | exact certificate_sound 5 14 4 cell_5_14_4
    | exact certificate_sound 5 14 5 cell_5_14_5
theorem cell_5_15_0 : CertificateAt 5 15 0 := by decide +kernel
theorem cell_5_15_1 : CertificateAt 5 15 1 := by decide +kernel
theorem cell_5_15_2 : CertificateAt 5 15 2 := by decide +kernel
theorem cell_5_15_3 : CertificateAt 5 15 3 := by decide +kernel
theorem cell_5_15_4 : CertificateAt 5 15 4 := by decide +kernel
theorem cell_5_15_5 : CertificateAt 5 15 5 := by decide +kernel
theorem row_5_15 : ThresholdAt 5 15 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 15 0 cell_5_15_0
    | exact certificate_sound 5 15 1 cell_5_15_1
    | exact certificate_sound 5 15 2 cell_5_15_2
    | exact certificate_sound 5 15 3 cell_5_15_3
    | exact certificate_sound 5 15 4 cell_5_15_4
    | exact certificate_sound 5 15 5 cell_5_15_5
theorem cell_5_16_0 : CertificateAt 5 16 0 := by decide +kernel
theorem cell_5_16_1 : CertificateAt 5 16 1 := by decide +kernel
theorem cell_5_16_2 : CertificateAt 5 16 2 := by decide +kernel
theorem cell_5_16_3 : CertificateAt 5 16 3 := by decide +kernel
theorem cell_5_16_4 : CertificateAt 5 16 4 := by decide +kernel
theorem cell_5_16_5 : CertificateAt 5 16 5 := by decide +kernel
theorem row_5_16 : ThresholdAt 5 16 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 16 0 cell_5_16_0
    | exact certificate_sound 5 16 1 cell_5_16_1
    | exact certificate_sound 5 16 2 cell_5_16_2
    | exact certificate_sound 5 16 3 cell_5_16_3
    | exact certificate_sound 5 16 4 cell_5_16_4
    | exact certificate_sound 5 16 5 cell_5_16_5
theorem cell_5_17_0 : CertificateAt 5 17 0 := by decide +kernel
theorem cell_5_17_1 : CertificateAt 5 17 1 := by decide +kernel
theorem cell_5_17_2 : CertificateAt 5 17 2 := by decide +kernel
theorem cell_5_17_3 : CertificateAt 5 17 3 := by decide +kernel
theorem cell_5_17_4 : CertificateAt 5 17 4 := by decide +kernel
theorem cell_5_17_5 : CertificateAt 5 17 5 := by decide +kernel
theorem row_5_17 : ThresholdAt 5 17 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 17 0 cell_5_17_0
    | exact certificate_sound 5 17 1 cell_5_17_1
    | exact certificate_sound 5 17 2 cell_5_17_2
    | exact certificate_sound 5 17 3 cell_5_17_3
    | exact certificate_sound 5 17 4 cell_5_17_4
    | exact certificate_sound 5 17 5 cell_5_17_5
theorem cell_5_18_0 : CertificateAt 5 18 0 := by decide +kernel
theorem cell_5_18_1 : CertificateAt 5 18 1 := by decide +kernel
theorem cell_5_18_2 : CertificateAt 5 18 2 := by decide +kernel
theorem cell_5_18_3 : CertificateAt 5 18 3 := by decide +kernel
theorem cell_5_18_4 : CertificateAt 5 18 4 := by decide +kernel
theorem cell_5_18_5 : CertificateAt 5 18 5 := by decide +kernel
theorem row_5_18 : ThresholdAt 5 18 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 18 0 cell_5_18_0
    | exact certificate_sound 5 18 1 cell_5_18_1
    | exact certificate_sound 5 18 2 cell_5_18_2
    | exact certificate_sound 5 18 3 cell_5_18_3
    | exact certificate_sound 5 18 4 cell_5_18_4
    | exact certificate_sound 5 18 5 cell_5_18_5
theorem cell_5_19_0 : CertificateAt 5 19 0 := by decide +kernel
theorem cell_5_19_1 : CertificateAt 5 19 1 := by decide +kernel
theorem cell_5_19_2 : CertificateAt 5 19 2 := by decide +kernel
theorem cell_5_19_3 : CertificateAt 5 19 3 := by decide +kernel
theorem cell_5_19_4 : CertificateAt 5 19 4 := by decide +kernel
theorem cell_5_19_5 : CertificateAt 5 19 5 := by decide +kernel
theorem row_5_19 : ThresholdAt 5 19 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 19 0 cell_5_19_0
    | exact certificate_sound 5 19 1 cell_5_19_1
    | exact certificate_sound 5 19 2 cell_5_19_2
    | exact certificate_sound 5 19 3 cell_5_19_3
    | exact certificate_sound 5 19 4 cell_5_19_4
    | exact certificate_sound 5 19 5 cell_5_19_5
theorem cell_5_20_0 : CertificateAt 5 20 0 := by decide +kernel
theorem cell_5_20_1 : CertificateAt 5 20 1 := by decide +kernel
theorem cell_5_20_2 : CertificateAt 5 20 2 := by decide +kernel
theorem cell_5_20_3 : CertificateAt 5 20 3 := by decide +kernel
theorem cell_5_20_4 : CertificateAt 5 20 4 := by decide +kernel
theorem cell_5_20_5 : CertificateAt 5 20 5 := by decide +kernel
theorem row_5_20 : ThresholdAt 5 20 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 20 0 cell_5_20_0
    | exact certificate_sound 5 20 1 cell_5_20_1
    | exact certificate_sound 5 20 2 cell_5_20_2
    | exact certificate_sound 5 20 3 cell_5_20_3
    | exact certificate_sound 5 20 4 cell_5_20_4
    | exact certificate_sound 5 20 5 cell_5_20_5
theorem cell_5_21_0 : CertificateAt 5 21 0 := by decide +kernel
theorem cell_5_21_1 : CertificateAt 5 21 1 := by decide +kernel
theorem cell_5_21_2 : CertificateAt 5 21 2 := by decide +kernel
theorem cell_5_21_3 : CertificateAt 5 21 3 := by decide +kernel
theorem cell_5_21_4 : CertificateAt 5 21 4 := by decide +kernel
theorem cell_5_21_5 : CertificateAt 5 21 5 := by decide +kernel
theorem row_5_21 : ThresholdAt 5 21 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 21 0 cell_5_21_0
    | exact certificate_sound 5 21 1 cell_5_21_1
    | exact certificate_sound 5 21 2 cell_5_21_2
    | exact certificate_sound 5 21 3 cell_5_21_3
    | exact certificate_sound 5 21 4 cell_5_21_4
    | exact certificate_sound 5 21 5 cell_5_21_5
theorem cell_5_22_0 : CertificateAt 5 22 0 := by decide +kernel
theorem cell_5_22_1 : CertificateAt 5 22 1 := by decide +kernel
theorem cell_5_22_2 : CertificateAt 5 22 2 := by decide +kernel
theorem cell_5_22_3 : CertificateAt 5 22 3 := by decide +kernel
theorem cell_5_22_4 : CertificateAt 5 22 4 := by decide +kernel
theorem cell_5_22_5 : CertificateAt 5 22 5 := by decide +kernel
theorem row_5_22 : ThresholdAt 5 22 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 22 0 cell_5_22_0
    | exact certificate_sound 5 22 1 cell_5_22_1
    | exact certificate_sound 5 22 2 cell_5_22_2
    | exact certificate_sound 5 22 3 cell_5_22_3
    | exact certificate_sound 5 22 4 cell_5_22_4
    | exact certificate_sound 5 22 5 cell_5_22_5
theorem cell_5_23_0 : CertificateAt 5 23 0 := by decide +kernel
theorem cell_5_23_1 : CertificateAt 5 23 1 := by decide +kernel
theorem cell_5_23_2 : CertificateAt 5 23 2 := by decide +kernel
theorem cell_5_23_3 : CertificateAt 5 23 3 := by decide +kernel
theorem cell_5_23_4 : CertificateAt 5 23 4 := by decide +kernel
theorem cell_5_23_5 : CertificateAt 5 23 5 := by decide +kernel
theorem row_5_23 : ThresholdAt 5 23 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 23 0 cell_5_23_0
    | exact certificate_sound 5 23 1 cell_5_23_1
    | exact certificate_sound 5 23 2 cell_5_23_2
    | exact certificate_sound 5 23 3 cell_5_23_3
    | exact certificate_sound 5 23 4 cell_5_23_4
    | exact certificate_sound 5 23 5 cell_5_23_5
theorem cell_5_24_0 : CertificateAt 5 24 0 := by decide +kernel
theorem cell_5_24_1 : CertificateAt 5 24 1 := by decide +kernel
theorem cell_5_24_2 : CertificateAt 5 24 2 := by decide +kernel
theorem cell_5_24_3 : CertificateAt 5 24 3 := by decide +kernel
theorem cell_5_24_4 : CertificateAt 5 24 4 := by decide +kernel
theorem cell_5_24_5 : CertificateAt 5 24 5 := by decide +kernel
theorem row_5_24 : ThresholdAt 5 24 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 24 0 cell_5_24_0
    | exact certificate_sound 5 24 1 cell_5_24_1
    | exact certificate_sound 5 24 2 cell_5_24_2
    | exact certificate_sound 5 24 3 cell_5_24_3
    | exact certificate_sound 5 24 4 cell_5_24_4
    | exact certificate_sound 5 24 5 cell_5_24_5
theorem cell_5_25_0 : CertificateAt 5 25 0 := by decide +kernel
theorem cell_5_25_1 : CertificateAt 5 25 1 := by decide +kernel
theorem cell_5_25_2 : CertificateAt 5 25 2 := by decide +kernel
theorem cell_5_25_3 : CertificateAt 5 25 3 := by decide +kernel
theorem cell_5_25_4 : CertificateAt 5 25 4 := by decide +kernel
theorem cell_5_25_5 : CertificateAt 5 25 5 := by decide +kernel
theorem row_5_25 : ThresholdAt 5 25 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 25 0 cell_5_25_0
    | exact certificate_sound 5 25 1 cell_5_25_1
    | exact certificate_sound 5 25 2 cell_5_25_2
    | exact certificate_sound 5 25 3 cell_5_25_3
    | exact certificate_sound 5 25 4 cell_5_25_4
    | exact certificate_sound 5 25 5 cell_5_25_5
theorem cell_5_26_0 : CertificateAt 5 26 0 := by decide +kernel
theorem cell_5_26_1 : CertificateAt 5 26 1 := by decide +kernel
theorem cell_5_26_2 : CertificateAt 5 26 2 := by decide +kernel
theorem cell_5_26_3 : CertificateAt 5 26 3 := by decide +kernel
theorem cell_5_26_4 : CertificateAt 5 26 4 := by decide +kernel
theorem cell_5_26_5 : CertificateAt 5 26 5 := by decide +kernel
theorem row_5_26 : ThresholdAt 5 26 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 26 0 cell_5_26_0
    | exact certificate_sound 5 26 1 cell_5_26_1
    | exact certificate_sound 5 26 2 cell_5_26_2
    | exact certificate_sound 5 26 3 cell_5_26_3
    | exact certificate_sound 5 26 4 cell_5_26_4
    | exact certificate_sound 5 26 5 cell_5_26_5
theorem cell_5_27_0 : CertificateAt 5 27 0 := by decide +kernel
theorem cell_5_27_1 : CertificateAt 5 27 1 := by decide +kernel
theorem cell_5_27_2 : CertificateAt 5 27 2 := by decide +kernel
theorem cell_5_27_3 : CertificateAt 5 27 3 := by decide +kernel
theorem cell_5_27_4 : CertificateAt 5 27 4 := by decide +kernel
theorem cell_5_27_5 : CertificateAt 5 27 5 := by decide +kernel
theorem row_5_27 : ThresholdAt 5 27 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 27 0 cell_5_27_0
    | exact certificate_sound 5 27 1 cell_5_27_1
    | exact certificate_sound 5 27 2 cell_5_27_2
    | exact certificate_sound 5 27 3 cell_5_27_3
    | exact certificate_sound 5 27 4 cell_5_27_4
    | exact certificate_sound 5 27 5 cell_5_27_5
theorem cell_5_28_0 : CertificateAt 5 28 0 := by decide +kernel
theorem cell_5_28_1 : CertificateAt 5 28 1 := by decide +kernel
theorem cell_5_28_2 : CertificateAt 5 28 2 := by decide +kernel
theorem cell_5_28_3 : CertificateAt 5 28 3 := by decide +kernel
theorem cell_5_28_4 : CertificateAt 5 28 4 := by decide +kernel
theorem cell_5_28_5 : CertificateAt 5 28 5 := by decide +kernel
theorem row_5_28 : ThresholdAt 5 28 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 28 0 cell_5_28_0
    | exact certificate_sound 5 28 1 cell_5_28_1
    | exact certificate_sound 5 28 2 cell_5_28_2
    | exact certificate_sound 5 28 3 cell_5_28_3
    | exact certificate_sound 5 28 4 cell_5_28_4
    | exact certificate_sound 5 28 5 cell_5_28_5
theorem cell_5_29_0 : CertificateAt 5 29 0 := by decide +kernel
theorem cell_5_29_1 : CertificateAt 5 29 1 := by decide +kernel
theorem cell_5_29_2 : CertificateAt 5 29 2 := by decide +kernel
theorem cell_5_29_3 : CertificateAt 5 29 3 := by decide +kernel
theorem cell_5_29_4 : CertificateAt 5 29 4 := by decide +kernel
theorem cell_5_29_5 : CertificateAt 5 29 5 := by decide +kernel
theorem row_5_29 : ThresholdAt 5 29 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 29 0 cell_5_29_0
    | exact certificate_sound 5 29 1 cell_5_29_1
    | exact certificate_sound 5 29 2 cell_5_29_2
    | exact certificate_sound 5 29 3 cell_5_29_3
    | exact certificate_sound 5 29 4 cell_5_29_4
    | exact certificate_sound 5 29 5 cell_5_29_5
theorem cell_5_30_0 : CertificateAt 5 30 0 := by decide +kernel
theorem cell_5_30_1 : CertificateAt 5 30 1 := by decide +kernel
theorem cell_5_30_2 : CertificateAt 5 30 2 := by decide +kernel
theorem cell_5_30_3 : CertificateAt 5 30 3 := by decide +kernel
theorem cell_5_30_4 : CertificateAt 5 30 4 := by decide +kernel
theorem cell_5_30_5 : CertificateAt 5 30 5 := by decide +kernel
theorem row_5_30 : ThresholdAt 5 30 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 30 0 cell_5_30_0
    | exact certificate_sound 5 30 1 cell_5_30_1
    | exact certificate_sound 5 30 2 cell_5_30_2
    | exact certificate_sound 5 30 3 cell_5_30_3
    | exact certificate_sound 5 30 4 cell_5_30_4
    | exact certificate_sound 5 30 5 cell_5_30_5
theorem cell_5_31_0 : CertificateAt 5 31 0 := by decide +kernel
theorem cell_5_31_1 : CertificateAt 5 31 1 := by decide +kernel
theorem cell_5_31_2 : CertificateAt 5 31 2 := by decide +kernel
theorem cell_5_31_3 : CertificateAt 5 31 3 := by decide +kernel
theorem cell_5_31_4 : CertificateAt 5 31 4 := by decide +kernel
theorem cell_5_31_5 : CertificateAt 5 31 5 := by decide +kernel
theorem row_5_31 : ThresholdAt 5 31 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 31 0 cell_5_31_0
    | exact certificate_sound 5 31 1 cell_5_31_1
    | exact certificate_sound 5 31 2 cell_5_31_2
    | exact certificate_sound 5 31 3 cell_5_31_3
    | exact certificate_sound 5 31 4 cell_5_31_4
    | exact certificate_sound 5 31 5 cell_5_31_5
theorem cell_5_32_0 : CertificateAt 5 32 0 := by decide +kernel
theorem cell_5_32_1 : CertificateAt 5 32 1 := by decide +kernel
theorem cell_5_32_2 : CertificateAt 5 32 2 := by decide +kernel
theorem cell_5_32_3 : CertificateAt 5 32 3 := by decide +kernel
theorem cell_5_32_4 : CertificateAt 5 32 4 := by decide +kernel
theorem cell_5_32_5 : CertificateAt 5 32 5 := by decide +kernel
theorem row_5_32 : ThresholdAt 5 32 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 32 0 cell_5_32_0
    | exact certificate_sound 5 32 1 cell_5_32_1
    | exact certificate_sound 5 32 2 cell_5_32_2
    | exact certificate_sound 5 32 3 cell_5_32_3
    | exact certificate_sound 5 32 4 cell_5_32_4
    | exact certificate_sound 5 32 5 cell_5_32_5
theorem cell_5_33_0 : CertificateAt 5 33 0 := by decide +kernel
theorem cell_5_33_1 : CertificateAt 5 33 1 := by decide +kernel
theorem cell_5_33_2 : CertificateAt 5 33 2 := by decide +kernel
theorem cell_5_33_3 : CertificateAt 5 33 3 := by decide +kernel
theorem cell_5_33_4 : CertificateAt 5 33 4 := by decide +kernel
theorem cell_5_33_5 : CertificateAt 5 33 5 := by decide +kernel
theorem row_5_33 : ThresholdAt 5 33 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 33 0 cell_5_33_0
    | exact certificate_sound 5 33 1 cell_5_33_1
    | exact certificate_sound 5 33 2 cell_5_33_2
    | exact certificate_sound 5 33 3 cell_5_33_3
    | exact certificate_sound 5 33 4 cell_5_33_4
    | exact certificate_sound 5 33 5 cell_5_33_5
theorem cell_5_34_0 : CertificateAt 5 34 0 := by decide +kernel
theorem cell_5_34_1 : CertificateAt 5 34 1 := by decide +kernel
theorem cell_5_34_2 : CertificateAt 5 34 2 := by decide +kernel
theorem cell_5_34_3 : CertificateAt 5 34 3 := by decide +kernel
theorem cell_5_34_4 : CertificateAt 5 34 4 := by decide +kernel
theorem cell_5_34_5 : CertificateAt 5 34 5 := by decide +kernel
theorem row_5_34 : ThresholdAt 5 34 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 34 0 cell_5_34_0
    | exact certificate_sound 5 34 1 cell_5_34_1
    | exact certificate_sound 5 34 2 cell_5_34_2
    | exact certificate_sound 5 34 3 cell_5_34_3
    | exact certificate_sound 5 34 4 cell_5_34_4
    | exact certificate_sound 5 34 5 cell_5_34_5
theorem cell_5_35_0 : CertificateAt 5 35 0 := by decide +kernel
theorem cell_5_35_1 : CertificateAt 5 35 1 := by decide +kernel
theorem cell_5_35_2 : CertificateAt 5 35 2 := by decide +kernel
theorem cell_5_35_3 : CertificateAt 5 35 3 := by decide +kernel
theorem cell_5_35_4 : CertificateAt 5 35 4 := by decide +kernel
theorem cell_5_35_5 : CertificateAt 5 35 5 := by decide +kernel
theorem row_5_35 : ThresholdAt 5 35 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 35 0 cell_5_35_0
    | exact certificate_sound 5 35 1 cell_5_35_1
    | exact certificate_sound 5 35 2 cell_5_35_2
    | exact certificate_sound 5 35 3 cell_5_35_3
    | exact certificate_sound 5 35 4 cell_5_35_4
    | exact certificate_sound 5 35 5 cell_5_35_5
theorem cell_5_36_0 : CertificateAt 5 36 0 := by decide +kernel
theorem cell_5_36_1 : CertificateAt 5 36 1 := by decide +kernel
theorem cell_5_36_2 : CertificateAt 5 36 2 := by decide +kernel
theorem cell_5_36_3 : CertificateAt 5 36 3 := by decide +kernel
theorem cell_5_36_4 : CertificateAt 5 36 4 := by decide +kernel
theorem cell_5_36_5 : CertificateAt 5 36 5 := by decide +kernel
theorem row_5_36 : ThresholdAt 5 36 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 36 0 cell_5_36_0
    | exact certificate_sound 5 36 1 cell_5_36_1
    | exact certificate_sound 5 36 2 cell_5_36_2
    | exact certificate_sound 5 36 3 cell_5_36_3
    | exact certificate_sound 5 36 4 cell_5_36_4
    | exact certificate_sound 5 36 5 cell_5_36_5
theorem cell_5_37_0 : CertificateAt 5 37 0 := by decide +kernel
theorem cell_5_37_1 : CertificateAt 5 37 1 := by decide +kernel
theorem cell_5_37_2 : CertificateAt 5 37 2 := by decide +kernel
theorem cell_5_37_3 : CertificateAt 5 37 3 := by decide +kernel
theorem cell_5_37_4 : CertificateAt 5 37 4 := by decide +kernel
theorem cell_5_37_5 : CertificateAt 5 37 5 := by decide +kernel
theorem row_5_37 : ThresholdAt 5 37 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 37 0 cell_5_37_0
    | exact certificate_sound 5 37 1 cell_5_37_1
    | exact certificate_sound 5 37 2 cell_5_37_2
    | exact certificate_sound 5 37 3 cell_5_37_3
    | exact certificate_sound 5 37 4 cell_5_37_4
    | exact certificate_sound 5 37 5 cell_5_37_5
theorem cell_5_38_0 : CertificateAt 5 38 0 := by decide +kernel
theorem cell_5_38_1 : CertificateAt 5 38 1 := by decide +kernel
theorem cell_5_38_2 : CertificateAt 5 38 2 := by decide +kernel
theorem cell_5_38_3 : CertificateAt 5 38 3 := by decide +kernel
theorem cell_5_38_4 : CertificateAt 5 38 4 := by decide +kernel
theorem cell_5_38_5 : CertificateAt 5 38 5 := by decide +kernel
theorem row_5_38 : ThresholdAt 5 38 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 38 0 cell_5_38_0
    | exact certificate_sound 5 38 1 cell_5_38_1
    | exact certificate_sound 5 38 2 cell_5_38_2
    | exact certificate_sound 5 38 3 cell_5_38_3
    | exact certificate_sound 5 38 4 cell_5_38_4
    | exact certificate_sound 5 38 5 cell_5_38_5
theorem cell_5_39_0 : CertificateAt 5 39 0 := by decide +kernel
theorem cell_5_39_1 : CertificateAt 5 39 1 := by decide +kernel
theorem cell_5_39_2 : CertificateAt 5 39 2 := by decide +kernel
theorem cell_5_39_3 : CertificateAt 5 39 3 := by decide +kernel
theorem cell_5_39_4 : CertificateAt 5 39 4 := by decide +kernel
theorem cell_5_39_5 : CertificateAt 5 39 5 := by decide +kernel
theorem row_5_39 : ThresholdAt 5 39 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 39 0 cell_5_39_0
    | exact certificate_sound 5 39 1 cell_5_39_1
    | exact certificate_sound 5 39 2 cell_5_39_2
    | exact certificate_sound 5 39 3 cell_5_39_3
    | exact certificate_sound 5 39 4 cell_5_39_4
    | exact certificate_sound 5 39 5 cell_5_39_5
theorem cell_5_40_0 : CertificateAt 5 40 0 := by decide +kernel
theorem cell_5_40_1 : CertificateAt 5 40 1 := by decide +kernel
theorem cell_5_40_2 : CertificateAt 5 40 2 := by decide +kernel
theorem cell_5_40_3 : CertificateAt 5 40 3 := by decide +kernel
theorem cell_5_40_4 : CertificateAt 5 40 4 := by decide +kernel
theorem cell_5_40_5 : CertificateAt 5 40 5 := by decide +kernel
theorem row_5_40 : ThresholdAt 5 40 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 40 0 cell_5_40_0
    | exact certificate_sound 5 40 1 cell_5_40_1
    | exact certificate_sound 5 40 2 cell_5_40_2
    | exact certificate_sound 5 40 3 cell_5_40_3
    | exact certificate_sound 5 40 4 cell_5_40_4
    | exact certificate_sound 5 40 5 cell_5_40_5
theorem cell_5_41_0 : CertificateAt 5 41 0 := by decide +kernel
theorem cell_5_41_1 : CertificateAt 5 41 1 := by decide +kernel
theorem cell_5_41_2 : CertificateAt 5 41 2 := by decide +kernel
theorem cell_5_41_3 : CertificateAt 5 41 3 := by decide +kernel
theorem cell_5_41_4 : CertificateAt 5 41 4 := by decide +kernel
theorem cell_5_41_5 : CertificateAt 5 41 5 := by decide +kernel
theorem row_5_41 : ThresholdAt 5 41 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 41 0 cell_5_41_0
    | exact certificate_sound 5 41 1 cell_5_41_1
    | exact certificate_sound 5 41 2 cell_5_41_2
    | exact certificate_sound 5 41 3 cell_5_41_3
    | exact certificate_sound 5 41 4 cell_5_41_4
    | exact certificate_sound 5 41 5 cell_5_41_5
theorem cell_5_42_0 : CertificateAt 5 42 0 := by decide +kernel
theorem cell_5_42_1 : CertificateAt 5 42 1 := by decide +kernel
theorem cell_5_42_2 : CertificateAt 5 42 2 := by decide +kernel
theorem cell_5_42_3 : CertificateAt 5 42 3 := by decide +kernel
theorem cell_5_42_4 : CertificateAt 5 42 4 := by decide +kernel
theorem cell_5_42_5 : CertificateAt 5 42 5 := by decide +kernel
theorem row_5_42 : ThresholdAt 5 42 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 42 0 cell_5_42_0
    | exact certificate_sound 5 42 1 cell_5_42_1
    | exact certificate_sound 5 42 2 cell_5_42_2
    | exact certificate_sound 5 42 3 cell_5_42_3
    | exact certificate_sound 5 42 4 cell_5_42_4
    | exact certificate_sound 5 42 5 cell_5_42_5
theorem cell_5_43_0 : CertificateAt 5 43 0 := by decide +kernel
theorem cell_5_43_1 : CertificateAt 5 43 1 := by decide +kernel
theorem cell_5_43_2 : CertificateAt 5 43 2 := by decide +kernel
theorem cell_5_43_3 : CertificateAt 5 43 3 := by decide +kernel
theorem cell_5_43_4 : CertificateAt 5 43 4 := by decide +kernel
theorem cell_5_43_5 : CertificateAt 5 43 5 := by decide +kernel
theorem row_5_43 : ThresholdAt 5 43 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 43 0 cell_5_43_0
    | exact certificate_sound 5 43 1 cell_5_43_1
    | exact certificate_sound 5 43 2 cell_5_43_2
    | exact certificate_sound 5 43 3 cell_5_43_3
    | exact certificate_sound 5 43 4 cell_5_43_4
    | exact certificate_sound 5 43 5 cell_5_43_5
theorem cell_5_44_0 : CertificateAt 5 44 0 := by decide +kernel
theorem cell_5_44_1 : CertificateAt 5 44 1 := by decide +kernel
theorem cell_5_44_2 : CertificateAt 5 44 2 := by decide +kernel
theorem cell_5_44_3 : CertificateAt 5 44 3 := by decide +kernel
theorem cell_5_44_4 : CertificateAt 5 44 4 := by decide +kernel
theorem cell_5_44_5 : CertificateAt 5 44 5 := by decide +kernel
theorem row_5_44 : ThresholdAt 5 44 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 44 0 cell_5_44_0
    | exact certificate_sound 5 44 1 cell_5_44_1
    | exact certificate_sound 5 44 2 cell_5_44_2
    | exact certificate_sound 5 44 3 cell_5_44_3
    | exact certificate_sound 5 44 4 cell_5_44_4
    | exact certificate_sound 5 44 5 cell_5_44_5
theorem cell_5_45_0 : CertificateAt 5 45 0 := by decide +kernel
theorem cell_5_45_1 : CertificateAt 5 45 1 := by decide +kernel
theorem cell_5_45_2 : CertificateAt 5 45 2 := by decide +kernel
theorem cell_5_45_3 : CertificateAt 5 45 3 := by decide +kernel
theorem cell_5_45_4 : CertificateAt 5 45 4 := by decide +kernel
theorem cell_5_45_5 : CertificateAt 5 45 5 := by decide +kernel
theorem row_5_45 : ThresholdAt 5 45 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 45 0 cell_5_45_0
    | exact certificate_sound 5 45 1 cell_5_45_1
    | exact certificate_sound 5 45 2 cell_5_45_2
    | exact certificate_sound 5 45 3 cell_5_45_3
    | exact certificate_sound 5 45 4 cell_5_45_4
    | exact certificate_sound 5 45 5 cell_5_45_5
theorem cell_5_46_0 : CertificateAt 5 46 0 := by decide +kernel
theorem cell_5_46_1 : CertificateAt 5 46 1 := by decide +kernel
theorem cell_5_46_2 : CertificateAt 5 46 2 := by decide +kernel
theorem cell_5_46_3 : CertificateAt 5 46 3 := by decide +kernel
theorem cell_5_46_4 : CertificateAt 5 46 4 := by decide +kernel
theorem cell_5_46_5 : CertificateAt 5 46 5 := by decide +kernel
theorem row_5_46 : ThresholdAt 5 46 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 46 0 cell_5_46_0
    | exact certificate_sound 5 46 1 cell_5_46_1
    | exact certificate_sound 5 46 2 cell_5_46_2
    | exact certificate_sound 5 46 3 cell_5_46_3
    | exact certificate_sound 5 46 4 cell_5_46_4
    | exact certificate_sound 5 46 5 cell_5_46_5
theorem cell_5_47_0 : CertificateAt 5 47 0 := by decide +kernel
theorem cell_5_47_1 : CertificateAt 5 47 1 := by decide +kernel
theorem cell_5_47_2 : CertificateAt 5 47 2 := by decide +kernel
theorem cell_5_47_3 : CertificateAt 5 47 3 := by decide +kernel
theorem cell_5_47_4 : CertificateAt 5 47 4 := by decide +kernel
theorem cell_5_47_5 : CertificateAt 5 47 5 := by decide +kernel
theorem row_5_47 : ThresholdAt 5 47 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 47 0 cell_5_47_0
    | exact certificate_sound 5 47 1 cell_5_47_1
    | exact certificate_sound 5 47 2 cell_5_47_2
    | exact certificate_sound 5 47 3 cell_5_47_3
    | exact certificate_sound 5 47 4 cell_5_47_4
    | exact certificate_sound 5 47 5 cell_5_47_5
theorem cell_5_48_0 : CertificateAt 5 48 0 := by decide +kernel
theorem cell_5_48_1 : CertificateAt 5 48 1 := by decide +kernel
theorem cell_5_48_2 : CertificateAt 5 48 2 := by decide +kernel
theorem cell_5_48_3 : CertificateAt 5 48 3 := by decide +kernel
theorem cell_5_48_4 : CertificateAt 5 48 4 := by decide +kernel
theorem cell_5_48_5 : CertificateAt 5 48 5 := by decide +kernel
theorem row_5_48 : ThresholdAt 5 48 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 48 0 cell_5_48_0
    | exact certificate_sound 5 48 1 cell_5_48_1
    | exact certificate_sound 5 48 2 cell_5_48_2
    | exact certificate_sound 5 48 3 cell_5_48_3
    | exact certificate_sound 5 48 4 cell_5_48_4
    | exact certificate_sound 5 48 5 cell_5_48_5
theorem cell_5_49_0 : CertificateAt 5 49 0 := by decide +kernel
theorem cell_5_49_1 : CertificateAt 5 49 1 := by decide +kernel
theorem cell_5_49_2 : CertificateAt 5 49 2 := by decide +kernel
theorem cell_5_49_3 : CertificateAt 5 49 3 := by decide +kernel
theorem cell_5_49_4 : CertificateAt 5 49 4 := by decide +kernel
theorem cell_5_49_5 : CertificateAt 5 49 5 := by decide +kernel
theorem row_5_49 : ThresholdAt 5 49 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 49 0 cell_5_49_0
    | exact certificate_sound 5 49 1 cell_5_49_1
    | exact certificate_sound 5 49 2 cell_5_49_2
    | exact certificate_sound 5 49 3 cell_5_49_3
    | exact certificate_sound 5 49 4 cell_5_49_4
    | exact certificate_sound 5 49 5 cell_5_49_5
theorem cell_5_50_0 : CertificateAt 5 50 0 := by decide +kernel
theorem cell_5_50_1 : CertificateAt 5 50 1 := by decide +kernel
theorem cell_5_50_2 : CertificateAt 5 50 2 := by decide +kernel
theorem cell_5_50_3 : CertificateAt 5 50 3 := by decide +kernel
theorem cell_5_50_4 : CertificateAt 5 50 4 := by decide +kernel
theorem cell_5_50_5 : CertificateAt 5 50 5 := by decide +kernel
theorem row_5_50 : ThresholdAt 5 50 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 50 0 cell_5_50_0
    | exact certificate_sound 5 50 1 cell_5_50_1
    | exact certificate_sound 5 50 2 cell_5_50_2
    | exact certificate_sound 5 50 3 cell_5_50_3
    | exact certificate_sound 5 50 4 cell_5_50_4
    | exact certificate_sound 5 50 5 cell_5_50_5
theorem cell_5_51_0 : CertificateAt 5 51 0 := by decide +kernel
theorem cell_5_51_1 : CertificateAt 5 51 1 := by decide +kernel
theorem cell_5_51_2 : CertificateAt 5 51 2 := by decide +kernel
theorem cell_5_51_3 : CertificateAt 5 51 3 := by decide +kernel
theorem cell_5_51_4 : CertificateAt 5 51 4 := by decide +kernel
theorem cell_5_51_5 : CertificateAt 5 51 5 := by decide +kernel
theorem row_5_51 : ThresholdAt 5 51 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 51 0 cell_5_51_0
    | exact certificate_sound 5 51 1 cell_5_51_1
    | exact certificate_sound 5 51 2 cell_5_51_2
    | exact certificate_sound 5 51 3 cell_5_51_3
    | exact certificate_sound 5 51 4 cell_5_51_4
    | exact certificate_sound 5 51 5 cell_5_51_5
theorem cell_5_52_0 : CertificateAt 5 52 0 := by decide +kernel
theorem cell_5_52_1 : CertificateAt 5 52 1 := by decide +kernel
theorem cell_5_52_2 : CertificateAt 5 52 2 := by decide +kernel
theorem cell_5_52_3 : CertificateAt 5 52 3 := by decide +kernel
theorem cell_5_52_4 : CertificateAt 5 52 4 := by decide +kernel
theorem cell_5_52_5 : CertificateAt 5 52 5 := by decide +kernel
theorem row_5_52 : ThresholdAt 5 52 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 52 0 cell_5_52_0
    | exact certificate_sound 5 52 1 cell_5_52_1
    | exact certificate_sound 5 52 2 cell_5_52_2
    | exact certificate_sound 5 52 3 cell_5_52_3
    | exact certificate_sound 5 52 4 cell_5_52_4
    | exact certificate_sound 5 52 5 cell_5_52_5
theorem cell_5_53_0 : CertificateAt 5 53 0 := by decide +kernel
theorem cell_5_53_1 : CertificateAt 5 53 1 := by decide +kernel
theorem cell_5_53_2 : CertificateAt 5 53 2 := by decide +kernel
theorem cell_5_53_3 : CertificateAt 5 53 3 := by decide +kernel
theorem cell_5_53_4 : CertificateAt 5 53 4 := by decide +kernel
theorem cell_5_53_5 : CertificateAt 5 53 5 := by decide +kernel
theorem row_5_53 : ThresholdAt 5 53 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 53 0 cell_5_53_0
    | exact certificate_sound 5 53 1 cell_5_53_1
    | exact certificate_sound 5 53 2 cell_5_53_2
    | exact certificate_sound 5 53 3 cell_5_53_3
    | exact certificate_sound 5 53 4 cell_5_53_4
    | exact certificate_sound 5 53 5 cell_5_53_5
theorem cell_5_54_0 : CertificateAt 5 54 0 := by decide +kernel
theorem cell_5_54_1 : CertificateAt 5 54 1 := by decide +kernel
theorem cell_5_54_2 : CertificateAt 5 54 2 := by decide +kernel
theorem cell_5_54_3 : CertificateAt 5 54 3 := by decide +kernel
theorem cell_5_54_4 : CertificateAt 5 54 4 := by decide +kernel
theorem cell_5_54_5 : CertificateAt 5 54 5 := by decide +kernel
theorem row_5_54 : ThresholdAt 5 54 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 54 0 cell_5_54_0
    | exact certificate_sound 5 54 1 cell_5_54_1
    | exact certificate_sound 5 54 2 cell_5_54_2
    | exact certificate_sound 5 54 3 cell_5_54_3
    | exact certificate_sound 5 54 4 cell_5_54_4
    | exact certificate_sound 5 54 5 cell_5_54_5
theorem cell_5_55_0 : CertificateAt 5 55 0 := by decide +kernel
theorem cell_5_55_1 : CertificateAt 5 55 1 := by decide +kernel
theorem cell_5_55_2 : CertificateAt 5 55 2 := by decide +kernel
theorem cell_5_55_3 : CertificateAt 5 55 3 := by decide +kernel
theorem cell_5_55_4 : CertificateAt 5 55 4 := by decide +kernel
theorem cell_5_55_5 : CertificateAt 5 55 5 := by decide +kernel
theorem row_5_55 : ThresholdAt 5 55 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 55 0 cell_5_55_0
    | exact certificate_sound 5 55 1 cell_5_55_1
    | exact certificate_sound 5 55 2 cell_5_55_2
    | exact certificate_sound 5 55 3 cell_5_55_3
    | exact certificate_sound 5 55 4 cell_5_55_4
    | exact certificate_sound 5 55 5 cell_5_55_5
theorem cell_5_56_0 : CertificateAt 5 56 0 := by decide +kernel
theorem cell_5_56_1 : CertificateAt 5 56 1 := by decide +kernel
theorem cell_5_56_2 : CertificateAt 5 56 2 := by decide +kernel
theorem cell_5_56_3 : CertificateAt 5 56 3 := by decide +kernel
theorem cell_5_56_4 : CertificateAt 5 56 4 := by decide +kernel
theorem cell_5_56_5 : CertificateAt 5 56 5 := by decide +kernel
theorem row_5_56 : ThresholdAt 5 56 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 56 0 cell_5_56_0
    | exact certificate_sound 5 56 1 cell_5_56_1
    | exact certificate_sound 5 56 2 cell_5_56_2
    | exact certificate_sound 5 56 3 cell_5_56_3
    | exact certificate_sound 5 56 4 cell_5_56_4
    | exact certificate_sound 5 56 5 cell_5_56_5
theorem cell_5_57_0 : CertificateAt 5 57 0 := by decide +kernel
theorem cell_5_57_1 : CertificateAt 5 57 1 := by decide +kernel
theorem cell_5_57_2 : CertificateAt 5 57 2 := by decide +kernel
theorem cell_5_57_3 : CertificateAt 5 57 3 := by decide +kernel
theorem cell_5_57_4 : CertificateAt 5 57 4 := by decide +kernel
theorem cell_5_57_5 : CertificateAt 5 57 5 := by decide +kernel
theorem row_5_57 : ThresholdAt 5 57 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 57 0 cell_5_57_0
    | exact certificate_sound 5 57 1 cell_5_57_1
    | exact certificate_sound 5 57 2 cell_5_57_2
    | exact certificate_sound 5 57 3 cell_5_57_3
    | exact certificate_sound 5 57 4 cell_5_57_4
    | exact certificate_sound 5 57 5 cell_5_57_5
theorem cell_5_58_0 : CertificateAt 5 58 0 := by decide +kernel
theorem cell_5_58_1 : CertificateAt 5 58 1 := by decide +kernel
theorem cell_5_58_2 : CertificateAt 5 58 2 := by decide +kernel
theorem cell_5_58_3 : CertificateAt 5 58 3 := by decide +kernel
theorem cell_5_58_4 : CertificateAt 5 58 4 := by decide +kernel
theorem cell_5_58_5 : CertificateAt 5 58 5 := by decide +kernel
theorem row_5_58 : ThresholdAt 5 58 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 58 0 cell_5_58_0
    | exact certificate_sound 5 58 1 cell_5_58_1
    | exact certificate_sound 5 58 2 cell_5_58_2
    | exact certificate_sound 5 58 3 cell_5_58_3
    | exact certificate_sound 5 58 4 cell_5_58_4
    | exact certificate_sound 5 58 5 cell_5_58_5
theorem cell_5_59_0 : CertificateAt 5 59 0 := by decide +kernel
theorem cell_5_59_1 : CertificateAt 5 59 1 := by decide +kernel
theorem cell_5_59_2 : CertificateAt 5 59 2 := by decide +kernel
theorem cell_5_59_3 : CertificateAt 5 59 3 := by decide +kernel
theorem cell_5_59_4 : CertificateAt 5 59 4 := by decide +kernel
theorem cell_5_59_5 : CertificateAt 5 59 5 := by decide +kernel
theorem row_5_59 : ThresholdAt 5 59 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 59 0 cell_5_59_0
    | exact certificate_sound 5 59 1 cell_5_59_1
    | exact certificate_sound 5 59 2 cell_5_59_2
    | exact certificate_sound 5 59 3 cell_5_59_3
    | exact certificate_sound 5 59 4 cell_5_59_4
    | exact certificate_sound 5 59 5 cell_5_59_5
theorem cell_5_60_0 : CertificateAt 5 60 0 := by decide +kernel
theorem cell_5_60_1 : CertificateAt 5 60 1 := by decide +kernel
theorem cell_5_60_2 : CertificateAt 5 60 2 := by decide +kernel
theorem cell_5_60_3 : CertificateAt 5 60 3 := by decide +kernel
theorem cell_5_60_4 : CertificateAt 5 60 4 := by decide +kernel
theorem cell_5_60_5 : CertificateAt 5 60 5 := by decide +kernel
theorem row_5_60 : ThresholdAt 5 60 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 60 0 cell_5_60_0
    | exact certificate_sound 5 60 1 cell_5_60_1
    | exact certificate_sound 5 60 2 cell_5_60_2
    | exact certificate_sound 5 60 3 cell_5_60_3
    | exact certificate_sound 5 60 4 cell_5_60_4
    | exact certificate_sound 5 60 5 cell_5_60_5
theorem cell_5_61_0 : CertificateAt 5 61 0 := by decide +kernel
theorem cell_5_61_1 : CertificateAt 5 61 1 := by decide +kernel
theorem cell_5_61_2 : CertificateAt 5 61 2 := by decide +kernel
theorem cell_5_61_3 : CertificateAt 5 61 3 := by decide +kernel
theorem cell_5_61_4 : CertificateAt 5 61 4 := by decide +kernel
theorem cell_5_61_5 : CertificateAt 5 61 5 := by decide +kernel
theorem row_5_61 : ThresholdAt 5 61 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 61 0 cell_5_61_0
    | exact certificate_sound 5 61 1 cell_5_61_1
    | exact certificate_sound 5 61 2 cell_5_61_2
    | exact certificate_sound 5 61 3 cell_5_61_3
    | exact certificate_sound 5 61 4 cell_5_61_4
    | exact certificate_sound 5 61 5 cell_5_61_5
theorem cell_5_62_0 : CertificateAt 5 62 0 := by decide +kernel
theorem cell_5_62_1 : CertificateAt 5 62 1 := by decide +kernel
theorem cell_5_62_2 : CertificateAt 5 62 2 := by decide +kernel
theorem cell_5_62_3 : CertificateAt 5 62 3 := by decide +kernel
theorem cell_5_62_4 : CertificateAt 5 62 4 := by decide +kernel
theorem cell_5_62_5 : CertificateAt 5 62 5 := by decide +kernel
theorem row_5_62 : ThresholdAt 5 62 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 62 0 cell_5_62_0
    | exact certificate_sound 5 62 1 cell_5_62_1
    | exact certificate_sound 5 62 2 cell_5_62_2
    | exact certificate_sound 5 62 3 cell_5_62_3
    | exact certificate_sound 5 62 4 cell_5_62_4
    | exact certificate_sound 5 62 5 cell_5_62_5
theorem cell_5_63_0 : CertificateAt 5 63 0 := by decide +kernel
theorem cell_5_63_1 : CertificateAt 5 63 1 := by decide +kernel
theorem cell_5_63_2 : CertificateAt 5 63 2 := by decide +kernel
theorem cell_5_63_3 : CertificateAt 5 63 3 := by decide +kernel
theorem cell_5_63_4 : CertificateAt 5 63 4 := by decide +kernel
theorem cell_5_63_5 : CertificateAt 5 63 5 := by decide +kernel
theorem row_5_63 : ThresholdAt 5 63 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 63 0 cell_5_63_0
    | exact certificate_sound 5 63 1 cell_5_63_1
    | exact certificate_sound 5 63 2 cell_5_63_2
    | exact certificate_sound 5 63 3 cell_5_63_3
    | exact certificate_sound 5 63 4 cell_5_63_4
    | exact certificate_sound 5 63 5 cell_5_63_5
theorem cell_5_64_0 : CertificateAt 5 64 0 := by decide +kernel
theorem cell_5_64_1 : CertificateAt 5 64 1 := by decide +kernel
theorem cell_5_64_2 : CertificateAt 5 64 2 := by decide +kernel
theorem cell_5_64_3 : CertificateAt 5 64 3 := by decide +kernel
theorem cell_5_64_4 : CertificateAt 5 64 4 := by decide +kernel
theorem cell_5_64_5 : CertificateAt 5 64 5 := by decide +kernel
theorem row_5_64 : ThresholdAt 5 64 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 64 0 cell_5_64_0
    | exact certificate_sound 5 64 1 cell_5_64_1
    | exact certificate_sound 5 64 2 cell_5_64_2
    | exact certificate_sound 5 64 3 cell_5_64_3
    | exact certificate_sound 5 64 4 cell_5_64_4
    | exact certificate_sound 5 64 5 cell_5_64_5
theorem cell_5_65_0 : CertificateAt 5 65 0 := by decide +kernel
theorem cell_5_65_1 : CertificateAt 5 65 1 := by decide +kernel
theorem cell_5_65_2 : CertificateAt 5 65 2 := by decide +kernel
theorem cell_5_65_3 : CertificateAt 5 65 3 := by decide +kernel
theorem cell_5_65_4 : CertificateAt 5 65 4 := by decide +kernel
theorem cell_5_65_5 : CertificateAt 5 65 5 := by decide +kernel
theorem row_5_65 : ThresholdAt 5 65 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 65 0 cell_5_65_0
    | exact certificate_sound 5 65 1 cell_5_65_1
    | exact certificate_sound 5 65 2 cell_5_65_2
    | exact certificate_sound 5 65 3 cell_5_65_3
    | exact certificate_sound 5 65 4 cell_5_65_4
    | exact certificate_sound 5 65 5 cell_5_65_5
theorem cell_5_66_0 : CertificateAt 5 66 0 := by decide +kernel
theorem cell_5_66_1 : CertificateAt 5 66 1 := by decide +kernel
theorem cell_5_66_2 : CertificateAt 5 66 2 := by decide +kernel
theorem cell_5_66_3 : CertificateAt 5 66 3 := by decide +kernel
theorem cell_5_66_4 : CertificateAt 5 66 4 := by decide +kernel
theorem cell_5_66_5 : CertificateAt 5 66 5 := by decide +kernel
theorem row_5_66 : ThresholdAt 5 66 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 66 0 cell_5_66_0
    | exact certificate_sound 5 66 1 cell_5_66_1
    | exact certificate_sound 5 66 2 cell_5_66_2
    | exact certificate_sound 5 66 3 cell_5_66_3
    | exact certificate_sound 5 66 4 cell_5_66_4
    | exact certificate_sound 5 66 5 cell_5_66_5
theorem cell_5_67_0 : CertificateAt 5 67 0 := by decide +kernel
theorem cell_5_67_1 : CertificateAt 5 67 1 := by decide +kernel
theorem cell_5_67_2 : CertificateAt 5 67 2 := by decide +kernel
theorem cell_5_67_3 : CertificateAt 5 67 3 := by decide +kernel
theorem cell_5_67_4 : CertificateAt 5 67 4 := by decide +kernel
theorem cell_5_67_5 : CertificateAt 5 67 5 := by decide +kernel
theorem row_5_67 : ThresholdAt 5 67 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 67 0 cell_5_67_0
    | exact certificate_sound 5 67 1 cell_5_67_1
    | exact certificate_sound 5 67 2 cell_5_67_2
    | exact certificate_sound 5 67 3 cell_5_67_3
    | exact certificate_sound 5 67 4 cell_5_67_4
    | exact certificate_sound 5 67 5 cell_5_67_5
theorem cell_5_68_0 : CertificateAt 5 68 0 := by decide +kernel
theorem cell_5_68_1 : CertificateAt 5 68 1 := by decide +kernel
theorem cell_5_68_2 : CertificateAt 5 68 2 := by decide +kernel
theorem cell_5_68_3 : CertificateAt 5 68 3 := by decide +kernel
theorem cell_5_68_4 : CertificateAt 5 68 4 := by decide +kernel
theorem cell_5_68_5 : CertificateAt 5 68 5 := by decide +kernel
theorem row_5_68 : ThresholdAt 5 68 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 68 0 cell_5_68_0
    | exact certificate_sound 5 68 1 cell_5_68_1
    | exact certificate_sound 5 68 2 cell_5_68_2
    | exact certificate_sound 5 68 3 cell_5_68_3
    | exact certificate_sound 5 68 4 cell_5_68_4
    | exact certificate_sound 5 68 5 cell_5_68_5
theorem cell_5_69_0 : CertificateAt 5 69 0 := by decide +kernel
theorem cell_5_69_1 : CertificateAt 5 69 1 := by decide +kernel
theorem cell_5_69_2 : CertificateAt 5 69 2 := by decide +kernel
theorem cell_5_69_3 : CertificateAt 5 69 3 := by decide +kernel
theorem cell_5_69_4 : CertificateAt 5 69 4 := by decide +kernel
theorem cell_5_69_5 : CertificateAt 5 69 5 := by decide +kernel
theorem row_5_69 : ThresholdAt 5 69 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 69 0 cell_5_69_0
    | exact certificate_sound 5 69 1 cell_5_69_1
    | exact certificate_sound 5 69 2 cell_5_69_2
    | exact certificate_sound 5 69 3 cell_5_69_3
    | exact certificate_sound 5 69 4 cell_5_69_4
    | exact certificate_sound 5 69 5 cell_5_69_5
theorem cell_5_70_0 : CertificateAt 5 70 0 := by decide +kernel
theorem cell_5_70_1 : CertificateAt 5 70 1 := by decide +kernel
theorem cell_5_70_2 : CertificateAt 5 70 2 := by decide +kernel
theorem cell_5_70_3 : CertificateAt 5 70 3 := by decide +kernel
theorem cell_5_70_4 : CertificateAt 5 70 4 := by decide +kernel
theorem cell_5_70_5 : CertificateAt 5 70 5 := by decide +kernel
theorem row_5_70 : ThresholdAt 5 70 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 70 0 cell_5_70_0
    | exact certificate_sound 5 70 1 cell_5_70_1
    | exact certificate_sound 5 70 2 cell_5_70_2
    | exact certificate_sound 5 70 3 cell_5_70_3
    | exact certificate_sound 5 70 4 cell_5_70_4
    | exact certificate_sound 5 70 5 cell_5_70_5
theorem cell_5_71_0 : CertificateAt 5 71 0 := by decide +kernel
theorem cell_5_71_1 : CertificateAt 5 71 1 := by decide +kernel
theorem cell_5_71_2 : CertificateAt 5 71 2 := by decide +kernel
theorem cell_5_71_3 : CertificateAt 5 71 3 := by decide +kernel
theorem cell_5_71_4 : CertificateAt 5 71 4 := by decide +kernel
theorem cell_5_71_5 : CertificateAt 5 71 5 := by decide +kernel
theorem row_5_71 : ThresholdAt 5 71 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 71 0 cell_5_71_0
    | exact certificate_sound 5 71 1 cell_5_71_1
    | exact certificate_sound 5 71 2 cell_5_71_2
    | exact certificate_sound 5 71 3 cell_5_71_3
    | exact certificate_sound 5 71 4 cell_5_71_4
    | exact certificate_sound 5 71 5 cell_5_71_5
theorem cell_5_72_0 : CertificateAt 5 72 0 := by decide +kernel
theorem cell_5_72_1 : CertificateAt 5 72 1 := by decide +kernel
theorem cell_5_72_2 : CertificateAt 5 72 2 := by decide +kernel
theorem cell_5_72_3 : CertificateAt 5 72 3 := by decide +kernel
theorem cell_5_72_4 : CertificateAt 5 72 4 := by decide +kernel
theorem cell_5_72_5 : CertificateAt 5 72 5 := by decide +kernel
theorem row_5_72 : ThresholdAt 5 72 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 72 0 cell_5_72_0
    | exact certificate_sound 5 72 1 cell_5_72_1
    | exact certificate_sound 5 72 2 cell_5_72_2
    | exact certificate_sound 5 72 3 cell_5_72_3
    | exact certificate_sound 5 72 4 cell_5_72_4
    | exact certificate_sound 5 72 5 cell_5_72_5
theorem cell_5_73_0 : CertificateAt 5 73 0 := by decide +kernel
theorem cell_5_73_1 : CertificateAt 5 73 1 := by decide +kernel
theorem cell_5_73_2 : CertificateAt 5 73 2 := by decide +kernel
theorem cell_5_73_3 : CertificateAt 5 73 3 := by decide +kernel
theorem cell_5_73_4 : CertificateAt 5 73 4 := by decide +kernel
theorem cell_5_73_5 : CertificateAt 5 73 5 := by decide +kernel
theorem row_5_73 : ThresholdAt 5 73 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 73 0 cell_5_73_0
    | exact certificate_sound 5 73 1 cell_5_73_1
    | exact certificate_sound 5 73 2 cell_5_73_2
    | exact certificate_sound 5 73 3 cell_5_73_3
    | exact certificate_sound 5 73 4 cell_5_73_4
    | exact certificate_sound 5 73 5 cell_5_73_5
theorem cell_5_74_0 : CertificateAt 5 74 0 := by decide +kernel
theorem cell_5_74_1 : CertificateAt 5 74 1 := by decide +kernel
theorem cell_5_74_2 : CertificateAt 5 74 2 := by decide +kernel
theorem cell_5_74_3 : CertificateAt 5 74 3 := by decide +kernel
theorem cell_5_74_4 : CertificateAt 5 74 4 := by decide +kernel
theorem cell_5_74_5 : CertificateAt 5 74 5 := by decide +kernel
theorem row_5_74 : ThresholdAt 5 74 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 74 0 cell_5_74_0
    | exact certificate_sound 5 74 1 cell_5_74_1
    | exact certificate_sound 5 74 2 cell_5_74_2
    | exact certificate_sound 5 74 3 cell_5_74_3
    | exact certificate_sound 5 74 4 cell_5_74_4
    | exact certificate_sound 5 74 5 cell_5_74_5
theorem cell_5_75_0 : CertificateAt 5 75 0 := by decide +kernel
theorem cell_5_75_1 : CertificateAt 5 75 1 := by decide +kernel
theorem cell_5_75_2 : CertificateAt 5 75 2 := by decide +kernel
theorem cell_5_75_3 : CertificateAt 5 75 3 := by decide +kernel
theorem cell_5_75_4 : CertificateAt 5 75 4 := by decide +kernel
theorem cell_5_75_5 : CertificateAt 5 75 5 := by decide +kernel
theorem row_5_75 : ThresholdAt 5 75 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 75 0 cell_5_75_0
    | exact certificate_sound 5 75 1 cell_5_75_1
    | exact certificate_sound 5 75 2 cell_5_75_2
    | exact certificate_sound 5 75 3 cell_5_75_3
    | exact certificate_sound 5 75 4 cell_5_75_4
    | exact certificate_sound 5 75 5 cell_5_75_5
theorem cell_5_76_0 : CertificateAt 5 76 0 := by decide +kernel
theorem cell_5_76_1 : CertificateAt 5 76 1 := by decide +kernel
theorem cell_5_76_2 : CertificateAt 5 76 2 := by decide +kernel
theorem cell_5_76_3 : CertificateAt 5 76 3 := by decide +kernel
theorem cell_5_76_4 : CertificateAt 5 76 4 := by decide +kernel
theorem cell_5_76_5 : CertificateAt 5 76 5 := by decide +kernel
theorem row_5_76 : ThresholdAt 5 76 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 76 0 cell_5_76_0
    | exact certificate_sound 5 76 1 cell_5_76_1
    | exact certificate_sound 5 76 2 cell_5_76_2
    | exact certificate_sound 5 76 3 cell_5_76_3
    | exact certificate_sound 5 76 4 cell_5_76_4
    | exact certificate_sound 5 76 5 cell_5_76_5
theorem cell_5_77_0 : CertificateAt 5 77 0 := by decide +kernel
theorem cell_5_77_1 : CertificateAt 5 77 1 := by decide +kernel
theorem cell_5_77_2 : CertificateAt 5 77 2 := by decide +kernel
theorem cell_5_77_3 : CertificateAt 5 77 3 := by decide +kernel
theorem cell_5_77_4 : CertificateAt 5 77 4 := by decide +kernel
theorem cell_5_77_5 : CertificateAt 5 77 5 := by decide +kernel
theorem row_5_77 : ThresholdAt 5 77 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 77 0 cell_5_77_0
    | exact certificate_sound 5 77 1 cell_5_77_1
    | exact certificate_sound 5 77 2 cell_5_77_2
    | exact certificate_sound 5 77 3 cell_5_77_3
    | exact certificate_sound 5 77 4 cell_5_77_4
    | exact certificate_sound 5 77 5 cell_5_77_5
theorem cell_5_78_0 : CertificateAt 5 78 0 := by decide +kernel
theorem cell_5_78_1 : CertificateAt 5 78 1 := by decide +kernel
theorem cell_5_78_2 : CertificateAt 5 78 2 := by decide +kernel
theorem cell_5_78_3 : CertificateAt 5 78 3 := by decide +kernel
theorem cell_5_78_4 : CertificateAt 5 78 4 := by decide +kernel
theorem cell_5_78_5 : CertificateAt 5 78 5 := by decide +kernel
theorem row_5_78 : ThresholdAt 5 78 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 78 0 cell_5_78_0
    | exact certificate_sound 5 78 1 cell_5_78_1
    | exact certificate_sound 5 78 2 cell_5_78_2
    | exact certificate_sound 5 78 3 cell_5_78_3
    | exact certificate_sound 5 78 4 cell_5_78_4
    | exact certificate_sound 5 78 5 cell_5_78_5
theorem cell_5_79_0 : CertificateAt 5 79 0 := by decide +kernel
theorem cell_5_79_1 : CertificateAt 5 79 1 := by decide +kernel
theorem cell_5_79_2 : CertificateAt 5 79 2 := by decide +kernel
theorem cell_5_79_3 : CertificateAt 5 79 3 := by decide +kernel
theorem cell_5_79_4 : CertificateAt 5 79 4 := by decide +kernel
theorem cell_5_79_5 : CertificateAt 5 79 5 := by decide +kernel
theorem row_5_79 : ThresholdAt 5 79 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 79 0 cell_5_79_0
    | exact certificate_sound 5 79 1 cell_5_79_1
    | exact certificate_sound 5 79 2 cell_5_79_2
    | exact certificate_sound 5 79 3 cell_5_79_3
    | exact certificate_sound 5 79 4 cell_5_79_4
    | exact certificate_sound 5 79 5 cell_5_79_5
theorem cell_5_80_0 : CertificateAt 5 80 0 := by decide +kernel
theorem cell_5_80_1 : CertificateAt 5 80 1 := by decide +kernel
theorem cell_5_80_2 : CertificateAt 5 80 2 := by decide +kernel
theorem cell_5_80_3 : CertificateAt 5 80 3 := by decide +kernel
theorem cell_5_80_4 : CertificateAt 5 80 4 := by decide +kernel
theorem cell_5_80_5 : CertificateAt 5 80 5 := by decide +kernel
theorem row_5_80 : ThresholdAt 5 80 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 80 0 cell_5_80_0
    | exact certificate_sound 5 80 1 cell_5_80_1
    | exact certificate_sound 5 80 2 cell_5_80_2
    | exact certificate_sound 5 80 3 cell_5_80_3
    | exact certificate_sound 5 80 4 cell_5_80_4
    | exact certificate_sound 5 80 5 cell_5_80_5
theorem cell_5_81_0 : CertificateAt 5 81 0 := by decide +kernel
theorem cell_5_81_1 : CertificateAt 5 81 1 := by decide +kernel
theorem cell_5_81_2 : CertificateAt 5 81 2 := by decide +kernel
theorem cell_5_81_3 : CertificateAt 5 81 3 := by decide +kernel
theorem cell_5_81_4 : CertificateAt 5 81 4 := by decide +kernel
theorem cell_5_81_5 : CertificateAt 5 81 5 := by decide +kernel
theorem row_5_81 : ThresholdAt 5 81 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 81 0 cell_5_81_0
    | exact certificate_sound 5 81 1 cell_5_81_1
    | exact certificate_sound 5 81 2 cell_5_81_2
    | exact certificate_sound 5 81 3 cell_5_81_3
    | exact certificate_sound 5 81 4 cell_5_81_4
    | exact certificate_sound 5 81 5 cell_5_81_5
theorem cell_5_82_0 : CertificateAt 5 82 0 := by decide +kernel
theorem cell_5_82_1 : CertificateAt 5 82 1 := by decide +kernel
theorem cell_5_82_2 : CertificateAt 5 82 2 := by decide +kernel
theorem cell_5_82_3 : CertificateAt 5 82 3 := by decide +kernel
theorem cell_5_82_4 : CertificateAt 5 82 4 := by decide +kernel
theorem cell_5_82_5 : CertificateAt 5 82 5 := by decide +kernel
theorem row_5_82 : ThresholdAt 5 82 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 82 0 cell_5_82_0
    | exact certificate_sound 5 82 1 cell_5_82_1
    | exact certificate_sound 5 82 2 cell_5_82_2
    | exact certificate_sound 5 82 3 cell_5_82_3
    | exact certificate_sound 5 82 4 cell_5_82_4
    | exact certificate_sound 5 82 5 cell_5_82_5
theorem cell_5_83_0 : CertificateAt 5 83 0 := by decide +kernel
theorem cell_5_83_1 : CertificateAt 5 83 1 := by decide +kernel
theorem cell_5_83_2 : CertificateAt 5 83 2 := by decide +kernel
theorem cell_5_83_3 : CertificateAt 5 83 3 := by decide +kernel
theorem cell_5_83_4 : CertificateAt 5 83 4 := by decide +kernel
theorem cell_5_83_5 : CertificateAt 5 83 5 := by decide +kernel
theorem row_5_83 : ThresholdAt 5 83 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 83 0 cell_5_83_0
    | exact certificate_sound 5 83 1 cell_5_83_1
    | exact certificate_sound 5 83 2 cell_5_83_2
    | exact certificate_sound 5 83 3 cell_5_83_3
    | exact certificate_sound 5 83 4 cell_5_83_4
    | exact certificate_sound 5 83 5 cell_5_83_5
theorem cell_5_84_0 : CertificateAt 5 84 0 := by decide +kernel
theorem cell_5_84_1 : CertificateAt 5 84 1 := by decide +kernel
theorem cell_5_84_2 : CertificateAt 5 84 2 := by decide +kernel
theorem cell_5_84_3 : CertificateAt 5 84 3 := by decide +kernel
theorem cell_5_84_4 : CertificateAt 5 84 4 := by decide +kernel
theorem cell_5_84_5 : CertificateAt 5 84 5 := by decide +kernel
theorem row_5_84 : ThresholdAt 5 84 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 84 0 cell_5_84_0
    | exact certificate_sound 5 84 1 cell_5_84_1
    | exact certificate_sound 5 84 2 cell_5_84_2
    | exact certificate_sound 5 84 3 cell_5_84_3
    | exact certificate_sound 5 84 4 cell_5_84_4
    | exact certificate_sound 5 84 5 cell_5_84_5
theorem cell_5_85_0 : CertificateAt 5 85 0 := by decide +kernel
theorem cell_5_85_1 : CertificateAt 5 85 1 := by decide +kernel
theorem cell_5_85_2 : CertificateAt 5 85 2 := by decide +kernel
theorem cell_5_85_3 : CertificateAt 5 85 3 := by decide +kernel
theorem cell_5_85_4 : CertificateAt 5 85 4 := by decide +kernel
theorem cell_5_85_5 : CertificateAt 5 85 5 := by decide +kernel
theorem row_5_85 : ThresholdAt 5 85 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 85 0 cell_5_85_0
    | exact certificate_sound 5 85 1 cell_5_85_1
    | exact certificate_sound 5 85 2 cell_5_85_2
    | exact certificate_sound 5 85 3 cell_5_85_3
    | exact certificate_sound 5 85 4 cell_5_85_4
    | exact certificate_sound 5 85 5 cell_5_85_5
theorem cell_5_86_0 : CertificateAt 5 86 0 := by decide +kernel
theorem cell_5_86_1 : CertificateAt 5 86 1 := by decide +kernel
theorem cell_5_86_2 : CertificateAt 5 86 2 := by decide +kernel
theorem cell_5_86_3 : CertificateAt 5 86 3 := by decide +kernel
theorem cell_5_86_4 : CertificateAt 5 86 4 := by decide +kernel
theorem cell_5_86_5 : CertificateAt 5 86 5 := by decide +kernel
theorem row_5_86 : ThresholdAt 5 86 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 86 0 cell_5_86_0
    | exact certificate_sound 5 86 1 cell_5_86_1
    | exact certificate_sound 5 86 2 cell_5_86_2
    | exact certificate_sound 5 86 3 cell_5_86_3
    | exact certificate_sound 5 86 4 cell_5_86_4
    | exact certificate_sound 5 86 5 cell_5_86_5
theorem cell_5_87_0 : CertificateAt 5 87 0 := by decide +kernel
theorem cell_5_87_1 : CertificateAt 5 87 1 := by decide +kernel
theorem cell_5_87_2 : CertificateAt 5 87 2 := by decide +kernel
theorem cell_5_87_3 : CertificateAt 5 87 3 := by decide +kernel
theorem cell_5_87_4 : CertificateAt 5 87 4 := by decide +kernel
theorem cell_5_87_5 : CertificateAt 5 87 5 := by decide +kernel
theorem row_5_87 : ThresholdAt 5 87 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 87 0 cell_5_87_0
    | exact certificate_sound 5 87 1 cell_5_87_1
    | exact certificate_sound 5 87 2 cell_5_87_2
    | exact certificate_sound 5 87 3 cell_5_87_3
    | exact certificate_sound 5 87 4 cell_5_87_4
    | exact certificate_sound 5 87 5 cell_5_87_5
theorem cell_5_88_0 : CertificateAt 5 88 0 := by decide +kernel
theorem cell_5_88_1 : CertificateAt 5 88 1 := by decide +kernel
theorem cell_5_88_2 : CertificateAt 5 88 2 := by decide +kernel
theorem cell_5_88_3 : CertificateAt 5 88 3 := by decide +kernel
theorem cell_5_88_4 : CertificateAt 5 88 4 := by decide +kernel
theorem cell_5_88_5 : CertificateAt 5 88 5 := by decide +kernel
theorem row_5_88 : ThresholdAt 5 88 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 88 0 cell_5_88_0
    | exact certificate_sound 5 88 1 cell_5_88_1
    | exact certificate_sound 5 88 2 cell_5_88_2
    | exact certificate_sound 5 88 3 cell_5_88_3
    | exact certificate_sound 5 88 4 cell_5_88_4
    | exact certificate_sound 5 88 5 cell_5_88_5
theorem cell_5_89_0 : CertificateAt 5 89 0 := by decide +kernel
theorem cell_5_89_1 : CertificateAt 5 89 1 := by decide +kernel
theorem cell_5_89_2 : CertificateAt 5 89 2 := by decide +kernel
theorem cell_5_89_3 : CertificateAt 5 89 3 := by decide +kernel
theorem cell_5_89_4 : CertificateAt 5 89 4 := by decide +kernel
theorem cell_5_89_5 : CertificateAt 5 89 5 := by decide +kernel
theorem row_5_89 : ThresholdAt 5 89 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 89 0 cell_5_89_0
    | exact certificate_sound 5 89 1 cell_5_89_1
    | exact certificate_sound 5 89 2 cell_5_89_2
    | exact certificate_sound 5 89 3 cell_5_89_3
    | exact certificate_sound 5 89 4 cell_5_89_4
    | exact certificate_sound 5 89 5 cell_5_89_5
theorem cell_5_90_0 : CertificateAt 5 90 0 := by decide +kernel
theorem cell_5_90_1 : CertificateAt 5 90 1 := by decide +kernel
theorem cell_5_90_2 : CertificateAt 5 90 2 := by decide +kernel
theorem cell_5_90_3 : CertificateAt 5 90 3 := by decide +kernel
theorem cell_5_90_4 : CertificateAt 5 90 4 := by decide +kernel
theorem cell_5_90_5 : CertificateAt 5 90 5 := by decide +kernel
theorem row_5_90 : ThresholdAt 5 90 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 90 0 cell_5_90_0
    | exact certificate_sound 5 90 1 cell_5_90_1
    | exact certificate_sound 5 90 2 cell_5_90_2
    | exact certificate_sound 5 90 3 cell_5_90_3
    | exact certificate_sound 5 90 4 cell_5_90_4
    | exact certificate_sound 5 90 5 cell_5_90_5
theorem cell_5_91_0 : CertificateAt 5 91 0 := by decide +kernel
theorem cell_5_91_1 : CertificateAt 5 91 1 := by decide +kernel
theorem cell_5_91_2 : CertificateAt 5 91 2 := by decide +kernel
theorem cell_5_91_3 : CertificateAt 5 91 3 := by decide +kernel
theorem cell_5_91_4 : CertificateAt 5 91 4 := by decide +kernel
theorem cell_5_91_5 : CertificateAt 5 91 5 := by decide +kernel
theorem row_5_91 : ThresholdAt 5 91 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 91 0 cell_5_91_0
    | exact certificate_sound 5 91 1 cell_5_91_1
    | exact certificate_sound 5 91 2 cell_5_91_2
    | exact certificate_sound 5 91 3 cell_5_91_3
    | exact certificate_sound 5 91 4 cell_5_91_4
    | exact certificate_sound 5 91 5 cell_5_91_5
theorem cell_5_92_0 : CertificateAt 5 92 0 := by decide +kernel
theorem cell_5_92_1 : CertificateAt 5 92 1 := by decide +kernel
theorem cell_5_92_2 : CertificateAt 5 92 2 := by decide +kernel
theorem cell_5_92_3 : CertificateAt 5 92 3 := by decide +kernel
theorem cell_5_92_4 : CertificateAt 5 92 4 := by decide +kernel
theorem cell_5_92_5 : CertificateAt 5 92 5 := by decide +kernel
theorem row_5_92 : ThresholdAt 5 92 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 92 0 cell_5_92_0
    | exact certificate_sound 5 92 1 cell_5_92_1
    | exact certificate_sound 5 92 2 cell_5_92_2
    | exact certificate_sound 5 92 3 cell_5_92_3
    | exact certificate_sound 5 92 4 cell_5_92_4
    | exact certificate_sound 5 92 5 cell_5_92_5
theorem cell_5_93_0 : CertificateAt 5 93 0 := by decide +kernel
theorem cell_5_93_1 : CertificateAt 5 93 1 := by decide +kernel
theorem cell_5_93_2 : CertificateAt 5 93 2 := by decide +kernel
theorem cell_5_93_3 : CertificateAt 5 93 3 := by decide +kernel
theorem cell_5_93_4 : CertificateAt 5 93 4 := by decide +kernel
theorem cell_5_93_5 : CertificateAt 5 93 5 := by decide +kernel
theorem row_5_93 : ThresholdAt 5 93 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 93 0 cell_5_93_0
    | exact certificate_sound 5 93 1 cell_5_93_1
    | exact certificate_sound 5 93 2 cell_5_93_2
    | exact certificate_sound 5 93 3 cell_5_93_3
    | exact certificate_sound 5 93 4 cell_5_93_4
    | exact certificate_sound 5 93 5 cell_5_93_5
theorem cell_5_94_0 : CertificateAt 5 94 0 := by decide +kernel
theorem cell_5_94_1 : CertificateAt 5 94 1 := by decide +kernel
theorem cell_5_94_2 : CertificateAt 5 94 2 := by decide +kernel
theorem cell_5_94_3 : CertificateAt 5 94 3 := by decide +kernel
theorem cell_5_94_4 : CertificateAt 5 94 4 := by decide +kernel
theorem cell_5_94_5 : CertificateAt 5 94 5 := by decide +kernel
theorem row_5_94 : ThresholdAt 5 94 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 94 0 cell_5_94_0
    | exact certificate_sound 5 94 1 cell_5_94_1
    | exact certificate_sound 5 94 2 cell_5_94_2
    | exact certificate_sound 5 94 3 cell_5_94_3
    | exact certificate_sound 5 94 4 cell_5_94_4
    | exact certificate_sound 5 94 5 cell_5_94_5
theorem cell_5_95_0 : CertificateAt 5 95 0 := by decide +kernel
theorem cell_5_95_1 : CertificateAt 5 95 1 := by decide +kernel
theorem cell_5_95_2 : CertificateAt 5 95 2 := by decide +kernel
theorem cell_5_95_3 : CertificateAt 5 95 3 := by decide +kernel
theorem cell_5_95_4 : CertificateAt 5 95 4 := by decide +kernel
theorem cell_5_95_5 : CertificateAt 5 95 5 := by decide +kernel
theorem row_5_95 : ThresholdAt 5 95 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 95 0 cell_5_95_0
    | exact certificate_sound 5 95 1 cell_5_95_1
    | exact certificate_sound 5 95 2 cell_5_95_2
    | exact certificate_sound 5 95 3 cell_5_95_3
    | exact certificate_sound 5 95 4 cell_5_95_4
    | exact certificate_sound 5 95 5 cell_5_95_5
theorem cell_5_96_0 : CertificateAt 5 96 0 := by decide +kernel
theorem cell_5_96_1 : CertificateAt 5 96 1 := by decide +kernel
theorem cell_5_96_2 : CertificateAt 5 96 2 := by decide +kernel
theorem cell_5_96_3 : CertificateAt 5 96 3 := by decide +kernel
theorem cell_5_96_4 : CertificateAt 5 96 4 := by decide +kernel
theorem cell_5_96_5 : CertificateAt 5 96 5 := by decide +kernel
theorem row_5_96 : ThresholdAt 5 96 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 96 0 cell_5_96_0
    | exact certificate_sound 5 96 1 cell_5_96_1
    | exact certificate_sound 5 96 2 cell_5_96_2
    | exact certificate_sound 5 96 3 cell_5_96_3
    | exact certificate_sound 5 96 4 cell_5_96_4
    | exact certificate_sound 5 96 5 cell_5_96_5
theorem cell_5_97_0 : CertificateAt 5 97 0 := by decide +kernel
theorem cell_5_97_1 : CertificateAt 5 97 1 := by decide +kernel
theorem cell_5_97_2 : CertificateAt 5 97 2 := by decide +kernel
theorem cell_5_97_3 : CertificateAt 5 97 3 := by decide +kernel
theorem cell_5_97_4 : CertificateAt 5 97 4 := by decide +kernel
theorem cell_5_97_5 : CertificateAt 5 97 5 := by decide +kernel
theorem row_5_97 : ThresholdAt 5 97 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 97 0 cell_5_97_0
    | exact certificate_sound 5 97 1 cell_5_97_1
    | exact certificate_sound 5 97 2 cell_5_97_2
    | exact certificate_sound 5 97 3 cell_5_97_3
    | exact certificate_sound 5 97 4 cell_5_97_4
    | exact certificate_sound 5 97 5 cell_5_97_5
theorem cell_5_98_0 : CertificateAt 5 98 0 := by decide +kernel
theorem cell_5_98_1 : CertificateAt 5 98 1 := by decide +kernel
theorem cell_5_98_2 : CertificateAt 5 98 2 := by decide +kernel
theorem cell_5_98_3 : CertificateAt 5 98 3 := by decide +kernel
theorem cell_5_98_4 : CertificateAt 5 98 4 := by decide +kernel
theorem cell_5_98_5 : CertificateAt 5 98 5 := by decide +kernel
theorem row_5_98 : ThresholdAt 5 98 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 98 0 cell_5_98_0
    | exact certificate_sound 5 98 1 cell_5_98_1
    | exact certificate_sound 5 98 2 cell_5_98_2
    | exact certificate_sound 5 98 3 cell_5_98_3
    | exact certificate_sound 5 98 4 cell_5_98_4
    | exact certificate_sound 5 98 5 cell_5_98_5
theorem cell_5_99_0 : CertificateAt 5 99 0 := by decide +kernel
theorem cell_5_99_1 : CertificateAt 5 99 1 := by decide +kernel
theorem cell_5_99_2 : CertificateAt 5 99 2 := by decide +kernel
theorem cell_5_99_3 : CertificateAt 5 99 3 := by decide +kernel
theorem cell_5_99_4 : CertificateAt 5 99 4 := by decide +kernel
theorem cell_5_99_5 : CertificateAt 5 99 5 := by decide +kernel
theorem row_5_99 : ThresholdAt 5 99 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 99 0 cell_5_99_0
    | exact certificate_sound 5 99 1 cell_5_99_1
    | exact certificate_sound 5 99 2 cell_5_99_2
    | exact certificate_sound 5 99 3 cell_5_99_3
    | exact certificate_sound 5 99 4 cell_5_99_4
    | exact certificate_sound 5 99 5 cell_5_99_5
theorem cell_5_100_0 : CertificateAt 5 100 0 := by decide +kernel
theorem cell_5_100_1 : CertificateAt 5 100 1 := by decide +kernel
theorem cell_5_100_2 : CertificateAt 5 100 2 := by decide +kernel
theorem cell_5_100_3 : CertificateAt 5 100 3 := by decide +kernel
theorem cell_5_100_4 : CertificateAt 5 100 4 := by decide +kernel
theorem cell_5_100_5 : CertificateAt 5 100 5 := by decide +kernel
theorem row_5_100 : ThresholdAt 5 100 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 100 0 cell_5_100_0
    | exact certificate_sound 5 100 1 cell_5_100_1
    | exact certificate_sound 5 100 2 cell_5_100_2
    | exact certificate_sound 5 100 3 cell_5_100_3
    | exact certificate_sound 5 100 4 cell_5_100_4
    | exact certificate_sound 5 100 5 cell_5_100_5
theorem cell_5_101_0 : CertificateAt 5 101 0 := by decide +kernel
theorem cell_5_101_1 : CertificateAt 5 101 1 := by decide +kernel
theorem cell_5_101_2 : CertificateAt 5 101 2 := by decide +kernel
theorem cell_5_101_3 : CertificateAt 5 101 3 := by decide +kernel
theorem cell_5_101_4 : CertificateAt 5 101 4 := by decide +kernel
theorem cell_5_101_5 : CertificateAt 5 101 5 := by decide +kernel
theorem row_5_101 : ThresholdAt 5 101 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 101 0 cell_5_101_0
    | exact certificate_sound 5 101 1 cell_5_101_1
    | exact certificate_sound 5 101 2 cell_5_101_2
    | exact certificate_sound 5 101 3 cell_5_101_3
    | exact certificate_sound 5 101 4 cell_5_101_4
    | exact certificate_sound 5 101 5 cell_5_101_5
theorem cell_5_102_0 : CertificateAt 5 102 0 := by decide +kernel
theorem cell_5_102_1 : CertificateAt 5 102 1 := by decide +kernel
theorem cell_5_102_2 : CertificateAt 5 102 2 := by decide +kernel
theorem cell_5_102_3 : CertificateAt 5 102 3 := by decide +kernel
theorem cell_5_102_4 : CertificateAt 5 102 4 := by decide +kernel
theorem cell_5_102_5 : CertificateAt 5 102 5 := by decide +kernel
theorem row_5_102 : ThresholdAt 5 102 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 102 0 cell_5_102_0
    | exact certificate_sound 5 102 1 cell_5_102_1
    | exact certificate_sound 5 102 2 cell_5_102_2
    | exact certificate_sound 5 102 3 cell_5_102_3
    | exact certificate_sound 5 102 4 cell_5_102_4
    | exact certificate_sound 5 102 5 cell_5_102_5
theorem cell_5_103_0 : CertificateAt 5 103 0 := by decide +kernel
theorem cell_5_103_1 : CertificateAt 5 103 1 := by decide +kernel
theorem cell_5_103_2 : CertificateAt 5 103 2 := by decide +kernel
theorem cell_5_103_3 : CertificateAt 5 103 3 := by decide +kernel
theorem cell_5_103_4 : CertificateAt 5 103 4 := by decide +kernel
theorem cell_5_103_5 : CertificateAt 5 103 5 := by decide +kernel
theorem row_5_103 : ThresholdAt 5 103 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 103 0 cell_5_103_0
    | exact certificate_sound 5 103 1 cell_5_103_1
    | exact certificate_sound 5 103 2 cell_5_103_2
    | exact certificate_sound 5 103 3 cell_5_103_3
    | exact certificate_sound 5 103 4 cell_5_103_4
    | exact certificate_sound 5 103 5 cell_5_103_5
theorem cell_5_104_0 : CertificateAt 5 104 0 := by decide +kernel
theorem cell_5_104_1 : CertificateAt 5 104 1 := by decide +kernel
theorem cell_5_104_2 : CertificateAt 5 104 2 := by decide +kernel
theorem cell_5_104_3 : CertificateAt 5 104 3 := by decide +kernel
theorem cell_5_104_4 : CertificateAt 5 104 4 := by decide +kernel
theorem cell_5_104_5 : CertificateAt 5 104 5 := by decide +kernel
theorem row_5_104 : ThresholdAt 5 104 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 104 0 cell_5_104_0
    | exact certificate_sound 5 104 1 cell_5_104_1
    | exact certificate_sound 5 104 2 cell_5_104_2
    | exact certificate_sound 5 104 3 cell_5_104_3
    | exact certificate_sound 5 104 4 cell_5_104_4
    | exact certificate_sound 5 104 5 cell_5_104_5
theorem cell_5_105_0 : CertificateAt 5 105 0 := by decide +kernel
theorem cell_5_105_1 : CertificateAt 5 105 1 := by decide +kernel
theorem cell_5_105_2 : CertificateAt 5 105 2 := by decide +kernel
theorem cell_5_105_3 : CertificateAt 5 105 3 := by decide +kernel
theorem cell_5_105_4 : CertificateAt 5 105 4 := by decide +kernel
theorem cell_5_105_5 : CertificateAt 5 105 5 := by decide +kernel
theorem row_5_105 : ThresholdAt 5 105 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 105 0 cell_5_105_0
    | exact certificate_sound 5 105 1 cell_5_105_1
    | exact certificate_sound 5 105 2 cell_5_105_2
    | exact certificate_sound 5 105 3 cell_5_105_3
    | exact certificate_sound 5 105 4 cell_5_105_4
    | exact certificate_sound 5 105 5 cell_5_105_5
theorem cell_5_106_0 : CertificateAt 5 106 0 := by decide +kernel
theorem cell_5_106_1 : CertificateAt 5 106 1 := by decide +kernel
theorem cell_5_106_2 : CertificateAt 5 106 2 := by decide +kernel
theorem cell_5_106_3 : CertificateAt 5 106 3 := by decide +kernel
theorem cell_5_106_4 : CertificateAt 5 106 4 := by decide +kernel
theorem cell_5_106_5 : CertificateAt 5 106 5 := by decide +kernel
theorem row_5_106 : ThresholdAt 5 106 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 106 0 cell_5_106_0
    | exact certificate_sound 5 106 1 cell_5_106_1
    | exact certificate_sound 5 106 2 cell_5_106_2
    | exact certificate_sound 5 106 3 cell_5_106_3
    | exact certificate_sound 5 106 4 cell_5_106_4
    | exact certificate_sound 5 106 5 cell_5_106_5
theorem cell_5_107_0 : CertificateAt 5 107 0 := by decide +kernel
theorem cell_5_107_1 : CertificateAt 5 107 1 := by decide +kernel
theorem cell_5_107_2 : CertificateAt 5 107 2 := by decide +kernel
theorem cell_5_107_3 : CertificateAt 5 107 3 := by decide +kernel
theorem cell_5_107_4 : CertificateAt 5 107 4 := by decide +kernel
theorem cell_5_107_5 : CertificateAt 5 107 5 := by decide +kernel
theorem row_5_107 : ThresholdAt 5 107 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 107 0 cell_5_107_0
    | exact certificate_sound 5 107 1 cell_5_107_1
    | exact certificate_sound 5 107 2 cell_5_107_2
    | exact certificate_sound 5 107 3 cell_5_107_3
    | exact certificate_sound 5 107 4 cell_5_107_4
    | exact certificate_sound 5 107 5 cell_5_107_5
theorem cell_5_108_0 : CertificateAt 5 108 0 := by decide +kernel
theorem cell_5_108_1 : CertificateAt 5 108 1 := by decide +kernel
theorem cell_5_108_2 : CertificateAt 5 108 2 := by decide +kernel
theorem cell_5_108_3 : CertificateAt 5 108 3 := by decide +kernel
theorem cell_5_108_4 : CertificateAt 5 108 4 := by decide +kernel
theorem cell_5_108_5 : CertificateAt 5 108 5 := by decide +kernel
theorem row_5_108 : ThresholdAt 5 108 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 108 0 cell_5_108_0
    | exact certificate_sound 5 108 1 cell_5_108_1
    | exact certificate_sound 5 108 2 cell_5_108_2
    | exact certificate_sound 5 108 3 cell_5_108_3
    | exact certificate_sound 5 108 4 cell_5_108_4
    | exact certificate_sound 5 108 5 cell_5_108_5
theorem cell_5_109_0 : CertificateAt 5 109 0 := by decide +kernel
theorem cell_5_109_1 : CertificateAt 5 109 1 := by decide +kernel
theorem cell_5_109_2 : CertificateAt 5 109 2 := by decide +kernel
theorem cell_5_109_3 : CertificateAt 5 109 3 := by decide +kernel
theorem cell_5_109_4 : CertificateAt 5 109 4 := by decide +kernel
theorem cell_5_109_5 : CertificateAt 5 109 5 := by decide +kernel
theorem row_5_109 : ThresholdAt 5 109 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 109 0 cell_5_109_0
    | exact certificate_sound 5 109 1 cell_5_109_1
    | exact certificate_sound 5 109 2 cell_5_109_2
    | exact certificate_sound 5 109 3 cell_5_109_3
    | exact certificate_sound 5 109 4 cell_5_109_4
    | exact certificate_sound 5 109 5 cell_5_109_5
theorem cell_5_110_0 : CertificateAt 5 110 0 := by decide +kernel
theorem cell_5_110_1 : CertificateAt 5 110 1 := by decide +kernel
theorem cell_5_110_2 : CertificateAt 5 110 2 := by decide +kernel
theorem cell_5_110_3 : CertificateAt 5 110 3 := by decide +kernel
theorem cell_5_110_4 : CertificateAt 5 110 4 := by decide +kernel
theorem cell_5_110_5 : CertificateAt 5 110 5 := by decide +kernel
theorem row_5_110 : ThresholdAt 5 110 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 110 0 cell_5_110_0
    | exact certificate_sound 5 110 1 cell_5_110_1
    | exact certificate_sound 5 110 2 cell_5_110_2
    | exact certificate_sound 5 110 3 cell_5_110_3
    | exact certificate_sound 5 110 4 cell_5_110_4
    | exact certificate_sound 5 110 5 cell_5_110_5
theorem cell_5_111_0 : CertificateAt 5 111 0 := by decide +kernel
theorem cell_5_111_1 : CertificateAt 5 111 1 := by decide +kernel
theorem cell_5_111_2 : CertificateAt 5 111 2 := by decide +kernel
theorem cell_5_111_3 : CertificateAt 5 111 3 := by decide +kernel
theorem cell_5_111_4 : CertificateAt 5 111 4 := by decide +kernel
theorem cell_5_111_5 : CertificateAt 5 111 5 := by decide +kernel
theorem row_5_111 : ThresholdAt 5 111 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 111 0 cell_5_111_0
    | exact certificate_sound 5 111 1 cell_5_111_1
    | exact certificate_sound 5 111 2 cell_5_111_2
    | exact certificate_sound 5 111 3 cell_5_111_3
    | exact certificate_sound 5 111 4 cell_5_111_4
    | exact certificate_sound 5 111 5 cell_5_111_5
theorem cell_5_112_0 : CertificateAt 5 112 0 := by decide +kernel
theorem cell_5_112_1 : CertificateAt 5 112 1 := by decide +kernel
theorem cell_5_112_2 : CertificateAt 5 112 2 := by decide +kernel
theorem cell_5_112_3 : CertificateAt 5 112 3 := by decide +kernel
theorem cell_5_112_4 : CertificateAt 5 112 4 := by decide +kernel
theorem cell_5_112_5 : CertificateAt 5 112 5 := by decide +kernel
theorem row_5_112 : ThresholdAt 5 112 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 112 0 cell_5_112_0
    | exact certificate_sound 5 112 1 cell_5_112_1
    | exact certificate_sound 5 112 2 cell_5_112_2
    | exact certificate_sound 5 112 3 cell_5_112_3
    | exact certificate_sound 5 112 4 cell_5_112_4
    | exact certificate_sound 5 112 5 cell_5_112_5
theorem cell_5_113_0 : CertificateAt 5 113 0 := by decide +kernel
theorem cell_5_113_1 : CertificateAt 5 113 1 := by decide +kernel
theorem cell_5_113_2 : CertificateAt 5 113 2 := by decide +kernel
theorem cell_5_113_3 : CertificateAt 5 113 3 := by decide +kernel
theorem cell_5_113_4 : CertificateAt 5 113 4 := by decide +kernel
theorem cell_5_113_5 : CertificateAt 5 113 5 := by decide +kernel
theorem row_5_113 : ThresholdAt 5 113 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 113 0 cell_5_113_0
    | exact certificate_sound 5 113 1 cell_5_113_1
    | exact certificate_sound 5 113 2 cell_5_113_2
    | exact certificate_sound 5 113 3 cell_5_113_3
    | exact certificate_sound 5 113 4 cell_5_113_4
    | exact certificate_sound 5 113 5 cell_5_113_5
theorem cell_5_114_0 : CertificateAt 5 114 0 := by decide +kernel
theorem cell_5_114_1 : CertificateAt 5 114 1 := by decide +kernel
theorem cell_5_114_2 : CertificateAt 5 114 2 := by decide +kernel
theorem cell_5_114_3 : CertificateAt 5 114 3 := by decide +kernel
theorem cell_5_114_4 : CertificateAt 5 114 4 := by decide +kernel
theorem cell_5_114_5 : CertificateAt 5 114 5 := by decide +kernel
theorem row_5_114 : ThresholdAt 5 114 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 114 0 cell_5_114_0
    | exact certificate_sound 5 114 1 cell_5_114_1
    | exact certificate_sound 5 114 2 cell_5_114_2
    | exact certificate_sound 5 114 3 cell_5_114_3
    | exact certificate_sound 5 114 4 cell_5_114_4
    | exact certificate_sound 5 114 5 cell_5_114_5
theorem cell_5_115_0 : CertificateAt 5 115 0 := by decide +kernel
theorem cell_5_115_1 : CertificateAt 5 115 1 := by decide +kernel
theorem cell_5_115_2 : CertificateAt 5 115 2 := by decide +kernel
theorem cell_5_115_3 : CertificateAt 5 115 3 := by decide +kernel
theorem cell_5_115_4 : CertificateAt 5 115 4 := by decide +kernel
theorem cell_5_115_5 : CertificateAt 5 115 5 := by decide +kernel
theorem row_5_115 : ThresholdAt 5 115 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 115 0 cell_5_115_0
    | exact certificate_sound 5 115 1 cell_5_115_1
    | exact certificate_sound 5 115 2 cell_5_115_2
    | exact certificate_sound 5 115 3 cell_5_115_3
    | exact certificate_sound 5 115 4 cell_5_115_4
    | exact certificate_sound 5 115 5 cell_5_115_5
theorem cell_5_116_0 : CertificateAt 5 116 0 := by decide +kernel
theorem cell_5_116_1 : CertificateAt 5 116 1 := by decide +kernel
theorem cell_5_116_2 : CertificateAt 5 116 2 := by decide +kernel
theorem cell_5_116_3 : CertificateAt 5 116 3 := by decide +kernel
theorem cell_5_116_4 : CertificateAt 5 116 4 := by decide +kernel
theorem cell_5_116_5 : CertificateAt 5 116 5 := by decide +kernel
theorem row_5_116 : ThresholdAt 5 116 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 116 0 cell_5_116_0
    | exact certificate_sound 5 116 1 cell_5_116_1
    | exact certificate_sound 5 116 2 cell_5_116_2
    | exact certificate_sound 5 116 3 cell_5_116_3
    | exact certificate_sound 5 116 4 cell_5_116_4
    | exact certificate_sound 5 116 5 cell_5_116_5
theorem cell_5_117_0 : CertificateAt 5 117 0 := by decide +kernel
theorem cell_5_117_1 : CertificateAt 5 117 1 := by decide +kernel
theorem cell_5_117_2 : CertificateAt 5 117 2 := by decide +kernel
theorem cell_5_117_3 : CertificateAt 5 117 3 := by decide +kernel
theorem cell_5_117_4 : CertificateAt 5 117 4 := by decide +kernel
theorem cell_5_117_5 : CertificateAt 5 117 5 := by decide +kernel
theorem row_5_117 : ThresholdAt 5 117 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 117 0 cell_5_117_0
    | exact certificate_sound 5 117 1 cell_5_117_1
    | exact certificate_sound 5 117 2 cell_5_117_2
    | exact certificate_sound 5 117 3 cell_5_117_3
    | exact certificate_sound 5 117 4 cell_5_117_4
    | exact certificate_sound 5 117 5 cell_5_117_5
theorem cell_5_118_0 : CertificateAt 5 118 0 := by decide +kernel
theorem cell_5_118_1 : CertificateAt 5 118 1 := by decide +kernel
theorem cell_5_118_2 : CertificateAt 5 118 2 := by decide +kernel
theorem cell_5_118_3 : CertificateAt 5 118 3 := by decide +kernel
theorem cell_5_118_4 : CertificateAt 5 118 4 := by decide +kernel
theorem cell_5_118_5 : CertificateAt 5 118 5 := by decide +kernel
theorem row_5_118 : ThresholdAt 5 118 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 118 0 cell_5_118_0
    | exact certificate_sound 5 118 1 cell_5_118_1
    | exact certificate_sound 5 118 2 cell_5_118_2
    | exact certificate_sound 5 118 3 cell_5_118_3
    | exact certificate_sound 5 118 4 cell_5_118_4
    | exact certificate_sound 5 118 5 cell_5_118_5
theorem cell_5_119_0 : CertificateAt 5 119 0 := by decide +kernel
theorem cell_5_119_1 : CertificateAt 5 119 1 := by decide +kernel
theorem cell_5_119_2 : CertificateAt 5 119 2 := by decide +kernel
theorem cell_5_119_3 : CertificateAt 5 119 3 := by decide +kernel
theorem cell_5_119_4 : CertificateAt 5 119 4 := by decide +kernel
theorem cell_5_119_5 : CertificateAt 5 119 5 := by decide +kernel
theorem row_5_119 : ThresholdAt 5 119 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 119 0 cell_5_119_0
    | exact certificate_sound 5 119 1 cell_5_119_1
    | exact certificate_sound 5 119 2 cell_5_119_2
    | exact certificate_sound 5 119 3 cell_5_119_3
    | exact certificate_sound 5 119 4 cell_5_119_4
    | exact certificate_sound 5 119 5 cell_5_119_5
theorem cell_5_120_0 : CertificateAt 5 120 0 := by decide +kernel
theorem cell_5_120_1 : CertificateAt 5 120 1 := by decide +kernel
theorem cell_5_120_2 : CertificateAt 5 120 2 := by decide +kernel
theorem cell_5_120_3 : CertificateAt 5 120 3 := by decide +kernel
theorem cell_5_120_4 : CertificateAt 5 120 4 := by decide +kernel
theorem cell_5_120_5 : CertificateAt 5 120 5 := by decide +kernel
theorem row_5_120 : ThresholdAt 5 120 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 120 0 cell_5_120_0
    | exact certificate_sound 5 120 1 cell_5_120_1
    | exact certificate_sound 5 120 2 cell_5_120_2
    | exact certificate_sound 5 120 3 cell_5_120_3
    | exact certificate_sound 5 120 4 cell_5_120_4
    | exact certificate_sound 5 120 5 cell_5_120_5
theorem cell_5_121_0 : CertificateAt 5 121 0 := by decide +kernel
theorem cell_5_121_1 : CertificateAt 5 121 1 := by decide +kernel
theorem cell_5_121_2 : CertificateAt 5 121 2 := by decide +kernel
theorem cell_5_121_3 : CertificateAt 5 121 3 := by decide +kernel
theorem cell_5_121_4 : CertificateAt 5 121 4 := by decide +kernel
theorem cell_5_121_5 : CertificateAt 5 121 5 := by decide +kernel
theorem row_5_121 : ThresholdAt 5 121 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 121 0 cell_5_121_0
    | exact certificate_sound 5 121 1 cell_5_121_1
    | exact certificate_sound 5 121 2 cell_5_121_2
    | exact certificate_sound 5 121 3 cell_5_121_3
    | exact certificate_sound 5 121 4 cell_5_121_4
    | exact certificate_sound 5 121 5 cell_5_121_5
theorem cell_5_122_0 : CertificateAt 5 122 0 := by decide +kernel
theorem cell_5_122_1 : CertificateAt 5 122 1 := by decide +kernel
theorem cell_5_122_2 : CertificateAt 5 122 2 := by decide +kernel
theorem cell_5_122_3 : CertificateAt 5 122 3 := by decide +kernel
theorem cell_5_122_4 : CertificateAt 5 122 4 := by decide +kernel
theorem cell_5_122_5 : CertificateAt 5 122 5 := by decide +kernel
theorem row_5_122 : ThresholdAt 5 122 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 122 0 cell_5_122_0
    | exact certificate_sound 5 122 1 cell_5_122_1
    | exact certificate_sound 5 122 2 cell_5_122_2
    | exact certificate_sound 5 122 3 cell_5_122_3
    | exact certificate_sound 5 122 4 cell_5_122_4
    | exact certificate_sound 5 122 5 cell_5_122_5
theorem cell_5_123_0 : CertificateAt 5 123 0 := by decide +kernel
theorem cell_5_123_1 : CertificateAt 5 123 1 := by decide +kernel
theorem cell_5_123_2 : CertificateAt 5 123 2 := by decide +kernel
theorem cell_5_123_3 : CertificateAt 5 123 3 := by decide +kernel
theorem cell_5_123_4 : CertificateAt 5 123 4 := by decide +kernel
theorem cell_5_123_5 : CertificateAt 5 123 5 := by decide +kernel
theorem row_5_123 : ThresholdAt 5 123 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 123 0 cell_5_123_0
    | exact certificate_sound 5 123 1 cell_5_123_1
    | exact certificate_sound 5 123 2 cell_5_123_2
    | exact certificate_sound 5 123 3 cell_5_123_3
    | exact certificate_sound 5 123 4 cell_5_123_4
    | exact certificate_sound 5 123 5 cell_5_123_5
theorem cell_5_124_0 : CertificateAt 5 124 0 := by decide +kernel
theorem cell_5_124_1 : CertificateAt 5 124 1 := by decide +kernel
theorem cell_5_124_2 : CertificateAt 5 124 2 := by decide +kernel
theorem cell_5_124_3 : CertificateAt 5 124 3 := by decide +kernel
theorem cell_5_124_4 : CertificateAt 5 124 4 := by decide +kernel
theorem cell_5_124_5 : CertificateAt 5 124 5 := by decide +kernel
theorem row_5_124 : ThresholdAt 5 124 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 124 0 cell_5_124_0
    | exact certificate_sound 5 124 1 cell_5_124_1
    | exact certificate_sound 5 124 2 cell_5_124_2
    | exact certificate_sound 5 124 3 cell_5_124_3
    | exact certificate_sound 5 124 4 cell_5_124_4
    | exact certificate_sound 5 124 5 cell_5_124_5
theorem cell_5_125_0 : CertificateAt 5 125 0 := by decide +kernel
theorem cell_5_125_1 : CertificateAt 5 125 1 := by decide +kernel
theorem cell_5_125_2 : CertificateAt 5 125 2 := by decide +kernel
theorem cell_5_125_3 : CertificateAt 5 125 3 := by decide +kernel
theorem cell_5_125_4 : CertificateAt 5 125 4 := by decide +kernel
theorem cell_5_125_5 : CertificateAt 5 125 5 := by decide +kernel
theorem row_5_125 : ThresholdAt 5 125 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 125 0 cell_5_125_0
    | exact certificate_sound 5 125 1 cell_5_125_1
    | exact certificate_sound 5 125 2 cell_5_125_2
    | exact certificate_sound 5 125 3 cell_5_125_3
    | exact certificate_sound 5 125 4 cell_5_125_4
    | exact certificate_sound 5 125 5 cell_5_125_5
theorem cell_5_126_0 : CertificateAt 5 126 0 := by decide +kernel
theorem cell_5_126_1 : CertificateAt 5 126 1 := by decide +kernel
theorem cell_5_126_2 : CertificateAt 5 126 2 := by decide +kernel
theorem cell_5_126_3 : CertificateAt 5 126 3 := by decide +kernel
theorem cell_5_126_4 : CertificateAt 5 126 4 := by decide +kernel
theorem cell_5_126_5 : CertificateAt 5 126 5 := by decide +kernel
theorem row_5_126 : ThresholdAt 5 126 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 126 0 cell_5_126_0
    | exact certificate_sound 5 126 1 cell_5_126_1
    | exact certificate_sound 5 126 2 cell_5_126_2
    | exact certificate_sound 5 126 3 cell_5_126_3
    | exact certificate_sound 5 126 4 cell_5_126_4
    | exact certificate_sound 5 126 5 cell_5_126_5
theorem cell_5_127_0 : CertificateAt 5 127 0 := by decide +kernel
theorem cell_5_127_1 : CertificateAt 5 127 1 := by decide +kernel
theorem cell_5_127_2 : CertificateAt 5 127 2 := by decide +kernel
theorem cell_5_127_3 : CertificateAt 5 127 3 := by decide +kernel
theorem cell_5_127_4 : CertificateAt 5 127 4 := by decide +kernel
theorem cell_5_127_5 : CertificateAt 5 127 5 := by decide +kernel
theorem row_5_127 : ThresholdAt 5 127 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 127 0 cell_5_127_0
    | exact certificate_sound 5 127 1 cell_5_127_1
    | exact certificate_sound 5 127 2 cell_5_127_2
    | exact certificate_sound 5 127 3 cell_5_127_3
    | exact certificate_sound 5 127 4 cell_5_127_4
    | exact certificate_sound 5 127 5 cell_5_127_5
theorem cell_5_128_0 : CertificateAt 5 128 0 := by decide +kernel
theorem cell_5_128_1 : CertificateAt 5 128 1 := by decide +kernel
theorem cell_5_128_2 : CertificateAt 5 128 2 := by decide +kernel
theorem cell_5_128_3 : CertificateAt 5 128 3 := by decide +kernel
theorem cell_5_128_4 : CertificateAt 5 128 4 := by decide +kernel
theorem cell_5_128_5 : CertificateAt 5 128 5 := by decide +kernel
theorem row_5_128 : ThresholdAt 5 128 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 128 0 cell_5_128_0
    | exact certificate_sound 5 128 1 cell_5_128_1
    | exact certificate_sound 5 128 2 cell_5_128_2
    | exact certificate_sound 5 128 3 cell_5_128_3
    | exact certificate_sound 5 128 4 cell_5_128_4
    | exact certificate_sound 5 128 5 cell_5_128_5
theorem cell_5_129_0 : CertificateAt 5 129 0 := by decide +kernel
theorem cell_5_129_1 : CertificateAt 5 129 1 := by decide +kernel
theorem cell_5_129_2 : CertificateAt 5 129 2 := by decide +kernel
theorem cell_5_129_3 : CertificateAt 5 129 3 := by decide +kernel
theorem cell_5_129_4 : CertificateAt 5 129 4 := by decide +kernel
theorem cell_5_129_5 : CertificateAt 5 129 5 := by decide +kernel
theorem row_5_129 : ThresholdAt 5 129 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 129 0 cell_5_129_0
    | exact certificate_sound 5 129 1 cell_5_129_1
    | exact certificate_sound 5 129 2 cell_5_129_2
    | exact certificate_sound 5 129 3 cell_5_129_3
    | exact certificate_sound 5 129 4 cell_5_129_4
    | exact certificate_sound 5 129 5 cell_5_129_5
theorem cell_5_130_0 : CertificateAt 5 130 0 := by decide +kernel
theorem cell_5_130_1 : CertificateAt 5 130 1 := by decide +kernel
theorem cell_5_130_2 : CertificateAt 5 130 2 := by decide +kernel
theorem cell_5_130_3 : CertificateAt 5 130 3 := by decide +kernel
theorem cell_5_130_4 : CertificateAt 5 130 4 := by decide +kernel
theorem cell_5_130_5 : CertificateAt 5 130 5 := by decide +kernel
theorem row_5_130 : ThresholdAt 5 130 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 130 0 cell_5_130_0
    | exact certificate_sound 5 130 1 cell_5_130_1
    | exact certificate_sound 5 130 2 cell_5_130_2
    | exact certificate_sound 5 130 3 cell_5_130_3
    | exact certificate_sound 5 130 4 cell_5_130_4
    | exact certificate_sound 5 130 5 cell_5_130_5
theorem cell_5_131_0 : CertificateAt 5 131 0 := by decide +kernel
theorem cell_5_131_1 : CertificateAt 5 131 1 := by decide +kernel
theorem cell_5_131_2 : CertificateAt 5 131 2 := by decide +kernel
theorem cell_5_131_3 : CertificateAt 5 131 3 := by decide +kernel
theorem cell_5_131_4 : CertificateAt 5 131 4 := by decide +kernel
theorem cell_5_131_5 : CertificateAt 5 131 5 := by decide +kernel
theorem row_5_131 : ThresholdAt 5 131 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 131 0 cell_5_131_0
    | exact certificate_sound 5 131 1 cell_5_131_1
    | exact certificate_sound 5 131 2 cell_5_131_2
    | exact certificate_sound 5 131 3 cell_5_131_3
    | exact certificate_sound 5 131 4 cell_5_131_4
    | exact certificate_sound 5 131 5 cell_5_131_5
theorem cell_5_132_0 : CertificateAt 5 132 0 := by decide +kernel
theorem cell_5_132_1 : CertificateAt 5 132 1 := by decide +kernel
theorem cell_5_132_2 : CertificateAt 5 132 2 := by decide +kernel
theorem cell_5_132_3 : CertificateAt 5 132 3 := by decide +kernel
theorem cell_5_132_4 : CertificateAt 5 132 4 := by decide +kernel
theorem cell_5_132_5 : CertificateAt 5 132 5 := by decide +kernel
theorem row_5_132 : ThresholdAt 5 132 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 132 0 cell_5_132_0
    | exact certificate_sound 5 132 1 cell_5_132_1
    | exact certificate_sound 5 132 2 cell_5_132_2
    | exact certificate_sound 5 132 3 cell_5_132_3
    | exact certificate_sound 5 132 4 cell_5_132_4
    | exact certificate_sound 5 132 5 cell_5_132_5
theorem cell_5_133_0 : CertificateAt 5 133 0 := by decide +kernel
theorem cell_5_133_1 : CertificateAt 5 133 1 := by decide +kernel
theorem cell_5_133_2 : CertificateAt 5 133 2 := by decide +kernel
theorem cell_5_133_3 : CertificateAt 5 133 3 := by decide +kernel
theorem cell_5_133_4 : CertificateAt 5 133 4 := by decide +kernel
theorem cell_5_133_5 : CertificateAt 5 133 5 := by decide +kernel
theorem row_5_133 : ThresholdAt 5 133 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 133 0 cell_5_133_0
    | exact certificate_sound 5 133 1 cell_5_133_1
    | exact certificate_sound 5 133 2 cell_5_133_2
    | exact certificate_sound 5 133 3 cell_5_133_3
    | exact certificate_sound 5 133 4 cell_5_133_4
    | exact certificate_sound 5 133 5 cell_5_133_5
theorem cell_5_134_0 : CertificateAt 5 134 0 := by decide +kernel
theorem cell_5_134_1 : CertificateAt 5 134 1 := by decide +kernel
theorem cell_5_134_2 : CertificateAt 5 134 2 := by decide +kernel
theorem cell_5_134_3 : CertificateAt 5 134 3 := by decide +kernel
theorem cell_5_134_4 : CertificateAt 5 134 4 := by decide +kernel
theorem cell_5_134_5 : CertificateAt 5 134 5 := by decide +kernel
theorem row_5_134 : ThresholdAt 5 134 := by
  intro j hj
  have hj6 : j < 6 := List.mem_range.mp hj
  interval_cases j <;> first
    | exact certificate_sound 5 134 0 cell_5_134_0
    | exact certificate_sound 5 134 1 cell_5_134_1
    | exact certificate_sound 5 134 2 cell_5_134_2
    | exact certificate_sound 5 134 3 cell_5_134_3
    | exact certificate_sound 5 134 4 cell_5_134_4
    | exact certificate_sound 5 134 5 cell_5_134_5
theorem checkedR5 : ∀ V ∈ List.range 135, ThresholdAt 5 V := by
  intro V hV
  have hv : V < 135 := List.mem_range.mp hV
  by_cases h0_135 : V < 67
  · by_cases h0_67 : V < 33
    · by_cases h0_33 : V < 16
      · by_cases h0_16 : V < 8
        · by_cases h0_8 : V < 4
          · by_cases h0_4 : V < 2
            · by_cases h0_2 : V < 1
              · have he : V = 0 := by omega
                subst V
                exact row_5_0
              · have he : V = 1 := by omega
                subst V
                exact row_5_1
            · by_cases h2_4 : V < 3
              · have he : V = 2 := by omega
                subst V
                exact row_5_2
              · have he : V = 3 := by omega
                subst V
                exact row_5_3
          · by_cases h4_8 : V < 6
            · by_cases h4_6 : V < 5
              · have he : V = 4 := by omega
                subst V
                exact row_5_4
              · have he : V = 5 := by omega
                subst V
                exact row_5_5
            · by_cases h6_8 : V < 7
              · have he : V = 6 := by omega
                subst V
                exact row_5_6
              · have he : V = 7 := by omega
                subst V
                exact row_5_7
        · by_cases h8_16 : V < 12
          · by_cases h8_12 : V < 10
            · by_cases h8_10 : V < 9
              · have he : V = 8 := by omega
                subst V
                exact row_5_8
              · have he : V = 9 := by omega
                subst V
                exact row_5_9
            · by_cases h10_12 : V < 11
              · have he : V = 10 := by omega
                subst V
                exact row_5_10
              · have he : V = 11 := by omega
                subst V
                exact row_5_11
          · by_cases h12_16 : V < 14
            · by_cases h12_14 : V < 13
              · have he : V = 12 := by omega
                subst V
                exact row_5_12
              · have he : V = 13 := by omega
                subst V
                exact row_5_13
            · by_cases h14_16 : V < 15
              · have he : V = 14 := by omega
                subst V
                exact row_5_14
              · have he : V = 15 := by omega
                subst V
                exact row_5_15
      · by_cases h16_33 : V < 24
        · by_cases h16_24 : V < 20
          · by_cases h16_20 : V < 18
            · by_cases h16_18 : V < 17
              · have he : V = 16 := by omega
                subst V
                exact row_5_16
              · have he : V = 17 := by omega
                subst V
                exact row_5_17
            · by_cases h18_20 : V < 19
              · have he : V = 18 := by omega
                subst V
                exact row_5_18
              · have he : V = 19 := by omega
                subst V
                exact row_5_19
          · by_cases h20_24 : V < 22
            · by_cases h20_22 : V < 21
              · have he : V = 20 := by omega
                subst V
                exact row_5_20
              · have he : V = 21 := by omega
                subst V
                exact row_5_21
            · by_cases h22_24 : V < 23
              · have he : V = 22 := by omega
                subst V
                exact row_5_22
              · have he : V = 23 := by omega
                subst V
                exact row_5_23
        · by_cases h24_33 : V < 28
          · by_cases h24_28 : V < 26
            · by_cases h24_26 : V < 25
              · have he : V = 24 := by omega
                subst V
                exact row_5_24
              · have he : V = 25 := by omega
                subst V
                exact row_5_25
            · by_cases h26_28 : V < 27
              · have he : V = 26 := by omega
                subst V
                exact row_5_26
              · have he : V = 27 := by omega
                subst V
                exact row_5_27
          · by_cases h28_33 : V < 30
            · by_cases h28_30 : V < 29
              · have he : V = 28 := by omega
                subst V
                exact row_5_28
              · have he : V = 29 := by omega
                subst V
                exact row_5_29
            · by_cases h30_33 : V < 31
              · have he : V = 30 := by omega
                subst V
                exact row_5_30
              · by_cases h31_33 : V < 32
                · have he : V = 31 := by omega
                  subst V
                  exact row_5_31
                · have he : V = 32 := by omega
                  subst V
                  exact row_5_32
    · by_cases h33_67 : V < 50
      · by_cases h33_50 : V < 41
        · by_cases h33_41 : V < 37
          · by_cases h33_37 : V < 35
            · by_cases h33_35 : V < 34
              · have he : V = 33 := by omega
                subst V
                exact row_5_33
              · have he : V = 34 := by omega
                subst V
                exact row_5_34
            · by_cases h35_37 : V < 36
              · have he : V = 35 := by omega
                subst V
                exact row_5_35
              · have he : V = 36 := by omega
                subst V
                exact row_5_36
          · by_cases h37_41 : V < 39
            · by_cases h37_39 : V < 38
              · have he : V = 37 := by omega
                subst V
                exact row_5_37
              · have he : V = 38 := by omega
                subst V
                exact row_5_38
            · by_cases h39_41 : V < 40
              · have he : V = 39 := by omega
                subst V
                exact row_5_39
              · have he : V = 40 := by omega
                subst V
                exact row_5_40
        · by_cases h41_50 : V < 45
          · by_cases h41_45 : V < 43
            · by_cases h41_43 : V < 42
              · have he : V = 41 := by omega
                subst V
                exact row_5_41
              · have he : V = 42 := by omega
                subst V
                exact row_5_42
            · by_cases h43_45 : V < 44
              · have he : V = 43 := by omega
                subst V
                exact row_5_43
              · have he : V = 44 := by omega
                subst V
                exact row_5_44
          · by_cases h45_50 : V < 47
            · by_cases h45_47 : V < 46
              · have he : V = 45 := by omega
                subst V
                exact row_5_45
              · have he : V = 46 := by omega
                subst V
                exact row_5_46
            · by_cases h47_50 : V < 48
              · have he : V = 47 := by omega
                subst V
                exact row_5_47
              · by_cases h48_50 : V < 49
                · have he : V = 48 := by omega
                  subst V
                  exact row_5_48
                · have he : V = 49 := by omega
                  subst V
                  exact row_5_49
      · by_cases h50_67 : V < 58
        · by_cases h50_58 : V < 54
          · by_cases h50_54 : V < 52
            · by_cases h50_52 : V < 51
              · have he : V = 50 := by omega
                subst V
                exact row_5_50
              · have he : V = 51 := by omega
                subst V
                exact row_5_51
            · by_cases h52_54 : V < 53
              · have he : V = 52 := by omega
                subst V
                exact row_5_52
              · have he : V = 53 := by omega
                subst V
                exact row_5_53
          · by_cases h54_58 : V < 56
            · by_cases h54_56 : V < 55
              · have he : V = 54 := by omega
                subst V
                exact row_5_54
              · have he : V = 55 := by omega
                subst V
                exact row_5_55
            · by_cases h56_58 : V < 57
              · have he : V = 56 := by omega
                subst V
                exact row_5_56
              · have he : V = 57 := by omega
                subst V
                exact row_5_57
        · by_cases h58_67 : V < 62
          · by_cases h58_62 : V < 60
            · by_cases h58_60 : V < 59
              · have he : V = 58 := by omega
                subst V
                exact row_5_58
              · have he : V = 59 := by omega
                subst V
                exact row_5_59
            · by_cases h60_62 : V < 61
              · have he : V = 60 := by omega
                subst V
                exact row_5_60
              · have he : V = 61 := by omega
                subst V
                exact row_5_61
          · by_cases h62_67 : V < 64
            · by_cases h62_64 : V < 63
              · have he : V = 62 := by omega
                subst V
                exact row_5_62
              · have he : V = 63 := by omega
                subst V
                exact row_5_63
            · by_cases h64_67 : V < 65
              · have he : V = 64 := by omega
                subst V
                exact row_5_64
              · by_cases h65_67 : V < 66
                · have he : V = 65 := by omega
                  subst V
                  exact row_5_65
                · have he : V = 66 := by omega
                  subst V
                  exact row_5_66
  · by_cases h67_135 : V < 101
    · by_cases h67_101 : V < 84
      · by_cases h67_84 : V < 75
        · by_cases h67_75 : V < 71
          · by_cases h67_71 : V < 69
            · by_cases h67_69 : V < 68
              · have he : V = 67 := by omega
                subst V
                exact row_5_67
              · have he : V = 68 := by omega
                subst V
                exact row_5_68
            · by_cases h69_71 : V < 70
              · have he : V = 69 := by omega
                subst V
                exact row_5_69
              · have he : V = 70 := by omega
                subst V
                exact row_5_70
          · by_cases h71_75 : V < 73
            · by_cases h71_73 : V < 72
              · have he : V = 71 := by omega
                subst V
                exact row_5_71
              · have he : V = 72 := by omega
                subst V
                exact row_5_72
            · by_cases h73_75 : V < 74
              · have he : V = 73 := by omega
                subst V
                exact row_5_73
              · have he : V = 74 := by omega
                subst V
                exact row_5_74
        · by_cases h75_84 : V < 79
          · by_cases h75_79 : V < 77
            · by_cases h75_77 : V < 76
              · have he : V = 75 := by omega
                subst V
                exact row_5_75
              · have he : V = 76 := by omega
                subst V
                exact row_5_76
            · by_cases h77_79 : V < 78
              · have he : V = 77 := by omega
                subst V
                exact row_5_77
              · have he : V = 78 := by omega
                subst V
                exact row_5_78
          · by_cases h79_84 : V < 81
            · by_cases h79_81 : V < 80
              · have he : V = 79 := by omega
                subst V
                exact row_5_79
              · have he : V = 80 := by omega
                subst V
                exact row_5_80
            · by_cases h81_84 : V < 82
              · have he : V = 81 := by omega
                subst V
                exact row_5_81
              · by_cases h82_84 : V < 83
                · have he : V = 82 := by omega
                  subst V
                  exact row_5_82
                · have he : V = 83 := by omega
                  subst V
                  exact row_5_83
      · by_cases h84_101 : V < 92
        · by_cases h84_92 : V < 88
          · by_cases h84_88 : V < 86
            · by_cases h84_86 : V < 85
              · have he : V = 84 := by omega
                subst V
                exact row_5_84
              · have he : V = 85 := by omega
                subst V
                exact row_5_85
            · by_cases h86_88 : V < 87
              · have he : V = 86 := by omega
                subst V
                exact row_5_86
              · have he : V = 87 := by omega
                subst V
                exact row_5_87
          · by_cases h88_92 : V < 90
            · by_cases h88_90 : V < 89
              · have he : V = 88 := by omega
                subst V
                exact row_5_88
              · have he : V = 89 := by omega
                subst V
                exact row_5_89
            · by_cases h90_92 : V < 91
              · have he : V = 90 := by omega
                subst V
                exact row_5_90
              · have he : V = 91 := by omega
                subst V
                exact row_5_91
        · by_cases h92_101 : V < 96
          · by_cases h92_96 : V < 94
            · by_cases h92_94 : V < 93
              · have he : V = 92 := by omega
                subst V
                exact row_5_92
              · have he : V = 93 := by omega
                subst V
                exact row_5_93
            · by_cases h94_96 : V < 95
              · have he : V = 94 := by omega
                subst V
                exact row_5_94
              · have he : V = 95 := by omega
                subst V
                exact row_5_95
          · by_cases h96_101 : V < 98
            · by_cases h96_98 : V < 97
              · have he : V = 96 := by omega
                subst V
                exact row_5_96
              · have he : V = 97 := by omega
                subst V
                exact row_5_97
            · by_cases h98_101 : V < 99
              · have he : V = 98 := by omega
                subst V
                exact row_5_98
              · by_cases h99_101 : V < 100
                · have he : V = 99 := by omega
                  subst V
                  exact row_5_99
                · have he : V = 100 := by omega
                  subst V
                  exact row_5_100
    · by_cases h101_135 : V < 118
      · by_cases h101_118 : V < 109
        · by_cases h101_109 : V < 105
          · by_cases h101_105 : V < 103
            · by_cases h101_103 : V < 102
              · have he : V = 101 := by omega
                subst V
                exact row_5_101
              · have he : V = 102 := by omega
                subst V
                exact row_5_102
            · by_cases h103_105 : V < 104
              · have he : V = 103 := by omega
                subst V
                exact row_5_103
              · have he : V = 104 := by omega
                subst V
                exact row_5_104
          · by_cases h105_109 : V < 107
            · by_cases h105_107 : V < 106
              · have he : V = 105 := by omega
                subst V
                exact row_5_105
              · have he : V = 106 := by omega
                subst V
                exact row_5_106
            · by_cases h107_109 : V < 108
              · have he : V = 107 := by omega
                subst V
                exact row_5_107
              · have he : V = 108 := by omega
                subst V
                exact row_5_108
        · by_cases h109_118 : V < 113
          · by_cases h109_113 : V < 111
            · by_cases h109_111 : V < 110
              · have he : V = 109 := by omega
                subst V
                exact row_5_109
              · have he : V = 110 := by omega
                subst V
                exact row_5_110
            · by_cases h111_113 : V < 112
              · have he : V = 111 := by omega
                subst V
                exact row_5_111
              · have he : V = 112 := by omega
                subst V
                exact row_5_112
          · by_cases h113_118 : V < 115
            · by_cases h113_115 : V < 114
              · have he : V = 113 := by omega
                subst V
                exact row_5_113
              · have he : V = 114 := by omega
                subst V
                exact row_5_114
            · by_cases h115_118 : V < 116
              · have he : V = 115 := by omega
                subst V
                exact row_5_115
              · by_cases h116_118 : V < 117
                · have he : V = 116 := by omega
                  subst V
                  exact row_5_116
                · have he : V = 117 := by omega
                  subst V
                  exact row_5_117
      · by_cases h118_135 : V < 126
        · by_cases h118_126 : V < 122
          · by_cases h118_122 : V < 120
            · by_cases h118_120 : V < 119
              · have he : V = 118 := by omega
                subst V
                exact row_5_118
              · have he : V = 119 := by omega
                subst V
                exact row_5_119
            · by_cases h120_122 : V < 121
              · have he : V = 120 := by omega
                subst V
                exact row_5_120
              · have he : V = 121 := by omega
                subst V
                exact row_5_121
          · by_cases h122_126 : V < 124
            · by_cases h122_124 : V < 123
              · have he : V = 122 := by omega
                subst V
                exact row_5_122
              · have he : V = 123 := by omega
                subst V
                exact row_5_123
            · by_cases h124_126 : V < 125
              · have he : V = 124 := by omega
                subst V
                exact row_5_124
              · have he : V = 125 := by omega
                subst V
                exact row_5_125
        · by_cases h126_135 : V < 130
          · by_cases h126_130 : V < 128
            · by_cases h126_128 : V < 127
              · have he : V = 126 := by omega
                subst V
                exact row_5_126
              · have he : V = 127 := by omega
                subst V
                exact row_5_127
            · by_cases h128_130 : V < 129
              · have he : V = 128 := by omega
                subst V
                exact row_5_128
              · have he : V = 129 := by omega
                subst V
                exact row_5_129
          · by_cases h130_135 : V < 132
            · by_cases h130_132 : V < 131
              · have he : V = 130 := by omega
                subst V
                exact row_5_130
              · have he : V = 131 := by omega
                subst V
                exact row_5_131
            · by_cases h132_135 : V < 133
              · have he : V = 132 := by omega
                subst V
                exact row_5_132
              · by_cases h133_135 : V < 134
                · have he : V = 133 := by omega
                  subst V
                  exact row_5_133
                · have he : V = 134 := by omega
                  subst V
                  exact row_5_134
end ProximityPrize.SubmissionLower.Lower80801.ThresholdCompressed
